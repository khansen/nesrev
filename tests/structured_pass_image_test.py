"""Fixed-ID media transport, role separation and independent wire budgets."""
import base64
import copy
import io
import json
import os
from pathlib import Path
import shutil
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch
import zlib

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from structured_pass import bridge, declared_inputs as inputs, input_delivery, producer
from structured_pass.launcher import Corridor
from structured_pass.retained_service import RetainedReviewService
from structured_pass_inputs_test import setup_inputs
from structured_pass_fixture import prepare, closeout_ops


def png(width=1,height=1,padding=0):
    def chunk(name,data):
        return struct.pack('>I',len(data))+name+data+struct.pack('>I',zlib.crc32(name+data))
    return (b'\x89PNG\r\n\x1a\n'+chunk(b'IHDR',struct.pack('>IIBBBBB',width,height,8,0,0,0,0))
            +chunk(b'IDAT',zlib.compress(b'\x00\x80'))+chunk(b'tEXt',b'x\x00'+b'y'*padding)+chunk(b'IEND',b''))


def call(root,generation,input_id='page',role='implementer',profile='corridor',payload_extra=None,**extra):
    request={'id':1,'method':'tools/call','params':{'name':'operation','arguments':{
        'operation':'input','arguments':{'generation':generation,'input_id':input_id,**extra,**(payload_extra or {})}}}}
    output=io.StringIO()
    bridge.mcp(root,role,profile,io.StringIO(json.dumps(request)+'\n'),output)
    wire=output.getvalue()
    return json.loads(wire)['result'],len(wire.encode())


class ImageTests(unittest.TestCase):
    def setUp(self):
        if not os.environ.get('STRUCTURED_PASS_XASM'):self.skipTest('pinned producer required')
        (ROOT/'tmp').mkdir(exist_ok=True)
        self.tmp=tempfile.TemporaryDirectory(dir=ROOT/'tmp',prefix='image-test-');self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name).resolve()
        self.c=prepare(self.root,declared_setup=setup_inputs)
        self.g=self.c.editor.state['current']
        self.capture=self.c.editor.model(self.g).capture
        self.expected=(self.capture/'input-page.bin').read_bytes()

    def error(self,result,code):
        answer,size=result
        self.assertTrue(answer.get('isError'),answer)
        self.assertEqual(json.loads(answer['content'][0]['text'])['error'],code)
        self.assertEqual([v['type'] for v in answer['content']],['text'])
        self.assertLessEqual(size,24576)

    def test_exact_image_and_role_refusals(self):
        answer,size=call(self.c.root,self.g)
        self.assertFalse(answer.get('isError'),answer)
        self.assertEqual([v['type'] for v in answer['content']],['text','image'])
        meta=json.loads(answer['content'][0]['text']);image=answer['content'][1]
        self.assertEqual(base64.b64decode(image['data']),self.expected)
        self.assertEqual(meta['sha256'],producer.digest(self.expected))
        self.assertEqual(meta['generation'],self.g)
        self.assertEqual(meta['origin']['identity']['pdf_page'],1)
        self.assertEqual(meta['manifest_sha256'],producer.sha(self.capture/inputs.FILE))
        self.assertEqual((meta['width'],meta['height'],meta['bytes']),(1,1,len(self.expected)))
        self.assertEqual(image['mimeType'],'image/png')
        self.error(call(self.c.root,self.g,role='reviewer'),'INPUT_MEDIA_REQUIRED')
        for extra in ({'offset':0},{'limit':4096},{'path':'/tmp/page.png'},
                      {'url':'https://example.invalid/'},{'size':1},{'role':'implementer'}):
            self.error(call(self.c.root,self.g,payload_extra=extra),'REQUEST_SCHEMA')
        self.error(call(self.c.root,self.g,input_id='unselected'),'INPUT_UNKNOWN')
        for gen in ('G-missing','E-'+'0'*64):
            self.error(call(self.c.root,gen),'UNKNOWN_GENERATION')

    def test_hash_catalog_and_symlink_drift_refuse(self):
        path=self.capture/'input-page.bin'
        # A forged reader result still faces the per-read payload check.
        original_load=inputs.load
        catalog=original_load(self.capture)
        path.write_bytes(png(padding=1))
        with patch.object(inputs,'load',return_value=catalog):
            with self.assertRaisesRegex(ValueError,'INPUT_CHANGED'):
                inputs.implementer_read(self.capture,self.g,'page')
        path.write_bytes(self.expected)
        other=self.root/'other.png';other.write_bytes(self.expected);path.unlink();path.symlink_to(other)
        self.error(call(self.c.root,self.g),'INPUT_CHANGED')
        path.unlink();path.write_bytes(self.expected)
        p=self.capture/inputs.FILE;raw=p.read_bytes();p.write_bytes(raw+b' ')
        with self.assertRaisesRegex(ValueError,'INPUT_CHANGED|CAPTURE_CHANGED'):
            call(self.c.root,self.g)

    def test_published_generation_and_restored_payload(self):
        preview=self.c.dispatch('preview',{'generation':self.g,'operations':closeout_ops(self.c,self.g)},'implementer')
        cid=self.c.dispatch('confirm',{'generation':self.g,'preview_digest':preview['preview_digest']},'implementer')['candidate']
        self.assertEqual(self.c.dispatch('validate',{'cid':cid},'implementer')['status'],'validated')
        pub=self.c.dispatch('publish',{'cid':cid},'implementer');ticket=pub['review']['artifact_id']
        shutil.rmtree(self.root/'repo/projects/sample/tmp')
        shutil.rmtree(self.root/'repo/projects/sample/docs/game_reference')
        (self.root/'selection.json').unlink()
        answer,_=call(self.c.root,ticket)
        self.assertFalse(answer.get('isError'),answer)
        self.assertEqual(json.loads(answer['content'][0]['text'])['generation'],ticket)
        self.assertEqual(base64.b64decode(answer['content'][1]['data']),self.expected)
        restored=RetainedReviewService.from_publication(self.root/'restored',self.c.config['store'],ticket)
        self.error(call(restored.root,ticket,role='reviewer',profile='retained'),'INPUT_MEDIA_REQUIRED')
        self.error(call(restored.root,ticket,role='implementer',profile='retained'),'INPUT_MEDIA_REQUIRED')
        # The same checked capture supports exact image reads independently of the operator's folder.
        capture=restored.model(ticket).capture
        self.assertEqual(inputs.implementer_read(capture,ticket,'page').png,self.expected)

    def test_text_pagination_and_wrong_kind_have_no_image_exception(self):
        answer,_=call(self.c.root,self.g,input_id='reference',offset=1,limit=17)
        self.assertEqual([v['type'] for v in answer['content']],['text'])
        expected=(self.capture/'input-reference.bin').read_bytes().decode()
        self.assertEqual(json.loads(answer['content'][0]['text'])['text'],expected[1:18])
        output=io.StringIO()
        fake={'type':'ImageResult','metadata':{},'png':'x'*30000}
        with patch.object(Corridor,'dispatch',return_value=fake):
            self.error(call(self.c.root,self.g),'RESPONSE_TOO_LARGE')
        for image in (png(padding=30000),png(padding=inputs.IMAGE_LIMIT)):
            result=inputs.ImageResult({'generation':self.g},image)
            with patch.object(Corridor,'dispatch',return_value=result):
                if len(image)>inputs.IMAGE_LIMIT:self.error(call(self.c.root,self.g),'INPUT_LIMIT_EXCEEDED')
                else:
                    answer,size=call(self.c.root,self.g)
                    self.assertFalse(answer.get('isError'));self.assertGreater(size,24576)
                    self.assertEqual(base64.b64decode(answer['content'][1]['data']),image)
        result=inputs.ImageResult({'generation':self.g,'text':'x'*25000},self.expected)
        with patch.object(Corridor,'dispatch',return_value=result):
            self.error(call(self.c.root,self.g),'RESPONSE_TOO_LARGE')
        with patch.object(inputs,'IMAGE_REPLY_LIMIT',100):
            self.error(call(self.c.root,self.g),'RESPONSE_TOO_LARGE')

    def test_inventory_and_assembly_checks(self):
        record=input_delivery.assemble(self.c.root,self.root/'assembly','implementer','Complete this pass.')
        inputs.image_inventory(record)
        original=copy.deepcopy(record)
        record['media']*=9
        with self.assertRaisesRegex(ValueError,'INPUT_LIMIT_EXCEEDED'):inputs.image_inventory(record)
        path=Path(original['media'][0]['path']);path.write_bytes(png(width=2049))
        original['media'][0]['sha256']=producer.sha(path)
        with self.assertRaisesRegex(ValueError,'INPUT_LIMIT_EXCEEDED'):inputs.image_inventory(original)
        with self.assertRaisesRegex(ValueError,'INPUT_CHANGED'):
            input_delivery.verify(self.c.root,self.root/'assembly/assembly.json')


class FormatTests(unittest.TestCase):
    def test_png_bounds_and_header(self):
        self.assertEqual(inputs.image_dimensions(png(width=2048,height=2048)),(2048,2048))
        for data in (png(width=0),png(height=0),png(width=2049),png(height=2049),png(padding=inputs.IMAGE_LIMIT),
                     b'not PNG',b'\x89PNG\r\n\x1a\n',png()[:29]+b'\0'*4):
            with self.subTest(size=len(data)),self.assertRaises(ValueError):inputs.image_dimensions(data)

    def test_help_is_pinned_per_role(self):
        implementer=bridge.tool_listing('implementer')['tools'][0]['description']
        self.assertIn(inputs.IMAGE_GUIDANCE,implementer)
        for role,profile in (('reviewer','corridor'),('reviewer','retained')):
            help=bridge.tool_listing(role,profile)['tools'][0]['description']
            self.assertIn('INPUT_MEDIA_REQUIRED',help)
            self.assertNotIn('returns one selected PNG as image content',help)


if __name__=='__main__':unittest.main()
