"""First-contact mistakes against real offered routes, before any client run."""
import copy
import json
import os
from pathlib import Path
import unittest

import structured_pass_pagination_test as pagination
from structured_pass_fixture import closeout_ops, rename_ops
from structured_pass import operation_contract as contract

# Unknown lookup keys are distinct from valid free-text queries returning no hits.
UNKNOWN = {
    'generation':'G-unknown', 'base_generation':'E-unknown', 'ticket':'E-unknown',
    'cid':'C-unknown', 'preview_digest':'unknown-preview', 'input_id':'not-declared',
    'symbol':'NoSuchSymbol', 'record_id':'unknown-record', 'set_id':'unknown-set',
    'view':'unknown-view', 'kind':'unknown-kind', 'span':'unknown-span',
    'decoder':'unknown-decoder', 'artifact':'unknown-artifact',
    'path':'projects/sample/docs/reverse_engineering/NOPE.md',
    'continuation':'unknown-continuation', 'analogue_index':999, 'revision':999,
    'attempt':999, 'sequence':999, 'address':99999, 'byte_offset':10**9, 'byte_count':99999,
    'offset':10**9, 'limit':20000, 'query':{'kind':'unknown-kind'},
    'operations':[{'kind':'unknown-kind'}],
    'claims':[{'id':'unknown-claim'}],
    'decisions':[{'statement':'Synthetic decision','claims':['unknown-claim']}],
}
# These are authored text or filters, not foreign keys. A spelling with no match
# is legal; type and missing-required tests still apply.
FREE = {'names','contains','key','report','response'}
MUTATIONS = {'preview','confirm','validate','publish','start_chain','reready','closeout',
             'approve','request-changes','checkpoint'}


class ArgumentTests(unittest.TestCase):
    setUpClass = classmethod(pagination.PaginationTests.setUpClass.__func__)
    call = classmethod(pagination.PaginationTests.call.__func__)
    cases = pagination.PaginationTests.cases

    def all_cases(self, profile):
        cases = [(op,args) for op,args,_ in self.cases(profile)]
        g = self.ig if profile=='investigator' else self.g
        cases += [('status',{}), ('inspect',{'generation':g,'symbol':'Entry'}),
                  ('documents',{'generation':g})]
        model=(self.ic if profile=='investigator' else self.c).editor.model(g)
        data_id=model.ids[model.document['data'][0]['syntax_id']]
        cases += [('evidence',{'generation':g,'view':'decode','record_id':data_id,
                              'decoder':'bytes','byte_offset':0,'byte_count':1}),
                  ('evidence',{'generation':g,'view':'artifact_rows','artifact':'extent_rows','key':'absent'})]
        if profile!='investigator':cases.append(('candidate_status',{'cid':self.cid}))
        if profile=='investigator':
            cases.append(('checkpoint',{'generation':g,'claims':[], 'decisions':[]}))
        elif profile=='editor':
            cases += [('preview',{'generation':g,'operations':closeout_ops(self.c,g,notes='Synthetic proposal.')}),
                ('confirm',{'generation':g,'preview_digest':self.preview}),
                ('validate',{'cid':self.cid}),('publish',{'cid':self.cid}),
                ('start_chain',{'generation':g}),('reready',{'response':'Synthetic reply.'}),('closeout',{})]
        else:
            cases += [(op,{'ticket':self.ticket,'report':'Synthetic report.'}) for op in ('approve','request-changes')]
        return cases

    def test_all_arguments_recover_before_mutation(self):
        rows=[]
        for profile in ('investigator','editor','reviewer'):
            role='reviewer' if profile=='reviewer' else 'implementer'
            mode='investigation' if profile=='investigator' else 'corridor'
            cases=self.all_cases(profile)
            self.assertEqual({op for op,_ in cases},set(contract.offered(role,mode)))
            covered=set()
            for op,args in cases:
                spec=contract.entry(op,role,mode)
                for field in spec['required']+spec['optional']:
                    covered.add((op,field))
                    wrong=[] if field=='query' else {'private-invalid-value':1}
                    mistakes=[('wrong-type',{**args,field:wrong})]
                    if field in spec['required']:
                        mistakes.append(('missing',{k:v for k,v in args.items() if k!=field}))
                    if field in UNKNOWN:mistakes.append(('unknown',{**args,field:copy.deepcopy(UNKNOWN[field])}))
                    else:self.assertIn(field,FREE,(op,field))
                    for mistake,bad in mistakes:
                        editor=self.ic.editor if profile=='investigator' else self.c.editor
                        before=editor.state_path.read_bytes()
                        try:
                            result=self.call(profile,op,bad)
                        except Exception as error:
                            result={'error':'UNCAUGHT_'+type(error).__name__,'error_class':'terminal'}
                        detail=result.get('details',{}); named=detail.get('field','')
                        names=named.replace('/','.').replace('[]','').split('.')
                        good=(result.get('error_class')=='correctable' and field in names)
                        rows.append({'profile':profile,'operation':op,'field':field,'mistake':mistake,
                            'error':result.get('error'),'class':result.get('error_class'),
                            'diagnostic':detail,'passed':good})
                        with self.subTest(profile=profile,operation=op,field=field,mistake=mistake):
                            self.assertTrue(good,result)
                            self.assertNotEqual(result.get('error'),'INTERNAL_SERVICE_ERROR')
                            self.assertNotIn('private-invalid-value',json.dumps(result))
                            if op in MUTATIONS:self.assertEqual(editor.state_path.read_bytes(),before)
            expected={(op,f) for op in contract.offered(role,mode)
                      for f in contract.entry(op,role,mode)['required']+contract.entry(op,role,mode)['optional']}
            self.assertEqual(covered,expected)
        if os.environ.get('ARGUMENT_SWEEP_REPORT'):
            Path(os.environ['ARGUMENT_SWEEP_REPORT']).write_text(json.dumps(rows,indent=2)+'\n')

    def test_unsupported_legacy_mutations_are_not_offered(self):
        for profile in ('investigator','editor','reviewer'):
            for op in ('propose','amend'):
                result=self.call(profile,op,{'generation':self.ig if profile=='investigator' else self.g})
                expected=('INVESTIGATION_READ_ONLY','terminal') if profile=='investigator' else ('UNKNOWN_OPERATION','correctable')
                self.assertEqual((result['error'],result['error_class']),expected)

    def test_document_boundaries_and_corrected_lookup(self):
        # Fixed boundary list: no caller typo grants another namespace or owner.
        boundaries={
            '/etc/passwd':'absolute host path',
            'projects/sample/docs/../secret.md':'traversal',
            'projects/other/docs/reverse_engineering/WORKING_NOTES.md':'another project',
            'projects/sample/asm/sample.asm':'source, not a document',
            'projects/sample/docs/reverse_engineering/reviews/pass-1.md':'reviewer archive ownership',
        }
        for profile in ('investigator','editor','reviewer'):
            g=self.ig if profile=='investigator' else self.g
            for path,reason in boundaries.items():
                with self.subTest(profile=profile,reason=reason):
                    result=self.call(profile,'document',{'generation':g,'path':path})
                    self.assertEqual((result['error'],result['error_class']),('DOCUMENT_PATH_FORBIDDEN','terminal'))
            miss=self.call(profile,'document',{'generation':g,'path':UNKNOWN['path']})
            self.assertEqual(miss['error_class'],'correctable')
            self.assertIn('operation-reference',miss['details']['source'])
            corrected=self.call(profile,'document',{'generation':g,
                'path':'projects/sample/docs/reverse_engineering/WORKING_NOTES.md'})
            self.assertTrue(corrected['exists'])

    def test_nested_edit_and_checkpoint_mistakes_do_not_change_state(self):
        operations=rename_ops(self.ic,self.ig)
        model=self.c.editor.model(self.g); node=model.declarations['Capacity']
        operations[0].update(declaration_id=model.ids[node],old_name='Capacity',new_name='Available',
                             preimage=model.statement(node)['preimage_sha256'])
        operations[1].update(preimage=self.c.editor.state['generations'][self.g]['manifest'][self.c.editor.ledger])
        operations[1]['rows'][0].update(old_name='Capacity',new_name='Available')
        operations[2:]=closeout_ops(self.c,self.g)
        for field in ('kind','declaration_id','old_name','new_name','preimage'):
            for mistake in (('wrong-type','missing') if field=='new_name' else ('wrong-type','missing','unknown')):
                bad=copy.deepcopy(operations)
                if mistake=='missing':bad[0].pop(field)
                else:bad[0][field]={'private-invalid-value':1} if mistake=='wrong-type' else 'unknown-value'
                before=self.c.editor.state_path.read_bytes()
                with self.subTest(operation='preview',field=field,mistake=mistake):
                    result=self.call('editor','preview',{'generation':self.g,'operations':bad})
                    self.assertEqual(result.get('error_class'),'correctable',result)
                    self.assertIn(field,result['details']['field'])
                    self.assertEqual(self.c.editor.state_path.read_bytes(),before)
        corrected=self.call('editor','preview',{'generation':self.g,'operations':operations})
        self.assertIn('preview_digest',corrected)
        type(self).preview=corrected['preview_digest']
        claim={'id':'finding','kind':'unknown','subject':'Synthetic corridor','statement':'Unresolved',
               'confidence':'unknown','citations':[],'searched_sets':[],'unknowns':'Needs review','contrary':[]}
        for field in claim:
            for mistake in ('wrong-type','missing'):
                bad=copy.deepcopy(claim)
                if mistake=='missing':bad.pop(field)
                else:bad[field]={'private-invalid-value':1}
                with self.subTest(operation='checkpoint',field=field,mistake=mistake):
                    before=json.loads((self.flow.root/'state.json').read_text())
                    result=self.call('investigator','checkpoint',{'generation':self.ig,'claims':[bad],'decisions':[]})
                    self.assertEqual(result.get('error_class'),'correctable',result)
                    self.assertIn(field,result['details']['field'])
                    after=json.loads((self.flow.root/'state.json').read_text())
                    # Refusals are journaled too, but cannot stage a checkpoint
                    # or grant coverage. Keep all state except that audit row.
                    for entry in after['sessions']:
                        after['sessions'][entry]['journal']=before['sessions'][entry]['journal']
                    self.assertEqual(after,before)
        for field,value in [('citations',[{'id':{},'sha256':'0'*64}]),
                            ('searched_sets',[{}]),('decisions',[{'statement':'x','claims':[{}]}])]:
            bad=copy.deepcopy(claim);decisions=[]
            if field=='decisions':decisions=value
            else:bad[field]=value
            with self.subTest(nested=field):
                result=self.call('investigator','checkpoint',{'generation':self.ig,'claims':[bad],'decisions':decisions})
                self.assertEqual(result.get('error_class'),'correctable',result)
                self.assertIn(field,result['details']['field'])

        # IDs were nonempty strings, not trimmed prose. Keep that acceptance
        # while proving a corrected checkpoint reaches the real staging path.
        corrected=self.call('investigator','checkpoint',{'generation':self.ig,
            'claims':[{**claim,'id':' '}],
            'decisions':[{'statement':'Defer until reviewed','claims':[' ']}]})
        self.assertEqual(corrected.get('completion'),'pending_native_audit',corrected)
        self.assertTrue(corrected['staged_sha256'])


if __name__=='__main__':unittest.main()
