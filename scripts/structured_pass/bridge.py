"""Fixed-role JSON-RPC bridge; clients cannot select role, commands or host paths."""
import base64
import json
from pathlib import Path
import sys

from . import operation_contract as contract
from . import error_policy
from . import service, paging, review_pages, search, ram_evidence, declared_inputs, learning

TOOL='mcp__facts__operation'


def hook(policy):
    config=json.loads(Path(policy).read_text());request=json.load(sys.stdin)
    tool=request.get('tool_name');args=request.get('tool_input',{})
    allowed=tool==TOOL
    if tool=='Read':
        path=Path(args.get('file_path',''))
        allowed=path.is_absolute() and str(path.resolve()) in config['reads']
    with open(config['log'],'a') as stream:stream.write(json.dumps({'tool':tool,'allowed':allowed})+'\n')
    print(json.dumps({'hookSpecificOutput':{'hookEventName':'PreToolUse',
        'permissionDecision':'allow' if allowed else 'deny','permissionDecisionReason':
        'STRUCTURED_PASS_ALLOW' if allowed else 'STRUCTURED_PASS_DENY'}}))


def tool_listing(role,profile='corridor'):
    operations=contract.offered(role,profile)
    if profile=='investigation':
        return {'tools':[{'name':'operation','description':
            'Read-only investigation of the frozen corridor. Read operation-reference for contracts. '
            'Read investigation-assignment for the planned coverage. Submit claims with checkpoint; '
            'completion is accepted only after the final native audit. Reference images are not admitted in this phase.',
            'inputSchema':{'type':'object','properties':{'operation':{'type':'string','enum':operations},
                'arguments':{'type':'object','description':contract.describe(operations,role,profile)}},
                'required':['operation','arguments'],'additionalProperties':False}}]}
    return {'tools':[{'name':'operation','description':'Structured pass records and controlled mutations.'+ram_evidence.TOOL_HELP+declared_inputs.help_text(role,profile)+(search.TOOL_HELP+learning.help_text(role) if profile=='corridor' else '')+' See arguments.description for required and optional keys.',
        'inputSchema':{'type':'object','properties':{'operation':{'type':'string','enum':operations},
            'arguments':{'type':'object','description':contract.describe(operations,role,profile)}},'required':['operation','arguments'],'additionalProperties':False}}]}


def mcp(root,role,profile='corridor',input_stream=None,output_stream=None):
    from .launcher import Corridor
    from .retained_service import RetainedReviewService
    service.schema({'role':role},('role',))
    if role not in ('implementer','reviewer') or profile not in ('corridor','retained','investigation') or (profile=='investigation' and role!='implementer'):
        raise ValueError('REQUEST_SCHEMA')
    from .investigation_service import Session
    instance=(Session if profile=='investigation' else Corridor if profile=='corridor' else RetainedReviewService)(root)
    for line in input_stream or sys.stdin:
        identifier=None;operation=None;image_result=None;request_arguments=None
        try:
            request=json.loads(line)
        except ValueError:
            response={'error':{'code':-32700,'message':'Parse error'}}
        else:
            if not isinstance(request,dict) or not isinstance(request.get('method'),str):
                response={'error':{'code':-32600,'message':'Invalid request'}}
            elif 'id' not in request:
                continue
            else:
                identifier=request['id'];method=request['method'];candidate=None
                try:
                    if method=='initialize':
                        result={'protocolVersion':request['params']['protocolVersion'],'capabilities':{'tools':{}},
                            'serverInfo':{'name':'structured-pass','version':'1'}}
                    elif method=='tools/list':
                        result=tool_listing(role,profile)
                    elif method=='ping':result={}
                    elif method=='tools/call':
                        params=request.get('params');service.schema(params,('name','arguments'),('_meta',))
                        if params['name']!='operation':raise ValueError('REQUEST_SCHEMA')
                        args=params['arguments'];service.schema(args,('operation','arguments'))
                        if not isinstance(args['operation'],str) or not isinstance(args['arguments'],dict):raise ValueError('REQUEST_SCHEMA')
                        operation=args['operation']
                        request_arguments=args['arguments']
                        candidate=args['arguments'].get('cid')
                        contract.request_arguments(operation,request_arguments,role,profile)
                        answer=instance.dispatch(args['operation'],args['arguments'],role)
                        if isinstance(answer,declared_inputs.ImageResult):
                            if (role,profile,operation)!=('implementer','corridor','input'):raise ValueError('REQUEST_SCHEMA')
                            metadata={'content':[{'type':'text','text':json.dumps(answer.metadata)}]}
                            if len(json.dumps({'jsonrpc':'2.0','id':identifier,'result':metadata}).encode())+1>paging.MAX_BYTES:
                                raise ValueError('RESPONSE_TOO_LARGE')
                            declared_inputs.image_dimensions(answer.png)
                            result={'content':[*metadata['content'],{'type':'image','mimeType':'image/png',
                                    'data':base64.b64encode(answer.png).decode('ascii')}]}
                            image_result=answer
                        else:result={'content':[{'type':'text','text':json.dumps(answer)}]}
                    else:
                        response={'error':{'code':-32601,'message':'Unknown method'}}
                        emit(instance,identifier,response,output_stream or sys.stdout)
                        continue
                    response={'result':result}
                except Exception as error:
                    code=service.public_error_code(error);value={'error':code}
                    if isinstance(error,(service.ServiceError,contract.RequestError)):
                        value['details']=error.details
                        if code=='RESPONSE_TOO_LARGE' and operation=='review':value.update(review_pages.continuation(error.details))
                    if code=='REQUEST_SCHEMA' and operation in (contract.investigating() if profile=='investigation' else contract.corridor() if profile=='corridor' else contract.retained()):
                        value['expected_arguments']=contract.entry(operation,role,profile)
                    if code=='UNKNOWN_OPERATION':
                        value['details']={'field':'operation','accepted_values':contract.offered(role,profile)}
                    value={**error_policy.describe(code,correction=value.get('action'),
                        request_error=isinstance(error,contract.RequestError)),**value}
                    if value['error_class']=='correctable':
                        value['reference']={'operation':'input','input_id':'operation-reference',
                            'section':operation if operation in contract.offered(role,profile) else 'arguments'}
                        if 'details' not in value:
                            value['details']=error_policy.diagnostics(code,operation,role,profile)
                    try:value.update(instance.error_context(candidate))
                    except Exception:pass
                    response={'result':{'isError':True,'content':[{'type':'text','text':json.dumps(value)}]}}
        emit(instance,identifier,response,output_stream or sys.stdout,operation,image_result,request_arguments)


def emit(instance,identifier,response,output,operation=None,image_result=None,request_arguments=None):
    def encode(value, ident=identifier):
        # Count the delivered envelope, including this counter and JSON escaping.
        # This is an observable per-response measure, not a session budget ledger.
        if operation is not None and image_result is None and 'result' in value:
            content=value['result'].get('content',[])
            if len(content)==1 and content[0].get('type')=='text':
                answer=json.loads(content[0]['text'])
                if isinstance(answer,dict):
                    answer['volume']={'response_bytes':0,'question_limit_bytes':contract.QUESTION_BYTES}
                    while True:
                        content[0]['text']=json.dumps(answer)
                        encoded=json.dumps({'jsonrpc':'2.0','id':ident,**value})
                        size=len(encoded.encode())+1
                        if size==answer['volume']['response_bytes']:return encoded
                        answer['volume']['response_bytes']=size
        return json.dumps({'jsonrpc':'2.0','id':ident,**value})
    encoded=encode(response)
    cap=declared_inputs.IMAGE_REPLY_LIMIT if isinstance(image_result,declared_inputs.ImageResult) else paging.MAX_BYTES
    if len(encoded.encode())+1>cap:
        value={'error':'RESPONSE_TOO_LARGE',**error_policy.describe('RESPONSE_TOO_LARGE')}
        try:
            answer=json.loads(response['result']['content'][0]['text'])
            if operation=='review':value.update(review_pages.continuation(answer))
            elif (type(answer.get('offset')) is int and
                  'limit' in {**contract.BASE,**contract.RENAME,**contract.VERDICT}.get(operation,((),()))[1] and
                  any(isinstance(answer.get(key),(str,list)) and len(answer[key])>1
                      for key in ('text','records','lines','mentions','rows'))):
                value['action']='Reduce limit and retry the same offset; no records were delivered.'
                value['offset']=answer['offset']
        except (KeyError,IndexError,TypeError,ValueError):pass
        value.update(error_policy.describe('RESPONSE_TOO_LARGE',correction=value.get('action')))
        try:value['generation']=instance.error_context(None)['generation']
        except Exception:pass
        response={'result':{'isError':True,'content':[{'type':'text','text':json.dumps(value)}]}}
        encoded=encode(response)
        if len(encoded.encode())+1>paging.MAX_BYTES:
            encoded=encode(response,None)
    callback=getattr(instance,'record_delivery',None)
    if callback is not None and operation is not None and request_arguments is not None:
        callback(operation,request_arguments,json.loads(encoded)['result'])
    print(encoded,file=output,flush=True)
