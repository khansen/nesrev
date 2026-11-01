"""Fixed-role JSON-RPC bridge; clients cannot select role, commands or host paths."""
import json
from pathlib import Path
import sys

from . import service, paging, review_pages

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


def mcp(root,role,profile='corridor',input_stream=None,output_stream=None):
    from .launcher import Corridor
    from .retained_service import RetainedReviewService
    service.schema({'role':role},('role',))
    if role not in ('implementer','reviewer') or profile not in ('corridor','retained'):
        raise ValueError('REQUEST_SCHEMA')
    instance=(Corridor if profile=='corridor' else RetainedReviewService)(root)
    for line in input_stream or sys.stdin:
        identifier=None;operation=None
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
                        operations=['status','query','navigate','inspect','q09','documents','document','review','candidate_status','guidance']
                        if profile=='retained':operations=['status','query','review','reassemble','inspect','navigate','q09','document']
                        elif role=='implementer':operations+=['preview','preview_page','confirm','validate','publish','start_chain','reready','closeout']
                        else:operations+=['approve','request-changes']
                        result={'tools':[{'name':'operation','description':'Structured pass records and controlled mutations.',
                            'inputSchema':{'type':'object','properties':{'operation':{'type':'string','enum':operations},
                                'arguments':{'type':'object'}},'required':['operation','arguments'],'additionalProperties':False}}]}
                    elif method=='ping':result={}
                    elif method=='tools/call':
                        params=request.get('params');service.schema(params,('name','arguments'),('_meta',))
                        if params['name']!='operation':raise ValueError('REQUEST_SCHEMA')
                        args=params['arguments'];service.schema(args,('operation','arguments'))
                        if not isinstance(args['operation'],str) or not isinstance(args['arguments'],dict):raise ValueError('REQUEST_SCHEMA')
                        operation=args['operation']
                        candidate=args['arguments'].get('cid')
                        answer=instance.dispatch(args['operation'],args['arguments'],role)
                        result={'content':[{'type':'text','text':json.dumps(answer)}]}
                    else:
                        response={'error':{'code':-32601,'message':'Unknown method'}}
                        emit(instance,identifier,response,output_stream or sys.stdout)
                        continue
                    response={'result':result}
                except Exception as error:
                    code=service.public_error_code(error);value={'error':code}
                    if isinstance(error,service.ServiceError):
                        value['details']=error.details
                        if code=='RESPONSE_TOO_LARGE' and operation=='review':value.update(review_pages.continuation(error.details))
                    value['retryable']=code in ('VALIDATION_IN_PROGRESS','REVIEW_STATE_BUSY','REVIEW_RESTORE_IN_PROGRESS')
                    try:value.update(instance.error_context(candidate))
                    except Exception:pass
                    response={'result':{'isError':True,'content':[{'type':'text','text':json.dumps(value)}]}}
        emit(instance,identifier,response,output_stream or sys.stdout,operation)


def emit(instance,identifier,response,output,operation=None):
    encoded=json.dumps({'jsonrpc':'2.0','id':identifier,**response})
    if len(encoded.encode())+1>paging.MAX_BYTES:
        value={'error':'RESPONSE_TOO_LARGE','retryable':False}
        try:
            answer=json.loads(response['result']['content'][0]['text'])
            if operation=='review':value.update(review_pages.continuation(answer))
            elif type(answer.get('offset')) is int:
                value['action']='Reduce limit and retry the same offset; no records were delivered.'
                value['offset']=answer['offset']
        except (KeyError,IndexError,TypeError,ValueError):pass
        try:value['generation']=instance.error_context(None)['generation']
        except Exception:pass
        response={'result':{'isError':True,'content':[{'type':'text','text':json.dumps(value)}]}}
        encoded=json.dumps({'jsonrpc':'2.0','id':identifier,**response})
        if len(encoded.encode())+1>paging.MAX_BYTES:
            encoded=json.dumps({'jsonrpc':'2.0','id':None,**response})
    print(encoded,file=output,flush=True)
