"""Generic constant-use context view. No fixture symbols, lines or expected answers.

All references include data and EQU expressions. Dependents are followed through
producer bindings; counts distinguish direct references from uses via aliases.
This exposes evidence for judgment and does not declare semantic misuse.
"""
from collections import Counter


def constant_uses(model, symbol, offset=0, limit=20):
    if type(offset) is not int or type(limit) is not int or offset<0 or not 1<=limit<=64:
        raise ValueError('invalid pagination')
    declaration = model.declarations.get(symbol)
    if declaration is None or model.facts[declaration]['kind']!='EQU_NODE':
        raise ValueError('unknown constant')
    dependent = {declaration: []}
    changed = True
    while changed:
        changed = False
        for ref,bound in model.bindings.items():
            ctx = model.context(ref)
            if bound in dependent and model.facts[ctx]['kind']=='EQU_NODE' and ctx not in dependent:
                dependent[ctx] = [model.ids[bound], *dependent[bound]]
                changed = True
    rows = []
    for ref,bound in model.bindings.items():
        if bound not in dependent:
            continue
        ctx = model.context(ref)
        statement = model.statement(ctx)
        # Nearby typed instructions supply local value-use context, never raw lines.
        neighbors = []
        if ctx in model.instructions:
            instruction = model.instructions[ctx]
            candidates = [(n,r) for n,r in model.instructions.items()
                          if r['lexical_owner']==instruction['lexical_owner']
                          and r['segment_id']==instruction['segment_id']
                          and abs(r['output_offset']-instruction['output_offset'])<=6]
            neighbors = [model.statement(n) for n,r in candidates if n!=ctx][:6]
        rows.append({'reference_id':model.ids[ref], 'declaration_id':model.ids[bound],
                     'direct':bound==declaration,'via_declarations':dependent[bound],
                     'statement':statement,'context_instructions':neighbors})
    rows.sort(key=lambda row:(not row['direct'],row['statement']['span'],row['reference_id']))
    owners = Counter(row['statement'].get('lexical_owner') or row['statement'].get('name') or row['statement']['kind'] for row in rows)
    page = rows[offset:offset+limit]
    return {'constant':model.statement(declaration),'direct_use_count':sum(r['direct'] for r in rows),
            'via_equ_use_count':sum(not r['direct'] for r in rows),'total':len(rows),
            'owners':dict(owners),'offset':offset,'next_offset':offset+len(page) if offset+len(page)<len(rows) else None,
            'uses':page,'limits':['Semantic owner/subsystem identity is not inferred from equal values.',
                'Complete parsed references; implicit hardware, dynamic transfers and runtime state are not inferred.']}
