"""Edit operands projected from native records, with page-local hash sharing."""
import json
import re
from .model import digest
from .producer import require

COLUMNS = ('record_id', 'kind', 'name', 'text', 'preimage', 'expressions', 'owner_id')
EXPRESSION_COLUMNS = ('record_id', 'fields', 'children', 'preimage')
HELP = ('Zip columns with records and expression_columns with expressions. '
    'A preimage is an index into this page\'s preimages array. Record expressions '
    'and expression children are ordered IDs into the expressions table. Expression '
    'fields retain kind and any native name, value, operator_name, string_hex, '
    'datatype or declaration_id; absent fields stay absent. Text is the exact '
    'producer span. owner_id is the lexical owner, not a control-flow proof. '
    'Every page is independent. These are editing operands, not analysis records; '
    'full records remain available. Trivia units and comments still use their own views.')


def hash_characters(value):
    """Conservative charge for every long hex run, including IDs and repeats."""
    return sum(len(m.group()) for m in re.finditer(r'[0-9a-fA-F]{32,}',
        json.dumps(value, ensure_ascii=True, separators=(',', ':'))))


def project(model, node):
    statement = model.statement(node)
    def expression(value):
        n = model.node(value['record_id'])
        return {**value, 'preimage': digest(model.source[slice(*model.ranges[n])]),
                'children': [expression(child) for child in value['children']]}
    owner = model.owners[node]
    return {'record_id': statement['record_id'], 'kind': statement['kind'],
            'name': statement.get('name'),
            'text': model.source[slice(*model.ranges[node])].decode('utf-8'),
            'preimage': statement['preimage_sha256'],
            'expressions': [expression(value) for value in statement['expressions']],
            'owner_id': model.ids[owner] if owner is not None else None}


def encode(page):
    preimages = []; hashes = {}; expressions = {}; records = []
    def preimage(value):
        if value not in hashes:
            hashes[value] = len(preimages); preimages.append(value)
        return hashes[value]
    def expression(value):
        ident = value['record_id']
        fields = {k: v for k, v in value.items() if k not in ('record_id', 'children', 'preimage')}
        row = [ident, fields, [expression(child) for child in value['children']], preimage(value['preimage'])]
        require(ident not in expressions or expressions[ident] == row, 'SOURCE_MODEL_JOIN')
        expressions[ident] = row
        return ident
    for record in page['records']:
        row = {**record, 'preimage': preimage(record['preimage']),
               'expressions': [expression(value) for value in record['expressions']]}
        records.append([row[key] for key in COLUMNS])
    return {**page, 'view': 'edit', 'encoding': 'source-edit-v1',
            'columns': list(COLUMNS), 'records': records,
            'expression_columns': list(EXPRESSION_COLUMNS), 'expressions': list(expressions.values()),
            'preimages': preimages, 'decode': HELP}
