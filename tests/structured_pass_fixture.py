"""Synthetic project and explicitly simulated gate writers for lifecycle tests.

The source and PRG are real inputs to the pinned assembler. Gate simulation
tests ownership/lifecycle, not the correctness of the production quality gates.
Real project gate replay is separate, outside the project-neutral test tree.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess

from structured_pass import producer, mixed_documents as mixed, service as common
from structured_pass.model import certify, digest
from structured_pass.launcher import Corridor
from structured_pass_test import fixture

PROJECT='projects/sample/'
SOURCE=PROJECT+'asm/sample.asm'
REFERENCE=PROJECT+'reference/sample.nes'


def git(repo,*args):
    return subprocess.check_output(['git','-C',str(repo),'-c','commit.gpgsign=false',
        '-c','user.name=Fixture','-c','user.email=fixture@example.invalid',*args],text=True).strip()


def prepare(root, *, uses=1, gate_extra=""):
    root=Path(root);repo=root/'repo';repo.mkdir(parents=True)
    source,reference=fixture(root/'inputs',uses=uses)
    for path,original in ((SOURCE,source),(REFERENCE,reference)):
        target=repo/path;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(original,target)
    docs=repo/PROJECT/'docs/reverse_engineering';(docs/'inventory/pass').mkdir(parents=True)
    fields=['pass_id','focus','notes',*sorted(mixed.PROTECTED)]
    (docs/'PROGRESS_SCORECARD.md').write_text('| '+' | '.join(fields)+' |\n| '+' | '.join(['---']*len(fields))+' |\n')
    (docs/'inventory/renames.csv').write_text('old_name,new_name,reason,confidence,pass_id\n')
    (docs/'inventory/deferrals.csv').write_text(','.join(mixed.DEFERRAL_FIELDS)+'\n')
    (docs/'WORKING_NOTES.md').write_text('# Notes\n\nSynthetic project.\n')
    (docs/'inventory/pass/current_pass_plan.json').write_text(json.dumps({'intended_pass_id':1,'warning_baseline_count_at_start':0}))
    (docs/'inventory/pass/next_pass.json').write_text('{}\n')
    (repo/'AGENTS.md').write_text('Synthetic lifecycle fixture.\n')
    (repo/'Makefile').write_text('project-inventory project-verify project-process-check project-docs-check:\n\t@echo simulated-quality-gate\n')
    scripts=repo/'scripts';scripts.mkdir()
    (scripts/'project_pass_closeout.sh').write_text('''#!/bin/bash
set -euo pipefail
python3 scripts/fixture_closeout.py "$1" "$2"
''')
    (scripts/'fixture_closeout.py').write_text('''import os,sys
from pathlib import Path
p=Path('projects')/sys.argv[1]/'docs/reverse_engineering/PROGRESS_SCORECARD.md'
lines=p.read_text().splitlines(); fields=[v.strip() for v in lines[0].strip('|').split('|')]
for i,line in enumerate(lines[2:],2):
    row=dict(zip(fields,[v.strip() for v in line.strip('|').split('|')]))
    if row['pass_id']==sys.argv[2]:
        for key in fields:
            if key in ('verify','docs_check'):row[key]='pass'
            elif key=='rework_items':row[key]=os.environ['REWORK_ITEMS']
            elif key not in ('pass_id','focus','notes','raw_ptr_immediates_remaining'):row[key]='0'
        lines[i]='| '+' | '.join(row[k] for k in fields)+' |'
p.write_text('\\n'.join(lines)+'\\n')
''')
    if gate_extra:
        with (scripts/'fixture_closeout.py').open('a') as stream:stream.write(gate_extra)
    (repo/'.gitignore').write_text('projects/*/reference/\n')
    git(repo,'init','-q');git(repo,'add','.');git(repo,'commit','-qm','Synthetic project')
    baseline=root/'baseline.json';baseline.write_text(json.dumps({'checks':[
        {'target':t,'exit_code':0} for t in ('project-inventory','project-verify','project-process-check','project-docs-check')]}))
    producer.EXE=Path(os.environ['STRUCTURED_PASS_XASM']).resolve()
    model,_=certify(repo/SOURCE,root/'capture',repo/REFERENCE)
    profile={'schema':'current-project-profile-v1','slug':'sample','source':SOURCE,'reference':REFERENCE,
        'source_sha256':digest(model.source),'base_commit':git(repo,'rev-parse','HEAD'),
        'baseline_path':str(baseline),'baseline_sha256':producer.sha(baseline),
        'producer_path':str(producer.EXE),'producer_sha256':producer.sha(producer.EXE),'pass_id':'1',
        'objective':'Synthetic rename and repair','next_pass_sha256':producer.sha(docs/'inventory/pass/next_pass.json'),
        'pass_plan_sha256':producer.sha(docs/'inventory/pass/current_pass_plan.json')}
    common.write_json(root/'profile.json',profile)
    toolchain=producer.EXE.parent;store=root/'store';destination=store/'toolchains'/producer.sha(producer.EXE)
    destination.mkdir(parents=True)
    for name in ('xasm','REBUILD-v2.json','source.tar.gz','local.patch'):shutil.copy2(toolchain/name,destination/name)
    return Corridor.initialize(root/'session',repo,root/'capture',store,run_id='sample-pass-1',
        objective=profile['objective'],project_profile=root/'profile.json')


def closeout_ops(controller,generation,notes='Synthetic lifecycle exercise.'):
    info=controller.editor.documents(generation)
    return [{'kind':'scorecard_update','pass_id':'1','preimage':info['scorecard']['preimage'],
             'fields':{'focus':'Synthetic corridor','notes':notes}},
            {'kind':'closeout','pass_id':'1','deferrals_preimage':info['deferrals']['preimage'],'deferrals':[],'rework_items':0}]


def rename_ops(controller,generation):
    m=controller.editor.model(generation);n=m.declarations['Cell']
    return [{'kind':'rename','declaration_id':m.ids[n],'old_name':'Cell','new_name':'Capacity',
             'preimage':m.statement(n)['preimage_sha256']},
            {'kind':'ledger_append','path':controller.editor.ledger,
             'preimage':controller.editor.state['generations'][generation]['manifest'][controller.editor.ledger],
             'rows':[{'old_name':'Cell','new_name':'Capacity','reason':'Synthetic fixture','confidence':'high','pass_id':'1'}]},
            *closeout_ops(controller,generation)]
