"""Operator-owned current-project profile. No expected semantic answers or edit map.

The legacy service calls its base metadata a fixture. For this profile that file
contains only configured paths, input identities and the actual baseline gates.
It is outside both client workspaces and has no client write operation.
"""
import json
from pathlib import Path
import re
import shutil
import sys

HERE=Path(__file__).resolve().parent
from .rename_service import RenameService
from . import service as common
from .model import producer
from . import mixed_documents as mixed
ERRORS=frozenset(('PROJECT_PROFILE_INVALID','PROJECT_PROFILE_CHANGED'))
common.PUBLIC_ERROR_CODES|=ERRORS


def require(value,code='PROJECT_PROFILE_INVALID'):
    if not value:raise ValueError(code)


def service_class(path,expected=None):
    path=Path(path).resolve();profile=json.loads(path.read_text())
    require(expected is None or producer.sha(path)==expected,'PROJECT_PROFILE_CHANGED')
    common.schema(profile,('schema','slug','source','reference','source_sha256','base_commit',
        'baseline_path','baseline_sha256','producer_path','producer_sha256','pass_id','objective',
        'next_pass_sha256','pass_plan_sha256'))
    require(profile['schema']=='current-project-profile-v1')
    slug=profile['slug'];require(isinstance(slug,str) and re.fullmatch('[a-z0-9_]+',slug))
    project='projects/'+slug+'/'
    for key in ('source','reference'):
        value=profile[key];require(isinstance(value,str) and value.startswith(project)
            and not Path(value).is_absolute() and '..' not in Path(value).parts)
    for key in ('source_sha256','baseline_sha256','producer_sha256','next_pass_sha256','pass_plan_sha256'):
        require(isinstance(profile[key],str) and re.fullmatch('[a-f0-9]{64}',profile[key]))
    require(re.fullmatch('[a-f0-9]{40}',profile['base_commit']) is not None)
    require(isinstance(profile['pass_id'],str) and profile['pass_id'].isdigit())
    require(isinstance(profile['objective'],str) and bool(profile['objective'].strip()))
    baseline=Path(profile['baseline_path']).resolve();executable=Path(profile['producer_path']).resolve()
    require(producer.sha(baseline)==profile['baseline_sha256'],'PROJECT_PROFILE_CHANGED')
    require(producer.sha(executable)==profile['producer_sha256'],'PROJECT_PROFILE_CHANGED')
    checks=json.loads(baseline.read_text())['checks']
    require({c['target'] for c in checks}=={'project-inventory','project-verify','project-process-check','project-docs-check'}
        and all(c['exit_code']==0 for c in checks))
    # One fixed profile per bridge process; clients cannot choose an executable.
    producer.EXE=executable

    class ProjectService(RenameService):
        source=profile['source']
        reference=profile['reference']
        fixture_path=path
        baseline_path=baseline

        def document_pass_id(self):
            return profile['pass_id']

        def apply_authored(self,checkout,operations):
            super().apply_authored(checkout,operations)
            base=self.state['generations'][self.state['pass_start_generation']]
            relative=self.project+'docs/reverse_engineering/inventory/pass/current_pass_plan.json'
            plan=Path(base['checkout'])/relative
            require(producer.sha(plan)==profile['pass_plan_sha256'],'PROJECT_PROFILE_CHANGED')
            target=checkout/relative;target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(plan,target)

        def run_gates(self,checkout,operations,folder,env):
            if mixed.document_operations(operations) is None:
                return super().run_gates(checkout,operations,folder,env)
            return mixed.run_closeout(checkout,self.project,self.slug,operations,self.document_pass_id(),
                folder,env,checkout/'scripts',pass_plan_sha256=profile['pass_plan_sha256'])

    ProjectService.project=project
    ProjectService.slug=slug
    return ProjectService
