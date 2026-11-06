"""Reproduce the fresh referee checks and collect their machine-readable results.
Use --collect-only to consolidate a completed run without repeating it.
"""
import hashlib,json,subprocess,sys
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent
SCRIPTS=['algebra','structure','quadratic_products','weights_and_product4','multipliers','ordinary_products','feedback_and_early','conditioned_products','source_audit']
MINOR={
 'l3:lem:D1':'The exterior projection is written with target Lambda(U*) although U was defined as a space of linear forms; use Lambda(U).',
 'l3:lem:P':'P1 uses a nonconstant affine l in exterior expressions without specifying its linear part.',
 'l3:prop:B':'State dim Q3=3 explicitly for the direct application of the four-dimensional theorem, or extend Q\u2032.',
 'l3:lem:pl':'Producing [I2|M] needs invertible row reduction as well as a column permutation.',
 'l1:lem:cubic':'Handle dependent factor functions modulo constants before asserting the affine factor B is nonzero.'
}

def passing(data): return data.get('status')=='pass' and bool(data.get('positive_controls_detected',data.get('positive_control_detected',False)))
# Positive control: a planted failing check and a missing positive control are rejected.
assert not passing({'status':'fail','positive_controls_detected':True})
assert not passing({'status':'pass'})
if '--collect-only' not in sys.argv:
 for name in SCRIPTS:
  subprocess.run([sys.executable,str(HERE/(name+'.py'))],check=True,cwd=HERE.parent)
checks={name:json.loads((HERE/(name+'.json')).read_text()) for name in SCRIPTS}
assert all(passing(v) for v in checks.values())
scope=checks['source_audit']['in_scope_results']
for result in scope:
 result['classification']='MINOR' if result['label'] in MINOR else 'OK'
 result['finding']=MINOR.get(result['label'])
summary={k:sum(r['classification']==k for r in scope) for k in ['OK','MINOR','GAP','FALSE']}
assert summary=={'OK':31,'MINOR':5,'GAP':0,'FALSE':0}
source=HERE.parent/'source.tex'
assert hashlib.sha256(source.read_bytes()).hexdigest()==checks['source_audit']['source_sha256']
manifest={
 'audited_source':'../source.tex',
 'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'scope':'Sections Three linear gates, Two linear gates, One linear gate',
 'summary':summary,'results':scope,'checks':checks,
 'whole_paper_logic':{'normal_form':'OK by reading','lambda_5_to_1_exhaustive':'OK by reading','circular_dependency_found':False,'lambda_4':'Assumed as requested; later hypotheses checked'},
 'method_limits':['Not a formal proof checker.','The general six-variable quadratic product lemma was read; random tests supplement that proof, not replace it.','No independent full five-gate circuit search was performed.','Existing workspace proofs, reports, and scripts were not read or reused.'],
 'script_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in HERE.glob('*.py')},
 'collector_positive_controls_detected':2
}
(HERE/'results.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'summary':summary,'all_checks_passed':True,'results_file':str(HERE/'results.json')}))
