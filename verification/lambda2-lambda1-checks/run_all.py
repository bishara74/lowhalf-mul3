"""Run every required exhaustive check sequentially, <=30 minutes per script.
A failed check stops the run. Every child must report a detected positive control.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,time
HERE=Path(__file__).resolve().parent
JOBS=[
 ('check_algebra_symmetry.py','algebra_symmetry'),
 ('check_replacement.py','replacement'),
 ('check_degree.py','degree_structure'),
 ('check_annihilator.py','annihilator_four_factors'),
 ('check_final_factor.py','final_factor'),
 ('check_two_feedback.py','two_feedback'),
 ('check_reordering.py','rank_two_reordering'),
 ('check_ideal_extraction.py','ideal_extraction'),
 ('check_rank_exterior.py','rank_exterior'),
 ('check_one_high_space.py','one_high_space'),
 ('check_lambda1_normal_form.py','lambda1_cubic_normal_form'),
 ('check_early_core.py','early_core'),
 ('check_core_cubic.py','core_cubic'),
 ('check_ordinary_pair.py','ordinary_pair'),
 ('check_noncore_multiplier.py','noncore_multiplier'),
 ('check_noncore_onehigh.py','noncore_onehigh'),
 ('explore_prefixes.py','prefix_census'),
 ('check_screen_bruteforce.py','screen_bruteforce'),
 ('check_lambda2_exact.py','lambda2_exact_0_83'),
 ('check_lambda2_full.py','lambda2_full'),
 ('check_lambda1_exact.py','lambda1_exact_0_222'),
 ('check_level_survivors.py','level_0_83'),
 ('check_historical_counts.py','historical_counts'),
 ('check_quotient_witness.py','quotient_witness'),
]

def main():
    t=time.time();completed=[]
    for script,key in JOBS:
        log=HERE/(script.removesuffix('.py')+'.log')
        print('RUN',script,flush=True)
        with log.open('w') as stream:
            subprocess.run([sys.executable,str(HERE/script)],cwd=HERE.parent,
                           stdout=stream,stderr=subprocess.STDOUT,timeout=1800,check=True)
        result=json.loads((HERE/'results.json').read_text())[key]
        assert result['status']=='PASS',(key,result)
        pc=result.get('positive_controls_detected',result.get('representative_totals',{}).get('positive_controls_detected',0))
        assert pc>0,(key,'no positive control')
        completed.append(key)
    results=json.loads((HERE/'results.json').read_text())
    results.pop('level_0_1',None)
    results['run_all']={'status':'PASS','checks':completed,'positive_controls_detected':len(completed),
        'seconds':round(time.time()-t,3),
        'script_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in HERE.glob('*.py')}}
    (HERE/'results.json').write_text(json.dumps(results,indent=2,sort_keys=True)+'\n')
    print('PASS:',len(completed),'checks;',round(time.time()-t,3),'seconds',flush=True)
if __name__=='__main__':main()
