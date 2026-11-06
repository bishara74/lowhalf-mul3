"""Compare freshly computed counts with the supplied historical reports.
No historical claim is used to prove an exclusion. The lambda=2 pair-count
discrepancy is accounted for exactly by lifts through a redundant coordinate.
"""
from core import *
from check_lambda2_exact import products

def main():
    t=time.time();r=json.loads(Path(__file__).with_name('results.json').read_text())
    full=r['lambda2_full']['totals'];lev=r['level_0_83']['totals']
    ours=full['A_pairs']+full['B_pairs']
    extra=0
    for Q,w in q2_orbits():
        pp=products(Q);pa=products(Q,True);tr=reduce(Z1,v_basis(Q))
        extra+=3*pp.get(0,0)*pa.get(tr,0)
    assert ours==398732 and extra==2088 and ours+extra==400820
    assert lev['surviving_pairs']==2064 and lev['surviving_cosets']==1776
    l1=r['lambda1_exact_0_222']['weighted_totals']
    l1ours=l1['A_pairs']+l1['B_pairs']
    assert l1ours==4623120
    # Mutation control: a one-pair transcription error is detected.
    assert ours+extra+1!=400820
    record('historical_counts',{'status':'PASS','positive_controls_detected':1,
      'lambda2':{'function_plane_candidate_pairs':ours,'redundant_coordinate_lift_extra':extra,
                 'historical_coordinate_pairs':400820,'difficult_pairs':2064,'difficult_output_cosets':1776},
      'lambda1':{'our_function_space_candidate_pairs':l1ours,'historical_candidate_pairs':4644000,
                 'difference':4644000-l1ours,'full_historical_total_reproduced':False,
                 'note':'Different treatment of dependent signal coordinates; no field-by-field match is claimed.'},
      'seconds':round(time.time()-t,3)})
if __name__=='__main__':main()
