"""Exact right-inverse replay and numerical straight-path actuator diagnostic."""
import sys,json
from pathlib import Path
import numpy as np
import sympy as s
W=Path(__file__).resolve().parent
sys.path.insert(0,str(W.parent/'RAF_phosphorylation_generalized_oscillation_beer_game'))
import preparation_pilot as p

def main():
    N=s.Matrix(p.N);R=s.Matrix(p.RCH.astype(int));P=s.Matrix(p.lift().astype(int));M=R*N
    _,cols=M.rref();K=s.zeros(18,9);inv=M[:,list(cols)].inv()
    for i,c in enumerate(cols):K[c,:]=inv[i,:]
    nu=s.Matrix([2,1,1]*6)
    assert M*K==s.eye(9) and N*K==P and N*nu==s.zeros(12,1)
    (W/'control_right_inverse.json').write_text(json.dumps({'evidence':'exact rational identities','selected_columns':cols,'K':[[str(v) for v in row] for row in K.tolist()],'positive_kernel_flux':list(map(int,nu)),'RNK_equals_identity':True,'NK_equals_P':True,'Nnu_equals_zero':True},indent=2))
    a=np.load(W/'finite_t0.7_factor1.3.npz');start=a['xstar'];d=a['y'][:,0];finish=start+p.lift()@d
    rows=[]
    for name,x0,dd in [('ON',start,d),('OFF',finish,-d)]:
        h=np.array(K,float)@dd;Q=1+max(abs(h));v=Q*np.array(nu,float).ravel()+h
        path=x0[:,None]+p.lift()@dd[:,None]*np.linspace(0,1,101)[None,:]
        mon=np.empty((18,101));mon[0::3]=path[p.LEVEL]*path[4+p.EN];mon[1::3]=path[6:];mon[2::3]=path[6:]
        rates=v[:,None]/mon
        rows.append({'name':name,'duration':1,'constant_flux':v.tolist(),'Q':float(Q),'rate_min':float(rates.min()),'rate_max':float(rates.max()),'path_min_species':float(path.min()),'field_identity_error':float(np.max(abs(p.N@(rates*mon)-(p.lift()@dd)[:,None]))),'endpoint':path[:,-1].tolist(),'destination':'numerical cycle phase point' if name=='ON' else 'exact baseline equilibrium','destination_validation':'ON basin unvalidated at this finite pilot; existential theorem uses the proved actual cycle'})
    (W/'control_pilot.json').write_text(json.dumps({'evidence':'exact right-inverse algebra plus N finite-path diagnostic','protocols':rows},indent=2));print(json.dumps(rows,indent=2))
if __name__=='__main__':main()
