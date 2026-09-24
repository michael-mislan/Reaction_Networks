"""Independent literal-reaction construction, separate from the block builder."""
import sympy as s
from pathlib import Path
import json
import preparation_pilot as p

def run():
    root=Path(__file__).parent;rows=[]
    for name in ['one_pool','closed','attracting','compressed_attracting']:
        data=json.loads((root/(name+'_certificate.json')).read_text());src=data['source']
        x=s.Matrix(list(map(s.Rational,src['x'])));q=list(map(s.Rational,src['q']))
        ke=0 if name=='one_pool' else 1
        P=s.Matrix(p.lift(ke,1)).applyfunc(lambda z:s.Rational(int(z)))
        proj=s.Matrix(p.RCH).applyfunc(lambda z:s.Rational(int(z)))
        N=s.Matrix(p.N);Y=s.Matrix(p.Y)
        assert proj*P==s.eye(9)
        for rr in [0,1,2]:
            ratios=[s.Rational(1,100)]*6;ratios[3]=s.Rational(rr)
            flux=[];binding=[]
            for j in range(6):
                v=(1+ratios[j])*q[j%3]
                flux.extend([v,v-q[j%3],q[j%3]])
                binding.append(v/x[int(p.LEVEL[j])]/x[4+int(p.EN[j])])
            assert N*s.Matrix(flux)==s.zeros(12,1)
            full=N*s.diag(*flux)*Y.T*s.diag(*[1/v for v in x])
            direct=proj*full*P
            expected=[s.Rational(a)+rr*s.Rational(b) for a,b in zip(src['p0'],src['p1'])]
            assert direct.charpoly().all_coeffs()==expected
            # Literal binding Hessians: project each stoichiometric column.
            for j in range(6):
                si=int(p.LEVEL[j]);ei=4+int(p.EN[j]);col=proj*N[:,3*j]
                assert col==s.eye(9)[:,3+j]
                if j<3 and not ke:assert P[ei,:]==s.zeros(1,9)
                B=binding[j]*(P[si,:].T*P[ei,:]+P[ei,:].T*P[si,:])
                # The source chart substrate row and enzyme row used in certificates.
                expected_s=s.Matrix([[int(p.T[si,k]) if k<3 else -int(p.LEVEL[k-3]==si) for k in range(9)]])
                expected_e=s.Matrix([[0 if k<3 else -int((k-3)//3==j//3)*(ke if j<3 else 1) for k in range(9)]])
                assert B==binding[j]*(expected_s.T*expected_e+expected_e.T*expected_s)
        rows.append({'source':name,'exact_equilibrium':True,'chart_inverse':True,'literal_characteristic_at_0_1_2':True,'literal_hessian':True})
    # Exact stated error bounds, without comparing rounded decimals.
    from fractions import Fraction as F
    full=json.loads((root/'closed_certificate.json').read_text());red=json.loads((root/'nonlinear_reduction_certificate.json').read_text())
    errors={}
    for fk,rk,bound in [('r_interval','r','131/1000000'),('omega_interval','omega','43/1000000'),('lyapunov_interval','l1','357/1000000')]:
        fa,fb=map(F,full[fk]);ra,rb=map(F,red[rk]);error=max(abs(fa-rb),abs(fb-ra));assert error<F(bound)
        errors[rk]=str(error)
    assert s.Rational(full['source']['p0'][-1])>0 and s.Rational(full['source']['p1'][-1])>=0
    report={'evidence':'exact rational independent reaction-list audit','sources':rows,'reduction_error_upper':errors,'no_zero_root_for_positive_r':True}
    (root/'literal_source_audit.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':run()
