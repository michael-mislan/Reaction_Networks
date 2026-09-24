"""Exact one-parameter Hurwitz determinant certificates using Bernstein positivity."""
from certify_reduction import matrix,reduced
import sympy as s
import json
from pathlib import Path

t=s.Symbol('t')
def positive_interval(poly,lo,hi):
    poly=s.Poly(poly,t);n=poly.degree()
    # (1+x)^n p((lo+hi*x)/(1+x)); positivity of coefficients suffices.
    x=s.Symbol('x')
    transformed=s.Poly(sum(c*(lo+hi*x)**k*(1+x)**(n-k) for (k,),c in poly.terms()),x)
    coeff=transformed.all_coeffs()
    return all(c>0 for c in coeff),list(map(str,coeff))

def certify(name,J,lo,hi):
    J=J+s.eye(J.rows)*s.Rational(1,10000)
    cs=J.charpoly().all_coeffs();n=J.rows;dets=[]
    for k in range(1,n+1):
        H=s.Matrix(k,k,lambda i,j:cs[2*j-i+1] if 0<=2*j-i+1<=n else 0)
        det=s.Poly(H.det(method='domain-ge'),t).as_expr()
        ok,co=positive_interval(det,lo,hi)
        dets.append({'order':k,'pass':ok,'polynomial':str(det),'positive_transform_coefficients':co})
    return {'name':name,'spectral_margin':'1/10000','interval':[str(lo),str(hi)],'pass':all(v['pass'] for v in dets),'characteristic_coefficients':list(map(str,cs)),'hurwitz':dets}

def main():
    cases=[('full_r',matrix(t),s.Rational(27,100),s.Rational(3,10)),
           ('retained_except_C2_r',reduced(matrix(t)),s.Rational(27,100),s.Rational(3,10)),
           ('full_speed_k',matrix(s.Rational(28,100),1/t),s.Rational(10,9),s.Rational(2))]
    rows=[]
    for args in cases:
        result=certify(*args);rows.append(result);print(result['name'],result['pass'],flush=True)
        Path(__file__).with_name('stability_intervals.json').write_text(json.dumps(rows,indent=2))
if __name__=='__main__':main()
