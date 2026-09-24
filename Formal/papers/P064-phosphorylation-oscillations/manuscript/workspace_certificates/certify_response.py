"""Exact resonant gain law using rank-one dependence; interval evaluation."""
from interval_arithmetic import I,C,solve,dot,F
from certify_reduction import matrix
from pathlib import Path
import json

def run():
    root=json.loads(Path(__file__).with_name('closed_certificate.json').read_text())
    omega=I(*root['omega_interval']);rh=I(*root['r_interval'])
    J=matrix(0);D=matrix(1)-J
    z=C(0,omega)
    resolvent=[[(z if i==j else C())-C(I(str(J[i,j]))) for j in range(9)] for i in range(9)]
    y=solve(resolvent,[C(int(i==6)) for i in range(9)])
    vy=dot([C(I(str(D[6,j]))) for j in range(9)],y)
    results={}
    for name,cy in [('free_S3',y[2]-y[8]),('total_level3',y[2])]:
        K=-cy/vy/10
        # Squaring general intervals is safe here, endpoints exclude zero.
        mag=(K.re*K.re+K.im*K.im).sqrt()
        assert mag.a>0
        lower=mag* (1+rh)
        upper=mag* (1+rh+I('3/100'))
        results[name]={'K_re':K.re.bounds(),'K_im':K.im.bounds(),'K_abs':mag.bounds(),
                       'delta_gain_lower':str(lower.a),'delta_gain_upper':str(upper.b),
                       'readable_delta_gain':[float(lower.a),float(upper.b)]}
    out={'evidence':'I + exact Sherman-Morrison identity','delta_interval':'0 < delta <= 3/100','frequency':'original algebraic omega_H',
         'formula':'G(i omega_H,r_H+delta) = (1+r_H+delta) K / delta',
         'input':'small modulation of log(alpha1), all other rates and totals fixed',
         'outputs':'absolute concentration; units concentration per unit log-rate input','results':results,
         'scope':'steady linear sinusoidal response at specified frequency; lower bound on peak, not global peak upper bound'}
    Path(__file__).with_name('response_certificate.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v['readable_delta_gain'] for k,v in results.items()},indent=2))
if __name__=='__main__':run()
