"""Exact resource, sensor-normalization and reduction-error consequences."""
from interval_arithmetic import *
from pathlib import Path
import json
P=Path(__file__).resolve().parent
def atan_bounds(inv,n=80):
    v=sum((F((-1)**k,(2*k+1)*inv**(2*k+1)) for k in range(n)),F())
    nxt=F((-1)**n,(2*n+1)*inv**(2*n+1))
    return I(min(v,v+nxt),max(v,v+nxt))
def run():
    full=json.loads((P/'compressed_attracting_certificate.json').read_text())
    red=json.loads((P/'attracting_reduction_certificate.json').read_text())
    x=list(map(F,full['source']['x']));q=list(map(F,full['source']['q']))
    et=x[4]+sum(x[6:9]);ft=x[5]+sum(x[9:]);st=sum(x[:4])+sum(x[6:])
    pi=16*atan_bounds(5)-4*atan_bounds(239)
    omega=I(*full['omega_interval']);T=2*pi/omega;Q=T*sum(q)
    a=-I(*full['crossing_interval']);l1=I(*full['lyapunov_interval'])
    eig=[C(I(*v['real']),I(*v['imag'])) for v in full['extra']['right_eigenvector']]
    sensors={'free_S3':eig[2]-eig[8],'total_S3':eig[2],'D1':eig[6]}
    coeff={k:4*(v.re*v.re+v.im*v.im).sqrt()*(a/(-omega*l1)).sqrt() for k,v in sensors.items()}
    errs={k:I(*full[old])-I(*red[k]) for k,old in [('r','r_interval'),('omega','omega_interval'),('l1','lyapunov_interval')]}
    assert errs['r'].a>0 and errs['r'].b<F('0.0024')
    assert errs['omega'].a>0 and errs['omega'].b<F('0.000619')
    assert abs(errs['l1'].a)<F('0.000279') and abs(errs['l1'].b)<F('0.000279')
    rr=[I('1/100')]*6;rr[3]=I(*full['r_interval'])
    cat=[q[j%3]/x[6+j] for j in range(6)]
    bind=[(1+rr[j])*q[j%3]/x[[0,1,2,1,2,3][j]]/x[4+j//3] for j in range(6)]
    uni=[rr[j]*cat[j] for j in range(6)]+list(map(I,cat))
    # Verify max/min indices with separated interval comparisons.
    assert all(bind[4].a>=v.b for k,v in enumerate(bind) if k!=4)
    assert all(bind[0].b<=v.a for v in bind[1:])
    result={'evidence':'C+I; rational source balances, Machin alternating-series pi enclosure, inherited Hopf intervals',
      'totals':dict(E=str(et),F=str(ft),S=str(st)),
      'loading':dict(E_over_S=str(et/st),F_over_S=str(ft/st),bound_E=str(sum(x[6:9])/et),bound_F=str(sum(x[9:])/ft)),
      'catalytic_span':str(max(cat)/min(cat)), 'binding_span':(bind[4]/bind[0]).bounds(),
      'all_unimolecular_span':(I(max(cat))/min(uni,key=lambda z:z.a)).bounds(),
      'pi':pi.bounds(),'period':T.bounds(),'turnover':Q.bounds(),'turnover_per_substrate':(Q/st).bounds(),
      'amplitude_coefficient':{k:v.bounds() for k,v in coeff.items()},'radial_recovery_coefficient':(2*a).bounds(),
      'reduction_errors':{k:v.bounds() for k,v in errs.items()},
      'rates':{'binding':[v.bounds() for v in bind],'dissociation':[(rr[j]*cat[j]).bounds() for j in range(6)],'catalytic':list(map(str,cat))},
      'summary':{'T':T.approx(),'Q':Q.approx(),'Q_per_S':(Q/st).approx(),'amplitude_coefficients':{k:v.approx() for k,v in coeff.items()}}}
    (P/'resource_certificate.json').write_text(json.dumps(result,indent=2));print(json.dumps(result['summary'],indent=2))
if __name__=='__main__':run()
