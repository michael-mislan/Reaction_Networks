"""Validated polynomial Taylor flow: ideal D1 assay under an association pulse."""
from interval_arithmetic import I,F
import preparation_pilot as p
from pathlib import Path
import json
import sys
P=Path(__file__).resolve().parent
xstar=list(map(F,['2','12','1/5','2/5','23/10','2/5','23/50','3/10','17/10','23','9/50','4']))
q=list(map(F,['1/10','32/5','6/5']))
lift=[[int(v) for v in row] for row in p.lift()]
def field(x,rates):
    out=[I() for _ in range(12)]
    for j in range(6):
        vals=[rates[3*j]*x[int(p.LEVEL[j])]*x[4+int(p.EN[j])],rates[3*j+1]*x[6+j],rates[3*j+2]*x[6+j]]
        for k,v in enumerate(vals):
            for i in range(12):
                if p.N[i,3*j+k]:out[i]+=int(p.N[i,3*j+k])*v
    return out
def jet(x,rates,order):
    co=[x]
    for n in range(order):
        v=[I() for _ in range(12)]
        for j in range(6):
            a=int(p.LEVEL[j]);e=4+int(p.EN[j])
            vals=[rates[3*j]*sum((co[k][a]*co[n-k][e] for k in range(n+1)),I()),rates[3*j+1]*co[n][6+j],rates[3*j+2]*co[n][6+j]]
            for k,z in enumerate(vals):
                for i in range(12):
                    if p.N[i,3*j+k]:v[i]+=int(p.N[i,3*j+k])*z
        co.append([z/(n+1) for z in v])
    return co
def step(x,rates,h,order=7):
    dx=field(x,rates)
    radius=[max(abs(v.a),abs(v.b))*h*2+F('1e-15') for v in dx]
    for retry in range(12):
        tube=[I(v.a-w,v.b+w) for v,w in zip(x,radius)]
        fs=field(tube,rates)
        if all(h*max(abs(v.a),abs(v.b))<w for v,w in zip(fs,radius)):break
        radius=[max(w*2,h*max(abs(v.a),abs(v.b))*2+F('1e-15')) for w,v in zip(radius,fs)]
    else:raise RuntimeError('Picard tube failed')
    a=jet(x,rates,order-1);last=jet(tube,rates,order)[order]
    end=[sum((a[k][i]*h**k for k in range(order)),I())+last[i]*h**order for i in range(12)]
    assert all(v.a>0 for v in tube)
    return end
def run():
    practical='--practical' in sys.argv
    prep=F('1e-5') if practical else F('1e-8')
    pulse=I('49/100','51/100') if practical else I('99/1000','101/1000')
    h=F('1/1000')
    results=[]
    for r in [F('13/10'),F('3/2')]:
        rr=[F('1/100')]*6;rr[3]=r
        rates=[]
        for j in range(6):rates.extend([I((1+rr[j])*q[j%3]/xstar[int(p.LEVEL[j])]/xstar[4+int(p.EN[j])]),I(rr[j]*q[j%3]/xstar[6+j]),I(q[j%3]/xstar[6+j])])
        rates[9]*=1+pulse
        x=[I(v-prep*sum(abs(k) for k in row),v+prep*sum(abs(k) for k in row)) for v,row in zip(xstar,lift)]
        rows=[]
        for k in range(1,101):
            x=step(x,rates,h)
            if k in [10,25,50,75,100]:rows.append({'time':str(k*h),'D1':x[9].bounds()})
        results.append({'r':str(r),'samples':rows})
    gaps=[]
    for aa,bb in zip(results[0]['samples'],results[1]['samples']):
        gap=F(bb['D1'][0])-F(aa['D1'][1]);gaps.append({'time':aa['time'],'gap':str(gap),'max_readout_error':str(gap/2),'gap_float':float(gap)})
    best=max(gaps,key=lambda x:F(x['gap']))
    out={'evidence':'I: exact outward rational Taylor remainder with Picard tube inclusion','prep_chart_linf':str(prep),'relative_pulse':pulse.bounds(),'step':str(h),'order':7,'results':results,'separations':gaps,'best':best}
    name='measurement_practical_certificate.json' if practical else 'measurement_certificate.json'
    (P/name).write_text(json.dumps(out,indent=2));print(json.dumps(gaps,indent=2))
if __name__=='__main__':run()
