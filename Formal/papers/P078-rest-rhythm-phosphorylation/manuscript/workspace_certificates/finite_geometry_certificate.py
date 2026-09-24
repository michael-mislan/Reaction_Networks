"""Directed bounds for finite sink, orbit positivity, readout and period."""
from pathlib import Path
import json
import numpy as np
from mpmath import iv
from finite_source import coefficients
from local_certificate import P
W=Path(__file__).resolve().parent

def main():
    iv.dps=55;a=np.load(W/'fourier_N40.npz');c=np.load(W/'finite_fourier_inverse.npz')
    cert=json.loads((W/'finite_fourier_certificate.json').read_text());rho=iv.mpf(cert['radius'])
    J,B,scales=coefficients(a);z=c['z'];N=40;JI=iv.matrix(J)
    H=iv.eye(9);cs=[iv.mpf(1)]
    for k in range(1,10):
        H=JI*H;v=-sum((H[i,i] for i in range(9)),iv.mpf(0))/k;cs.append(v);H+=v*iv.eye(9)
    rows=[cs[0::2],cs[1::2]]
    for k in range(2,10):
        prev,cur=rows[-2:];rows.append([(cur[0]*prev[j+1]-prev[0]*cur[j+1])/cur[0] for j in range(4)]+[iv.mpf(0)])
    assert all(row[0].a>0 for row in rows)
    Z=[[iv.mpc(float(v.real),float(v.imag))*scales[j] for j,v in enumerate(row)] for row in z]
    lifted=[[sum((P[i][j]*row[j] for j in range(9)),iv.mpc(0)) for i in range(12)] for row in Z]
    variation=[sum((abs(k-N)*abs(lifted[k][i]).b for k in range(2*N+1)),iv.mpf(0)) for i in range(12)]
    err=[max(abs(P[i][j]*scales[j]).b for j in range(9))*rho for i in range(12)]
    x=list(map(iv.mpf,a['xstar']));grid=128;values=[];sensor=[]
    for n in range(grid):
        phase=2*iv.pi*n/grid
        exp=[iv.mpc(iv.cos((k-N)*phase),iv.sin((k-N)*phase)) for k in range(2*N+1)]
        point=[x[i]+sum((lifted[k][i]*exp[k] for k in range(2*N+1)),iv.mpc(0)).real for i in range(12)]
        values.append(point)
        sensor.append(point[3]+point[11])
    lower=[min(v[i].a for v in values)-variation[i]*iv.pi/grid-err[i] for i in range(12)]
    assert all(v.a>0 for v in lower)
    # At named grid phases the actual readout error is at most max|scale*u3|rho.
    sensorerr=abs(scales[2])*rho
    peak=max(v.a for v in sensor);trough=min(v.b for v in sensor)
    amplitude=peak-trough-2*sensorerr
    assert amplitude.a>2
    omega=iv.mpf(float(c['omega']))+iv.mpf([-1,1])*iv.mpf(float(.2))*rho
    period=2*iv.pi/omega
    totals=[x[4]+sum(x[6:9]),x[5]+sum(x[9:12]),sum(x[:4])+sum(x[6:])]
    result={'evidence':'directed interval finite geometry; attraction separately certified','sink_hurwitz':True,'sink_routh_first_column':[str(row[0]) for row in rows],'species_global_lower_bounds':[str(v) for v in lower],'S3_plus_D3_peak_to_peak_lower':str(amplitude),'period':str(period),'totals':[str(v) for v in totals],'grid_nodes':grid,'between_nodes_bound':'global Fourier derivative times pi/128 plus validated Fourier-ball lift radius','same_source':'exact dyadic xstar,currents,r in fourier_N40.npz; ratios other than r exactly 1/100'}
    (W/'finite_geometry_certificate.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
