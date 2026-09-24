"""Exact-rational certification kit: interval arithmetic, rigorous rational
log bounds, Chernoff-KL confidence sets, and the two target evaluators."""
from fractions import Fraction as Q
from math import isqrt, log

# ---------------------------------------------------------------- intervals
class I:
    __slots__=('a','b')
    def __init__(s,a,b=None):
        s.a=Q(a); s.b=s.a if b is None else Q(b)
        assert s.a<=s.b,(s.a,s.b)
    def __add__(s,t): t=iv(t); return I(s.a+t.a,s.b+t.b)
    __radd__=__add__
    def __neg__(s): return I(-s.b,-s.a)
    def __sub__(s,t): return s+(-iv(t))
    def __rsub__(s,t): return iv(t)+(-s)
    def __mul__(s,t):
        t=iv(t); v=[s.a*t.a,s.a*t.b,s.b*t.a,s.b*t.b]; return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(s,t):
        t=iv(t)
        if t.a<=0<=t.b: raise ZeroDivisionError('denominator interval contains 0')
        return s*I(Q(1,1)/t.b,Q(1,1)/t.a)
    def __rtruediv__(s,t): return iv(t)/s
    def width(s): return s.b-s.a
    def pair(s): return [float(s.a),float(s.b)]
    def __repr__(s): return '[%.12g, %.12g]'%(float(s.a),float(s.b))
def iv(x): return x if isinstance(x,I) else I(x)

def sqrt_up(q,scale=10**12):
    q=Q(q); return Q(isqrt(q.numerator*scale*scale//q.denominator)+1,scale)

# ------------------------------------------------- rigorous rational log(x)
def _round_out(x,den=10**18):
    n=(x*den); lo=Q(n.numerator//n.denominator,den); return lo,lo+Q(1,den)

def _artanh_series(y,terms):
    """Two-sided rational bounds on log(y) = 2*artanh((y-1)/(y+1))."""
    z=(y-1)/(y+1); z2=z*z; s=Q(0); zp=z
    for k in range(1,2*terms,2):
        s+=zp/k; zp*=z2
    tail=abs(zp)/((2*terms+1)*(1-z2))
    return 2*(s-tail),2*(s+tail)

LOG2_LO,LOG2_HI=_artanh_series(Q(2),60)   # z = 1/3, error below 10**-56

def log_bounds(x,terms=20):
    """(lo,hi) with lo <= log(x) <= hi for positive rational x, exact rationals.
    The argument is reduced to [2/3,4/3] by exact halving before the series,
    so the enclosure stays tight for arguments far from one."""
    x=Q(x); assert x>0
    k=0
    while x>=Q(4,3): x/=2; k+=1
    while x<Q(2,3):  x*=2; k-=1
    xl,xh=_round_out(x)
    lo,_=_artanh_series(xl,terms); _,hi=_artanh_series(xh,terms)
    if k>=0: return lo+k*LOG2_LO, hi+k*LOG2_HI
    return lo+k*LOG2_HI, hi+k*LOG2_LO

def kl_lower(phat,p):
    """Rigorous rational lower bound on kl(phat||p) = binary relative entropy."""
    phat=Q(phat); p=Q(p)
    assert 0<p<1
    out=Q(0)
    if phat>0: out+=phat*log_bounds(phat/p)[0]
    if phat<1: out+=(1-phat)*log_bounds((1-phat)/(1-p))[0]
    return out

def kl_float(a,p):
    a=float(a); p=float(p)
    t=0.0
    if a>0: t+=a*log(a/p)
    if a<1: t+=(1-a)*log((1-a)/(1-p))
    return t

# --------------------------------------------- certified Chernoff-KL sets
def kl_interval(phat,n,L,step=Q(1,10**9)):
    """Certified outer enclosure of C = {p in (0,1): n*kl(phat||p) <= L}.
    Returns rational [lo,hi] with C subset [lo,hi]; endpoints are verified by
    exact rational evaluation of a lower bound on kl."""
    phat=Q(phat); L=Q(L); thr=L/n
    f=lambda p: kl_float(phat,p)
    def bisect(lo,hi,want_upper):
        # find root of f(p)=thr on monotone side, float bisection
        for _ in range(200):
            mid=(lo+hi)/2
            if (f(mid)>thr)==want_upper: hi=mid
            else: lo=mid
        return hi if want_upper else lo
    ph=float(phat)
    hi0=bisect(ph,1-1e-15,True) if ph<1 else 1.0
    lo0=bisect(1e-15,ph,False) if ph>0 else 0.0
    # outward rational candidates, then certify
    def certify(cand,direction):
        cand=Q(cand)
        for _ in range(80):
            if 0<cand<1 and n*kl_lower(phat,cand)>=thr: return cand
            cand=cand+direction*step
            if cand<=0: return Q(0)
            if cand>=1: return Q(1)
        raise RuntimeError('KL endpoint certification failed')
    hi=Q(1) if ph>=1 else certify(Q(int(hi0*10**9)+1,10**9),+1)
    lo=Q(0) if ph<=0 else certify(Q(int(lo0*10**9),10**9),-1)
    return I(max(Q(0),lo),min(Q(1),hi))

def hoeffding_interval(phat,n,L):
    r=sqrt_up(Q(L,2*n))
    return I(max(Q(0),Q(phat)-r),min(Q(1),Q(phat)+r))

def kl_ball_hat(p,n,L,step=Q(1,10**9)):
    """Certified outer enclosure of {phat: n*kl(phat||p) <= L} (first argument)."""
    p=Q(p); thr=Q(L)/n
    f=lambda a: kl_float(a,p)
    def bisect(lo,hi,want_upper):
        for _ in range(200):
            mid=(lo+hi)/2
            if (f(mid)>thr)==want_upper: hi=mid
            else: lo=mid
        return hi if want_upper else lo
    pf=float(p)
    hi0=bisect(pf,1.0,True); lo0=bisect(0.0,pf,False)
    def certify(cand,direction):
        cand=Q(cand)
        for _ in range(80):
            if 0<=cand<=1 and kl_lower(cand,p)>=thr: return cand
            cand=cand+direction*step
            if cand<=0: return Q(0)
            if cand>=1: return Q(1)
        raise RuntimeError('KL ball certification failed')
    hi=certify(Q(int(hi0*10**9)+1,10**9),+1); lo=certify(Q(int(lo0*10**9),10**9),-1)
    return I(max(Q(0),lo),min(Q(1),hi))

# ------------------------------------------------------------- evaluators
def evaluate(J,mu,eS,eT,lam,method):
    """J = 2x2 of intervals, mu, eS, eT intervals. Returns interval or None."""
    d=eT-eS
    if d.a<=0: return None
    if method=='matrix':
        L=[[eT/d,-(1-eT)/d],[-eS/d,(1-eS)/d]]
        LJ=[[sum((L[i][k]*J[k][j] for k in (0,1)),I(0)) for j in (0,1)] for i in (0,1)]
        M=[[sum((LJ[i][k]*L[j][k] for k in (0,1)),I(0)) for j in (0,1)] for i in (0,1)]
        det=M[0][0]*M[1][1]-M[0][1]*M[1][0]
        if det.a<=0: return None
        q=lam*((mu-eS)/d)*M[0][1]/det
    elif method=='cancelled':
        N=(-eT*eS*J[0][0]+eT*(1-eS)*J[0][1]
           +(1-eT)*eS*J[1][0]-(1-eT)*(1-eS)*J[1][1])
        det=J[0][0]*J[1][1]-J[0][1]*J[1][0]
        if det.a<=0: return None
        q=lam*(mu-eS)*N/(d*det)
    else: raise ValueError(method)
    return I(max(Q(0),q.a),max(Q(0),q.b))
