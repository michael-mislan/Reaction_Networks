"""Auditable outward-rounded dyadic rational arithmetic; adapted from the inherited certificate. Not Lean."""
from fractions import Fraction as F
from math import isqrt
import sympy as s
t=s.Symbol('t')
def eo(cs):
    E=0; O=0
    for i,c in enumerate(cs):
        k=len(cs)-1-i
        if k%2: O+=s.Rational(c)*(-1)**((k-1)//2)*t**((k-1)//2)
        else: E+=s.Rational(c)*(-1)**(k//2)*t**(k//2)
    return E,O
BITS=160; SCALE=1<<BITS
class I:
    def __init__(self,a=0,b=None):
        if isinstance(a,I):self.a,self.b=a.a,a.b;return
        self.a=F(a);self.b=F(a if b is None else b)
    @staticmethod
    def rounded(a,b):
        return I(F((a*SCALE).__floor__(),SCALE),F((b*SCALE).__ceil__(),SCALE))
    def __add__(self,v):
        v=I(v);return I.rounded(self.a+v.a,self.b+v.b)
    __radd__=__add__
    def __neg__(self):return I(-self.b,-self.a)
    def __sub__(self,v):return self+-I(v)
    def __rsub__(self,v):return I(v)+-self
    def __mul__(self,v):
        v=I(v);p=[a*b for a in (self.a,self.b) for b in (v.a,v.b)]
        return I.rounded(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(self,v):
        v=I(v);assert v.a>0 or v.b<0,(float(v.a),float(v.b))
        return self*I.rounded(1/v.b,1/v.a)
    def __rtruediv__(self,v):return I(v)/self
    def sqrt(self):
        assert self.a>0
        lo=isqrt((self.a*SCALE*SCALE).__floor__())
        hi=isqrt((self.b*SCALE*SCALE).__ceil__())+1
        return I(F(lo,SCALE),F(hi,SCALE))
    def bounds(self):return [str(self.a),str(self.b)]
    def approx(self):return [float(self.a),float(self.b)]
class C:
    def __init__(self,a=0,b=0):
        if isinstance(a,C):self.re,self.im=a.re,a.im;return
        self.re,self.im=I(a),I(b)
    def __add__(self,v):v=C(v);return C(self.re+v.re,self.im+v.im)
    __radd__=__add__
    def __neg__(self):return C(-self.re,-self.im)
    def __sub__(self,v):return self+-C(v)
    def __rsub__(self,v):return C(v)+-self
    def __mul__(self,v):
        v=C(v);return C(self.re*v.re-self.im*v.im,self.re*v.im+self.im*v.re)
    __rmul__=__mul__
    def __truediv__(self,v):
        v=C(v);den=v.re*v.re+v.im*v.im
        return C((self.re*v.re+self.im*v.im)/den,(self.im*v.re-self.re*v.im)/den)
    def conj(self):return C(self.re,-self.im)
    def size(self):return float(self.re.a+self.re.b)**2+float(self.im.a+self.im.b)**2
def solve(A,b):
    n=len(b);a=[[C(v) for v in row]+[C(rhs)] for row,rhs in zip(A,b)]
    for j in range(n):
        k=max(range(j,n),key=lambda k:a[k][j].size());a[j],a[k]=a[k],a[j]
        pivot=a[j][j]
        a[j]=[v/pivot for v in a[j]]
        for k in range(n):
            if k==j:continue
            fac=a[k][j];a[k]=[u-fac*v for u,v in zip(a[k],a[j])]
    return [row[-1] for row in a]
def dot(a,b):return sum((u*v for u,v in zip(a,b)),C())

def solve_preconditioned(A,b):
    """Certified midpoint preconditioning and a Neumann residual enclosure."""
    import numpy as np
    A=[[C(v) for v in row] for row in A];b=list(map(C,b));n=len(b)
    mid=lambda v: complex(float((v.re.a+v.re.b)/2),float((v.im.a+v.im.b)/2))
    ah=np.array([[mid(v) for v in row] for row in A]);bh=np.array([mid(v) for v in b])
    inv=np.linalg.inv(ah);xc=np.linalg.solve(ah,bh)
    rat=lambda z:C(I(F(round(float(z.real)*10**14),10**14)),I(F(round(float(z.imag)*10**14),10**14)))
    R=[[rat(v) for v in row] for row in inv];x=list(map(rat,xc))
    ab=lambda z:max(abs(z.re.a),abs(z.re.b))+max(abs(z.im.a),abs(z.im.b))
    E=[[C(int(i==j))-dot(R[i],[A[k][j] for k in range(n)]) for j in range(n)] for i in range(n)]
    eta=max(sum(ab(v) for v in row) for row in E);assert eta<1
    residual=[b[i]-dot(A[i],x) for i in range(n)]
    radius=max(ab(dot(row,residual)) for row in R)/(1-eta)
    return [C(v.re+I(-radius,radius),v.im+I(-radius,radius)) for v in x]
def peval(cs,x):
    out=type(x)(0)
    for c in cs:out=out*x+type(x)(str(c))
    return out
def ipoly(expr,iv):return peval(s.Poly(expr,t).all_coeffs(),iv)

