"""Second, independent computer-assisted proof of the finite-amplitude attracting periodic
orbit of the finite witness (Table 3 of the paper), by multiple shooting and the
Newton--Kantorovich theorem.  Adapted from the companion paper's validator; it shares no
code with the Fourier/variational certificates of the research workspace.

    python validate_orbit.py witness        (run after make_data.py)

Arithmetic: interval arithmetic in binary64 with outward rounding (np.nextafter after
every correctly rounded IEEE-754 operation).  Every acceptance condition is a strict
inequality between machine numbers.  Floating-point numbers computed without intervals
(the shooting nodes, the approximate inverse A, the Floquet frames Q_l) are only
candidates; the theorem uses them as exact dyadic rationals.

Output: certificates/orbit_certificate_<r>.json.
"""
import sys, json, time
from fractions import Fraction as Fr
from pathlib import Path
import numpy as np
import sympy as sp
from clock import finite_model
from companion_numerics import FloatModel

ROOT = Path(__file__).resolve().parent
INF = np.inf


# ----------------------------------------------------------------------------- intervals
def up(x): return np.nextafter(x, INF)
def dn(x): return np.nextafter(x, -INF)


class IA:
    """Interval arrays [lo, hi] with outward rounding."""
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        lo = np.asarray(lo, dtype=float)
        self.lo = lo; self.hi = lo.copy() if hi is None else np.asarray(hi, dtype=float)
        assert self.lo.shape == self.hi.shape and np.all(self.lo <= self.hi)

    @staticmethod
    def exact(x):
        return IA(np.asarray(x, dtype=float))

    @staticmethod
    def frac(x):
        """Enclosure of a rational (or list of rationals) by neighbouring binary64 numbers."""
        f = np.array([float(Fr(str(v))) for v in np.ravel(x)], dtype=float).reshape(np.shape(x))
        return IA(dn(f), up(f))

    @property
    def shape(self): return self.lo.shape
    def __getitem__(self, k): return IA(self.lo[k], self.hi[k])
    def __add__(self, o):
        o = o if isinstance(o, IA) else IA.exact(o)
        return IA(dn(self.lo + o.lo), up(self.hi + o.hi))
    __radd__ = __add__
    def __neg__(self): return IA(-self.hi, -self.lo)
    def __sub__(self, o):
        o = o if isinstance(o, IA) else IA.exact(o)
        return IA(dn(self.lo - o.hi), up(self.hi - o.lo))
    def __rsub__(self, o): return IA.exact(o) - self
    def __mul__(self, o):
        o = o if isinstance(o, IA) else IA.exact(o)
        p = np.stack([self.lo*o.lo, self.lo*o.hi, self.hi*o.lo, self.hi*o.hi])
        return IA(dn(p.min(axis=0)), up(p.max(axis=0)))
    __rmul__ = __mul__
    def mag(self): return np.maximum(np.abs(self.lo), np.abs(self.hi))
    def mid(self): return (self.lo + self.hi)/2
    def rad(self): return up(np.maximum(self.hi - self.mid(), self.mid() - self.lo))
    def hull(self, o): return IA(np.minimum(self.lo, o.lo), np.maximum(self.hi, o.hi))
    def contains(self, o): return np.all(self.lo <= o.lo) and np.all(o.hi <= self.hi)
    def inflate(self, rel, absr):
        r = up(up(self.rad()*rel) + absr)
        return IA(dn(self.lo - r), up(self.hi + r))
    def inflate_uniform(self, rel, absr, axes):
        """Inflate every entry by rel times the largest radius over the given trailing axes."""
        rad = self.rad()
        for ax in axes: rad = rad.max(axis=ax, keepdims=True)
        r = up(up(rad*rel) + absr)
        return IA(dn(self.lo - r), up(self.hi + r))
    def reshape(self, *s): return IA(self.lo.reshape(*s), self.hi.reshape(*s))
    def T(self): return IA(np.swapaxes(self.lo, -1, -2), np.swapaxes(self.hi, -1, -2))
    def swap(self, a, b): return IA(np.swapaxes(self.lo, a, b), np.swapaxes(self.hi, a, b))


def isum(x, axis):
    """Rigorous sum of an interval array along an axis."""
    n = x.shape[axis]
    acc = x[(slice(None),)*axis + (0,)]
    for k in range(1, n):
        acc = acc + x[(slice(None),)*axis + (k,)]
    return acc


def imatmul(A, B):
    """(..., n, k) @ (..., k, p) with rigorous accumulation."""
    prod = A[..., :, :, None]*B[..., None, :, :]
    return isum(prod, prod.lo.ndim - 2)


def imatvec(A, v):
    prod = A*v[..., None, :]
    return isum(prod, prod.lo.ndim - 1)


def stack(lst):
    return IA(np.stack([x.lo for x in lst]), np.stack([x.hi for x in lst]))


# ----------------------------------------------------------------------------- model
class Field:
    """y' = J y + q(y,y),  q(u,v)_{n+j} = kappa_j (s_j.u)(e_j.v);  DF(y) = J + Bmat(y)."""

    def __init__(self, model):
        self.n = model.n; d = 3*model.n; self.d = d
        self.J = IA.frac(np.array(model.jacobian().tolist(), dtype=object))
        rows = model.hessian_rows()
        self.S = IA.exact(np.array([[int(v) for v in r[0]] for r in rows]))    # (2n, d)
        self.E = IA.exact(np.array([[int(v) for v in r[1]] for r in rows]))
        self.kappa = IA.frac([r for r in model.kon])
        self.P = IA.exact(np.array(model.P.tolist(), dtype=float))
        self.xstar = IA.frac([v for v in model.x])
        self.Rm = np.array(model.Rm.tolist(), dtype=float)

    def q(self, u, v):
        """(..., d) x (..., d) -> (..., d): rows n.. are kappa (S u)(E v), pool rows 0."""
        su = imatvec(self.S, u); ev = imatvec(self.E, v)
        top = IA(np.zeros(u.lo.shape[:-1] + (self.n,)))
        return IA(np.concatenate([top.lo, (self.kappa*su*ev).lo], axis=-1),
                  np.concatenate([top.hi, (self.kappa*su*ev).hi], axis=-1))

    def F(self, y):
        return imatvec(self.J, y) + self.q(y, y)

    def Bmat(self, u):
        """matrix of B(u,.) = DF(u) - J, shape (..., d, d)."""
        su = imatvec(self.S, u); eu = imatvec(self.E, u)          # (..., 2n)
        rows = self.kappa[:, None]*(eu[..., :, None]*self.S + su[..., :, None]*self.E)   # (..., 2n, d)
        top = np.zeros(u.lo.shape[:-1] + (self.n, self.d))
        return IA(np.concatenate([top, rows.lo], axis=-2), np.concatenate([top, rows.hi], axis=-2))

    def BV(self, u, V):
        """B(u,.) applied to a matrix V: (..., d, d)."""
        SV = imatmul(self.S, V); EV = imatmul(self.E, V)        # (..., 2n, d)
        su = imatvec(self.S, u); eu = imatvec(self.E, u)
        rows = self.kappa[:, None]*(eu[..., :, None]*SV + su[..., :, None]*EV)
        top = np.zeros(u.lo.shape[:-1] + (self.n, self.d))
        return IA(np.concatenate([top, rows.lo], axis=-2), np.concatenate([top, rows.hi], axis=-2))


# ----------------------------------------------------------------------------- one Taylor substep (batched)
def rough_enclosure(fld, y, h, guess=None):
    """Box W with y + [0,h] F(W) subset W, for every batch member."""
    zero_h = IA(np.zeros(h.lo.shape), h.hi)
    W = y.inflate(0.0, 0.0) if guess is None else guess.hull(y)
    W = W.hull(y + zero_h[:, None]*fld.F(W)).inflate_uniform(1.0, 1e-14, (-1,))
    for it in range(40):
        Wn = y + zero_h[:, None]*fld.F(W)
        if W.contains(Wn):
            return W
        W = W.hull(Wn).inflate_uniform(0.5, 1e-14, (-1,))
    raise RuntimeError('rough enclosure did not converge; reduce the substep')


def rough_enclosure_V(fld, W, h):
    d = fld.d; zero_h = IA(np.zeros(h.lo.shape), h.hi)
    DFW = fld.J + fld.Bmat(W)                    # (m, d, d)
    Id = IA(np.broadcast_to(np.eye(d), W.lo.shape[:-1] + (d, d)).copy())
    V = Id.inflate(0.0, 1e-12)
    V = V.hull(Id + zero_h[:, None, None]*imatmul(DFW, V)).inflate_uniform(1.0, 1e-14, (-1, -2))
    for it in range(60):
        Vn = Id + zero_h[:, None, None]*imatmul(DFW, V)
        if V.contains(Vn):
            return V
        V = V.hull(Vn).inflate_uniform(0.5, 1e-14, (-1, -2))
    raise RuntimeError('variational rough enclosure did not converge')


def jets(fld, y0, order, V0=None):
    """Taylor coefficients y_k, k=0..order (and V_k if V0 given) of the solution through y0."""
    ys = [y0]; Vs = [V0] if V0 is not None else None
    for k in range(order):
        acc = imatvec(fld.J, ys[k])
        for i in range(k + 1):
            acc = acc + fld.q(ys[i], ys[k - i])
        ys.append(acc*(1.0/(k + 1)) if False else IA(dn(acc.lo/(k + 1)), up(acc.hi/(k + 1))))
        if Vs is not None:
            accV = imatmul(fld.J, Vs[k])
            for i in range(k + 1):
                accV = accV + fld.BV(ys[i], Vs[k - i])
            Vs.append(IA(dn(accV.lo/(k + 1)), up(accV.hi/(k + 1))))
    return ys, Vs


def horner(coeffs, h, last_extra):
    """sum_{k<=p} c_k h^k + c_{p+1} h^{p+1} with interval h (broadcast over trailing axes)."""
    p = len(coeffs) - 1
    hh = h.reshape(h.lo.shape + (1,)*(coeffs[0].lo.ndim - 1))
    acc = last_extra
    for k in range(p, -1, -1):
        acc = coeffs[k] + hh*acc
    return acc


def substep(fld, box, h, order, want_V=True, guessW=None):
    """Enclosures of phi_h(y) for y in box (mean-value form) and of D phi_h over the box."""
    d = fld.d
    W = rough_enclosure(fld, box, h, guessW)
    mid = IA.exact(box.mid())
    ys_mid, _ = jets(fld, mid, order)
    ysW, _ = jets(fld, W, order + 1)
    phi_mid = horner(ys_mid, h, ysW[order + 1])
    if not want_V:
        return phi_mid, None, W
    VW = rough_enclosure_V(fld, W, h)
    Id = IA(np.broadcast_to(np.eye(d), box.lo.shape[:-1] + (d, d)).copy())
    ys_box, Vs_box = jets(fld, box, order, Id)
    _, VsW = jets(fld, W, order + 1, VW)
    Dphi = horner(Vs_box, h, VsW[order + 1])
    delta = box - mid
    phi_box = phi_mid + imatvec(Dphi, delta)
    return phi_box, Dphi, W


# ----------------------------------------------------------------------------- main proof
def validate(rstr, m=256, q=None, order=12, rho=None):
    t_start = time.time()
    model = finite_model(); fm = FloatModel(model); fld = Field(model); d = fld.d
    # --- candidate orbit (floating point, not part of the proof)
    cand = np.load(ROOT/'data'/'cycles.npz'); y0 = cand['stable_y0']; T = float(cand['stable_T'])
    # the candidate was polished by DOP853 shooting in make_data.py; do not re-polish with a stiff solver
    from scipy.integrate import solve_ivp
    hp = lambda ya, dur: solve_ivp(fm.F, (0, dur), ya, method='DOP853', rtol=3e-14, atol=1e-17).y[:, -1]
    res = float(np.abs(hp(y0, T) - y0).max())
    Lest = max(np.abs(fm.DF(0, y)).sum(axis=1).max() for y in fm.integrate(y0, T, t_eval=np.linspace(0, T, 2001)).y.T)
    q = q or int(np.ceil(T/m/(0.45/(1.1*Lest))))          # substep length with h * Lipschitz constant below 0.45
    H = T/m; nodes = [y0]
    for l in range(m - 1):
        nodes.append(hp(nodes[-1], H))
    Ybar = np.array(nodes)                                   # (m, d) floats: the candidate X-bar
    Tbar = float(T)
    print(f'r={rstr}: candidate T={Tbar:.12f}, shooting residual {res:.1e}, m={m}, q={q}, h={T/(m*q):.5f}, order={order}', flush=True)
    N = 1 + d*m
    hbar = IA.frac(Fr(Tbar))*IA.exact(1.0/(m*q)) if False else IA(dn(dn(Tbar/m)/q), up(up(Tbar/m)/q))
    phase = fm.F(0, y0)                                     # phase normal (float, exact by fiat)

    def propagate(radius_y, radius_T, want_V):
        """Propagate all m shooting intervals through q substeps."""
        box = IA(dn(Ybar - radius_y), up(Ybar + radius_y))
        h = IA(dn(dn((Tbar - radius_T)/m)/q), up(up((Tbar + radius_T)/m)/q))
        h = IA(np.full(m, h.lo), np.full(m, h.hi))
        Dacc = IA(np.broadcast_to(np.eye(d), (m, d, d)).copy()) if want_V else None
        Ws = []; W = None
        for j in range(q):
            box, Dphi, W = substep(fld, box, h, order, want_V, None)
            Ws.append(W)
            if want_V:
                Dacc = imatmul(Dphi, Dacc)
        return box, Dacc, Ws

    # --- Y: G(X-bar)
    endpoint, _, _ = propagate(0.0, 0.0, want_V=False)
    G = IA(np.zeros(N)); shifted = np.roll(Ybar, -1, axis=0)
    Gy = endpoint - IA.exact(shifted)
    G = IA(np.concatenate([[0.0], Gy.lo.ravel()]), np.concatenate([[0.0], Gy.hi.ravel()]))
    print(f'  residual |G(Xbar)| <= {G.mag().max():.2e}   ({time.time()-t_start:.0f}s)', flush=True)

    # --- approximate inverse A from floating-point derivative data
    Dmid = np.array([fm.flow_with_variation(nodes[l], H, rtol=1e-13, atol=1e-15)[1] for l in range(m)])
    DGf = np.zeros((N, N)); DGf[0, 1:1 + d] = phase
    for l in range(m):
        r0 = 1 + d*l; c1 = 1 + d*((l + 1) % m)
        DGf[r0:r0 + d, 0] = fm.F(0, shifted[l])/m
        DGf[r0:r0 + d, r0:r0 + d] = Dmid[l]; DGf[r0:r0 + d, c1:c1 + d] -= np.eye(d)
    A = np.linalg.inv(DGf)
    Aint = IA.exact(A)
    AG = imatvec(Aint, G)
    Y = float(AG.mag().max())
    print(f'  Y = {Y:.3e}, ||A||_inf = {np.abs(A).sum(axis=1).max():.3e}   ({time.time()-t_start:.0f}s)', flush=True)
    rho = rho or 4*Y
    for attempt in range(3):
        # --- derivative enclosure over the ball
        ballend, Dball, Ws = propagate(rho, rho, want_V=True)
        Fend = fld.F(ballend)*IA.exact(1.0/m) if False else fld.F(ballend)*IA(dn(1.0/m), up(1.0/m))   # dG_{l+1}/dT
        # --- E = I - A DG over the ball, assembled block-sparse
        Elo = np.eye(N); Ehi = np.eye(N)
        E = IA(Elo, Ehi)
        # column 0 (T): A[:, rows] @ Fend
        colT = IA(np.zeros(N))
        for l in range(m):
            r0 = 1 + d*l
            colT = colT + imatvec(Aint[:, r0:r0 + d], Fend[l])
        # phase row: DG[0, 1:1+d] = phase (exact floats)
        Aph = imatvec(Aint[:, 0:1], IA.exact(phase)[None, :]) if False else None
        blocks_lo = np.zeros((N, N)); blocks_hi = np.zeros((N, N))
        # contribution of DG row 0: A[:,0] * phase^T into columns 1..d
        c = Aint[:, 0][:, None]*IA.exact(phase)[None, :]
        blocks_lo[:, 1:1 + d] += c.lo; blocks_hi[:, 1:1 + d] += c.hi
        # NOTE: the sums below are of disjoint column blocks except the diagonal blocks and -I blocks,
        # which are accumulated with rigorous rounding through IA additions.
        AD = IA(blocks_lo, blocks_hi)
        for l in range(m):
            r0 = 1 + d*l; c1 = 1 + d*((l + 1) % m)
            block = imatmul(Aint[:, r0:r0 + d], Dball[l])              # (N, d)
            cur = IA(AD.lo[:, r0:r0 + d], AD.hi[:, r0:r0 + d]) + block
            AD.lo[:, r0:r0 + d] = cur.lo; AD.hi[:, r0:r0 + d] = cur.hi
            cur = IA(AD.lo[:, c1:c1 + d], AD.hi[:, c1:c1 + d]) - Aint[:, r0:r0 + d]
            AD.lo[:, c1:c1 + d] = cur.lo; AD.hi[:, c1:c1 + d] = cur.hi
        AD.lo[:, 0] = colT.lo; AD.hi[:, 0] = colT.hi
        E = IA(np.eye(N)) - AD
        Z = float(E.mag().sum(axis=1).max())
        ok = Z < 1 and Y + Z*rho <= rho
        print(f'  attempt {attempt}: rho={rho:.3e}, Z={Z:.3e}, Y+Z*rho={Y + Z*rho:.3e} -> {"OK" if ok else "retry"}   ({time.time()-t_start:.0f}s)', flush=True)
        if ok: break
        rho = 2*Y/(1 - Z) if Z < 1 else rho/4
    assert ok, 'Newton-Kantorovich condition failed'

    # --- consequences: period, positivity, amplitude
    Tint = IA(dn(Tbar - rho), up(Tbar + rho))
    Wall = stack(Ws)                                            # (q, m, d) rough enclosures cover all t
    Wflat = Wall.reshape(q*m, d)
    species = fld.xstar[None, :] + imatvec(fld.P, Wflat)       # (q m, 12)
    smin = species.lo.min(axis=0); smax = species.hi.max(axis=0)
    # sharper node values: y(t_l) in ball, species there
    nodesp = fld.xstar[None, :] + imatvec(fld.P, IA(dn(Ybar - rho), up(Ybar + rho)))
    node_lo = nodesp.lo; node_hi = nodesp.hi
    p2p_lower = node_lo.max(axis=0) - node_hi.min(axis=0)      # rigorous lower bound of peak-to-peak
    p2p_upper = smax - smin
    # readout S3 + D3 equals the third pool coordinate U_3 = U_3^* + y[2]: rigorous bounds from the node balls
    ro_lower = dn(dn(Ybar[:, 2].max() - rho) - up(Ybar[:, 2].min() + rho))
    ro_upper = up(Wflat.hi[:, 2].max() - Wflat.lo[:, 2].min())
    print(f'  readout S3+D3 peak-to-peak in [{ro_lower:.6f}, {ro_upper:.6f}]', flush=True)
    print(f'  T in [{Tint.lo:.12f}, {Tint.hi:.12f}], min species >= {smin.min():.6f}, S3 peak-to-peak in [{p2p_lower[3]:.6f}, {p2p_upper[3]:.6f}]', flush=True)
    assert smin.min() > 0
    # minimal period: an interval longer than T/2 on which S3 stays below a level exceeded elsewhere
    s3hi = species.hi.reshape(q, m, 12)[:, :, 3].T.ravel()       # chronological order (node l, substep j)
    s3max_lower = node_lo[:, 3].max()
    minimal = None
    for theta in np.linspace(smin[3], s3max_lower, 60)[1:-1]:
        below = s3hi < theta
        ext = np.concatenate([below, below])                          # cyclic runs
        best_run = 0; run = 0
        for b in ext:
            run = run + 1 if b else 0; best_run = max(best_run, run)
        if best_run*(Tbar - rho)/(m*q) > (Tbar + rho)/2 and best_run <= m*q:
            minimal = float(theta); break
    print(f'  minimal period certified: {minimal is not None} (level {minimal})', flush=True)
    assert minimal is not None

    np.savez(ROOT/'certificates'/f'orbit_blocks_{rstr.replace("/", "_")}.npz', Dlo=Dball.lo, Dhi=Dball.hi, Dmid=Dmid)
    gersh = stability(Dball, Dmid)
    out = dict(r=rstr, evidence='binary64 interval arithmetic with outward rounding; Newton-Kantorovich on multiple shooting',
               m=m, q=q, order=order, Tbar=repr(float(Tbar)), rho=repr(float(rho)), Y=repr(float(Y)), Z=repr(float(Z)),
               T_interval=[repr(float(Tint.lo)), repr(float(Tint.hi))], species_min=[repr(float(v)) for v in smin], species_max=[repr(float(v)) for v in smax],
               p2p_lower=[repr(float(v)) for v in p2p_lower], p2p_upper=[repr(float(v)) for v in p2p_upper],
               readout_p2p=[repr(float(ro_lower)), repr(float(ro_upper))], node_values_float=Ybar.tolist(), phase_normal=phase.tolist(), gershgorin=gersh,
               minimal_period_level=minimal, seconds=time.time() - t_start)
    (ROOT/'certificates').mkdir(exist_ok=True)
    (ROOT/'certificates'/f'orbit_certificate_{rstr.replace("/", "_")}.json').write_text(json.dumps(out, indent=1))
    print(f'  certificate written ({time.time()-t_start:.0f}s)')
    return out


def stability(Dball, Dmid):
    """Floquet multipliers of the true orbit from the interval blocks [D_l] (product in a
    floating-point orthogonal frame, then Gershgorin discs of the transformed product)."""
    m, d = Dmid.shape[0], Dmid.shape[1]
    Mf = np.eye(d)
    for l in range(m): Mf = Dmid[l] @ Mf
    Q0 = np.eye(d)
    for rep in range(600):                                 # orthogonal iteration: dominant frame
        Qc = Q0
        for l in range(m):
            Qc, Rn = np.linalg.qr(Dmid[l] @ Qc); sgn = np.sign(np.diag(Rn)); sgn[sgn == 0] = 1; Qc = Qc*sgn
        gap_lead = np.abs(Qc[:, :4] - Q0[:, :4]).max()
        Q0 = Qc
        if gap_lead < 1e-11: break
    Qs = [Q0]
    for l in range(m):
        Qn, Rn = np.linalg.qr(Dmid[l] @ Qs[-1])
        sgn = np.sign(np.diag(Rn)); sgn[sgn == 0] = 1
        Qs.append(Qn*sgn)
    frame_gap = np.abs(Qs[m][:, :4] - Q0[:, :4]).max()
    Qs[m] = Q0
    Pi = IA(np.eye(d))
    for l in range(m):
        Q = Qs[l + 1]; C = Q.T
        Err = IA(np.eye(d)) - imatmul(IA.exact(C), IA.exact(Q))
        e = float(Err.mag().sum(axis=1).max()); assert e < 1e-8
        delta = up(e/(1 - e)*np.abs(C).sum(axis=1).max())
        Qinv = IA.exact(C) + IA(-np.full((d, d), delta), np.full((d, d), delta))
        Rl = imatmul(imatmul(Qinv, Dball[l]), IA.exact(Qs[l]))
        Pi = imatmul(Rl, Pi)
    # Gershgorin after diagonal scaling
    best = None
    for cap, s in [(c, s) for c in (2, 3, 4, 8) for s in (1.0, 0.5, 0.25, 0.125, 0.0625, 1/32, 1/64, 1/128)]:
        sc = s**np.minimum(np.arange(d), cap)              # exact powers of two: the scaling is exact
        Ps = IA(Pi.lo*sc[None, :]/sc[:, None], Pi.hi*sc[None, :]/sc[:, None])   # entrywise scaling: exact up to rounding
        Ps = IA(dn(np.minimum(Pi.lo*sc[None, :]/sc[:, None], Pi.hi*sc[None, :]/sc[:, None])),
                up(np.maximum(Pi.lo*sc[None, :]/sc[:, None], Pi.hi*sc[None, :]/sc[:, None])))
        centers = Ps.mid()[np.arange(d), np.arange(d)]
        radii = up(Ps.rad()[np.arange(d), np.arange(d)] + (Ps.mag().sum(axis=1) - Ps.mag()[np.arange(d), np.arange(d)]))
        radii = up(radii)
        outer = np.abs(centers) + radii
        # disc containing 1 must be isolated from all others; the others inside the unit disc
        i1 = int(np.argmin(np.abs(centers - 1)))
        isolated = all(abs(centers[i1] - centers[j]) > radii[i1] + radii[j] for j in range(d) if j != i1)
        inside = all(outer[j] < 1 for j in range(d) if j != i1)
        cand = (isolated and inside, (s, cap), centers, radii)
        if cand[0]: best = cand; break
    print(f'  Floquet frame closure error {frame_gap:.1e}; Gershgorin scaling s={best[1] if best else None}: ' +
          ('all nontrivial multipliers inside the unit disc' if best else 'FAILED'), flush=True)
    if best is None:
        np.set_printoptions(linewidth=200)
        print('  Pi mid\n', np.array2string(Pi.mid(), precision=3, suppress_small=True))
        print('  Pi rad\n', np.array2string(Pi.rad(), precision=1))
    assert best is not None
    _, s, centers, radii = best
    i1 = int(np.argmin(np.abs(centers - 1)))
    discs = sorted([(float(centers[j]), float(radii[j])) for j in range(d) if j != i1], key=lambda t: -abs(t[0]))
    print('  nontrivial Gershgorin discs (centre, radius):', [(round(c, 6), f'{r:.1e}') for c, r in discs[:3]])
    return dict(scaling=s, trivial_disc=[float(centers[i1]), float(radii[i1])], nontrivial_discs=discs,
                floquet_frame_closure=float(frame_gap))


if __name__ == '__main__':
    validate(sys.argv[1] if len(sys.argv) > 1 else 'witness')
