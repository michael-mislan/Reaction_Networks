from fractions import Fraction as Fr
import json
import numpy as np
from scipy.linalg import solve_continuous_lyapunov
from scipy.optimize import brentq

XQ = list(map(Fr, [
    '30', '13', '19/100', '9/100', '33/10', '1',
    '13/25', '7/250', '39/50', '93/10', '3/20', '5/2'
]))
X = np.array(list(map(float, XQ)))
S, ENZ, Z = X[:4], X[4:6], X[6:]
QF = np.array([.1, 7.8, 1.])
QFQ = list(map(Fr, ['1/10', '39/5', '1']))
ARM = np.tile(np.arange(3), 2)
LEVEL = np.array([0, 1, 2, 1, 2, 3])
OUT = np.array([1, 2, 3, 0, 1, 2])
EN = np.array([0, 0, 0, 1, 1, 1])
HS = np.eye(4)[:, LEVEL]
HE = np.eye(2)[:, EN]
T = np.array([[-1., 0., 0.], [1., -1., 0.],
              [0., 1., -1.], [0., 0., 1.]])

# Literal reactant and stoichiometric matrices, three reactions per arm.
Y = np.zeros((12, 18), dtype=int)
N = np.zeros((12, 18), dtype=int)
for j in range(6):
    s, e, c, out = LEVEL[j], 4 + EN[j], 6 + j, OUT[j]
    reactants = [{s: 1, e: 1}, {c: 1}, {c: 1}]
    products = [{c: 1}, {s: 1, e: 1}, {out: 1, e: 1}]
    for k, (rea, pro) in enumerate(zip(reactants, products)):
        col = 3*j + k
        for i, val in rea.items():
            Y[i, col] = val
            N[i, col] -= val
        for i, val in pro.items():
            N[i, col] += val

# Pool/complex projection; enzymes carry no substrate.
RCH = np.zeros((9, 12))
for i in range(1, 4):
    RCH[i-1, :4] = (np.arange(4) >= i)
    RCH[i-1, 6:] = (LEVEL >= i)
RCH[3:, 6:] = np.eye(6)

def lift(ke=1., kf=1.):
    return np.vstack((
        np.c_[T, -HS],
        np.c_[np.zeros((2, 3)), -np.diag([ke, kf]) @ HE],
        np.c_[np.zeros((6, 3)), np.eye(6)]
    ))

def blocks(r, ke=1., kf=1.):
    ratios = np.array([.01, .01, .01, r, .01, .01])
    v = (1 + ratios) * QF[ARM]
    L = np.c_[np.diag(QF / Z[:3]), -np.diag(QF / Z[3:])]
    G = (np.diag(1/Z) + HS.T @ np.diag(1/S) @ HS
         + HE.T @ np.diag([ke/ENZ[0], kf/ENZ[1]]) @ HE)
    A = np.diag(v) @ G
    M = np.diag(v / S[LEVEL]) @ HS.T @ T
    J = np.block([[np.zeros((3, 3)), L], [M, -A]])
    return J, L, M, A, v, G

def literal_jacobian(r, ke=1., kf=1., eps=1.):
    ratios = np.array([.01, .01, .01, r, .01, .01])
    catflux = QF[ARM]
    bindflux = (1 + ratios) * catflux / eps
    flux = np.empty(18)
    flux[0::3] = bindflux
    flux[1::3] = bindflux - catflux
    flux[2::3] = catflux
    assert np.all(flux > 0)
    assert np.max(np.abs(N @ flux)) < 1e-11
    full = N @ np.diag(flux) @ Y.T @ np.diag(1/X)
    P = lift(ke, kf)
    assert np.max(np.abs(RCH @ P - np.eye(9))) < 1e-14
    return RCH @ full @ P

def exact_equilibrium_check():
    ratios = [Fr(1, 100)] * 6
    ratios[3] = Fr(1, 4)
    flux = []
    for j in range(6):
        qq = QFQ[j % 3]
        vv = (1 + ratios[j]) * qq
        flux.extend([vv, vv-qq, qq])
    for i in range(12):
        assert sum(int(N[i, k])*flux[k] for k in range(18)) == 0
    assert sum(XQ[6:9]) + XQ[4] == Fr(1157, 250)
    assert sum(XQ[9:12]) + XQ[5] == Fr(259, 20)
    assert sum(XQ[:4]) + sum(XQ[6:]) == Fr(28279, 500)

def positive_pair(r, ke, kf):
    eig = np.linalg.eigvals(blocks(r, ke, kf)[0])
    candidates = eig[eig.imag > 1e-7]
    if len(candidates) == 0:
        raise ValueError('No nonreal upper-half-plane candidate in this bracket')
    return max(candidates, key=lambda zz: zz.real)

def hopf_pilot(ke, kf, bracket):
    r = brentq(lambda rr: positive_pair(rr, ke, kf).real,
               *bracket, xtol=1e-13)
    J, L, M, A, v, G = blocks(r, ke, kf)
    ev, vec = np.linalg.eig(J)
    lam = positive_pair(r, ke, kf)
    ix = int(np.argmin(np.abs(ev-lam)))
    q = vec[:, ix] / vec[-1, ix]
    el, vl = np.linalg.eig(J.T)
    ell = vl[:, np.argmin(np.abs(el-lam))]
    ell = ell / (ell @ q)  # Bilinear transpose convention, not Hermitian.
    P = lift(ke, kf)
    bindrates = v / (S[LEVEL] * ENZ[EN])

    # Hessian from literal binding columns and the source lift.
    def B(u, w):
        pu, pw = P @ u, P @ w
        result = np.zeros(12, dtype=complex)
        for j in range(6):
            si, ei = LEVEL[j], 4 + EN[j]
            result += (N[:, 3*j] * bindrates[j]
                       * (pu[si]*pw[ei] + pw[si]*pu[ei]))
        return RCH @ result

    omega = lam.imag
    first = np.linalg.solve(J, B(q, q.conjugate()))
    second = np.linalg.solve(2j*omega*np.eye(9)-J, B(q, q))
    g21 = ell @ (-2*B(q, first) + B(q.conjugate(), second))
    jr = blocks(1., ke, kf)[0] - blocks(0., ke, kf)[0]
    derivative = ell @ jr @ q
    rest = [zz for zz in ev if abs(zz-lam) > 1e-7
            and abs(zz-lam.conjugate()) > 1e-7]
    return dict(r=r, omega=omega, l1=float(g21.real/(2*omega)),
                crossing=[float(derivative.real), float(derivative.imag)],
                max_other_real=float(max(zz.real for zz in rest))), (q, ell)

def main():
    exact_equilibrium_check()
    for ke, kf in [(1., 1.), (0., 1.), (1., 0.), (0., 0.)]:
        assert np.max(np.abs(literal_jacobian(.25, ke, kf)
                             - blocks(.25, ke, kf)[0])) < 1e-10
    original, (q, ell) = hopf_pilot(1., 1., (.25, .30))
    onepool, _ = hopf_pilot(0., 1., (1., 2.))
    r = original['r']
    J, L, M, A, v, G = blocks(r)
    eps_derivative = ell @ np.block([
        [np.zeros((3, 9))], [-M, A]
    ]) @ q
    for eps in [.5, 1., 1.005]:
        jeps = np.block([[np.zeros((3, 3)), L], [M/eps, -A/eps]])
        assert np.max(np.abs(jeps-literal_jacobian(r, eps=eps))) < 1e-9

    fastR = np.linalg.solve(A, M)
    J0 = L @ fastR
    W = np.diag(1/v)
    Pslow = solve_continuous_lyapunov(J0.T, -np.eye(3))
    cross = Pslow @ L - J0.T @ fastR.T @ W
    aa = float(np.linalg.eigvalsh(G).min())
    tmp = W @ fastR @ L
    bb = float(np.linalg.norm((tmp+tmp.T)/2, 2))
    cc = float(np.linalg.norm(cross, 2))

    sqrtW, invsqrtW = np.diag(1/np.sqrt(v)), np.diag(np.sqrt(v))
    avec, modes = np.linalg.eigh(sqrtW @ A @ invsqrtW)
    Cout, Bin = L @ invsqrtW @ modes, modes.T @ sqrtW @ M
    modal = []
    for k in range(7):
        direct = (Cout[:, k:] @ np.diag(1/avec[k:]) @ Bin[k:, :]
                  if k < 6 else np.zeros((3, 3)))
        approx = np.block([[direct, Cout[:, :k]],
                           [Bin[:k, :], -np.diag(avec[:k])]])
        roots = sorted(np.linalg.eigvals(approx),
                       key=lambda zz: zz.real, reverse=True)
        modal.append(dict(retained=k, leading=[
            [float(zz.real), float(zz.imag)] for zz in roots[:2]
        ]))

    # Nonlinear inventory baseline: tau=1, kx=2, saturation U=1.
    ji = np.array([[0., 0., 1.], [-2., -1., 0.], [0., 1., -1.]])
    qi = np.array([1., -1+1j, 1j])
    li = np.array([2j, 1., 1+1j]) / (-2+4j)
    assert np.linalg.norm(ji @ qi - 1j*qi) < 1e-14
    assert np.linalg.norm(li @ ji - 1j*li) < 1e-14
    assert abs(li @ qi - 1) < 1e-14

    result = dict(
        evidence='Exact rational equilibrium check; all spectral values are floating N evidence',
        original=original, one_dynamic_phosphatase=onepool,
        epsilon_crossing=[float(eps_derivative.real), float(eps_derivative.imag)],
        energy_bound=dict(a=aa, b=bb, c=cc, strict_epsilon_upper=aa/(bb+cc*cc)),
        relaxation_eigenvalues=list(map(float, avec)), modal=modal,
        inventory=dict(l1_U1=float((16*li[1]).real/2),
                       crossing_kx=[float((-li[1]).real), float((-li[1]).imag)])
    )
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
