"""Numerical illustration (NOT a certificate): alpha_1-only switching at the finite witness.

A resonant modulation  alpha_1(t) = alpha_1 (1 + u(t)),
        u(t) = A sin(Omega t + psi) sin^2(pi t / tau),   A = 0.1,  tau = 3 periods,
moves the state from rest into the basin of the attracting cycle (ON, psi = pi) and, when
started at the section crossing {zeta = 0, xi > 0} of the cycle, back into the basin of rest
(OFF, psi = pi/3).  All other rates and the three totals are untouched.  binary64 / LSODA.
"""
import json
import numpy as np
from scipy.integrate import solve_ivp
from clock import FloatSystem, finite_model

S = FloatSystem(finite_model())
cy = np.load('data/cycles.npz'); T = float(cy['stable_T']); XI, ZETA = cy['XI'], cy['ZETA']
OM = 2*np.pi/T
A, NPER = 0.1, 3
TAU = NPER*T
amp = lambda y: float(np.hypot(XI @ y, ZETA @ y))
AMP_S, AMP_U = amp(cy['stable_y0']), amp(cy['unstable_y0'])
kw = dict(method='LSODA', rtol=1e-10, atol=1e-13, max_step=0.25)
segments = []                                                  # (t, y, u)


def free(y0, dur, t0, stop_on_section=False):
    ev = None
    if stop_on_section:
        ev = lambda t, y: ZETA @ y
        ev.terminal = True; ev.direction = 0
    sol = solve_ivp(lambda t, y: S.f(t, y), (0, dur), y0, jac=lambda t, y: S.jac(t, y), events=ev, **kw)
    segments.append((t0 + sol.t, sol.y, np.zeros_like(sol.t)))
    return sol.y[:, -1], t0 + sol.t[-1]


def pulse(y0, psi, t0):
    u = lambda t: A*np.sin(OM*t + psi)*np.sin(np.pi*t/TAU)**2
    sol = solve_ivp(lambda t, y: S.f(t, y, u(t)), (0, TAU), y0, jac=lambda t, y: S.jac(t, y, u(t)), **kw)
    segments.append((t0 + sol.t, sol.y, u(sol.t)))
    return sol.y[:, -1], t0 + TAU


y, t = free(np.zeros(9), 2*T, 0.0)
y, t = pulse(y, np.pi, t); on_amp = amp(y); t_on_end = t
y, t = free(y, 14*T, t)
# phase trigger: wait for the section crossing zeta = 0 with xi > 0
for _ in range(4):
    y, t = free(y + 0.0, 2*T, t, stop_on_section=True)
    if XI @ y > 0 and abs(ZETA @ y) < 1e-6:
        break
    y, t = free(y, 0.05*T, t)
pre_off_amp = amp(y); t_off_start = t
y, t = pulse(y, np.pi/3, t); off_amp = amp(y)
y, t = free(y, 14*T, t)
tt = np.concatenate([s[0] for s in segments]); Y = np.concatenate([s[1] for s in segments], axis=1)
uu = np.concatenate([s[2] for s in segments])
X = S.x0[:, None] + S.P @ Y
np.savez('data/switch_demo.npz', t=tt, readout=X[3] + X[11], u=uu, period=T)
# long-run fates, judged by the readout range over the final 1.5 periods
def final_range(y0, dur):
    sol = solve_ivp(lambda t, y: S.f(t, y), (0, dur), y0, jac=lambda t, y: S.jac(t, y), dense_output=True, **kw)
    rd = sol.sol(np.linspace(dur - 1.5*T, dur, 600))[2]        # chart coordinate 2 is S3 + D3 up to a constant
    return float(rd.max() - rd.min())


fate_on = final_range(segments[2][1][:, -1], 400*T)
fate_off = final_range(y, 600*T)
out = dict(evidence='binary64 numerics; illustration only, not a certificate', A=A, periods=NPER, psi_on=float(np.pi),
           psi_off=float(np.pi/3), amp_stable_cycle=AMP_S, amp_unstable_cycle=AMP_U, amp_after_on=on_amp,
           amp_before_off=pre_off_amp, amp_after_off=off_amp, readout_range_400_periods_after_on=fate_on,
           readout_range_600_periods_after_off=fate_off, min_species=float(X.min()), t_on_end=t_on_end,
           t_off_start=t_off_start)
json.dump(out, open('data/switch_demo.json', 'w'), indent=1)
print(json.dumps(out, indent=1))
assert on_amp > AMP_U and off_amp < AMP_U and abs(fate_on - 2.345935) < 1e-3 and fate_off < 0.01 and X.min() > 0
