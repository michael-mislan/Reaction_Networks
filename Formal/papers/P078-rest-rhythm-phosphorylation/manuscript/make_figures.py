"""Figures for the paper (vector PDF).  Run after make_data.py and make_switch_demo.py.

fig_switch.pdf   numerical illustration of alpha_1-only ON/OFF switching at the finite witness
fig_wedge.pdf    leading-order unfolding of the certified generalized-Hopf point
fig_witness.pdf  finite witness: waveforms, phase projection, hard excitation (numerical)
fig_branch.pdf   cycle branch in the reverse ratio r (numerical) with the certified Hopf point
"""
import json
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from clock import FloatSystem, finite_model

plt.rcParams.update({'font.size': 9, 'axes.spines.top': False, 'axes.spines.right': False,
                     'font.family': 'serif', 'mathtext.fontset': 'cm', 'axes.linewidth': 0.7,
                     'legend.frameon': False, 'pdf.fonttype': 42})
BLUE, RED, GREY, GOLD = '#1f5f8b', '#a23b3b', '#555555', '#c9952b'
D2 = 0.04442750254                                            # -Re G_2 (certified enclosure midpoint)

# ------------------------------------------------------------------ wedge
fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.7))
b = np.linspace(0, 0.02, 300)
fold = -b**2/(4*D2)
a0 = ax[0]
a0.fill_between(b, fold, 0, color=GOLD, alpha=0.35, lw=0)
a0.plot(b, fold, color=RED, lw=1.4, label=r'fold of cycles $a=-b^2/(4d)$')
a0.plot([0, 0.02], [0, 0], color=BLUE, lw=1.4, label=r'subcritical Hopf $a=0,\ b>0$')
a0.plot([-0.012, 0], [0, 0], color=BLUE, lw=1.4, ls=':', label=r'supercritical Hopf $a=0,\ b<0$')
a0.plot([0], [0], 'ko', ms=4)
a0.set_xlim(-0.012, 0.02); a0.set_ylim(-0.0024, 0.0012)
a0.set_xlabel(r'cubic coefficient $b=\mathrm{Re}\,G_1$'); a0.set_ylabel(r'$a=\mathrm{Re}\,\lambda$')
a0.text(0.0125, -0.00035, 'rest and\nrhythm', ha='center', va='center', fontsize=8)
a0.text(-0.006, -0.0007, 'rest only', ha='center', fontsize=8)
a0.text(0.004, 0.0007, 'rhythm only', ha='center', fontsize=8)
a0.text(0.0005, 0.00012, 'GH', fontsize=8)
a0.legend(fontsize=6.5, loc='lower left', handlelength=1.6)
a0.ticklabel_format(style='sci', scilimits=(-2, 2))
a0.set_title('(a) leading-order unfolding', fontsize=9)
b0 = 0.012
a = np.linspace(-b0**2/(4*D2), 0.0006, 400)
disc = np.sqrt(np.maximum(b0**2 + 4*D2*a, 0))
Rp = np.sqrt((b0 + disc)/(2*D2)); Rm_ = np.sqrt(np.maximum((b0 - disc)/(2*D2), 0))
a1 = ax[1]
a1.plot(a, Rp, color=BLUE, lw=1.6, label='attracting cycle $R_+$')
m_ = a <= 0
a1.plot(a[m_], Rm_[m_], color=RED, lw=1.4, ls='--', label='unstable cycle $R_-$')
a1.plot([a[0]*1.6, 0], [0, 0], color='k', lw=1.6, label='sink')
a1.plot([0, 0.0006], [0, 0], color='k', lw=1.0, ls=':')
a1.axvspan(a[0], 0, color=GOLD, alpha=0.25, lw=0)
a1.set_xlim(a[0]*1.6, 0.0006)
a1.set_xlabel(r'$a=\mathrm{Re}\,\lambda$  (fixed $b=0.012$)'); a1.set_ylabel('cycle radius $R$')
a1.ticklabel_format(style='sci', scilimits=(-2, 2), axis='x')
a1.legend(fontsize=6.5, loc='center right', bbox_to_anchor=(1.0, 0.42))
a1.set_title('(b) hard excitation and hysteresis', fontsize=9)
fig.tight_layout(); fig.savefig('figures/fig_wedge.pdf'); plt.close(fig)

# ------------------------------------------------------------------ witness
S = FloatSystem(finite_model())
cy = np.load('data/cycles.npz')


def orbit(y0, T, n=1200):
    sol = solve_ivp(lambda t, y: S.f(t, y), (0, T), y0, method='LSODA', rtol=1e-11, atol=1e-13,
                    jac=lambda t, y: S.jac(t, y), dense_output=True)
    t = np.linspace(0, T, n); X = S.x0[:, None] + S.P @ sol.sol(t)
    return t, X


ts, Xs = orbit(cy['stable_y0'], float(cy['stable_T']))
tu, Xu = orbit(cy['unstable_y0'], float(cy['unstable_T']))
rest = S.x0[3] + S.x0[11]
fig, ax = plt.subplots(1, 3, figsize=(6.9, 2.45))
k = np.argmax(Xs[3] + Xs[11]); ku = np.argmax(Xu[3] + Xu[11])
ax[0].plot(ts, np.roll(Xs[3] + Xs[11], -k), color=BLUE, lw=1.6, label='attracting cycle')
ax[0].plot(tu, np.roll(Xu[3] + Xu[11], -ku), color=RED, lw=1.2, ls='--', label='unstable cycle')
ax[0].axhline(rest, color='k', lw=1.2, label='sink (rest)')
ax[0].set_xlabel('model time'); ax[0].set_ylabel(r'readout $S_3+D_3$')
ax[0].set_ylim(2.2, 6.6)
ax[0].legend(fontsize=6.3, loc='upper center', ncol=1, handlelength=1.8)
ax[0].set_title('(a) one period', fontsize=9)
ax[1].plot(Xs[5], Xs[3] + Xs[11], color=BLUE, lw=1.6)
ax[1].plot(Xu[5], Xu[3] + Xu[11], color=RED, lw=1.2, ls='--')
ax[1].plot([S.x0[5]], [rest], 'ko', ms=3.5)
ax[1].set_xlabel('free phosphatase $F$'); ax[1].set_ylabel(r'$S_3+D_3$')
ax[1].set_title('(b) projection', fontsize=9)
# hard excitation: two starts on either side of the unstable cycle
Tw = 9000.0
for fac, col in ((0.93, 'k'), (1.07, BLUE)):
    y0 = fac*cy['unstable_y0']
    sol = solve_ivp(lambda t, y: S.f(t, y), (0, Tw), y0, method='LSODA', rtol=1e-10, atol=1e-13,
                    jac=lambda t, y: S.jac(t, y), dense_output=True)
    tt = np.linspace(0, Tw, 60001); rd = (S.x0[:, None] + S.P @ sol.sol(tt))[3] + (S.x0[:, None] + S.P @ sol.sol(tt))[11]
    win = 200                                                  # 30 time units: just over one period
    nwin = len(tt)//win
    env = np.array([rd[i*win:(i+1)*win].max() - rd[i*win:(i+1)*win].min() for i in range(nwin)])
    ax[2].plot(tt[:nwin*win:win]/float(cy['stable_T']), env, color=col, lw=1.3)
ax[2].axhline(np.ptp(Xu[3] + Xu[11]), color=RED, lw=1.0, ls='--')
ax[2].set_xlabel('time (periods)'); ax[2].set_ylabel('peak-to-peak per window')
ax[2].set_title('(c) threshold response', fontsize=9)
fig.tight_layout(w_pad=0.6); fig.savefig('figures/fig_witness.pdf'); plt.close(fig)

# ------------------------------------------------------------------ branch
B = np.load('data/branch.npz')['rows']                       # xi, r, period, range, lead multiplier
num = json.load(open('data/numerics.json'))
RH = 1.3446715241927645
ifold = int(np.argmax(B[:, 1]))
fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.6))
ax[0].plot(B[:ifold+1, 1], B[:ifold+1, 3], color=RED, lw=1.3, ls='--', label='unstable cycle')
ax[0].plot(B[ifold:, 1], B[ifold:, 3], color=BLUE, lw=1.6, label='attracting cycle')
ax[0].plot([RH, 1.362], [0, 0], color='k', lw=1.6, label='sink')
ax[0].plot([B[:, 1].min(), RH], [0, 0], color='k', lw=1.0, ls=':', label='unstable equilibrium')
ax[0].axvspan(RH, B[ifold, 1], color=GOLD, alpha=0.25, lw=0)
ax[0].axvline(num['r_witness'], color=GREY, lw=0.8)
ax[0].plot([RH], [0], 'ko', ms=3.5)
ax[0].annotate('certified\nHopf point', (RH, 0), (1.3225, 0.55), fontsize=7, arrowprops=dict(arrowstyle='-', lw=0.5))
ax[0].text(num['r_witness'] + 0.0004, 0.9, 'witness', fontsize=7, rotation=90, va='top', color=GREY)
ax[0].set_xlim(B[:, 1].min(), 1.362); ax[0].set_ylim(-0.1, 3.7)
ax[0].set_xlabel(r'reverse ratio $r=\beta_1/\gamma_1$'); ax[0].set_ylabel(r'peak-to-peak of $S_3+D_3$')
ax[0].legend(fontsize=6.5, loc='center left', bbox_to_anchor=(0.0, 0.66))
ax[0].set_title('(a) amplitude', fontsize=9)
ax[1].plot(B[:ifold+1, 1], B[:ifold+1, 4], color=RED, lw=1.3, ls='--')
ax[1].plot(B[ifold:, 1], B[ifold:, 4], color=BLUE, lw=1.6)
ax[1].axhline(1, color='k', lw=0.6)
ax[1].axvline(num['r_witness'], color=GREY, lw=0.8)
ax[1].set_xlim(B[:, 1].min(), 1.362)
ax[1].set_xlabel(r'reverse ratio $r$'); ax[1].set_ylabel('largest nontrivial $|$multiplier$|$')
ax[1].set_title('(b) stability', fontsize=9)
fig.tight_layout(); fig.savefig('figures/fig_branch.pdf'); plt.close(fig)
# ------------------------------------------------------------------ switching illustration
D = np.load('data/switch_demo.npz'); sw = json.load(open('data/switch_demo.json'))
tp = D['t']/float(D['period'])
fig, ax = plt.subplots(2, 1, figsize=(6.6, 3.1), sharex=True, gridspec_kw=dict(height_ratios=[3, 1.1]))
ax[0].plot(tp, D['readout'], color=BLUE, lw=0.9)
ax[0].axhline(rest, color='k', lw=0.6, ls=':')
for a_ in ax:
    a_.axvspan(2, 5, color=GOLD, alpha=0.3, lw=0)
    a_.axvspan(sw['t_off_start']/float(D['period']), sw['t_off_start']/float(D['period']) + 3, color=GOLD, alpha=0.3, lw=0)
ax[0].set_ylabel(r'readout $S_3+D_3$')
ax[0].text(3.5, 5.75, 'ON', ha='center', fontsize=8); ax[0].text(sw['t_off_start']/float(D['period']) + 1.5, 5.75, 'OFF', ha='center', fontsize=8)
ax[0].set_ylim(2.7, 6.1)
ax[1].plot(tp, D['u'], color=RED, lw=0.9)
ax[1].set_ylabel(r'$u(t)$'); ax[1].set_xlabel('time (periods of the attracting cycle)')
ax[1].set_ylim(-0.13, 0.13); ax[1].set_xlim(0, tp[-1])
fig.tight_layout(h_pad=0.3); fig.savefig('figures/fig_switch.pdf'); plt.close(fig)
print('figures written')
