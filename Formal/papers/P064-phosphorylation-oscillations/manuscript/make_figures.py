"""Vector figures for the paper.  Inputs: figures/numerical_data.json (make_data.py),
figures/region_data.json (make_region.py), certificates/paper_certificates.json (check_paper.py)
and workspace_certificates/measurement_practical_certificate.json.
All plotted finite-amplitude data are numerical (N); certified quantities are marked as such."""
import json
from fractions import Fraction as Fr
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent; FIG = ROOT/'figures'
D = json.loads((FIG/'numerical_data.json').read_text())
CERT = json.loads((ROOT/'certificates'/'paper_certificates.json').read_text())
plt.rcParams.update({'font.size': 8.5, 'axes.labelsize': 8.5, 'axes.titlesize': 9, 'legend.fontsize': 7.5,
                     'xtick.labelsize': 7.5, 'ytick.labelsize': 7.5, 'axes.spines.top': False, 'axes.spines.right': False,
                     'lines.linewidth': 1.3, 'pdf.fonttype': 42, 'font.family': 'DejaVu Sans', 'mathtext.fontset': 'dejavusans'})
BLUE, ORANGE, GREEN, RED, PURPLE, GREY = '#0072B2', '#E69F00', '#009E73', '#D55E00', '#CC79A7', '#666666'
mid = lambda v: float((Fr(v[0]) + Fr(v[1]))/2)
rA = mid(CERT['hopf_A']['r'])

# ------------------------------------------------------------------ branch
br = sorted(D['branch'], key=lambda b: b['r']); r = np.array([b['r'] for b in br])
fig, axs = plt.subplots(2, 2, figsize=(6.9, 4.7)); ax = [axs[0, 0], axs[1, 0], axs[1, 1]]; ins = axs[0, 1]
lo = np.array([b['minmax']['S3'][0] for b in br]); hi = np.array([b['minmax']['S3'][1] for b in br])
ax[0].fill_between(r, lo, hi, color=BLUE, alpha=0.18, lw=0)
ax[0].plot(r, hi, '-', color=BLUE, marker='o', ms=2.2, label=r'max, min of $S_3$ on the cycle (N)'); ax[0].plot(r, lo, '-', color=BLUE, marker='o', ms=2.2)
rr = np.linspace(0, rA, 50); ax[0].plot(rr, 0.4 + 0*rr, '--', color=GREY, lw=1, label='equilibrium, unstable')
rr = np.linspace(rA, 1.75, 10); ax[0].plot(rr, 0.4 + 0*rr, '-', color='k', lw=1.2, label='equilibrium, stable')
ax[0].plot([rA], [0.4], marker='*', color=RED, ms=9, ls='none', label='certified Hopf point', zorder=5)
for tag, rv, lab in (('7_5', 1.4, 'validated orbits (Thm. 7.2)'), ('1', 1.0, None)):
    ocert = ROOT/'certificates'/f'orbit_certificate_{tag}.json'
    if ocert.exists():
        oc = json.loads(ocert.read_text())
        ax[0].plot([rv, rv], [float(oc['species_min'][3]), float(oc['species_max'][3])], marker='D', color=RED, ms=4, ls='none',
                   label=lab, zorder=6)
ax[0].set_xlabel(r'$r=\sigma_1=\beta_1/\gamma_1$'); ax[0].set_ylabel(r'free $S_3$'); ax[0].set_xlim(0, 1.75); ax[0].set_ylim(0, 10.5)
ax[0].legend(frameon=False, loc='upper right'); ax[0].set_title('(a) attracting branch')
mu = rA - r; sel = mu < 0.2
for key, lab, col, mk in (('S3', r'free $S_3$', BLUE, 'o'), ('S3+D3', r'$S_3+D_3$', ORANGE, 's'), ('D1', r'$D_1$', GREEN, '^')):
    dk = key.replace('+', '')
    ins.plot(mu[sel], [b['p2p'][dk] for b, s in zip(br, sel) if s], mk, color=col, ms=3, label=lab + ' (N)')
    mm = np.linspace(0, 0.2, 200); ins.plot(mm, mid(CERT['A_amplitude_constants'][key])*np.sqrt(mm), '-', color=col, lw=1)
ins.plot([], [], '-', color='k', lw=1, label=r'certified law $A_c\sqrt{\mu}$')
ins.set_xlabel(r'$\mu=r_A-r$'); ins.set_ylabel('peak-to-peak amplitude'); ins.set_xlim(0, 0.2); ins.set_ylim(0, 3.6); ins.set_xticks([0, 0.05, 0.1, 0.15, 0.2])
ins.legend(frameon=False, loc='upper left', ncol=2, columnspacing=0.8); ins.set_title('(b) square-root law at onset')
ax[1].plot(r, [b['period'] for b in br], '-o', ms=2.2, color=GREEN, label='period $T$')
ax[1].plot([rA], [mid(CERT['A_limits']['period'])], marker='*', color=RED, ms=9, ls='none')
ax[1].set_xlabel('$r$'); ax[1].set_ylabel('period $T$', color=GREEN); ax[1].set_xlim(0, 1.5)
a2 = ax[1].twinx(); a2.spines['right'].set_visible(True)
a2.plot(r, [b['turnover'] for b in br], '-s', ms=2.2, color=ORANGE); a2.plot([rA], [mid(CERT['A_limits']['turnover'])], marker='*', color=RED, ms=9, ls='none')
a2.set_ylabel('turnover per cycle $Q$', color=ORANGE); ax[1].set_title('(c) period and ATP-equivalent turnover (N)')
ax[2].semilogy(r, [b['leading_nontrivial'] for b in br], '-o', ms=2.2, color=PURPLE, label='largest nontrivial')
ax[2].semilogy(r, [abs(complex(*b['multipliers'][2])) for b in br], '-o', ms=2.2, color=GREY, label='second')
ax[2].axhline(1, color='k', lw=0.6); ax[2].set_xlabel('$r$'); ax[2].set_ylabel('modulus of Floquet multiplier'); ax[2].set_xlim(0, 1.5)
ax[2].set_ylim(1e-3, 1.6); ax[2].legend(frameon=False, loc='lower right'); ax[2].set_title('(d) Floquet multipliers (N)')
fig.tight_layout(w_pad=1.2, h_pad=1.0); fig.savefig(FIG/'branch.pdf'); plt.close(fig)

# ------------------------------------------------------------------ waveforms and convergence at r=1
W = D['waveform_r1.0']; t = np.array(W['t'])/W['T']; X = np.array(W['X'])
cv = D['convergence_r1']
fig, ax = plt.subplots(1, 3, figsize=(7.0, 2.55), gridspec_kw={'width_ratios': [1.25, 1.1, 0.9]})
for name, col in (('outside', ORANGE), ('inside', BLUE)):
    ax[0].plot(cv[name]['t'], cv[name]['S3'], color=col, lw=0.9, label=f'start {name}')
ax[0].axhline(0.4, color=GREY, lw=0.7, ls='--'); ax[0].set_xlabel('time'); ax[0].set_ylabel(r'free $S_3$'); ax[0].set_xlim(0, 700)
ax[0].set_ylim(-0.1, 4.6); ax[0].legend(frameon=False, loc='upper center', ncol=2, columnspacing=1.0, handlelength=1.4)
ax[0].set_title('(a) convergence to the cycle, $r=1$')
ST = 44.24
for idx, lab, col in ((0, '$S_0$', GREY), (1, '$S_1$', BLUE), (9, '$D_1=S_1F$', RED), (11, '$D_3=S_3F$', ORANGE), (3, '$S_3$', GREEN), (8, '$C_3=S_2E$', PURPLE)):
    ax[1].plot(t, X[idx], color=col, label=lab)
ax[1].set_xlabel('time / period'); ax[1].set_ylabel('concentration'); ax[1].set_yscale('log'); ax[1].set_xlim(0, 1)
ax[1].legend(frameon=False, ncol=2, loc='lower center', columnspacing=0.8, handlelength=1.2); ax[1].set_title('(b) one period, $r=1$'); ax[1].set_ylim(0.003, 60)
ax[2].plot(X[5], X[4], color='k'); ax[2].plot([0.4], [2.3], 'x', color=RED, ms=5)
for name, col in (('outside', ORANGE), ('inside', BLUE)):
    pass
ax[2].set_xlabel('free phosphatase $F$'); ax[2].set_ylabel('free kinase $E$'); ax[2].set_title('(c) free enzymes')
ax[2].set_xscale('log')
fig.tight_layout(w_pad=0.7); fig.savefig(FIG/'waveforms.pdf'); plt.close(fig)

# ------------------------------------------------------------------ mechanism
fig, ax = plt.subplots(1, 2, figsize=(6.6, 2.4))
for c, col, lab in zip(D['relaxation'], (RED, BLUE), (r'$r=r_A$', r'$r=1$')):
    cur = np.array(c['curve']); ax[0].plot(cur[:, 0], cur[:, 1], color=col, label=lab)
ax[0].axhline(0, color='k', lw=0.6); ax[0].axhline(D['static_eigs'][-1], color=GREY, ls=':', lw=1); ax[0].axvline(1, color=GREY, lw=0.6, ls='--')
ax[0].text(0.052, D['static_eigs'][-1] + 0.002, 'slowest static eigenvalue', fontsize=6.5, color=GREY)
ax[0].set_xscale('log'); ax[0].set_xlabel(r'relaxation factor $\varepsilon$ (complexes slower $\rightarrow$)'); ax[0].set_ylabel(r'leading $\mathrm{Re}\,\lambda$')
ax[0].legend(frameon=False, loc='upper left'); ax[0].set_title('(a) same static chemistry, different stability')
K = D['kernel']; ax[1].loglog(K['w'], K['sv'], color=BLUE)
ax[1].axvline(D['omegaA'], color=RED, lw=1); ax[1].text(D['omegaA']*1.12, max(K['sv'])*0.5, r'$\omega_A$', color=RED)
for v in K['relax_rates']: ax[1].plot([v, v], [min(K['sv']), min(K['sv'])*3], color=GREY, lw=1)
ax[1].axhline(K['sv'][0], color=GREY, ls=':', lw=1); ax[1].text(3, K['sv'][0]*1.15, r'static value $\|\mathcal{H}(0)\|$', fontsize=6.5, color=GREY)
ax[1].set_xlabel(r'frequency $\omega$'); ax[1].set_ylabel(r'$\sigma_{\max}\,\mathcal{H}(i\omega)$'); ax[1].set_title('(b) what elimination discards')
fig.tight_layout(w_pad=1.0); fig.savefig(FIG/'mechanism.pdf'); plt.close(fig)

# ------------------------------------------------------------------ two-parameter region
Rg = json.loads((FIG/'region_data.json').read_text()); sc = np.array(Rg['scales'])
lead = np.array([[np.nan if v is None else v for v in row] for row in Rg['lead']])
fig, ax = plt.subplots(figsize=(3.5, 2.9))
vmax = np.nanmax(np.abs(lead)); vmax = 0.08
pc = ax.pcolormesh(sc*Rg['FT0'], sc*Rg['ET0'], np.clip(lead, -vmax, vmax), cmap='RdBu_r', vmin=-vmax, vmax=vmax, shading='nearest', rasterized=True)
ax.contour(sc*Rg['FT0'], sc*Rg['ET0'], lead, levels=[0], colors='k', linewidths=1)
ax.plot([Rg['FT0']], [Rg['ET0']], 'k*', ms=8); ax.set_xscale('log'); ax.set_yscale('log')
ax.set_xticks([15, 20, 30, 40, 50]); ax.set_xticklabels(['15', '20', '30', '40', '50']); ax.set_yticks([3, 4, 5, 6, 8]); ax.set_yticklabels(['3', '4', '5', '6', '8'])
ax.minorticks_off()
ax.set_xlabel(r'phosphatase total $F_{\mathrm{T}}$'); ax.set_ylabel(r'kinase total $E_{\mathrm{T}}$')
cb = fig.colorbar(pc, ax=ax, pad=0.02); cb.set_label(r'leading $\mathrm{Re}\,\lambda$ at the equilibrium', fontsize=7.5)
ax.set_title(r'rate constants of witness A, $r=1$, $S_{\mathrm{T}}=44.24$', fontsize=8)
fig.tight_layout(); fig.savefig(FIG/'region.pdf', dpi=300); plt.close(fig)

# ------------------------------------------------------------------ validated pulse experiment
Mz = json.loads((ROOT/'workspace_certificates'/'measurement_practical_certificate.json').read_text())
fig, ax = plt.subplots(figsize=(3.6, 2.5)); e_read = 8e-5
for res, col in zip(Mz['results'], (BLUE, ORANGE)):
    tt = [float(Fr(s['time'])) for s in res['samples']]
    lo = np.array([float(Fr(s['D1'][0])) for s in res['samples']]) - 23; hi = np.array([float(Fr(s['D1'][1])) for s in res['samples']]) - 23
    ax.fill_between(tt, (lo - e_read)*1e3, (hi + e_read)*1e3, color=col, alpha=0.25, lw=0)
    ax.errorbar(tt, (lo + hi)/2*1e3, yerr=(hi - lo)/2*1e3, fmt='o-', ms=2.5, color=col, capsize=2, lw=1, label=f"$r={res['r']}$")
ax.axvline(0.05, color=GREY, ls=':', lw=1); ax.set_xlabel('time after pulse onset (model units)'); ax.set_ylabel(r'$10^{3}\,(D_1-D_1^*)$')
ax.legend(frameon=False, loc='upper left', title='validated enclosures'); fig.tight_layout(); fig.savefig(FIG/'pulse.pdf'); plt.close(fig)
print('figures written')
