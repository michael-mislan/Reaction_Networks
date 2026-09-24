"""Figure 3: memory size, actuator amplitude and certified rates."""
import json, os
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', 'figures', 'sites.pdf')

# certified brackets on the critical intrinsic erasure (exact, denominator 1e6)
CERT = {2: (0.092750, 0.092751), 3: (0.188128, 0.188129), 4: (0.263685, 0.263686),
        5: (0.324157, 0.324158), 6: (0.373695, 0.373696), 7: (0.415181, 0.415182),
        8: (0.450572, 0.450573)}
# exploratory floating values (diagnostics, not certificates)
EXPL = {9: 0.4812, 10: 0.5081, 12: 0.5533, 16: 0.6208, 20: 0.6696, 24: 0.7070,
        32: 0.7615, 40: 0.7996, 48: 0.8281, 56: 0.8501, 64: 0.8676}
# certified mean contraction rate at constant intrinsic erasure e = 1/2
GAMMA = {2: 0.166376, 3: 0.129493, 4: 0.095088, 5: 0.067868, 6: 0.046787,
         7: 0.030242, 8: 0.017016}
# certified brackets on the added-death threshold with no eraser (e = 1/100)
KAPPA = {2: 0.033181, 3: 0.054493, 4: 0.066139, 5: 0.073090, 6: 0.077472,
         7: 0.080374, 8: 0.082373}

fig, ax = plt.subplots(1, 2, figsize=(11.0, 3.9))

a = ax[0]
ns = sorted(CERT)
a.plot(ns, [CERT[n][0] for n in ns], 'o-', color='#1f4e79', ms=5,
       label='critical erasure $e_c(N)$, certified')
a.plot(sorted(EXPL), [EXPL[n] for n in sorted(EXPL)], 's--', color='#1f4e79',
       ms=4, mfc='white', alpha=.75, label='exploratory (floating)')
a.axhline(0.30, color='#c0504d', lw=1.4)
a.fill_between([1.5, 70], 0.0, 0.30, color='#c0504d', alpha=.10, lw=0)
a.text(2.1, 0.255, 'amplitude $v_{\\max}=.29$', color='#c0504d', fontsize=9)
a.text(9, 0.10, 'no admissible policy eradicates\n(certified for $5\\leq N\\leq 8$)',
       color='#c0504d', fontsize=8.5)
a.set_xscale('log')
a.set_xlim(1.7, 75)
a.set_ylim(0, 1.0)
a.set_xticks([2, 4, 8, 16, 32, 64])
a.set_xticklabels(['2', '4', '8', '16', '32', '64'])
a.set_xlabel('sites $N$')
a.set_ylabel('intrinsic erasure $e$')
a.legend(fontsize=8.5, loc='upper left', framealpha=.9)
a.grid(alpha=.25)
a.set_title('Amplitude threshold of the eraser', fontsize=10)

b = ax[1]
ns = sorted(GAMMA)
b.bar([n - .15 for n in ns], [GAMMA[n] for n in ns], width=.3, color='#1f4e79',
      label='$\\gamma$ at $e=1/2$ (eraser)')
kn = sorted(KAPPA)
b.bar([n + .15 for n in kn], [KAPPA[n] for n in kn], width=.3, color='#4f81bd',
      label='$\\kappa_c$, added death alone')
b.axhline(0.09, color='#c0504d', lw=1.4, ls='--')
b.text(4.6, 0.0955, 'proved bound $\\kappa_c\\leq b-d_{\\rm prot}=.09$',
       color='#c0504d', fontsize=8.5)
b.set_xlabel('sites $N$')
b.set_ylabel('rate (inverse synthetic time)')
b.set_xticks(ns)
b.set_ylim(0, 0.195)
b.legend(fontsize=8.5, loc='upper right', framealpha=.95)
b.grid(alpha=.25, axis='y')
b.set_title('Certified rates and the second actuator', fontsize=10)

fig.tight_layout()
fig.savefig(OUT)
print('wrote', os.path.normpath(OUT))
