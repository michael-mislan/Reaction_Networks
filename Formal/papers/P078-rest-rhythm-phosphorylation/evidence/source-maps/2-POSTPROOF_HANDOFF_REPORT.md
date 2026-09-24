# Post-proof research and publication handoff

Date: 20 September 2026. Project: RAF_switchable_phosphorylation_clock.

## Outcome and explicit incompleteness

The publication PDF is `Switchable_Phosphorylation_Clock.pdf` in this project
root. It is a nine-page mathematical paper titled **Rest–rhythm bistability
and single-rate switching in a distributive phosphorylation cycle**. The
editable source is `publication/paper.tex`, with `exact_tables.tex` and a
vector waveform figure. All nine rendered pages were visually inspected;
references resolve and the final LaTeX log contains no overfull, underfull,
undefined-reference or LaTeX warnings. A generic MiKTeX update notice was not
treated as a reason to alter the installed environment.

**The new continuation campaign is a partial result: 35/40 deliverables pass,
five remain open.** The historical 64/64 campaign is preserved separately.
The three new theorem roots are 1 GREEN / 2 RED: local scalar switching is
proved; quantitative finite scalar operation and a joint numerical physical
parameter region are not. The paper states those boundaries and does not
present the numerical finite protocol as proved. No full Lean proof of the
ODE theorem has been claimed or produced. Both new small Lean modules
compile strictly, as does the inherited selected algebra.

The unresolved registered items are:

| Item | Remaining mathematical implication |
|---|---|
| D2 | A numerical section radius on which the return map exists and contracts, with a positive flow tube |
| D3 | Rounded ON waveform tube ends strictly inside that cycle capture neighborhood, with a positive numeric uncertainty budget |
| D4 | Rounded phase-triggered OFF tube reaches the sink capture set, including preparation/timing margins |
| D5 | Assemble a finite quantitative operating theorem and certified settling/repetition rules from those inclusions |
| E4 | A joint nonzero numerical region of independent physical rates/totals preserves the adopted sink and cycle |

These are unresolved mathematical enclosure gaps, not evidence that scalar
switching is impossible. The most useful next calculation is specified
below. The report does not turn an unfinished theorem into a passed task.

## Strongest new proof

The exact alpha1 association reaction changes S1 and F by minus one and D1
by plus one. In the pool/complex chart its pool increments cancel, leaving
only coordinate6. Consequently relative modulation produces exactly
`u alpha1 S1 F e6`; at the GH equilibrium the input is `(1+r)q1 e6`.
This actuator differs from a reconstructed multi-rate family that preserves
the equilibrium throughout a pulse.

The supplied interval Kalman test was incorporated as a separate checker
and run twice in the canonical environment. Over the entire inherited
radius-1e-20 GH root box, with 80-decimal directed intervals, the determinant
of `[e6,(J/100)e6,...,(J/100)^8e6]` lies in
`[-1.874031380e-46,-1.874028367e-46]`. All nine Gaussian pivots exclude zero.
Thus the input controls all nine class directions. The determinant's small
scaled magnitude is not an energy estimate.

The new ordinary proof chooses nine fixed compactly supported temporal
functions whose linear endpoint images span the class. The nonlinear
endpoint map has an invertible coefficient derivative at GH. The
parameterized implicit-function theorem yields one neighborhood of initial
states, targets and baselines, chosen at GH before selecting a coexisting
member. The sink and entire attracting cycle tend into that neighborhood.
This uniformity closes the logical gap that would remain if one simply
asserted that each sink's unknown controllability neighborhood reaches its
cycle.

For any prescribed positive duration and relative bound eta<1, sufficiently
nearby coexisting baselines therefore have smooth alpha1-only ON and
phase-selected OFF controls below eta, positive concentrations and rate,
unchanged other rates/totals, smooth return to baseline, and positive
qualitative preparation/control tolerances. This result does not identify a
practical baseline or a pulse at the separate finite source.

The supported asymptotic family has attractor displacement O(sqrt epsilon),
fixed-basis waveform coefficients of that order and squared L2 cost
O(epsilon), as upper bounds only. Recovery scales as epsilon^-2 and the
transverse unfolding wedge width as epsilon^2 on an interior wedge family.
Large endpoint inverse constants remain possible. This ancillary tradeoff
is documented in the proof record but omitted from the PDF's critical path.

## Foundation replay and focused audit

The canonical interpreter check and full numerical smoke suite passed.
One bounded inherited replay passed all six stages: local GH, directed
finite-source defect, Fourier existence, positive finite geometry,
transverse attraction and exact control algebra, in approximately90.5s.
NPZ inputs were real arrays. The source remains the exact dyadic xstar,
currents and r, with all other reverse ratios exactly1/100.

The focused review checked the preconditioned l1 Banach space, bounded tail
resolvents and k-times-resolvents, injectivity, conjugacy and regularity;
the source/assembly error budget and complex matrix operation counts;
actual-orbit/frequency perturbations, phase/step/frame errors; and interval
event projection and Lyapunov LDL. No concrete fatal defect was identified
under the stated arithmetic model. The review is not independent kernel
verification of every floating-point operation. The saved argument states
that limitation explicitly.

Stale claims that the finite orbit and qualitative full-rate control were
still red were removed from the mathematical supplement. The chart and
homological equations are now supplied directly rather than defined by an
external research guide. The paper omits the full-actuation path lemma,
discovery plots and exploratory auxiliary results because they are not
needed for its final single-rate proof path.

## Finite control experiments and what they discriminate

All numerical campaigns were single-threaded where BLAS permits and bounded
by process_guard. No brute-force actuator-pair campaign was launched.

1. A quadrature-factor SVD of the finite-horizon scalar Gramian measured
   weak directions without binary64 powers of a stiff Jacobian. The
   one-period factor has smallest singular value about2.73e-6 and condition
   about1.14e6 in the declared amplitude-scaled chart. The weak direction is
   dominated by the second pool and coupled complex directions. Linear
   exact-target ON costs are large; this does not exclude nonlinear basin
   transfer. These values are numerical diagnostics, not interval rank tests.
2. The first nonlinear pilot used twelve bounded Gaussian windows with a
   sin-squared envelope, one period, phase zero and |u|<=0.8. Six-decimal
   rounded ON/OFF endpoint errors were0.213501 and0.026219. Optimization hit
   its22-evaluation limit. The endpoint derivative's smallest singular
   values were below1e-13: the low-bandwidth temporal basis introduces much
   worse conditioning than the full input space. This is not loss of
   controllability or proof of amplitude infeasibility.
3. Increasing the horizon to three periods and selecting phase pi/2 reduced
   rounded ON/OFF errors to0.009254 and0.001458. The resulting schedules
   are retained as the finite candidates. They are C1 and piecewise smooth
   when joined to baseline, not the C-infinity basis of the local theorem.
4. Baseline continuation after these rounded endpoints approached the
   intended attractors. Over150 periods, ON nearest-cycle distance fell
   from0.00708 to about6e-6; OFF sink distance fell to0.000237. Numerical
   integration and phase-fitting errors are not enclosed, so these are
   successful diagnostics rather than basin certificates.

The important lesson is to validate capture, not spend unlimited effort
forcing an exact endpoint. The candidate's existence is now plausible;
the remaining difficulty is an enclosure and settling argument.

## Capture calculations and next proof route

A directed-interval quadratic Lyapunov calculation produced the explicit
sink ellipsoid `||S y_scaled||<=1e-9`. It verifies lambda>1.2418e-5,
K<1807.452 and exponential norm decay>1.0610e-5 inside the ellipsoid.
Species displacement bounds and a Euclidean preparation radius are saved.
The latter is above6.8761e-12 in the declared scaled chart. This is a
sufficient inner capture set, not an estimate of the basin's true extent.

The candidate OFF endpoint has metric distance0.040459, falling to0.007443
after150 periods, both above1e-9. That is the precise failed inclusion.
The conservative Frobenius tensor bound is a dominant contributor; longer
settling or a sharper nonlinear Lyapunov function could help, but neither
has yet been certified for the candidate tube.

At the cycle a second-variation numerical pilot computed the return-map
Hessian, including event-time derivatives. Nominal metric contraction is
0.982710 and Hessian Frobenius norm is23.603. A uniform bound of that size
would suggest a radius around3.66e-4. It is only a value at the orbit.
The direct raw-J norm Gronwall majorant instead has logarithm base10 near
140677. Increasing Taylor order does not repair that correlation loss.

A further targeted pilot used a periodic Lyapunov metric, satisfying the
nominal differential equation with growth rate mu=0.02. It reduces nominal
one-period amplification to1.775, has periodicity residual1.11e-11 and
sampled eigenvalues between0.00404 and6436.72. The transformed tensor norm
peaks near1861.18, giving a nominal second-variation majorant2.99e5. This
shows a viable conditioning improvement over the global-J bound.

**Next discriminator:** validate the periodic metric differential inequality
against the Fourier-ball orbit/frequency uncertainty, then propagate the
nonlinear tube and event Hessian with that metric, retaining conversion to
the certified section metric. A Fourier representation of the saved metric
and a residual inequality is a concrete starting point. Sampled positivity
and a small nominal periodicity residual alone do not prove it. Only after
that succeeds should the rounded pulse tube and parameter-dependent
continuation be enclosed. No bulk certificate replay is recommended.

## Physical and parameter follow-ups

All21 independent log-parameter sink sensitivities were computed, with
equilibria re-solved rather than reconstructed. A targeted negative-Ftotal
continuation located the sink's numerical Hopf boundary at log displacement
-0.0007031861. Four continued sink/cycle pairs reveal a Pareto tradeoff:
increasing Ftotal improves sink recovery but worsens cycle recovery and
reduces readout range. At offsets -0.0002,0,+0.0001,+0.0002 the numerical
cycle recovery ratios are10.53,13.75,16.41,20.69 periods; sink ratios are
123.70,89.19,78.43,70.11. These samples are not a joint interval region.

The full rate/total table separates molecularity and units. An uncalibrated
C0=0.1 micromolar,T0=100s example has47.82-minute period,10.96-hour cycle
e-folding and2.96-day sink e-folding. A certified readout derivative bound
0.33 supplies a sampling-loss bound; with gap<=0.29 and declared measurement
and settled tracking errors, threshold1 separates the stated cases. No
arbitrary OFF transient is assumed settled.

Sink linear-noise covariance and cycle phase-adjoint diagnostics were
computed at declared volumes. The 1fL Gaussian free-F standard deviation
exceeds its mean, warning that the local approximation is not useful there.
Eight short SSA paths at1 and10fL conserve integer totals exactly; source
rounding discrepancies, seeds, propensities and event caps are recorded.
All finished, but two paths per case over one period cannot estimate
retention or switching probabilities. No escape-time claim is made.

A limited finite-fuel inventory extension bounds kinetic drift using
`A0-A(t)<=t E_T max(c_i)`. The100-period,1%-drift sufficient inventory bound
is about5.998e7 model units, versus nominal222.75 units consumed per period.
This is conservative and is not a physiological requirement or a
thermodynamically consistent ATP/ADP/Pi completion. An actuator must still
be characterized experimentally, including off-target rates, timing and
phase sensing. Fuel and noise results remain outside the paper's proof path.

## Reproduction, AGC and saved evidence

`POSTPROOF_REPRODUCE.md` gives minimal checker commands and separately lists
the optional numerical scripts. `postproof_theorem_evidence.json` is the
claim/dependency map; `postproof_input_hashes.json` records provenance.
`daily/2026-09-20.md` continues globally numbered sprints. The old register
and old handoff remain historical records. Failed Lean and numerical
attempts were retained rather than overwritten as successes.

SingleInputColumn.lean compiled strictly. CaptureInequality.lean first failed
because an unnecessary hypothesis triggered the unused-variable warning;
removing that hypothesis produced a strict clean compilation. This was a
formal hygiene failure, not a failed mathematical inequality. The final
new-claim replay reran rank, sink capture and physical interpretation.
Unchanged inherited certificates were not repeatedly rebuilt.

Actual AGC checkpoints were saved at entry, scalar closure, finite-pilot
failure, the periodic-metric route and handoff. The handoff classification
was `current_with_unbound_authored_route`, with `guidance_safe=true`; earlier
checkpoints reported authored-route refinement. AGC was useful for lifecycle and
freshness checks, but its historical focus did not supply the new scalar
endpoint argument or resolve the enclosure gap. It does not certify these
mathematical claims. No protected theorem graph was published, no dependencies
were changed, and no generated evidence was committed by this task.

The paper is ready as a presentation of the proved results. The continuation
brief is not fully completed: the five registered quantitative obligations
above remain open and are the reason for this partial-result handoff.
