# Postproof continuation: precise conventional proofs

Historical baseline: 80/80. New register: CONTINUATION_TASKS.json (40 roles).
Evidence labels C = conventional proof, K = compiled finite algebra,
R = exact/validated reproducible computation with conventional checker soundness,
N = unvalidated numerical diagnostic. R is not K.

## U1: direction, all finite N

Use the molecular source and chronological construction in PROBABILITY_PROOFS.md.
All rate constants are nonnegative, division has constant rate b>0, and death
is nonincreasing in the order (a,r) <= (a',r') iff a<=a', r>=r'.
At equal a, activating write is larger and activating erasure smaller in the
upper state. At equal r, repressive write is smaller and repressive erasure
larger there. Couple each channel at its common minimum and retain excess
jumps separately. Only equality of the corresponding coordinate can allow
an order-breaking nearest-neighbor jump; the four inequalities forbid it.
On a+r=N the write rates vanish; at a=0 or r=0 the corresponding erase rate
vanishes. Thus the coupling stays in the triangle including its corners.

Use common division clocks and death clocks at the smaller hazard, plus
extra deaths only in the worse cell. Partition common A and R marks with
shared independent fair bits, add the better cell's extra A marks and the
worse cell's extra R marks with further independent bits. Both corresponding
daughters remain ordered. For independent daughters do this separately for
each marginal. Continue recursively, retaining unmatched better subtrees.
Nonexplosion follows from Yule domination. This gives pathwise embedding
within each model and shows that scalar population PGFs, finite-time
extinction, and eventual extinction are decreasing in the molecular order.
It does NOT couple the two different models by population-size dominance.

For independent bits, increasing functions have nonnegative covariance.
Proof by induction: condition on the last bit. The conditional covariance
has nonnegative expectation by induction; the covariance of the two
conditional means is (f1-f0)(g1-g0)/4 >= 0. The base is a one-point space.
Reverse R bits. For an extinction-like decreasing f, f(Y) is decreasing
and f(Z) increasing in every transformed bit. Apply the preceding result
to -f(Y),f(Z). Hence D_J(f,f) <= (D1 f)^2.

Embedded maps F_J,F_I preserve both the ordinary positive order and the
cone of [0,1]-valued decreasing molecular functions (use the stopped
first-event version of the same coupling; death's payoff is 1). Starting
at zero, induction yields F_J^n(0)<=F_I^n(0). Monotone convergence to the
least fixed points gives qJ<=qI, for every finite N. For strictness it
suffices that delta=F_I(qJ)-F_J(qJ) is positive at some state and that
the nonnegative Jacobian secant B has a positive path from the queried
state to that state: h=delta+Bh implies h>=sum_{k=0}^m B^k delta.
No strictness is asserted when both models go extinct almost surely.

For scalar z in [0,1], uJ(t;z) remains in the same cone by the within-model
coupling. The vector field for J at uJ is <= the vector field for I there.
The I vector field is cooperative on [0,1]^S; its off-diagonal derivatives
are nonnegative. The elementary first-contact comparison, with an epsilon
strict supersolution and then epsilon->0, proves uJ(t;z)<=uI(t;z).
This includes finite-time extinction (z=0), not every first-passage event.
First means coincide since the two marginal laws coincide. Nontrivial
stochastic dominance of all population sizes would contradict equal means.

The same conclusion holds with molecular-independent Erlang clocks: augment
the state by phase, compare states at equal phase, couple phase clocks,
and send both daughters to phase zero at division. All arguments apply on
the finite augmented space. More general age clocks require a separate
age-dependent construction; only finite-phase clocks are used here.

## U2: covariance, response, critical margin, and total variation

Write R=(diag(b+d)-Q)^(-1)>=0, T=Rb, and C_J(z,z)=T D_J(z,z).
The covariance identity FJ(z)-FI(z)=T Cov(z(Y),z(Z)) is just conditional
expectation, and depends on the entire predivision mother state.
For h=qI-qJ and delta=FI(qJ)-FJ(qJ)>=0, subtract fixed-point equations.
Difference of two squares yields h=delta+Bh with
B=T diag(D1(qI+qJ)) D1. Therefore h=(I-B)^(-1)delta if rho(B)<1.
If J(ubar)w<=kappa w for w>0,kappa<1 and 0<=qJ<=qI<=ubar,
then 0<=B<=J(ubar), and the Neumann series proves the weighted norm bound
||h||w<=||delta||w/(1-kappa). This explicitly retains the critical margin;
it does not assert that absolute gaps diverge as the margin tends to zero.

For certified probability enclosures 0<=lJ<=qJ<=uJ<=1 and
0<=lI<=qI<=uI<=1, bound delta below by
max(0,T[(D1 lJ)^2-DJ(uJ,uJ)]) and above by
T[(D1 uJ)^2-DJ(lJ,lJ)]. Define B- and B+ by the same nonnegative formula
using lower and upper pairs. If B+ is stable, positivity of the series gives
(I-B-)^-1 delta- <=h<= (I-B+)^-1 delta+.
The exact six-state instance in results/continuation_exact.json checks all
supersolution residuals and the positive weight; source least-fixed-point
iteration supplies lower bounds. No fitted eigenvalue is the certificate.

On the conservation graph, the independent pair law has mass p_ij^2,
while the joint law has p_ij; off it joint mass is zero. Thus TV=1-sum p^2.
The coefficient of x^a in (1+x)^a(1+x)^a proves
sum_i binom(a,i)^2=binom(2a,a), giving the formula in the paper.
For all-active parents central-binomial/4^N tends to zero (e.g. Wallis),
so TV tends to one, not zero. This is a refutation of small-TV scaling.

If each single-bit change alters f by at most c=L_N/N, the Doob martingale
over allocation bits has orthogonal increments with conditional variance
at most c^2/4. Sum over a+r bits: Var f(Y)<= (a+r)c^2/4; same for Z.
Cauchy-Schwarz gives the covariance bound. Taking ||T1||w and the response
margin yields ||h||w <= ||T1||w L_N^2/[4N(1-kappa)].
The regularity premise is literal. No uniform-in-N bounded L_N is assumed.
For the exact source instance every neighboring-state difference is enclosed
by u_i-l_j, and therefore can be certified directly. The margin-dependent
bound replaces the requested near-critical expansion: an O(epsilon^2)
remainder for a varying source is NOT claimed or needed for this endpoint.

## U4: substantial regrowth and finite deadline

Before population size hits 0 or L, there are finitely many configurations.
Positive death rates imply a positive probability of L consecutive deaths
within a fixed time, uniformly over this finite set. Iteration implies
geometric tails for the stopping time, hence almost-sure finiteness.
Binary division hits exactly L. Strong Markov and conditional independence
of descendant subtrees give 1-qx=E[(1-product qXj)1_hit]. Consequently
1-qx<=pL(x)<=(1-qx)/(1-qmax^L) when qmax<1.
The exact supersolution and eight-step lower bound yield the >.059 gap
at L=300; independentUpper.lean checks its finite arithmetic.

For scalar z in (0,1), E[z^K;1<=K<L]>=z^(L-1)P(1<=K<L).
Subtract from 1-P(K=0) to obtain the PGF lower bound stated in the paper.
Its coefficient on u(H;0) is positive, hence use a LOWER enclosure for
u(H;0), and UPPER for u(H;z). A hit by H includes K(H)>=L.

Validated integration: the six-state polynomial has ||Q||infinity=1.06.
In the complex ball ||v||infinity<=2, ||f(v)||infinity<=3.62<4.
Starting from any point of [0,1]^6, complex Picard continuation is analytic
for |t|<1/4 and bounded by 2: the first exit from the radius-one ball
would require length >=1/3.62>1/4. Cauchy bounds give coefficient
|c_k|<=2*4^k and degree-20 tail at h=1/50 at most
2*(2/25)^21/(1-2/25). The coefficient recurrence is evaluated with outward
integer intervals at denominator 10^40. Each endpoint is projected to
[0,1], a nonexpansive operation toward the exact real solution.
On [0,1]^6 the Jacobian is Metzler with row sums <=2b-b-d<=.09.
Therefore its flow is exp(.09t)-Lipschitz in infinity norm. Summing local
tails and interval-rounding errors and using exp(27)<6*10^11 proves the
reported global enclosures. The exponential inequality is checked by a
200-term rational Taylor sum with a geometric remainder. No solver tolerance
or assumed small residual is used. This is R evidence, not a Lean ODE proof.

## U3: corrected size/preparation result and robust readout

The finite source-specific replacement for an unproved size asymptotic is:
at N=16 and every slope s in [7.999,8.001], all-A extinction error is below
.000122, whereas preparation (9,7) has error above .01427. Thus an interior
error estimate below .01 cannot be promoted to a uniform preparation bound,
even for this smooth source. The general corrected bound is the explicit
L_N^2/[N(1-kappa_N)] law above; neither bounded L_N nor a nonvanishing
boundary-layer asymptotic has been proved. The finite result is not offered
as proof of either asymptotic. The bounded N=2,4,8,16,32 diagnostics explain
why this distinction matters and preserve the k/N contact scaling.

Smooth16 certificate: bound exp(x), |x|<=8.001, by its 120-term rational
Taylor series and a geometric remainder; invert positive endpoints for
negative x. Monotonicity in the slope at each state bounds every hazard
for the entire interval. Floor lower hazards and ceil upper hazards at
denominator 10^14. For the upper hazard, test an actual rational PGF
supersolution, componentwise below one, against every exact source row.
For the lower hazard, iterate the positive uniformized fixed-point map
from zero, rounding every nonnegative coefficient down at 10^14. Those
iterates lie below the true least fixed point by induction. Pointwise
death coupling encloses all intermediate hazards, regardless of how the
worst endpoints vary with state. Results retain all 153 state coordinates,
hazard brackets, exact residual minima and rational risk endpoints.

The declared preparation families are all-A (interior),
(floor((N+sqrt(N))/2), N-floor((N+sqrt(N))/2)) (boundary), and a one-unit
predivision molecular hold starting all-A. The hold is an explicitly
controlled preparation experiment: division and death are suspended, so
it is not a drug-treatment model. Its output law is exp(Q^T) delta_allA,
without posterior selection. The main risk examples instead condition on
one known living founder at time zero and do not assert treatment efficacy.

For each same-mean m-phase clock, rate m/10 per phase gives mean 10. Molecular
jumps and death remain active in every phase. The conventional extension
proves the sign for every finite m, but numerical magnitudes/growth at
m=1,2,4 are diagnostics; the quantitative certificate in the main theorem
is specifically for m=1. The substantial numerical clock effect is reported
in the paper, not hidden inside a claimed clock-invariant margin.

The same N=16 certificate also gives a robust substantial-threshold result:
at (9,7), qJ<.48562, qI>.49988, and max qI<.997. Hence pJ_2000>.51438 and
pI_2000<.50012/(1-.997^2000)<.50138, so the eventual hit-2000 gap is >.013.
The exact arithmetic is checked in publication_checks.py. No N=16 finite
deadline and no clinical cell-count interpretation is asserted.

## Observation and empirical limits

Prospectively enroll sister pairs at birth from a specified predivision
mother state and culture each daughter separately under the same challenge.
At a fixed follow-up H record whether its entire clone is extinct, retaining
all deaths and all enrolled divisions. Given Y,Z, the two observed clone
outcomes have probabilities f_H(Y),f_H(Z); conditional independence of
subtrees makes the outcome covariance exactly Cov(f_H(Y),f_H(Z))<=0.
It is zero for independent marginal allocation at a fixed mother state.
This measures continuation fate, not a thresholded chromatin marker.

If conditioning is only on an imperfect parental measurement W, the total
covariance is E[c_X|W]+Var(m_X|W), where m_X=D1 f_H(X), since sister
marginals agree. If the range of m_X in that stratum is at most Delta,
the unidentified mixing term lies in [0,Delta^2/4] by the elementary
range-variance inequality. Thus mean within-mother covariance lies in
[C_obs-Delta^2/4,C_obs] before outcome errors. If each daughter's binary
outcome is misclassified with probability <=zeta, the joint event changes
by <=2zeta and the product of marginal probabilities by <=2zeta, so the
covariance changes by <=4zeta. If a fraction <=epsilon of enrolled pairs
is missing, each probability can change by <=epsilon, giving a further
3epsilon covariance allowance. The resulting sensitivity interval is
[C_obs-Delta^2/4-4zeta-3epsilon, C_obs+4zeta+3epsilon]. Without a justified
bound on Delta or missingness the mechanism is not identifiable by a
pooled covariance sign. Delayed follow-up changes f_H; missed deaths and
divisions must be handled as errors/missingness, never dropped by survival
selection. These are deterministic sensitivity bounds, not estimated
instrument performance or confidence intervals for finite samples.
