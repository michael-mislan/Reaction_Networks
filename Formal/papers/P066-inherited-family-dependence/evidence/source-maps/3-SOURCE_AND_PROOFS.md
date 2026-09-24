# Source and conventional proofs

Evidence C unless identified E or N. This is a mathematical synthetic source;
no empirical rates or clinical prescription are asserted.

## Selected scope and literal ROOT target

The primary endpoint is **eventual total extinction after a finite course**.
Two actions A and B, each of duration 10, are compared in opposite orders.
They have identical deadline 20, erasure exposure 2.9 above intrinsic .01,
and additional molecular death exposure 1.20553. M is unaffected by either
action. The target is a certified counterexample to the principle that preserving
all type-resolved mean dynamics preserves this schedule decision, together with
a quantitative replacement margin criterion and an actual-law feedback floor.
This is a two-schedule comparison; no global optimality claim is selected.

## S: construction, daughter rule and mean operator

Types, Q and the two daughter laws are defined literally in experiments/source.py
and equations (1)-(2) of sources/GUIDE.md. Order is UU,UR,RR,AU,AR,AA,M.
For J allocate each of a activating and r repressive marks independently by a
fair bit, giving complementary daughter counts. Binomial normalization and the
bijection of complemented bits prove exchangeability and the marginal Lambda.
I independently samples that marginal and is an approximation, not conservation.
The exact finite sums are checked with fractions in source.exact_checks().

The mother is removed at every division. With probability mu_i=epsilon*kappa_i,
one uniformly selected daughter becomes M; otherwise both sampled daughters
remain molecular. kappa=.4 in AU,AA and .1 elsewhere. Thus 0<=epsilon<=5/2.
Exchangeability makes the mutant offspring PGF y Lambda_i x, and the literal
PGF is (1-mu_i)D_i(x,x)+mu_i*y*Lambda_i x. There are always TWO daughters.
b=.1; d=(.3,.3,.3,.01,.3,.01)+c; e=.01+v. M divides at .1, dies at .02,
and cannot revert. All listed quantities are synthetic assumptions.

For bounded actions the process is constructed using independent marked Poisson
proposals on a countable binary genealogical tree. Total living population is
dominated on finite intervals by a Yule process with birth .1 per individual.
Its finite mean also bounds the expected integrated population and hence total
proposal count for bounded rates. Explosion would require infinitely many
proposals, which has probability zero. Predictable population feedback is
allowed in this construction, but the branching property of independent founder
families is asserted only for deterministic actions and the fixed continuation.

The seven-dimensional backward field is exactly guide (2). Differentiation at
the all-one vector gives the mean operator, with molecular block
A_epsilon=Q+diag(b)((2-mu)Lambda-Id)-diag(d), column M=b*mu, and M diagonal
b_M-d_M. It is identical for J and I. At epsilon=0 the molecular block is A.
The derivative is +A, not -A. Substitution h=1-x gives h'=-Phi(1-h) with the
same positive linearization. Exact checks save both common-marginal and
augmented-mean identities. No printed sign error is imported.

## P: probability, chronological composition and continuation

For a terminal vector g in [0,1]^7 let u_i(t;g) be the expectation, starting
from one type i, of the product of g over all cells living at t (empty product
one). In a first time interval h, one death gives value 1, one type change
gives the new founder's continuation, and one division gives the product of
the two descendants' continuations, averaged over their JOINT birth law.
Probability of two events from one founder in h is O(h^2), uniformly by the
bounded per-cell rates and binary offspring. Nonexplosion, conditioning and
bounded convergence give the first-event integral identity. Its differentiation
gives u'=Phi(u), u(0)=g. Polynomial Lipschitz uniqueness on the invariant cube
identifies the computed solution with this actual expectation. At a zero
coordinate the field is nonnegative; at a one coordinate it is nonpositive,
so the cube is invariant. Smoothness holds on each constant phase.

For chronological A then B, q=F_A^a(F_B^b(g)). No sensitivity coordinate is
reset at a phase boundary. Deterministic founders z give product_i q_i^z_i.
A random founder vector gives its actual mixture expectation; substituting its
mean is invalid. For n fixed AA founders the objective q_AA^n preserves the
one-founder optimizer. This product cannot be used during population feedback.

Terminal zero gives total extinction by T. Terminal (1,...,1,0) gives no M at T.
The killed no-appearance field deletes the mutant offspring term entirely;
the M coordinate is not allowed to evolve from zero. M can appear and then
die with positive probability when mu,d_M,T>0, so appearance and M presence
are different events (a first mutant division followed by death supplies a
positive-probability event separating them).

After T the declared continuation sets mutation to zero, e=.3, c=0, retaining
all other rates. For the molecular mean matrix, the positive weight
w=(14,11,10,84,43,107) satisfies A w<=-.09 w (direct rational residual below).
Expected weighted molecular population therefore decays exponentially; Markov's
inequality implies almost sure extinction, including any finite configuration
at T. The probability that it survives forever is bounded by its probability
of being nonempty at each integer time, which tends to zero.
M's scalar birth-death process has extinction probability r=d_M/b_M=1/5:
first-event conditioning gives roots r,1, and iteration from zero gives the
minimal root r. Binary continuous-time nonexplosion identifies this limit with
extinction. Hence the complete continuation extinction vector is (1^6,1/5).
There is no mutation after T. Finite population at T and conditional independence
then prove eventual total survival equals survival of an M lineage seeded by T.
This proves the endpoint equivalence rather than substituting M risk for total risk.

## H: rare-mutation cancellation and exact finite-amplitude replacement

For molecular terminal one and an autonomous M terminal payoff, y is independent
of epsilon. Polynomial ODE smooth parameter dependence on a compact valid
finite-horizon domain gives x_D=1-epsilon*h+epsilon^2*k_D+O(epsilon^3).
Expansion of the normalized bilinear daughter form gives

    h'=A h+b*kappa*(1-y),
    k_D'=A k_D+b*D(h,h)+b*kappa*(2-y)*Lambda h,
    h(0)=k_D(0)=0.

All products with b,kappa are coordinatewise. Consequently h is common, and
Delta=k_I-k_J obeys Delta'=A Delta+b*(D_I(h,h)-D_J(h,h)), Delta(0)=0.
The forcing is minus the sister covariance. Variation of constants gives its
positive mean-propagator response. Phasewise equations compose without resets.
The Taylor O term here is local at fixed T and rates; it is NOT used to certify
the finite-epsilon decision. Exact arithmetic and Taylor enclosure handle that.

There is also an EXACT response valid at finite epsilon and any common terminal
molecular payoff. Put z=x_I-x_J and

 B(t)f=Qf-(d+b)f+b*(1-mu)*D_I(x_I+x_J,f)+b*mu*y*Lambda f,
 C(t)=b*(1-mu)*(D_I(x_J,x_J)-D_J(x_J,x_J)).

Symmetry and bilinearity give z'=B(t)z+C(t), z(0)=0, with B Metzler.
Thus z(t)=integral U_B(t,s)C(s) ds. This expression isolates all dependence
error from same-marginal mutation. It avoids mistaking an asymptotic remainder
for a usable finite-parameter guarantee. It supplies an absolute bound by
integrating the nonnegative response to |C|. For two schedules, if the absolute
sum of their dependence errors is smaller than an approximate decision margin,
the decision is preserved. Conversely, a change in the two errors exceeding
the signed margin can reverse it. The decisive calculation encloses the four
exact flows and hence these errors directly.

For a sufficient sign condition on the leading coefficient, order states by
increasing a and decreasing r. Constant b, decreasing mortality, increasing
kappa and the ordered reader-writer source preserve nonnegative increasing
mean rewards by the inherited population embedding. Its literal rates and
common mark allocation agree with the source used here. The forcing for h is
increasing, so h is increasing. Reversing repressive allocation bits makes
h(Y) increasing and h(Z) decreasing in independent bits; association (proved
inductively by conditioning one Bernoulli bit at a time) gives covariance<=0.
Then Delta>=0. This is a leading-coefficient sign only; it is not a claim that
the difference of TWO schedule errors has fixed sign. State-dependent b is
excluded because that embedding need not preserve order.

## F: a finite-course feedback barrier compatible with the continuation

The guide's time-independent barrier cannot be used across our mutation-free
continuation: its positive mutation lower bound fails there and q_off is not
bounded by its molecular q<1. The replacement below resolves this mismatch.

Assume during [0,T] all actions have d_i<=dmax, b_i*mu_i>=lambda>0;
M is autonomous with birth beta>death delta and r=delta/beta in (0,1).
Let alpha=(1-r) min(1/2,lambda/(4*dmax)), and define
a(s)=alpha*(1-exp(-dmax*s)), q_S(s)=1-a(s), q_M(s)=r.
Then a<=alpha<=(1-r)/2, so q_S>=1/2 and q_S-r>=(1-r)/2.
All molecular Q terms cancel at this constant molecular vector, and exactly

 Phi_i(q)=d_i*a-b_i*q_S*a-b_i*mu_i*q_S*(q_S-r)
         <=dmax*a-lambda*(1-r)/4
         <=dmax*(a-alpha)=-a'=q_S'.

Phi_M(r)=0=q_M'. Thus V(t,z)=product q_i(T-t)^z_i has
(partial_t+G_u)V=V sum z_i(Phi_i(q)-q_i')/q_i<=0 for every action.
Apply the stopped Dynkin inequality up to bounded population/proposal count,
then nonexplosion and bounded convergence remove stopping, since 0<=V<=1.
At T, V(T,Z_T)=r^{Z_M(T)}, the conditional probability of eventual extinction
under the specified continuation. Therefore for n molecular founders and m M,

 P(eventual total survival)>=1-(1-a(T))^n*r^m

for EVERY admitted predictable feedback course. This is a population test
function, not founder independence under feedback. The same bound is a
resistant-lineage establishment bound precisely because continuation clears S
and creates no new M. It is also <= the total-survival-by-T probability.

The admitted compact action rectangle is .01<=e<=.3, 0<=c<=.121, epsilon=.1.
Here dmax=.421, lambda=.001, r=.2, alpha=1/2105. This action class includes
both compared pulses. At T=20, a(T)=(1-exp(-8.42))/2105>0.
The positive floor excludes arbitrary-risk eradication in this actuator class;
the certified schedule supplies an attainable upper bound at a larger target.
No infinite-time positive-mutation hypothesis is required after withdrawal.
