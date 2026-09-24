# Hopf capacity of the literal three-site phosphorylation cycle

Final research handoff, 17 September 2026. The source-level Lean theorem is proved:
`ThreeSitePhosphorylation.three_site_hopf_capacity` in
`proofs/ThreeSitePhosphorylation/Resolution.lean`. Strict verification and its
authenticated declaration/axiom export passed in 50.703 seconds. The user's
compiled-proof stopping criterion is met. See `resolution.verify.json`.

## Statement and evidence boundary

The sequential, distributive three-site mass-action phosphorylation cycle admits
a nondegenerate subcritical Hopf bifurcation at a strictly positive equilibrium,
with all eighteen rates positive and all three conserved totals fixed along the
unfolding. The construction below supplies a conventional computer-assisted proof:
exact polynomial arithmetic, rational isolating intervals, directed rational
interval arithmetic, and the classical finite-dimensional Hopf theorem.

The Lean theorem independently proves Hopf capacity: a transverse source
eigenvalue branch and arbitrarily small positive, nonconstant, whole-line periodic
solutions on the fixed compatibility class. Its analytic implication is proved
using amplitude rescaling and two implicit-function arguments. It assumes no
Hopf theorem or numerical certificate. The stronger direction/stability claim
"nondegenerate subcritical" and the numerical value of the first Lyapunov
coefficient remain ordinary computer-assisted results, not Lean conclusions.

## Literal source and witness

For i=1,2,3 use precisely

S_(i-1)+E <-> C_i -> S_i+E,

S_i+F <-> D_i -> S_(i-1)+F.

All bindings are bimolecular; reverse and catalytic reactions are unimolecular.
There are no additional reactions. C_i here is C_(i-1) in the all-n manuscript.
The species order is (S0,S1,S2,S3,E,F,C1,C2,C3,D1,D2,D3).

Set the equilibrium to

```
x* = (30,13,19/100,9/100,33/10,1,13/25,7/250,39/50,93/10,3/20,5/2).
q  = (1/10,39/5,1).
```

The kinase reverse ratios and the last two phosphatase reverse ratios are 1/100.
The first phosphatase reverse ratio is r>0. Rates, in binding/reverse/catalytic
order for each arm, are:

| Arm | Binding | Reverse | Catalytic |
|---|---:|---:|---:|
| K1 | 101/99000 | 1/520 | 5/26 |
| K2 | 101/550 | 39/14 | 1950/7 |
| K3 | 1010/627 | 1/78 | 50/39 |
| F1 | (1+r)/130 | r/93 | 1/93 |
| F2 | 3939/95 | 13/25 | 52 |
| F3 | 101/9 | 1/250 | 2/5 |

For each arm, binding flux equals reverse plus catalytic flux. Opposing catalytic
fluxes are q_i on edge i. Therefore the full twelve-dimensional vector field
vanishes identically at x* for every r. This is an exact identity. Rates are
strictly positive for r>0. The totals, independent of r, are

```
E_T = 1157/250, F_T = 259/20, S_T = 28279/500.
```

The stoichiometric rank is nine. Six binding columns have independent complex
coordinates. Adding each kinase catalytic column to its binding column gives
one adjacent substrate difference; the three differences are independent.
The three conserved totals give the matching upper bound.

## Exact compatibility-class coordinates

Use displacement coordinates y=(u1,u2,u3,c1,c2,c3,d1,d2,d3). The twelve species
displacements from x* are

```
(-u1-c1, u1-u2-c2-d1, u2-u3-c3-d2, u3-d3,
 -c1-c2-c3, -d1-d2-d3, c1,c2,c3,d1,d2,d3).
```

This linear map P has a left inverse R given by cumulative input-level substrate
pools and the six complex coordinates. It maps R^9 bijectively to the tangent
space of the fixed-total affine class. All concentrations are positive on an
open neighborhood of y=0. The reduced field is R f(x*+Py;r), and f= P R f on
that class. Independent symbolic differentiation checked these identities, the
equilibrium identity, and every Hessian entry directly from the eighteen reactions.

The reduced field is polynomial of degree two in y and smooth in r. Its Jacobian
J(r) has the exact block form in the supplied guide. The complex-relaxation
block remains strictly stable, but that alone does not control the full feedback.

## Algebraic definition of the Hopf point

Let p(z;r)=det(z I9-J(r)). The reverse family changes the source Jacobian by
the rank-one matrix -r q1 nu nu^T diag(1/x*), where nu is the F1 binding column.
Consequently p=p0+r p1. The exact rational coefficient arrays of p0 and p1,
in descending powers, are stored in
`experiments/candidate_certificate.json`, key `source`. The independent checker
derives J from the literal source and verifies the polynomials at r=0,1,2 and
rank one of the parameter derivative. Affineness plus the first two values
establishes the identity for every real r; the third value is a control.

Define E_k(t), O_k(t) by p_k(i sqrt(t))=E_k(t)+i sqrt(t) O_k(t).
Define Phi=O0 E1-E0 O1. The certificate records its full exact coefficients and
an exact rational isolating interval with width below 10^-55 containing its
unique positive root t*. The Sturm root count on that interval is one and the
root is simple. Define

r* = -(E0 E1+t* O0 O1)/(E1^2+t* O1^2), evaluated at t*.

The denominator is bounded away from zero by directed rational arithmetic.
The identity Phi(t*)=0 proves both real frequency equations: substitution into
E0+r*E1 and O0+r*O1 leaves respectively -t*O1 Phi/den and E1 Phi/den.
Thus p(i sqrt(t*);r*)=0 exactly, not just to floating precision.

Readable enclosing bounds, deliberately much wider than the stored bounds, are:

| Quantity | Strict enclosure |
|---|---|
| t* | (0.03253896252, 0.03253896254) |
| r* | (0.26553704252, 0.26553704254) |
| omega*=sqrt(t*) | (0.18038559401, 0.18038559403) |
| Re(lambda'(r*)) | (-0.04649665728, -0.04649665726) |
| first Lyapunov coefficient | (0.66961007953, 0.66961007956) |

## Isolation, crossing and nonlinear certificate

Divide p by z^2+t*. The exact remainder vanishes by the frequency equations.
For the degree-seven quotient g7, every entry of the Routh first column is
strictly positive. Approximate values are

```
1, 406.1426, 35862.2862, 1085458.1082,
10924589.8727, 24494015.5711, 5131445.8541, 15020.8749.
```

Every sign is certified by stored rational intervals. Therefore all seven roots
of g7 are strictly in the left half-plane. The imaginary pair is simple and
isolated, and the reduced Jacobian and 2i omega* I-J are invertible.
Implicit differentiation of the simple root gives
lambda'=-p1(i omega*)/p_z(i omega*;r*). Its real part has the negative enclosure
above. The same x* and totals hold along this smooth two-rate unfolding.

The affine chart preserves quadratic degree, so the third derivative tensor is
zero. Write the reduced field as J y + B(y,y)/2. Choose a right eigenvector v
with final coordinate one and a left bilinear eigenvector ell with ell^T v=1.
Then the convention used is

l1 = Re(ell^T[-2 B(v,J^-1 B(v,conj(v)))
             +B(conj(v),(2i omega* I-J)^-1 B(v,v))])/(2 omega*).

This is the usual adjoint formula with ell=conj(p). The Hessian B was derived
twice: directly from source polynomials and from the binding-product formula;
all entries agree exactly. Eigenvectors are constructed by invertible 8x8
minors, with the remaining equation following from the zero determinant.
All normalization and resolvent divisions are enclosed away from zero.

The interval checker rounds outwards to a 160-bit dyadic grid after every real
arithmetic operation. Each multiply takes the minimum/maximum of all four
endpoint products; reciprocals require an interval excluding zero. Square roots
use integer square roots with outward bounds. Complex arithmetic uses pairs of
these real intervals. Gaussian elimination encloses each solve and checks every
pivot denominator. Thus the result encloses exact evaluation at the algebraic
root, rather than a floating approximation to it.

Independent 90-digit evaluation, with J and B obtained through symbolic source
differentiation, gives

```
l1 = 0.669610079541494420427650411726755636922699880821322280...
```

It falls inside the rational interval. This independent numerical calculation
is corroboration; the interval computation supplies the sign certificate.

## Conventional dynamical conclusion

Apply the finite-dimensional Hopf theorem to the smooth reduced nine-dimensional
family at (y,r)=(0,r*): the equilibrium persists, the sole imaginary pair is
simple with positive frequency, its real part crosses transversely, and l1 is
nonzero. These verified hypotheses imply nonconstant small periodic solutions
bifurcating from x* on this fixed compatibility class. Since x* is strictly
positive, sufficiently small bifurcating solutions remain positive.

The positive Lyapunov sign makes this Hopf subcritical. Since the crossing
derivative is negative, the small unstable cycles are on the r>r* side; the
equilibrium is stable on that side near r*. No attracting cycle is claimed.

Analytic reference: Kuznetsov, *Elements of Applied Bifurcation Theory*, second
edition, Chapters 3 and 5 (Hopf normal form and center-manifold reduction):
https://www.ma.ic.ac.uk/~dturaev/kuznetsov.pdf . The same multilinear coefficient
formula is given explicitly as equation (1) in Badiale–Cravero:
https://arxiv.org/html/2511.08428v1 . These analytic results are applied in the
ordinary proof. The general normal-form and stability results are not supplied
as Lean theorems; the source-level periodic-existence implication is now proved
directly in Lean, as described below. See POSTPROOF_HANDOFF.md for the completed
publication follow-ups and the ordinary all-site extension.

## What the experiments taught us

1. All four preparation controls reproduced exactly. The initial 18 reverse
   slices gave no admissible pair. The single positive frequency required a
   negative reverse ratio. This was a slice obstruction, not universal exclusion.
2. Residence-time/flux asymmetry changed the picture. A small optimization of
   complex growth located instability while the static pool approximation stayed
   stable. Its final objective approached a real collision and was unsuitable
   as a certificate. Continuation from the control exposed the earlier genuine
   nonzero-frequency crossing in two independently selected leads.
3. Coarse rational rounding landed on the stable side: all reconstructed reverse
   ratios remained negative. Moving the background slightly to the unstable side
   yielded the positive F1 reverse ratio above. The successful step was informed
   by the sign obstruction, not a larger enumeration.
4. The stable relaxation block does not rule out a destabilizing finite-time
   feedback response. Static elimination misses this example's mechanism.
5. The inherited saturating child cannot be directly realized, but that
   incompatibility does not exclude other admissible mass-action feedback.
6. A subsequent compression test fixed omega=9/50 and allowed one inverse
   concentration plus r to vary. Multi-affinity reduced the condition to a
   quadratic; several positive roots were found. These are formalization leads,
   not replacements for the fully checked witness above. Their nonlinear
   conditions have not been re-certified, and switching witnesses must earn its
   cost by reducing actual Lean obligations.


7. The adjugate-column experiment exposed a constant rational companion basis.
   Its inverse reduced source spectral questions to a scalar polynomial and
   a simple recurrence. This replaced a large symbolic determinant expansion.
8. Exact Horner signs isolated seven distinct negative real roots, uniformly for
   r in [1/4,3/10]. A separate frequency-equation bound puts the critical ratio
   inside that interval. The resulting eigenbasis was useful for the actual
   shooting inverse, not merely a stronger spectral description.
9. The amplitude-rescaled shooting pilot at a=0.001 converged in 17 Radau
   integrations, under seven seconds, with endpoint residual 5.4e-14. The
   linearized augmented matrix had smallest singular value about 0.06537 and
   condition number about 66.44. This tested the proposed analytic route; none
   of those floating-point quantities is an input to the Lean theorem.
10. A factorial Volterra bound removed the need to compose thousands of short
    time steps. The full-period Banach IFT can be applied once, even though a
    direct one-step contraction estimate is not small. The ordinary numerical
    route and formal route consequently share the source but use different
    evidence for the final dynamical implication.

## Exact final Lean conclusion

There exist r0>0, w>0 and a smooth local complex eigenvalue branch g through iw,
with strictly negative derivative of its real part. Near r0 each g(r) is an
actual eigenvalue of the reduced source Jacobian. For every epsilon>0 the theorem
provides r>0, T>0 and a function phi: R -> R^12 such that:

- all eighteen witnessRates(r) are strictly positive;
- |r-r0|<epsilon and |T-2*pi/w|<epsilon;
- phi is T-periodic on the whole real line;
- phi'(s)=field(witnessRates(r),phi(s)) for every real s, including period seams;
- every concentration is strictly positive at every s;
- ||phi(s)-witnessState||<epsilon uniformly in s (the finite-product sup norm);
- all three totals equal the fixed witness totals at every s;
- phi is nonconstant.

The theorem has no input hypotheses. Source.lean separately proves the witness
is an equilibrium for every r, and Rank.lean proves the compatibility rank is
nine. Simplicity and isolation of the critical pair are proved in the spectral
chain. This is the existential three-site Hopf-capacity resolution, not an all-n
classification. No attracting-cycle claim is made by the Lean theorem.

## How the analytic proof closes

Write the reduced source exactly as f(r,y)=J(r)y+Q(r,y), with Q homogeneous
quadratic. Set y=a*u and extend the rescaled equation to a=0:

    u' = T*(J(r)u + a*Q(r,u)),  0 <= s <= 1.

At a=0 choose the nonzero eigen-orbit with T=2*pi/w. On continuous paths, the
integral residual has derivative 1-V_(TJ). Volterra proves
||V_A^n|| <= ||A||^n/n! for every bounded real linear operator A. A power therefore
has norm below one, and a finite geometric identity yields invertibility of
1-V_A. The Banach implicit-function theorem supplies smooth paths on the whole
unit interval. The fundamental theorem of calculus identifies their actual ODE.

The endpoint residual has nine real components. A normalized complex left
functional supplies two real initial phase/amplitude constraints. Unknowns are
the nine initial coordinates, reverse ratio, and period. For its kernel:

1. Differentiate the source integral equation. This gives the full initial,
   parameter, and period variational equation, without assuming a flow derivative.
2. Project to the critical left eigenvector and use an integrating factor.
   Periodicity kills the resonant forcing coefficient. Its real part is the
   strictly negative eigenvalue-crossing pairing times the ratio variation.
   Hence that variation vanishes, and the imaginary part kills period variation.
3. Project the now-homogeneous equation onto the seven negative real eigenmodes.
   Their exponential multipliers cannot equal one, so all seven coordinates vanish.
4. The gauge kills the positive critical coordinate. A real vector supported on
   the remaining imaginary eigenspace must be zero, by taking imaginary parts of
   its eigen-equation. Thus the initial variation is zero.

The finite-dimensional derivative is injective and hence invertible. The second
IFT produces a smooth nonlinear closed-path family indexed by amplitude. Uniform
continuity preserves positivity and smallness. The initial rescaled velocity is
nonzero, so nonzero amplitude yields a nonconstant source trajectory. The affine
chart lifts it to the twelve-species source. A separately proved seam derivative
extends it periodically to all real times; time rescaling gives physical period T.

This proves the dynamical implication directly. There is no assumed generic Hopf
record, Python premise, native unchecked computation, or finite replay standing
in for an infinite-domain assertion.

## Proof and evidence map

See CLAIM_MAP.md for exact paths and evidence levels. The principal chains are:

- Source / Rank / Jacobian: literal mass action, equilibrium, fixed class, exact
  source derivative and quadratic Taylor identity.
- Frequency / FrequencyData / Polynomial: exact positive frequency root and
  admissible positive ratio.
- Spectral / Companion / PolynomialBasis / CompanionSpectral / SpectrumNecessary:
  actual source eigenpair and exact companion similarity in both directions.
- PolynomialIsolation / SpectralIsolation / SimpleRoot / Semisimple / SourceSimple:
  critical frequency isolation, simple root, eigenline and no Jordan chain.
- EigenBranch / CrossingQuotient / TransverseBranch: actual smooth transverse
  source eigenvalue branch.
- ParameterDomain / RealSpectrum / Eigenbasis / LeftProjection: seven negative
  modes and the normalized left/right crossing pairing.
- Volterra / RescaledSource / PathSource / SmoothPaths / LinearOrbit / SourceFlow:
  full-period smooth source paths around the linear eigen-orbit.
- ScalarODE / HarmonicForcing / EigenCoordinates / HomogeneousKernel /
  ResonantKernel / ComplexOrbit / SourceVariationalKernel: periodic mode elimination.
- PathODE / VariationalPaths / VariationalODE / PathKernel / ShootingMap /
  ShootingInverse / ClosedPaths: actual shooting inverse and nonlinear closed paths.
- SourceLift / FamilyBounds / PeriodicExtension / GlobalOrbit / SourceOrbits /
  Resolution: positive nonconstant whole-line source solutions and final theorem.

Resolution's strict receipt covers all 51 local imported dependencies, as well as
the final module and authenticated theorem interface. The exported axiom list is
exactly Classical.choice, Quot.sound, and propext. No sorryAx or custom axiom occurs.
Some earlier compile-only receipts are failed attempts or diagnostic-only receipts;
they are not the final proof authority. The complete final dependency closure is
recorded in resolution.verify.json. Never rerun an old generator over a proof file
without checking it: several early generators intentionally produced pilots and
were superseded by in-place proof development.

## Reproduction and performance

Use the pinned repository environment. From E:\Erdos Problems:

```powershell
& '.venv/Scripts/python.exe' scripts/check_python.py --quiet
& '.venv/Scripts/python.exe' scripts/verify_proof.py proofs/ThreeSitePhosphorylation/Resolution.lean --timeout 600 --declaration ThreeSitePhosphorylation.three_site_hopf_capacity --output 'problem_workspaces/RAF_hopf_ bifurcation_three-site_phosphorylation_cycle/resolution.verify.json'
```

The bridge enforces the mathlib4_project working directory. The final warm-cache
run took 50.703 seconds including the declaration probe; a cold replay will take
longer. Lean is 4.30.0, mathlib is pinned at
c5ea00351c28e24afc9f0f84379aa41082b1188f. No dependencies were updated.

For ordinary numerical reproduction first run scripts/smoke_numerics.py with the
same interpreter, then workspace experiments/three_site_prep_check.py,
reverse_pilot.py, certify_candidate.py, and independent_certificate_check.py.
The other experiments and their JSON outputs retain discovery and compression
history. Use scripts/process_guard.py for any run expected to exceed 30 seconds;
pass the absolute canonical interpreter to its child command. Discovery and
shooting pilots were single-worker jobs lasting seconds. Only one Lean compilation
chain ran at a time. Timed-out compilations were bounded, diagnosed, and retried;
they were never accepted as evidence. No bulk numerical search or certificate
campaign was launched.

## AGC and final handoff state

The final mathematical root is CLOSED by the strict Lean receipt. AGC checkpoints
were used at entry, new structures, failed routes, and the final proof gate. AGC
helped preserve the distinction between a spectral witness and a source-level
periodic theorem. Its route advice remained behind the mathematics and did not
supply the key analytic simplifications.

The final checkpoint first requested reconciliation of the newly authenticated
receipt. The exact self-service command succeeded with
BOUND_SAME_FRONTIER_PROOF_INPUTS. The subsequent checkpoint is CURRENT, recorded
in logs/checkpoint_root_reconciled.json. However post-proof-publish returned
AGC-POST-PROOF-E001: no synchronizable live frontier: NO_OPEN_FRONTIER. This
workspace has an AGC spec but no explicit live theorem graph; its generic published
open-cut guidance therefore still lists the old nodes. No protected theorem graph
was fabricated or marked closed. Canonical AGC graph integration/publication is
an administrative follow-up for the authority integrator, not a missing theorem.

Final guide score: 59/60 PASS, 1 BLOCKED (task 59's live-graph reconciliation).
Task 48 and the user's mathematical stopping criterion are complete. Tasks 55,
58 and 60 are complete through the claim map, final checkpoint, and this report.
The timestamped ledger is logs/2026-09-17.md; it preserves failures and superseded
frontiers rather than erasing them. Generated receipts/publications have not been
staged or committed. No other mathematical task's files were modified.

No unresolved mathematical implication remains for the stated Hopf-capacity
existence theorem. Formalizing the Lyapunov-coefficient sign, subcritical direction,
or orbital instability is additional work beyond this root; those claims retain
their explicitly separate ordinary certificate here.
