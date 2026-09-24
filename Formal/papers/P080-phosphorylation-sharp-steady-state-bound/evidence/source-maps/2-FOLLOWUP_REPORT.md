# Postproof research and publication handoff

19 September 2026. Problem: sharpness of the 2n−1 positive-equilibrium bound for the literal sequential distributive n-site phosphorylation mechanism. The original campaign remains complete at 60/60. This report records the successor guide's follow-ups; it is deliberately separate from the publication manuscript so discovery diagnostics and optional engineering work do not interrupt the proof.

## Final mathematical claims

The manuscript proves a uniform construction for arbitrary n≥1 and any 2n−1 distinct positive free-enzyme ratios. It constructs a single positive rate list and three common positive totals and reconstructs that many distinct positive full mass-action equilibria. Wang–Sontag's Theorem 3 supplies the upper bound and therefore equality. Every constructed equilibrium is nondegenerate on the 3n-dimensional stoichiometric subspace. An ordinary implicit-function argument then gives a nonempty open subset of the full 6n+3 original rate/totals parameter space with exactly 2n−1 positive nondegenerate equilibria. This is not a claim of 2n−1 stable states.

When x_j=sqrt(1+8u_j) are rational, all rates, totals and states can be rational. The proof does not give rational data for every arbitrary rational u-list. Choosing rational x_j gives a dense collection of rationally realizable lists. The original all-n rational example uses x_j=j+2.

The proof's only construction dependencies are the positive paired-root recurrence, its product identity, the exact polynomial quotient, the explicit large-r positivity estimate, source realization and common-total identities. Simple-root differentiation and nonsingular source elimination establish the immediate nondegeneracy and openness conclusions. No numerical search or finite family of certificates is a premise of the all-n theorem.

## Exact evidence and formal scope

| Claim | Evidence | Scope |
|---|---|---|
| All-n real source attainment | `../certificates/lean_resolution.json` | Five original Lean modules, strict zero-exit warning-free verification; standard axioms only |
| Receipt still matches checkout | `data/formal_receipt_reuse.json` | All original proof source hashes checked; no unnecessary repeated build |
| Arbitrary paired-root recurrence, dense positivity, distinct-root product, residual factorization, enzyme-total determinant identity, negative slope prefactor | `proofs/PhosphorylationSharpness/PublicationAlgebra.lean` at repository root and `data/lean_publication_algebra.json` | New module compiled warning-free, 87.531 seconds; exported declaration audit for prescribedPair_identity uses only standard Lean axioms |
| Arbitrary-ratio full source endpoint; rationality; upper-bound equality | Manuscript Theorem 1 and construction | Ordinary proof; original Lean endpoint is the special arithmetic-list real-attainment theorem |
| Full derivative formula, source Jacobian nonsingularity, openness | Manuscript Section 6 | Complete ordinary arguments; not claimed as new compiled Lean endpoints |
| Literal source replay and derivative identity, n=1,…,8 | `exact_review.py`, `data/exact_review.json` | 8 instances, 64 states, exact rational arithmetic; independent implementation checks |
| Three-site stability | Exact characteristic coefficients, restricted matrices and Routh columns in `data/exact_review.json` | Conventional exact rational computation, not a Lean theorem |
| Tolerance box | `data/tolerance_box.json` | Exact rational interval arithmetic for independent original enzyme and substrate totals; equilibrium existence/count only |

The raw versus normalized polynomial convention has been checked: multiplying A,B,D by k>0 and replacing s by s/k preserves every coefficient ratio defining a rate and every coefficient-times-s concentration. The ordinary paper takes D(0)=1; the original formal assembly uses raw coefficients. Stale statements that the root still awaited Lean compilation have been corrected in the ordinary proof and structural review.

## Why scalar simplicity really implies source nondegeneracy

The manuscript includes this argument in full. The cumulative pool Z_i is the sum of S_j for j≥i, C_j for j>i and phosphatase complexes Y_j for j≥i. Its derivative is the catalytic current c_i C_i−γ_iY_i. The coordinates (C,Y,Z) are an invertible linear coordinate system on the fixed-total subspace; elementary reaction directions also show that the source's stoichiometric rank is 3n.

Eliminate complex balances with pivots −(b_i+c_i) and −(β_i+γ_i), then the substrate recurrence with pivots −γ_iq_iF. The equilibrium manifold is smooth and three-dimensional, parameterized by (u,s,f). At fixed u, the enzyme-total derivative in (s,f) has determinant uf(B−uD)>0 on the constructed branch. The remaining total derivative is H′(u), whose exact nonzero expression is the displayed derivative formula labeled `eq:slope` in the LaTeX source. Thus the augmented equilibrium-and-total derivative is nonsingular. This proves nonsingularity on the actual stoichiometric subspace, rather than relying on a generic assertion about eliminants.

## Exact three-site benchmark and stability

The retained benchmark has roots x=(2,3,4,5,6), r=5 and totals (10,2,12). Its normalized B,D and six rates per site are in the manuscript and machine-readable exact data. Positivity at r=5 is directly checked rather than inferred from the conservative general sufficient bound, which allows the integer 6616 in this example. The improvement is a factor 1323.2 in kinase total compared with that sufficient integer choice, not a proof that r=5 is optimal.

The literal 12-species Jacobian is restricted to the nine-dimensional fixed-total chart (S1,S2,S3,C1,C2,C3,Y1,Y2,Y3). Exact rational Faddeev–LeVerrier characteristic coefficients and exact Routh first columns give:

| E/F | Routh first column | Right-half-plane roots | Classification within the class |
|---|---|---:|---|
| 3/8 | ten positive entries | 0 | Asymptotically stable |
| 1 | nine positive, then negative | 1 | Saddle |
| 15/8 | ten positive entries | 0 | Asymptotically stable |
| 3 | nine positive, then negative | 1 | Saddle |
| 35/8 | ten positive entries | 0 | Asymptotically stable |

No zero pivot or zero row occurs. The exact Routh certificate excludes imaginary-axis roots here. Decimal eigenvalues are used only for timescale diagnostics. Three-site tristability was known before this construction; it is not the novelty claim.

## Readouts, sequestration, and dimensional interpretation

For every constructed state, E=(x−1)/2, F=4/(x+1), and total free substrate equals E+F. Write m=n−1 and let d_m be D's leading coefficient. Then

    S_n = (d_m/2) [u^m/D(u)] (x−1),
    S_n+Y_n = (d_m/2) [u^m/D(u)] (x−1)(x+5)/(x+1).

For m≥1 the derivative of u^m/D is u^(m−1) sum_k (m−k)d_k u^k /D²≥0; for m=0 it is constant. The remaining x-factors are strictly increasing, with derivative 1+8/(x+1)² for the second. Both readouts strictly order all the constructed states. This proves mathematical separation, not a noise margin or reporter model.

| E/F | Free S3, approximately | S3+Y3, approximately | Kinase bound fraction | Phosphatase bound fraction |
|---|---:|---:|---:|---:|
| 3/8 | 0.022493 | 0.052483 | 0.95 | 1/3 |
| 1 | 0.119297 | 0.238594 | 0.90 | 1/2 |
| 15/8 | 0.309221 | 0.556598 | 0.85 | 3/5 |
| 3 | 0.591075 | 0.985125 | 0.80 | 2/3 |
| 35/8 | 0.951945 | 1.495914 | 0.75 | 5/7 |

Exact fractions are in `data/readouts.json`; `figures/readouts_resources.svg` is the corresponding vector figure. It stays outside the paper because it is not needed for the proof. A measurement after dissociation of enzyme complexes could target S_n+Y_n; a free-substrate reporter measures a different observable. No particular assay is validated here.

Generally the kinase and phosphatase bound fractions are 1−(x−1)/(4r) and 1−2/(x+1). Total enzyme divided by total substrate is exactly one, with kinase fraction r/(r+1) and phosphatase fraction 1/(r+1). These are strongly enzyme-loaded examples. Changing concentration units does not change these ratios, and a substrate-excess approximation does not describe them.

Using C0=0.1 μM and T0=10 seconds gives kinase 1 μM, phosphatase 0.2 μM and substrate 1.2 μM. Unimolecular constants are divided by T0; association constants by C0*T0. The association rates range from about 0.0941 to 2 μM⁻¹s⁻¹; kinase catalytic rates from 0.00130 to 0.0624 s⁻¹ and phosphatase catalytic rates equal 0.1 s⁻¹. Stable total fully phosphorylated outputs are approximately 5.25, 55.66 and 149.59 nM.

The baseline stable leading real parts are approximately −0.0005772876, −0.0000454538 and −0.0001934242 in dimensionless time. With T0=10 seconds their local linear e-folding times are approximately 4.81 hours, 2.55 days and 14.36 hours. These are floating spectral diagnostics, not certified settling times or basin estimates. The example is an uncalibrated cell-free mathematical design benchmark, with substantial loading and slow recovery; it is not an experimentally fitted protein system.

## Bounded follow-up experiments and what they taught us

### A sharper r condition

Hypothesis: r>max_j u_j alone might imply converted coefficient positivity. We tested the arithmetic-root family at r=max_j u_j+1/1000 for n=1,…,8,10,12. All ten exact coefficient tests passed (`data/sharper_r_pilot.json`). This small pilot was intentionally not scaled to a census.

The quotient recurrence exposes the obstacle to a direct coefficientwise induction: q_i=N_r d_i+(q_(i−1)−J_r a_(i−1))/r has signed corrections. This is an actual negative correction, not just a loose estimate: for n=2 and x=(2,3,4), N=27+8u and J=3+32u, so N_r d_0−J_r a_0=−840r. The final q_1=24+256r remains positive, but positivity cannot be inferred by discarding a putatively nonnegative correction. The existing large-r bound controls these corrections uniformly and already closes the all-n root. No general near-largest-root positivity theorem was established, and no counterexample to that stronger claim was found. Its status remains unproved; the paper retains the proven bound.

### Equilibrium-preserving kinetic tuning

With fixed A,B,D, hold p_i=B_(i−1)/t_(i−1) and q_i=D_(i−1)/t_i and choose λ_i,b_i,β_i>0. Set γ_i=λ_i, c_i=λ_iD_(i−1)/B_(i−1), a_i=(b_i+c_i)p_i and α_i=(β_i+γ_i)q_i. The equilibrium set and totals remain unchanged while kinetics can change.

We tested each of nine such coordinates separately at factors 1/2 and 2: 18 candidates, one short process, no global rate multiplier. Screening required association constants at most 2, unimolecular constants at most 2, and preservation of all three stable equilibria by floating spectral diagnostics. The best accepted change doubles the third-site kinase dissociation rate. Its association maximum is 2 and unimolecular maximum about 1.24879. Exact Routh recomputation confirms the same stable/saddle pattern. The slowest decay improves only by a factor 1.002247, approximately 0.225%. This does not justify replacing the simple baseline or claiming meaningful chemical acceleration. All trials, exact winning rates, characteristic coefficients and Routh columns are saved in `data/kinetic_tuning.json`. The test does not establish an optimum over the continuous tuning family.

### A certified independent-total tolerance box

With all original rate constants fixed at the baseline and FT=2, exact rational interval arithmetic certifies five positive equilibria throughout

    ET in [10−2*10^−8, 10+2*10^−8],
    ST in [12−10^−8, 12+10^−8],

with ET and ST varying independently. This is not a reconstructed curve that keeps the old states fixed. For every parameter choice, one equilibrium lies in each ratio interval u_j±1/1000.

The method clears the regular-chart substrate residual with its positive denominator:

    P(u;r,T)=(r−u)A M+2(r−u)u L(B+D)−T u L M,
    L=B−rD, M=B−uD, r=ET/2.

Rational intervals prove r−u>0 and L>0 over each bracket, hence M>0, and give strictly opposite endpoint signs for P uniformly over the parameter box. The intermediate-value theorem supplies a positive source state in each bracket; disjointness and the universal bound give exactly five. All endpoint enclosures are saved in `data/tolerance_box.json`.

The first attempted half-width 10^−6 in (r,ST) failed this sufficient interval test; 10^−8 passed. Failure of the larger enclosure is not evidence that equilibria disappear there. The returned box is small and certifies equilibrium count only. Stability and derivative-sign enclosures were not certified on this box. Qualitative full-parameter nondegeneracy and openness are proved separately in the manuscript.

## AGC and execution ledger

The postproof entry checkpoint was used, and AGC was consulted after the new algebra/nondegeneracy structure and before handoff. It detected the new receipt-reuse artifact outside its consumption closure. The named self-service `authority reconcile-frontier` command bound that input without changing the theorem graph; the next checkpoint returned CURRENT. AGC was useful for input freshness and scope discipline, not for finding this proof. Its inherited minimal cut still contains historical red entries because proof-neutral checkpoint/reconciliation does not publish theorem-status evidence. It also initially quoted the stale structural-review sentence that formal obligations remained; that prose has been corrected. The source-bound strict receipts, not a diagnostic ledger or an AGC freshness label, are the formal evidence.

The original five proof files were preserved. Only the new algebra module was compiled. Independent replay took about two seconds; bounded tuning/coefficient/interval work about one second. Numerical native thread counts were limited to one. All longer-expected numerical jobs used the repository process guard. No dependency update, bulk certificate campaign, generated-evidence commit, or external publication was performed.

The daily ledger in `../campaign/daily/2026-09-19.md` and `tasks.json` provide the item-level handoff. The manuscript intentionally omits the tuning, sharper-r conjecture, readout/resource discussion, and discovery history. Those are documented here to finish the guide without inflating the final critical proof path.

## Deliverables and residual scope

- Workspace root: `Phosphorylation_Sharpness_Paper.pdf`.
- Editable source: `paper.tex`; vector equilibrium figure: `figures/equilibrium.pdf`.
- Exact data and receipts: `data/`; exact checker and bounded follow-up scripts beside this report.
- Reproduction instructions and precise evidence map: `README.md`.
- Rendered pages and QA record: `qa/`; build and AGC logs: `logs/`.

There is no unresolved implication in the ordinary all-n sharpness proof or the original compiled attainment scope. The full prescribed-ratio endpoint, source nondegeneracy and openness are not additional Lean endpoints; their completed ordinary proofs are explicitly distinguished. A sharper general r threshold, general stability classification, sizable stability-certified tolerances, and experimental calibration remain outside the completed proof/publication scope.

