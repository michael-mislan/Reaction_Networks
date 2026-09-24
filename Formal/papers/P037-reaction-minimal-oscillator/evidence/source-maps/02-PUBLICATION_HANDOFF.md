# Research paper handoff — 9 September 2026

The paper is saved as `Oscillatory_Cores_Research_Paper.pdf` in this workspace root.
Its editable source is `paper/main.tex`; reproduction commands are in `paper/README.md`.
It contains the final mathematical path, not the discovery ledger or abandoned routes.
The complete historical experiments remain in the existing daily ledger and original
HANDOFF_REPORT.md. Follow-up score: **17/18**, with the LaTeX-build requirement blocked.

## Mathematical outcome

The original axiom-clean Lean theorem is unchanged. It proves actual all-time positive
nonconstant periodic dynamics, exclusion of every D-unstable supported child, and
universal proper-deletion periodic minimality at arbitrary nonnegative retained rates.

The paper proves the requested immediate consequences: all positive rate choices have
one positive equilibrium, its Jacobian determinant is 216000 k5^4/product(x*), every
active deletion has a strictly increasing linear observable, and periodic average fluxes
equal equilibrium fluxes. A nonconstant orbit has strictly smaller mean fourth-species
concentration. The recurrence and boundary conclusions are explicitly conditional on
positive/global/bounded trajectories where appropriate.

The stronger conventional result also closed. The original rational interval expression
is the first Lyapunov coefficient under the paper's unchanged-time derivative-jet
convention. Its unit-eigenvector normalization lies strictly between -0.023 and -0.022.
Positive crossing speed and a stable complementary pair imply a supercritical attracting
hyperbolic periodic branch. A transverse return-map implicit-function argument gives an
open neighborhood in the full five-dimensional positive rate space. One monodromy
multiplier is neutral (phase); the other three contract. These are conventional
computer-assisted results, not newly Lean-compiled stability claims.

## What was tested and learned

1. **Source geometry, exact fractions.** The circuit is (2,3,2,2,2), det S0=48,
   det Y0=3000. All 20 deletion dual identities passed. The 24 nonempty supported
   children are covered by six explicit selections. Five have rational diagonal
   energy certificates; the sixth has an elementary scaled spectral factorization.
   This explains deletion minimality as loss of positive balanced operation.
2. **Coefficient normalization and exact inclusion.** The script uses derivatives
   with falling factorials, not Taylor coefficients with missing factorials. The
   left row is conjugate to the adjoint eigenvector. Its nonzero pairing is normalized
   exactly. Positive rescaling of q changes the coefficient by the square of that
   scale. All 14 elimination pivots exclude zero. Rational sign bisection encloses
   the unique exact crossing, and squared endpoint inequalities enclose its exact
   frequency. Invertibility of the leading block plus the zero full determinant
   supplies both omitted eigenvector equations by the Schur complement. This closes
   the earlier exact-object binding gap without a larger search.
3. **Small numerical branch, explicitly nonvalidated.** Existing implicit midpoint
   shooting was reused at amplitude 0.02 and 128/256/512 steps. Parameter values are
   0.956506609271, 0.956506654719, 0.956506666084; periods are 62.2226143528,
   62.2132421634, 62.2108996453. The refinement is consistent with second order.
   At 512 steps midpoint-quadrature flux ratios differ from one by at most
   1.4e-15. This checks the implementation, not an exact continuous-time decimal
   orbit or its multipliers. The calculations completed inside 60-second leases.
4. **New Lean exports.** PublicationConsequences.lean compiles the literal deletion
   observable derivative and exact period-integrated flux vector. LocalBranchCorollaries.lean
   exports the whole eventual returning family, preserving uniform localization,
   positivity, parameter/period continuity and nonzero displacement velocity.
   Both receipts have zero exit status, no warnings/output, and only standard axioms.
   The branch receipt took 45.972 seconds. The first adapter attempt failed only because
   the rational-valued weight definition needed `noncomputable`; this was corrected
   in place before the clean verification.
5. **Publication rendering.** The installed pdfLaTeX and LuaLaTeX executables were
   inaccessible. WSL also refused execution, and direct network socket policy blocked
   obtaining a separate portable engine. No permissions were changed or bypassed.
   A local ReportLab/math-font renderer produced the paper from the same editable
   manuscript, with vector display mathematics and vector figures. Inline mathematics
   is rendered at 230 dpi. All pages were rendered and inspected; concrete numbering,
   case-formula and heading-placement issues were fixed.

## Exact formal boundary

Compiled: original Resolution theorem and its 94-source closure; new
`periodic_integrated_flux`, `deletion_observable_hasDerivAt`, and `local_return_family`.

Conventional: full positive-root equilibrium existence/uniqueness, explicit Jacobian
determinant, recurrence and bounded-trajectory corollaries, strict mean inequality,
the complete physical branch limit statement with spectral base identification,
the interval inclusion justification, Hopf stability application and open-rate persistence.
The local-family Lean export retains its base parameter and period but does not
identify them with the displayed spectral constants in its public interface.

Outstanding: **a permitted LaTeX compilation and inspection of main.tex**. The supplied
PDF exists and is usable, but this specific requested build is not claimed complete.
The README provides the exact commands. Further Lean formalization of the conventional
corollaries is separately visible and is not falsely credited to the accepted root.

## AGC and scope

AGC was invoked at entry, post-structure, after failures, on the branch export and at
handoff. New strict receipts triggered same-cut reconciliation, which was serviced
without theorem-graph changes. AGC was useful for input freshness; its unbound authored
route still suggested already completed moving-mode work and supplied no new mathematical
step. The known absent publication frontier was not manufactured or repaired. Nothing
was staged, committed, submitted to a journal or uploaded externally.
