# Publication handoff

## Result and scope

The completed paper is **Shared NADPH Regeneration Sets Sharp Limits on Joint
Glutathione and Thioredoxin Service**, saved as
`Shared_NADPH_Regeneration_Research_Paper.pdf` in this workspace root. The editable
source and figures are in `publication/`. It includes the critical source
reduction, exact theorem, constructive reconstruction, isolated comparison,
kinetic penalty, optimal enzyme redesign, operating margins, and explicitly
qualified full-state dynamics. Discovery fixtures and abandoned models are
excluded. Historical guide score: **39/48**; the distinct postproof register
records the requested 18 follow-ups and their evidence levels.

The claim is kinetic and regeneration-capacity compatibility in a maintained
subnetwork of Adimora et al. (2010). It is not a named literature conjecture,
a thermodynamic impossibility theorem, empirical whole-cell validation, a
clinical intervention, or a global stability theorem. The parent paper already
introduced coupled glutathione/thioredoxin kinetics. Our contribution is the
exact decision theorem and reconstruction for the declared subsystem, including
its intervention consequences.

## Follow-up results

1. **Isolated comparison, now formal.** `Postproof.isolated_successes` constructs
   actual literal steady states for both physically isolated branches at scale
   0.1, meeting quotas 10 and 4. It uses the one-branch endpoint criterion and
   exact threshold equality. This closes the former numerical-only gap in the
   headline comparison. Removing a quota still does not remove a branch.
2. **Kinetic penalty, now formal.** The exact difference between fixed-kinetics
   and quota-only scales is total overdelivery divided by unit-scale supply.
   Its sign and equality conditions compile. In the nominal example the extra
   GPx demand is 0.348943552 uM/s; the true capacity is 2.49245% above the relaxed
   estimate, or 2.76531 percentage points more repair from the original scale.
3. **Enzyme redesign, now formal.** `Allocation.allocation_attained` reconstructs
   the literal state at a positive algebraic glutathione root. All carrier
   totals remain fixed. The designed GPx amount is approximately 48.313663962
   uM instead of 50, with g approximately 361.350553587 uM. The scale is exactly
   14/R1(XT), numerically 0.110947356002. `allocation_lower_bound` proves the
   matching universal lower bound, even over all admitted glutathione branches
   coupled to the unchanged Trx branch. Its specialization is the requested
   enzyme-only optimum. `original_source_insufficient_for_redesign` proves
   that scale 0.1 cannot be rescued in this design class.
4. **Repair ceiling and asymptotics.** The manuscript proves conventionally
   that finite repair exists exactly below both j_i(N) ceilings, and that
   s_min(L) is asymptotic to J(N)(D-N)/(V(N-L)). Ceiling obstruction itself is
   also formalized. Nominal ceilings are 10.351641535 and 5.143546798 uM/s.
5. **Binding quota.** The formal max-floor identity and the original threshold
   theorem show that relaxing a nonbinding quota leaves capacity unchanged.
   The quota plot shows the plateau and the eventual switch of binding branch.
6. **Tolerance.** `Postproof.robust_command` proves the exact multiplicative
   tolerance criterion. A declared 5% tolerance gives command 0.119697545002,
   a 19.697545% increase over the original command. This is not empirical
   uncertainty. A separate exact-fraction interval calculation bounds a design
   box of +/-1% enzyme amounts and +/-5% reductase constants, obtaining a
   sufficient scale 0.125895728694 at target x=1.5. It bounds dependent
   expressions conservatively; it does not assume corner extremality.

## Full ODE investigation and limitations

The calculator reconstructs the eight-dimensional ODE after eliminating only
conserved totals. It does not substitute steady-state responses during a
transient. The manuscript provides a conventional inward-face proof for its
nonnegative conserved domain, with oxidized carriers at or above their
baseline offsets and 0<=x<=N. Thus the baseline-subtracted laws never create
negative reaction currents on the admitted domain.

Three equilibria and six perturbations were checked with SciPy. The largest
Jacobian real parts at scales 0.1, s_min and 0.12 are -0.002999934,
-0.003001207 and -0.003004280 /s. Full equilibrium residuals are below 1e-12.
Separate perturbations increase carrier oxidation or redistribute enzyme
states. At scale 0.12 all sampled services pass throughout; at the exact
boundary transient Trx violations occur. Apparent late crossings at zero
limiting margin are not certified service times. These are numerical results,
not formal local or global stability evidence.

A bounded Lyapunov pilot solved the continuous equation at scale 0.12 and
rounded its candidate matrix to eight decimals. Numerical minimum eigenvalues
were 0.000137116 for P and 0.999978825 for -(A^T P+P A). This is a successful
candidate search, not a completed certificate: an interval Jacobian at the
algebraic equilibrium and a nonlinear remainder bound remain unproved. The
pilot is preserved in the JSON and this handoff, but excluded from the paper's
critical proof path. The dynamics investigation deliverable is complete with
this accurately limited outcome; no attraction neighbourhood is claimed.

## Interpretation and literature accounting

Both branch quotas are deliberate independent assay specifications. The Trx
quota also means a reduced-carrier floor 5000/23009 uM, about 43.03% of total
Trx, but is not a measured health threshold. Joint branch failure does not
mean lower aggregate antioxidant activity: original joint NADPH turnover
12.784739 uM/s exceeds GPx-only turnover 10.351411 uM/s.

Peroxide removal equals jG+jT+(bT/dT)jT at steady state. The final term is
additional hyperoxidation turnover, accompanied by external maintenance.
At the boundary its current is 0.000192 uM/s. Sulfiredoxin's ATP and reductant
requirements, authenticated against the primary mechanistic source, are not
resolved in the adopted first-order law. The source and peroxide feed are
maintained, and omitted protein-thiol/catalase/transport pathways remain absent.
Direction consistency was checked; a complete thermodynamic realization was
not inferred from irreversible phenomenological kinetics.

Primary references for Adimora, Pannala--Dash, Henry et al., Noor et al. and
Joensson et al. were checked. The comparison distinguishes same-model numerical
solution, quota-only relaxation, thermodynamic flux analysis and enzyme-cost
minimization. No broad novelty claim about coupled redox modelling is made.
The Pannala printed-equation discrepancy remains unresolved in the historical
source diagnostics and is not an input to this paper. Empirical calibration
and whole-cell time-course reproduction remain open, without obstructing this
clearly scoped maintained-model paper.

## Verification and reproducibility

- Original root: `proofs/CommonEnvironmentProtection/Main.lean`, unchanged.
- New formal files: `Postproof.lean` and `Allocation.lean` in the same directory.
- Strict receipts: `verification/Main.json` and `verification/Allocation.json`.
- Final calculator: `experiments/publication_calculations.py`.
- Results: `certificates/publication_calculations.json`.
- Figures and transient sample arrays: `publication/`.
- Rebuild entry point: `publication/reproduce.ps1`; `-VerifyLean` additionally
  invokes the strict repository verifier without modifying dependencies.
- Final evidence and visual audit: `verification/publication_audit.json`.

All new formal targets compile warning-free. The authenticated declarations
use only Classical.choice, Quot.sound and propext. AGC checkpoints were useful
for distinguishing current proof evidence from canonical publication routing;
they supplied no new mathematical insight. Canonical graph integration remains
assigned to the authority integrator. No protected authority graph, dependency,
or generated-evidence commit was changed to manufacture a completion status.

Final AGC diagnostic: the publication checkpoint reported CURRENT with
current_with_unbound_authored_route and asked the proof agent to evaluate the
authored route. Its exact suggested Foundry packet command was run; it returned
FOUNDRY_TOTAL_ARTIFACT_BUDGET_EXHAUSTED. This is a diagnostic artifact budget, not
a failed theorem or Lean verification. The proposed enzyme route has already
been proved in Allocation.lean and authenticated in Allocation.json. No new
Foundry packet or canonical publication is claimed. This gate was useful for
exposing routing lag, but supplied no mathematical help for the completed proof.
