# Publication handoff — 10 September 2026

The publication guide's ten items are complete. The existing 33/33 baseline is preserved. The final paper is `Random_Autocatalysis_Production_and_Rarity.pdf` in this workspace root; editable source, bibliography, scripts, figure data and build instructions are under `paper/`. The PDF has 18 pages, all rendered and visually inspected.

## What was proved for publication

The strongest new event requires only total mass at most 11 through time 100 and normalized nonfood export greater than 0.1 on (1,100]. It imposes no prescribed RAF, product-residence floor or reaction-label condition. For the exact source and physical model, its source/mark/trajectory probability obeys

`q0^6 p (1 - 24 exp(-cV/n)) <= P(output) <= C_k p + 4 exp(-cV/n)`.

The same finite sandwich holds for output intersected with existence of some RAF. The disabled reactor uses exactly the same physical output observable and has probability at most `2 exp(-cV/n)`. At the declared sufficient quadratic volume scale, the enabled probabilities are Theta(p), and the disabled/enabled ratio tends to zero. The event construction, finite physical-law bounds, averaging, asymptotic bounds and ratio are strictly compiled.

The source asymptotics identify `p ~ 9/(pi^2 X_n)`, equivalently order `n/R_n`. The exact-source structural theorem bounds the probability of some RAF away from zero. Dividing the compiled output-and-RAF probability by this denominator gives a compiled Theta(p) conditional output probability. Thus structural abundance and rarity of the specified productive event coexist in the same sampler; the argument never substitutes a different power-law convention or independent-edge source.

The finite reliability implication is stated independently of a joint volume sequence: for `0 < eta < 1`, sufficient volume is the maximum of `2n/d` and `(n/c) log(24/eta)`. Its exponential inequality is compiled and composed in the paper with the already compiled finite conditional success theorem. The huge constants are sufficient proof bounds, not fitted or necessary physical thresholds.

The RAF-attributed baseline remains a distinct result. Its volume-dependent lower paid-path cost and upper catalog factor give the logarithmic rate at `V=40+floor(sqrt(n))`; they do not justify a uniform Theta claim. The paper defines its separate attribution, stock, residence, signed-current and basal-budget requirements explicitly.

## Conventional proofs and exact evidence boundary

The deterministic sustained-mean proposition is proved fully in Section 7. Positive basal forcing starts the selected product, bounded mass gives global ODE existence, and the corrected logarithm with food deficits yields positive long-time mean catalytic input. The finite-window initial stock term is retained. No unique-attractor or convergence assertion is needed.

The fixed finite-copy process is irreducible using outflow, finite food arrivals and positive basal ligations. The construction checks repeated-reactant multiplicities. Nonexplosion, finite mass sublevels and generator identity `G L = 10-L` permit the continuous-time Foster–Lyapunov criterion stated by Anderson and Kim, Theorem 3.1. This gives positive recurrence, a unique stationary law, and infinitely many returns to zero. Therefore everlasting residence above a positive product floor fails at every fixed finite volume. Zero is not absorbing because food continues to enter.

These two general ODE/recurrence consequences are conventional proofs, not Lean exports. Independent complete-trial sampling costs and catalog-size interpretations are also explicitly identified as conventional elementary consequences. The paper does not claim to solve a general persistence or positive-recurrence conjecture, determine a transition location, or obtain an exact probability prefactor.

## What the experiments taught us

The numerical preflight checked exact rational margins before the new formal work: basal positive input at most 0.0103872 and positive catalytic input at most 0.05 cannot explain output exceeding 0.1 outside the short-incidence/noise events. This directly motivated and validated the label-free upper proof. The deterministic mean-production coefficient is also strictly larger than the positive basal budget.

The finite-host illustration retains the complete n=4 basal catalog and only a specified set of catalytic assignments. It is a chosen environment in the constructive class, not an empirical sample of environmental rarity. A first tolerance comparison caught insufficient absolute accuracy around basal startup. Fixing absolute tolerance at 1e-18 and comparing relative tolerances 1e-10 and 2e-12 yielded maximum saved-array discrepancy below 1.6e-8 and mass error below 7.2e-15. Enabled and disabled export on the matching window are approximately 162.6930 and 0.0000414748. Large accumulated export is consistent with finite instantaneous mass because feed continues.

The source-scaling figure evaluates the exact capped expectation, including the cap atom, through 100-digit Hurwitz-zeta arithmetic. It does not enumerate huge catalogs. The reliability figure plots the theorem bound, not simulated establishment frequencies. All parameters, assignments, arrays and scripts are retained. The complete figure calculation ran under a 60-second process lease and finished in about 7.6 seconds.

## Verification and delivery checks

Six new Lean files compiled strictly, with warnings treated as errors. The publication entry point is `proofs/RandomViability/PublicationStructure.lean`; it imports the completed corollaries and baseline. The final strict run took 54.953 seconds. The foundational axiom audit lists only Classical.choice, Quot.sound and propext. The final diagnostic independently checked the baseline and six new receipts against current proof files and 566 distinct imported local source hashes. All matched. The exact theorem-to-code map appears in Appendix D and the reproduction README.

The manuscript build used existing pdflatex and BibTeX because latexmk's Perl engine was missing. No installation, dependency update, toolchain change or verification-bridge change was performed. The final LaTeX log is clean of unresolved references, citations and overfull boxes. Every final page was rendered; the proof tables, displayed inequalities, three vector figures and bibliography were inspected. The PDF was copied to the workspace root only after these checks.

AGC was used at entry, after structure, after failures and before handoff. Its requests for same-cut freshness reconciliation were followed. The final checkpoint is CURRENT. It was useful for identifying freshness and keeping stale route previews separate from compiled evidence; it did not prove any mathematical statement. Protected canonical graph integration remains outside this paper-delivery task. Nothing was staged or committed.

The running ledger records all publication attempts, diagnostics and repairs in dated Sprints 76–80. Discovery history remains outside the paper. The existing `FINAL_EMERGENCE_REPORT.md` continues to document the original proof campaign; this handoff records the completed publication extension.

Final accounting: **publication 10/10 PASS; baseline 33/33 preserved; no unresolved publication proof or artifact item.**
