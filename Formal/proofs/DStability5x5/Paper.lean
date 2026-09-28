import proofs.DStability5x5.Boundary
import proofs.DStability5x5.KappaStar
import proofs.DStability5x5.AlDoura

/-!
# Paper root: "Critical points on Johnson's contact variety decide D-stability"

This module imports the complete development of the paper.  The statements of the paper and their Lean
declarations (namespace `DStability5x5`):

* Lemma 2.2 (principal-minor expansion): `contactDet_expansion`, `pminor_eq_minorR`.
* Lemma 2.3 (Johnson's criterion): `dStable_iff_no_contact`.
* Theorem 3.2 (coverage, any proper exhaustion): `dStable_iff_morseFor`, `dStable_iff_morse_logBarrier`.
* Theorem 3.4 (explicit criterion): `dStable_iff_explicit`.
* Corollary 3.5 (Lagrange and tangency branches): `dStable_iff_lagrange_tangency`.
* Theorem 3.6 (the 5 × 5 criterion): `dStable_iff_five`.
* Lemma 4.2 (singular contacts ⇔ tangency system): `not_surjective_iff_tangency`, `regular_iff_rank`.
* Theorem 4.3 (regular contacts persist): `exists_contact_near_of_regular`, `not_dStable_near_of_regular`.
* Corollary 4.4: `not_regular_of_mem_closure`, `isOpen_hurwitz_regularContact`.
* Theorem 4.5 (boundary dichotomy): `closure_dichotomy`.
* Theorem 6.2 (bounded time-scale stability): `kStable_iff_no_cone_contact`,
  `kStable_iff_no_boxFaceCritical`, `dStable_iff_forall_kStable`, `kStable_mono`.
* Proposition 6.3(a) (κ* is attained): `exists_least_unstable_ratio`.
* Theorem 6.4 (separation protection): `eventually_kStable_of_no_contact`,
  `contact_of_tendsto_not_kStable`.
* Section 7 (diagonal Lyapunov certificates imply D-stability; the refinery column of Section 7.2):
  `dStable_of_diagLyapunov`, `alDoura_dStable`.
-/
