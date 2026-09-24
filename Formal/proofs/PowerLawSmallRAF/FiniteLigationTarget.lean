import proofs.PowerLawSmallRAF.LigationStaticTargetProbability
import proofs.PowerLawSmallRAF.LigationSubstringSchedule

namespace PowerLawSmallRAF

set_option maxHeartbeats 100000

attribute [local irreducible] ligationSubstringSchedule

def ligationTargetNucleus (L : Nat) (w : LigationWord) : Finset LigationWord :=
  (ligationSubstrings w).filter fun u => u.length ≤ L

noncomputable def ligationTargetFailureProbability (p : ℝ) (L : Nat) (w : LigationWord) : ℝ :=
  ∑ cfg : LigationRawConfiguration (ligationSubstringSchedule w),
    if w ∉ ligationRawKnown (ligationSubstringSchedule w) cfg (ligationTargetNucleus L w)
    then ligationRawWeight p (ligationSubstringSchedule w) cfg else 0

/-- Uniform in every target word, including words with repeated substrings:
one independent full row is used for each distinct nonempty substring. -/
theorem finite_ligation_target_failure_bound {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (L : Nat) (w : LigationWord) (hL : 4 ≤ L) (hLw : L ≤ w.length)
    (hlarge : 32 * Real.log 2 ≤ p * (L : ℝ)) :
    ligationTargetFailureProbability p L w ≤
      Real.exp (-p * (w.length : ℝ) / 2) +
        2 * (w.length : ℝ)^2 * Real.exp (-p * (L : ℝ)^2 / 32) := by
  have hw : w ∈ ligationSubstrings w := by
    apply (mem_ligationSubstrings_iff w w).mpr
    refine ⟨List.infix_refl w, ?_⟩
    intro heq
    simp only [heq, List.length_nil] at hLw
    omega
  have hfood : ∀ u ∈ ligationSubstrings w, u.length ≤ L → u ∈ ligationTargetNucleus L w := by
    intro u hu hlen
    exact Finset.mem_filter.mpr ⟨hu, hlen⟩
  have hcover : ligationSubstrings w ⊆ (ligationSubstringSchedule w).toFinset := by
    rw [ligationSubstringSchedule_toFinset]
  have h := ligationTarget_static_mass_le hp hp1 (ligationSubstringSchedule w)
    (ligationSubstringSchedule_nodup w) (ligationSubstringSchedule_order w)
    (ligationSubstrings w) (ligationTargetNucleus L w) L hL hlarge
    (ligationSubstrings_cut_closed w) hfood hcover w hw hLw
  apply h.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact_mod_cast ligationSubstrings_card_le w

end PowerLawSmallRAF
