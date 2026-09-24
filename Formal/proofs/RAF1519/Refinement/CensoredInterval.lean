import proofs.RAF1519.Refinement.CensoredMaximal
import proofs.RandomViability.CoordinateIntervalControl

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators ENNReal
variable {α β : Type*} [Fintype β]

def coordinatePrefix (rate inc : α → β → ℝ) (good : Set α) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (z : ℕ → JumpState α β) (K : ℕ) : ℝ :=
  ∑ i : Fin K,coordinateCompensation rate inc good T stop
    i (Preorder.frestrictLe (i:ℕ) z) (z ((i:ℕ)+1))

def coordinateWithin (rate inc : α → β → ℝ) (good : Set α) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (z : ℕ → JumpState α β) (k : ℕ) (s : ℝ) : ℝ :=
  if coordinateStop good T stop k (Preorder.frestrictLe k z) then
    coordinatePrefix rate inc good T stop z k else
    coordinatePrefix rate inc good T stop z k-(∑ a,rate (z k).1 a*inc (z k).1 a)*s

theorem coordinate_prefix_neg (rate inc : α → β → ℝ) (good : Set α) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (z : ℕ → JumpState α β) (K : ℕ) :
    coordinatePrefix rate (fun x a => -inc x a) good T stop z K =
      -coordinatePrefix rate inc good T stop z K := by
  unfold coordinatePrefix
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold coordinateCompensation
  dsimp only
  by_cases hp : coordinateStop good T stop i (Preorder.frestrictLe (i:ℕ) z)
  · simp only [if_pos hp,neg_zero]
  · simp only [if_neg hp,mul_neg,Finset.sum_neg_distrib]
    by_cases ht : (z ((i:ℕ)+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe (i:ℕ) z)
    · simp only [if_pos ht]
      cases (z ((i:ℕ)+1)).2.1 <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> ring
    · simp only [if_neg ht]
      ring

theorem coordinate_interval_envelope (rate inc : α → β → ℝ) (good : Set α) (T B : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (hB : 0 ≤ B) (hinc : ∀ x a, |inc x a| ≤ B)
    (z : ℕ → JumpState α β) (k : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hsh : s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) :
    |coordinateWithin rate inc good T stop z k s| ≤
      max |coordinatePrefix rate inc good T stop z k|
        |coordinatePrefix rate inc good T stop z (k+1)|+B := by
  by_cases hp : coordinateStop good T stop k (Preorder.frestrictLe k z)
  · rw [coordinateWithin,if_pos hp]
    exact (le_max_left _ _).trans (le_add_of_nonneg_right hB)
  · let d : ℝ := if (z (k+1)).2.2 ≤ T-prefixElapsed k (Preorder.frestrictLe k z) then
      (z (k+1)).2.1.elim (fun _ => 0) (inc (z k).1) else 0
    have hd : |d| ≤ B := by
      dsimp [d]
      split_ifs
      · cases (z (k+1)).2.1 with
        | inl u => simpa only [Sum.elim_inl,abs_zero] using hB
        | inr a => exact hinc _ a
      · simpa only [abs_zero] using hB
    have hstep : coordinatePrefix rate inc good T stop z (k+1) =
        coordinatePrefix rate inc good T stop z k+d-
        (∑ a,rate (z k).1 a*inc (z k).1 a)*
          min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) := by
      have hsucc : coordinatePrefix rate inc good T stop z (k+1) =
          coordinatePrefix rate inc good T stop z k+
            coordinateCompensation rate inc good T stop k (Preorder.frestrictLe k z) (z (k+1)) := by
        unfold coordinatePrefix
        rw [Fin.sum_univ_castSucc]
        rfl
      rw [hsucc]
      unfold coordinateCompensation
      dsimp only
      rw [if_neg hp]
      dsimp [d]
      ring
    have hh := affine_jump_interval_abs_envelope
      (coordinatePrefix rate inc good T stop z k)
      (∑ a,rate (z k).1 a*inc (z k).1 a) d
      (min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) s B hs hsh hB hd
    rw [← hstep] at hh
    simpa only [coordinateWithin,if_neg hp] using hh

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

theorem coordinate_two_sided_tail (initial : α) (next : α → β → α) (rate inc : α → β → ℝ)
    (hr : ∀ x a,0 ≤ rate x a) (ht : ∀ x,0 < ∑ a,rate x a)
    (good : Set α) (θ v T : ℝ) (hθ : 0 ≤ θ) (hv : 0 ≤ v) (hT : 0 ≤ T)
    (hsmall : ∀ x ∈ good, ∀ a, |θ*inc x a| ≤ 1)
    (hvar : ∀ x ∈ good, (∑ a,rate x a*(inc x a)^2) ≤ v)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (δ : ℝ) :
    jumpTrajectoryLaw initial next rate hr ht
      {z | ∃ K,δ ≤ |coordinatePrefix rate inc good T stop z K|} ≤
      2*ENNReal.ofReal (Real.exp (-θ*δ+θ^2*v*T)) := by
  let μ := jumpTrajectoryLaw initial next rate hr ht
  let E := fun d : α → β → ℝ => ⋃ K,{z | coordinateFluctuationBy rate d good T stop δ K z}
  let B := ENNReal.ofReal (Real.exp (-θ*δ+θ^2*v*T))
  have hp : μ (E inc) ≤ B := coordinate_any_index_tail initial next rate inc hr ht good
    θ v T hθ hv hT hsmall hvar stop hstop δ
  have hn : μ (E (fun x a => -inc x a)) ≤ B :=
    coordinate_any_index_tail initial next rate (fun x a => -inc x a) hr ht good
      θ v T hθ hv hT (by simpa only [mul_neg,abs_neg] using hsmall)
      (by simpa only [neg_sq] using hvar) stop hstop δ
  have hsub : {z | ∃ K,δ ≤ |coordinatePrefix rate inc good T stop z K|} ⊆
      E inc ∪ E (fun x a => -inc x a) := by
    intro z hz
    obtain ⟨K,hK⟩ := hz
    rcases le_abs.mp hK with hp|hn
    · exact Or.inl (Set.mem_iUnion.mpr ⟨K,K,le_rfl,hp⟩)
    · apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨K,K,le_rfl,?_⟩
      change δ ≤ coordinatePrefix rate (fun x a => -inc x a) good T stop z K
      rwa [coordinate_prefix_neg]
  calc
    _ ≤ μ (E inc ∪ E (fun x a => -inc x a)) := measure_mono hsub
    _ ≤ μ (E inc)+μ (E (fun x a => -inc x a)) := measure_union_le _ _
    _ ≤ B+B := add_le_add hp hn
    _ = _ := (two_mul B).symm

theorem coordinate_interval_tail (initial : α) (next : α → β → α) (rate inc : α → β → ℝ)
    (hr : ∀ x a,0 ≤ rate x a) (ht : ∀ x,0 < ∑ a,rate x a)
    (good : Set α) (θ v T B : ℝ) (hθ : 0 ≤ θ) (hv : 0 ≤ v) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hinc : ∀ x a, |inc x a| ≤ B)
    (hsmall : ∀ x ∈ good, ∀ a, |θ*inc x a| ≤ 1)
    (hvar : ∀ x ∈ good, (∑ a,rate x a*(inc x a)^2) ≤ v)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (δ : ℝ) :
    jumpTrajectoryLaw initial next rate hr ht
      {z | ∃ k s,0 ≤ s ∧ s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) ∧
        δ+B ≤ |coordinateWithin rate inc good T stop z k s|} ≤
      2*ENNReal.ofReal (Real.exp (-θ*δ+θ^2*v*T)) := by
  apply le_trans (measure_mono ?_)
    (coordinate_two_sided_tail initial next rate inc hr ht good θ v T hθ hv hT hsmall hvar stop hstop δ)
  intro z hz
  obtain ⟨k,s,hs,hsh,hcross⟩ := hz
  have hb := coordinate_interval_envelope rate inc good T B stop hB hinc z k s hs hsh
  have hm : δ ≤ max |coordinatePrefix rate inc good T stop z k|
      |coordinatePrefix rate inc good T stop z (k+1)| := by linarith
  rcases le_max_iff.mp hm with hl|hr
  · exact ⟨k,hl⟩
  · exact ⟨k+1,hr⟩

end
end RAF1519.Refinement
