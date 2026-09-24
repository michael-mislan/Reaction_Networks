import proofs.FiniteCopy.MarkedTilt
import proofs.FiniteCopy.FiniteJump

namespace FiniteCopy
open scoped NNReal
namespace FiniteJumpModel
variable {α β : Type*} [Fintype α] [Fintype β] (M : FiniteJumpModel α β)

noncomputable def withMarks (mark : β → ℝ) (q : ℝ) (hq : 0 < q)
    (hclock : ∀ x, M.total x ≤ q) : MarkedKernel α (Option β) where
  prob := fun x r => match r with | none => 1-M.total x/q | some j => M.rate x j/q
  next := fun x r => match r with | none => x | some j => M.next x j
  mark := fun r => match r with | none => 0 | some j => mark j
  nonneg := by
    intro x r
    cases r with
    | none => exact sub_nonneg.mpr ((div_le_one hq).mpr (hclock x))
    | some j => exact div_nonneg (M.nonneg x j) hq.le
  row_sum := by
    intro x
    rw [Fintype.sum_option]
    dsimp only
    rw [← Finset.sum_div]
    unfold total
    ring

theorem marked_tilted_row (mark : β → ℝ) (alive : Set α) (q θ δ : ℝ)
    (hq : 0 < q) (hclock : ∀ x, M.total x ≤ q)
    (hdead : ∀ x, x ∉ alive → ∀ r, M.next x r ∉ alive)
    (hbudget : ∀ x ∈ alive, ∑ r, M.rate x r*(Real.exp (θ*mark r)-1) ≤ -δ) (x : α) :
    (M.withMarks mark q hq hclock).tiltedRow alive θ x ≤
      (1-δ/q)*FiniteKernel.eventIndicator alive x := by
  classical
  by_cases hx : x ∈ alive
  · have hh (r : β) :
        M.rate x r/q*(if M.next x r ∈ alive then Real.exp (θ*mark r) else 0) ≤
        M.rate x r/q*Real.exp (θ*mark r) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (M.nonneg x r) hq.le)
      split_ifs
      · exact le_rfl
      · exact (Real.exp_pos _).le
    have hs := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hh r)
    have he : 1-M.total x/q+(∑ r, M.rate x r/q*Real.exp (θ*mark r)) =
        1+(∑ r, M.rate x r*(Real.exp (θ*mark r)-1))/q := by
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div]
      unfold total
      ring
    have hb := div_le_div_of_nonneg_right (hbudget x hx) hq.le
    unfold MarkedKernel.tiltedRow
    rw [Fintype.sum_option]
    simp only [withMarks,hx,ite_true,mul_zero,Real.exp_zero,mul_one,FiniteKernel.eventIndicator]
    calc
      _ ≤ 1-M.total x/q+(∑ r, M.rate x r/q*Real.exp (θ*mark r)) := add_le_add le_rfl hs
      _ = 1+(∑ r, M.rate x r*(Real.exp (θ*mark r)-1))/q := he
      _ ≤ 1+(-δ/q) := add_le_add le_rfl hb
      _ = 1-δ/q := by ring
  · unfold MarkedKernel.tiltedRow
    rw [Fintype.sum_option]
    simp [withMarks,hx,hdead x hx,FiniteKernel.eventIndicator]

theorem marked_activity_bound (mark : β → ℝ) (alive : Set α) (q T : ℝ≥0) (θ δ h : ℝ)
    (hq : 0 < (q : ℝ)) (hclock : ∀ x, M.total x ≤ q) (hθ : 0 ≤ θ) (hδq : δ ≤ q)
    (hdead : ∀ x, x ∉ alive → ∀ r, M.next x r ∉ alive)
    (hbudget : ∀ x ∈ alive, ∑ r, M.rate x r*(Real.exp (θ*mark r)-1) ≤ -δ)
    (x : α) (hx : x ∈ alive) :
    (M.withMarks mark q hq hclock).poissonized (q*T)
      (MarkedKernel.eventIndicator {s | s.1 ∈ alive ∧ h ≤ s.2}) x 0 ≤
      Real.exp (-θ*h-δ*(T : ℝ)) := by
  have hh := (M.withMarks mark q hq hclock).activity_chernoff alive θ (1-δ/(q : ℝ)) h hθ
    (sub_nonneg.mpr ((div_le_one hq).mpr hδq))
    (M.marked_tilted_row mark alive q θ δ hq hclock hdead hbudget) (q*T) x hx
  have he : -θ*h+((q*T : ℝ≥0) : ℝ)*(1-δ/(q : ℝ)-1) = -θ*h-δ*(T : ℝ) := by
    rw [NNReal.coe_mul]
    field_simp
    ring
  simpa only [he] using hh

end FiniteJumpModel
end FiniteCopy


