import proofs.HeritableCompositions.FiniteLaw

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

/-- Conditional joint endpoint law of finitely many independently clocked cells.
Each coordinate retains its own failure outcome; no conditioning on success. -/
noncomputable def recoveryProductLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (μ : ∀ i, FiniteLaw (α i)) :
    FiniteLaw (∀ i, α i) := by
  classical
  exact {
    mass := fun x => ∏ i, (μ i).mass (x i)
    nonneg := fun x => Finset.prod_nonneg (fun i _ => (μ i).nonneg (x i))
    total := by rw [← Fintype.prod_sum]; simp only [FiniteLaw.total, Finset.prod_const_one] }

theorem product_event_indicator {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} (A : ∀ i, Set (α i)) (x : ∀ i, α i) :
    FiniteKernel.eventIndicator {y | ∀ i, y i ∈ A i} x =
      ∏ i, FiniteKernel.eventIndicator (A i) (x i) := by
  classical
  by_cases h : ∀ i, x i ∈ A i
  · simp [FiniteKernel.eventIndicator, h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    have hz : (∏ j, FiniteKernel.eventIndicator (A j) (x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [FiniteKernel.eventIndicator,hi])
    simp [FiniteKernel.eventIndicator, h] at hz ⊢
    exact hz.symm

theorem recoveryProductLaw_event {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FiniteLaw (α i)) (A : ∀ i, Set (α i)) :
    (recoveryProductLaw μ).expect (FiniteKernel.eventIndicator {x | ∀ i, x i ∈ A i}) =
      ∏ i, (μ i).expect (FiniteKernel.eventIndicator (A i)) := by
  classical
  simp only [FiniteLaw.expect, recoveryProductLaw, product_event_indicator,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i y => (μ i).mass y*
    FiniteKernel.eventIndicator (A i) y)).symm

theorem finite_product_union_lower {ι : Type*} (S : Finset ι) (p e : ι → ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i ∧ p i ≤ 1)
    (he : ∀ i ∈ S, 0 ≤ e i) (hb : ∀ i ∈ S, 1-e i ≤ p i) :
    1-(∑ i ∈ S, e i) ≤ ∏ i ∈ S, p i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hpS : ∀ j ∈ S, 0 ≤ p j ∧ p j ≤ 1 := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have heS : ∀ j ∈ S, 0 ≤ e j := fun j hj => he j (Finset.mem_insert_of_mem hj)
    have hbS : ∀ j ∈ S, 1-e j ≤ p j := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hh := ih hpS heS hbS
    have hpi := hp i (Finset.mem_insert_self i S)
    have hei := he i (Finset.mem_insert_self i S)
    have hbi := hb i (Finset.mem_insert_self i S)
    have hm := mul_le_mul_of_nonneg_left hh hpi.1
    have hsum : 0 ≤ ∑ j ∈ S, e j := Finset.sum_nonneg heS
    have hs := mul_le_mul_of_nonneg_right hpi.2 hsum
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith only [hm, hs, hbi]

theorem recoveryProductLaw_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FiniteLaw (α i)) (A : ∀ i, Set (α i)) (e : ℝ) (he : 0 ≤ e)
    (hb : ∀ i, 1-e ≤ (μ i).expect (FiniteKernel.eventIndicator (A i))) :
    1-(Fintype.card ι : ℝ)*e ≤
      (recoveryProductLaw μ).expect (FiniteKernel.eventIndicator {x | ∀ i, x i ∈ A i}) := by
  classical
  rw [recoveryProductLaw_event]
  have hp (i : ι) : 0 ≤ (μ i).expect (FiniteKernel.eventIndicator (A i)) ∧
      (μ i).expect (FiniteKernel.eventIndicator (A i)) ≤ 1 := by
    constructor
    · have h := (μ i).expect_mono (fun _ => 0) (FiniteKernel.eventIndicator (A i))
        (by intro x; unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
      simpa [FiniteLaw.expect_const] using h
    · have h := (μ i).expect_mono (FiniteKernel.eventIndicator (A i)) (fun _ => 1)
        (by intro x; unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
      simpa [FiniteLaw.expect_const] using h
  have h := finite_product_union_lower Finset.univ
    (fun i => (μ i).expect (FiniteKernel.eventIndicator (A i))) (fun _ => e)
    (fun i _ => hp i) (fun _ _ => he) (fun i _ => hb i)
  simpa using h

end SerialTransferSelection
