import proofs.CompositionalMemory.WholeFamily
import proofs.CompositionalMemory.LineageNecessity

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

theorem family_fidelity_upper {α : Type*} [Fintype α]
    (K : α → FiniteLaw (Option (α × α))) (r : ℝ) (hr : 0 ≤ r)
    (hK : ∀ x,1-r ≤ (K x).mass none) (G : ℕ) (x : α) :
    familyFidelity K G x ≤ r^(2^G-1) := by
  induction G generalizing x with
  | zero => simp [familyFidelity]
  | succ G ih =>
    have h := goodIntegral_mono (K x)
      (fun p => familyFidelity K G p.1*familyFidelity K G p.2)
      (fun _ => r^(2^G-1)*r^(2^G-1))
      (fun p => mul_le_mul (ih p.1) (ih p.2) (familyFidelity_nonneg K G p.2) (pow_nonneg hr _))
    rw [goodIntegral_const] at h
    have hq := mul_le_mul_of_nonneg_right (show 1-(K x).mass none ≤ r by linarith [hK x])
      (mul_nonneg (pow_nonneg hr (2^G-1)) (pow_nonneg hr (2^G-1)))
    change goodIntegral (K x) _ ≤ _
    calc
      _ ≤ r*(r^(2^G-1)*r^(2^G-1)) := h.trans hq
      _ = _ := by rw [family_divisions_succ,pow_add,pow_one,Nat.mul_comm 2 (2^G-1),pow_mul,pow_two]

theorem word_lineage_multiplicative_lower {α : Type*} [Fintype α]
    (K : α → FiniteLaw (Option (α × α))) (a : ℝ) (ha : 0 ≤ a)
    (hK : ∀ x,a ≤ 1-(K x).mass none) (G : ℕ) (x : α) :
    a^G ≤ wordLineageSuccess K G x := by
  classical
  have hstep (s : Option α) : a*lineageAlive s ≤ (wordLineageKernel K).step lineageAlive s := by
    change _ ≤ (wordLineageNext K s).expect lineageAlive
    rw [expect_lineageAlive]
    cases s with
    | none => simp [wordLineageNext,FiniteLaw.pure,lineageAlive]
    | some s => simpa [wordLineageNext,option_map_failure,lineageAlive] using hK s
  have hpow (n : ℕ) (s : Option α) : a^n*lineageAlive s ≤ (wordLineageKernel K).steps n lineageAlive s := by
    induction n generalizing s with
    | zero => simp [FiniteKernel.steps]
    | succ n ih =>
      have hm := (wordLineageKernel K).step_mono ih s
      rw [FiniteKernel.step_scale] at hm
      have hh := mul_le_mul_of_nonneg_left (hstep s) (pow_nonneg ha n)
      change _ ≤ (wordLineageKernel K).step _ s
      rw [pow_succ]
      nlinarith only [hh,hm]
  have he : (fun s : Option α => lineageAlive s+FiniteKernel.eventIndicator {none} s)=(fun _ => 1) := by
    funext s
    cases s <;> simp [lineageAlive,FiniteKernel.eventIndicator]
  have hs := steps_additive (wordLineageKernel K) G lineageAlive (FiniteKernel.eventIndicator {none}) (some x)
  rw [he,FiniteKernel.steps_const] at hs
  have hp := hpow G (some x)
  simp only [lineageAlive,mul_one] at hp
  unfold wordLineageSuccess
  linarith only [hp,hs]

/-- Tail bounds imply finite mean lifetime and exclude an infinite flawless lineage.
The expectation is the tail sum, with first failure indexed starting at one. -/
theorem lifetime_tail_bounds (s : ℕ → ℝ) (ε r : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 ≤ r) (hr1 : r < 1)
    (hs : ∀ n,(1-ε)^n ≤ s n ∧ s n ≤ r^n) :
    Summable s ∧ 1/ε ≤ ∑' n,s n ∧ (∑' n,s n) ≤ 1/(1-r) ∧
      Filter.Tendsto s Filter.atTop (nhds 0) := by
  have hl : 0 ≤ 1-ε := by linarith
  have hl1 : 1-ε < 1 := by linarith
  have hsr := summable_geometric_of_lt_one hr hr1
  have hsl := summable_geometric_of_lt_one hl hl1
  have hn (n) : 0 ≤ s n := (pow_nonneg hl n).trans (hs n).1
  have hss : Summable s := Summable.of_nonneg_of_le hn (fun n => (hs n).2) hsr
  refine ⟨hss,?_,?_,?_⟩
  · have h := Summable.tsum_le_tsum (fun n => (hs n).1) hsl hss
    rw [tsum_geometric_of_lt_one hl hl1] at h
    convert h using 1
    ring
  · have h := Summable.tsum_le_tsum (fun n => (hs n).2) hss hsr
    simpa [tsum_geometric_of_lt_one hr hr1,one_div] using h
  · exact squeeze_zero hn (fun n => (hs n).2) (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1)

/-- A finite graph of bounded degree has a row allowance independent of its order. -/
theorem bounded_degree_row {k : ℕ} (neighbors : Fin k → Finset (Fin k))
    (Δ : ℕ) (hΔ : 0 < Δ) (κ : ℝ) (hκ : 0 ≤ κ) (w : Fin k → Fin k → ℝ)
    (hdeg : ∀ i,(neighbors i).card ≤ Δ)
    (hoff : ∀ i j,j ∉ neighbors i → w i j=0)
    (hedge : ∀ i j,j ∈ neighbors i → w i j ≤ κ/Δ) :
    ∀ i,∑ j,w i j ≤ κ := by
  intro i
  have he : (∑ j,w i j)=∑ j ∈ neighbors i,w i j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    exact hoff i j hj
  rw [he]
  calc
    _ ≤ ∑ _j ∈ neighbors i,κ/Δ := Finset.sum_le_sum (fun j hj => hedge i j hj)
    _ = ((neighbors i).card : ℝ)*(κ/Δ) := by simp
    _ ≤ (Δ : ℝ)*(κ/Δ) := mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg i) (div_nonneg hκ (Nat.cast_nonneg _))
    _ = κ := by
      have hd : (Δ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hΔ)
      field_simp

end CompositionalMemory
