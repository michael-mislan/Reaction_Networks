import proofs.CompositionalMemory.ResourceBounds

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

theorem source_physical_density {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool) (b : ℝ) (hb : b ≤ 1/32000000)
    (s : {s // s ∈ productDomain N (sourceWordCenter σ) (wordEnergy σ) b}) :
    (1/4 : ℝ) ≤ (residentMolecules s.val : ℝ)/(s.val.2 : ℝ) ∧
      (residentMolecules s.val : ℝ)/(s.val.2 : ℝ) ≤ 280 := by
  have hm := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp s.property).1).2)
  have hml : ((k*N : ℕ) : ℝ) ≤ s.val.2 := by exact_mod_cast hm.1
  have hmh : (s.val.2 : ℝ) ≤ 2*((k*N : ℕ) : ℝ) := by exact_mod_cast hm.2
  have hmpos : (0 : ℝ) < s.val.2 := by
    have hp : (0 : ℝ) < ((k*N : ℕ) : ℝ) := by exact_mod_cast (Nat.mul_pos (by omega : 0 < k) (by omega : 0 < N))
    exact hp.trans_le hml
  have hr := source_resident_bounds hk N hN σ b hb s
  have hru : (residentMolecules s.val : ℝ) ≤ 280*((k*N : ℕ) : ℝ) := by exact_mod_cast hr.2
  constructor
  · apply (le_div_iff₀ hmpos).mpr
    linarith only [hr.1,hmh]
  · apply (div_le_iff₀ hmpos).mpr
    linarith only [hru,hml]

/-- Physical time is k times the two rescaled intervals in wordGenerationLaw. -/
noncomputable def physicalGenerationDeadline (k : ℕ) (γ : ℝ) : ℝ :=
  (k : ℝ)*(2688+11/(5*γ))

theorem physical_generation_time_bounds (k : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) :
    0 ≤ physicalGenerationDeadline k γ ∧ physicalGenerationDeadline k γ ≤ 3*(k : ℝ)/γ := by
  have ht : 2688+11/(5*γ) ≤ 3/γ := by
    apply (le_div_iff₀ hγ).mpr
    have he : (2688+11/(5*γ))*γ = 2688*γ+11/5 := by
      field_simp
    rw [he]
    linarith only [hγmax]
  constructor
  · unfold physicalGenerationDeadline
    positivity
  · have h := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg k)
    unfold physicalGenerationDeadline
    convert h using 1
    ring

end CompositionalMemory
