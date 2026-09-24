import proofs.CompositionalMemory.WordPartitionReturn

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC HeritableCompositions Set

noncomputable def wordBirthRegion {k : ℕ} (N : ℕ) (center : Fin k → Point)
    (σ : Fin k → Bool) : Set (ModularCountState k) :=
  {s | s.2=k*N ∧ ∀ i, wordEnergy σ i
    (fun a => modularConcentration s i a-center i a) ≤ 4*innerEnergy}

noncomputable instance {k : ℕ} (N : ℕ) (center : Fin k → Point) (σ : Fin k → Bool)
    (s : ModularCountState k) : Decidable (s ∈ wordBirthRegion N center σ) := Classical.propDecidable _

theorem module_lattice_concentration {k : ℕ} (hk : 1 ≤ k) (N : ℕ)
    (n : Fin k → Counts) (i : Fin k) :
    modularConcentration (n,k*N) i = concentration N (n i) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hvol : (((k*N : ℕ) : ℝ)/(k : ℝ)) = (N : ℝ) := by
    push_cast
    field_simp
  change effectiveConcentration (((k*N : ℕ) : ℝ)/k) (n i) = concentration N (n i)
  rw [hvol]
  rfl

theorem division_lattice_concentration {k : ℕ} (hk : 1 ≤ k) (N : ℕ)
    (n : Fin k → Counts) (i : Fin k) :
    modularConcentration (n,2*(k*N)) i = concentration (2*N) (n i) := by
  rw [show 2*(k*N)=k*(2*N) by ring]
  exact module_lattice_concentration hk (2*N) n i

theorem word_return_birth {k : ℕ} (hk : 1 ≤ k) (N : ℕ)
    (center : Fin k → Point) (σ : Fin k → Bool) (n : Fin k → Counts) (d : WordDraw k)
    (hr : wordBothReturn N center σ n d) :
    (drawModule d,k*N) ∈ wordBirthRegion N center σ ∧
      (wordSibling n d,k*N) ∈ wordBirthRegion N center σ := by
  constructor
  · refine ⟨rfl,?_⟩
    intro i
    change wordEnergy σ i (fun a => modularConcentration (drawModule d,k*N) i a-center i a) ≤ _
    rw [module_lattice_concentration hk N (drawModule d) i]
    exact (hr i).1.le
  · refine ⟨rfl,?_⟩
    intro i
    change wordEnergy σ i (fun a => modularConcentration (wordSibling n d,k*N) i a-center i a) ≤ _
    rw [module_lattice_concentration hk N (wordSibling n d) i]
    exact (hr i).2.le

/-- Full word, both complementary daughters, immediate closed birth-region
return. The actual parent membrane is 2*k*N. -/
theorem source_word_partition_failure {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 0 < N)
    (z₀ z₁ : ℝ) (σ : Fin k → Bool)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (n : Fin k → Counts)
    (hparent : ∀ i, wordEnergy σ i (fun a => modularConcentration (n,2*(k*N)) i a-
      wordCenter z₀ z₁ σ i a) ≤ 2*innerEnergy) :
    (∑ d ∈ wordDraws n, wordDrawWeight n d*
      (if ¬ ((drawModule d,k*N) ∈ wordBirthRegion N (wordCenter z₀ z₁ σ) σ ∧
        (wordSibling n d,k*N) ∈ wordBirthRegion N (wordCenter z₀ z₁ σ) σ) then 1 else 0)) ≤
      8*(k : ℝ)*Real.exp (-(N : ℝ)*(1/1000000)^2/35) := by
  classical
  have hc := word_center_bounds z₀ z₁ σ h₀ h₁
  have hp (i) : wordEnergy σ i (fun a => concentration (2*N) (n i) a-wordCenter z₀ z₁ σ i a) ≤
      2*innerEnergy := by
    simpa only [division_lattice_concentration hk N n i] using hparent i
  have h := word_partition_failure N hN _ hc.1 σ n hp
  apply le_trans _ h
  apply Finset.sum_le_sum
  intro d _
  by_cases hr : wordBothReturn N (wordCenter z₀ z₁ σ) σ n d
  · have hb := word_return_birth hk N _ σ n d hr
    simp only [if_neg (not_not.mpr hb),if_neg (not_not.mpr hr)]
    exact le_rfl
  · rw [if_pos hr,mul_one]
    split_ifs
    · simpa only [mul_zero] using word_draw_weight_nonneg n d
    · simp

end CompositionalMemory
