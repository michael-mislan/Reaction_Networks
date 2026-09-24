import proofs.CompositionalMemory.WordGeometry

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set

theorem modular_z_count_bounds {k : ℕ} (hk : 1 ≤ k) (s : ModularCountState k)
    (hm : 0 < s.2) (lo hi : ℝ)
    (hz : ∀ i, lo ≤ modularConcentration s i 2 ∧ modularConcentration s i 2 ≤ hi) :
    lo*(s.2 : ℝ) ≤ ∑ i, (s.1 i 2 : ℝ) ∧ ∑ i, (s.1 i 2 : ℝ) ≤ hi*(s.2 : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hmpos : (0 : ℝ) < s.2 := by exact_mod_cast hm
  have hv : (0 : ℝ) < (s.2 : ℝ)/k := div_pos hmpos hkpos
  have hlo (i) : lo*((s.2 : ℝ)/k) ≤ (s.1 i 2 : ℝ) := (le_div_iff₀ hv).mp (hz i).1
  have hhi (i) : (s.1 i 2 : ℝ) ≤ hi*((s.2 : ℝ)/k) := (div_le_iff₀ hv).mp (hz i).2
  have hl := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlo i)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hhi i)
  have hconst (a : ℝ) : ∑ _i : Fin k, a*((s.2 : ℝ)/k) = a*(s.2 : ℝ) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  rw [hconst] at hl hh
  exact ⟨hl,hh⟩

theorem word_membrane_rate_bounds {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (z₀ z₁ γ : ℝ) (σ : Fin k → Bool) (hγ : 0 ≤ γ)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (b : ℝ) (hb : b ≤ 1/32000000) (s : ModularCountState k)
    (hs : s ∈ productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b) :
    (γ/2)*(k*N : ℕ) ≤ ∑ i, γ*(s.1 i 2 : ℝ) ∧
      ∑ i, γ*(s.1 i 2 : ℝ) ≤ 2*(4*γ)*(k*N : ℕ) := by
  have hc := word_center_bounds z₀ z₁ σ h₀ h₁
  have hmem := (mem_productDomain hk N hN _ hc.1 _ (word_energy_lower σ) b hb s).mp hs
  have hmpos : 0 < s.2 := lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hmem.1
  have hz (i) : (1/2 : ℝ) ≤ modularConcentration s i 2 ∧ modularConcentration s i 2 ≤ 4 := by
    have hbounds := product_domain_point_bounds hk N hN _ hc.1 hc.2 _ (word_energy_lower σ) b hb s hs i
    have hcenter : (99/100 : ℝ) ≤ wordCenter z₀ z₁ σ i 2 := by
      change (99/100 : ℝ) ≤ if σ i then z₁ else z₀
      split <;> linarith [h₀.1,h₁.1]
    refine ⟨?_,(hbounds.2.2.2 i).2⟩
    have h := (abs_le.mp (hbounds.1 2)).1
    linarith only [h,hcenter]
  have hcount := modular_z_count_bounds hk s hmpos (1/2) 4 hz
  have hl := mul_le_mul_of_nonneg_left hcount.1 hγ
  have hh := mul_le_mul_of_nonneg_left hcount.2 hγ
  have hml : (k*N : ℕ) ≤ (s.2 : ℝ) := by exact_mod_cast hmem.1
  have hmh : (s.2 : ℝ) ≤ 2*(k*N : ℕ) := by exact_mod_cast hmem.2.1
  have hgl := mul_le_mul_of_nonneg_left hml hγ
  have hgh := mul_le_mul_of_nonneg_left hmh hγ
  rw [Finset.mul_sum] at hl hh
  constructor <;> nlinarith only [hl,hh,hgl,hgh]

end CompositionalMemory
