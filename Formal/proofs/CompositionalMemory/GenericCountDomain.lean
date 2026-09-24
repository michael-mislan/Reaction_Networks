import Mathlib

namespace CompositionalMemory

abbrev GeneralCountState (k d : ℕ) := (Fin k → Fin d → ℕ) × ℕ

noncomputable def generalConcentration {k d : ℕ} (s : GeneralCountState k d)
    (i : Fin k) (j : Fin d) : ℝ := (s.1 i j:ℝ)/((s.2:ℝ)/k)

noncomputable def generalCountBox (k d cap : ℕ) : Finset (Fin k → Fin d → ℕ) := by
  classical
  exact Finset.univ.image (fun f : Fin k → Fin d → Fin (cap+1) => fun i j => (f i j).val)

theorem mem_generalCountBox (k d cap : ℕ) (n : Fin k → Fin d → ℕ) :
    n ∈ generalCountBox k d cap ↔ ∀ i j, n i j ≤ cap := by
  classical
  constructor
  · intro hn
    obtain ⟨f,_,hf⟩ := Finset.mem_image.mp hn
    intro i j
    have hi := (f i j).isLt
    have he := congrFun (congrFun hf i) j
    omega
  · intro hn
    exact Finset.mem_image.mpr
      ⟨fun i j => ⟨n i j,by have h := hn i j; omega⟩,Finset.mem_univ _,rfl⟩

noncomputable def generalProductDomain {k d : ℕ} (N C : ℕ)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ) (b : ℝ) :
    Finset (GeneralCountState k d) := by
  classical
  exact ((generalCountBox k d (C*(2*N))).product (Finset.Icc (k*N) (2*(k*N)))).filter
    (fun s => ∀ i, E i (fun j => generalConcentration s i j-center i j) < b)

theorem energy_coordinate_cap {k d : ℕ} (C : ℕ) (c radius b : ℝ)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ)
    (hc : 0 < c) (hradius : 0 ≤ radius) (hb : b ≤ c*radius^2)
    (hcenter : ∀ i j, center i j ≤ (C:ℝ)-radius)
    (hE : ∀ i y j, c*(y j)^2 ≤ E i y) (i : Fin k) (x : Fin d → ℝ)
    (he : E i (fun j => x j-center i j) < b) (j : Fin d) : x j ≤ C := by
  have hs : (x j-center i j)^2 ≤ radius^2 :=
    (mul_le_mul_iff_right₀ hc).mp ((hE i _ j).trans (he.le.trans hb))
  have ha : |x j-center i j| ≤ radius :=
    (sq_le_sq₀ (abs_nonneg _) hradius).mp (by simpa only [sq_abs] using hs)
  linarith only [(abs_le.mp ha).2,hcenter i j]

theorem mem_generalProductDomain {k d : ℕ} (hk : 1 ≤ k) (N C : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ)
    (c radius b : ℝ) (hc : 0 < c) (hradius : 0 ≤ radius) (hb : b ≤ c*radius^2)
    (hcenter : ∀ i j, center i j ≤ (C:ℝ)-radius) (hE : ∀ i y j, c*(y j)^2 ≤ E i y)
    (s : GeneralCountState k d) :
    s ∈ generalProductDomain N C center E b ↔ k*N ≤ s.2 ∧ s.2 ≤ 2*(k*N) ∧
      ∀ i, E i (fun j => generalConcentration s i j-center i j) < b := by
  classical
  change (s.1,s.2) ∈ generalProductDomain N C center E b ↔ _
  simp only [generalProductDomain,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_,hlo,hhi⟩,he⟩
    exact ⟨hlo,hhi,he⟩
  · rintro ⟨hlo,hhi,he⟩
    have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hmpos : (0:ℝ) < s.2 := by
      exact_mod_cast (lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hlo)
    have hvpos : 0 < (s.2:ℝ)/k := div_pos hmpos hkpos
    have hvmax : (s.2:ℝ)/k ≤ 2*(N:ℝ) := by
      apply (div_le_iff₀ hkpos).mpr
      exact_mod_cast (by nlinarith only [hhi] : s.2 ≤ 2*N*k)
    have hn : s.1 ∈ generalCountBox k d (C*(2*N)) := by
      apply (mem_generalCountBox k d _ s.1).mpr
      intro i j
      have hx := energy_coordinate_cap C c radius b center E hc hradius hb hcenter hE
        i (generalConcentration s i) (he i) j
      have hnreal : (s.1 i j:ℝ) ≤ (C:ℝ)*((s.2:ℝ)/k) := (div_le_iff₀ hvpos).mp hx
      have hnmax := hnreal.trans (mul_le_mul_of_nonneg_left hvmax (Nat.cast_nonneg C))
      exact_mod_cast hnmax
    exact ⟨⟨hn,hlo,hhi⟩,he⟩

end CompositionalMemory
