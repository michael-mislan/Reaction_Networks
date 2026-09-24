import proofs.CompositionalMemory.CountBinding
import proofs.FiniteCopy.WellDomains

namespace CompositionalMemory
open FiniteCopy

noncomputable def modularCountBox (k N : ℕ) : Finset (Fin k → Counts) := by
  classical
  exact Finset.univ.image (fun f : Fin k → Fin 4 → Fin (35*N+1) => fun j a => (f j a).val)

theorem mem_modularCountBox {k : ℕ} (N : ℕ) (n : Fin k → Counts) :
    n ∈ modularCountBox k N ↔ ∀ j a, n j a ≤ 35*N := by
  classical
  constructor
  · intro hn
    obtain ⟨f,_,hf⟩ := Finset.mem_image.mp hn
    intro j a
    have hi := (f j a).isLt
    have he := congrFun (congrFun hf j) a
    omega
  · intro hn
    apply Finset.mem_image.mpr
    exact ⟨fun j a => ⟨n j a,by have h := hn j a; omega⟩,Finset.mem_univ _,rfl⟩

noncomputable def productDomain {k : ℕ} (N : ℕ) (center : Fin k → Point)
    (E : Fin k → Point → ℝ) (b : ℝ) : Finset (ModularCountState k) := by
  classical
  exact ((modularCountBox k (2*N)).product (Finset.Icc (k*N) (2*(k*N)))).filter
    (fun s => ∀ j, E j (fun a => modularConcentration s j a-center j a) < b)

theorem mem_productDomain {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ j a, center j a ≤ 34)
    (E : Fin k → Point → ℝ) (hE : ∀ j y, (1/200)*normSq y ≤ E j y)
    (b : ℝ) (hb : b ≤ 1/32000000) (s : ModularCountState k) :
    s ∈ productDomain N center E b ↔ k*N ≤ s.2 ∧ s.2 ≤ 2*(k*N) ∧
      ∀ j, E j (fun a => modularConcentration s j a-center j a) < b := by
  classical
  change (s.1,s.2) ∈ productDomain N center E b ↔ _
  simp only [productDomain,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_,hlo,hhi⟩,he⟩
    exact ⟨hlo,hhi,he⟩
  · rintro ⟨hlo,hhi,he⟩
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hmpos : (0 : ℝ) < s.2 := by
      exact_mod_cast (lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hlo)
    have hvpos : (0 : ℝ) < (s.2 : ℝ)/k := div_pos hmpos hkpos
    have hvr : (s.2 : ℝ)/k ≤ 2*(N : ℝ) := by
      apply (div_le_iff₀ hkpos).mpr
      exact_mod_cast (by nlinarith only [hhi] : s.2 ≤ 2*N*k)
    have hn : s.1 ∈ modularCountBox k (2*N) := by
      apply (mem_modularCountBox (2*N) s.1).mpr
      intro j a
      have hy := (abs_le.mp (small_energy_coordinates (E j) (hE j) _ ((he j).trans_le hb) a)).2
      have hx : modularConcentration s j a ≤ 35 := by linarith [hc j a]
      have hnreal : (s.1 j a : ℝ) ≤ 35*((s.2 : ℝ)/k) := (div_le_iff₀ hvpos).mp hx
      have hnmax : (s.1 j a : ℝ) ≤ 35*(2*(N : ℝ)) := by nlinarith only [hnreal,hvr]
      exact_mod_cast hnmax
    exact ⟨⟨hn,hlo,hhi⟩,he⟩

theorem product_departure_energy {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ j a, center j a ≤ 34)
    (E : Fin k → Point → ℝ) (hE : ∀ j y, (1/200)*normSq y ≤ E j y)
    (b : ℝ) (hb : b ≤ 1/32000000) (s : ModularCountState k)
    (hs : s ∈ productDomain N center E b) (hm : s.2 < 2*(k*N))
    (r : ModularChannel k) (hout : modularNext s r ∉ productDomain N center E b) :
    ∃ j, b ≤ E j (fun a => modularConcentration (modularNext s r) j a-center j a) := by
  classical
  have hmem := mem_productDomain hk N hN center hc E hE b hb s
  have hr := modular_membrane_range N s (hmem.mp hs).1 hm r
  by_contra h
  push Not at h
  exact hout ((mem_productDomain hk N hN center hc E hE b hb (modularNext s r)).mpr
    ⟨hr.1,hr.2,h⟩)

end CompositionalMemory
