import Mathlib

namespace CompositionalMemory

theorem exists_uniform_exponential_parameter (lam S T B : ℝ)
    (hlam : 0 < lam) (hS : 0 ≤ S) (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∃ α : ℝ, 0 < α ∧ α*S ≤ 1 ∧ α*T ≤ 1 ∧ α*B ≤ lam/4 := by
  let D := 1+S+T+4*B/lam
  have hD : 0 < D := by dsimp [D]; positivity
  have hBD : 0 ≤ 4*B/lam := by positivity
  refine ⟨1/D,by positivity,?_,?_,?_⟩
  · calc
      _ = S/D := by ring
      _ ≤ 1 := (div_le_one hD).mpr (by dsimp [D]; linarith)
  · calc
      _ = T/D := by ring
      _ ≤ 1 := (div_le_one hD).mpr (by dsimp [D]; linarith)
  · have he : (lam/4)*D = B+(lam/4)*(1+S+T) := by
      dsimp [D]
      field_simp
      ring
    calc
      _ = B/D := by ring
      _ ≤ lam/4 := (div_le_iff₀ hD).mpr (by rw [he]; exact le_add_of_nonneg_right (by positivity))

theorem exists_uniform_force_copy_parameters (α lam rho H J K C : ℝ)
    (hα : 0 ≤ α) (hlam : 0 < lam) (hrho : 0 < rho)
    (hH : 0 ≤ H) (hJ : 0 ≤ J) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ δ N0 : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      (H/N+J*δ)^2 ≤ lam^2*rho/8 ∧ K+α*C/N ≤ lam*N*rho/8 := by
  let t := min 1 (lam^2*rho/32)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htb : t ≤ lam^2*rho/32 := min_le_right _ _
  let δ := t/(J+1)
  let N0 := 1+H/t+8*(K+α*C)/(lam*rho)
  have hJ1 : 0 < J+1 := by positivity
  have hterm : 0 ≤ 8*(K+α*C)/(lam*rho) := by positivity
  have hHt : 0 ≤ H/t := by positivity
  have hN01 : 1 ≤ N0 := by dsimp [N0]; linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one hJ1).mpr (by linarith)
  refine ⟨δ,N0,hδ,hδ1,hN01,?_⟩
  intro N hN
  have hN1 : 1 ≤ N := hN01.trans hN
  have hN0 : 0 < N := by linarith
  have hHN : H/t ≤ N := by dsimp [N0] at hN; linarith
  have hHN' : H/N ≤ t := (div_le_iff₀ hN0).mpr (by
    have h := (div_le_iff₀ ht).mp hHN
    nlinarith only [h])
  have hJδ : J*δ ≤ t := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hJ1).mpr
    nlinarith only [ht]
  constructor
  · have hpos : 0 ≤ H/N+J*δ := by positivity
    have hs := (sq_le_sq₀ hpos (show 0 ≤ 2*t by positivity)).mpr
      (show H/N+J*δ ≤ 2*t by linarith only [hHN',hJδ])
    nlinarith only [hs,htb,mul_nonneg ht.le (sub_nonneg.mpr ht1)]
  · have hbudget : 8*(K+α*C)/(lam*rho) ≤ N := by dsimp [N0] at hN; linarith
    have hb := (div_le_iff₀ (mul_pos hlam hrho)).mp hbudget
    have hc : α*C/N ≤ α*C := (div_le_iff₀ hN0).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_left hN1 (mul_nonneg hα hC)])
    nlinarith only [hb,hc]

end CompositionalMemory
