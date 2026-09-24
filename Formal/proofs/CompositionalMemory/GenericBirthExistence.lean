import proofs.CompositionalMemory.GenericBirthDomain

namespace CompositionalMemory

theorem birth_floor_budget (L birth N : ℝ) (hL : 0 ≤ L) (hb : 0 < birth)
    (hN : 1+L/birth ≤ N) : L/N^2 < birth := by
  have hN1 : 1 ≤ N := by linarith only [hN, div_nonneg hL hb.le]
  have hNp : 0 < N := by linarith only [hN1]
  have hdiv : L ≤ (N-1)*birth :=
    (div_le_iff₀ hb).mp (by linarith only [hN])
  have hsq : N ≤ N^2 := by nlinarith only [mul_le_mul_of_nonneg_left hN1 hNp.le]
  apply (div_lt_iff₀ (sq_pos_of_pos hNp)).mpr
  nlinarith only [hdiv, hb, mul_le_mul_of_nonneg_left hsq hb.le]

/-- Uniform integer initialization: flooring adds energy at most L/N^2. -/
theorem general_birth_nonempty {k d : ℕ} (N C : ℕ) (hN : 0 < N)
    (center : Fin k → Fin d → ℝ)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (L birth : ℝ) (hL : 0 ≤ L)
    (hcenter0 : ∀ i a, 0 ≤ center i a) (hcenterC : ∀ i a, center i a ≤ (C:ℝ))
    (hop : ∀ i x y, |Q i x y| ≤ L*‖x‖*‖y‖) (hlarge : L/(N:ℝ)^2 < birth) :
    Nonempty (GeneralBirthCount N C center (fun i y => Q i y y) birth) := by
  classical
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  let n : Fin k → Fin d → ℕ := fun i a => Nat.floor ((N:ℝ)*center i a)
  have hfloor (i : Fin k) (a : Fin d) : (n i a:ℝ) ≤ (N:ℝ)*center i a :=
    Nat.floor_le (mul_nonneg hNr.le (hcenter0 i a))
  have hcap : n ∈ generalCountBox k d (C*N) := by
    apply (mem_generalCountBox k d (C*N) n).mpr
    intro i a
    have hh := (hfloor i a).trans (mul_le_mul_of_nonneg_left (hcenterC i a) hNr.le)
    have hh' : (n i a:ℝ) ≤ (C:ℝ)*(N:ℝ) := by nlinarith only [hh]
    exact_mod_cast hh'
  refine ⟨⟨n,Finset.mem_filter.mpr ⟨hcap,?_⟩⟩⟩
  intro i
  let y := fun a => (n i a:ℝ)/(N:ℝ)-center i a
  have hy : ‖y‖ ≤ 1/(N:ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    have hup : (n i a:ℝ)/(N:ℝ) ≤ center i a :=
      (div_le_iff₀ hNr).mpr (by nlinarith only [hfloor i a])
    have hfl := Nat.lt_floor_add_one ((N:ℝ)*center i a)
    have hlo : center i a-1/(N:ℝ) ≤ (n i a:ℝ)/(N:ℝ) := by
      apply (le_div_iff₀ hNr).mpr
      have heq : (center i a-1/(N:ℝ))*(N:ℝ)=(N:ℝ)*center i a-1 := by field_simp
      rw [heq]
      have hfl' : (N:ℝ)*center i a < (n i a:ℝ)+1 := hfl
      linarith only [hfl']
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by dsimp [y]; linarith only [hlo],by dsimp [y]; linarith only [hup,one_div_pos.mpr hNr]⟩
  calc
    Q i y y ≤ |Q i y y| := le_abs_self _
    _ ≤ L*‖y‖*‖y‖ := hop i y y
    _ ≤ L*(1/(N:ℝ))*(1/(N:ℝ)) := by gcongr
    _ = L/(N:ℝ)^2 := by ring
    _ < birth := hlarge

end CompositionalMemory
