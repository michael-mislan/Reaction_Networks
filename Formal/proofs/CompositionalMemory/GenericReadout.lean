import proofs.CompositionalMemory.GenericBirthDomain

namespace CompositionalMemory

theorem general_birth_norm_lt {k d : ℕ} (N C : ℕ)
    (center : Fin k → Fin d → ℝ)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (c radius birth : ℝ) (hc : 0 < c) (hr : 0 ≤ radius) (hb : birth ≤ c*radius^2)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y)
    (n : GeneralBirthCount N C center (fun i y => Q i y y) birth) (i : Fin k) :
    ‖fun a => (n.val i a:ℝ)/(N:ℝ)-center i a‖ < radius := by
  classical
  have he := (Finset.mem_filter.mp n.property).2 i
  let y := fun a => (n.val i a:ℝ)/(N:ℝ)-center i a
  have he' : Q i y y < birth := he
  by_contra h
  have hn : radius ≤ ‖y‖ := le_of_not_gt h
  have hs : radius^2 ≤ ‖y‖^2 := (sq_le_sq₀ hr (norm_nonneg y)).mpr hn
  nlinarith only [mul_le_mul_of_nonneg_left hs hc.le,hcoerc i y,he',hb]

noncomputable def generalWordReadout {k d : ℕ} (N : ℕ)
    (a : Fin k → Fin d) (threshold : Fin k → ℝ) (n : Fin k → Fin d → ℕ) : Fin k → Bool :=
  fun i => decide (threshold i < (n i (a i):ℝ)/(N:ℝ))

/-- A fixed coordinate threshold decodes every certified newborn. -/
theorem general_birth_readout {k d : ℕ} (N C : ℕ)
    (center : Fin k → Fin d → ℝ)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (c radius birth : ℝ) (hc : 0 < c) (hr : 0 ≤ radius) (hb : birth ≤ c*radius^2)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y)
    (σ : Fin k → Bool) (a : Fin k → Fin d) (threshold : Fin k → ℝ)
    (hmargin : ∀ i, if σ i then threshold i+radius ≤ center i (a i)
      else center i (a i)+radius ≤ threshold i)
    (n : GeneralBirthCount N C center (fun i y => Q i y y) birth) :
    generalWordReadout N a threshold n.val=σ := by
  funext i
  let y := fun b => (n.val i b:ℝ)/(N:ℝ)-center i b
  have hn : ‖y‖ < radius := general_birth_norm_lt N C center Q c radius birth hc hr hb hcoerc n i
  have ha : ‖y (a i)‖ ≤ ‖y‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mp le_rfl (a i)
  have habs : |(n.val i (a i):ℝ)/(N:ℝ)-center i (a i)| < radius :=
    (show ‖y (a i)‖ < radius from ha.trans_lt hn)
  have hlo := (abs_lt.mp habs).1
  have hhi := (abs_lt.mp habs).2
  have hm := hmargin i
  cases hs : σ i with
  | false =>
    simp only [hs,Bool.false_eq_true,if_false] at hm
    have hh : ¬threshold i < (n.val i (a i):ℝ)/(N:ℝ) := by linarith only [hhi,hm]
    simp only [generalWordReadout,decide_eq_false hh]
  | true =>
    simp only [hs,if_true] at hm
    have hh : threshold i < (n.val i (a i):ℝ)/(N:ℝ) := by linarith only [hlo,hm]
    simp only [generalWordReadout,decide_eq_true hh]

theorem general_word_initialization_injective {k d : ℕ} (N : ℕ)
    (a : Fin k → Fin d) (threshold : Fin k → ℝ)
    (initial : (Fin k → Bool) → Fin k → Fin d → ℕ)
    (hdecode : ∀ σ, generalWordReadout N a threshold (initial σ)=σ) :
    Function.Injective initial :=
  Function.LeftInverse.injective hdecode

end CompositionalMemory
