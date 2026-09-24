import proofs.CompositionalMemory.ReversibleCountChemistry

namespace CompositionalMemory

/-- Propensities in seconds for C0=1 micromolar and F=W=1 millimolar.
Omega=N_A*V=10^6*m. Pair propensities use the ordered/falling-factorial convention.
The coefficients in this table are fixed, not functions of molecule count. -/
noncomputable def reversibleCalibratedRate (ε ρ : ℝ) (m x y z : Nat) (r : Fin 14) : ℝ :=
  let Ω : ℝ := 1000000*m
  let F : ℝ := 1000*m
  let W : ℝ := 1000*m
  let q : ℝ := (x*(x-1) : Nat)
  ![(193/5000)*F,1555000*(y : ℝ)*F/Ω,15000000*q/Ω,
    100000000*(x : ℝ)*(y : ℝ)/Ω,(105/2)*(x : ℝ),(x : ℝ)/10,
    (1000000*ε)*(x : ℝ)*(z : ℝ)/Ω,(1000000*ε)*(y : ℝ)*(z : ℝ)/Ω,
    (193/750000)*(x : ℝ),(31100/3)*q/Ω,15000000*(x : ℝ)*(y : ℝ)/Ω,
    (y : ℝ)*W/Ω,(21/40000000)*W,ρ*(m : ℝ)] r

theorem reversible_dimensional_rate_identity (N : Nat) (ε ρ : ℝ)
    (s : Nat × (Fin 2 → Int × Int)) (r : ReversiblePhysicalChannel)
    (hm : s.1≠0) (hdiv : s.1≠2*N)
    (hn : ∀ k, 0 ≤ (s.2 k).1 ∧ 0 ≤ (s.2 k).2) :
    reversibleRawRate N ε ρ s r=reversibleCalibratedRate ε ρ s.1
      (s.2 r.1).1.toNat (s.2 r.1).2.toNat (s.2 ⟨1-r.1.val,by omega⟩).2.toNat r.2 := by
  have hbad : ¬(s.1=0 ∨ s.1=2*N ∨ ∃ k, (s.2 k).1<0 ∨ (s.2 k).2<0) := by
    rintro (h | h | ⟨k,h | h⟩)
    · exact hm h
    · exact hdiv h
    · exact (not_lt.mpr (hn k).1) h
    · exact (not_lt.mpr (hn k).2) h
  have hmr : (s.1 : ℝ)≠0 := Nat.cast_ne_zero.mpr hm
  simp only [reversibleRawRate,if_neg hbad]
  rcases r with ⟨k,r⟩
  fin_cases r <;> norm_num [reversibleCalibratedRate] <;>
    field_simp <;> ring

theorem reversible_positive_growth_ratio (ρ : ℝ)
    (hlo : 1/10000000 ≤ ρ) (hhi : ρ ≤ 2/10000000) :
    0 < ρ ∧ 500000 ≤ (1/10 : ℝ)/ρ ∧ (1/10 : ℝ)/ρ ≤ 1000000 := by
  have hp : 0 < ρ := by linarith
  refine ⟨hp,?_,?_⟩
  · apply (le_div_iff₀ hp).mpr
    linarith
  · apply (div_le_iff₀ hp).mpr
    linarith

end CompositionalMemory
