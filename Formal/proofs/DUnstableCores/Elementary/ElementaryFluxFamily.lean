import proofs.DUnstableCores.Elementary.ElementarySource

namespace DUnstableCores

def elementaryFamilyFlux (s T : ℝ) : Fin 6 → ℝ :=
  ![s*T,4*s,s*T,s,s*(T-1),2*s]

theorem elementaryFamilyFlux_positive (s T : ℝ) (hs : 0 < s) (hT : 1 < T) :
    ∀ r, 0 < elementaryFamilyFlux s T r := by
  intro r
  have ht : 0 < T := lt_trans (by norm_num) hT
  have ht1 : 0 < T-1 := sub_pos.mpr hT
  fin_cases r <;> dsimp [elementaryFamilyFlux] <;> positivity

theorem elementaryFamilyFlux_stationary (s T : ℝ) :
    ∀ i, ∑ r : Fin 6, (elementarySource.stoich i r : ℝ) *
      elementaryFamilyFlux s T r = 0 := by
  intro i
  fin_cases i
  · norm_num [elementarySource,SourceNetwork.stoich,elementaryFamilyFlux,Fin.sum_univ_succ]
    ring
  all_goals norm_num [elementarySource,SourceNetwork.stoich,elementaryFamilyFlux,Fin.sum_univ_succ]

theorem elementary_positive_stationary_flux_complete
    (v : Fin 6 → ℝ) (hv : ∀ r, 0 < v r)
    (hb : ∀ i, ∑ r : Fin 6, (elementarySource.stoich i r : ℝ)*v r = 0) :
    ∃ s T : ℝ, 0 < s ∧ 1 < T ∧ v = elementaryFamilyFlux s T := by
  have hA := hb 0
  have hB := hb 1
  have hC := hb 2
  have hD := hb 3
  have hS (i : Fin 4) (r : Fin 6) : (elementarySource.stoich i r : ℝ) =
      (!![-1,0,0,1,1,0; 0,-1,0,4,0,0; 2,-1,-2,4,0,0; -1,0,1,-2,0,1] :
        Matrix (Fin 4) (Fin 6) ℝ) i r := by
    fin_cases i <;> fin_cases r <;> norm_num [elementarySource,SourceNetwork.stoich]
  simp_rw [hS] at hA hB hC hD
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty] at hA hB hC hD
  change (-1:ℝ)*v 0+(0*v 1+(0*v 2+(1*v 3+(1*v 4+(0*v 5+0)))))=0 at hA
  change (0:ℝ)*v 0+((-1)*v 1+(0*v 2+(4*v 3+(0*v 4+(0*v 5+0)))))=0 at hB
  change (2:ℝ)*v 0+((-1)*v 1+((-2)*v 2+(4*v 3+(0*v 4+(0*v 5+0)))))=0 at hC
  change (-1:ℝ)*v 0+(0*v 1+(1*v 2+((-2)*v 3+(0*v 4+(1*v 5+0)))))=0 at hD
  norm_num at hA hB hC hD
  have hs := hv 3
  have hn : v 3 ≠ 0 := ne_of_gt hs
  have hT : 1 < v 0 / v 3 := (lt_div_iff₀ hs).mpr (by nlinarith [hv 4])
  refine ⟨v 3,v 0/v 3,hs,hT,?_⟩
  funext r
  fin_cases r
  · change v 0 = v 3*(v 0/v 3)
    field_simp [hn]
  · change v 1 = 4*v 3
    linarith
  · change v 2 = v 3*(v 0/v 3)
    field_simp [hn]
    nlinarith
  · rfl
  · change v 4 = v 3*(v 0/v 3-1)
    field_simp [hn]
    nlinarith
  · change v 5 = 2*v 3
    linarith

theorem elementaryFamilyFlux_reconstruct (s T : ℝ) (hs : 0 < s) (hT : 1 < T)
    (x : Fin 4 → ℝ) (hx : ∀ i, 0 < x i) :
    (∀ r, 0 < reconstructedRate elementarySource x (elementaryFamilyFlux s T) r) ∧
    (∀ r, reconstructedRate elementarySource x (elementaryFamilyFlux s T) r *
      massActionMonomial elementarySource x r = elementaryFamilyFlux s T r) :=
  ⟨reconstructedRate_pos _ _ _ hx (elementaryFamilyFlux_positive s T hs hT),
    reconstructedRate_mul_monomial _ _ _ hx⟩

end DUnstableCores




