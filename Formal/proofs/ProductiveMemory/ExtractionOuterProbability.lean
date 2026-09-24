import proofs.ProductiveMemory.ExtractionOuterBoundary

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition Set
open scoped NNReal
noncomputable section
set_option Elab.async false
local instance productiveOuterDecidableEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) := Classical.decEq _

theorem productive_active_divisions (N M W0 J : ℕ) (rho zL zH : ℝ)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) : s.val.population.divisions ≤ 7*M := by
  classical
  have hb := (mem_productiveBox N M W0 J s.val).mp (Finset.mem_filter.mp s.property).1
  exact ((SerialTransferSelection.mem_phasePopulationBox N M W0 s.val.population).mp hb.1).2.2

theorem productive_outer_observable_nonneg (N M W0 J : ℕ) (rho zL zH : ℝ)
    (x : ProductiveStopped (productiveActiveDomain N M W0 J rho zL zH)) :
    0 ≤ productiveOuterObservable N M W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH) x := by
  classical
  cases x with
  | inl s =>
    exact add_nonneg (sum_map_nonneg _ (extraction_outer_nonneg N rho zL zH) _)
      (productive_outer_reserve_nonneg N M _ (productive_active_divisions N M W0 J rho zL zH s))
  | inr e => simp only [productiveOuterObservable]; split_ifs <;> positivity

theorem productive_outer_generator (N M W0 J : ℕ) (hN : 1 ≤ N)
    (hlarge : (200000000000000000000:ℝ) ≤ N) (rho zL zH γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hsL : extractDrift rho 0 (lift rho zL) = 0) (hsH : extractDrift rho 0 (lift rho zH) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (x : ProductiveStopped (productiveActiveDomain N M W0 J rho zL zH)) :
    (productiveStoppedModel rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).generator
      (productiveOuterObservable N M W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH)) x ≤
      16*(M:ℝ)*((N:ℝ)*localAlpha*readyLevel/960)*Real.exp ((N:ℝ)*localAlpha*readyLevel/2) := by
  classical
  cases x with
  | inr e => rw [productive_terminal_generator]; unfold localAlpha readyLevel outerLevel; positivity
  | inl s =>
    have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
    have hgen : (productiveStoppedModel rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
        (productiveActiveDomain N M W0 J rho zL zH)).generator
        (productiveOuterObservable N M W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH)) (.inl s) ≤
        ∑ e : ProductiveEvent s.val, productiveRate rho γ (4*W0) s.val e*
          (productiveRawPotential (extractionCellOuter N rho zL zH) s.val e-
            potentialSum (extractionCellOuter N rho zL zH) s.val.population) := by
      rw [productive_active_generator]
      apply Finset.sum_le_sum
      intro e _
      have h := productive_outer_next_le_raw N M W0 J rho zL zH _ s (productive_active_divisions N M W0 J rho zL zH s) e
      apply mul_le_mul_of_nonneg_left _ (productive_rate_nonneg rho γ (by linarith [hr.1]) hγ (4*W0) s.val e)
      change _-(potentialSum (extractionCellOuter N rho zL zH) s.val.population+productiveOuterReserve N M s.val.population.divisions) ≤ _
      linarith only [h]
    rw [productive_raw_generator_sum] at hgen
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s.val.population.live.length)))
      (fun i _ => extraction_outer_source N hN hlarge rho zL zH γ hr hzL hzH hsL hsH hγ hγmax
        s.val.population.resource (4*W0) hs.2.1 (selectedCell s.val.population i)
        (hs.2.2.2.2.1 _ (selected_mem _ _)).1
        (productive_active_energy N M W0 J rho zL zH s _ (selected_mem _ _)))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    have hlen : (s.val.population.live.length:ℝ) ≤ 8*(M:ℝ) := by
      exact_mod_cast productive_active_cell_count N M W0 J rho zL zH s
    have hscale := mul_le_mul_of_nonneg_right hlen
      (by unfold localAlpha readyLevel outerLevel; positivity : 0 ≤ ((N:ℝ)*localAlpha*readyLevel/960)*(2*Real.exp ((N:ℝ)*localAlpha*readyLevel/2)))
    nlinarith only [hgen,hsum,hscale]

def productiveOuterFailure (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState) : Set (ProductiveStopped D) :=
  {x | ∃ e, x=.inr e ∧ productiveReason N W0 J rho zL zH e=.outer}

theorem productive_outer_failure_bound (N M W0 J : ℕ) (hN : 1 ≤ N)
    (hlarge : (200000000000000000000:ℝ) ≤ N) (rho zL zH γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hsL : extractDrift rho 0 (lift rho zL) = 0) (hsH : extractDrift rho 0 (lift rho zH) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (q t : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ x, (productiveStoppedModel rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).total x ≤ q)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) :
    Real.exp ((N:ℝ)*localAlpha*(8*readyLevel))*
      ((productiveStoppedModel rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
        (productiveActiveDomain N M W0 J rho zL zH)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator (productiveOuterFailure N W0 J rho zL zH
          (productiveActiveDomain N M W0 J rho zL zH))) (.inl s) ≤
      potentialSum (extractionCellOuter N rho zL zH) s.val.population+productiveOuterReserve N M s.val.population.divisions+
        (t:ℝ)*(16*(M:ℝ)*((N:ℝ)*localAlpha*readyLevel/960)*Real.exp ((N:ℝ)*localAlpha*readyLevel/2)) := by
  classical
  apply (productiveStoppedModel rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
    (productiveActiveDomain N M W0 J rho zL zH)).uniformized_event_bound q t hq hclock
      (productiveOuterFailure N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH))
      (productiveOuterObservable N M W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH))
  · exact productive_outer_observable_nonneg N M W0 J rho zL zH
  · rintro x ⟨e,rfl,he⟩
    simp [productiveOuterObservable,he]
  · exact productive_outer_generator N M W0 J hN hlarge rho zL zH γ hr hzL hzH hsL hsH hγ hγmax

end
end ProductiveMemory
