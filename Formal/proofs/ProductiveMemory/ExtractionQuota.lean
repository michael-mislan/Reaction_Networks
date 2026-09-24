import proofs.ProductiveMemory.ExtractionSupport
import proofs.FiniteCopy.UniformizedBounds

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false
local instance productiveQuotaDecEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) := Classical.decEq _

def productiveCollectedObservable (N : ℕ) {D : Finset ProductiveState} (x : ProductiveStopped D) : ℝ :=
  ((productivePhysical N x).collected:ℝ)

theorem productive_collected_legacy (N : ℕ) (s : ProductiveState) (e : CellEvent s.population) :
    (productiveOutcome N s (.inl e)).collected=s.collected := by
  rcases e with ⟨i,r | d⟩ <;> rfl

theorem productive_collection_generator_binding (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (Ω N W0 J : ℕ) (zL zH : ℝ) (D : Finset ProductiveState) (s : ProductiveActive D) :
    (productiveStoppedModel rho γ hr hg Ω N W0 J zL zH D).generator (productiveCollectedObservable N) (.inl s) =
      ∑ i : Fin s.val.population.live.length, rho*((selectedCell s.val.population i).compartment.1 2:ℝ) := by
  classical
  have hnext (e : ProductiveEvent s.val) :
      productivePhysical N (productiveStoppedNext N W0 J rho zL zH D (.inl s) ⟨s,e⟩) =
        productiveOutcome N s.val e := productive_physical_chosen N W0 J rho zL zH D ⟨s,e⟩
  rw [productive_active_generator,Fintype.sum_sum_type]
  simp only [productiveCollectedObservable]
  simp only [hnext]
  simp only [productivePhysical,productive_collected_legacy,sub_self,mul_zero,Finset.sum_const_zero,zero_add]
  simp only [productiveOutcome,productiveRate,Nat.cast_add,Nat.cast_one,add_sub_cancel_left,mul_one]

theorem productive_collection_generator (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (Ω N M W0 J : ℕ) (zL zH : ℝ)
    (x : ProductiveStopped (productiveActiveDomain N M W0 J rho zL zH)) :
    (productiveStoppedModel rho γ hr hg Ω N W0 J zL zH (productiveActiveDomain N M W0 J rho zL zH)).generator
      (productiveCollectedObservable N) x ≤ 560*(N:ℝ)*(M:ℝ)*rho := by
  classical
  cases x with
  | inr e => rw [productive_terminal_generator]; positivity
  | inl s =>
    have hb := (mem_productiveBox N M W0 J s.val).mp (Finset.mem_filter.mp s.property).1
    have hs := (SerialTransferSelection.mem_phasePopulationBox N M W0 s.val.population).mp hb.1
    rw [productive_collection_generator_binding]
    have hcell (i : Fin s.val.population.live.length) :
        ((selectedCell s.val.population i).compartment.1 2:ℝ) ≤ 70*(N:ℝ) := by
      have hc := (mem_cellBox N _).mp (hs.2.1.2 _ (selected_mem s.val.population i))
      exact_mod_cast hc.2 2
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s.val.population.live.length)))
      (fun i _ => mul_le_mul_of_nonneg_left (hcell i) hr)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    have hlen : (s.val.population.live.length:ℝ) ≤ 8*(M:ℝ) := by exact_mod_cast hs.2.1.1
    have hscale := mul_le_mul_of_nonneg_right hlen (by positivity : 0 ≤ rho*(70*(N:ℝ)))
    nlinarith only [hsum,hscale]

def productiveQuotaFailure (N J : ℕ) (D : Finset ProductiveState) : Set (ProductiveStopped D) :=
  {x | J ≤ (productivePhysical N x).collected}

theorem productive_quota_probability (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (Ω N M W0 J : ℕ) (zL zH : ℝ) (q t : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ x, (productiveStoppedModel rho γ hr hg Ω N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).total x ≤ q)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) :
    (J:ℝ)*((productiveStoppedModel rho γ hr hg Ω N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator (productiveQuotaFailure N J (productiveActiveDomain N M W0 J rho zL zH))) (.inl s) ≤
      (s.val.collected:ℝ)+(t:ℝ)*(560*(N:ℝ)*(M:ℝ)*rho) := by
  classical
  exact (productiveStoppedModel rho γ hr hg Ω N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).uniformized_event_bound q t hq hclock
      (productiveQuotaFailure N J _) (productiveCollectedObservable N) J (560*(N:ℝ)*(M:ℝ)*rho)
      (fun x => Nat.cast_nonneg _)
      (fun x hx => by
        change J ≤ (productivePhysical N x).collected at hx
        change (J:ℝ) ≤ ((productivePhysical N x).collected:ℝ)
        exact_mod_cast hx)
      (productive_collection_generator rho γ hr hg Ω N M W0 J zL zH) (.inl s)

end
end ProductiveMemory
