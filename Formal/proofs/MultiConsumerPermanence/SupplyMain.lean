import proofs.MultiConsumerPermanence.SupplyLimits
import proofs.MultiConsumerPermanence.ZeroSupplyGlobalExistence
import proofs.MultiConsumerPermanence.ReservoirGlobalExistence

namespace MultiConsumerPermanence
open CoreCouplingCAC Filter Topology

theorem no_uniform_floor_down_to_zero_supply {n : ℕ} (hn : 0 < n) (e : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) :
    ¬ ∃ eta : ℝ, 0 < eta ∧ ∀ d : ℝ, 0 < d →
      ∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ),
      IsReservoirTrajectory n e d d Y x R → ∀ᶠ t in atTop, ∀ i, eta ≤ x t i := by
  rintro ⟨eta,heta,hfloor⟩
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let d : ℝ := (n:ℝ)*eta/4
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨Y,x,R,_,_,_,h⟩ := reservoir_positive_global_solution n e d he he' hd
    ⟨1,1,1,1⟩ (fun _ => 1) 1 (by norm_num [State.Positive]) (by intro i; norm_num) (by norm_num)
  have hb := necessary_supply_for_species_floor e d eta hd.le heta.le Y x R h (hfloor d hd Y x R h)
  have hp := mul_pos hnR heta
  have hq := mul_nonneg (sq_nonneg (n:ℝ)) (sq_nonneg eta)
  dsimp [d] at hb
  nlinarith only [hb,hp,hq]

/-- B3: the zero-supply source has actual positive global solutions, every
consumer tends to zero, and any permanent positive floor requires positive supply. -/
theorem reservoir_supply_operating_limits (n : ℕ) (hn : 2 ≤ n) (e : ℝ)
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000) :
    (∀ (s₀ : State) (x₀ : Fin n → ℝ) (r₀ : ℝ), s₀.Positive → (∀ i, 0 < x₀ i) → 0 < r₀ →
      ∃ Y : ℝ → State, ∃ x : ℝ → Fin n → ℝ, ∃ R : ℝ → ℝ,
        Y 0 = s₀ ∧ x 0 = x₀ ∧ R 0 = r₀ ∧ IsReservoirTrajectory n e 0 0 Y x R) ∧
    (∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ),
      IsReservoirTrajectory n e 0 0 Y x R → ∀ i, Tendsto (fun t => x t i) atTop (𝓝 0)) ∧
    (∀ d eta : ℝ, 0 ≤ d → 0 ≤ eta →
      ∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ), IsReservoirTrajectory n e d d Y x R →
      (∀ᶠ t in atTop, ∀ i, eta ≤ x t i) → ((n:ℝ)*eta)/2+(n:ℝ)^2*eta^2 ≤ d) ∧
    (¬ ∃ eta : ℝ, 0 < eta ∧ ∀ d : ℝ, 0 < d →
      ∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ),
      IsReservoirTrajectory n e d d Y x R → ∀ᶠ t in atTop, ∀ i, eta ≤ x t i) := by
  have he0 : 0 ≤ e := by linarith
  exact ⟨zero_supply_positive_global_solution n e he0 he',
    zero_supply_every_consumer_extinction e,
    fun d eta => necessary_supply_for_species_floor e d eta,
    no_uniform_floor_down_to_zero_supply (by omega) e he0 he'⟩

end MultiConsumerPermanence
