import proofs.StartupCount.KilledTerminal
import proofs.StartupCount.CensoredAffine

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Affine drift controls the killed terminal payoff under the actual marked
trajectory measure. The exponential clock and channel law are discharged. -/
theorem physical_affine_terminal_bound (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (guard : α → Prop) (f : α → ℝ) (hf : ∀ x,0 ≤ f x)
    (c b : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hcR : ∀ x,guard x → c < ∑ j,rate x j)
    (hgen : ∀ x,guard x → (∑ j,rate x j*(f (next x j)-f x)) ≤ -c*f x+c*b)
    (T : ℝ) (hT : 0 ≤ T) (x : α) :
    (∫⁻ z,⨆ k,killedTerminal guard (fun y => ENNReal.ofReal (f y)) k T z
      ∂jumpTrajectoryLaw x next rate hr ht) ≤ ENNReal.ofReal (affineEnvelope c b (f x) T) := by
  apply killedTerminal_limit_bound next rate hr ht guard (fun y => ENNReal.ofReal (f y))
    (fun t y => ENNReal.ofReal (affineEnvelope c b (f y) t)) _ T hT x
  intro t ht' y hy
  apply jumpClock_affine_bound (rate y) (hr y) (ht y) (fun j => f (next y j))
    (fun j => hf (next y j)) c b (f y) t hc (hcR y hy) hb (hf y) ht'
  have hh := hgen y hy
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul] at hh
  nlinarith only [hh]

end
end StartupCount
