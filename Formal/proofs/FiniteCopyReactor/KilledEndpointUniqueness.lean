import proofs.FiniteCopyReactor.EndpointUniqueness
import proofs.FiniteCopyReactor.SurvivalBounds

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The global process may have unbounded rates: a killed endpoint needs the rate bound only before exit. -/
theorem killed_endpoint_renewal_unique (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (q : ℝ) (hq : 0 ≤ q) (hbound : ∀ x ∈ D,(∑ b,rate x b) ≤ q)
    (F G B : ℝ × α → ℝ≥0∞) (hFm : Measurable F) (hGm : Measurable G)
    (hF1 : ∀ p,F p ≤ 1) (hG1 : ∀ p,G p ≤ 1)
    (hFn : ∀ p,p.1 < 0 → F p=0) (hGn : ∀ p,p.1 < 0 → G p=0)
    (hF0 : ∀ p,p.2 ∉ D → F p=0) (hG0 : ∀ p,p.2 ∉ D → G p=0) (hB0 : ∀ p,p.2 ∉ D → B p=0)
    (hF : ∀ p,p.2 ∈ D → F p=B p+∫⁻ y,F (p.1-y.2,next p.2 y.1) ∂jumpClockMeasure (rate p.2) (hr p.2) (ht p.2))
    (hG : ∀ p,p.2 ∈ D → G p=B p+∫⁻ y,G (p.1-y.2,next p.2 y.1) ∂jumpClockMeasure (rate p.2) (hr p.2) (ht p.2)) : F=G := by
  let step := fun (p : ℝ × α) (y : β × ℝ) => (p.1-y.2,next p.2 y.1)
  have hm (p : ℝ × α) : Measurable (step p) :=
    (measurable_const.sub measurable_snd).prodMk ((measurable_of_countable (next p.2)).comp measurable_fst)
  let μ := fun p : ℝ × α => if p.2 ∈ D then
    (jumpClockMeasure (rate p.2) (hr p.2) (ht p.2)).map (step p) else 0
  let w := fun p : ℝ × α => Real.exp (q*p.1)
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hweight (p : ℝ × α) : (∫⁻ a,ENNReal.ofReal (w a) ∂μ p) ≤
      ENNReal.ofReal (1/2:ℝ)*ENNReal.ofReal (w p) := by
    by_cases hp : p.2 ∈ D
    · dsimp only [μ]
      rw [if_pos hp,lintegral_map hw.ennreal_ofReal (hm p)]
      exact jump_clock_half_weight (rate p.2) (hr p.2) (ht p.2) q p.1 (hbound p.2 hp)
    · simp only [μ,if_neg hp,lintegral_zero_measure,zero_le]
  have hfw (H : ℝ × α → ℝ≥0∞) (h1 : ∀ p,H p ≤ 1) (hn : ∀ p,p.1 < 0 → H p=0) (p : ℝ × α) :
      H p ≤ ENNReal.ofReal (w p) :=
    causal_bounded_exponential_weight q hq (fun t => H (t,p.2))
      (fun t => h1 (t,p.2)) (fun t ht => hn (t,p.2) ht) p.1
  apply weighted_half_renewal_unique μ F G B w hFm hGm hw (hfw F hF1 hFn) (hfw G hG1 hGn)
  · intro p
    by_cases hp : p.2 ∈ D
    · dsimp only [μ]
      rw [if_pos hp,lintegral_map hFm (hm p)]
      exact hF p hp
    · simp only [μ,if_neg hp,hF0 p hp,hB0 p hp,lintegral_zero_measure,add_zero]
  · intro p
    by_cases hp : p.2 ∈ D
    · dsimp only [μ]
      rw [if_pos hp,lintegral_map hGm (hm p)]
      exact hG p hp
    · simp only [μ,if_neg hp,hG0 p hp,hB0 p hp,lintegral_zero_measure,add_zero]
  · exact hweight

end
end FiniteCopyReactor
