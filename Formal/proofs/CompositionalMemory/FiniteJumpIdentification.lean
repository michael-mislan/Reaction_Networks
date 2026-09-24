import proofs.CompositionalMemory.PhysicalDeadlineCommonClock
import proofs.CompositionalMemory.FiniteKernelRenewal
import proofs.CompositionalMemory.SafeClockCausal
import proofs.CompositionalMemory.UniformizeENNReal

namespace CompositionalMemory
open Classical RandomViability FiniteCopy MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000
attribute [local irreducible] physicalSafeDeadline
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem finite_common_clock_unique (P : FiniteKernel α) (q : ℝ) (hq : 0 < q) (D : Set α)
    (f : α → ℝ≥0∞) (F G : α × ℝ → ℝ≥0∞) (hFm : Measurable F) (hGm : Measurable G)
    (hFb : ∀ p,F p ≤ 1) (hGb : ∀ p,G p ≤ 1)
    (hFn : ∀ p,p.2 < 0 → F p=0) (hGn : ∀ p,p.2 < 0 → G p=0)
    (hFo : ∀ p,p.1 ∉ D → F p=0) (hGo : ∀ p,p.1 ∉ D → G p=0)
    (hFe : ∀ x,x ∈ D → ∀ T,F (x,T)=causalExp q T*f x+
      renewalConv (causalExp q) (fun t => ENNReal.ofReal q*∑ y,ENNReal.ofReal (P.prob x y)*F (y,t)) T)
    (hGe : ∀ x,x ∈ D → ∀ T,G (x,T)=causalExp q T*f x+
      renewalConv (causalExp q) (fun t => ENNReal.ofReal q*∑ y,ENNReal.ofReal (P.prob x y)*G (y,t)) T) : F=G := by
  let B : α × ℝ → ℝ≥0∞ := fun p => if p.1 ∈ D then causalExp q p.2*f p.1 else 0
  have he (J : α × ℝ → ℝ≥0∞) (hJm : Measurable J)
      (hJn : ∀ p,p.2 < 0 → J p=0) (hJo : ∀ p,p.1 ∉ D → J p=0)
      (hJe : ∀ x,x ∈ D → ∀ T,J (x,T)=causalExp q T*f x+
        renewalConv (causalExp q) (fun t => ENNReal.ofReal q*∑ y,ENNReal.ofReal (P.prob x y)*J (y,t)) T)
      (p : α × ℝ) : J p=B p+∫⁻ y,J y ∂clockRenewalMeasure (clockStatePMF P) q D p := by
    rcases p with ⟨x,T⟩
    by_cases hx : x ∈ D
    · by_cases hT : 0 ≤ T
      · rw [finiteClockRenewal_future P q hq D J hJm x T hx hT]
        simpa only [B,if_pos hx] using hJe x hx T
      · rw [hJn (x,T) (lt_of_not_ge hT)]
        simp [B,hx,causalExp,hT,clockRenewalMeasure]
    · rw [hJo (x,T) hx]
      simp [B,hx,clockRenewalMeasure]
  exact clock_renewal_unique (clockStatePMF P) q hq D F G B hFm hGm hFb hGb hFn hGn
    (he F hFm hFn hFo hFe) (he G hGm hGn hGo hGe)

variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq α]

/-- Exact identification of an actual exponential-jump safe-history payoff with uniformization. -/
theorem finite_jump_uniformization_identification (M : FiniteJumpModel α β)
    (ht : ∀ x,0 < ∑ b,M.rate x b) (q : ℝ) (hq : 0 < q) (hbound : ∀ x,M.total x ≤ q)
    (D : Set α) (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (x : α) (T : ℝ) :
    physicalSafeDeadline M.next M.rate M.nonneg ht D f x T =
      causalSafeClock (M.uniformize q hq hbound) D f q T x := by
  let P := M.uniformize q hq hbound
  let F : α × ℝ → ℝ≥0∞ := fun p => physicalSafeDeadline M.next M.rate M.nonneg ht D f p.1 p.2
  let G : α × ℝ → ℝ≥0∞ := fun p => causalSafeClock P D f q p.2 p.1
  have hFe (y : α) (hy : y ∈ D) (t : ℝ) : F (y,t)=causalExp q t*f y+
      renewalConv (causalExp q) (fun u => ENNReal.ofReal q*∑ z,ENNReal.ofReal (P.prob y z)*F (z,u)) t := by
    have hh := physicalSafeDeadline_common_clock M.next M.rate M.nonneg ht D f y hy q (hbound y) t
    dsimp only [F,P]
    rw [hh]
    congr 1
    apply congrArg (fun H => renewalConv (causalExp q) H t)
    funext u
    rw [uniformize_ennreal_step M q hq hbound]
    exact add_comm _ _
  have hEq : F=G := finite_common_clock_unique P q hq D f F G
    (physicalSafeDeadline_measurable M.next M.rate M.nonneg ht D f)
    (causalSafeClock_measurable P D f q)
    (fun p => physicalSafeDeadline_le_one M.next M.rate M.nonneg ht D f hf p.1 p.2)
    (fun p => causalSafeClock_le_one P D f hf ⟨q,hq.le⟩ p.2 p.1)
    (fun p hp => physicalSafeDeadline_outside M.next M.rate M.nonneg ht D f p.1 p.2
      (fun h => (not_le.mpr hp) h.2))
    (fun p hp => causalSafeClock_negative P D f q p.2 hp p.1)
    (fun p hp => physicalSafeDeadline_outside M.next M.rate M.nonneg ht D f p.1 p.2 (fun h => hp h.1))
    (fun p hp => causalSafeClock_outside P D f q hq.le p.2 p.1 hp)
    hFe (fun y hy t => causalSafeClock_causal_all P D f q hq.le t y hy)
  exact congrFun hEq (x,T)

end
end CompositionalMemory
