import proofs.MemoryPrediction.YulePaths
import proofs.MemoryPrediction.YulePolynomial

namespace MemoryPrediction
noncomputable section
open Classical LowFounderPrediction FiniteCopy FiniteCopyReactor CompositionalMemory
open MeasureTheory
open scoped ENNReal

def yuleObserve (s : ℕ) (x : State) : Fin 9 :=
  if h : x ∈ yuleLive s then ⟨x.2, by have := h.2; omega⟩ else 8

theorem yule_clock_bound (s : ℕ) (x : State) (hx : x ∈ yuleLive s) :
    (∑ e, rate yuleRates x e) ≤ 9 := by
  have hr : (x.2 : ℝ) ≤ 7 := by exact_mod_cast hx.2
  rw [total_eq]
  norm_num [yuleRates]
  linarith

theorem yule_finite_bound (n : Fin 9) : yuleFinite.total n ≤ 9 := by
  simp [FiniteJumpModel.total,yuleFinite]

def yuleStopped (s : ℕ) :=
  stoppedClockKernel (yuleLive s) next (rate yuleRates) (rate_nonneg yuleRates)
    9 (by norm_num) (yule_clock_bound s)

private theorem mk2 (h : 2 < 9) : (⟨2,h⟩ : Fin 9) = 2 := rfl
private theorem mk3 (h : 3 < 9) : (⟨3,h⟩ : Fin 9) = 3 := rfl
private theorem mk4 (h : 4 < 9) : (⟨4,h⟩ : Fin 9) = 4 := rfl
private theorem mk5 (h : 5 < 9) : (⟨5,h⟩ : Fin 9) = 5 := rfl
private theorem mk6 (h : 6 < 9) : (⟨6,h⟩ : Fin 9) = 6 := rfl
private theorem mk7 (h : 7 < 9) : (⟨7,h⟩ : Fin 9) = 7 := rfl
private theorem mk8 (h : 8 < 9) : (⟨8,h⟩ : Fin 9) = 8 := rfl

theorem yule_step_projection (s : ℕ) (g : Fin 9 → ℝ) (x : State) :
    (∑ e, (yuleStopped s).prob x e * g (yuleObserve s ((yuleStopped s).next x e))) =
      (yuleFinite.uniformize 9 (by norm_num) yule_finite_bound).step g (yuleObserve s x) := by
  rw [FiniteJumpModel.uniformize_step,yule_generator]
  by_cases hx : x ∈ yuleLive s
  · rcases x with ⟨u,r⟩
    have hu : u=s := hx.1
    have hr : r ≤ 7 := hx.2
    subst u
    interval_cases r <;>
      norm_num [yuleStopped,stoppedClockKernel,boundedClockKernel,stoppedRate,
        yuleLive,rate,next,yuleRates,yuleObserve,yuleNext,
        Fintype.sum_option,Fin.sum_univ_succ,mk2,mk3,mk4,mk5,mk6,mk7,mk8] <;> ring
  · simp [yuleStopped,stoppedClockKernel,boundedClockKernel,stoppedRate,hx,
      Fintype.sum_option,yuleObserve,yuleNext]

theorem yule_source_exact (s r : ℕ) (hr : r ≤ 7) (k : Fin 8) (T : NNReal) :
    (law yuleRates (s,r) T).real {y | totalCount y ≤ s+k.val} =
      yuleValue k T ⟨r, by omega⟩ := by
  let f := countSuccess (s+k.val)
  have hf : ∀ y, f y ≤ 1 := by intro y; dsimp [f,countSuccess]; split_ifs <;> norm_num
  have hp := InheritedCellAssay.clock_finite_projection (yuleStopped s) yuleFinite
    (yuleObserve s) 9 T (by norm_num) yule_finite_bound (yule_step_projection s)
    (yulePayoff k) (fun n => by unfold yulePayoff; split_ifs <;> norm_num) (s,r)
  have he : (fun y => ENNReal.ofReal (yulePayoff k (yuleObserve s y))) =
      (fun y => if y ∈ yuleLive s then f y else 0) := by
    funext y
    by_cases hy : y ∈ yuleLive s
    · have hs := hy.1
      simp [yuleObserve,hy,yulePayoff,f,countSuccess,totalCount,hs]
      split_ifs <;> norm_num
    · have hk : ¬8 ≤ k.val := by omega
      simp [yuleObserve,hy,yulePayoff,hk]
  rw [he] at hp
  have ho : yuleObserve s (s,r) = ⟨r,by omega⟩ := by
    simp [yuleObserve,yuleLive,hr]
  rw [ho,yule_finite_exact] at hp
  have hc := stopped_clock_eq_killed_chronology (yuleLive s) next (rate yuleRates)
    (rate_nonneg yuleRates) (total_pos yuleRates) 9 (by norm_num) (yule_clock_bound s)
    f hf (s,r) T
  have hce : clockEndpoint (yuleStopped s) 9 T
      (fun y => if y ∈ yuleLive s then f y else 0) (s,r) =
      chronologicalEndpoint next (rate yuleRates) (rate_nonneg yuleRates)
        (total_pos yuleRates) f (s,r) T := by
    have hk : s+k.val ≤ (s,r).1+7 := by have := k.isLt; dsimp; omega
    rw [yule_killed_exact (s,r) (s+k.val) hk T] at hc
    simpa [causalClockEndpoint,yuleStopped] using hc
  norm_num only [NNReal.coe_ofNat] at hp
  rw [hce] at hp
  rw [chronological_endpoint_measure next (rate yuleRates) (rate_nonneg yuleRates)
    (total_pos yuleRates) (s,r) T T.property (source_nonexplosion yuleRates (s,r))] at hp
  have hi : f = Set.indicator {y : State | totalCount y ≤ s+k.val} (fun _ => 1) := by
    funext y
    simp [f,countSuccess,Set.indicator]
  rw [hi,lintegral_indicator (Set.to_countable _).measurableSet] at hp
  simp only [lintegral_one,Measure.restrict_apply_univ] at hp
  have hv : 0 ≤ yuleValue k T ⟨r,by omega⟩ := by
    rw [← yule_finite_exact]
    rw [finite_time_eq_uniformized yuleFinite 9 T (by norm_num) yule_finite_bound]
    exact FiniteKernel.poissonized_nonneg _ _ _ (fun n => by unfold yulePayoff; split_ifs <;> norm_num) _
  have hrp := congrArg ENNReal.toReal hp
  rw [ENNReal.toReal_ofReal hv] at hrp
  exact hrp

end
end MemoryPrediction
