import proofs.DiagnosticWindows.LoadingOrder
import proofs.DiagnosticWindows.Capacity

namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

theorem scaled_step (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1)
    (c : NNReal) (hc : ∀ z, (c:ℝ)*r z ∈ Set.Icc 0 1)
    (f : Fin 6 → ℝ) (x : Fin 6) :
    (birthKernel (fun z => (c:ℝ)*r z) hc).step f x =
      (c:ℝ)*(birthKernel r hr).step f x+(1-(c:ℝ))*f x := by
  rw [birth_step,birth_step]
  ring

theorem scaled_survival {ι : Type*} [Fintype ι]
    (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1)
    (V : ι → Fin 6 → ℝ) (e : ι → ℝ)
    (hsum : ∀ x, uncalled x = ∑ i, V i x)
    (he : ∀ i x, (birthKernel r hr).step (V i) x = e i*V i x)
    (c : NNReal) (hc : ∀ z, (c:ℝ)*r z ∈ Set.Icc 0 1)
    (t : NNReal) (x : Fin 6) :
    (birthKernel (fun z => (c:ℝ)*r z) hc).poissonized t uncalled x =
      (birthKernel r hr).poissonized (c*t) uncalled x := by
  have hec (i : ι) (y : Fin 6) :
      (birthKernel (fun z => (c:ℝ)*r z) hc).step (V i) y =
        ((c:ℝ)*(e i-1)+1)*V i y := by
    rw [scaled_step r hr c hc,he]
    ring
  rw [spectral_survival _ _ V _ hsum hec,spectral_survival _ _ V e hsum he]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  simp only [NNReal.coe_mul]
  ring

theorem scaled10_loading (c : NNReal)
    (hc : ∀ z, (c:ℝ)*rates10 z ∈ Set.Icc 0 1) (load t : NNReal) :
    loadedSurvival (birthKernel (fun z => (c:ℝ)*rates10 z) hc) load t =
      loadedSurvival kernel10 load (c*t) := by
  unfold loadedSurvival
  congr 1
  funext n
  rw [scaled_survival rates10 rates10_valid modes10 eigen10 capacity10_sum capacity10_eigen]
  rfl

/-- Scaling a physical clock cannot create a feasible continuous deadline. -/
theorem clock_feasibility_iff (F M : NNReal → ℝ) (c : NNReal) (hc : c ≠ 0) :
    (∃ t, F (c*t) ≤ 1/100 ∧ M (c*t) ≤ 1/20) ↔
      (∃ t, F t ≤ 1/100 ∧ M t ≤ 1/20) := by
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨c*t,ht⟩
  · rintro ⟨t,ht⟩
    refine ⟨t/c,?_⟩
    simpa [mul_div_cancel₀ _ hc] using ht

end DiagnosticWindows
