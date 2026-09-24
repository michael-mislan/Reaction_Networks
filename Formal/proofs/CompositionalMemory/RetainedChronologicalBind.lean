import proofs.CompositionalMemory.RetainedChronologicalLaw
import proofs.HeritableCompositions.FiniteLaw

namespace CompositionalMemory
open Classical RandomViability FiniteCopy HeritableCompositions MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

theorem finiteLaw_bounded_expectation {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (H : α → ℝ) (hH : ∀ x,0 ≤ H x ∧ H x ≤ 1) : 0 ≤ μ.expect H ∧ μ.expect H ≤ 1 := by
  have hl := μ.expect_mono (fun _ => 0) H (fun x => (hH x).1)
  have hu := μ.expect_mono H (fun _ => 1) (fun x => (hH x).2)
  simpa only [FiniteLaw.expect_const] using And.intro hl hu

theorem product_domain_membrane_positive {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (E : Fin k → Point → ℝ) (b : ℝ)
    (s : ModularCountState k) (hs : s ∈ productDomain N center E b) : 0 < s.2 := by
  have hm : s.1 ∈ modularCountBox k (2*N) ∧ k*N ≤ s.2 ∧ s.2 ≤ 2*(k*N) := by
    have hh := (Finset.mem_filter.mp hs).1
    simpa only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc] using hh
  have hp : 0 < k*N := Nat.mul_pos (by omega) (by omega)
  omega

def liftRetainedNonneg {k : ℕ} (D : Finset (ModularCountState k)) (H : StoppedModularState D → ℝ≥0∞)
    (s : ModularCountState k) : ℝ≥0∞ := if h : s ∈ D then H (some ⟨s,h⟩) else 0

theorem liftRetainedNonneg_ofReal {k : ℕ} (D : Finset (ModularCountState k))
    (H : StoppedModularState D → ℝ) : liftRetainedNonneg D (fun s => ENNReal.ofReal (H s))=
      (fun s => ENNReal.ofReal (liftRetainedPayoff D H s)) := by
  funext s
  by_cases hs : s ∈ D <;> simp [liftRetainedNonneg,liftRetainedPayoff,hs]

/-- Any bounded recovery/partition continuation can follow the actual retained trajectory. -/
theorem retained_chronological_bind {k : ℕ} {α : Type*} [Fintype α]
    (γ : ℝ) (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j)
    (N : ℕ) (D : Finset (ModularCountState k)) (hD : ∀ s ∈ D,0 < s.2)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s,(retainedModularModel γ w hγ hw N D).total s ≤ q)
    (K : StoppedModularState D → FiniteLaw α) (H : α → ℝ)
    (hzero : (K none).expect H=0) (hH : ∀ x,0 ≤ H x ∧ H x ≤ 1)
    (x : {s : ModularCountState k // s ∈ D}) :
    physicalSafeDeadline (frozenCountNext N) (frozenCountRate γ w N)
      (frozen_count_rate_nonneg γ w hγ hw N) (frozen_count_total_positive γ w hγ hw N)
      (D : Set (ModularCountState k))
      (liftRetainedNonneg D (fun s => ENNReal.ofReal ((K s).expect H))) x.val t =
      ENNReal.ofReal (((poissonLaw ((retainedModularModel γ w hγ hw N D).uniformize q hq hclock)
        (q*t) (some x)).bind K).expect H) := by
  rw [liftRetainedNonneg_ofReal,
    retained_chronological_expectation γ w hγ hw N D hD t (fun s => (K s).expect H) hzero
      (fun s => finiteLaw_bounded_expectation (K s) H hH) x,
    FiniteLaw.expect_bind,poissonLaw_expect]
  exact congrArg ENNReal.ofReal (finite_time_eq_uniformized _ q t hq hclock _ _)

end
end CompositionalMemory
