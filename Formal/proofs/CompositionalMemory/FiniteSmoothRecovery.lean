import proofs.CompositionalMemory.FiniteTimeDependentCertificate
import proofs.CompositionalMemory.SmoothQuadraticCap

namespace CompositionalMemory
open FiniteCopy HeritableCompositions Set

theorem finite_time_expectation_mono {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (T : NNReal) (f g : α → ℝ)
    (hfg : ∀ y, f y ≤ g y) (x : α) :
    finiteTimeExpectation M T f x ≤ finiteTimeExpectation M T g x := by
  obtain ⟨q,hq,_,hb⟩ := M.exists_clock 0
  rw [finite_time_eq_uniformized M q T hq hb,finite_time_eq_uniformized M q T hq hb]
  exact poisson_mono (M.uniformize q hq hb) (q*T) f g hfg x

/-- An actual finite-time failure bound from a local recovery energy.
The energy may be a higher power of a quadratic form. Outside its unit tube,
the concave cap controls the generator without a global stability premise. -/
theorem finite_smooth_recovery_bound {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (T : NNReal)
    (E dE : ℝ → α → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hE : ∀ t ∈ Icc (0 : ℝ) T, ∀ y, 0 ≤ E t y)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, ∀ y, HasDerivAt (fun u => E u y) (dE t y) t)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, ∀ y, E t y ≤ 1 → dE t y+M.generator (E t) y ≤ c)
    (failure : α → ℝ) (hfailure : ∀ y, failure y ≤ smoothQuadraticCap (E T y)) (x : α) :
    finiteTimeExpectation M T failure x ≤ smoothQuadraticCap (E 0 x)+2*(T : ℝ)*c := by
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (y : α) :
      HasDerivAt (fun u => smoothQuadraticCap (E u y))
        (smoothQuadraticSlope (E t y)*dE t y) t := by
    simpa only [Function.comp_def] using
      (hasDerivAt_smoothQuadraticCap (E t y)).comp t (hd t ht y)
  have hgen (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (y : α) :
      smoothQuadraticSlope (E t y)*dE t y+
        M.generator (fun z => smoothQuadraticCap (E t z)) y ≤ 2*c :=
    smoothQuadraticCap_local_to_global M (E t) (dE t) c hc (hE t ht) (hg t ht) y
  have hh := finite_time_dependent_drift_bound M T
    (fun t y => smoothQuadraticCap (E t y))
    (fun t y => smoothQuadraticSlope (E t y)*dE t y) (2*c) hder hgen x
  have hm := finite_time_expectation_mono M T failure (fun y => smoothQuadraticCap (E T y)) hfailure x
  nlinarith only [hh,hm]

end CompositionalMemory
