import proofs.ProductiveMemory.ExtractionEndpoint
import proofs.FiniteCopy.KernelExpectations

namespace ProductiveMemory
open FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

theorem low_extraction_terminal_bound (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : 480*100000000 ≤ (N:ℝ)*readyLevel)
    (q : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (extractionStoppedModel rho (by linarith [hr.1]) N (lowExtractionWell rho z N outerLevel)).total s ≤ q)
    (hk : (N:ℝ)*localAlpha*readyLevel/480 ≤ q)
    (n : {n : Counts // n ∈ lowExtractionWell rho z N outerLevel})
    (hbirth : lowExtractionEnergy (fun i => concentration N n.val i-lift rho z i) ≤ 8*readyLevel) :
    ((extractionStoppedModel rho (by linarith [hr.1]) N (lowExtractionWell rho z N outerLevel)).uniformize q hq hclock).poissonized (q*5376)
      (FiniteKernel.eventIndicator (terminalUnready N (lowExtractionWell rho z N outerLevel) (lift rho z) lowExtractionEnergy)) (some n) ≤
      Real.exp (-((N:ℝ)*localAlpha*readyLevel))+2*Real.exp (-((N:ℝ)*localAlpha*readyLevel)/2) := by
  classical
  let u := (N:ℝ)*localAlpha*readyLevel
  let s := lift rho z
  let D := lowExtractionWell rho z N outerLevel
  let f := energyExponential lowExtractionEnergy N s
  have hu : 0 ≤ u := by dsimp [u,localAlpha,readyLevel,outerLevel]; positivity
  have hG (m : Counts) (hm : m ∈ D) : countGenerator rho N f (concentration N m) ≤
      -(u/480)*f (concentration N m)+(u/480)*(2*Real.exp (u/2)) := by
    have hmem := (mem_energyDomain N hN m s (low_extraction_root_upper rho z hr hz)
      lowExtractionEnergy lowExtractionEnergy_lower outerLevel (by norm_num [outerLevel])).mp hm
    let y : Point := fun i => concentration N m i-s i
    have hy := small_energy_coordinates lowExtractionEnergy lowExtractionEnergy_lower y hmem
    exact (low_count_generator rho z hr hz he N hN m hy (low_extraction_root_upper rho z hr hz)).trans
      (extraction_affine_envelope (N:ℝ) (normSq y) (lowExtractionEnergy y) readyLevel
        (Nat.cast_nonneg N) (normSq_nonneg y) (by norm_num [readyLevel,outerLevel])
        (lowExtractionEnergy_upper y) hlarge)
  have hA : ∀ x ∈ terminalUnready N D s lowExtractionEnergy, Real.exp u ≤ extractionStoppedObservable N D f 0 x := by
    intro x hx
    cases x with
    | none => exact False.elim hx
    | some x =>
      change readyLevel < lowExtractionEnergy (fun i => concentration N x.val i-s i) at hx
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hx.le (by unfold localAlpha; positivity)
  have h := extraction_affine_event rho (by linarith [hr.1]) N D f (fun _ => (Real.exp_pos _).le)
    (u/480) (2*Real.exp (u/2)) (by positivity) (by positivity) hG q 5376 hq hclock hk
    (terminalUnready N D s lowExtractionEnergy) (Real.exp u) hA n
  have ht : -(u/480)*(5376:NNReal) = -(56/5)*u := by norm_num; ring
  rw [ht] at h
  apply terminal_exponential_tail u _ (f (concentration N n.val)) hu _ h
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hbirth (by unfold localAlpha; positivity : 0 ≤ (N:ℝ)*localAlpha)
  dsimp [u]
  nlinarith only [hh]

theorem high_extraction_terminal_bound (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : 480*100000000 ≤ (N:ℝ)*readyLevel)
    (q : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (extractionStoppedModel rho (by linarith [hr.1]) N (highExtractionWell rho z N outerLevel)).total s ≤ q)
    (hk : (N:ℝ)*localAlpha*readyLevel/480 ≤ q)
    (n : {n : Counts // n ∈ highExtractionWell rho z N outerLevel})
    (hbirth : highExtractionEnergy (fun i => concentration N n.val i-lift rho z i) ≤ 8*readyLevel) :
    ((extractionStoppedModel rho (by linarith [hr.1]) N (highExtractionWell rho z N outerLevel)).uniformize q hq hclock).poissonized (q*5376)
      (FiniteKernel.eventIndicator (terminalUnready N (highExtractionWell rho z N outerLevel) (lift rho z) highExtractionEnergy)) (some n) ≤
      Real.exp (-((N:ℝ)*localAlpha*readyLevel))+2*Real.exp (-((N:ℝ)*localAlpha*readyLevel)/2) := by
  classical
  let u := (N:ℝ)*localAlpha*readyLevel
  let s := lift rho z
  let D := highExtractionWell rho z N outerLevel
  let f := energyExponential highExtractionEnergy N s
  have hu : 0 ≤ u := by dsimp [u,localAlpha,readyLevel,outerLevel]; positivity
  have hG (m : Counts) (hm : m ∈ D) : countGenerator rho N f (concentration N m) ≤
      -(u/480)*f (concentration N m)+(u/480)*(2*Real.exp (u/2)) := by
    have hmem := (mem_energyDomain N hN m s (high_extraction_root_upper rho z hr hz)
      highExtractionEnergy highExtractionEnergy_lower outerLevel (by norm_num [outerLevel])).mp hm
    let y : Point := fun i => concentration N m i-s i
    have hy := small_energy_coordinates highExtractionEnergy highExtractionEnergy_lower y hmem
    exact (high_count_generator rho z hr hz he N hN m hy (high_extraction_root_upper rho z hr hz)).trans
      (extraction_affine_envelope (N:ℝ) (normSq y) (highExtractionEnergy y) readyLevel
        (Nat.cast_nonneg N) (normSq_nonneg y) (by norm_num [readyLevel,outerLevel])
        (highExtractionEnergy_upper y) hlarge)
  have hA : ∀ x ∈ terminalUnready N D s highExtractionEnergy, Real.exp u ≤ extractionStoppedObservable N D f 0 x := by
    intro x hx
    cases x with
    | none => exact False.elim hx
    | some x =>
      change readyLevel < highExtractionEnergy (fun i => concentration N x.val i-s i) at hx
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hx.le (by unfold localAlpha; positivity)
  have h := extraction_affine_event rho (by linarith [hr.1]) N D f (fun _ => (Real.exp_pos _).le)
    (u/480) (2*Real.exp (u/2)) (by positivity) (by positivity) hG q 5376 hq hclock hk
    (terminalUnready N D s highExtractionEnergy) (Real.exp u) hA n
  have ht : -(u/480)*(5376:NNReal) = -(56/5)*u := by norm_num; ring
  rw [ht] at h
  apply terminal_exponential_tail u _ (f (concentration N n.val)) hu _ h
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hbirth (by unfold localAlpha; positivity : 0 ≤ (N:ℝ)*localAlpha)
  dsimp [u]
  nlinarith only [hh]

end
end ProductiveMemory
