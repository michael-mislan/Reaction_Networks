import proofs.CompositionalMemory.CanonicalFiniteLaw
import proofs.HeritableCompositions.KernelComposition
import proofs.FiniteCopy.UniformizedBounds

namespace CompositionalMemory
open FiniteCopy HeritableCompositions
set_option maxHeartbeats 30000

/-- A backward subsolution is below its actual finite-time expectation.
The function may take negative values, as residual corrections often do. -/
theorem finite_time_subsolution {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (t : NNReal) (v : α → ℝ)
    (hv : ∀ x, 0 ≤ M.generator v x) (x : α) :
    v x ≤ finiteTimeExpectation M t v x := by
  obtain ⟨q,hq,_,hb⟩ := M.exists_clock 0
  rw [finite_time_eq_uniformized M q t hq hb]
  let P := M.uniformize q hq hb
  have hs (y) : v y ≤ P.step v y := by
    rw [FiniteJumpModel.uniformize_step]
    exact le_add_of_nonneg_right (div_nonneg (hv y) hq.le)
  have hn (n : ℕ) (y : α) : v y ≤ P.steps n v y := by
    induction n generalizing y with
    | zero => rfl
    | succ n ih => exact (hs y).trans (P.step_mono ih y)
  have hh := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (hn n x) (poissonWeight_nonneg (q*t) n))
    ((poissonWeight_sum (q*t)).mul_right (v x)).summable
    (poisson_summable P (q*t) v x)
  simpa only [((poissonWeight_sum (q*t)).mul_right (v x)).tsum_eq, one_mul] using hh

/-- Concrete generator inequalities suffice for a deadline reward bound.
For an absorbing division model, `h` is the complementary-daughter terminal
payoff, `v` the corrected backward solution, and `w` the killed time witness.
No stochastic bound or backward-equation identification is assumed here. -/
theorem finite_deadline_certificate {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (t : NNReal)
    (h v w : α → ℝ) (s : ℝ)
    (hv : ∀ x, 0 ≤ M.generator v x)
    (hw : ∀ x, 0 ≤ w x)
    (hdecay : ∀ x, M.generator w x ≤ -s*w x)
    (hcover : ∀ x, v x ≤ h x+w x) (x : α) :
    v x-Real.exp (-s*(t : ℝ))*w x ≤ finiteTimeExpectation M t h x := by
  obtain ⟨q,hq,hsq,hb⟩ := M.exists_clock s
  have hl := finite_time_subsolution M t v hv x
  rw [finite_time_eq_uniformized M q t hq hb] at hl ⊢
  have hm := poisson_mono (M.uniformize q hq hb) (q*t) v
    (fun y => h y+w y) hcover x
  rw [poisson_additive] at hm
  have hd := M.uniformized_decay_bound q t hq hb w hw s hsq hdecay x
  linarith

/-- A signed finite observable obeys its generator drift bound over actual time. -/
theorem finite_time_drift_signed {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (t : NNReal) (v : α → ℝ)
    (b : ℝ) (hv : ∀ x, M.generator v x ≤ b) (x : α) :
    finiteTimeExpectation M t v x ≤ v x+(t : ℝ)*b := by
  obtain ⟨q,hq,_,hb⟩ := M.exists_clock 0
  rw [finite_time_eq_uniformized M q t hq hb]
  let P := M.uniformize q hq hb
  have hn := P.steps_drift_bound v (b/(q : ℝ))
    (M.uniformize_drift q hq hb v b hv)
  have hs : HasSum (fun n => poissonWeight (q*t) n*(v x+(n : ℝ)*(b/(q : ℝ))))
      (v x+((q*t : NNReal) : ℝ)*(b/(q : ℝ))) := by
    convert (((poissonWeight_sum (q*t)).mul_right (v x)).add
      ((poissonWeight_mean (q*t)).mul_right (b/(q : ℝ)))) using 1
    · funext n; ring
    · ring
  have hh := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (hn n x) (poissonWeight_nonneg (q*t) n))
    (poisson_summable P (q*t) v x) hs.summable
  rw [hs.tsum_eq] at hh
  have he : ((q*t : NNReal) : ℝ)*(b/(q : ℝ))=(t : ℝ)*b := by
    rw [NNReal.coe_mul]; field_simp
  simpa only [he] using hh

/-- Signed version of exponential decay, needed to subtract an affine offset. -/
theorem finite_time_decay_signed {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (t : NNReal) (w : α → ℝ)
    (s : ℝ) (hw : ∀ x, M.generator w x ≤ -s*w x) (x : α) :
    finiteTimeExpectation M t w x ≤ Real.exp (-s*(t : ℝ))*w x := by
  obtain ⟨q,hq,hsq,hb⟩ := M.exists_clock s
  rw [finite_time_eq_uniformized M q t hq hb]
  let P := M.uniformize q hq hb
  let r : ℝ := 1-s/(q : ℝ)
  have hr : 0 ≤ r := sub_nonneg.mpr ((div_le_one hq).mpr hsq)
  have hn := P.steps_decay_bound w r hr (M.uniformize_decay q hq hb w s hw)
  have hs : HasSum (fun n => poissonWeight (q*t) n*(r^n*w x))
      (Real.exp (((q*t : NNReal) : ℝ)*(r-1))*w x) := by
    convert (poissonWeight_geometric (q*t) r).mul_right (w x) using 1
    funext n; ring
  have hh := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (hn n x) (poissonWeight_nonneg (q*t) n))
    (poisson_summable P (q*t) w x) hs.summable
  rw [hs.tsum_eq] at hh
  have he : ((q*t : NNReal) : ℝ)*(r-1)=-s*(t : ℝ) := by
    dsimp [r]; field_simp; ring
  simpa only [he] using hh

/-- Direct fixed-deadline residual certificate. It avoids accumulation of
layerwise inverse norms: the reward residual costs only `epsilon * time`. -/
theorem finite_deadline_residual_certificate {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (t : NNReal)
    (h v w : α → ℝ) (s ε η : ℝ) (hs : 0 < s) (hη : 0 ≤ η)
    (hv : ∀ x, -ε ≤ M.generator v x)
    (hw : ∀ x, M.generator w x ≤ -s*w x+η)
    (hcover : ∀ x, v x ≤ h x+w x) (x : α) :
    v x-(t : ℝ)*ε-Real.exp (-s*(t : ℝ))*w x-η/s ≤
      finiteTimeExpectation M t h x := by
  have hneg (y) : M.generator (fun z => -v z) y = -M.generator v y := by
    simp only [FiniteJumpModel.generator, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro z _; ring
  have hl := finite_time_drift_signed M t (fun z => -v z) ε
    (fun y => by rw [hneg]; linarith [hv y]) x
  have hEn : finiteTimeExpectation M t (fun z => -v z) x =
      -finiteTimeExpectation M t v x := by
    simp [finiteTimeExpectation, Matrix.mulVec, dotProduct]
  rw [hEn] at hl
  let c := η/s
  have hc : 0 ≤ c := div_nonneg hη hs.le
  have hsc : s*c=η := by dsimp [c]; field_simp
  have hshift (y) : M.generator (fun z => w z-c) y = M.generator w y := by
    simp only [FiniteJumpModel.generator]
    apply Finset.sum_congr rfl; intro z _; ring
  have hd := finite_time_decay_signed M t (fun z => w z-c) s
    (fun y => by rw [hshift]; nlinarith [hw y,hsc]) x
  obtain ⟨q,hq,_,hb⟩ := M.exists_clock 0
  have hEs : finiteTimeExpectation M t (fun z => w z-c) x =
      finiteTimeExpectation M t w x-c := by
    rw [finite_time_eq_uniformized M q t hq hb,
      finite_time_eq_uniformized M q t hq hb]
    change (M.uniformize q hq hb).poissonized (q*t) (fun z => w z+(-c)) x = _
    rw [poisson_additive,poisson_constant]; ring
  rw [hEs] at hd
  have hm := poisson_mono (M.uniformize q hq hb) (q*t) v
    (fun z => h z+w z) hcover x
  rw [poisson_additive] at hm
  rw [← finite_time_eq_uniformized M q t hq hb,
    ← finite_time_eq_uniformized M q t hq hb,
    ← finite_time_eq_uniformized M q t hq hb] at hm
  have hp := mul_nonneg (Real.exp_pos (-s*(t : ℝ))).le hc
  change _-c ≤ _
  nlinarith only [hl,hd,hm,hp]

/-- A small exact Taylor certificate supplies the only transcendental constant
needed at deadline20 and tilt5/8. -/
theorem wide_deadline_exp_bound : Real.exp (-(25/2 : ℝ)) ≤ 1/250000 := by
  have ht := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 25/2 by norm_num) 20
  have hb : (250000 : ℝ) ≤ ∑ i ∈ Finset.range 20, (25/2 : ℝ)^i/(i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have he := hb.trans ht
  rw [Real.exp_neg]
  simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num) he)

/-- The concrete integer birth inequality leaves a uniform991/1000 reward
bound once its literal finite generator inequalities are supplied. -/
theorem wide_deadline_from_generator {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (h v w : α → ℝ)
    (hv : ∀ x, -(1/10000 : ℝ) ≤ M.generator v x)
    (hw : ∀ x, M.generator w x ≤ -(5/8 : ℝ)*w x+1/4000)
    (hcover : ∀ x, v x ≤ h x+w x) (x : α) (hwx : 0 ≤ w x)
    (hbirth : (248350 : ℝ) ≤ 250000*v x-w x) :
    (991/1000 : ℝ) ≤ finiteTimeExpectation M 20 h x := by
  have hh := finite_deadline_residual_certificate M 20 h v w (5/8) (1/10000)
    (1/4000) (by norm_num) (by norm_num) hv hw hcover x
  norm_num at hh
  have ht := mul_le_mul_of_nonneg_right wide_deadline_exp_bound hwx
  nlinarith only [hh,ht,hbirth]

end CompositionalMemory
