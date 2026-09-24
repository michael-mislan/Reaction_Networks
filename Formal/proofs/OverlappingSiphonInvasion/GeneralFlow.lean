import proofs.OverlappingSiphonInvasion.GeneralExistence

noncomputable section
open Set
namespace OverlappingSiphonInvasion

def populationBox (R : ℝ) : Set State := {x | (∀ i, 0 ≤ x i) ∧ total x ≤ R}

theorem nonnegative_norm_le_total (x : State) (hx : ∀ i, 0 ≤ x i) : ‖x‖ ≤ total x := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have hN : 0 ≤ total x := by dsimp [total]; positivity
  apply (pi_norm_le_iff_of_nonneg hN).2
  intro i
  rw [Real.norm_eq_abs,abs_of_nonneg (hx i)]
  fin_cases i <;> dsimp [total] <;> linarith

theorem populationBox_isCompact (R : ℝ) : IsCompact (populationBox R) := by
  have hc0 : IsClosed {x : State | ∀ i, 0 ≤ x i} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have hcN : Continuous (fun x : State => total x) := by dsimp [total]; fun_prop
  have hclosed : IsClosed (populationBox R) := hc0.inter (isClosed_le hcN continuous_const)
  apply (isCompact_closedBall (0:State) R).of_isClosed_subset hclosed
  intro x hx
  simpa only [Metric.mem_closedBall,dist_zero_right] using
    (nonnegative_norm_le_total x hx.1).trans hx.2

theorem bounded_source_dependence (p : Rates) (R : ℝ) :
    ∃ K : NNReal, ∀ X Y : ℝ → State,
      (∀ t, 0 ≤ t → HasDerivAt X (field p (X t)) t) →
      (∀ t, 0 ≤ t → HasDerivAt Y (field p (Y t)) t) →
      (∀ t, 0 ≤ t → X t ∈ populationBox R) →
      (∀ t, 0 ≤ t → Y t ∈ populationBox R) →
      ∀ t, 0 ≤ t → dist (X t) (Y t) ≤ dist (X 0) (Y 0)*Real.exp (K*t) := by
  obtain ⟨K,hK⟩ := (field_contDiff p).contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_closedBall (0:State) R)
    (isCompact_closedBall (0:State) R)
  refine ⟨K,?_⟩
  intro X Y hXd hYd hX hY t ht
  have hmX : ∀ s ∈ Ico (0:ℝ) t, X s ∈ Metric.closedBall (0:State) R := by
    intro s hs
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      (nonnegative_norm_le_total (X s) (hX s hs.1).1).trans (hX s hs.1).2
  have hmY : ∀ s ∈ Ico (0:ℝ) t, Y s ∈ Metric.closedBall (0:State) R := by
    intro s hs
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      (nonnegative_norm_le_total (Y s) (hY s hs.1).1).trans (hY s hs.1).2
  have hh := dist_le_of_trajectories_ODE_of_mem (v := fun _ => field p)
    (s := fun _ => Metric.closedBall (0:State) R) (fun _ _ => hK)
    (fun s hs => (hXd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hXd s hs.1).hasDerivWithinAt) hmX
    (fun s hs => (hYd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hYd s hs.1).hasDerivWithinAt) hmY
    (le_refl (dist (X 0) (Y 0))) t ⟨ht,le_rfl⟩
  simpa only [sub_zero] using hh

def boxFlow (p : Rates) (hp : PositiveRates p) (R : ℝ) (x : populationBox R) : ℝ → State :=
  (general_nonnegative_global p hp x x.property.1).choose

theorem boxFlow_spec (p : Rates) (hp : PositiveRates p) (R : ℝ)
    (hR : p.recruitment/deathFloor p+1 ≤ R) (x : populationBox R) :
    boxFlow p hp R x 0 = x ∧
      (∀ t, 0 ≤ t → boxFlow p hp R x t ∈ populationBox R) ∧
      (∀ t, 0 ≤ t → HasDerivAt (boxFlow p hp R x) (field p (boxFlow p hp R x t)) t) := by
  have hh := (general_nonnegative_global p hp x x.property.1).choose_spec
  refine ⟨hh.1,?_,hh.2.2.2⟩
  intro t ht
  refine ⟨hh.2.1 t ht,?_⟩
  exact (hh.2.2.1 t ht).trans (max_le x.property.2 hR)

theorem boxFlow_lipschitz (p : Rates) (hp : PositiveRates p) (R : ℝ)
    (hR : p.recruitment/deathFloor p+1 ≤ R) (t : ℝ) (ht : 0 ≤ t) :
    ∃ K : NNReal, LipschitzWith K (fun x : populationBox R => boxFlow p hp R x t) := by
  obtain ⟨K,hK⟩ := bounded_source_dependence p R
  refine ⟨⟨Real.exp (K*t),(Real.exp_pos _).le⟩,?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx := boxFlow_spec p hp R hR x
  have hy := boxFlow_spec p hp R hR y
  have hh := hK (boxFlow p hp R x) (boxFlow p hp R y) hx.2.2 hy.2.2 hx.2.1 hy.2.1 t ht
  simpa only [hx.1,hy.1,Subtype.dist_eq,mul_comm] using hh

theorem boxFlow_continuous (p : Rates) (hp : PositiveRates p) (R : ℝ)
    (hR : p.recruitment/deathFloor p+1 ≤ R) (t : ℝ) (ht : 0 ≤ t) :
    Continuous (fun x : populationBox R => boxFlow p hp R x t) :=
  (boxFlow_lipschitz p hp R hR t ht).choose_spec.continuous

end OverlappingSiphonInvasion
