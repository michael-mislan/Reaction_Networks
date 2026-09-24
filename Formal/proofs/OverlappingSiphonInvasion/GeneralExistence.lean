import proofs.OverlappingSiphonInvasion.GeneralSourceBounds
import proofs.OverlappingSiphonInvasion.GlobalExistence

noncomputable section
open CoreCouplingCAC CoreCouplingGlobal
open Filter Topology
namespace OverlappingSiphonInvasion

theorem field_contDiff (p : Rates) : ContDiff ℝ 1 (field p) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [field] <;> fun_prop

theorem general_extension_solution (p : Rates) (R : ℝ) (hR : 0 < R) (x₀ : State) :
    ∃ q : State → ℝ, ∃ X : ℝ → State,
      (∀ x, 0 ≤ q x ∧ q x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → q x = 1) ∧
      X 0 = x₀ ∧ ∀ t, HasDerivAt X
        (q (positivePart (X t)) • field p (positivePart (X t))) t := by
  let q : ContDiffBump (0 : State) := ⟨R,2*R,hR,by linarith⟩
  let f : State → State := fun x => q x • field p x
  have hs : HasCompactSupport f := q.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := q.contDiff.smul (field_contDiff p)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (positivePart x)) := by
    simpa only [mul_one] using hK.comp positivePart_lipschitz
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (positivePart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) x₀
  refine ⟨q,X,(fun _ => ⟨q.nonneg,q.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact q.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

def sourceRadius (p : Rates) (x₀ : State) : ℝ :=
  max (total x₀) (p.recruitment/deathFloor p+1)

/-- Nonnegative global solutions, including every resident boundary face. The
cutoff is proved inactive using the source mortality balance. -/
theorem general_nonnegative_global (p : Rates) (hp : PositiveRates p)
    (x₀ : State) (hx₀ : ∀ i, 0 ≤ x₀ i) :
    ∃ X : ℝ → State, X 0 = x₀ ∧
      (∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i) ∧
      (∀ t, 0 ≤ t → total (X t) ≤ sourceRadius p x₀) ∧
      (∀ t, 0 ≤ t → HasDerivAt X (field p (X t)) t) := by
  let R := sourceRadius p x₀
  have hm := deathFloor_pos p hp
  have hΛ : 0 < p.recruitment := by simpa [rateVector] using hp 0
  have hR : p.recruitment/deathFloor p+1 ≤ R := le_max_right _ _
  have hR0 : 0 < R := (by positivity : 0 < p.recruitment/deathFloor p+1).trans_le hR
  obtain ⟨q,X,hq,hqone,hX0,hXd⟩ := general_extension_solution p R hR0 x₀
  have hinit : ∀ i, 0 ≤ X 0 i := by simpa only [hX0] using hx₀
  have hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i := by
    intro t ht i
    apply scalar_lower_barrier (fun t => X t i)
      (fun t => q (positivePart (X t))*field p (positivePart (X t)) i) 0
      (fun t _ => (hasDerivAt_pi.1 (hXd t)) i) (hinit i) ?_ t ht
    intro s _ hs
    apply mul_nonneg (hq _).1
    apply field_boundary_nonneg p hp _ (fun j => le_max_left 0 (X s j)) i
    exact max_eq_left hs
  have hpart : ∀ t, 0 ≤ t → positivePart (X t) = X t := by
    intro t ht
    funext i
    exact max_eq_right (hnonneg t ht i)
  have hscaled : ∀ t, 0 ≤ t → HasDerivAt X (q (X t) • field p (X t)) t := by
    intro t ht
    simpa only [hpart t ht] using hXd t
  have htotal : ∀ t, 0 ≤ t → total (X t) ≤ R := by
    apply scalar_upper_barrier (fun t => total (X t))
      (fun t => q (X t)*(p.recruitment-p.mu0*X t 0-p.mu1*X t 1-
        p.mu2*X t 2-p.mu3*X t 3)) R
    · intro t ht
      have hd := hasDerivAt_pi.1 (hscaled t ht)
      convert (((hd 0).add (hd 1)).add (hd 2)).add (hd 3) using 1
      simp only [Pi.smul_apply,smul_eq_mul]
      rw [← mul_add,← mul_add,← mul_add,total_field]
    · rw [hX0]
      exact le_max_left _ _
    · intro t ht hlevel
      apply mul_nonpos_of_nonneg_of_nonpos (hq _).1
      have hb := total_mortality_bound p (X t) (hnonneg t ht)
      have hr : p.recruitment/deathFloor p ≤ R := by linarith
      have hmR := (div_le_iff₀ hm).mp hr
      have hmN := mul_le_mul_of_nonneg_left hlevel hm.le
      nlinarith only [hb,hmR,hmN]
  have hupper : ∀ t, 0 ≤ t → ∀ i, X t i ≤ R := by
    intro t ht i
    have h0 := hnonneg t ht 0
    have h1 := hnonneg t ht 1
    have h2 := hnonneg t ht 2
    have h3 := hnonneg t ht 3
    have hn := htotal t ht
    dsimp [total] at hn
    fin_cases i <;> dsimp <;> linarith
  have hnorm : ∀ t, 0 ≤ t → ‖X t‖ ≤ R := by
    intro t ht
    apply (pi_norm_le_iff_of_nonneg hR0.le).2
    intro i
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hnonneg t ht i)] using hupper t ht i
  refine ⟨X,hX0,hnonneg,htotal,?_⟩
  intro t ht
  simpa only [hqone _ (hnorm t ht),one_smul] using hscaled t ht

theorem general_positive_global (p : Rates) (hp : PositiveRates p)
    (x₀ : State) (hx₀ : ∀ i, 0 < x₀ i) :
    ∃ X : ℝ → State, X 0 = x₀ ∧ IsTrajectory p X := by
  obtain ⟨X,hX0,hnonneg,htotal,hd⟩ := general_nonnegative_global p hp x₀ (fun i => (hx₀ i).le)
  have hupper : ∀ t, 0 ≤ t → ∀ i, X t i ≤ sourceRadius p x₀ := by
    intro t ht i
    have h0 := hnonneg t ht 0
    have h1 := hnonneg t ht 1
    have h2 := hnonneg t ht 2
    have h3 := hnonneg t ht 3
    have hn := htotal t ht
    dsimp [total] at hn
    fin_cases i <;> dsimp <;> linarith
  refine ⟨X,hX0,?_,fun t ht => hasDerivAt_pi.1 (hd t ht)⟩
  intro t ht i
  apply positive_of_linear_lower (fun t => X t i) (fun t => field p (X t) i)
    (lossBound p (sourceRadius p x₀)) (fun s hs => hasDerivAt_pi.1 (hd s hs) i)
    (by simpa only [hX0] using hx₀ i)
    (fun s hs => field_linear_lower p hp _ (X s) (hnonneg s hs) (hupper s hs) i) t ht

/-- An absorbing total-count bound uniform over positive initial states. -/
theorem general_eventual_total_upper (p : Rates) (hp : PositiveRates p)
    (X : ℝ → State) (hX : IsTrajectory p X) :
    ∀ᶠ t in atTop, total (X t) < p.recruitment/deathFloor p+1 := by
  apply eventual_upper_of_linear_drift (fun t => total (X t))
    (fun t => p.recruitment-p.mu0*X t 0-p.mu1*X t 1-p.mu2*X t 2-p.mu3*X t 3)
    0 p.recruitment (deathFloor p) (p.recruitment/deathFloor p+1)
    (deathFloor_pos p hp) (by linarith)
  · intro t ht
    convert (((hX.derivative t ht 0).add (hX.derivative t ht 1)).add
      (hX.derivative t ht 2)).add (hX.derivative t ht 3) using 1
    exact (total_field p (X t)).symm
  · intro t ht
    exact total_mortality_bound p (X t) (fun i => (hX.positive t ht i).le)

end OverlappingSiphonInvasion
