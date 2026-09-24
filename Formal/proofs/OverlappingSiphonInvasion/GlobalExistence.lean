import proofs.OverlappingSiphonInvasion.TrajectoryBounds
import proofs.CoreCouplingCAC.GlobalExistence
import proofs.CoreCouplingGlobal.ScalarBarrier

noncomputable section
namespace OverlappingSiphonInvasion
open CoreCouplingCAC CoreCouplingGlobal

def positivePart (x : State) : State := fun i => max 0 (x i)

theorem positivePart_lipschitz : LipschitzWith 1 positivePart := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0 ≤ dist x y)).2
  intro i
  calc
    dist (positivePart x i) (positivePart y i) ≤ dist (x i) (y i) := by
      simpa only [positivePart,id_eq,NNReal.coe_one,one_mul] using
        ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max 0).dist_le_mul (x i) (y i)
    _ ≤ dist x y := dist_le_pi_dist x y i

theorem witness_contDiff : ContDiff ℝ 1 (field (witness 1)) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [field,witness] <;> fun_prop

theorem extension_solution (R : ℝ) (hR : 0 < R) (x₀ : State) :
    ∃ q : State → ℝ, ∃ X : ℝ → State,
      (∀ x, 0 ≤ q x ∧ q x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → q x = 1) ∧
      X 0 = x₀ ∧ ∀ t, HasDerivAt X
        (q (positivePart (X t)) • field (witness 1) (positivePart (X t))) t := by
  let q : ContDiffBump (0 : State) := ⟨R,2*R,hR,by linarith⟩
  let f : State → State := fun x => q x • field (witness 1) x
  have hs : HasCompactSupport f := q.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := q.contDiff.smul witness_contDiff
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (positivePart x)) := by
    simpa only [mul_one] using hK.comp positivePart_lipschitz
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (positivePart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) x₀
  refine ⟨q,X,(fun _ => ⟨q.nonneg,q.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact q.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem witness_boundary_nonneg (x : State) (hx : ∀ i, 0 ≤ x i)
    (i : Fin 4) (hi : x i = 0) : 0 ≤ field (witness 1) x i := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  fin_cases i
  · change x 0 = 0 at hi
    simp [field,witness,hi]
  · change x 1 = 0 at hi
    simp [field,witness,hi]
    positivity
  · change x 2 = 0 at hi
    simp [field,witness,hi]
    positivity
  · change x 3 = 0 at hi
    simp [field,witness,hi]
    positivity

theorem witness_linear_lower (R : ℝ) (hR : 0 ≤ R) (x : State)
    (hx : ∀ i, 0 ≤ x i) (hu : ∀ i, x i ≤ R) (i : Fin 4) :
    -(1+6*R)*x i ≤ field (witness 1) x i := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have u0 := hu 0
  have u1 := hu 1
  have u2 := hu 2
  have u3 := hu 3
  fin_cases i
  · simp [field,witness]
    have hm := mul_le_mul_of_nonneg_left
      (show 1+2*x 1+x 2+(1+1/10+1)*x 3 ≤ 1+6*R by linarith) h0
    nlinarith
  · simp [field,witness]
    have hm := mul_nonneg h1 (show 0 ≤ 6*R-x 2/10-x 3/10 by linarith)
    nlinarith [mul_nonneg h0 h1,mul_nonneg h0 h3]
  · simp [field,witness]
    have hm := mul_nonneg h2 (show 0 ≤ 6*R-x 1/10-x 3/10 by linarith)
    nlinarith [mul_nonneg h0 h2,mul_nonneg h0 h3]
  · simp [field,witness]
    nlinarith [mul_nonneg h1 h2,mul_nonneg h3 h1,mul_nonneg h3 h2,
      mul_nonneg h3 h0,mul_nonneg hR h3]

/-- Positive global solutions of the actual polynomial source from every
strictly positive initial condition. The cutoff is proved inactive. -/
theorem witness_positive_global (x₀ : State) (hx₀ : ∀ i, 0 < x₀ i) :
    ∃ X : ℝ → State, X 0 = x₀ ∧ IsTrajectory (witness 1) X := by
  let R := max (total x₀) 4
  have hR : 4 ≤ R := le_max_right _ _
  obtain ⟨q,X,hq,hqone,hX0,hXd⟩ := extension_solution R (by linarith) x₀
  have hinit : ∀ i, 0 < X 0 i := by simpa only [hX0] using hx₀
  have hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i := by
    intro t ht i
    apply scalar_lower_barrier (fun t => X t i)
      (fun t => q (positivePart (X t))*field (witness 1) (positivePart (X t)) i) 0
      (fun t _ => (hasDerivAt_pi.1 (hXd t)) i) (hinit i).le ?_ t ht
    intro s _ hs
    apply mul_nonneg (hq _).1
    apply witness_boundary_nonneg _ (fun j => le_max_left 0 (X s j)) i
    exact max_eq_left hs
  have hpart : ∀ t, 0 ≤ t → positivePart (X t) = X t := by
    intro t ht
    funext i
    exact max_eq_right (hnonneg t ht i)
  have hscaled : ∀ t, 0 ≤ t → HasDerivAt X (q (X t) • field (witness 1) (X t)) t := by
    intro t ht
    simpa only [hpart t ht] using hXd t
  have htotal : ∀ t, 0 ≤ t → total (X t) ≤ R := by
    apply scalar_upper_barrier (fun t => total (X t))
      (fun t => q (X t)*(4-total (X t))) R
    · intro t ht
      have hd := hasDerivAt_pi.1 (hscaled t ht)
      convert (((hd 0).add (hd 1)).add (hd 2)).add (hd 3) using 1
      simp only [Pi.smul_apply,smul_eq_mul]
      rw [← mul_add,← mul_add,← mul_add,total_field]
      simp only [witness,total,one_mul]
      ring
    · rw [hX0]
      exact le_max_left _ _
    · intro t _ ht
      exact mul_nonpos_of_nonneg_of_nonpos (hq _).1 (by linarith)
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
    apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R)).2
    intro i
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hnonneg t ht i)] using hupper t ht i
  have hd : ∀ t, 0 ≤ t → HasDerivAt X (field (witness 1) (X t)) t := by
    intro t ht
    simpa only [hqone _ (hnorm t ht),one_smul] using hscaled t ht
  refine ⟨X,hX0,?_,fun t ht => hasDerivAt_pi.1 (hd t ht)⟩
  intro t ht i
  exact positive_of_linear_lower (fun t => X t i) (fun t => field (witness 1) (X t) i)
    (1+6*R) (fun s hs => hasDerivAt_pi.1 (hd s hs) i) (hinit i)
    (fun s hs => witness_linear_lower R (by linarith) (X s) (hnonneg s hs) (hupper s hs) i) t ht

end OverlappingSiphonInvasion
