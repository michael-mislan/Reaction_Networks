import proofs.ProductiveRecovery.Source
import proofs.CoreCouplingCAC.GlobalExistence
import proofs.CoreCouplingGlobal.ScalarBarrier

namespace ProductiveRecovery
noncomputable section
open CoreCouplingGlobal CoreCouplingCAC

def positivePart (c : State) : State := fun i => max 0 (c i)

theorem positivePart_lipschitz : LipschitzWith 1 positivePart := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0 ≤ dist x y)).2
  intro i
  calc
    dist (positivePart x i) (positivePart y i) ≤ dist (x i) (y i) := by
      have h := ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max 0).dist_le_mul (x i) (y i)
      simpa only [positivePart,id_eq,NNReal.coe_one,one_mul] using h
    _ ≤ dist x y := dist_le_pi_dist x y i

theorem field_contDiff (r d : ℝ) : ContDiff ℝ 1 (field r d) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [field,flux] <;> fun_prop

theorem boundary_nonneg (r d : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (c : State) (hc : Nonneg c) (i : Fin 6) (hi : c i = 0) :
    0 ≤ field r d c i := by
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  fin_cases i
  · change c 0 = 0 at hi
    change 0 ≤ 1-c 0-((1/500000000)*c 0*c 1-(1/5000000000)*c 2) -
      (20*c 2*c 0-20*c 3)+(d*c 2-d*(1/8000000000)*c 0*c 1)
    rw [hi]
    ring_nf
    positivity
  · change c 1 = 0 at hi
    change 0 ≤ 1-c 1-((1/500000000)*c 0*c 1-(1/5000000000)*c 2) -
      (20*c 3*c 1-20*c 4)+(d*c 2-d*(1/8000000000)*c 0*c 1)
    rw [hi]
    ring_nf
    positivity
  · change c 2 = 0 at hi
    change 0 ≤ -c 2+((1/500000000)*c 0*c 1-(1/5000000000)*c 2) -
      (20*c 2*c 0-20*c 3)+2*(r*(c 5-c 2^2))-(d*c 2-d*(1/8000000000)*c 0*c 1)
    rw [hi]
    ring_nf
    positivity
  · change c 3 = 0 at hi
    change 0 ≤ -c 3+(20*c 2*c 0-20*c 3)-(20*c 3*c 1-20*c 4)
    rw [hi]
    ring_nf
    positivity
  · change c 4 = 0 at hi
    change 0 ≤ -c 4+(20*c 3*c 1-20*c 4)-(20*c 4-2*c 5)
    rw [hi]
    ring_nf
    positivity
  · change c 5 = 0 at hi
    change 0 ≤ -c 5+(20*c 4-2*c 5)-r*(c 5-c 2^2)
    rw [hi]
    ring_nf
    positivity

theorem deriv_A (X : ℝ → State) (v : State) (t : ℝ) (h : HasDerivAt X v t) :
    HasDerivAt (fun s => A (X s)) (A v) t := by
  have hd := hasDerivAt_pi.1 h
  exact ((((hd 0).add (hd 2)).add ((hd 3).const_mul 2)).add
    ((hd 4).const_mul 2)).add ((hd 5).const_mul 2)

theorem deriv_B (X : ℝ → State) (v : State) (t : ℝ) (h : HasDerivAt X v t) :
    HasDerivAt (fun s => B (X s)) (B v) t := by
  have hd := hasDerivAt_pi.1 h
  exact ((((hd 1).add (hd 2)).add (hd 3)).add
    ((hd 4).const_mul 2)).add ((hd 5).const_mul 2)

theorem deriv_Y (X : ℝ → State) (v : State) (t : ℝ) (h : HasDerivAt X v t) :
    HasDerivAt (fun s => Y (X s)) (Y v) t := by
  have hd := hasDerivAt_pi.1 h
  exact (((hd 2).add ((hd 3).const_mul (9/8))).add
    ((hd 4).const_mul (7/5))).add ((hd 5).const_mul (9/5))

theorem A_smul (a : ℝ) (c : State) : A (a • c) = a*A c := by
  simp [A]; ring
theorem B_smul (a : ℝ) (c : State) : B (a • c) = a*B c := by
  simp [B]; ring

theorem extension_solution (r d R : ℝ) (hR : 0 < R) (c : State) :
    ∃ b : State → ℝ, ∃ X : ℝ → State,
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → b x = 1) ∧
      X 0 = c ∧ ∀ t, HasDerivAt X
        (b (positivePart (X t)) • field r d (positivePart (X t))) t := by
  let b : ContDiffBump (0 : State) := ⟨R,2*R,hR,by linarith⟩
  let f : State → State := fun x => b x • field r d x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (field_contDiff r d)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (positivePart x)) := by
    simpa only [mul_one] using hK.comp positivePart_lipschitz
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (positivePart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) c
  refine ⟨b,X,(fun _ => ⟨b.nonneg,b.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem global_nonnegative_solution (r d : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (c : State) (hc : Nonneg c) :
    ∃ X : ℝ → State, X 0 = c ∧ (∀ t, 0 ≤ t → Nonneg (X t)) ∧
      ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t := by
  let R := max (max (A c) (B c)) 1
  have hR : 1 ≤ R := le_max_right _ _
  obtain ⟨b,X,hb,hbone,hX0,hXd⟩ := extension_solution r d R (by linarith) c
  have hnonneg : ∀ t, 0 ≤ t → Nonneg (X t) := by
    intro t ht i
    apply scalar_lower_barrier (fun t => X t i)
      (fun t => b (positivePart (X t))*field r d (positivePart (X t)) i) 0
      (fun t _ => hasDerivAt_pi.1 (hXd t) i) (by simpa [hX0] using hc i) ?_ t ht
    intro s _ hs
    apply mul_nonneg (hb _).1
    exact boundary_nonneg r d hr hd _ (fun j => le_max_left 0 (X s j)) i (max_eq_left hs)
  have hpart : ∀ t, 0 ≤ t → positivePart (X t) = X t := by
    intro t ht
    funext i
    exact max_eq_right (hnonneg t ht i)
  have hscaled : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • field r d (X t)) t := by
    intro t ht
    simpa only [hpart t ht] using hXd t
  have hA : ∀ t, 0 ≤ t → A (X t) ≤ R := by
    apply scalar_upper_barrier (fun t => A (X t)) (fun t => b (X t)*(1-A (X t))) R
    · intro t ht
      simpa only [A_smul,material_A] using deriv_A X _ t (hscaled t ht)
    · rw [hX0]
      exact (le_max_left _ _).trans (le_max_left _ _)
    · intro t _ hs
      exact mul_nonpos_of_nonneg_of_nonpos (hb _).1 (by linarith)
  have hB : ∀ t, 0 ≤ t → B (X t) ≤ R := by
    apply scalar_upper_barrier (fun t => B (X t)) (fun t => b (X t)*(1-B (X t))) R
    · intro t ht
      simpa only [B_smul,material_B] using deriv_B X _ t (hscaled t ht)
    · rw [hX0]
      exact (le_max_right _ _).trans (le_max_left _ _)
    · intro t _ hs
      exact mul_nonpos_of_nonneg_of_nonpos (hb _).1 (by linarith)
  have hnorm : ∀ t, 0 ≤ t → ‖X t‖ ≤ R := by
    intro t ht
    apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R)).2
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (hnonneg t ht i)]
    have ha := hA t ht
    have hb' := hB t ht
    have hn := hnonneg t ht
    dsimp [A,B] at ha hb'
    fin_cases i
    · change X t 0 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]
    · change X t 1 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]
    · change X t 2 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]
    · change X t 3 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]
    · change X t 4 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]
    · change X t 5 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]
  refine ⟨X,hX0,hnonneg,?_⟩
  intro t ht
  simpa only [hbone _ (hnorm t ht),one_smul] using hscaled t ht

end
end ProductiveRecovery
