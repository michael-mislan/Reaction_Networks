import proofs.RAF1519.Refinement.Source
import proofs.ProductiveRecovery.SourceFlow

namespace RAF1519.Refinement
noncomputable section
open CoreCouplingCAC CoreCouplingGlobal

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

theorem field_contDiff (r d beta theta : ℝ) : ContDiff ℝ 1 (field r d beta theta) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [field,firstFlux,secondFlux,ProductiveRecovery.flux,free] <;> fun_prop

theorem boundary_nonneg (r d beta theta : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hb : 0 < beta) (ht : 0 < theta) (c : State) (hc : ∀ i, 0 ≤ c i)
    (i : Fin 7) (hi : c i = 0) : 0 ≤ field r d beta theta c i := by
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  have h6 := hc 6
  fin_cases i <;>
    dsimp [field,firstFlux,secondFlux,ProductiveRecovery.flux,free] at hi ⊢ <;>
    rw [hi] <;> ring_nf <;> positivity

theorem deriv_material_A (X : ℝ → State) (v : State) (t : ℝ) (h : HasDerivAt X v t) :
    HasDerivAt (fun s => materialA (X s)) (materialA v) t := by
  have hd := hasDerivAt_pi.1 h
  exact (((((hd 0).add (hd 2)).add ((hd 3).const_mul 2)).add
    ((hd 4).const_mul 2)).add ((hd 5).const_mul 2)).add (hd 6)

theorem deriv_material_B (X : ℝ → State) (v : State) (t : ℝ) (h : HasDerivAt X v t) :
    HasDerivAt (fun s => materialB (X s)) (materialB v) t := by
  have hd := hasDerivAt_pi.1 h
  exact (((((hd 1).add (hd 2)).add (hd 3)).add
    ((hd 4).const_mul 2)).add ((hd 5).const_mul 2)).add (hd 6)

theorem deriv_stock (X : ℝ → State) (v : State) (t : ℝ) (h : HasDerivAt X v t) :
    HasDerivAt (fun s => stock (X s)) (stock v) t := by
  have hd := hasDerivAt_pi.1 h
  exact (((hd 2).add ((hd 3).const_mul (9/8))).add
    ((hd 4).const_mul (7/5))).add ((hd 5).const_mul (9/5))

theorem materialA_smul (a : ℝ) (c : State) : materialA (a • c) = a*materialA c := by
  simp [materialA,free,ProductiveRecovery.A]; ring
theorem materialB_smul (a : ℝ) (c : State) : materialB (a • c) = a*materialB c := by
  simp [materialB,free,ProductiveRecovery.B]; ring

theorem extension_solution (r d beta theta R : ℝ) (hR : 0 < R) (c : State) :
    ∃ b : State → ℝ, ∃ X : ℝ → State,
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → b x = 1) ∧
      X 0 = c ∧ ∀ t, HasDerivAt X
        (b (positivePart (X t)) • field r d beta theta (positivePart (X t))) t := by
  let b : ContDiffBump (0 : State) := ⟨R,2*R,hR,by linarith⟩
  let f : State → State := fun x => b x • field r d beta theta x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (field_contDiff r d beta theta)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (positivePart x)) := by
    simpa only [mul_one] using hK.comp positivePart_lipschitz
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (positivePart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) c
  refine ⟨b,X,(fun _ => ⟨b.nonneg,b.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem global_nonnegative_solution (r d beta theta : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hbpos : 0 < beta) (htpos : 0 < theta) (c : State) (hc : ∀ i, 0 ≤ c i) :
    ∃ X : ℝ → State, X 0 = c ∧ (∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i) ∧
      ∀ t, 0 ≤ t → HasDerivAt X (field r d beta theta (X t)) t := by
  let R := max (max (materialA c) (materialB c)) 1
  have hR : 1 ≤ R := le_max_right _ _
  obtain ⟨b,X,hb,hbone,hX0,hXd⟩ := extension_solution r d beta theta R (by linarith) c
  have hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i := by
    intro t ht i
    apply scalar_lower_barrier (fun t => X t i)
      (fun t => b (positivePart (X t))*field r d beta theta (positivePart (X t)) i) 0
      (fun t _ => hasDerivAt_pi.1 (hXd t) i) (by simpa [hX0] using hc i) ?_ t ht
    intro s _ hs
    apply mul_nonneg (hb _).1
    exact boundary_nonneg r d beta theta hr hd hbpos htpos _
      (fun j => le_max_left 0 (X s j)) i (max_eq_left hs)
  have hpart : ∀ t, 0 ≤ t → positivePart (X t) = X t := by
    intro t ht; funext i; exact max_eq_right (hnonneg t ht i)
  have hscaled : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • field r d beta theta (X t)) t := by
    intro t ht; simpa only [hpart t ht] using hXd t
  have hA : ∀ t, 0 ≤ t → materialA (X t) ≤ R := by
    apply scalar_upper_barrier (fun t => materialA (X t)) (fun t => b (X t)*(1-materialA (X t))) R
    · intro t ht
      simpa only [materialA_smul,material_A] using deriv_material_A X _ t (hscaled t ht)
    · rw [hX0]; exact (le_max_left _ _).trans (le_max_left _ _)
    · intro t _ hs; exact mul_nonpos_of_nonneg_of_nonpos (hb _).1 (by linarith)
  have hB : ∀ t, 0 ≤ t → materialB (X t) ≤ R := by
    apply scalar_upper_barrier (fun t => materialB (X t)) (fun t => b (X t)*(1-materialB (X t))) R
    · intro t ht
      simpa only [materialB_smul,material_B] using deriv_material_B X _ t (hscaled t ht)
    · rw [hX0]; exact (le_max_right _ _).trans (le_max_left _ _)
    · intro t _ hs; exact mul_nonpos_of_nonneg_of_nonpos (hb _).1 (by linarith)
  have hnorm : ∀ t, 0 ≤ t → ‖X t‖ ≤ R := by
    intro t ht
    apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R)).2
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (hnonneg t ht i)]
    have ha := hA t ht
    have hb' := hB t ht
    have hn := hnonneg t ht
    simp [materialA,materialB,free,ProductiveRecovery.A,ProductiveRecovery.B] at ha hb'
    fin_cases i
    · change X t 0 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5,hn 6]
    · change X t 1 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5,hn 6]
    · change X t 2 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5,hn 6]
    · change X t 3 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5,hn 6]
    · change X t 4 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5,hn 6]
    · change X t 5 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5,hn 6]
    · change X t 6 ≤ R
      linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5,hn 6]
  refine ⟨X,hX0,hnonneg,?_⟩
  intro t ht
  simpa only [hbone _ (hnorm t ht),one_smul] using hscaled t ht
end
end RAF1519.Refinement
