import proofs.C4Assemblies.Source
import proofs.ProductiveRecovery.SourceFlow

namespace C4Assemblies
noncomputable section
open scoped BigOperators
open ProductiveRecovery CoreCouplingGlobal CoreCouplingCAC
variable {ι : Type*} [Fintype ι]

def assemblyPositivePart (c : Assembly ι) : Assembly ι := fun i => positivePart (c i)
def totalA (c : Assembly ι) : ℝ := ∑ i, A (c i)
def totalB (c : Assembly ι) : ℝ := ∑ i, B (c i)

theorem assemblyPositivePart_lipschitz : LipschitzWith 1 (@assemblyPositivePart ι) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0 ≤ dist x y)).2
  intro i
  exact (positivePart_lipschitz.dist_le_mul (x i) (y i)).trans
    (by simpa using dist_le_pi_dist x y i)

theorem assemblyField_contDiff (k : ι → ι → ℝ) (r d : ι → ℝ) :
    ContDiff ℝ 1 (assemblyField k r d) := by
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro s
  apply ContDiff.add
  · have hi : ContDiff ℝ 1 (fun c : Assembly ι => c i) := by fun_prop
    have hf := (field_contDiff (r i) (d i)).comp hi
    exact (contDiff_pi.1 hf) s
  · dsimp [diffusion]
    fun_prop

theorem assembly_boundary_nonneg (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j)
    (r d : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (c : Assembly ι) (hc : ∀ i, Nonneg (c i)) (i : ι) (s : Fin 6) (hz : c i s = 0) :
    0 ≤ assemblyField k r d c i s := by
  apply add_nonneg (boundary_nonneg (r i) (d i) (hr i) (hd i) (c i) (hc i) s hz)
  apply diffusion_at_min k hk (fun j => c j s) i
  intro j
  rw [hz]
  exact hc j s

theorem totalA_field (k : ι → ι → ℝ) (hs : ∀ i j, k i j = k j i)
    (r d : ι → ℝ) (c : Assembly ι) :
    totalA (assemblyField k r d c) = Fintype.card ι - totalA c := by
  simp only [totalA, assembly_A, Finset.sum_add_distrib, diffusion_sum_zero k hs,
    add_zero, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem totalB_field (k : ι → ι → ℝ) (hs : ∀ i j, k i j = k j i)
    (r d : ι → ℝ) (c : Assembly ι) :
    totalB (assemblyField k r d c) = Fintype.card ι - totalB c := by
  simp only [totalB, assembly_B, Finset.sum_add_distrib, diffusion_sum_zero k hs,
    add_zero, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem deriv_totalA (X : ℝ → Assembly ι) (v : Assembly ι) (t : ℝ) (h : HasDerivAt X v t) :
    HasDerivAt (fun s => totalA (X s)) (totalA v) t := by
  exact HasDerivAt.fun_sum fun i _ => deriv_A (fun s => X s i) (v i) t (hasDerivAt_pi.1 h i)

theorem deriv_totalB (X : ℝ → Assembly ι) (v : Assembly ι) (t : ℝ) (h : HasDerivAt X v t) :
    HasDerivAt (fun s => totalB (X s)) (totalB v) t := by
  exact HasDerivAt.fun_sum fun i _ => deriv_B (fun s => X s i) (v i) t (hasDerivAt_pi.1 h i)

theorem totalA_smul (a : ℝ) (c : Assembly ι) : totalA (a • c) = a*totalA c := by
  simp [totalA,A_smul,Finset.mul_sum]

theorem totalB_smul (a : ℝ) (c : Assembly ι) : totalB (a • c) = a*totalB c := by
  simp [totalB,B_smul,Finset.mul_sum]

theorem assembly_extension_solution (k : ι → ι → ℝ) (r d : ι → ℝ)
    (R : ℝ) (hR : 0 < R) (c : Assembly ι) :
    ∃ b : Assembly ι → ℝ, ∃ X : ℝ → Assembly ι,
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → b x = 1) ∧
      X 0 = c ∧ ∀ t, HasDerivAt X
        (b (assemblyPositivePart (X t)) • assemblyField k r d (assemblyPositivePart (X t))) t := by
  let b : ContDiffBump (0 : Assembly ι) := ⟨R,2*R,hR,by linarith⟩
  let f : Assembly ι → Assembly ι := fun x => b x • assemblyField k r d x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (assemblyField_contDiff k r d)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (assemblyPositivePart x)) := by
    simpa only [mul_one] using hK.comp assemblyPositivePart_lipschitz
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (assemblyPositivePart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) c
  refine ⟨b,X,(fun _ => ⟨b.nonneg,b.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem assembly_global_nonnegative_solution (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hs : ∀ i j, k i j = k j i)
    (r d : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (c : Assembly ι) (hc : ∀ i, Nonneg (c i)) :
    ∃ X : ℝ → Assembly ι, X 0 = c ∧ (∀ t, 0 ≤ t → ∀ i, Nonneg (X t i)) ∧
      ∀ t, 0 ≤ t → HasDerivAt X (assemblyField k r d (X t)) t := by
  classical
  let R := max (max (totalA c) (totalB c)) ((Fintype.card ι : ℝ)+1)
  have hR : (Fintype.card ι : ℝ)+1 ≤ R := le_max_right _ _
  have hRp : 0 < R := lt_of_lt_of_le (by positivity) hR
  obtain ⟨b,X,hb,hbone,hX0,hXd⟩ := assembly_extension_solution k r d R hRp c
  have hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i) := by
    intro t ht i s
    apply scalar_lower_barrier (fun t => X t i s)
      (fun t => b (assemblyPositivePart (X t))*assemblyField k r d (assemblyPositivePart (X t)) i s) 0
      (fun t _ => hasDerivAt_pi.1 (hasDerivAt_pi.1 (hXd t) i) s)
      (by simpa [hX0] using hc i s) ?_ t ht
    intro u _ hu
    apply mul_nonneg (hb _).1
    exact assembly_boundary_nonneg k hk r d hr hd _ (fun j l => le_max_left 0 (X u j l))
      i s (max_eq_left hu)
  have hpart : ∀ t, 0 ≤ t → assemblyPositivePart (X t) = X t := by
    intro t ht
    funext i s
    exact max_eq_right (hn t ht i s)
  have hscaled : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • assemblyField k r d (X t)) t := by
    intro t ht
    simpa only [hpart t ht] using hXd t
  have ha : ∀ t, 0 ≤ t → totalA (X t) ≤ R := by
    apply scalar_upper_barrier (fun t => totalA (X t))
      (fun t => b (X t)*((Fintype.card ι : ℝ)-totalA (X t))) R
    · intro t ht
      simpa only [totalA_smul,totalA_field k hs] using deriv_totalA X _ t (hscaled t ht)
    · rw [hX0]
      exact (le_max_left _ _).trans (le_max_left _ _)
    · intro t _ ht
      exact mul_nonpos_of_nonneg_of_nonpos (hb _).1 (by linarith)
  have hbb : ∀ t, 0 ≤ t → totalB (X t) ≤ R := by
    apply scalar_upper_barrier (fun t => totalB (X t))
      (fun t => b (X t)*((Fintype.card ι : ℝ)-totalB (X t))) R
    · intro t ht
      simpa only [totalB_smul,totalB_field k hs] using deriv_totalB X _ t (hscaled t ht)
    · rw [hX0]
      exact (le_max_right _ _).trans (le_max_left _ _)
    · intro t _ ht
      exact mul_nonpos_of_nonneg_of_nonpos (hb _).1 (by linarith)
  have hnorm : ∀ t, 0 ≤ t → ‖X t‖ ≤ R := by
    intro t ht
    apply (pi_norm_le_iff_of_nonneg hRp.le).2
    intro i
    apply (pi_norm_le_iff_of_nonneg hRp.le).2
    intro s
    rw [Real.norm_eq_abs,abs_of_nonneg (hn t ht i s)]
    have hAN : ∀ j, 0 ≤ A (X t j) := by
      intro j
      dsimp [A]
      linarith [hn t ht j 0, hn t ht j 2, hn t ht j 3, hn t ht j 4, hn t ht j 5]
    have hBN : ∀ j, 0 ≤ B (X t j) := by
      intro j
      dsimp [B]
      linarith [hn t ht j 1, hn t ht j 2, hn t ht j 3, hn t ht j 4, hn t ht j 5]
    have hai : A (X t i) ≤ R :=
      (Finset.single_le_sum (fun j _ => hAN j) (Finset.mem_univ i)).trans (ha t ht)
    have hbi : B (X t i) ≤ R :=
      (Finset.single_le_sum (fun j _ => hBN j) (Finset.mem_univ i)).trans (hbb t ht)
    have h0 := hn t ht i 0
    have h1 := hn t ht i 1
    have h2 := hn t ht i 2
    have h3 := hn t ht i 3
    have h4 := hn t ht i 4
    have h5 := hn t ht i 5
    dsimp [A,B] at hai hbi
    fin_cases s
    · change X t i 0 ≤ R; linarith
    · change X t i 1 ≤ R; linarith
    · change X t i 2 ≤ R; linarith
    · change X t i 3 ≤ R; linarith
    · change X t i 4 ≤ R; linarith
    · change X t i 5 ≤ R; linarith
  refine ⟨X,hX0,hn,?_⟩
  intro t ht
  simpa only [hbone _ (hnorm t ht),one_smul] using hscaled t ht

end
end C4Assemblies
