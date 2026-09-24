import proofs.CompositionalMemory.FiniteDeadlineCertificate

namespace CompositionalMemory
open FiniteCopy HeritableCompositions Set
open scoped Matrix.Norms.Operator

theorem jumpGeneratorMatrix_mulVec {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (v : α → ℝ) :
    (jumpGeneratorMatrix M).mulVec v=fun x => M.generator v x := by
  obtain ⟨q,hq,_,hb⟩ := M.exists_clock 0
  rw [← uniformize_generator_matrix M q hq hb]
  funext x
  have hh := M.uniformize_step q hq hb v x
  change (kernelMatrix (M.uniformize q hq hb)).mulVec v x=v x+M.generator v x/q at hh
  simp only [Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul,Pi.sub_apply]
  rw [hh]
  field_simp
  ring

theorem finite_time_upper_of_pointwise {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (t : NNReal) (v : α → ℝ)
    (c : ℝ) (hv : ∀ y, v y ≤ c) (x : α) : finiteTimeExpectation M t v x ≤ c := by
  obtain ⟨q,hq,_,hb⟩ := M.exists_clock 0
  rw [finite_time_eq_uniformized M q t hq hb]
  have hh := poisson_mono (M.uniformize q hq hb) (q*t) v (fun _ => c) hv x
  simpa only [poisson_constant] using hh

theorem finite_dynamic_expectation_derivative {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (v dv : ℝ → α → ℝ) (t : ℝ)
    (hv : ∀ y, HasDerivAt (fun u => v u y) (dv t y) t) (x : α) :
    HasDerivAt (fun u => (NormedSpace.exp (u • jumpGeneratorMatrix M)).mulVec (v u) x)
      ((NormedSpace.exp (t • jumpGeneratorMatrix M)).mulVec
        (fun y => dv t y+M.generator (v t) y) x) t := by
  let Q := jumpGeneratorMatrix M
  have he (y : α) : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Q) x y)
      ((NormedSpace.exp (t • Q)*Q) x y) t := by
    let entry : Matrix α α ℝ →ₗ[ℝ] ℝ :=
      { toFun := fun A => A x y
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hh := entry.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_exp_smul_const Q t)
    exact hh
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun y _ => (he y).mul (hv y))
  have hd : (∑ y,((NormedSpace.exp (t • Q)*Q) x y*v t y+
      NormedSpace.exp (t • Q) x y*dv t y))=
      (NormedSpace.exp (t • Q)).mulVec (fun y => dv t y+M.generator (v t) y) x := by
    rw [Finset.sum_add_distrib]
    change ((NormedSpace.exp (t • Q)*Q).mulVec (v t)) x+
      (NormedSpace.exp (t • Q)).mulVec (dv t) x=_
    rw [← Matrix.mulVec_mulVec,show Q.mulVec (v t)=(fun y => M.generator (v t) y) from
      jumpGeneratorMatrix_mulVec M (v t)]
    simp only [Matrix.mulVec,dotProduct,mul_add,Finset.sum_add_distrib]
    exact add_comm _ _
  rw [hd] at hh
  exact hh

/-- Time-dependent bounded observables are controlled by their time-plus-
generator inequality under the actual finite law, without a grid in time. -/
theorem finite_time_dependent_drift_bound {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (T : NNReal)
    (v dv : ℝ → α → ℝ) (c : ℝ)
    (hv : ∀ t ∈ Icc (0 : ℝ) T, ∀ y, HasDerivAt (fun u => v u y) (dv t y) t)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, ∀ y, dv t y+M.generator (v t) y ≤ c) (x : α) :
    finiteTimeExpectation M T (v T) x ≤ v 0 x+(T : ℝ)*c := by
  let F := fun t : ℝ => (NormedSpace.exp (t • jumpGeneratorMatrix M)).mulVec (v t) x
  let dF := fun t : ℝ => (NormedSpace.exp (t • jumpGeneratorMatrix M)).mulVec
    (fun y => dv t y+M.generator (v t) y) x
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt F (dF t) t :=
    finite_dynamic_expectation_derivative M v dv t (hv t ht) x
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) : dF t ≤ c :=
    finite_time_upper_of_pointwise M ⟨t,ht.1⟩ _ c (hg t ⟨ht.1,ht.2.le⟩) x
  have hc : ContinuousOn (fun t : ℝ => v 0 x+t*c) (Icc (0 : ℝ) T) := by fun_prop
  have hcd (t : ℝ) : HasDerivAt (fun u : ℝ => v 0 x+u*c) c t := by
    simpa using ((hasDerivAt_id t).mul_const c).const_add (v 0 x)
  have hinitial : F 0 ≤ v 0 x+(0 : ℝ)*c := by simp [F]
  have hh := image_le_of_deriv_right_le_deriv_boundary
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    hinitial hc (fun t _ => (hcd t).hasDerivWithinAt) hbound
  exact hh ⟨T.property,le_rfl⟩

end CompositionalMemory
