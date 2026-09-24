import proofs.CoreCouplingGlobal.PhysicalSpectrum

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Polynomial Module

/-- Distinct real characteristic roots give an actual continuous linear change
of coordinates that diagonalizes the physical derivative. -/
theorem real_eigenbasis_coordinates (M : Matrix (Fin 4) (Fin 4) ℝ)
    (μ : Fin 4 → ℝ) (hμ : Function.Injective μ)
    (hroot : ∀ i, M.charpoly.eval (μ i) = 0) :
    ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
      ∀ x : ResponseVector, M.toLin' (C x) = C (fun i => μ i*x i) := by
  classical
  have hev : ∀ i, ∃ v, Module.End.HasEigenvector M.toLin' (μ i) v := by
    intro i
    have hs : μ i ∈ spectrum ℝ M := Matrix.mem_spectrum_of_isRoot_charpoly (hroot i)
    have hs' : μ i ∈ spectrum ℝ M.toLin' := by simpa only [Matrix.spectrum_toLin'] using hs
    exact (Module.End.HasEigenvalue.of_mem_spectrum hs').exists_hasEigenvector
  choose v hv using hev
  have hlin := Module.End.eigenvectors_linearIndependent' M.toLin' μ hμ v hv
  let b : Basis (Fin 4) ℝ ResponseVector := basisOfPiSpaceOfLinearIndependent hlin
  have hb : ∀ i, b i = v i := by
    intro i
    exact congrFun (coe_basisOfPiSpaceOfLinearIndependent hlin) i
  let C : ResponseVector ≃L[ℝ] ResponseVector := b.equivFun.symm.toContinuousLinearEquiv
  refine ⟨C,?_⟩
  intro x
  change M.toLin' (b.equivFun.symm x) = b.equivFun.symm (fun i => μ i*x i)
  rw [Basis.equivFun_symm_apply,Basis.equivFun_symm_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,hb,(hv i).apply_eq_smul,smul_smul]
  rw [mul_comm]

/-- A middle equilibrium admits three strictly stable real coordinates and one
strictly unstable real coordinate. The stable rates exceed 1/2 in magnitude. -/
theorem middle_diagonal_coordinates (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ μ : Fin 4 → ℝ, ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
      (∀ i : Fin 3, μ i.castSucc < -(1/2:ℝ)) ∧ 0 < μ 3 ∧ μ 3 < 1/10 ∧
      ∀ x : ResponseVector,
        (physicalJacobian e (encodeState s)).toLin' (C x) = C (fun i => μ i*x i) := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hfactor⟩ := middle_physical_characteristic_factorization e he hu s hs hss hz
  let μ : Fin 4 → ℝ := ![a,b,c,d]
  have hab : a < b := ha.2.trans hb.1
  have hbc : b < c := hb.2.trans hc.1
  have hcd : c < d := by linarith [hc.2,hd.1]
  have hinj : Function.Injective μ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [μ] at hij ⊢
    all_goals linarith
  have hroot : ∀ i, (physicalJacobian e (encodeState s)).charpoly.eval (μ i) = 0 := by
    intro i
    rw [hfactor]
    fin_cases i <;> simp [μ]
  obtain ⟨C,hC⟩ := real_eigenbasis_coordinates _ μ hinj hroot
  refine ⟨μ,C,?_,hd.1,hd.2,hC⟩
  intro i
  fin_cases i <;> dsimp [μ]
  · linarith [ha.2]
  · linarith [hb.2]
  · exact hc.2

/-- The uniform decay weight 1/4 leaves positive stable and unstable gaps even
though the positive eigenvalue is small. -/
theorem middle_weighted_gaps (μ : Fin 4 → ℝ)
    (hs : ∀ i : Fin 3, μ i.castSucc < -(1/2:ℝ)) (hu : 0 < μ 3) :
    (∀ i : Fin 3, 1/4 < -μ i.castSucc-1/4) ∧ 1/4 < μ 3+1/4 := by
  exact ⟨fun i => by linarith [hs i],by linarith⟩

end CoreCouplingGlobal
