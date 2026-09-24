import proofs.ThreeSitePhosphorylation.EigenCoordinates

namespace ThreeSitePhosphorylation
noncomputable section

theorem periodic_homogeneous_source_kernel (r w T : ℝ) (hw : 0<w) (hT : 0<T)
    (x : Fin 7 → ℝ) (hn : ∀ i, x i<0)
    (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (he : ∀ i, (complexSource r).mulVec (b i)=spectralValues x w i • b i)
    (u : ℝ → (Fin 9 → ℂ))
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt u (T • (complexSource r).mulVec (u t)) t)
    (hp : u 1=u 0) (hc : b.coord (Sum.inr 0) (u 0)=0) (hr : imagPart (u 0)=0) : u 0=0 := by
  have hs (i : Fin 7) : b.coord (Sum.inl i) (u 0)=0 := by
    let L := ((b.coord (Sum.inl i)).toContinuousLinearMap).restrictScalars ℝ
    have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
        HasDerivAt (fun s => b.coord (Sum.inl i) (u s))
          (((T*x i:ℝ):ℂ)*b.coord (Sum.inl i) (u t)) t := by
      have hh := L.hasFDerivAt.comp_hasDerivAt t (hu t ht)
      convert hh using 1
      change _ = b.coord (Sum.inl i) (T • (complexSource r).mulVec (u t))
      change _ = ((b.coord (Sum.inl i)).restrictScalars ℝ) (T • (complexSource r).mulVec (u t))
      rw [map_smul]
      change _ = T • b.coord (Sum.inl i) ((complexSource r).mulVec (u t))
      rw [basis_coord_eigen b _ _ he]
      simp [spectralValues,Complex.ofReal_mul,mul_assoc]
    exact scalar_periodic_homogeneous ((T*x i:ℝ):ℂ)
      (negative_real_nonresonance (T*x i) (mul_neg_of_pos_of_neg hT (hn i)))
      (fun t => b.coord (Sum.inl i) (u t)) hd (congrArg (b.coord (Sum.inl i)) hp)
  have hminus : (complexSource r).mulVec (u 0)=(Complex.I*((-w:ℝ):ℂ)) • u 0 := by
    apply sub_eq_zero.mp
    apply (b.forall_coord_eq_zero_iff).mp
    intro i
    rw [map_sub,map_smul,basis_coord_eigen b _ _ he]
    cases i with
    | inl i => simp [hs]
    | inr j =>
      fin_cases j
      · simp [hc]
      · simp [spectralValues]
  exact real_vector_imaginary_eigen_zero r (-w) (neg_ne_zero.mpr (ne_of_gt hw)) (u 0) hr hminus

end
end ThreeSitePhosphorylation
