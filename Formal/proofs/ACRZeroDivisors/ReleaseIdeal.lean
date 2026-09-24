import proofs.ACRZeroDivisors.TriangularRelease

namespace ACRZeroDivisors
open MvPolynomial

theorem span_sup_perturbation {A ι : Type*} [CommRing A]
    (J : Ideal A) (f g : ι → A) (h : ∀ i, f i - g i ∈ J) :
    Ideal.span (Set.range f) ⊔ J = Ideal.span (Set.range g) ⊔ J := by
  apply le_antisymm
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hd := (show J ≤ Ideal.span (Set.range g) ⊔ J from le_sup_right) (h i)
    have hg := (show Ideal.span (Set.range g) ≤ Ideal.span (Set.range g) ⊔ J
      from le_sup_left) (Ideal.subset_span ⟨i,rfl⟩)
    simpa using (Ideal.span (Set.range g) ⊔ J).add_mem hd hg
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hd := (show J ≤ Ideal.span (Set.range f) ⊔ J from le_sup_right) (h i)
    have hf := (show Ideal.span (Set.range f) ≤ Ideal.span (Set.range f) ⊔ J
      from le_sup_left) (Ideal.subset_span ⟨i,rfl⟩)
    simpa using (Ideal.span (Set.range f) ⊔ J).sub_mem hf hd

/-- Old-species equations after releasing products through private intermediates.
The weight at the final step includes both final products. -/
noncomputable def releasedOldField {σ A : Type*} [CommRing A] {n : ℕ}
    (f : σ → A) (F : A) (rates : Fin (n+1) → Aˣ)
    (w : σ → Fin (n+1) → A) (i : σ) : MvPolynomial (Fin (n+1)) A :=
  C (f i) - ∑ j, C (w i j) * cumulativeRelease F rates j

noncomputable def releaseIdeal {σ A : Type*} [CommRing A] {n : ℕ}
    (f : σ → A) (F : A) (rates : Fin (n+1) → Aˣ)
    (w : σ → Fin (n+1) → A) : Ideal (MvPolynomial (Fin (n+1)) A) :=
  Ideal.span (Set.range (releasedOldField f F rates w)) ⊔
    Ideal.span (Set.range (triangularDifferences (cumulativeRelease F rates)))

theorem releaseIdeal_eq_graph {σ A : Type*} [CommRing A] {n : ℕ}
    (f : σ → A) (F : A) (rates : Fin (n+1) → Aˣ)
    (w : σ → Fin (n+1) → A) :
    releaseIdeal f F rates w =
      graphIdeal (Ideal.span (Set.range f)) (fun j => F * (↑(rates j)⁻¹ : A)) := by
  classical
  rw [releaseIdeal,triangular_span]
  have h := span_sup_perturbation
    (Ideal.span (Set.range (cumulativeRelease F rates)))
    (releasedOldField f F rates w) (fun i => C (f i)) (by
      intro i
      have hs : ∑ j, C (w i j) * cumulativeRelease F rates j ∈
          Ideal.span (Set.range (cumulativeRelease F rates)) := by
        apply (Ideal.span (Set.range (cumulativeRelease F rates))).sum_mem
        intro j _
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)
      simpa [releasedOldField] using
        (Ideal.span (Set.range (cumulativeRelease F rates))).neg_mem hs)
  rw [h,release_span_graph,graphIdeal,Ideal.map_span]
  congr 2
  ext p
  simp only [Set.mem_range,Set.mem_image]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨f i,⟨i,rfl⟩,rfl⟩
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩

noncomputable def releaseQuotientEquiv {σ A : Type*} [CommRing A] {n : ℕ}
    (f : σ → A) (F : A) (rates : Fin (n+1) → Aˣ)
    (w : σ → Fin (n+1) → A) :
    (MvPolynomial (Fin (n+1)) A ⧸ releaseIdeal f F rates w) ≃+*
      (A ⧸ Ideal.span (Set.range f)) :=
  (Ideal.quotEquivOfEq (releaseIdeal_eq_graph f F rates w)).trans
    (graphQuotientEquiv _ _)

end ACRZeroDivisors
