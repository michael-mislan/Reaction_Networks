import proofs.ACRZeroDivisors.IdealSubstitution
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace ACRZeroDivisors
open MvPolynomial

noncomputable def graphIdeal {τ A : Type*} [CommRing A]
    (I : Ideal A) (v : τ → A) : Ideal (MvPolynomial τ A) :=
  I.map C ⊔ Ideal.span (Set.range (fun j => X j - C (v j)))

theorem graphIdeal_mem_iff {τ A : Type*} [CommRing A]
    (I : Ideal A) (v : τ → A) (p : MvPolynomial τ A) :
    p ∈ graphIdeal I v ↔ eval v p ∈ I := by
  have hle : graphIdeal I v ≤ I.comap (eval v) := by
    apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      simpa using ha
    · apply Ideal.span_le.mpr
      rintro _ ⟨j,rfl⟩
      simp
  constructor
  · exact fun hp => hle hp
  · intro hp
    have hv : ∀ j, X j - C (v j) ∈ graphIdeal I v := by
      intro j
      exact (show Ideal.span (Set.range (fun j => X j - C (v j))) ≤ graphIdeal I v
        from le_sup_right) (Ideal.subset_span ⟨j,rfl⟩)
    have h := substitution_sub_mem (graphIdeal I v) (fun j => C (v j)) hv p
    have he : eval₂Hom (C (σ := τ)) (fun j => C (v j)) = C.comp (eval v) := by
      ext <;> simp
    rw [he,RingHom.comp_apply] at h
    have hc : C (eval v p) ∈ graphIdeal I v :=
      (show I.map C ≤ graphIdeal I v from le_sup_left) (Ideal.mem_map_of_mem C hp)
    simpa using (graphIdeal I v).add_mem h hc

theorem graphIdeal_ker {τ A : Type*} [CommRing A] (I : Ideal A) (v : τ → A) :
    RingHom.ker ((Ideal.Quotient.mk I).comp (eval v)) = graphIdeal I v := by
  ext p
  simp only [RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem,
    graphIdeal_mem_iff]

noncomputable def graphQuotientEquiv {τ A : Type*} [CommRing A]
    (I : Ideal A) (v : τ → A) :
    (MvPolynomial τ A ⧸ graphIdeal I v) ≃+* (A ⧸ I) := by
  let f := (Ideal.Quotient.mk I).comp (eval v)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨C a,by simp [f]⟩
  exact (Ideal.quotEquivOfEq (graphIdeal_ker I v).symm).trans
    (f.quotientKerEquivOfSurjective hf)

/-- Old-coordinate ideal membership and nonzero annihilators are preserved. -/
theorem graph_coefficient_candidate_iff {τ A : Type*} [CommRing A]
    (I : Ideal A) (v : τ → A) (a : A) :
    (C a ∈ graphIdeal I v ∨ ∃ p, p ∉ graphIdeal I v ∧ C a*p ∈ graphIdeal I v) ↔
      (a ∈ I ∨ ∃ p, p ∉ I ∧ a*p ∈ I) := by
  simp only [graphIdeal_mem_iff,map_mul,eval_C]
  constructor
  · rintro (ha | ⟨p,hp,ht⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨eval v p,hp,ht⟩
  · rintro (ha | ⟨p,hp,ht⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨C p,by simpa using hp,by simpa using ht⟩

end ACRZeroDivisors
