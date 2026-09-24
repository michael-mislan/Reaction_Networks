import proofs.AllIrrRAFCert.Main

namespace AllIrrRAFCert
open RAF Hardness
open MinRAFApprox.SetCoverSource (IsIrreducibleRAF)

def ValidListedFamily {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : CRS M R) (C : Catalysis M R) (L : Finset (Finset R)) : Prop :=
  ∀ S ∈ L, IsIrreducibleRAF Q C S

def ExactIrrRAFCertification {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : CRS M R) (C : Catalysis M R) (L : Finset (Finset R)) : Prop :=
  ValidListedFamily Q C L ∧ AllCertified Q C L

theorem clique_iff_not_exactCertification {k n : Nat}
    (G : SimpleGraph (Fin (n+2))) [DecidableRel G.Adj] :
    (∃ s : Finset (Fin (n+2)), G.IsNClique k s) ↔
      ¬ ExactIrrRAFCertification (crs (graphBad G)) cat (listedFamily k n) := by
  have hv : ValidListedFamily (crs (graphBad G)) cat (listedFamily k n) := listed_promise _
  simpa only [ExactIrrRAFCertification,and_iff_right hv] using (clique_reduction G).1

variable {M R : Type*} [Fintype R] [DecidableEq M] [DecidableEq R]

def ExtraIrrRAF (Q : CRS M R) (C : Catalysis M R) (L : Finset (Finset R)) : Prop :=
  ∃ J, IsIrreducibleRAF Q C J ∧ J ∉ L

/-- A tuple chooses one reaction from each listed irrRAF and preserves a RAF. -/
theorem extra_iff_preservingTransversal (Q : CRS M R) (C : Catalysis M R)
    (L : Finset (Finset R)) (hL : ValidListedFamily Q C L) :
    ExtraIrrRAF Q C L ↔ ∃ f : {I // I ∈ L} → R,
      (∀ I, f I ∈ I.val) ∧ IrrRAFEnumeration.HasRAFWithin Q C
        (Finset.univ \ Finset.univ.image f) := by
  classical
  constructor
  · rintro ⟨J,hJ,hJL⟩
    have hex : ∀ I : {I // I ∈ L}, ∃ r, r ∈ I.val ∧ r ∉ J := by
      intro I
      have hn : ¬ I.val ⊆ J := by
        intro hs
        have he : J = I.val := Finset.Subset.antisymm
          (hJ.2 _ (hL _ I.property).1 hs) hs
        exact hJL (he.symm ▸ I.property)
      exact Finset.not_subset.mp hn
    choose f hf using hex
    refine ⟨f,fun I => (hf I).1,J,hJ.1,?_⟩
    intro r hr
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_image]
    rintro ⟨I,he⟩
    exact (hf I).2 (he.symm ▸ hr)
  · rintro ⟨f,hf,J,hJ,hsub⟩
    obtain ⟨T,hTJ,hT⟩ := IrrRAFEnumeration.exists_minimal_subset (IsRAF Q C) hJ
    refine ⟨T,hT,?_⟩
    intro hTL
    let I : {I // I ∈ L} := ⟨T,hTL⟩
    have hmem := hsub (hTJ (hf I))
    have hin : f I ∈ Finset.univ.image f := Finset.mem_image.mpr ⟨I,Finset.mem_univ _,rfl⟩
    exact (Finset.mem_sdiff.mp hmem).2 hin

omit [Fintype R] in
theorem preservingTransversal_card_le (L : Finset (Finset R))
    (f : {I // I ∈ L} → R) : (Finset.univ.image f).card ≤ L.card := by
  classical
  exact (Finset.card_image_le).trans (by simp)

omit [Fintype R] in
theorem irrRAF_single_deletion (Q : CRS M R) (C : Catalysis M R) (S : Finset R) :
    IsIrreducibleRAF Q C S ↔ IsRAF Q C S ∧
      ∀ r ∈ S, ¬ IrrRAFEnumeration.HasRAFWithin Q C (S.erase r) :=
  IrrRAFEnumeration.irreducibleRAF_iff_oneDeletion Q C S

theorem axiom_iff_not_exactCertification {k n q : Nat} (A : WPHardness.System n q) :
    WPHardness.SmallGenerating A k ↔
      ¬ ExactIrrRAFCertification (WPHardness.crs A) WPHardness.cat
        (WPHardness.listedFamily k n q) := by
  classical
  have hv : ValidListedFamily (WPHardness.crs A) WPHardness.cat
      (WPHardness.listedFamily k n q) := WPHardness.listed_valid A
  rw [ExactIrrRAFCertification,and_iff_right hv,WPHardness.smallGenerating_iff_extra]
  simp only [WPHardness.Extra,AllCertified,WPHardness.listedFamily,
    Finset.mem_image,Finset.mem_univ,true_and,not_forall,not_exists,
    exists_prop,eq_comm]

end AllIrrRAFCert
