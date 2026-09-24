import proofs.AllIrrRAFCert.Hardness.GraphAdapter
import proofs.AllIrrRAFCert.Hardness.Encoding
import proofs.AllIrrRAFCert.WPHardness.Encoding

namespace AllIrrRAFCert

open RAF Hardness
open MinRAFApprox.SetCoverSource (IsIrreducibleRAF)

/-- Completeness of a supplied finite family; validity is stated separately. -/
def AllCertified {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : CRS M R) (C : Catalysis M R) (L : Finset (Finset R)) : Prop :=
  ∀ S, IsIrreducibleRAF Q C S → S ∈ L

theorem listed_promise {k n : Nat} (bad : Pair k n → Bool) :
    ∀ S ∈ listedFamily k n, IsIrreducibleRAF (crs bad) cat S := by
  intro S hS
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
  exact guard_isIrrRAF bad i

theorem extra_iff_not_allCertified {k n : Nat} (bad : Pair k n → Bool) :
    Extra bad ↔ ¬ AllCertified (crs bad) cat (listedFamily k n) := by
  classical
  constructor
  · rintro ⟨S,hS,hu⟩ hAll
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hAll S hS)
    exact hu i hi.symm
  · intro h
    have hex : ∃ S, IsIrreducibleRAF (crs bad) cat S ∧ S ∉ listedFamily k n := by
      by_contra hn
      apply h
      intro S hS
      by_contra hmem
      exact hn ⟨S,hS,hmem⟩
    obtain ⟨S,hS,hu⟩ := hex
    refine ⟨S,hS,?_⟩
    intro i hi
    apply hu
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,hi.symm⟩

/-- Terminal finite reduction: ordinary Mathlib k-Clique reduces to an unlisted
irrRAF, preserving exactly the number k of distinct valid supplied irrRAFs.
EncodingSize supplies an explicit polynomial dense source encoding. -/
theorem clique_reduction {k n : Nat} (G : SimpleGraph (Fin (n+2)))
    [DecidableRel G.Adj] :
    ((∃ s : Finset (Fin (n+2)), G.IsNClique k s) ↔
      ¬ AllCertified (crs (graphBad G)) cat (listedFamily k n)) ∧
    (∀ S ∈ listedFamily k n, IsIrreducibleRAF (crs (graphBad G)) cat S) ∧
    (listedFamily k n).card = k ∧
    encodingCells k n =
      (2 + 2*(k*(n+2)) + k + (k*(n+2))^2) +
      (3*(2 + 2*(k*(n+2)) + k + (k*(n+2))^2)+k) *
      (2*(k*(n+2)) + 2*(k*(n+2))^2 + 1) := by
  exact ⟨(graph_clique_iff_extra G).trans (extra_iff_not_allCertified _),
    listed_promise _,parameter_eq,encoding_polynomial⟩

/-- Minimum Axiom Set reduction, with the usual at-most-k set semantics. -/
theorem axiom_reduction {k n q : Nat} (A : WPHardness.System n q) :
    (WPHardness.SmallGenerating A k ↔ WPHardness.Extra (k := k) A) ∧
    (∀ S ∈ WPHardness.listedFamily k n q,
      IsIrreducibleRAF (WPHardness.crs A) WPHardness.cat S) ∧
    (WPHardness.listedFamily k n q).card = k :=
  ⟨WPHardness.smallGenerating_iff_extra A,WPHardness.listed_valid A,
    WPHardness.parameter_eq⟩

end AllIrrRAFCert
