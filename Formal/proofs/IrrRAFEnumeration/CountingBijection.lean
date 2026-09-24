import proofs.IrrRAFEnumeration.RAFCompletion

namespace IrrRAFEnumeration

open RAF
open MinRAFApprox
open MinRAFApprox.SetCoverSource
open MinRAFApprox.SetCoverSource.IndexedHypergraph

/-- The finite family of all minimal transversals of an indexed hypergraph. -/
noncomputable def minimalTransversalFamily {e v : Nat}
    (H : IndexedHypergraph e v) : Finset (Finset (Fin v)) := by
  classical
  exact Finset.univ.powerset.filter H.MinimalTransversal

@[simp] theorem mem_minimalTransversalFamily {e v : Nat}
    (H : IndexedHypergraph e v) (C : Finset (Fin v)) :
    C ∈ minimalTransversalFamily H ↔ H.MinimalTransversal C := by
  classical
  simp [minimalTransversalFamily]

/-- Every irrRAF of the literal hypergraph source is canonical, so its entire
irrRAF family is exactly the image of the minimal-transversal family. -/
theorem source_irrRAFFamily_eq_image {e v : Nat}
    (H : IndexedHypergraph e v) (he : 0 < e) :
    irrRAFFamily (crs e v 1) (catalysis (toSetCover H)) =
      (minimalTransversalFamily H).image
        (MinRAFApprox.canonicalRAF (U := Fin e) (K := Fin 1)) := by
  classical
  ext S
  simp only [mem_irrRAFFamily, Finset.mem_image]
  constructor
  · intro hS
    obtain ⟨C, hcover, hEq⟩ :=
      (setCoverSource_raf_iff (toSetCover H) he (by omega) S).mp hS.1
    have hCanonical : IsIrreducibleRAF
        (crs e v 1) (catalysis (toSetCover H))
        (MinRAFApprox.canonicalRAF (U := Fin e) (K := Fin 1) C) := by
      rw [← hEq]
      exact hS
    have hC : H.MinimalTransversal C :=
      (irreducibleRAF_iff_minimalTransversal H he C).mp hCanonical
    exact ⟨C, (mem_minimalTransversalFamily H C).mpr hC, hEq.symm⟩
  · rintro ⟨C, hC, rfl⟩
    exact (irreducibleRAF_iff_minimalTransversal H he C).mpr
      ((mem_minimalTransversalFamily H C).mp hC)

theorem canonicalRAF_injective {m n M : Nat} (hM : 0 < M) :
    Function.Injective
      (MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M)
        : Finset (Fin n) → Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M))) := by
  intro C D hEq
  apply Finset.Subset.antisymm
  · exact (canonicalRAF_subset_iff (m := m) hM).mp (by rw [hEq])
  · exact (canonicalRAF_subset_iff (m := m) hM).mp (by rw [← hEq])

/-- Parsimonious counting reduction: the number of irrRAFs in the explicit
source CRS equals the number of minimal transversals of the input hypergraph. -/
theorem source_irrRAFFamily_card_eq_minimalTransversalFamily_card
    {e v : Nat} (H : IndexedHypergraph e v) (he : 0 < e) :
    (irrRAFFamily (crs e v 1) (catalysis (toSetCover H))).card =
      (minimalTransversalFamily H).card := by
  classical
  rw [source_irrRAFFamily_eq_image H he]
  exact Finset.card_image_iff.mpr fun C _ D _ hEq =>
    canonicalRAF_injective (m := e) (n := v) (M := 1) (by omega) hEq

end IrrRAFEnumeration
