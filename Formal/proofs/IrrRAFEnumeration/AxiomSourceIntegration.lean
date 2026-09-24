import proofs.AllIrrRAFCert.Publication
import proofs.IrrRAFEnumeration.EnumerationTimeout

namespace IrrRAFEnumeration

open RAF

/-- The certification paper and enumeration use exactly the same RAF semantics. -/
theorem exactCertification_iff_family_eq {M R : Type*} [Fintype R]
    [DecidableEq M] [DecidableEq R] (Q : CRS M R) (C : Catalysis M R)
    (L : Finset (Finset R)) :
    AllIrrRAFCert.ExactIrrRAFCertification Q C L ↔ irrRAFFamily Q C = L := by
  constructor
  · rintro ⟨hv, hc⟩
    apply Finset.Subset.antisymm
    · intro S hS
      exact hc S ((mem_irrRAFFamily Q C S).mp hS)
    · intro S hS
      exact (mem_irrRAFFamily Q C S).mpr (hv S hS)
  · intro he
    constructor
    · intro S hS
      exact (mem_irrRAFFamily Q C S).mp (he.symm ▸ hS)
    · intro S hS
      exact he ▸ (mem_irrRAFFamily Q C S).mpr hS

namespace AxiomSource
open AllIrrRAFCert.WPHardness

/-- Finite negative transfer. Runtime realization and source NP-completeness
are not assumptions hidden inside this semantic theorem. -/
theorem deadline_decides_smallGenerating {k n q : Nat} (A : System n q)
    (run : Nat → Option (Finset (Finset (Rxn k n q))))
    (cost : Finset (Finset (Rxn k n q)) → Nat) (bound : Nat → Nat)
    (hcorrect : SATSource.BoundedRunCorrect (irrRAFFamily (crs A) cat) run)
    (htotal : ∃ t ≤ bound (cost (irrRAFFamily (crs A) cat)),
      run t = some (irrRAFFamily (crs A) cat)) :
    SmallGenerating A k ↔
      run (bound (cost (listedFamily k n q))) ≠ some (listedFamily k n q) := by
  rw [AllIrrRAFCert.axiom_iff_not_exactCertification,
    exactCertification_iff_family_eq]
  exact not_congr (SATSource.timeout_eq_baseline_iff
    (irrRAFFamily (crs A) cat) (listedFamily k n q) run cost bound hcorrect htotal).symm

end AxiomSource
end IrrRAFEnumeration

namespace AllIrrRAFCert.WPHardness
open RAF
variable {k n q : Nat}

theorem full_signal_stage_one (A : System n q) (v : Vertex k n) :
    Mol.signal v ∈ closureAt (crs A) Finset.univ 1 := by
  apply emit (r := .selector v)
  · exact Finset.mem_univ _
  · exact Finset.Subset.rfl
  · simp [crs]

theorem full_decoder_stage_two (A : System n q) (v : Vertex k n)
    {x : Mol k n} (hx : x ∈ (crs A).outputs (.colorGate v)) :
    x ∈ closureAt (crs A) Finset.univ 2 := by
  apply emit A Finset.univ (r := .colorGate v) (t := 1) (Finset.mem_univ _) _ hx
  intro y hy
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
  exact full_signal_stage_one A (v.1,w)

theorem full_close_inputs_stage_two (A : System n q) (hk : 0 < k) :
    (crs A).inputs (Rxn.close : Rxn k n q) ⊆ closureAt (crs A) Finset.univ 2 := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact full_decoder_stage_two A (i,0) (by simp [crs])
  · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    exact full_decoder_stage_two A (⟨0,hk⟩,u) (by simp [crs])

/-- No generating-set assumption: all reactions produce the global catalyst
by the third food-closure stage whenever at least one slot is present. -/
theorem full_globalCat_stage_three (A : System n q) (hk : 0 < k) :
    (Mol.globalCat : Mol k n) ∈ closureAt (crs A) Finset.univ 3 :=
  emit A _ (r := .close) (Finset.mem_univ _) (full_close_inputs_stage_two A hk)
    (by simp [crs])

theorem full_source_isRAF (A : System n q) (hk : 0 < k) :
    IsRAF (crs A) cat (Finset.univ : Finset (Rxn k n q)) := by
  refine ⟨⟨.close,Finset.mem_univ _⟩,?_,?_⟩
  · intro r _
    cases r with
    | selector v => exact ⟨0,Finset.Subset.rfl⟩
    | colorGate v =>
      refine ⟨1,?_⟩
      intro x hx
      obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hx
      exact full_signal_stage_one A (v.1,w)
    | rule j =>
      refine ⟨2,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact time_mono A _ (by omega : 0 ≤ 2) (by simp [closureAt,crs])
      · obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
        exact full_decoder_stage_two A (⟨0,hk⟩,u) (by simp [crs])
    | close => exact ⟨2,full_close_inputs_stage_two A hk⟩
  · intro r _
    exact ⟨.globalCat,3,full_globalCat_stage_three A hk,trivial⟩

end AllIrrRAFCert.WPHardness
