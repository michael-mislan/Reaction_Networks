import proofs.RAFStructuredEnumeration.Resolution

namespace RAFStructuredEnumeration
open RAF RAFQueryCompilation

theorem sink_eq_of_common {R : Type*} (K : Finset R) (d : R → Finset R)
    {A B : Finset R} (hA : A ∈ sinkCandidates K d) (hB : B ∈ sinkCandidates K d)
    {z : R} (hzA : z ∈ A) (hzB : z ∈ B) : A = B := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨_, haret⟩ := Finset.mem_filter.mp ha
  obtain ⟨_, hbret⟩ := Finset.mem_filter.mp hb
  obtain ⟨_, haz⟩ := (mem_reachable K d a z).mp hzA
  obtain ⟨_, hbz⟩ := (mem_reachable K d b z).mp hzB
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨hxK, hax⟩ := (mem_reachable K d a x).mp hx
    exact (mem_reachable K d b x).mpr ⟨hxK, hbz.trans ((haret z hzA).trans hax)⟩
  · intro x hx
    obtain ⟨hxK, hbx⟩ := (mem_reachable K d b x).mp hx
    exact (mem_reachable K d a x).mpr ⟨hxK, haz.trans ((hbret z hzB).trans hbx)⟩

theorem sink_frequency_le_one {R : Type*} [DecidableEq R] (K : Finset R) (d : R → Finset R) (r : R) :
    ((sinkCandidates K d).filter (fun I => r ∈ I)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro A hA B hB
  exact sink_eq_of_common K d (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1
    (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2

variable {M R : Type*} [DecidableEq M] [DecidableEq R] [LinearOrder M]
  [Fintype M] [Fintype R]

theorem catalogue_frequency_bound (Q : CRS M R) (cats : R → Finset M) (r : R) :
    ((supplierCatalogue Q cats).filter (fun I => r ∈ I)).card ≤
      (resolutions Q cats (originalMax Q cats)).card := by
  classical
  let sigmas := resolutions Q cats (originalMax Q cats)
  let f := fun pc : (M → Option R) × (R → Option M) =>
    (resolutionCandidates Q (originalMax Q cats) pc.1 pc.2).filter (fun I => r ∈ I)
  have hsub : (supplierCatalogue Q cats).filter (fun I => r ∈ I) ⊆ sigmas.biUnion f := by
    intro I hI
    obtain ⟨hI, hrI⟩ := Finset.mem_filter.mp hI
    have hraw := (Finset.mem_filter.mp hI).1
    obtain ⟨pc, hpc, hcan⟩ := Finset.mem_biUnion.mp hraw
    exact Finset.mem_biUnion.mpr ⟨pc,hpc,Finset.mem_filter.mpr ⟨hcan,hrI⟩⟩
  calc
    _ ≤ (sigmas.biUnion f).card := Finset.card_le_card hsub
    _ ≤ ∑ pc ∈ sigmas, (f pc).card := Finset.card_biUnion_le
    _ ≤ ∑ _pc ∈ sigmas, 1 := Finset.sum_le_sum (fun pc _ => sink_frequency_le_one _ _ r)
    _ = _ := by simp [sigmas]

theorem catalogue_membership_bound (Q : CRS M R) (cats : R → Finset M) :
    (∑ I ∈ supplierCatalogue Q cats, I.card) ≤ (originalMax Q cats).card *
      (resolutions Q cats (originalMax Q cats)).card := by
  classical
  have hsub (I : Finset R) (hI : I ∈ supplierCatalogue Q cats) : I ⊆ originalMax Q cats :=
    raf_subset_evaluate Q (fun x r => x ∈ cats r) (Finset.subset_univ I)
      ((supplierCatalogue_correct Q cats I).mp hI).1
  calc
    (∑ I ∈ supplierCatalogue Q cats, I.card) =
        ∑ I ∈ supplierCatalogue Q cats, ∑ r ∈ originalMax Q cats, if r ∈ I then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro I hI
      exact Finset.card_eq_sum_ite (hsub I hI)
    _ = ∑ r ∈ originalMax Q cats, ((supplierCatalogue Q cats).filter (fun I => r ∈ I)).card := by
      rw [Finset.sum_comm]
      simp
    _ ≤ ∑ _r ∈ originalMax Q cats, (resolutions Q cats (originalMax Q cats)).card :=
      Finset.sum_le_sum (fun r _ => catalogue_frequency_bound Q cats r)
    _ = _ := by simp

end RAFStructuredEnumeration
