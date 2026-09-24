import proofs.RAFQueryCompilation.RankedWitness

namespace RAFSupportSelection
open RAF RAF.Frankl RAFQueryCompilation

variable {R : Type*} [DecidableEq R] [Fintype R]

def selectedStep (S : Finset R) (p : R → Finset R) (D : Finset R) : Finset R :=
  D ∪ S.filter (fun r => (p r ∩ D).Nonempty)

def selectedCone (S : Finset R) (p : R → Finset R) (K : Finset R) : Finset R :=
  settle (selectedStep S p) (Fintype.card R) (K ∩ S)

omit [Fintype R] in
theorem selectedStep_mono (S : Finset R) (p : R → Finset R) :
    Monotone (selectedStep S p) := by
  intro A B hab r hr
  rcases Finset.mem_union.mp hr with hr | hr
  · exact Finset.mem_union_left _ (hab hr)
  · obtain ⟨hrS, t, ht⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨hrS, t, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ht).1, hab (Finset.mem_inter.mp ht).2⟩⟩)

theorem selectedCone_fixed (S : Finset R) (p : R → Finset R) (K : Finset R) :
    selectedStep S p (selectedCone S p K) = selectedCone S p K :=
  settle_grow_fixed _ (fun _ => Finset.subset_union_left) _ _ (by omega)

theorem selectedCone_seed (S : Finset R) (p : R → Finset R) (K : Finset R) :
    K ∩ S ⊆ selectedCone S p K :=
  subset_settle _ (fun _ => Finset.subset_union_left) _ _

theorem selectedCone_le (S : Finset R) (p : R → Finset R) (K B : Finset R)
    (hK : K ∩ S ⊆ B) (hB : ∀ r ∈ S, (p r ∩ B).Nonempty → r ∈ B) :
    selectedCone S p K ⊆ B := by
  apply settle_le_closed _ (selectedStep_mono S p) _ _ _ hK
  intro r hr
  rcases Finset.mem_union.mp hr with hr | hr
  · exact hr
  · exact hB r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2

theorem selectedCone_subset (S : Finset R) (p : R → Finset R) (K : Finset R) :
    selectedCone S p K ⊆ S :=
  selectedCone_le S p K S Finset.inter_subset_right (fun _ hr _ => hr)

theorem selectedCone_retained (S : Finset R) (p : R → Finset R) (K : Finset R) :
    ∀ r ∈ S \ selectedCone S p K, p r ∩ S ⊆ S \ selectedCone S p K := by
  intro r hr t ht
  obtain ⟨hrS, hrD⟩ := Finset.mem_sdiff.mp hr
  obtain ⟨htp, htS⟩ := Finset.mem_inter.mp ht
  refine Finset.mem_sdiff.mpr ⟨htS, ?_⟩
  intro htD
  apply hrD
  rw [← selectedCone_fixed S p K]
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr
    ⟨hrS, t, Finset.mem_inter.mpr ⟨htp, htD⟩⟩)

variable {M : Type*} [DecidableEq M] [Fintype M]

theorem loss_subset_selectedCone (Q : CRS M R) (cats : R → Finset M)
    (S K : Finset R) (p : R → Finset R) (rank : R → ℕ)
    (hw : RankedSupport Q cats S p rank) :
    S \ evaluate Q (fun x r => x ∈ cats r) (S \ K) ⊆ selectedCone S p K := by
  have hfix := ranked_retained_fixed Q cats S (S \ selectedCone S p K) p rank hw
    Finset.sdiff_subset (selectedCone_retained S p K)
  have hsub : S \ selectedCone S p K ⊆ S \ K := by
    intro r hr
    obtain ⟨hrS, hn⟩ := Finset.mem_sdiff.mp hr
    exact Finset.mem_sdiff.mpr ⟨hrS, fun hk => hn
      (selectedCone_seed S p K (Finset.mem_inter.mpr ⟨hk, hrS⟩))⟩
  have hs := supported_subset_evaluate Q (fun x r => x ∈ cats r) hsub
    (fixed_supported Q (fun x r => x ∈ cats r) hfix)
  intro r hr
  obtain ⟨hrS, hn⟩ := Finset.mem_sdiff.mp hr
  by_contra hh
  exact hn (hs (Finset.mem_sdiff.mpr ⟨hrS, hh⟩))

end RAFSupportSelection
