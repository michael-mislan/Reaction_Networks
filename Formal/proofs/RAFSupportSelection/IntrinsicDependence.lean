import proofs.RAFSupportSelection.PerfectQuery

namespace RAFSupportSelection
open RAF RAF.Frankl RAFQueryCompilation
variable {R : Type*} [DecidableEq R] [Fintype R]

theorem cone_edge (S : Finset R) (p : R → Finset R) (K : Finset R)
    {a r : R} (hr : r ∈ S) (ha : a ∈ p r) (hK : a ∈ selectedCone S p K) :
    r ∈ selectedCone S p K := by
  rw [← selectedCone_fixed S p K]
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr
    ⟨hr, a, Finset.mem_inter.mpr ⟨ha, hK⟩⟩)

theorem cone_mono_seed (S : Finset R) (p : R → Finset R) {K D : Finset R}
    (h : K ⊆ D) : selectedCone S p K ⊆ selectedCone S p D := by
  apply selectedCone_le
  · intro r hr
    exact selectedCone_seed S p D (Finset.mem_inter.mpr
      ⟨h (Finset.mem_inter.mp hr).1, (Finset.mem_inter.mp hr).2⟩)
  · intro r hr hh
    obtain ⟨a, ha⟩ := hh
    exact cone_edge S p D hr (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp ha).2

theorem cone_singleton_trans (S : Finset R) (p : R → Finset R) {a b c : R}
    (hab : b ∈ selectedCone S p {a}) (hbc : c ∈ selectedCone S p {b}) :
    c ∈ selectedCone S p {a} := by
  apply selectedCone_le S p {b} (selectedCone S p {a}) _ _ hbc
  · intro r hr
    have : r = b := Finset.mem_singleton.mp (Finset.mem_inter.mp hr).1
    simpa only [this] using hab
  · intro r hr hh
    obtain ⟨t, ht⟩ := hh
    exact cone_edge S p {a} hr (Finset.mem_inter.mp ht).1 (Finset.mem_inter.mp ht).2

theorem cone_mem_iff_singleton (S : Finset R) (p : R → Finset R) (K : Finset R) (r : R) :
    r ∈ selectedCone S p K ↔ ∃ d ∈ K ∩ S, r ∈ selectedCone S p {d} := by
  classical
  constructor
  · intro hr
    have hle : selectedCone S p K ⊆ (K ∩ S).biUnion (fun d => selectedCone S p {d}) := by
      apply selectedCone_le
      · intro d hd
        exact Finset.mem_biUnion.mpr ⟨d, hd, selectedCone_seed S p {d}
          (Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, (Finset.mem_inter.mp hd).2⟩)⟩
      · intro t ht hh
        obtain ⟨a, ha⟩ := hh
        obtain ⟨d, hd, had⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp ha).2
        exact Finset.mem_biUnion.mpr ⟨d, hd, cone_edge S p {d} ht (Finset.mem_inter.mp ha).1 had⟩
    exact Finset.mem_biUnion.mp (hle hr)
  · rintro ⟨d, hd, hr⟩
    exact cone_mono_seed S p (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp hd).1) hr

variable {M : Type*} [DecidableEq M] [Fintype M]

def actualLoss (Q : CRS M R) (cats : R → Finset M) (S K : Finset R) : Finset R :=
  S \ evaluate Q (fun x r => x ∈ cats r) (S \ K)

omit [Fintype R] in
theorem actualLoss_seed (Q : CRS M R) (cats : R → Finset M) (S K : Finset R) :
    K ∩ S ⊆ actualLoss Q cats S K := by
  intro r hr
  refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hr).2, ?_⟩
  intro he
  exact (Finset.mem_sdiff.mp (evaluate_subset Q _ _ he)).2 (Finset.mem_inter.mp hr).1

theorem actualLoss_mono (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (hS : prune Q (fun x r => x ∈ cats r) S = S) {K D : Finset R} (hKD : K ⊆ D) :
    actualLoss Q cats S K ⊆ actualLoss Q cats S D := by
  intro r hr
  apply (loss_iff_every_certificate Q cats S D hS r).mpr
  intro p rank hw
  exact cone_mono_seed S p hKD (loss_subset_selectedCone Q cats S K p rank hw hr)

def indispensable (Q : CRS M R) (cats : R → Finset M) (S : Finset R) (d r : R) : Prop :=
  r ∈ actualLoss Q cats S {d}

omit [Fintype R] in
theorem indispensable_reflexive (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (r : R) (hr : r ∈ S) : indispensable Q cats S r r :=
  actualLoss_seed Q cats S {r} (Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, hr⟩)

theorem indispensable_transitive (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (hS : prune Q (fun x r => x ∈ cats r) S = S) {a b c : R}
    (hab : indispensable Q cats S a b) (hbc : indispensable Q cats S b c) :
    indispensable Q cats S a c := by
  apply (loss_iff_every_certificate Q cats S {a} hS c).mpr
  intro p rank hw
  exact cone_singleton_trans S p
    (loss_subset_selectedCone Q cats S {a} p rank hw hab)
    (loss_subset_selectedCone Q cats S {b} p rank hw hbc)

theorem mutual_indispensability_equivalence (Q : CRS M R) (cats : R → Finset M)
    (S : Finset R) (hS : prune Q (fun x r => x ∈ cats r) S = S) :
    Equivalence (fun a b : {r // r ∈ S} =>
      indispensable Q cats S a b ∧ indispensable Q cats S b a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact ⟨indispensable_reflexive Q cats S a a.property,
      indispensable_reflexive Q cats S a a.property⟩
  · intro a b h
    exact h.symm
  · intro a b c hab hbc
    exact ⟨indispensable_transitive Q cats S hS hab.1 hbc.1,
      indispensable_transitive Q cats S hS hbc.2 hab.2⟩

theorem perfect_singletons_all_deletions (Q : CRS M R) (cats : R → Finset M)
    (S : Finset R) (hS : prune Q (fun x r => x ∈ cats r) S = S)
    (p : R → Finset R) (rank : R → ℕ) (hw : RankedSupport Q cats S p rank)
    (hs : ∀ d ∈ S, selectedCone S p {d} = actualLoss Q cats S {d}) (K : Finset R) :
    selectedCone S p K = actualLoss Q cats S K := by
  apply Finset.Subset.antisymm _ (loss_subset_selectedCone Q cats S K p rank hw)
  intro r hr
  obtain ⟨d, hd, hrd⟩ := (cone_mem_iff_singleton S p K r).mp hr
  rw [hs d (Finset.mem_inter.mp hd).2] at hrd
  exact actualLoss_mono Q cats S hS
    (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp hd).1) hrd

def deletionSynergy (Q : CRS M R) (cats : R → Finset M) (S K : Finset R) : Finset R :=
  actualLoss Q cats S K \ (K ∩ S).biUnion (fun d => actualLoss Q cats S {d})

theorem synergy_obstructs_perfect_singletons (Q : CRS M R) (cats : R → Finset M)
    (S : Finset R) (hS : prune Q (fun x r => x ∈ cats r) S = S) (K : Finset R)
    (hne : (deletionSynergy Q cats S K).Nonempty) :
    ¬ ∃ p rank, RankedSupport Q cats S p rank ∧
      ∀ d ∈ S, selectedCone S p {d} = actualLoss Q cats S {d} := by
  rintro ⟨p, rank, hw, hs⟩
  obtain ⟨r, hr⟩ := hne
  obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hr
  rw [← perfect_singletons_all_deletions Q cats S hS p rank hw hs K] at hl
  obtain ⟨d, hd, hrd⟩ := (cone_mem_iff_singleton S p K r).mp hl
  exact hn (Finset.mem_biUnion.mpr ⟨d, hd, (hs d (Finset.mem_inter.mp hd).2) ▸ hrd⟩)

theorem expected_cone_decomposition {T : Type*} [Fintype T]
    (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (p : R → Finset R) (rank : R → ℕ) (hw : RankedSupport Q cats S p rank)
    (queries : T → Finset R) (weight : T → ℝ) :
    ∑ t, weight t * (selectedCone S p (queries t)).card =
      (∑ t, weight t * (actualLoss Q cats S (queries t)).card) +
      ∑ t, weight t * (selectedCone S p (queries t) \ actualLoss Q cats S (queries t)).card := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  have hc := Finset.card_sdiff_add_card_eq_card
    (loss_subset_selectedCone Q cats S (queries t) p rank hw)
  change (selectedCone S p (queries t) \ actualLoss Q cats S (queries t)).card +
    (actualLoss Q cats S (queries t)).card = _ at hc
  have hc' := congrArg (fun n : ℕ => (n : ℝ)) hc
  push_cast at hc'
  rw [← hc']
  ring

end RAFSupportSelection
