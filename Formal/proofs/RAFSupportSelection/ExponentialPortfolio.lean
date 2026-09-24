import proofs.RAFSupportSelection.IntrinsicDependence
import proofs.RAFSupportSelection.Objective

namespace RAFSupportSelection.Paired
open RAF RAF.Frankl RAFQueryCompilation
variable {I J : Type*} [DecidableEq I] [Fintype I] [Fintype J]
abbrev Reaction (I : Type*) := Option (I × Bool)
abbrev Molecule (I : Type*) := Option (I ⊕ Reaction I)

def source : CRS (Molecule I) (Reaction I) where
  food := {none}
  inputs r := match r with
    | some _ => {none}
    | none => Finset.univ.image (fun i => some (Sum.inl i))
  outputs r := match r with
    | some (i,b) => {some (Sum.inl i), some (Sum.inr (some (i,b)))}
    | none => {some (Sum.inr none)}

def cats (_ : Reaction I) : Finset (Molecule I) := {none}
def parents (a : I → Bool) : Reaction I → Finset (Reaction I)
  | some _ => ∅
  | none => Finset.univ.image (fun i => some (i,a i))
def ranks : Reaction I → ℕ
  | some _ => 0
  | none => 1

theorem source_certificate (a : I → Bool) :
    RankedSupport (source : CRS (Molecule I) (Reaction I)) cats Finset.univ (parents a) ranks := by
  constructor
  · intro r _ x hx
    cases r with
    | some t => exact Or.inl hx
    | none =>
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact Or.inr ⟨some (i,a i), Finset.mem_univ _, by simp [parents],
        by simp [ranks], by simp [source]⟩
  · intro r _
    exact ⟨none, by simp [cats], Or.inl (by simp [source])⟩

theorem normalize (p : Reaction I → Finset (Reaction I)) (rank : Reaction I → ℕ)
    (hw : RankedSupport source cats Finset.univ p rank) :
    ∃ a : I → Bool, ∀ r, parents a r ⊆ p r := by
  classical
  have hh : ∀ i, ∃ b, some (i,b) ∈ p none := by
    intro i
    rcases hw.1 none (Finset.mem_univ _) (some (Sum.inl i))
      (by simp [source]) with hf | ⟨r, _, hp, _, ho⟩
    · simp [source] at hf
    · cases r with
      | none => simp [source] at ho
      | some t =>
        obtain ⟨j,b⟩ := t
        have he : i = j := by simpa [source] using ho
        subst j
        exact ⟨b,hp⟩
  choose a ha using hh
  refine ⟨a, ?_⟩
  intro r t ht
  cases r with
  | some u => simp [parents] at ht
  | none =>
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact ha i

def region (a : I → Bool) (K : Finset (Reaction I)) : Finset (Reaction I) :=
  K ∪ (if ∃ i, some (i,a i) ∈ K then {none} else ∅)

@[simp] theorem mem_region_some (a : I → Bool) (K : Finset (Reaction I)) (t : I × Bool) :
    some t ∈ region a K ↔ some t ∈ K := by
  classical
  unfold region
  split <;> simp

theorem cone_eq_region (a : I → Bool) (K : Finset (Reaction I)) :
    selectedCone Finset.univ (parents a) K = region a K := by
  classical
  apply Finset.Subset.antisymm
  · apply selectedCone_le
    · intro r hr
      exact Finset.mem_union_left _ (Finset.mem_inter.mp hr).1
    · intro r _ hh
      cases r with
      | some t => simp [parents] at hh
      | none =>
        obtain ⟨t, ht⟩ := hh
        obtain ⟨i, _, he⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ht).1
        subst t
        have hi : some (i,a i) ∈ K := by
          simpa only [mem_region_some] using (Finset.mem_inter.mp ht).2
        simp [region, show ∃ i, some (i,a i) ∈ K from ⟨i,hi⟩]
  · intro r hr
    rcases Finset.mem_union.mp hr with hk | he
    · exact selectedCone_seed _ _ _ (Finset.mem_inter.mpr ⟨hk,Finset.mem_univ _⟩)
    · by_cases h : ∃ i, some (i,a i) ∈ K
      · have hrn : r = none := by simpa [h] using he
        subst r
        obtain ⟨i,hi⟩ := h
        exact cone_edge _ _ _ (Finset.mem_univ _) (by simp [parents])
          (selectedCone_seed _ _ _ (Finset.mem_inter.mpr ⟨hi,Finset.mem_univ _⟩))
      · simp [h] at he

def deletion (a : I → Bool) : Finset (Reaction I) :=
  Finset.univ.image (fun i => some (i, !(a i)))

theorem mem_deletion (a : I → Bool) (i : I) (b : Bool) :
    some (i,b) ∈ deletion a ↔ b ≠ a i := by
  simp only [deletion, Finset.mem_image, Finset.mem_univ, true_and, Option.some.injEq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨j,hji,hb⟩
    subst j
    cases h : a i <;> simp_all
  · intro hb
    refine ⟨i,rfl,?_⟩
    cases h : a i <;> cases b <;> simp_all

theorem deletion_exact_loss (a : I → Bool) :
    actualLoss source cats Finset.univ (deletion a) = deletion a := by
  have he : selectedCone Finset.univ (parents a) (deletion a) = deletion a := by
    rw [cone_eq_region]
    have hn : ¬ ∃ i, some (i,a i) ∈ deletion a := by simp [mem_deletion]
    simp [region,hn]
  apply Finset.Subset.antisymm
  · simpa only [he] using
      loss_subset_selectedCone source cats Finset.univ (deletion a) _ _ (source_certificate a)
  · simpa only [Finset.inter_univ] using actualLoss_seed source cats Finset.univ (deletion a)

theorem source_baseline :
    prune (source : CRS (Molecule I) (Reaction I)) (fun x r => x ∈ cats r) Finset.univ =
      Finset.univ := by
  exact ranked_retained_fixed source cats Finset.univ Finset.univ
    (parents (fun _ => false)) ranks (source_certificate _) (Finset.Subset.refl _)
    (fun _ _ => Finset.inter_subset_right)

/-- The complete assignment pool is exact for every deletion set. -/
theorem full_portfolio_exact (K : Finset (Reaction I)) (r : Reaction I) :
    r ∈ actualLoss source cats Finset.univ K ↔
      ∀ a : I → Bool, r ∈ selectedCone Finset.univ (parents a) K := by
  constructor
  · intro hr a
    exact loss_subset_selectedCone source cats _ _ _ _ (source_certificate a) hr
  · intro hall
    obtain ⟨p, rank, hw, he⟩ := perfect_query_certificate source cats Finset.univ K source_baseline
    obtain ⟨a,ha⟩ := normalize p rank hw
    rw [actualLoss, ← he]
    exact selectedCone_mono_parents _ _ _ _ (fun r _ => ha r) (hall a)

/-- Arbitrary valid certificates, not merely normalized assignments, obey the
exponential lower bound for exact regions under arbitrary deletions. -/
theorem exponential_lower_bound
    (p : J → Reaction I → Finset (Reaction I)) (rank : J → Reaction I → ℕ)
    (hw : ∀ j, RankedSupport source cats Finset.univ (p j) (rank j))
    (hsize : Fintype.card J < 2 ^ Fintype.card I) :
    ∃ K : Finset (Reaction I), none ∉ actualLoss source cats Finset.univ K ∧
      ∀ j, none ∈ selectedCone Finset.univ (p j) K := by
  classical
  choose a ha using fun j => normalize (p j) (rank j) (hw j)
  have hmiss : ∃ b : I → Bool, ∀ j, a j ≠ b := by
    by_contra hn
    push Not at hn
    have hs : Function.Surjective a := hn
    have hc := Fintype.card_le_of_surjective a hs
    simp only [Fintype.card_fun, Fintype.card_bool] at hc
    omega
  obtain ⟨b,hb⟩ := hmiss
  refine ⟨deletion b, ?_, ?_⟩
  · rw [deletion_exact_loss]
    simp [deletion]
  · intro j
    have hdiff : ∃ i, a j i ≠ b i := Function.ne_iff.mp (hb j)
    obtain ⟨i,hi⟩ := hdiff
    have hd : some (i,a j i) ∈ deletion b := (mem_deletion b i _).mpr hi
    have hc : none ∈ selectedCone Finset.univ (parents (a j)) (deletion b) := by
      rw [cone_eq_region]
      simp [region, show ∃ i, some (i,a j i) ∈ deletion b from ⟨i,hd⟩]
    exact selectedCone_mono_parents _ _ _ _ (fun r _ => ha j r) hc

theorem assignment_pool_card : Fintype.card (I → Bool) = 2 ^ Fintype.card I := by simp
omit [DecidableEq I] in
theorem reaction_count : Fintype.card (Reaction I) = 2 * Fintype.card I + 1 := by
  simp [Reaction, Nat.mul_comm, Nat.add_comm]

/-- The same family needs only two complementary certificates for singleton regions. -/
theorem two_certificates_singletons (d r : Reaction I) :
    r ∈ actualLoss source cats Finset.univ {d} ↔
      r ∈ selectedCone Finset.univ (parents (fun _ : I => false)) {d} ∧
      r ∈ selectedCone Finset.univ (parents (fun _ : I => true)) {d} := by
  rw [full_portfolio_exact]
  constructor
  · intro h
    exact ⟨h _, h _⟩
  · rintro ⟨hf,ht⟩ a
    rw [cone_eq_region] at hf ht ⊢
    cases r with
    | some t => simpa only [mem_region_some] using hf
    | none =>
      cases d with
      | none => simp [region]
      | some t =>
        obtain ⟨i,b⟩ := t
        cases b <;> simp [region] at hf ht

end RAFSupportSelection.Paired
