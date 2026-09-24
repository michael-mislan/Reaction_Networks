import proofs.IrrRAFEnumeration.RAFCompletion

namespace IrrRAFEnumeration

/-- The `i`th disjoint two-point edge. -/
def pairEdge {k : Nat} (i : Fin k) : Finset (Fin k × Bool) :=
  {(i, false), (i, true)}

/-- A compact family of `k` pairwise disjoint two-point sets. -/
def pairFamily (k : Nat) : Finset (Finset (Fin k × Bool)) :=
  Finset.univ.image pairEdge

/-- Select exactly one point from every pair. -/
def pairChoiceSet {k : Nat} (f : Fin k → Bool) : Finset (Fin k × Bool) :=
  Finset.univ.image fun i => (i, f i)

@[simp] theorem mem_pairChoiceSet {k : Nat} (f : Fin k → Bool)
    (p : Fin k × Bool) :
    p ∈ pairChoiceSet f ↔ f p.1 = p.2 := by
  constructor
  · intro hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    rfl
  · intro hp
    apply Finset.mem_image.mpr
    exact ⟨p.1, Finset.mem_univ _, by ext <;> simp [hp]⟩

/-- Every binary choice is a minimal hitting set of the disjoint-pair family. -/
theorem pairChoiceSet_minimal {k : Nat} (f : Fin k → Bool) :
    Minimal (Hits (pairFamily k)) (pairChoiceSet f) := by
  classical
  constructor
  · intro A hA
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hA
    exact Finset.not_disjoint_iff.mpr
      ⟨(i, f i), by simp, by cases f i <;> simp [pairEdge]⟩
  · intro K hKhits hKsub p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    have hedge : pairEdge i ∈ pairFamily k :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hmeet := Finset.not_disjoint_iff.mp (hKhits (pairEdge i) hedge)
    obtain ⟨y, hyK, hyedge⟩ := hmeet
    have hychoice := hKsub hyK
    simp only [pairEdge, Finset.mem_insert, Finset.mem_singleton] at hyedge
    rcases hyedge with rfl | rfl
    · have hf := (mem_pairChoiceSet f (i, false)).mp hychoice
      simpa [hf] using hyK
    · have hf := (mem_pairChoiceSet f (i, true)).mp hychoice
      simpa [hf] using hyK

theorem pairChoiceSet_injective {k : Nat} :
    Function.Injective (pairChoiceSet (k := k)) := by
  intro f g hfg
  funext i
  have hmem : (i, f i) ∈ pairChoiceSet g := by
    rw [← hfg]
    simp
  exact ((mem_pairChoiceSet g (i, f i)).mp hmem).symm

def pairChoiceFamily (k : Nat) : Finset (Finset (Fin k × Bool)) :=
  Finset.univ.image pairChoiceSet

theorem pairChoiceFamily_subset_blocker (k : Nat) :
    pairChoiceFamily k ⊆ blocker (pairFamily k) := by
  classical
  intro H hH
  obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hH
  exact mem_blocker.mpr (pairChoiceSet_minimal f)

theorem pairChoiceFamily_card (k : Nat) :
    (pairChoiceFamily k).card = 2 ^ k := by
  classical
  rw [pairChoiceFamily,
    Finset.card_image_iff.mpr fun f _ g _ hfg => pairChoiceSet_injective hfg]
  simp

/-- The negative completion frontier can be exponential even when the known
positive antichain consists of only `k` two-element sets. -/
theorem two_pow_le_pairFamily_blocker_card (k : Nat) :
    2 ^ k ≤ (blocker (pairFamily k)).card := by
  rw [← pairChoiceFamily_card k]
  exact Finset.card_le_card (pairChoiceFamily_subset_blocker k)

end IrrRAFEnumeration
