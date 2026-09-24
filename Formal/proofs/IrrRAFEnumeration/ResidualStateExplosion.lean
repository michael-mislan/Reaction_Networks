import proofs.IrrRAFEnumeration.FiniteDuality

namespace IrrRAFEnumeration

/-- The low edge of the `i`th choice-memory triangle. -/
def memoryLowEdge {k : Nat} (i : Fin k) :
    Finset (Fin k × Option Bool) :=
  {(i, some false), (i, some true)}

/-- A high edge joins one choice vertex to the marker. -/
def memoryHighEdge {k : Nat} (i : Fin k) (b : Bool) :
    Finset (Fin k × Option Bool) :=
  {(i, some b), (i, none)}

def choiceMemoryFamily (k : Nat) :
    Finset (Finset (Fin k × Option Bool)) :=
  Finset.univ.image memoryLowEdge ∪
    (Finset.univ ×ˢ Finset.univ).image fun ib => memoryHighEdge ib.1 ib.2

/-- Delete one of the two choice vertices in every triangle. -/
def memoryDeletion {k : Nat} (f : Fin k → Bool) :
    Finset (Fin k × Option Bool) :=
  Finset.univ.image fun i => (i, some (f i))

/-- The canonical residual family after a binary deletion choice. -/
def memoryResidual {k : Nat} (f : Fin k → Bool) :
    Finset (Finset (Fin k × Option Bool)) :=
  (choiceMemoryFamily k).filter fun E => Disjoint E (memoryDeletion f)

@[simp] theorem mem_memoryDeletion {k : Nat} (f : Fin k → Bool)
    (p : Fin k × Option Bool) :
    p ∈ memoryDeletion f ↔ p.2 = some (f p.1) := by
  constructor
  · intro hp
    obtain ⟨i, -, h⟩ := Finset.mem_image.mp hp
    simp [← h]
  · intro hp
    apply Finset.mem_image.mpr
    exact ⟨p.1, Finset.mem_univ _, by ext <;> simp [hp]⟩

theorem memoryHighEdge_mem {k : Nat} (i : Fin k) (b : Bool) :
    memoryHighEdge i b ∈ choiceMemoryFamily k := by
  classical
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨(i, b), by simp, rfl⟩

@[simp] theorem memoryHighEdge_disjoint_deletion_iff {k : Nat}
    (f : Fin k → Bool) (i : Fin k) (b : Bool) :
    Disjoint (memoryHighEdge i b) (memoryDeletion f) ↔ b ≠ f i := by
  classical
  constructor
  · intro hdis hbf
    have hedge : (i, some b) ∈ memoryHighEdge i b := by
      simp [memoryHighEdge]
    have hdelete : (i, some b) ∈ memoryDeletion f := by
      rw [mem_memoryDeletion]
      simp [hbf]
    exact (Finset.disjoint_left.mp hdis) hedge hdelete
  · intro hne
    rw [Finset.disjoint_left]
    intro x hxEdge hxDelete
    simp only [memoryHighEdge, Finset.mem_insert, Finset.mem_singleton] at hxEdge
    rcases hxEdge with rfl | rfl
    · exact hne (Option.some.inj ((mem_memoryDeletion f _).mp hxDelete))
    · have hfalse := (mem_memoryDeletion f _).mp hxDelete
      simp at hfalse

@[simp] theorem memoryHighEdge_mem_residual_iff {k : Nat}
    (f : Fin k → Bool) (i : Fin k) (b : Bool) :
    memoryHighEdge i b ∈ memoryResidual f ↔ b ≠ f i := by
  classical
  simp [memoryResidual, memoryHighEdge_mem]

/-- Different binary deletion histories leave different canonical residual
families; the surviving high edge in any differing triangle records the bit. -/
theorem memoryResidual_injective {k : Nat} :
    Function.Injective (memoryResidual (k := k)) := by
  intro f g hfg
  funext i
  by_contra hne
  have hmemF : memoryHighEdge i (g i) ∈ memoryResidual f := by
    rw [memoryHighEdge_mem_residual_iff]
    exact Ne.symm hne
  have hmemG : memoryHighEdge i (g i) ∈ memoryResidual g := by
    rw [← hfg]
    exact hmemF
  exact ((memoryHighEdge_mem_residual_iff g i (g i)).mp hmemG) rfl

def memoryResidualFamily (k : Nat) :
    Finset (Finset (Finset (Fin k × Option Bool))) :=
  Finset.univ.image memoryResidual

/-- With only three displayed two-point sets per triangle, the residual-state
space already contains one distinct state for every binary history. -/
theorem memoryResidualFamily_card (k : Nat) :
    (memoryResidualFamily k).card = 2 ^ k := by
  classical
  rw [memoryResidualFamily,
    Finset.card_image_iff.mpr fun f _ g _ h => memoryResidual_injective h]
  simp

end IrrRAFEnumeration
