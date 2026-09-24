import proofs.RAFSupportSelection.OneLayer
import proofs.RAFSupportSelection.Objective

namespace RAFSupportSelection.OneLayer
open RAF RAF.Frankl RAFQueryCompilation

variable {P C : Type*} [DecidableEq P] [DecidableEq C] [Fintype P] [Fintype C]

abbrev Molecule (P C : Type*) := Option (P ⊕ (C ⊕ C))

/-- Arbitrary overlapping allowed-producer lists. Every reaction also has its own
private product; catalyst food is fixed and every producer is food-generated. -/
def source (allowed : C → Finset P) : CRS (Molecule P C) (P ⊕ C) where
  food := {none}
  inputs r := match r with
    | .inl _ => {none}
    | .inr c => {some (Sum.inr (Sum.inl c))}
  outputs r := match r with
    | .inl a => {some (Sum.inl a)} ∪
        (Finset.univ.filter (fun c => a ∈ allowed c)).image
          (fun c => some (Sum.inr (Sum.inl c)))
    | .inr c => {some (Sum.inr (Sum.inr c))}

def foodCats (_ : P ⊕ C) : Finset (Molecule P C) := {none}

def layerRank : P ⊕ C → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem source_certificate (allowed : C → Finset P) (choice : C → P)
    (hc : ∀ c, choice c ∈ allowed c) :
    RankedSupport (source allowed) foodCats Finset.univ (parents choice) layerRank := by
  constructor
  · intro r _ x hx
    cases r with
    | inl a => exact Or.inl hx
    | inr c =>
      have he : x = some (Sum.inr (Sum.inl c)) := by simpa [source] using hx
      subst x
      right
      refine ⟨Sum.inl (choice c), Finset.mem_univ _, ?_, by simp [layerRank], ?_⟩
      · simp [parents]
      · simp [source, hc]
  · intro r _
    exact ⟨none, by simp [foodCats], Or.inl (by simp [source])⟩

/-- Any ranked certificate for this literal source contains an allowed producer
parent for each consumer, irrespective of its extra parents or rank choices. -/
theorem normalize_source_certificate (allowed : C → Finset P)
    (p : P ⊕ C → Finset (P ⊕ C)) (rank : P ⊕ C → ℕ)
    (hw : RankedSupport (source allowed) foodCats Finset.univ p rank) :
    ∃ choice : C → P, (∀ c, choice c ∈ allowed c) ∧
      ∀ r, parents choice r ⊆ p r := by
  classical
  have he : ∀ c, ∃ a, a ∈ allowed c ∧ Sum.inl a ∈ p (Sum.inr c) := by
    intro c
    rcases hw.1 (Sum.inr c) (Finset.mem_univ _) (some (Sum.inr (Sum.inl c)))
      (by simp [source]) with hf | ⟨r, _, hp, _, hout⟩
    · simp [source] at hf
    · cases r with
      | inl a =>
        refine ⟨a, ?_, hp⟩
        simpa [source] using hout
      | inr d => simp [source] at hout
  choose choice hc hp using he
  refine ⟨choice, hc, ?_⟩
  intro r
  cases r with
  | inl a => simp [parents]
  | inr c => simpa [parents] using hp c

variable [LinearOrder P]

/-- Executable minimum weight, then minimum identifier tie-breaking. -/
def chooseMin (w : P → ℕ) (A : Finset P) (hA : A.Nonempty) : P :=
  (A.filter (fun a => w a = (A.image w).min' (hA.image w))).min' (by
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (Finset.min'_mem (A.image w) (hA.image w))
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, he⟩⟩)

omit [DecidableEq P] [Fintype P] in
theorem chooseMin_mem (w : P → ℕ) (A : Finset P) (hA : A.Nonempty) :
    chooseMin w A hA ∈ A := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

omit [DecidableEq P] [Fintype P] in
theorem chooseMin_le (w : P → ℕ) (A : Finset P) (hA : A.Nonempty) (a : P) (ha : a ∈ A) :
    w (chooseMin w A hA) ≤ w a := by
  have he : w (chooseMin w A hA) = (A.image w).min' (hA.image w) := by
    unfold chooseMin
    exact (Finset.mem_filter.mp (Finset.min'_mem
      (A.filter (fun a => w a = (A.image w).min' (hA.image w))) _)).2
  rw [he]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem automatic_selector (w : P ⊕ C → ℕ) (allowed : C → Finset P)
    (hne : ∀ c, (allowed c).Nonempty) :
    let choice := fun c => chooseMin (fun a => w (Sum.inl a)) (allowed c) (hne c)
    RankedSupport (source allowed) foodCats Finset.univ (parents choice) layerRank ∧
      ∀ other : C → P, (∀ c, other c ∈ allowed c) → cost w choice ≤ cost w other := by
  dsimp only
  constructor
  · exact source_certificate allowed _ (fun c => chooseMin_mem _ _ (hne c))
  · intro other ho
    exact minimum_weight_optimal w allowed _
      (fun c a ha => chooseMin_le (fun a => w (Sum.inl a)) _ (hne c) a ha) other ho

def select (w : P ⊕ C → ℕ) (allowed : C → Finset P) (hne : ∀ c, (allowed c).Nonempty) : C → P :=
  fun c => chooseMin (fun a => w (Sum.inl a)) (allowed c) (hne c)

/-- Optimality against every source-valid ranked certificate, including arbitrary
extra parents and arbitrary natural ranks. Normalization is proved from the source. -/
theorem automatic_selector_globally_optimal (w : P ⊕ C → ℕ) (allowed : C → Finset P)
    (hne : ∀ c, (allowed c).Nonempty) :
    RankedSupport (source allowed) foodCats Finset.univ (parents (select w allowed hne)) layerRank ∧
      ∀ p rank, RankedSupport (source allowed) foodCats Finset.univ p rank →
        weightedReach Finset.univ (parents (select w allowed hne)) w ≤ weightedReach Finset.univ p w := by
  obtain ⟨hv, hopt⟩ := automatic_selector w allowed hne
  refine ⟨hv, ?_⟩
  intro p rank hw
  obtain ⟨other, ho, hp⟩ := normalize_source_certificate allowed p rank hw
  have hm := weightedReach_mono Finset.univ (parents other) p w (fun r _ => hp r)
  exact (hopt other ho).trans hm

end RAFSupportSelection.OneLayer
