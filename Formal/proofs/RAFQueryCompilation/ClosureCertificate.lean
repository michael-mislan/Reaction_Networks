import proofs.RAFQueryCompilation.ProducerCache

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

/-- Replay a proposed firing order. Disabled or unavailable entries have no effect. -/
def scheduleStep (Q : CRS M R) (S : Finset R) (pool : Finset M) (r : R) : Finset M :=
  if r ∈ S ∧ Q.inputs r ⊆ pool then pool ∪ Q.outputs r else pool

def replaySchedule (Q : CRS M R) (S : Finset R) (order : List R) : Finset M :=
  order.foldl (scheduleStep Q S) Q.food

theorem scheduleStep_sound (Q : CRS M R) (S : Finset R) (pool : Finset M)
    (hp : pool ⊆ finiteClosure Q S) (r : R) :
    scheduleStep Q S pool r ⊆ finiteClosure Q S := by
  by_cases h : r ∈ S ∧ Q.inputs r ⊆ pool
  · simp only [scheduleStep, if_pos h]
    exact Finset.union_subset hp (outputs_subset_finiteClosure Q S h.1 (h.2.trans hp))
  · simpa only [scheduleStep, if_neg h] using hp

omit [Fintype M] in
theorem scheduleStep_grows (Q : CRS M R) (S : Finset R) (pool : Finset M) (r : R) :
    pool ⊆ scheduleStep Q S pool r := by
  unfold scheduleStep
  split
  · exact Finset.subset_union_left
  · exact Finset.Subset.refl _

theorem replay_sound (Q : CRS M R) (S : Finset R) (order : List R) :
    replaySchedule Q S order ⊆ finiteClosure Q S := by
  have aux : ∀ (l : List R) (pool : Finset M), pool ⊆ finiteClosure Q S →
      l.foldl (scheduleStep Q S) pool ⊆ finiteClosure Q S := by
    intro l
    induction l with
    | nil => intro pool hp; exact hp
    | cons r rs ih =>
        intro pool hp
        exact ih _ (scheduleStep_sound Q S pool hp r)
  exact aux order Q.food (food_subset_finiteClosure Q S)

omit [Fintype M] in
theorem food_subset_replay (Q : CRS M R) (S : Finset R) (order : List R) :
    Q.food ⊆ replaySchedule Q S order := by
  have aux : ∀ (l : List R) (pool : Finset M), pool ⊆ l.foldl (scheduleStep Q S) pool := by
    intro l
    induction l with
    | nil => intro pool; exact Finset.Subset.refl _
    | cons r rs ih =>
        intro pool
        exact (scheduleStep_grows Q S pool r).trans (ih _)
  exact aux order Q.food

/-- A linear-size firing witness plus terminal closedness certifies least closure. -/
def checkClosure (Q : CRS M R) (S : Finset R) (order : List R) : Option (Finset M) :=
  let pool := replaySchedule Q S order
  if closureStep Q S pool = pool then some pool else none

theorem checkClosure_sound (Q : CRS M R) (S : Finset R) (order : List R)
    {pool : Finset M} (h : checkClosure Q S order = some pool) :
    pool = finiteClosure Q S := by
  dsimp only [checkClosure] at h
  split at h
  next hc =>
    have he : replaySchedule Q S order = pool := Option.some.inj h
    rw [← he]
    exact Finset.Subset.antisymm (replay_sound Q S order)
      (finiteClosure_le_closed Q S _ (food_subset_replay Q S order) (by rw [hc]))
  next => contradiction

end RAFQueryCompilation
