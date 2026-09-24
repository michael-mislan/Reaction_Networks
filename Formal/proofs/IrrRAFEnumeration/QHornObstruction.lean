import proofs.IrrRAFEnumeration.CompletionCNF

namespace IrrRAFEnumeration

/-- The executable doubled-weight test for a q-Horn certificate.  Weights are
`0,1,2`; positive literals contribute their weight and negative literals
contribute its complement to `2`. -/
def CompletionQHornWeight {α : Type*} [DecidableEq α]
    (H G : Finset (Finset α)) (w : α → Fin 3) : Prop :=
  (H.filter fun E => E.sum (fun x => (w x).val) ≤ 2).card = H.card ∧
    (G.filter fun A => A.sum (fun x => 2 - (w x).val) ≤ 2).card = G.card

instance completionQHornWeightDecidable {α : Type*} [DecidableEq α]
    (H G : Finset (Finset α)) (w : α → Fin 3) :
    Decidable (CompletionQHornWeight H G w) := by
  unfold CompletionQHornWeight
  infer_instance

abbrev QWeight4 := Fin 3 × Fin 3 × Fin 3 × Fin 3

def qWeight4Fun (w : QWeight4) : Fin 4 → Fin 3 :=
  Fin.cases w.1 <| Fin.cases w.2.1 <| Fin.cases w.2.2.1 <|
    Fin.cases w.2.2.2 Fin.elim0

/-- A fully executable finite search over the `3^4` possible weights. -/
def HornCounterexampleHasQHornWeight : Prop :=
  ((Finset.univ : Finset QWeight4).filter fun w =>
    CompletionQHornWeight hornCounterexampleH hornCounterexampleG
      (qWeight4Fun w)).Nonempty

/-- The least renamable-Horn obstruction is already outside the strictly
larger q-Horn class. -/
theorem hornCounterexample_not_qHorn :
    ¬ HornCounterexampleHasQHornWeight := by
  unfold HornCounterexampleHasQHornWeight
  native_decide

end IrrRAFEnumeration
