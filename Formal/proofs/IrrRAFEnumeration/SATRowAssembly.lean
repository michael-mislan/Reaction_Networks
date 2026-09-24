import proofs.IrrRAFEnumeration.SATReactionRows

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

theorem ofFn_sum_equiv {α : Type} {a b : Nat} (f : Fin (a+b) → α) :
    List.ofFn f = List.ofFn (fun i : Fin a => f (finSumFinEquiv (.inl i))) ++
      List.ofFn (fun j : Fin b => f (finSumFinEquiv (.inr j))) := by
  exact List.ofFn_add

theorem ofFn_prod_equiv {α : Type} {a b : Nat} (f : Fin (a*b) → α) :
    List.ofFn f = (List.ofFn (fun i : Fin a =>
      List.ofFn (fun j : Fin b => f (finProdFinEquiv (i,j))))).flatten := by
  simpa [finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using List.ofFn_mul f

def structuredSourceBody {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  List.ofFn (fun i : Fin (moleculeCount n m) => datum Φ (.inl i)) ++
    (List.ofFn (fun r : Fin (reactionCount n m) =>
      (List.ofFn (fun c : Fin 3 =>
        List.ofFn (fun x : Fin (moleculeCount n m) => datum Φ (.inr (r,c,x))))).flatten)).flatten

theorem sourceBody_eq_structured {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    sourceBody Φ = structuredSourceBody Φ := by
  unfold sourceBody structuredSourceBody
  rw [ofFn_sum_equiv]
  congr 1
  · apply congrArg List.ofFn
    funext i
    change datum Φ ((slotCode _ _).symm ((slotCode _ _) (.inl i))) = _
    rw [Equiv.symm_apply_apply]
  · rw [ofFn_prod_equiv]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext r
    rw [ofFn_prod_equiv]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext c
    apply congrArg List.ofFn
    funext x
    change datum Φ ((slotCode _ _).symm ((slotCode _ _) (.inr (r,c,x)))) = _
    rw [Equiv.symm_apply_apply]

theorem ofFn_three {α : Type} (f : Fin 3 → α) : List.ofFn f = [f 0,f 1,f 2] := by
  simp only [List.ofFn_succ, List.ofFn_zero]
  all_goals rfl

def reactionRows {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))) : List Bool :=
  moleculeRow ((crs (rules Φ)).inputs r) ++
    moleculeRow ((crs (rules Φ)).outputs r) ++
    List.ofFn (fun x : Fin (moleculeCount n m) =>
      decide ((moleculeCode _ _).symm x = Molecule.marker (catalystIndex r)))

theorem datum_channels_eq_rows {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (r : Fin (reactionCount n m)) :
    (List.ofFn (fun c : Fin 3 =>
      List.ofFn (fun x : Fin (moleculeCount n m) => datum Φ (.inr (r,c,x))))).flatten =
      reactionRows Φ ((reactionCode _ _).symm r) := by
  rw [ofFn_three]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
    datum, reactionRows, moleculeRow, Fin.reduceEq, ↓reduceIte, List.append_assoc]
  rfl

/-- The exact original source body is food followed by three full rows for
each reaction, in the same finite-sum order used by the executable encoding. -/
theorem sourceBody_eq_rows {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    sourceBody Φ = moleculeRow (crs (rules Φ)).food ++
      (List.ofFn (fun r : Fin (reactionCount n m) =>
        reactionRows Φ ((reactionCode _ _).symm r))).flatten := by
  rw [sourceBody_eq_structured]
  unfold structuredSourceBody
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext r
  exact datum_channels_eq_rows Φ r

end IrrRAFEnumeration.SATSource
