import proofs.AllIrrRAFCert.WPHardness.Forward
namespace AllIrrRAFCert.WPHardness
open RAF RAF.Frankl
open MinRAFApprox.SetCoverSource (IsIrreducibleRAF)
variable {k n q : Nat}

theorem derives_mono (A : System n q) {B D : Finset (Fin (n+2))} (h : B ⊆ D)
    {u : Fin (n+2)} (hu : Derives A B u) : Derives A D u := by
  induction hu with
  | seed hu => exact Derives.seed (h hu)
  | rule j _ ih => exact Derives.rule j ih

theorem cover_by_slots (B : Finset (Fin (n+2))) (hB : B.card ≤ k) :
    ∃ a : Fin k → Fin (n+2), B ⊆ seeds a := by
  classical
  let e : {u // u ∈ B} ≃ Fin B.card := Fintype.equivFinOfCardEq (by simp)
  let a : Fin k → Fin (n+2) := fun i =>
    if h : i.val < B.card then (e.symm ⟨i.val,h⟩).val else 0
  refine ⟨a,?_⟩
  intro u hu
  let j := e ⟨u,hu⟩
  let i : Fin k := ⟨j.val,lt_of_lt_of_le j.isLt hB⟩
  apply Finset.mem_image.mpr
  refine ⟨i,Finset.mem_univ _,?_⟩
  change (if h : j.val < B.card then (e.symm ⟨j.val,h⟩).val else 0) = u
  simp only [dif_pos j.isLt]
  exact congrArg Subtype.val (e.symm_apply_apply ⟨u,hu⟩)

def SmallGenerating (A : System n q) (k : Nat) : Prop :=
  ∃ B : Finset (Fin (n+2)), B.card ≤ k ∧ ∀ u, Derives A B u

theorem smallGenerating_iff_slots (A : System n q) :
    SmallGenerating A k ↔ ∃ a : Fin k → Fin (n+2), Generates A a := by
  constructor
  · rintro ⟨B,hB,hgen⟩
    obtain ⟨a,ha⟩ := cover_by_slots B hB
    exact ⟨a,fun u => derives_mono A ha (hgen u)⟩
  · rintro ⟨a,ha⟩
    exact ⟨seeds a,seeds_card_le a,ha⟩

def listedFamily (k n q : Nat) : Finset (Finset (Rxn k n q)) :=
  Finset.univ.image guard
theorem parameter_eq : (listedFamily k n q).card = k := by
  rw [listedFamily,Finset.card_image_of_injective _ guards_injective]
  simp
theorem listed_valid (A : System n q) :
    ∀ S ∈ listedFamily k n q, IsIrreducibleRAF (crs A) cat S := by
  intro S hS
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
  exact guard_isIrrRAF A i
theorem smallGenerating_iff_extra (A : System n q) :
    SmallGenerating A k ↔ Extra (k := k) A :=
  (smallGenerating_iff_slots A).trans (generating_iff_extra A)

def rxnEquiv : Rxn k n q ≃ (Vertex k n ⊕ Vertex k n ⊕ Fin q ⊕ Unit) where
  toFun
    | .selector v => .inl v
    | .colorGate v => .inr (.inl v)
    | .rule j => .inr (.inr (.inl j))
    | .close => .inr (.inr (.inr ()))
  invFun
    | .inl v => .selector v
    | .inr (.inl v) => .colorGate v
    | .inr (.inr (.inl j)) => .rule j
    | .inr (.inr (.inr _)) => .close
  left_inv := by intro r; cases r <;> rfl
  right_inv := by rintro (v | v | j | u) <;> rfl
def molEquiv : Mol k n ≃ (Unit ⊕ Vertex k n ⊕ Vertex k n ⊕ Fin k ⊕ Fin (n+2) ⊕ Unit) where
  toFun
    | .food => .inl ()
    | .signal v => .inr (.inl v)
    | .guardCat v => .inr (.inr (.inl v))
    | .colorOK i => .inr (.inr (.inr (.inl i)))
    | .statement u => .inr (.inr (.inr (.inr (.inl u))))
    | .globalCat => .inr (.inr (.inr (.inr (.inr ()))))
  invFun
    | .inl _ => .food
    | .inr (.inl v) => .signal v
    | .inr (.inr (.inl v)) => .guardCat v
    | .inr (.inr (.inr (.inl i))) => .colorOK i
    | .inr (.inr (.inr (.inr (.inl u)))) => .statement u
    | .inr (.inr (.inr (.inr (.inr _)))) => .globalCat
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro (u | v | v | i | j | u) <;> rfl
theorem reaction_count : Fintype.card (Rxn k n q) = 2*(k*(n+2))+q+1 := by
  rw [Fintype.card_congr rxnEquiv]
  simp only [Fintype.card_sum,Fintype.card_unit,Vertex,Fintype.card_prod,Fintype.card_fin]
  ring
theorem molecule_count : Fintype.card (Mol k n) = 2+2*(k*(n+2))+k+(n+2) := by
  rw [Fintype.card_congr molEquiv]
  simp only [Fintype.card_sum,Fintype.card_unit,Vertex,Fintype.card_prod,Fintype.card_fin]
  ring
def encodingCells (k n q : Nat) := Fintype.card (Mol k n) +
  (3*Fintype.card (Mol k n)+k)*Fintype.card (Rxn k n q)
theorem encoding_polynomial : encodingCells k n q =
    (2+2*(k*(n+2))+k+(n+2)) + (3*(2+2*(k*(n+2))+k+(n+2))+k)*(2*(k*(n+2))+q+1) := by
  simp only [encodingCells,molecule_count,reaction_count]
end AllIrrRAFCert.WPHardness
