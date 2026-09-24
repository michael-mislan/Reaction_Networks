import proofs.DigraphRealizability.HornClosure
namespace DigraphRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- An injection selecting an available forced head for every minimal residual. -/
theorem residual_matching {G L : Set (Rule E)}
    (hGL : G ⊆ L) (hL : SingleHead L) :
    ∃ f : {B : Finset E // MinimalResidual G L B} → E,
      Function.Injective f ∧
      ∀ B, f B ∈ closure L B.val ∧ f B ∉ B.val ∧ f B ∉ Heads G := by
  classical
  have hn := fun B : {B : Finset E // MinimalResidual G L B} =>
    normalize hGL hL B.property
  choose q hq hb hr hf hc using hn
  refine ⟨fun B => (q B).2, ?_, ?_⟩
  · intro B C he
    have eq : q B = q C := hL (q B) (hq B) (q C) (hq C) he
    apply Subtype.ext
    exact (hc B).symm.trans ((congrArg (fun t : Rule E => closure G t.1) eq).trans (hc C))
  · intro B
    exact ⟨closure_models L B.val (q B) (hq B) ((hb B).trans (subset_closure L B.val)),
      hr B,hf B⟩
end DigraphRealizability

