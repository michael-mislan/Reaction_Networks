import proofs.RAF.Frankl.ReactionExtension

namespace RAF.Frankl
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

/-- Every non-food substrate incidence, including self-incidences, increases rank. -/
def SubstrateRank (Q : CRS M R) (rank : R → ℕ) : Prop :=
  ∀ p r x, x ∈ Q.outputs p → x ∈ Q.inputs r → x ∉ Q.food → rank p < rank r

def LocalSupply (Q : CRS M R) (C : Catalysis M R) (W : Finset R) (r : R) : Prop :=
  (∀ x ∈ Q.inputs r, x ∉ Q.food → ∃ p ∈ W, x ∈ Q.outputs p) ∧
    extensionSupport Q C W r

def CompleteSupplier (Q : CRS M R) (C : Catalysis M R) (p r : R) : Prop :=
  (Q.inputs r \ Q.food) ⊆ Q.outputs p ∧
    ((∃ x ∈ Q.food, C x r) ∨ ∃ x ∈ Q.outputs p, C x r)

omit [Fintype R] [DecidableEq R] in
theorem localSupply_mono (Q : CRS M R) (C : Catalysis M R)
    {A B : Finset R} (h : A ⊆ B) {r : R} :
    LocalSupply Q C A r → LocalSupply Q C B r := by
  rintro ⟨hs,hc⟩
  exact ⟨fun x hx hn => by obtain ⟨p,hp,ho⟩ := hs x hx hn; exact ⟨p,h hp,ho⟩,
    extensionSupport_mono Q C h hc⟩

omit [Fintype R] [DecidableEq R] in
theorem completeSupplier_local (Q : CRS M R) (C : Catalysis M R)
    {W : Finset R} {p r : R} (h : CompleteSupplier Q C p r) (hp : p ∈ W) :
    LocalSupply Q C W r := by
  refine ⟨fun x hx hn => ⟨p,hp,h.1 (Finset.mem_sdiff.mpr ⟨hx,hn⟩)⟩, ?_⟩
  rcases h.2 with hf | ho
  · exact Or.inl hf
  · exact Or.inr ⟨p,hp,ho⟩

omit [Fintype R] [DecidableEq R] in
theorem ranked_closure_mono (Q : CRS M R) (W : Finset R) :
    ∀ {i j}, i ≤ j → closureAt Q W i ⊆ closureAt Q W j := by
  intro i j hij
  induction hij with
  | refl => exact fun _ hx => hx
  | @step j hj ih =>
    exact fun x hx => Finset.mem_union_left _ (ih hx)

omit [Fintype R] [DecidableEq R] in
theorem ranked_foodGenerated (Q : CRS M R) (rank : R → ℕ)
    (hrank : SubstrateRank Q rank) (W : Finset R)
    (hs : ∀ r ∈ W, ∀ x ∈ Q.inputs r, x ∉ Q.food → ∃ p ∈ W, x ∈ Q.outputs p) :
    FoodGenerated Q W := by
  have hen : ∀ n r, rank r = n → r ∈ W → Q.inputs r ⊆ closureAt Q W n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro r he hr x hx
      by_cases hf : x ∈ Q.food
      · exact ranked_closure_mono Q W (Nat.zero_le n) hf
      · obtain ⟨p,hp,ho⟩ := hs r hr x hx hf
        have hlt : rank p < n := he ▸ hrank p r x ho hx hf
        have hEnabled : Enabled Q (closureAt Q W (rank p)) p := ih (rank p) hlt p rfl hp
        have hm : x ∈ closureAt Q W (rank p + 1) := by
          simp only [closureAt,closureStep,Finset.mem_union,Finset.mem_biUnion]
          exact Or.inr ⟨p,hp,by simpa [hEnabled] using ho⟩
        exact ranked_closure_mono Q W hlt hm
  exact fun r hr => ⟨rank r,hen (rank r) r rfl hr⟩

theorem ranked_fixed_iff (Q : CRS M R) (C : Catalysis M R)
    (rank : R → ℕ) (hrank : SubstrateRank Q rank) (W : Finset R) :
    W ∈ fixedFamily Q C ↔ ∀ r ∈ W, LocalSupply Q C W r := by
  rw [fixedFamily_iff_food_support]
  constructor
  · rintro ⟨hfg,hcat⟩ r hr
    refine ⟨?_,hcat r hr⟩
    intro x hx hn
    obtain ⟨k,hk⟩ := hfg r hr
    exact (mem_closureAt_imp_food_or_output Q W (hk hx)).resolve_left hn
  · intro h
    exact ⟨ranked_foodGenerated Q rank hrank W (fun r hr => (h r hr).1),
      fun r hr => (h r hr).2⟩

end RAF.Frankl
