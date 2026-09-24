import proofs.HordijkSteelThreshold.GatewayCavity

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- A gateway is inert when its product is already food.  Its two factors are
food automatically, so forcing it cannot enlarge the initial closure. -/
def InertGateway {n : Nat} (r : PolymerSeedReaction n 2) : Prop :=
  reactionProduct r.1 ∈ binaryFood n 2

lemma revClosureStep_eq_food_of_side_iff {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R)
    (hside : ∀ r ∈ S,
      RevEnabledLhs Q Q.food r ↔ RevEnabledRhs Q Q.food r) :
    revClosureStep Q S Q.food = Q.food := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [revClosureStep, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨r, hr, hx⟩
    · exact hx
    · by_cases hl : RevEnabledLhs Q Q.food r
      · have hh := (hside r hr).mp hl
        simp [hl, hh] at hx
        exact hx.elim (fun hx => hh hx) (fun hx => hl hx)
      · have hh : ¬ RevEnabledRhs Q Q.food r := by
          intro hrhs
          exact hl ((hside r hr).mpr hrhs)
        simp [hl, hh] at hx
  · exact Finset.subset_union_left

lemma revClosureAt_eq_food_of_side_iff {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R)
    (hside : ∀ r ∈ S,
      RevEnabledLhs Q Q.food r ↔ RevEnabledRhs Q Q.food r) :
    ∀ k, revClosureAt Q S k = Q.food := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [revClosureAt, ih]
      exact revClosureStep_eq_food_of_side_iff Q S hside

theorem inert_forcing_closure_eq_food {n : Nat} {bulk : Set (NonseedCoord n)}
    {J : Finset (PolymerSeedReaction n 2)}
    (hJ : ∀ r ∈ J, InertGateway r)
    {S : Finset (Reaction n)} (hS : IsGatewaySeededRAF bulk J S) :
    ∀ k, revClosureAt (binaryPolymerCRS n 2) S k = binaryFood n 2 := by
  apply revClosureAt_eq_food_of_side_iff
  intro r hr
  by_cases hseed : RevSeedReaction (binaryPolymerCRS n 2) r
  · have hleft : reactionLeft r ∈ binaryFood n 2 ∧
        reactionRight r ∈ binaryFood n 2 :=
      (revSeedReaction_iff_food_factors r).mp hseed
    have hforced : GatewayForced J r := by
      rcases hS.2.2 r hr with hforced | hbulk
      · exact hforced
      · simp [bulkCatalysis, hseed] at hbulk
    obtain ⟨hseed', hrJ⟩ := hforced
    have hproduct : reactionProduct r ∈ binaryFood n 2 :=
      hJ ⟨r, hseed'⟩ hrJ
    have hl : RevEnabledLhs (binaryPolymerCRS n 2) (binaryFood n 2) r := by
      intro x hx
      simp only [binaryPolymerCRS, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hleft.1
      · exact hleft.2
    have hh : RevEnabledRhs (binaryPolymerCRS n 2) (binaryFood n 2) r := by
      simpa [RevEnabledRhs, binaryPolymerCRS] using hproduct
    exact iff_of_true hl hh
  · have hnleft : ¬ RevEnabledLhs (binaryPolymerCRS n 2)
        (binaryFood n 2) r := by
      intro hl
      exact hseed (Or.inl hl)
    have hnright : ¬ RevEnabledRhs (binaryPolymerCRS n 2)
        (binaryFood n 2) r := by
      intro hh
      exact hseed (Or.inr hh)
    exact iff_of_false hnleft hnright

theorem inert_forcing_seededRAF_subset {n : Nat} {bulk : Set (NonseedCoord n)}
    {J : Finset (PolymerSeedReaction n 2)}
    (hJ : ∀ r ∈ J, InertGateway r)
    {S : Finset (Reaction n)} (hS : IsGatewaySeededRAF bulk J S) :
    ∀ r ∈ S, ∃ hseed : RevSeedReaction (binaryPolymerCRS n 2) r,
      (⟨r, hseed⟩ : PolymerSeedReaction n 2) ∈ J := by
  intro r hr
  obtain ⟨k, hk⟩ := hS.2.1 r hr
  have hclosure := inert_forcing_closure_eq_food hJ hS k
  have hlhs : (binaryPolymerCRS n 2).lhs r ⊆
      (binaryPolymerCRS n 2).food := by
    intro x hx
    simpa [binaryPolymerCRS] using hclosure ▸
      hk (Finset.mem_union_left _ hx)
  have hseed : RevSeedReaction (binaryPolymerCRS n 2) r := Or.inl hlhs
  rcases hS.2.2 r hr with hforced | hbulk
  · obtain ⟨hseed', hrJ⟩ := hforced
    exact ⟨hseed', hrJ⟩
  · simp [bulkCatalysis, hseed] at hbulk

theorem singleton_inert_isGatewaySeededRAF {n : Nat}
    (bulk : Set (NonseedCoord n)) (r₀ : PolymerSeedReaction n 2)
    (hinert : InertGateway r₀) :
    IsGatewaySeededRAF bulk {r₀} {r₀.1} := by
  have hfac : reactionLeft r₀.1 ∈ binaryFood n 2 ∧
      reactionRight r₀.1 ∈ binaryFood n 2 :=
    (revSeedReaction_iff_food_factors r₀.1).mp r₀.2
  refine ⟨by simp, ?_, ?_⟩
  · intro r hr
    simp only [Finset.mem_singleton] at hr
    subst r
    refine ⟨0, ?_⟩
    intro x hx
    simp only [binaryPolymerCRS, Finset.union_singleton,
      Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [revClosureAt]
    change x ∈ binaryFood n 2
    rcases hx with rfl | rfl | rfl
    · exact hinert
    · exact hfac.1
    · exact hfac.2
  · intro r hr
    simp only [Finset.mem_singleton] at hr
    subst r
    exact Or.inl ⟨r₀.2, by simp⟩

/-- The seeded maxRAF of one inert gateway is exactly that one reaction,
independently of every nongateway catalysis coordinate. -/
theorem gatewaySeededMaxRAF_singleton_inert {n : Nat}
    (bulk : Set (NonseedCoord n)) (r₀ : PolymerSeedReaction n 2)
    (hinert : InertGateway r₀) :
    gatewaySeededMaxRAF bulk {r₀} = {r₀.1} := by
  apply Finset.Subset.antisymm
  · intro r hr
    simp only [gatewaySeededMaxRAF, Finset.mem_biUnion] at hr
    obtain ⟨S, hSF, hrS⟩ := hr
    have hS : IsGatewaySeededRAF bulk {r₀} S :=
      (mem_gatewaySeededRAFFamily bulk {r₀} S).mp hSF
    have hJ : ∀ q ∈ ({r₀} : Finset (PolymerSeedReaction n 2)),
        InertGateway q := by
      intro q hq
      simp only [Finset.mem_singleton] at hq
      subst q
      exact hinert
    obtain ⟨hseed, hrJ⟩ := inert_forcing_seededRAF_subset hJ hS r hrS
    have heq : (⟨r, hseed⟩ : PolymerSeedReaction n 2) = r₀ := by
      simpa using hrJ
    simp only [Finset.mem_singleton]
    exact congrArg Subtype.val heq
  · intro r hr
    simp only [Finset.mem_singleton] at hr
    subst r
    exact subset_gatewaySeededMaxRAF_of_isRAF bulk {r₀}
      (singleton_inert_isGatewaySeededRAF bulk r₀ hinert) (by simp)

end HordijkSteelThreshold
