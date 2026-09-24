import proofs.SmallCusp.Equivalence.SimpleCuspInvariant
import proofs.SmallCusp.Equivalence.SpeciesSwap
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

namespace SmallCusp

/-- The unique candidate positive scale is read from the first nonzero source
stoichiometric coordinate.  Source reactions are non-self, so at least one
coordinate is available. -/
def codedRayScale (C D : CodedBimolNetwork) (r s : Fin 5) : ℚ :=
  if codedStoich C 0 r ≠ 0 then
    (codedStoich D 0 s : ℚ) / (codedStoich C 0 r : ℚ)
  else
    (codedStoich D 1 s : ℚ) / (codedStoich C 1 r : ℚ)

/-- A finite, decidable witness for simple equivalence of coded sources. -/
def CodedSimplyEquivalent (C D : CodedBimolNetwork) : Prop :=
  ∃ e : Equiv.Perm (Fin 5),
    (∀ r, (D.reaction (e r)).1 = (C.reaction r).1) ∧
    (∀ r, 0 < codedRayScale C D r (e r)) ∧
    (∀ i r, (codedStoich D i (e r) : ℚ) =
      codedRayScale C D r (e r) * (codedStoich C i r : ℚ))

instance codedSimplyEquivalent_decidable (C D : CodedBimolNetwork) :
    Decidable (CodedSimplyEquivalent C D) := by
  unfold CodedSimplyEquivalent
  infer_instance

theorem codedSimplyEquivalent_implies_simplyEquivalent
    {C D : CodedBimolNetwork} (h : CodedSimplyEquivalent C D) :
    SimplyEquivalent C.toNetwork D.toNetwork := by
  rcases h with ⟨e, hreact, hpos, hstoich⟩
  let scale : Fin 5 → ℝ := fun r => (codedRayScale C D r (e r) : ℝ)
  refine ⟨e, scale, ?_, ?_, ?_⟩
  · intro r
    change (0 : ℝ) < (codedRayScale C D r (e r) : ℝ)
    exact_mod_cast hpos r
  · intro r
    change (D.reaction (e r)).1.decode = (C.reaction r).1.decode
    exact congrArg BimolComplexCode.decode (hreact r)
  · intro i r
    change ((codedStoich D i (e r) : ℤ) : ℝ) =
      scale r * ((codedStoich C i r : ℤ) : ℝ)
    dsimp [scale]
    exact_mod_cast hstoich i r

theorem codedSimplyEquivalent_admitsTransverseCusp_iff
    {C D : CodedBimolNetwork} (h : CodedSimplyEquivalent C D) :
    AdmitsTransverseCusp C.toNetwork ↔ AdmitsTransverseCusp D.toNetwork :=
  simplyEquivalent_admitsTransverseCusp_iff
    (codedSimplyEquivalent_implies_simplyEquivalent h)

/-- Two coded sources have the same literal generator set, independently of
the arbitrary ordering of their five reactions. -/
def SameCodedReactionSet (C D : CodedBimolNetwork) : Prop :=
  Set.range C.reaction = Set.range D.reaction

private theorem bimolComplex_decode_injective :
    Function.Injective BimolComplexCode.decode := by
  intro a b h
  cases a <;> cases b <;>
    simp [BimolComplexCode.decode] at h ⊢

private theorem codedRayScale_of_reaction_eq
    (C D : CodedBimolNetwork) (r s : Fin 5)
    (h : D.reaction s = C.reaction r) :
    codedRayScale C D r s = 1 := by
  have hn : (C.reaction r).1 ≠ (C.reaction r).2 := C.noSelf r
  rw [codedRayScale]
  have hs0 : codedStoich D 0 s = codedStoich C 0 r := by
    simp [codedStoich, h]
  have hs1 : codedStoich D 1 s = codedStoich C 1 r := by
    simp [codedStoich, h]
  rw [hs0, hs1]
  by_cases h0 : codedStoich C 0 r ≠ 0
  · simp [h0]
  · simp only [h0, if_false]
    have h1 : codedStoich C 1 r ≠ 0 := by
      intro hz
      apply hn
      apply bimolComplex_decode_injective
      funext i
      have h0z : codedStoich C 0 r = 0 := not_ne_iff.mp h0
      fin_cases i
      · simp only [codedStoich] at h0z
        change (C.reaction r).1.decode 0 = (C.reaction r).2.decode 0
        omega
      · simp only [codedStoich] at hz
        change (C.reaction r).1.decode 1 = (C.reaction r).2.decode 1
        omega
    simp [h1]

/-- Equality of the unordered generator sets supplies the unique reaction
permutation and unit positive ray scales. -/
theorem sameCodedReactionSet_implies_codedSimplyEquivalent
    {C D : CodedBimolNetwork} (hset : SameCodedReactionSet C D) :
    CodedSimplyEquivalent C D := by
  classical
  have hexists : ∀ r : Fin 5, ∃ s : Fin 5, D.reaction s = C.reaction r := by
    intro r
    have hr : C.reaction r ∈ Set.range C.reaction := ⟨r, rfl⟩
    rw [hset] at hr
    rcases hr with ⟨s, hs⟩
    exact ⟨s, hs⟩
  let f : Fin 5 → Fin 5 := fun r ↦ Classical.choose (hexists r)
  have hf : ∀ r, D.reaction (f r) = C.reaction r := fun r ↦
    Classical.choose_spec (hexists r)
  have hinj : Function.Injective f := by
    intro r t hrt
    apply C.injective
    rw [← hf r, ← hf t, hrt]
  let e : Equiv.Perm (Fin 5) := Equiv.ofBijective f
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have he : ∀ r, D.reaction (e r) = C.reaction r := by
    intro r
    exact hf r
  refine ⟨e, ?_, ?_, ?_⟩
  · intro r
    exact congrArg Prod.fst (he r)
  · intro r
    rw [codedRayScale_of_reaction_eq C D r (e r) (he r)]
    norm_num
  · intro i r
    rw [codedRayScale_of_reaction_eq C D r (e r) (he r)]
    norm_num [codedStoich, he r]

def swapCodedNetwork (C : CodedBimolNetwork) : CodedBimolNetwork where
  reaction r := swapBimolReaction (C.reaction r)
  noSelf := by
    intro r h
    apply C.noSelf r
    apply BimolComplexCode.swap_injective
    exact h
  injective := by
    intro r s h
    apply C.injective
    exact swapBimolReaction_injective h

theorem swapCodedNetwork_toNetwork (C : CodedBimolNetwork) :
    (swapCodedNetwork C).toNetwork = swapSpeciesNetwork C.toNetwork := by
  cases C with
  | mk reaction noSelf injective =>
    simp only [swapCodedNetwork, CodedBimolNetwork.toNetwork,
      swapSpeciesNetwork]
    congr
    · funext r i
      cases h : (reaction r).1 <;> fin_cases i <;>
        simp [swapBimolReaction, h, BimolComplexCode.decode,
          BimolComplexCode.swap, swapComplex]
    · funext r i
      cases h : (reaction r).2 <;> fin_cases i <;>
        simp [swapBimolReaction, h, BimolComplexCode.decode,
          BimolComplexCode.swap, swapComplex]

theorem swapCodedNetwork_admitsTransverseCusp_iff (C : CodedBimolNetwork) :
    AdmitsTransverseCusp (swapCodedNetwork C).toNetwork ↔
      AdmitsTransverseCusp C.toNetwork := by
  rw [swapCodedNetwork_toNetwork, swapSpecies_admitsTransverseCusp_iff]

end SmallCusp
