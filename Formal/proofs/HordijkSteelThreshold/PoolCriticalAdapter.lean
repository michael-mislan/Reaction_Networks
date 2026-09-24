import proofs.HordijkSteelThreshold.AmbientShellInfluence

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- Every molecule in a self-consistent restricted pool also belongs to the
closure of the unrestricted exact seeded maxRAF. -/
theorem selfConsistentPool_subset_seededClosure {n : Nat}
    {bulk : Set (NonseedCoord n)} {J : Finset (PolymerSeedReaction n 2)}
    {C : Finset (Molecule n)}
    (hC : ReversiblePoolSelfConsistent bulk J C) :
    C ⊆ seededClosureMolecules bulk J := by
  intro x hx
  obtain ⟨k, hk⟩ := hC.2 x hx
  exact (mem_seededClosureMolecules bulk J x).mpr
    ⟨k, revClosureAt_mono_reactions _
      (poolSeededMaxRAF_subset_full bulk J C) k hk⟩

/-- A half-density self-consistent reversible catalyst pool is an exact
macroscopic seeded-bulk witness in the original source model. -/
theorem selfConsistentPool_implies_macro {n : Nat}
    {bulk : Set (NonseedCoord n)} {J : Finset (PolymerSeedReaction n 2)}
    {C : Finset (Molecule n)}
    (hC : ReversiblePoolSelfConsistent bulk J C)
    (hmacro : Fintype.card (Molecule n) ≤ 2 * C.card) :
    bulk ∈ SeededBulkMacroEvent n J := by
  exact hmacro.trans (Nat.mul_le_mul_left 2 <|
    Finset.card_le_card (selfConsistentPool_subset_seededClosure hC))

/-- The source-faithful construction event required by the zero-critical
route: some reversible self-consistent pool already has half density. -/
def MacroscopicSelfConsistentPoolEvent (n : Nat)
    (J : Finset (PolymerSeedReaction n 2)) :
    Set (Set (NonseedCoord n)) :=
  {bulk | ∃ C : Finset (Molecule n),
    ReversiblePoolSelfConsistent bulk J C ∧
      Fintype.card (Molecule n) ≤ 2 * C.card}

/-- Exact event containment reducing the low-side construction to positive
probability of a macroscopic self-consistent pool. -/
theorem macroscopicSelfConsistentPoolEvent_subset_seededMacro {n : Nat}
    (J : Finset (PolymerSeedReaction n 2)) :
    MacroscopicSelfConsistentPoolEvent n J ⊆ SeededBulkMacroEvent n J := by
  intro bulk hbulk
  obtain ⟨C, hC, hmacro⟩ := hbulk
  exact selfConsistentPool_implies_macro hC hmacro

/-- Restricting a nonempty exact seeded maxRAF to its own closure deletes no
catalytic witness. -/
theorem fullMaxRAF_isRAF_restrictedToOwnClosure {n : Nat}
    {bulk : Set (NonseedCoord n)} {J : Finset (PolymerSeedReaction n 2)}
    (hne : (gatewaySeededRAFFamily bulk J).Nonempty) :
    IsGatewaySeededRAF
      (restrictBulkToPool bulk (seededClosureMolecules bulk J)) J
      (gatewaySeededMaxRAF bulk J) := by
  have hfull := isGatewaySeededRAF_maxRAF bulk J hne
  refine ⟨hfull.1, hfull.2.1, ?_⟩
  intro r hr
  rcases hfull.2.2 r hr with hforced | ⟨x, k, hx, hcat⟩
  · exact Or.inl hforced
  · right
    refine ⟨x, k, hx, ?_⟩
    by_cases hseed : RevSeedReaction (binaryPolymerCRS n 2) r
    · simp [bulkCatalysis, hseed] at hcat
    · have hcoord : (x, ⟨r, hseed⟩) ∈ bulk := by
        simpa [bulkCatalysis, hseed] using hcat
      have hxC : x ∈ seededClosureMolecules bulk J :=
        (mem_seededClosureMolecules bulk J x).mpr ⟨k, hx⟩
      simpa [bulkCatalysis, hseed] using And.intro hcoord hxC

/-- The pool-restricted and unrestricted maxRAFs agree when the pool is the
unrestricted maxRAF's own molecule closure. -/
theorem poolMaxRAF_ownClosure_eq_full {n : Nat}
    {bulk : Set (NonseedCoord n)} {J : Finset (PolymerSeedReaction n 2)}
    (hne : (gatewaySeededRAFFamily bulk J).Nonempty) :
    poolSeededMaxRAF bulk J (seededClosureMolecules bulk J) =
      gatewaySeededMaxRAF bulk J := by
  apply Finset.Subset.antisymm
  · exact poolSeededMaxRAF_subset_full bulk J _
  · exact subset_gatewaySeededMaxRAF_of_isRAF _ J
      (fullMaxRAF_isRAF_restrictedToOwnClosure hne)

/-- A nonempty macroscopic seeded closure is itself a macroscopic
self-consistent pool.  Thus the pool formulation loses no source information. -/
theorem seededMacro_implies_macroscopicSelfConsistentPoolEvent {n : Nat}
    {bulk : Set (NonseedCoord n)} {J : Finset (PolymerSeedReaction n 2)}
    (hne : (gatewaySeededRAFFamily bulk J).Nonempty)
    (hmacro : bulk ∈ SeededBulkMacroEvent n J) :
    bulk ∈ MacroscopicSelfConsistentPoolEvent n J := by
  let C := seededClosureMolecules bulk J
  have hrestricted := fullMaxRAF_isRAF_restrictedToOwnClosure hne
  have hfamily :
      (gatewaySeededRAFFamily (restrictBulkToPool bulk C) J).Nonempty := by
    refine ⟨gatewaySeededMaxRAF bulk J, ?_⟩
    exact (mem_gatewaySeededRAFFamily _ J _).mpr hrestricted
  refine ⟨C, ⟨hfamily, ?_⟩, hmacro⟩
  intro x hx
  obtain ⟨k, hk⟩ := (mem_seededClosureMolecules bulk J x).mp hx
  rw [poolMaxRAF_ownClosure_eq_full hne]
  exact ⟨k, hk⟩

/-- On the nonempty seeded-family branch, macroscopic ignition is exactly the
existence of a macroscopic self-consistent reversible catalyst pool. -/
theorem seededMacro_iff_macroscopicSelfConsistentPoolEvent {n : Nat}
    {bulk : Set (NonseedCoord n)} {J : Finset (PolymerSeedReaction n 2)}
    (hne : (gatewaySeededRAFFamily bulk J).Nonempty) :
    bulk ∈ SeededBulkMacroEvent n J ↔
      bulk ∈ MacroscopicSelfConsistentPoolEvent n J := by
  constructor
  · exact seededMacro_implies_macroscopicSelfConsistentPoolEvent hne
  · intro hpool
    exact macroscopicSelfConsistentPoolEvent_subset_seededMacro J hpool

end HordijkSteelThreshold
