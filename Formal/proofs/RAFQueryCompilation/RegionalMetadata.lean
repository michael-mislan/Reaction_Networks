import proofs.RAFQueryCompilation.ChargedLocal

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

structure RegionalMetadata where
  successorEntries : ℕ
  needsEntries : ℕ
  outputEntries : ℕ
  inputArity : ℕ
  outputArity : ℕ
  catalystArity : ℕ

/-- Six finite-region passes over cached source/index row cardinalities. -/
def collectRegionalMetadata (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M) (E : Finset R) : RegionalMetadata :=
  ⟨∑ r ∈ E, (succ r).card, ∑ r ∈ E, (needs r).card, ∑ r ∈ E, (Q.outputs r).card,
    E.sup (fun r => (Q.inputs r).card), E.sup (fun r => (Q.outputs r).card),
    E.sup (fun r => (cats r).card)⟩

def metadataCharge (E : Finset R) : ℕ := 1+6*E.card

def metadataRegionCharge (md : RegionalMetadata) (D E : Finset R) : ℕ :=
  1+(D.card+E.card+md.successorEntries)*(E.card+1)

def metadataBoundaryCharge (md : RegionalMetadata) (foodSize e : ℕ) : ℕ :=
  1+(foodSize+md.needsEntries+e+1)^2+
    (md.needsEntries+1)*(e+1)*(md.outputEntries+e+2)

omit [DecidableEq R] in
theorem metadata_region_exact (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M) (D E : Finset R) :
    metadataRegionCharge (collectRegionalMetadata Q cats succ needs E) D E =
      regionCharge succ D E := rfl

omit [DecidableEq R] in
theorem metadata_boundary_exact (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M) (E : Finset R) :
    metadataBoundaryCharge (collectRegionalMetadata Q cats succ needs E) Q.food.card E.card =
      boundaryCharge Q needs E := rfl

omit [DecidableEq R] in
theorem metadata_arities (Q : CRS M R) (cats : R → Finset M)
    (succ : R → Finset R) (needs : R → Finset M) (E : Finset R) :
    ∀ r ∈ E, (Q.inputs r).card ≤ (collectRegionalMetadata Q cats succ needs E).inputArity ∧
      (Q.outputs r).card ≤ (collectRegionalMetadata Q cats succ needs E).outputArity ∧
      (cats r).card ≤ (collectRegionalMetadata Q cats succ needs E).catalystArity := by
  intro r hr
  dsimp only [collectRegionalMetadata]
  exact ⟨Finset.le_sup (f := fun s => (Q.inputs s).card) hr,
    Finset.le_sup (f := fun s => (Q.outputs s).card) hr,
    Finset.le_sup (f := fun s => (cats s).card) hr⟩

end RAFQueryCompilation
