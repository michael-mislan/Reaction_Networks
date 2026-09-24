import proofs.SmallCusp.Classification.StructuralSources

namespace SmallCusp

def structurallyEligibleSourceCatalogue : Finset (Finset BimolReactionCode) :=
  ((Finset.univ : Finset BimolReactionCode).powersetCard 5).filter
    StructurallyEligibleSource

theorem structurallyEligibleSourceCatalogue_card :
    structurallyEligibleSourceCatalogue.card = 60036 := by
  native_decide

end SmallCusp
