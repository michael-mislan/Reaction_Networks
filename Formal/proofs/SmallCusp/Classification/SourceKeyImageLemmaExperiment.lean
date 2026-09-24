import proofs.SmallCusp.Source.Enumeration

namespace SmallCusp

theorem bimol_catalogue_key_univ_image
    (f : Fin 5 → BimolReactionCode) (hf : Function.Injective f) :
    bimolCatalogueKey (Finset.univ.image f) =
      ∑ r : Fin 5, 2 ^ bimolReactionIndex (f r) := by
  unfold bimolCatalogueKey
  rw [Finset.sum_image]
  exact fun a _ b _ h => hf h

end SmallCusp
