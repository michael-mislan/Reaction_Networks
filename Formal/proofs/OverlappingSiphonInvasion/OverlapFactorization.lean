import Mathlib

namespace OverlappingSiphonInvasion
open Matrix

/-- Cross-multiplication counts the shared block once, without division at a
threshold. The source zero pattern supplies this three-block form. -/
theorem overlap_charpoly {u v i R : Type*}
    [Fintype u] [Fintype v] [Fintype i]
    [DecidableEq u] [DecidableEq v] [DecidableEq i] [CommRing R]
    (P : Matrix u u R) (Q : Matrix v v R) (C : Matrix i i R)
    (B : Matrix u i R) (D : Matrix v i R) :
    (fromBlocks (fromBlocks P 0 0 Q) (fun x j => Sum.elim (fun x => B x j) (fun x => D x j) x)
      0 C).charpoly * C.charpoly =
      (fromBlocks P B 0 C).charpoly * (fromBlocks Q D 0 C).charpoly := by
  simp only [charpoly_fromBlocks_zero₂₁]
  ring

end OverlappingSiphonInvasion
