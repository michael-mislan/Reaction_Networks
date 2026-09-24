import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_3_400Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_400Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_400Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (9 / 151 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (126 / 755 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (3 / 604 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (3 / 604 : ℚ)
  else 0

def foldGlobal_3_400Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_400_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_400Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_400Network foldGlobal_3_400Generator 1
    foldGlobal_3_400Multiplier foldGlobal_3_400Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_401Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_401Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_401Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (3 / 76 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (15 / 152 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 304 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 304 : ℚ)
  else 0

def foldGlobal_3_401Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_401_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_401Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_401Network foldGlobal_3_401Generator 1
    foldGlobal_3_401Multiplier foldGlobal_3_401Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_402Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_402Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)]]

def foldGlobal_3_402Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-19 / 36 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-19 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 36 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-11 / 72 : ℚ)
  else 0

def foldGlobal_3_402Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_402_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_402Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_402Network foldGlobal_3_402Generator 1
    foldGlobal_3_402Multiplier foldGlobal_3_402Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_403Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_403Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)]]

def foldGlobal_3_403Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-25 / 48 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 8 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 48 : ℚ)
  else 0

def foldGlobal_3_403Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_403_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_403Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_403Network foldGlobal_3_403Generator 1
    foldGlobal_3_403Multiplier foldGlobal_3_403Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_404Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_404Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_404Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-6 / 281 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-257 / 1124 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1853 / 2810 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-5724 / 7025 : ℚ)
  else 0

def foldGlobal_3_404Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_404_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_404Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_404Network foldGlobal_3_404Generator 1
    foldGlobal_3_404Multiplier foldGlobal_3_404Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_405Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_405Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![(4 / 7 : ℚ), 0, (2 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_3_405Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-60 / 169 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-6976 / 8281 : ℚ)
  else 0

def foldGlobal_3_405Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_405_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_405Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_405Network foldGlobal_3_405Generator 1
    foldGlobal_3_405Multiplier foldGlobal_3_405Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_406Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_406Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_406Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-1 / 48 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-11 / 48 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-9 / 16 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-29 / 48 : ℚ)
  else 0

def foldGlobal_3_406Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_406_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_406Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_406Network foldGlobal_3_406Generator 1
    foldGlobal_3_406Multiplier foldGlobal_3_406Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_407Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_407Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_407Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-18 / 61 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-688 / 1525 : ℚ)
  else 0

def foldGlobal_3_407Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_407_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_407Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_407Network foldGlobal_3_407Generator 1
    foldGlobal_3_407Multiplier foldGlobal_3_407Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_408Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_408Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_408Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-5 / 64 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-29 / 128 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-23 / 48 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-89 / 288 : ℚ)
  else 0

def foldGlobal_3_408Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_408_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_408Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_408Network foldGlobal_3_408Generator 1
    foldGlobal_3_408Multiplier foldGlobal_3_408Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_409Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_409Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_409Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 11 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-160 / 99 : ℚ)
  else 0

def foldGlobal_3_409Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_409_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_409Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_409Network foldGlobal_3_409Generator 1
    foldGlobal_3_409Multiplier foldGlobal_3_409Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_410Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_410Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_410Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 63 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (3 / 7 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 63 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 7 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 63 : ℚ)
  else 0

def foldGlobal_3_410Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_410_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_410Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_410Network foldGlobal_3_410Generator 1
    foldGlobal_3_410Multiplier foldGlobal_3_410Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_411Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_411Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_411Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (12 / 151 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (168 / 755 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 453 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 453 : ℚ)
  else 0

def foldGlobal_3_411Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_411_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_411Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_411Network foldGlobal_3_411Generator 1
    foldGlobal_3_411Multiplier foldGlobal_3_411Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_412Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_412Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_412Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (1 / 19 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (5 / 38 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 171 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 171 : ℚ)
  else 0

def foldGlobal_3_412Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_412_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_412Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_412Network foldGlobal_3_412Generator 1
    foldGlobal_3_412Multiplier foldGlobal_3_412Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_413Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_413Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_413Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-24 / 35 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-6424 / 2835 : ℚ)
  else 0

def foldGlobal_3_413Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_413_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_413Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_413Network foldGlobal_3_413Generator 1
    foldGlobal_3_413Multiplier foldGlobal_3_413Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_414Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_414Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_414Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 63 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (3 / 7 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 63 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 7 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 63 : ℚ)
  else 0

def foldGlobal_3_414Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_414_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_414Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_414Network foldGlobal_3_414Generator 1
    foldGlobal_3_414Multiplier foldGlobal_3_414Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_415Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_415Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_415Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (12 / 151 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (168 / 755 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 453 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 453 : ℚ)
  else 0

def foldGlobal_3_415Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_415_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_415Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_415Network foldGlobal_3_415Generator 1
    foldGlobal_3_415Multiplier foldGlobal_3_415Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_416Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_416Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_416Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (1 / 19 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (5 / 38 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 171 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 171 : ℚ)
  else 0

def foldGlobal_3_416Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_416_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_416Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_416Network foldGlobal_3_416Generator 1
    foldGlobal_3_416Multiplier foldGlobal_3_416Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_417Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.y, .yy), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_417Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_417Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-20496 / 9725 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-2080 / 1167 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-64 / 389 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2920 / 1167 : ℚ)
  else 0

def foldGlobal_3_417Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_417_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_417Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_417Network foldGlobal_3_417Generator 1
    foldGlobal_3_417Multiplier foldGlobal_3_417Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_418Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.y, .xx), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_418Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (4 / 9 : ℚ), (2 / 9 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_418Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-45952 / 96633 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-912 / 5965 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (320 / 3579 : ℚ)
  else 0

def foldGlobal_3_418Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_418_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_418Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_418Network foldGlobal_3_418Generator 1
    foldGlobal_3_418Multiplier foldGlobal_3_418Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_419Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.y, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_419Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_419Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-982 / 3447 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-264 / 1915 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (20 / 383 : ℚ)
  else 0

def foldGlobal_3_419Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_419_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_419Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_419Network foldGlobal_3_419Generator 1
    foldGlobal_3_419Multiplier foldGlobal_3_419Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_420Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_420Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_3_420Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 27 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-8 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-62 / 27 : ℚ)
  else 0

def foldGlobal_3_420Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_420_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_420Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_420Network foldGlobal_3_420Generator 1
    foldGlobal_3_420Multiplier foldGlobal_3_420Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_421Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_421Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_421Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 99 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (4 / 99 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 99 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 99 : ℚ)
  else 0

def foldGlobal_3_421Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_421_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_421Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_421Network foldGlobal_3_421Generator 1
    foldGlobal_3_421Multiplier foldGlobal_3_421Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_422Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_422Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_3_422Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-64 / 261 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-64 / 261 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-9952 / 6525 : ℚ)
  else 0

def foldGlobal_3_422Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_422_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_422Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_422Network foldGlobal_3_422Generator 1
    foldGlobal_3_422Multiplier foldGlobal_3_422Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_423Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_423Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_423Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 81 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (2 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (2 / 81 : ℚ)
  else 0

def foldGlobal_3_423Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_423_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_423Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_423Network foldGlobal_3_423Generator 1
    foldGlobal_3_423Multiplier foldGlobal_3_423Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_424Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_424Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0]]

def foldGlobal_3_424Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (3232 / 1425 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (824 / 475 : ℚ)
  else 0

def foldGlobal_3_424Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_424_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_424Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_424Network foldGlobal_3_424Generator (-1 : ℚ)
    foldGlobal_3_424Multiplier foldGlobal_3_424Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_425Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_425Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_425Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 81 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (2 / 81 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (2 / 81 : ℚ)
  else 0

def foldGlobal_3_425Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_425_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_425Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_425Network foldGlobal_3_425Generator 1
    foldGlobal_3_425Multiplier foldGlobal_3_425Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_426Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.y, .yy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_426Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_426Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-11 / 24 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 24 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-23 / 24 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-11 / 18 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-55 / 108 : ℚ)
  else 0

def foldGlobal_3_426Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_426_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_426Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_426Network foldGlobal_3_426Generator 1
    foldGlobal_3_426Multiplier foldGlobal_3_426Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_427Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.y, .yy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_427Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_427Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-5 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-34 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-38 / 81 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-34 / 81 : ℚ)
  else 0

def foldGlobal_3_427Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_427_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_427Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_427Network foldGlobal_3_427Generator 1
    foldGlobal_3_427Multiplier foldGlobal_3_427Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_428Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_428Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ), 0]]

def foldGlobal_3_428Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (6 / 49 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (48 / 245 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 49 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 49 : ℚ)
  else 0

def foldGlobal_3_428Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_428_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_428Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_428Network foldGlobal_3_428Generator 1
    foldGlobal_3_428Multiplier foldGlobal_3_428Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_429Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_429Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_429Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 49 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1 / 49 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (6 / 49 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (48 / 245 : ℚ)
  else 0

def foldGlobal_3_429Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_429_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_429Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_429Network foldGlobal_3_429Generator 1
    foldGlobal_3_429Multiplier foldGlobal_3_429Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_430Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_430Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_430Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (1 / 25 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (9 / 50 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 25 : ℚ)
  else 0

def foldGlobal_3_430Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_430_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_430Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_430Network foldGlobal_3_430Generator 1
    foldGlobal_3_430Multiplier foldGlobal_3_430Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_431Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_431Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_431Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (2 / 111 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 111 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (13 / 111 : ℚ)
  else 0

def foldGlobal_3_431Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 2, 2⟩}

theorem foldGlobal_3_431_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_431Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_431Network foldGlobal_3_431Generator 1
    foldGlobal_3_431Multiplier foldGlobal_3_431Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_432Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_432Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)],
  ![(4 / 7 : ℚ), 0, 0, (1 / 7 : ℚ), (2 / 7 : ℚ)]]

def foldGlobal_3_432Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 81 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (2 / 81 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (2 / 81 : ℚ)
  else 0

def foldGlobal_3_432Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_432_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_432Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_432Network foldGlobal_3_432Generator 1
    foldGlobal_3_432Multiplier foldGlobal_3_432Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_433Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_433Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_433Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (3 / 37 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (21 / 148 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 37 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 74 : ℚ)
  else 0

def foldGlobal_3_433Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_433_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_433Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_433Network foldGlobal_3_433Generator 1
    foldGlobal_3_433Multiplier foldGlobal_3_433Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_434Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_434Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_434Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 37 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1 / 74 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (3 / 37 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (21 / 148 : ℚ)
  else 0

def foldGlobal_3_434Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_434_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_434Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_434Network foldGlobal_3_434Generator 1
    foldGlobal_3_434Multiplier foldGlobal_3_434Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_435Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_435Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_435Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (2 / 73 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (28 / 219 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 73 : ℚ)
  else 0

def foldGlobal_3_435Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_435_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_435Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_435Network foldGlobal_3_435Generator 1
    foldGlobal_3_435Multiplier foldGlobal_3_435Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_436Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_436Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_436Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (2 / 141 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 141 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (40 / 423 : ℚ)
  else 0

def foldGlobal_3_436Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 2, 2⟩}

theorem foldGlobal_3_436_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_436Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_436Network foldGlobal_3_436Generator 1
    foldGlobal_3_436Multiplier foldGlobal_3_436Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_437Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_437Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_437Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-1 / 2 : ℚ)
  else 0

def foldGlobal_3_437Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_437_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_437Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_437Network foldGlobal_3_437Generator 1
    foldGlobal_3_437Multiplier foldGlobal_3_437Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_438Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_438Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_438Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-62032 / 13425 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-352 / 2685 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-11608 / 4833 : ℚ)
  else 0

def foldGlobal_3_438Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_438_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_438Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_438Network foldGlobal_3_438Generator 1
    foldGlobal_3_438Multiplier foldGlobal_3_438Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_439Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_439Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0]]

def foldGlobal_3_439Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (32 / 305 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (288 / 1525 : ℚ)
  else 0

def foldGlobal_3_439Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_439_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_439Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_439Network foldGlobal_3_439Generator (-1 : ℚ)
    foldGlobal_3_439Multiplier foldGlobal_3_439Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_440Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_440Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0]]

def foldGlobal_3_440Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (3 / 22 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3 / 11 : ℚ)
  else 0

def foldGlobal_3_440Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_440_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_440Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_440Network foldGlobal_3_440Generator (-1 : ℚ)
    foldGlobal_3_440Multiplier foldGlobal_3_440Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_441Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_441Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0]]

def foldGlobal_3_441Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 16 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 4 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (7 / 16 : ℚ)
  else 0

def foldGlobal_3_441Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_441_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_441Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_441Network foldGlobal_3_441Generator (-1 : ℚ)
    foldGlobal_3_441Multiplier foldGlobal_3_441Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_442Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_442Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)]]

def foldGlobal_3_442Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-15 / 28 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-59 / 84 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 28 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-65 / 252 : ℚ)
  else 0

def foldGlobal_3_442Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_442_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_442Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_442Network foldGlobal_3_442Generator 1
    foldGlobal_3_442Multiplier foldGlobal_3_442Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_443Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.y, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_443Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)]]

def foldGlobal_3_443Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-9 / 16 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 16 : ℚ)
  else 0

def foldGlobal_3_443Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_443_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_443Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_443Network foldGlobal_3_443Generator 1
    foldGlobal_3_443Multiplier foldGlobal_3_443Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_444Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_444Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_444Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-4 / 161 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-608 / 1449 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-278 / 345 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-3384 / 4025 : ℚ)
  else 0

def foldGlobal_3_444Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_444_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_444Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_444Network foldGlobal_3_444Generator 1
    foldGlobal_3_444Multiplier foldGlobal_3_444Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_445Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.y, .xx), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_445Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(4 / 7 : ℚ), 0, (2 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_3_445Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-60 / 169 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-6976 / 8281 : ℚ)
  else 0

def foldGlobal_3_445Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_445_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_445Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_445Network foldGlobal_3_445Generator 1
    foldGlobal_3_445Multiplier foldGlobal_3_445Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_446Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_446Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_446Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-2 / 95 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-362 / 855 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-61 / 95 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-49 / 76 : ℚ)
  else 0

def foldGlobal_3_446Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_446_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_446Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_446Network foldGlobal_3_446Generator 1
    foldGlobal_3_446Multiplier foldGlobal_3_446Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_447Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.y, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_447Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_447Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-18 / 61 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-688 / 1525 : ℚ)
  else 0

def foldGlobal_3_447Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_447_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_447Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_447Network foldGlobal_3_447Generator 1
    foldGlobal_3_447Multiplier foldGlobal_3_447Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_448Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_448Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, (2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_448Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-266 / 75 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-428 / 81 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (142 / 75 : ℚ)
  else 0

def foldGlobal_3_448Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_448_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_448Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_448Network foldGlobal_3_448Generator 1
    foldGlobal_3_448Multiplier foldGlobal_3_448Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_449Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_449Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, (2 / 7 : ℚ), (1 / 7 : ℚ), (4 / 7 : ℚ), 0]]

def foldGlobal_3_449Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (53 / 98 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (51 / 49 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (80 / 343 : ℚ)
  else 0

def foldGlobal_3_449Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_449_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_449Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_449Network foldGlobal_3_449Generator (-1 : ℚ)
    foldGlobal_3_449Multiplier foldGlobal_3_449Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
