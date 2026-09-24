import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_4_700Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_700Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_700Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-8 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4 / 3 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else 0

def foldGlobal_4_700Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_700_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_700Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_700Network foldGlobal_4_700Generator 1
    foldGlobal_4_700Multiplier foldGlobal_4_700Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_701Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_701Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_701Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (15 / 256 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 16 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 128 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 128 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (11 / 128 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-1 / 128 : ℚ)
  else 0

def foldGlobal_4_701Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_701_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_701Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_701Network foldGlobal_4_701Generator 1
    foldGlobal_4_701Multiplier foldGlobal_4_701Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_702Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_702Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_702Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 8 : ℚ)
  else 0

def foldGlobal_4_702Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 2, 2⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_702_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_702Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_702Network foldGlobal_4_702Generator 1
    foldGlobal_4_702Multiplier foldGlobal_4_702Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_703Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_703Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (4 / 7 : ℚ), (1 / 7 : ℚ), 0, (2 / 7 : ℚ)]]

def foldGlobal_4_703Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (1 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (8 / 21 : ℚ)
  else 0

def foldGlobal_4_703Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_703_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_703Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_703Network foldGlobal_4_703Generator (-1 : ℚ)
    foldGlobal_4_703Multiplier foldGlobal_4_703Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_704Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_704Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_704Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (142 / 201 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (10 / 201 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (30 / 67 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (103 / 134 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (863 / 603 : ℚ)
  else 0

def foldGlobal_4_704Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_704_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_704Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_704Network foldGlobal_4_704Generator (-1 : ℚ)
    foldGlobal_4_704Multiplier foldGlobal_4_704Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_705Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_705Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_705Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 63 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (22 / 63 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (85 / 189 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (13 / 63 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (131 / 189 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (34 / 63 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (172 / 189 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (394 / 567 : ℚ)
  else 0

def foldGlobal_4_705Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_705_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_705Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_705Network foldGlobal_4_705Generator (-1 : ℚ)
    foldGlobal_4_705Multiplier foldGlobal_4_705Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_706Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_706Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_706Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-141 / 266 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-85 / 266 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-632 / 665 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-116 / 665 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 133 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-30 / 133 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (20 / 133 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1164 / 3325 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-4 / 133 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (4 / 133 : ℚ)
  else 0

def foldGlobal_4_706Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_706_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_706Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_706Network foldGlobal_4_706Generator 1
    foldGlobal_4_706Multiplier foldGlobal_4_706Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_707Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_707Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(4 / 7 : ℚ), 0, (2 / 7 : ℚ), 0, (1 / 7 : ℚ)],
  ![0, (4 / 9 : ℚ), (2 / 9 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_707Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-4 / 7 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-4 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (4 / 15 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-32 / 49 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-64 / 63 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-4 / 105 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-32 / 81 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-16 / 45 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (4 / 75 : ℚ)
  else 0

def foldGlobal_4_707Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 2, 3⟩, ⟨0, 0, 3, 3⟩, ⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨1, 1, 1, 3⟩}

theorem foldGlobal_4_707_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_707Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_707Network foldGlobal_4_707Generator 1
    foldGlobal_4_707Multiplier foldGlobal_4_707Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_708Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_708Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_708Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-262 / 775 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-631 / 2325 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (8 / 155 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-256 / 775 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-266 / 465 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-66 / 775 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-34 / 93 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-536 / 2325 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (8 / 775 : ℚ)
  else 0

def foldGlobal_4_708Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_708_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_708Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_708Network foldGlobal_4_708Generator 1
    foldGlobal_4_708Multiplier foldGlobal_4_708Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_709Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_709Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_709Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-128 / 25 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-256 / 375 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-16 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 25 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (8 / 15 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (2 / 9 : ℚ)
  else 0

def foldGlobal_4_709Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_709_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_709Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_709Network foldGlobal_4_709Generator 1
    foldGlobal_4_709Multiplier foldGlobal_4_709Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_710Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_710Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), (1 / 3 : ℚ), 0, (1 / 6 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_710Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-6292 / 1065 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-30532 / 5325 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1613 / 639 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1036 / 639 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1549 / 1065 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-8017 / 7668 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1676 / 1065 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-4417 / 9585 : ℚ)
  else 0

def foldGlobal_4_710Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_710_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_710Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_710Network foldGlobal_4_710Generator 1
    foldGlobal_4_710Multiplier foldGlobal_4_710Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_711Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_711Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_711Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-351304 / 50725 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-21058 / 10145 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-285456 / 50725 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-4026 / 2029 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2093 / 4058 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-17128 / 10145 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-2541 / 4058 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-16072 / 10145 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-2304 / 10145 : ℚ)
  else 0

def foldGlobal_4_711Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_711_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_711Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_711Network foldGlobal_4_711Generator 1
    foldGlobal_4_711Multiplier foldGlobal_4_711Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_712Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_712Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, 0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_4_712Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-81 / 22 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-162 / 55 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-724 / 275 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-468 / 275 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-432 / 275 : ℚ)
  else 0

def foldGlobal_4_712Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_712_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_712Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_712Network foldGlobal_4_712Generator 1
    foldGlobal_4_712Multiplier foldGlobal_4_712Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_713Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_713Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_713Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-3956 / 925 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-698 / 185 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1462 / 555 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-821 / 666 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-527 / 555 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-197 / 222 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-58 / 37 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-457 / 555 : ℚ)
  else 0

def foldGlobal_4_713Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_713_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_713Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_713Network foldGlobal_4_713Generator 1
    foldGlobal_4_713Multiplier foldGlobal_4_713Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_714Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_714Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, 0, (1 / 3 : ℚ)],
  ![(2 / 5 : ℚ), 0, (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (2 / 7 : ℚ), (1 / 7 : ℚ), (4 / 7 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_714Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (96 / 625 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (48 / 875 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (96 / 625 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (48 / 875 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (48 / 625 : ℚ)
  else 0

def foldGlobal_4_714Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_714_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_714Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_714Network foldGlobal_4_714Generator (-1 : ℚ)
    foldGlobal_4_714Multiplier foldGlobal_4_714Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_715Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_715Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, 0, (1 / 3 : ℚ)],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_715Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (521 / 1650 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (293 / 825 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (34 / 165 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (112 / 825 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (128 / 825 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (16 / 275 : ℚ)
  else 0

def foldGlobal_4_715Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_715_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_715Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_715Network foldGlobal_4_715Generator (-1 : ℚ)
    foldGlobal_4_715Multiplier foldGlobal_4_715Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_716Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_716Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_716Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-3 / 2 : ℚ)
  else 0

def foldGlobal_4_716Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_716_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_716Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_716Network foldGlobal_4_716Generator 1
    foldGlobal_4_716Multiplier foldGlobal_4_716Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_717Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_717Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_717Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-20520 / 13777 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-57476 / 123993 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1358248 / 619965 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-113768 / 123993 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1184 / 123993 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-61124 / 206655 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-4736 / 123993 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-854144 / 1033275 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-3112 / 5391 : ℚ)
  else 0

def foldGlobal_4_717Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_717_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_717Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_717Network foldGlobal_4_717Generator 1
    foldGlobal_4_717Multiplier foldGlobal_4_717Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_718Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_718Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_718Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-9 / 73 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-86 / 1095 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-3 / 73 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1195 / 657 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-3475 / 1314 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-170 / 219 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-16862 / 16425 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-192 / 365 : ℚ)
  else 0

def foldGlobal_4_718Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_718_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_718Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_718Network foldGlobal_4_718Generator 1
    foldGlobal_4_718Multiplier foldGlobal_4_718Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_719Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_719Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_4_719Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-3508 / 573 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-16712 / 2865 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-824 / 955 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-4932 / 4775 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-1496 / 955 : ℚ)
  else 0

def foldGlobal_4_719Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_719_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_719Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_719Network foldGlobal_4_719Generator 1
    foldGlobal_4_719Multiplier foldGlobal_4_719Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_720Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_720Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_720Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4664 / 5085 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-462 / 565 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-3112 / 2825 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-5384 / 5085 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-16 / 565 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1642 / 2825 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-64 / 339 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-8656 / 14125 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1448 / 1695 : ℚ)
  else 0

def foldGlobal_4_720Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_720_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_720Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_720Network foldGlobal_4_720Generator 1
    foldGlobal_4_720Multiplier foldGlobal_4_720Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_721Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_721Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 6 : ℚ), (1 / 3 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_721Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-536 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-19 / 9 : ℚ)
  else 0

def foldGlobal_4_721Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_721_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_721Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_721Network foldGlobal_4_721Generator 1
    foldGlobal_4_721Multiplier foldGlobal_4_721Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_722Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_722Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_722Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-64 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-64 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-88 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-11 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-9 / 10 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-4 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-8 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-91 / 90 : ℚ)
  else 0

def foldGlobal_4_722Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_722_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_722Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_722Network foldGlobal_4_722Generator 1
    foldGlobal_4_722Multiplier foldGlobal_4_722Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_723Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_723Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 6 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_723Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-860 / 81 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-64 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-22 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-19 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-41 / 30 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-11 / 24 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-8 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-19 / 60 : ℚ)
  else 0

def foldGlobal_4_723Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_723_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_723Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_723Network foldGlobal_4_723Generator 1
    foldGlobal_4_723Multiplier foldGlobal_4_723Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_724Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_724Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)],
  ![(2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(2 / 7 : ℚ), 0, (1 / 7 : ℚ), (4 / 7 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_4_724Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-952 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-592 / 441 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-64 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-200 / 343 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-344 / 245 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-8 / 5 : ℚ)
  else 0

def foldGlobal_4_724Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_724_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_724Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_724Network foldGlobal_4_724Generator 1
    foldGlobal_4_724Multiplier foldGlobal_4_724Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_725Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_725Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 6 : ℚ), (1 / 3 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_725Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-624176 / 135675 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-344192 / 75375 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-2448 / 1675 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-12697 / 15075 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-12196 / 25125 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1892 / 3015 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2632 / 1675 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-856 / 1005 : ℚ)
  else 0

def foldGlobal_4_725Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_725_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_725Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_725Network foldGlobal_4_725Generator 1
    foldGlobal_4_725Multiplier foldGlobal_4_725Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_726Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_726Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), (1 / 7 : ℚ), (4 / 7 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), (1 / 5 : ℚ), 0, 0, (2 / 5 : ℚ)],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_726Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 3 then (2 / 7 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (381 / 160 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (16 / 25 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (14 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (2 / 5 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (9 / 8 : ℚ)
  else 0

def foldGlobal_4_726Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_726_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_726Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_726Network foldGlobal_4_726Generator (-1 : ℚ)
    foldGlobal_4_726Multiplier foldGlobal_4_726Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_727Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_727Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0, 0],
  ![(2 / 7 : ℚ), (2 / 7 : ℚ), 0, 0, (3 / 7 : ℚ)],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_727Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (8 / 35 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (2 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (104 / 49 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (24 / 35 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (22 / 7 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (2 / 5 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (5 / 4 : ℚ)
  else 0

def foldGlobal_4_727Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_727_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_727Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_727Network foldGlobal_4_727Generator (-1 : ℚ)
    foldGlobal_4_727Multiplier foldGlobal_4_727Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_728Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_728Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_728Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (125 / 266 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (3139 / 1596 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (30 / 133 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (341 / 532 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (3503 / 1197 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1639 / 1995 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (4981 / 1596 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 133 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (366 / 665 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (137 / 133 : ℚ)
  else 0

def foldGlobal_4_728Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_728_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_728Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_728Network foldGlobal_4_728Generator (-1 : ℚ)
    foldGlobal_4_728Multiplier foldGlobal_4_728Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_729Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_729Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_5_729Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-43703 / 13566 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-685 / 4522 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-56519 / 36176 : ℚ)
  else if a.val = 0 ∧ b.val = 4 then (-269 / 323 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (3 / 646 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-3609 / 2584 : ℚ)
  else if a.val = 1 ∧ b.val = 4 then (18 / 323 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (26007 / 161500 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-3003 / 1615 : ℚ)
  else if a.val = 2 ∧ b.val = 4 then (-879 / 1615 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-56379 / 15232 : ℚ)
  else if a.val = 3 ∧ b.val = 4 then (-735 / 1292 : ℚ)
  else 0

def foldGlobal_5_729Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_5_729_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_729Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_729Network foldGlobal_5_729Generator 1
    foldGlobal_5_729Multiplier foldGlobal_5_729Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_730Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_730Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_5_730Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-4 / 5 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-4 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-44 / 25 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-64 / 15 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-13 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-20 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-7 / 3 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-1 / 2 : ℚ)
  else 0

def foldGlobal_5_730Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_5_730_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_730Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_730Network foldGlobal_5_730Generator 1
    foldGlobal_5_730Multiplier foldGlobal_5_730Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_731Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_731Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (3 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_5_731Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 6 : ℚ)
  else 0

def foldGlobal_5_731Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩, ⟨1, 1, 1, 4⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_5_731_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_731Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_731Network foldGlobal_5_731Generator (-1 : ℚ)
    foldGlobal_5_731Multiplier foldGlobal_5_731Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_732Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_732Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 5 : ℚ), 0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_5_732Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 515 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-13 / 206 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-33 / 2575 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 4 then (-587 / 4635 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-86 / 515 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (131 / 5150 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 4 then (-407 / 3090 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-643 / 12875 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 4 then (-3 / 103 : ℚ)
  else if a.val = 4 ∧ b.val = 4 then (6 / 515 : ℚ)
  else 0

def foldGlobal_5_732Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_5_732_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_732Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_732Network foldGlobal_5_732Generator 1
    foldGlobal_5_732Multiplier foldGlobal_5_732Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_733Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_733Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(2 / 7 : ℚ), (4 / 7 : ℚ), 0, 0, (1 / 7 : ℚ)],
  ![(1 / 5 : ℚ), 0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_5_733Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-95 / 392 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-8879 / 35280 : ℚ)
  else if a.val = 0 ∧ b.val = 4 then (-107 / 735 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-24 / 49 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (8 / 35 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-6092 / 5145 : ℚ)
  else if a.val = 1 ∧ b.val = 4 then (-178 / 1715 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-7 / 50 : ℚ)
  else if a.val = 2 ∧ b.val = 4 then (-6 / 25 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-8 / 9 : ℚ)
  else if a.val = 3 ∧ b.val = 4 then (-368 / 3675 : ℚ)
  else if a.val = 4 ∧ b.val = 4 then (-312 / 1225 : ℚ)
  else 0

def foldGlobal_5_733Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_5_733_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_733Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_733Network foldGlobal_5_733Generator 1
    foldGlobal_5_733Multiplier foldGlobal_5_733Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_734Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_734Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![(2 / 7 : ℚ), 0, (2 / 7 : ℚ), 0, (3 / 7 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_5_734Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-381 / 2158 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-9977 / 226590 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 4 then (-829 / 5395 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-3851752 / 10115625 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-264008 / 404625 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-2 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 4 then (-6932 / 26975 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-12784 / 52871 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-2 / 7 : ℚ)
  else if a.val = 2 ∧ b.val = 4 then (-1076 / 5395 : ℚ)
  else if a.val = 4 ∧ b.val = 4 then (16 / 1079 : ℚ)
  else 0

def foldGlobal_5_734Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_5_734_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_734Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_734Network foldGlobal_5_734Generator 1
    foldGlobal_5_734Multiplier foldGlobal_5_734Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_735Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_735Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_5_735Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1101 / 425 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (437 / 765 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-9151 / 2040 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1286 / 765 : ℚ)
  else if a.val = 0 ∧ b.val = 4 then (-203 / 204 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1267 / 459 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (671 / 306 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-229 / 153 : ℚ)
  else if a.val = 1 ∧ b.val = 4 then (-1 / 34 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-155 / 68 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-79 / 102 : ℚ)
  else if a.val = 2 ∧ b.val = 4 then (-21 / 68 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-269 / 612 : ℚ)
  else if a.val = 3 ∧ b.val = 4 then (-14 / 51 : ℚ)
  else 0

def foldGlobal_5_735Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 3⟩}

theorem foldGlobal_5_735_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_735Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_735Network foldGlobal_5_735Generator 1
    foldGlobal_5_735Multiplier foldGlobal_5_735Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_736Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .yy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_736Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), (2 / 7 : ℚ), 0, 0, (3 / 7 : ℚ)],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_5_736Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-29581 / 97559 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-6023 / 125433 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-416288 / 5644485 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 7 : ℚ)
  else if a.val = 0 ∧ b.val = 4 then (-61837 / 278740 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2007 / 31856 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2008 / 9955 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 8 : ℚ)
  else if a.val = 1 ∧ b.val = 4 then (-3607 / 19910 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-42587 / 199100 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 4 then (-59087 / 199100 : ℚ)
  else if a.val = 4 ∧ b.val = 4 then (10 / 1991 : ℚ)
  else 0

def foldGlobal_5_736Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩, ⟨1, 1, 1, 4⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_5_736_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_736Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_736Network foldGlobal_5_736Generator 1
    foldGlobal_5_736Multiplier foldGlobal_5_736Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_737Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_737Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_5_737Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (4 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 4 then (2 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 9 : ℚ)
  else 0

def foldGlobal_5_737Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 3⟩, ⟨0, 0, 3, 3⟩, ⟨0, 0, 4, 4⟩, ⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩, ⟨1, 1, 1, 4⟩, ⟨2, 2, 2, 3⟩}

theorem foldGlobal_5_737_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_737Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_737Network foldGlobal_5_737Generator (-1 : ℚ)
    foldGlobal_5_737Multiplier foldGlobal_5_737Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_738Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_738Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_5_738Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then 1
  else if a.val = 0 ∧ b.val = 4 then (1 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 9 : ℚ)
  else 0

def foldGlobal_5_738Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 3⟩, ⟨0, 0, 3, 3⟩, ⟨0, 0, 4, 4⟩, ⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩, ⟨1, 1, 1, 4⟩, ⟨2, 2, 2, 3⟩}

theorem foldGlobal_5_738_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_738Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_738Network foldGlobal_5_738Generator (-1 : ℚ)
    foldGlobal_5_738Multiplier foldGlobal_5_738Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_739Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_739Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_5_739Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (5 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (3 / 5 : ℚ)
  else if a.val = 0 ∧ b.val = 4 then (1 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (16 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 4 then (1 / 32 : ℚ)
  else 0

def foldGlobal_5_739Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 3⟩, ⟨0, 0, 2, 4⟩, ⟨0, 0, 3, 3⟩, ⟨0, 0, 4, 4⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_5_739_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_739Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_739Network foldGlobal_5_739Generator (-1 : ℚ)
    foldGlobal_5_739Multiplier foldGlobal_5_739Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_740Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_740Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_5_740Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (56 / 53 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (49 / 106 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (112 / 265 : ℚ)
  else if a.val = 0 ∧ b.val = 4 then (6 / 53 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (221 / 477 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (8 / 265 : ℚ)
  else 0

def foldGlobal_5_740Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨0, 0, 4, 4⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_5_740_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_740Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_740Network foldGlobal_5_740Generator (-1 : ℚ)
    foldGlobal_5_740Multiplier foldGlobal_5_740Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_741Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_741Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_5_741Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 8 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 0 ∧ b.val = 4 then (-1 / 10 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 8 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 4 then (139 / 580 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-2 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 4 then (95 / 348 : ℚ)
  else if a.val = 3 ∧ b.val = 4 then (-209 / 2175 : ℚ)
  else if a.val = 4 ∧ b.val = 4 then (27 / 725 : ℚ)
  else 0

def foldGlobal_5_741Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨0, 3, 3, 4⟩, ⟨0, 4, 4, 4⟩, ⟨1, 1, 1, 3⟩, ⟨1, 1, 1, 4⟩, ⟨2, 2, 2, 3⟩}

theorem foldGlobal_5_741_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_741Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_741Network foldGlobal_5_741Generator (-1 : ℚ)
    foldGlobal_5_741Multiplier foldGlobal_5_741Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_742Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_742Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(4 / 7 : ℚ), 0, (2 / 7 : ℚ), 0, (1 / 7 : ℚ)],
  ![0, (1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_5_742Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (60 / 511 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1348 / 3577 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (136 / 511 : ℚ)
  else if a.val = 1 ∧ b.val = 4 then (24 / 511 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (968 / 3577 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (1108 / 3577 : ℚ)
  else if a.val = 2 ∧ b.val = 4 then (40 / 511 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (20 / 511 : ℚ)
  else if a.val = 3 ∧ b.val = 4 then (40 / 511 : ℚ)
  else 0

def foldGlobal_5_742Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨0, 3, 3, 3⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_5_742_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_742Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_742Network foldGlobal_5_742Generator (-1 : ℚ)
    foldGlobal_5_742Multiplier foldGlobal_5_742Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_5_743Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_5_743Generator : Fin 5 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_5_743Multiplier (a b : Fin 5) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-8 / 25 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-16 / 15 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-4 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-8 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-4 / 3 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-1 / 2 : ℚ)
  else 0

def foldGlobal_5_743Witnesses : Finset (QuarticWitness 5) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_5_743_noCusp : ¬ AdmitsTransverseCusp foldGlobal_5_743Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_5_743Network foldGlobal_5_743Generator 1
    foldGlobal_5_743Multiplier foldGlobal_5_743Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
