import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_3_450Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_450Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 7 : ℚ), (1 / 7 : ℚ), (4 / 7 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_450Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (4 / 35 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 15 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (13 / 140 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 75 : ℚ)
  else 0

def foldGlobal_3_450Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_450_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_450Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_450Network foldGlobal_3_450Generator (-1 : ℚ)
    foldGlobal_3_450Multiplier foldGlobal_3_450Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_451Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_451Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0]]

def foldGlobal_3_451Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (27 / 50 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (26 / 25 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (53 / 125 : ℚ)
  else 0

def foldGlobal_3_451Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_451_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_451Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_451Network foldGlobal_3_451Generator (-1 : ℚ)
    foldGlobal_3_451Multiplier foldGlobal_3_451Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_452Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_452Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_452Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (8 / 95 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (16 / 285 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (116 / 1425 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16 / 1425 : ℚ)
  else 0

def foldGlobal_3_452Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_452_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_452Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_452Network foldGlobal_3_452Generator (-1 : ℚ)
    foldGlobal_3_452Multiplier foldGlobal_3_452Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_453Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_453Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0]]

def foldGlobal_3_453Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 20 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (11 / 20 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (21 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (3 / 4 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (9 / 20 : ℚ)
  else 0

def foldGlobal_3_453Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_453_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_453Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_453Network foldGlobal_3_453Generator (-1 : ℚ)
    foldGlobal_3_453Multiplier foldGlobal_3_453Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_454Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_454Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_454Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (25 / 183 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (15 / 61 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (175 / 366 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (50 / 183 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (20 / 183 : ℚ)
  else 0

def foldGlobal_3_454Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_454_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_454Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_454Network foldGlobal_3_454Generator (-1 : ℚ)
    foldGlobal_3_454Multiplier foldGlobal_3_454Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_455Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.y, .x), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_455Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)]]

def foldGlobal_3_455Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-11 / 20 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-21 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 20 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-11 / 20 : ℚ)
  else 0

def foldGlobal_3_455Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_455_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_455Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_455Network foldGlobal_3_455Generator 1
    foldGlobal_3_455Multiplier foldGlobal_3_455Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_456Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.y, .xx), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_456Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_456Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-1 / 29 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-28 / 29 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-491 / 435 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-626 / 725 : ℚ)
  else 0

def foldGlobal_3_456Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_456_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_456Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_456Network foldGlobal_3_456Generator 1
    foldGlobal_3_456Multiplier foldGlobal_3_456Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_457Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .yy), (.y, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_457Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_457Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-1 / 38 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-37 / 38 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-33 / 38 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-51 / 76 : ℚ)
  else 0

def foldGlobal_3_457Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_457_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_457Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_457Network foldGlobal_3_457Generator 1
    foldGlobal_3_457Multiplier foldGlobal_3_457Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_458Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_458Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_3_458Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-3806 / 661 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-928 / 661 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-64896 / 16525 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4288 / 3305 : ℚ)
  else 0

def foldGlobal_3_458Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_458_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_458Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_458Network foldGlobal_3_458Generator 1
    foldGlobal_3_458Multiplier foldGlobal_3_458Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_459Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_459Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_3_459Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1856 / 525 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-232 / 105 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-8 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1856 / 525 : ℚ)
  else 0

def foldGlobal_3_459Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_459_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_459Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_459Network foldGlobal_3_459Generator 1
    foldGlobal_3_459Multiplier foldGlobal_3_459Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_460Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.y, .xy), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_460Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_460Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2920 / 1167 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-2080 / 1167 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-20496 / 9725 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-64 / 389 : ℚ)
  else 0

def foldGlobal_3_460Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_460_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_460Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_460Network foldGlobal_3_460Generator 1
    foldGlobal_3_460Multiplier foldGlobal_3_460Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_461Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_461Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_461Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-760 / 189 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1664 / 567 : ℚ)
  else 0

def foldGlobal_3_461Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_461_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_461Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_461Network foldGlobal_3_461Generator 1
    foldGlobal_3_461Multiplier foldGlobal_3_461Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_462Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_462Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_462Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (1275 / 2678 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (350 / 1339 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (120 / 1339 : ℚ)
  else 0

def foldGlobal_3_462Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_462_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_462Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_462Network foldGlobal_3_462Generator (-1 : ℚ)
    foldGlobal_3_462Multiplier foldGlobal_3_462Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_463Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.x, .yy), (.y, .xx), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_463Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, 0, (1 / 3 : ℚ)],
  ![0, (4 / 9 : ℚ), (2 / 9 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_463Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-45952 / 96633 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-912 / 5965 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (320 / 3579 : ℚ)
  else 0

def foldGlobal_3_463Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_463_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_463Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_463Network foldGlobal_3_463Generator 1
    foldGlobal_3_463Multiplier foldGlobal_3_463Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_464Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.x, .yy), (.y, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_464Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_464Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-982 / 3447 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-264 / 1915 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (20 / 383 : ℚ)
  else 0

def foldGlobal_3_464Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_464_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_464Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_464Network foldGlobal_3_464Generator 1
    foldGlobal_3_464Multiplier foldGlobal_3_464Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_465Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_465Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_3_465Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-142 / 25 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-88 / 75 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-128 / 45 : ℚ)
  else 0

def foldGlobal_3_465Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_465_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_465Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_465Network foldGlobal_3_465Generator 1
    foldGlobal_3_465Multiplier foldGlobal_3_465Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_466Network : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_466Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_3_466Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2120 / 801 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-352 / 267 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-7904 / 2225 : ℚ)
  else 0

def foldGlobal_3_466Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_466_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_466Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_466Network foldGlobal_3_466Generator 1
    foldGlobal_3_466Multiplier foldGlobal_3_466Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_467Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .zero), (.xx, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_467Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), (1 / 7 : ℚ), 0, (4 / 7 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_467Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (78 / 1015 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (11 / 145 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 725 : ℚ)
  else 0

def foldGlobal_3_467Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_467_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_467Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_467Network foldGlobal_3_467Generator (-1 : ℚ)
    foldGlobal_3_467Multiplier foldGlobal_3_467Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_468Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_468Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_3_468Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-131 / 23 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-245 / 207 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8573 / 1863 : ℚ)
  else 0

def foldGlobal_3_468Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_468_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_468Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_468Network foldGlobal_3_468Generator 1
    foldGlobal_3_468Multiplier foldGlobal_3_468Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_469Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .zero), (.xx, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_469Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), (1 / 7 : ℚ), 0, (4 / 7 : ℚ), 0],
  ![(1 / 5 : ℚ), 0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_469Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (52 / 665 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (116 / 1425 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16 / 1425 : ℚ)
  else 0

def foldGlobal_3_469Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_469_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_469Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_469Network foldGlobal_3_469Generator (-1 : ℚ)
    foldGlobal_3_469Multiplier foldGlobal_3_469Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_470Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_470Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_3_470Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-128 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-96 / 25 : ℚ)
  else 0

def foldGlobal_3_470Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_470_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_470Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_470Network foldGlobal_3_470Generator 1
    foldGlobal_3_470Multiplier foldGlobal_3_470Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_471Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .zero), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_471Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 7 : ℚ), (1 / 7 : ℚ), 0, (4 / 7 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_471Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (5 / 24 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 10 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (13 / 140 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 75 : ℚ)
  else 0

def foldGlobal_3_471Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_471_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_471Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_471Network foldGlobal_3_471Generator (-1 : ℚ)
    foldGlobal_3_471Multiplier foldGlobal_3_471Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_472Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .zero), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_472Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), (1 / 7 : ℚ), 0, (4 / 7 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_472Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (680 / 4599 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (260 / 4599 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (40 / 657 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16 / 1971 : ℚ)
  else 0

def foldGlobal_3_472Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_472_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_472Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_472Network foldGlobal_3_472Generator (-1 : ℚ)
    foldGlobal_3_472Multiplier foldGlobal_3_472Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_473Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .zero), (.xy, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_473Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), (1 / 7 : ℚ), 0, (4 / 7 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_473Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (680 / 4599 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (260 / 4599 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (40 / 657 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16 / 1971 : ℚ)
  else 0

def foldGlobal_3_473Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_473_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_473Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_473Network foldGlobal_3_473Generator (-1 : ℚ)
    foldGlobal_3_473Multiplier foldGlobal_3_473Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_474Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .zero), (.xy, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_474Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), (1 / 7 : ℚ), 0, (4 / 7 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_474Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (170 / 1533 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (65 / 2044 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (10 / 219 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 219 : ℚ)
  else 0

def foldGlobal_3_474Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_474_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_474Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_474Network foldGlobal_3_474Generator (-1 : ℚ)
    foldGlobal_3_474Multiplier foldGlobal_3_474Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_475Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .zero), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_475Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 7 : ℚ), (1 / 7 : ℚ), (4 / 7 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_475Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 2 then (13 / 140 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 75 : ℚ)
  else 0

def foldGlobal_3_475Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_475_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_475Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_475Network foldGlobal_3_475Generator (-1 : ℚ)
    foldGlobal_3_475Multiplier foldGlobal_3_475Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_476Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_476Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![(2 / 7 : ℚ), (1 / 7 : ℚ), (4 / 7 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0]]

def foldGlobal_3_476Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (15453 / 10430 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (2476 / 7301 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (7592 / 26075 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (11248 / 36505 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (6336 / 26075 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3336 / 18625 : ℚ)
  else 0

def foldGlobal_3_476Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_476_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_476Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_476Network foldGlobal_3_476Generator (-1 : ℚ)
    foldGlobal_3_476Multiplier foldGlobal_3_476Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_477Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero), (.yy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_477Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), (1 / 7 : ℚ), (4 / 7 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_477Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (130 / 2163 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (184 / 2163 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (8 / 927 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (88 / 1545 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 927 : ℚ)
  else 0

def foldGlobal_3_477Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_477_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_477Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_477Network foldGlobal_3_477Generator (-1 : ℚ)
    foldGlobal_3_477Multiplier foldGlobal_3_477Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_478Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .y), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_478Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 5 : ℚ), (1 / 5 : ℚ), 0, (3 / 5 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_478Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (8 / 125 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (116 / 1875 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16 / 1875 : ℚ)
  else 0

def foldGlobal_3_478Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_478_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_478Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_478Network foldGlobal_3_478Generator (-1 : ℚ)
    foldGlobal_3_478Multiplier foldGlobal_3_478Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_479Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .y), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_479Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (1 / 5 : ℚ), 0, (3 / 5 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_479Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (4 / 19 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (116 / 1425 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (8 / 95 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16 / 1425 : ℚ)
  else 0

def foldGlobal_3_479Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_479_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_479Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_479Network foldGlobal_3_479Generator (-1 : ℚ)
    foldGlobal_3_479Multiplier foldGlobal_3_479Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_480Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .y), (.xy, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_480Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (1 / 5 : ℚ), 0, (3 / 5 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_480Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (4 / 19 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (116 / 1425 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (8 / 95 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16 / 1425 : ℚ)
  else 0

def foldGlobal_3_480Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_480_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_480Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_480Network foldGlobal_3_480Generator (-1 : ℚ)
    foldGlobal_3_480Multiplier foldGlobal_3_480Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_481Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .y), (.xy, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_481Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (1 / 5 : ℚ), 0, (3 / 5 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_481Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (3 / 19 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (87 / 1900 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (6 / 95 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3 / 475 : ℚ)
  else 0

def foldGlobal_3_481Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_481_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_481Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_481Network foldGlobal_3_481Generator (-1 : ℚ)
    foldGlobal_3_481Multiplier foldGlobal_3_481Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_482Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .y), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_482Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_482Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 2 then (116 / 1425 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16 / 1425 : ℚ)
  else 0

def foldGlobal_3_482Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_482_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_482Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_482Network foldGlobal_3_482Generator (-1 : ℚ)
    foldGlobal_3_482Multiplier foldGlobal_3_482Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_483Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_483Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![(1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0]]

def foldGlobal_3_483Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4223 / 2826 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1061 / 4710 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (232 / 7065 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (16756 / 35325 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (12626 / 35325 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1264 / 3925 : ℚ)
  else 0

def foldGlobal_3_483Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_483_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_483Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_483Network foldGlobal_3_483Generator (-1 : ℚ)
    foldGlobal_3_483Multiplier foldGlobal_3_483Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_484Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero), (.yy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_484Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_484Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (32 / 585 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (24 / 325 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 195 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 195 : ℚ)
  else 0

def foldGlobal_3_484Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_484_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_484Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_484Network foldGlobal_3_484Generator (-1 : ℚ)
    foldGlobal_3_484Multiplier foldGlobal_3_484Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_485Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .xy), (.xx, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_485Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (2 / 3 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_485Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (125 / 266 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1375 / 1596 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (30 / 133 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (100 / 171 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (5 / 21 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 133 : ℚ)
  else 0

def foldGlobal_3_485Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_485_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_485Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_485Network foldGlobal_3_485Generator (-1 : ℚ)
    foldGlobal_3_485Multiplier foldGlobal_3_485Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_486Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .xy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_486Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_486Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (125 / 429 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (45 / 143 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (20 / 143 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (20 / 143 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 429 : ℚ)
  else 0

def foldGlobal_3_486Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_486_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_486Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_486Network foldGlobal_3_486Generator (-1 : ℚ)
    foldGlobal_3_486Multiplier foldGlobal_3_486Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_487Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .xy), (.xy, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_487Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_487Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (125 / 429 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (45 / 143 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (20 / 143 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (20 / 143 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 429 : ℚ)
  else 0

def foldGlobal_3_487Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_487_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_487Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_487Network foldGlobal_3_487Generator (-1 : ℚ)
    foldGlobal_3_487Multiplier foldGlobal_3_487Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_488Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .xy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_488Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_488Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (25 / 156 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (3 / 13 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 13 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 39 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2 / 195 : ℚ)
  else 0

def foldGlobal_3_488Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_488_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_488Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_488Network foldGlobal_3_488Generator (-1 : ℚ)
    foldGlobal_3_488Multiplier foldGlobal_3_488Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_489Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .xy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_489Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_489Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (125 / 266 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (30 / 133 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 133 : ℚ)
  else 0

def foldGlobal_3_489Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_489_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_489Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_489Network foldGlobal_3_489Generator (-1 : ℚ)
    foldGlobal_3_489Multiplier foldGlobal_3_489Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_490Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_490Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0]]

def foldGlobal_3_490Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (137 / 133 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (341 / 532 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (366 / 665 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (125 / 266 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (30 / 133 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 133 : ℚ)
  else 0

def foldGlobal_3_490Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_490_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_490Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_490Network foldGlobal_3_490Generator (-1 : ℚ)
    foldGlobal_3_490Multiplier foldGlobal_3_490Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_491Network : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero), (.yy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_491Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_491Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (99 / 206 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (15 / 103 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (21 / 103 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 103 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (66 / 515 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2 / 103 : ℚ)
  else 0

def foldGlobal_3_491Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_491_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_491Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_491Network foldGlobal_3_491Generator (-1 : ℚ)
    foldGlobal_3_491Multiplier foldGlobal_3_491Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_492Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.x, .y), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_492Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 5 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_4_492Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (40 / 141 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (40 / 141 : ℚ)
  else 0

def foldGlobal_4_492Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_492_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_492Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_492Network foldGlobal_4_492Generator 1
    foldGlobal_4_492Multiplier foldGlobal_4_492Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_493Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.x, .xy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_493Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 5 : ℚ), (2 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 5 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_4_493Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (10 / 51 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (10 / 51 : ℚ)
  else 0

def foldGlobal_4_493Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_493_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_493Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_493Network foldGlobal_4_493Generator 1
    foldGlobal_4_493Multiplier foldGlobal_4_493Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_494Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_494Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 6 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (2 / 9 : ℚ), 0, (4 / 9 : ℚ)],
  ![0, (1 / 5 : ℚ), 0, (2 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_4_494Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (35 / 117 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (35 / 117 : ℚ)
  else 0

def foldGlobal_4_494Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_494_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_494Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_494Network foldGlobal_4_494Generator 1
    foldGlobal_4_494Multiplier foldGlobal_4_494Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_495Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_495Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, (1 / 5 : ℚ), (2 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (3 / 7 : ℚ), 0, (2 / 7 : ℚ), (2 / 7 : ℚ)]]

def foldGlobal_4_495Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 2 ∧ b.val = 2 then (5 / 7 : ℚ)
  else 0

def foldGlobal_4_495Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_495_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_495Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_495Network foldGlobal_4_495Generator 1
    foldGlobal_4_495Multiplier foldGlobal_4_495Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_496Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_496Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 5 : ℚ), (2 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_496Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (20 / 63 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (20 / 63 : ℚ)
  else 0

def foldGlobal_4_496Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_496_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_496Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_496Network foldGlobal_4_496Generator 1
    foldGlobal_4_496Multiplier foldGlobal_4_496Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_497Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_497Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_497Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-16 / 133 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1024 / 1197 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (316 / 399 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8 / 133 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (352 / 1197 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (298 / 1197 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (58 / 133 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (32 / 1197 : ℚ)
  else 0

def foldGlobal_4_497Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_497_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_497Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_497Network foldGlobal_4_497Generator 1
    foldGlobal_4_497Multiplier foldGlobal_4_497Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_498Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_498Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_498Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (50 / 153 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (5 / 17 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (14 / 51 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (122 / 255 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 153 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (1 / 15 : ℚ)
  else 0

def foldGlobal_4_498Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_498_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_498Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_498Network foldGlobal_4_498Generator 1
    foldGlobal_4_498Multiplier foldGlobal_4_498Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_499Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_499Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_499Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (46 / 195 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (11 / 26 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (194 / 585 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (19 / 39 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 585 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (2 / 15 : ℚ)
  else 0

def foldGlobal_4_499Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_499_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_499Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_499Network foldGlobal_4_499Generator 1
    foldGlobal_4_499Multiplier foldGlobal_4_499Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
