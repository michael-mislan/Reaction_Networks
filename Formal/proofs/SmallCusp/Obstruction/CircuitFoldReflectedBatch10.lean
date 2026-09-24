import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_4_500Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_500Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_500Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 49 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-71 / 392 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 98 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-15 / 784 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (3 / 196 : ℚ)
  else 0

def foldGlobal_4_500Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_500_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_500Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_500Network foldGlobal_4_500Generator 1
    foldGlobal_4_500Multiplier foldGlobal_4_500Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_501Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_501Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_501Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-499 / 1828 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (47 / 1828 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1891 / 2742 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1117 / 4570 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-383 / 3656 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-15821 / 24678 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-1259 / 9140 : ℚ)
  else 0

def foldGlobal_4_501Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_501_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_501Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_501Network foldGlobal_4_501Generator 1
    foldGlobal_4_501Multiplier foldGlobal_4_501Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_502Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_502Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_502Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-861 / 2266 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-571 / 2266 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1766 / 5665 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-580 / 3399 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-398 / 16995 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (20 / 1133 : ℚ)
  else 0

def foldGlobal_4_502Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_502_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_502Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_502Network foldGlobal_4_502Generator 1
    foldGlobal_4_502Multiplier foldGlobal_4_502Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_503Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_503Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_4_503Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-64 / 545 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-128 / 327 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-256 / 327 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-96 / 545 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-64 / 545 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-32 / 109 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-64 / 545 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-184 / 545 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (64 / 2725 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-4464 / 13625 : ℚ)
  else 0

def foldGlobal_4_503Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_503_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_503Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_503Network foldGlobal_4_503Generator 1
    foldGlobal_4_503Multiplier foldGlobal_4_503Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_504Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .xy), (.xx, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_504Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_504Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 8 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-3 / 8 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 16 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (1 / 16 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 4 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (1 / 8 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-1 / 4 : ℚ)
  else 0

def foldGlobal_4_504Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_504_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_504Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_504Network foldGlobal_4_504Generator 1
    foldGlobal_4_504Multiplier foldGlobal_4_504Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_505Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .xy), (.xx, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_505Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_505Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 21 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-2 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-4 / 189 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 21 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-2 / 21 : ℚ)
  else 0

def foldGlobal_4_505Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_505_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_505Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_505Network foldGlobal_4_505Generator 1
    foldGlobal_4_505Multiplier foldGlobal_4_505Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_506Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .yy), (.xx, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_506Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_506Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 135 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-28 / 405 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-52 / 405 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 45 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 45 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-1 / 15 : ℚ)
  else 0

def foldGlobal_4_506Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_506_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_506Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_506Network foldGlobal_4_506Generator 1
    foldGlobal_4_506Multiplier foldGlobal_4_506Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_507Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_507Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_507Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 77 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-4 / 33 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-40 / 231 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-2 / 77 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 77 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-8 / 77 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-6 / 77 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-6 / 77 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (9 / 154 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-2 / 77 : ℚ)
  else 0

def foldGlobal_4_507Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_507_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_507Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_507Network foldGlobal_4_507Generator 1
    foldGlobal_4_507Multiplier foldGlobal_4_507Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_508Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .zero), (.y, .xy), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_508Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_508Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 12 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-7 / 36 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 48 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-5 / 24 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (1 / 48 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (1 / 36 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-1 / 9 : ℚ)
  else 0

def foldGlobal_4_508Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_508_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_508Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_508Network foldGlobal_4_508Generator 1
    foldGlobal_4_508Multiplier foldGlobal_4_508Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_509Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_509Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_509Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (55 / 54 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (25 / 54 : ℚ)
  else 0

def foldGlobal_4_509Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 3⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_509_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_509Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_509Network foldGlobal_4_509Generator (-1 : ℚ)
    foldGlobal_4_509Multiplier foldGlobal_4_509Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_510Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_510Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_510Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then 1
  else if a.val = 2 ∧ b.val = 2 then (4 / 9 : ℚ)
  else 0

def foldGlobal_4_510Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 3⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_510_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_510Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_510Network foldGlobal_4_510Generator (-1 : ℚ)
    foldGlobal_4_510Multiplier foldGlobal_4_510Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_511Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_511Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_511Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (13 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 36 : ℚ)
  else 0

def foldGlobal_4_511Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_511_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_511Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_511Network foldGlobal_4_511Generator (-1 : ℚ)
    foldGlobal_4_511Multiplier foldGlobal_4_511Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_512Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_512Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_512Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1 / 3 : ℚ)
  else 0

def foldGlobal_4_512Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_512_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_512Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_512Network foldGlobal_4_512Generator (-1 : ℚ)
    foldGlobal_4_512Multiplier foldGlobal_4_512Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_513Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_513Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_4_513Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-125 / 468 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 13 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-77 / 156 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-11 / 52 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-25 / 208 : ℚ)
  else 0

def foldGlobal_4_513Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_513_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_513Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_513Network foldGlobal_4_513Generator 1
    foldGlobal_4_513Multiplier foldGlobal_4_513Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_514Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_514Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_514Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-23 / 228 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (91 / 228 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 38 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (85 / 342 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (1 / 38 : ℚ)
  else 0

def foldGlobal_4_514Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_514_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_514Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_514Network foldGlobal_4_514Generator 1
    foldGlobal_4_514Multiplier foldGlobal_4_514Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_515Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.x, .xy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_515Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_515Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 48 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1 / 72 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (2 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (17 / 72 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 144 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (2 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (11 / 48 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (1 / 144 : ℚ)
  else 0

def foldGlobal_4_515Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_515_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_515Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_515Network foldGlobal_4_515Generator 1
    foldGlobal_4_515Multiplier foldGlobal_4_515Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_516Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_516Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 6 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_516Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (53 / 195 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (14 / 117 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (22 / 39 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (6 / 65 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (2 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (184 / 585 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (6 / 65 : ℚ)
  else 0

def foldGlobal_4_516Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_516_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_516Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_516Network foldGlobal_4_516Generator 1
    foldGlobal_4_516Multiplier foldGlobal_4_516Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_517Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_517Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_517Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (104 / 231 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (164 / 385 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (158 / 693 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (2 / 77 : ℚ)
  else 0

def foldGlobal_4_517Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_517_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_517Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_517Network foldGlobal_4_517Generator 1
    foldGlobal_4_517Multiplier foldGlobal_4_517Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_518Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_518Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_518Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (28 / 75 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (77 / 225 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (34 / 225 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (2 / 225 : ℚ)
  else 0

def foldGlobal_4_518Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_518_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_518Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_518Network foldGlobal_4_518Generator 1
    foldGlobal_4_518Multiplier foldGlobal_4_518Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_519Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_519Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_519Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-656 / 2817 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-31 / 1878 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-48 / 313 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-815 / 1878 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-637 / 1878 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-559 / 2817 : ℚ)
  else 0

def foldGlobal_4_519Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_519_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_519Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_519Network foldGlobal_4_519Generator 1
    foldGlobal_4_519Multiplier foldGlobal_4_519Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_520Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_520Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_520Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 7 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-6 / 77 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (4 / 77 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 231 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-9 / 154 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-8 / 77 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 231 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-2 / 231 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (4 / 231 : ℚ)
  else 0

def foldGlobal_4_520Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_520_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_520Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_520Network foldGlobal_4_520Generator 1
    foldGlobal_4_520Multiplier foldGlobal_4_520Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_521Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_521Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_521Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 43 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 43 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-32 / 387 : ℚ)
  else 0

def foldGlobal_4_521Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_521_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_521Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_521Network foldGlobal_4_521Generator 1
    foldGlobal_4_521Multiplier foldGlobal_4_521Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_522Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_522Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_522Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-148 / 605 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-247 / 2904 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (10 / 121 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-534 / 3025 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2011 / 7260 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1893 / 12100 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-139 / 1089 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-119 / 1815 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (2 / 121 : ℚ)
  else 0

def foldGlobal_4_522Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_522_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_522Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_522Network foldGlobal_4_522Generator 1
    foldGlobal_4_522Multiplier foldGlobal_4_522Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_523Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .zero), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_523Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_523Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-4 / 29 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (8 / 261 : ℚ)
  else 0

def foldGlobal_4_523Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_523_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_523Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_523Network foldGlobal_4_523Generator 1
    foldGlobal_4_523Multiplier foldGlobal_4_523Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_524Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .x), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_524Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_524Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-51 / 50 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-203 / 600 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-19 / 50 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 100 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 400 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (3 / 100 : ℚ)
  else 0

def foldGlobal_4_524Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_524_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_524Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_524Network foldGlobal_4_524Generator 1
    foldGlobal_4_524Multiplier foldGlobal_4_524Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_525Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_525Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 3 : ℚ), 0, (1 / 6 : ℚ)],
  ![0, 0, (1 / 6 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_525Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-455 / 3312 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-15 / 46 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 138 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-203 / 3312 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (3 / 46 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-173 / 207 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-28 / 69 : ℚ)
  else 0

def foldGlobal_4_525Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_525_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_525Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_525Network foldGlobal_4_525Generator 1
    foldGlobal_4_525Multiplier foldGlobal_4_525Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_526Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .xy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_526Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_526Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-6 / 175 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-172 / 525 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 175 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (87 / 700 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (9 / 175 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-179 / 700 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-43 / 210 : ℚ)
  else 0

def foldGlobal_4_526Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_526_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_526Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_526Network foldGlobal_4_526Generator 1
    foldGlobal_4_526Multiplier foldGlobal_4_526Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_527Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_527Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_4_527Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (16 / 145 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (12 / 145 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 145 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (4 / 145 : ℚ)
  else 0

def foldGlobal_4_527Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_527_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_527Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_527Network foldGlobal_4_527Generator 1
    foldGlobal_4_527Multiplier foldGlobal_4_527Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_528Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_528Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_528Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else 0

def foldGlobal_4_528Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_528_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_528Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_528Network foldGlobal_4_528Generator 1
    foldGlobal_4_528Multiplier foldGlobal_4_528Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_529Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .zero), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_529Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_529Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 6 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 9 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (1 / 54 : ℚ)
  else 0

def foldGlobal_4_529Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_529_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_529Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_529Network foldGlobal_4_529Generator 1
    foldGlobal_4_529Multiplier foldGlobal_4_529Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_530Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .x), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_530Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_530Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (1 / 152 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (3 / 38 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 152 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1 / 19 : ℚ)
  else 0

def foldGlobal_4_530Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_530_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_530Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_530Network foldGlobal_4_530Generator 1
    foldGlobal_4_530Multiplier foldGlobal_4_530Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_531Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_531Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 6 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_531Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (2 / 171 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (2 / 19 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 171 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-4 / 57 : ℚ)
  else 0

def foldGlobal_4_531Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_531_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_531Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_531Network foldGlobal_4_531Generator 1
    foldGlobal_4_531Multiplier foldGlobal_4_531Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_532Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .xy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_532Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_532Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (2 / 243 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (2 / 27 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 243 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-2 / 27 : ℚ)
  else 0

def foldGlobal_4_532Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_532_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_532Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_532Network foldGlobal_4_532Generator 1
    foldGlobal_4_532Multiplier foldGlobal_4_532Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_533Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_533Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_4_533Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 2 ∧ b.val = 2 then (1 / 9 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (1 / 9 : ℚ)
  else 0

def foldGlobal_4_533Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 2, 2, 2⟩, ⟨0, 3, 3, 3⟩, ⟨1, 2, 2, 2⟩}

theorem foldGlobal_4_533_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_533Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_533Network foldGlobal_4_533Generator 1
    foldGlobal_4_533Multiplier foldGlobal_4_533Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_534Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_534Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_534Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 9 : ℚ)
  else 0

def foldGlobal_4_534Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_534_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_534Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_534Network foldGlobal_4_534Generator 1
    foldGlobal_4_534Multiplier foldGlobal_4_534Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_535Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_535Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_535Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-6 / 145 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (1 / 145 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8 / 145 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-21 / 1160 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 145 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 145 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-6 / 145 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (1 / 145 : ℚ)
  else 0

def foldGlobal_4_535Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_535_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_535Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_535Network foldGlobal_4_535Generator 1
    foldGlobal_4_535Multiplier foldGlobal_4_535Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_536Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_536Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_4_536Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-45 / 1216 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-3 / 76 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-7 / 114 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-25 / 608 : ℚ)
  else 0

def foldGlobal_4_536Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_536_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_536Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_536Network foldGlobal_4_536Generator 1
    foldGlobal_4_536Multiplier foldGlobal_4_536Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_537Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_537Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_537Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-3 / 35 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (1 / 35 : ℚ)
  else 0

def foldGlobal_4_537Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_537_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_537Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_537Network foldGlobal_4_537Generator 1
    foldGlobal_4_537Multiplier foldGlobal_4_537Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_538Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_538Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_538Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-803 / 7036 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (374 / 5277 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1705 / 10554 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1042 / 5277 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1624 / 5277 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 3 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (9 / 1759 : ℚ)
  else 0

def foldGlobal_4_538Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_538_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_538Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_538Network foldGlobal_4_538Generator 1
    foldGlobal_4_538Multiplier foldGlobal_4_538Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_539Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .x), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_539Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_539Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-551 / 9696 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (109 / 2424 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-193 / 1212 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-385 / 9696 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-875 / 7272 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 6 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3 / 404 : ℚ)
  else 0

def foldGlobal_4_539Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_539_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_539Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_539Network foldGlobal_4_539Generator 1
    foldGlobal_4_539Multiplier foldGlobal_4_539Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_540Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_540Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_540Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (585 / 2348 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-985 / 3522 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 587 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-650 / 5283 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 8 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (6 / 587 : ℚ)
  else 0

def foldGlobal_4_540Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_540_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_540Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_540Network foldGlobal_4_540Generator 1
    foldGlobal_4_540Multiplier foldGlobal_4_540Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_541Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_541Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_4_541Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-1 / 32 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-25 / 192 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-2 / 9 : ℚ)
  else 0

def foldGlobal_4_541Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 3⟩}

theorem foldGlobal_4_541_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_541Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_541Network foldGlobal_4_541Generator 1
    foldGlobal_4_541Multiplier foldGlobal_4_541Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_542Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_542Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_542Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2369 / 29320 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-54 / 733 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-18 / 3665 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1288 / 18325 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-5458 / 32985 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-56 / 3665 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-492 / 18325 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16 / 3665 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (528 / 18325 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (16 / 3665 : ℚ)
  else 0

def foldGlobal_4_542Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_542_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_542Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_542Network foldGlobal_4_542Generator 1
    foldGlobal_4_542Multiplier foldGlobal_4_542Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_543Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_543Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_4_543Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-1 / 8 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (1 / 112 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-3 / 56 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 56 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-261 / 1400 : ℚ)
  else 0

def foldGlobal_4_543Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_543_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_543Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_543Network foldGlobal_4_543Generator 1
    foldGlobal_4_543Multiplier foldGlobal_4_543Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_544Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.yy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_544Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_544Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-29 / 152 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-94 / 95 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-3599 / 8550 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-67 / 285 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-137 / 475 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-43 / 75 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-89 / 190 : ℚ)
  else 0

def foldGlobal_4_544Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_544_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_544Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_544Network foldGlobal_4_544Generator 1
    foldGlobal_4_544Multiplier foldGlobal_4_544Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_545Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_545Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 2 : ℚ), 0, (1 / 6 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_545Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-407 / 468 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-35 / 117 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (139 / 468 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-77 / 312 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 312 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (1 / 26 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-79 / 234 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-7 / 39 : ℚ)
  else 0

def foldGlobal_4_545Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_545_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_545Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_545Network foldGlobal_4_545Generator 1
    foldGlobal_4_545Multiplier foldGlobal_4_545Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_546Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_546Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 6 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_546Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 3 then (25 / 234 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 702 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (1 / 78 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-313 / 702 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-53 / 234 : ℚ)
  else 0

def foldGlobal_4_546Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_546_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_546Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_546Network foldGlobal_4_546Generator 1
    foldGlobal_4_546Multiplier foldGlobal_4_546Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_547Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_547Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 6 : ℚ), (1 / 2 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_547Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (4 / 513 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (4 / 57 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-179 / 1026 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-3 / 19 : ℚ)
  else 0

def foldGlobal_4_547Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_547_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_547Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_547Network foldGlobal_4_547Generator 1
    foldGlobal_4_547Multiplier foldGlobal_4_547Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_548Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_548Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_4_548Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (3 / 46 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (3 / 46 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 92 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (1 / 46 : ℚ)
  else 0

def foldGlobal_4_548Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_548_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_548Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_548Network foldGlobal_4_548Generator 1
    foldGlobal_4_548Multiplier foldGlobal_4_548Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_549Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_549Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_549Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 6 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 9 : ℚ)
  else 0

def foldGlobal_4_549Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_549_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_549Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_549Network foldGlobal_4_549Generator 1
    foldGlobal_4_549Multiplier foldGlobal_4_549Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
