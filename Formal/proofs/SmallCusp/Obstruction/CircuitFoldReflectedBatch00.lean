import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_3_00Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.x, .zero), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_00Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (2 / 3 : ℚ), 0, 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_00Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-2 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-5 / 9 : ℚ)
  else 0

def foldGlobal_3_00Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_00_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_00Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_00Network foldGlobal_3_00Generator 1
    foldGlobal_3_00Multiplier foldGlobal_3_00Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_01Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_01Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 7 : ℚ), (2 / 7 : ℚ), (4 / 7 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_01Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-7 / 218 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 109 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-7 / 218 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-40 / 763 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 109 : ℚ)
  else 0

def foldGlobal_3_01Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_01_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_01Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_01Network foldGlobal_3_01Generator 1
    foldGlobal_3_01Multiplier foldGlobal_3_01Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_02Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.y, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_02Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 7 : ℚ), (2 / 7 : ℚ), (4 / 7 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_02Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 72 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-5 / 63 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 72 : ℚ)
  else 0

def foldGlobal_3_02Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_02_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_02Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_02Network foldGlobal_3_02Generator 1
    foldGlobal_3_02Multiplier foldGlobal_3_02Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_03Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.x, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_03Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 5 : ℚ), (2 / 5 : ℚ), 0, (2 / 5 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_03Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-5470 / 35739 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-13174 / 59565 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-952 / 19855 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-23428 / 99275 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-72 / 1805 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (48 / 3971 : ℚ)
  else 0

def foldGlobal_3_03Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_03_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_03Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_03Network foldGlobal_3_03Generator 1
    foldGlobal_3_03Multiplier foldGlobal_3_03Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_04Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_04Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_04Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 9 : ℚ)
  else 0

def foldGlobal_3_04Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_04_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_04Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_04Network foldGlobal_3_04Generator (-1 : ℚ)
    foldGlobal_3_04Multiplier foldGlobal_3_04Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_05Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_05Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), 0]]

def foldGlobal_3_05Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 36 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-5 / 36 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-29 / 240 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (11 / 60 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 36 : ℚ)
  else 0

def foldGlobal_3_05Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_05_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_05Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_05Network foldGlobal_3_05Generator (-1 : ℚ)
    foldGlobal_3_05Multiplier foldGlobal_3_05Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_06Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xx), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_06Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (2 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_06Multiplier (_a _b : Fin 3) : ℚ :=
  0

def foldGlobal_3_06Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_06_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_06Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_06Network foldGlobal_3_06Generator (-1 : ℚ)
    foldGlobal_3_06Multiplier foldGlobal_3_06Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_07Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_07Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_07Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-32 / 61 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-136 / 183 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-32 / 61 : ℚ)
  else 0

def foldGlobal_3_07Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_07_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_07Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_07Network foldGlobal_3_07Generator 1
    foldGlobal_3_07Multiplier foldGlobal_3_07Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_08Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_08Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_08Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 9 : ℚ)
  else 0

def foldGlobal_3_08Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_08_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_08Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_08Network foldGlobal_3_08Generator 1
    foldGlobal_3_08Multiplier foldGlobal_3_08Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_09Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .zero), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_09Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_09Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 45 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 5 : ℚ)
  else 0

def foldGlobal_3_09Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_09_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_09Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_09Network foldGlobal_3_09Generator 1
    foldGlobal_3_09Multiplier foldGlobal_3_09Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_10Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .y), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_10Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_10Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 5 : ℚ)
  else 0

def foldGlobal_3_10Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_10_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_10Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_10Network foldGlobal_3_10Generator 1
    foldGlobal_3_10Multiplier foldGlobal_3_10Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_11Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.y, .xx), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_11Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 6 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_11Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 99 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 297 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4 / 297 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-8 / 99 : ℚ)
  else 0

def foldGlobal_3_11Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_11_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_11Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_11Network foldGlobal_3_11Generator (-1 : ℚ)
    foldGlobal_3_11Multiplier foldGlobal_3_11Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_12Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.y, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_12Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_12Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 19 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 171 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 171 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 19 : ℚ)
  else 0

def foldGlobal_3_12Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_12_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_12Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_12Network foldGlobal_3_12Generator (-1 : ℚ)
    foldGlobal_3_12Multiplier foldGlobal_3_12Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_13Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_13Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_13Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (7 / 1474 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-109 / 3685 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1299 / 36850 : ℚ)
  else 0

def foldGlobal_3_13Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_13_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_13Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_13Network foldGlobal_3_13Generator (-1 : ℚ)
    foldGlobal_3_13Multiplier foldGlobal_3_13Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_14Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_14Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_14Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 2 then (-2 / 45 : ℚ)
  else 0

def foldGlobal_3_14Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_14_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_14Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_14Network foldGlobal_3_14Generator (-1 : ℚ)
    foldGlobal_3_14Multiplier foldGlobal_3_14Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_15Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .xx), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_15Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (4 / 7 : ℚ), 0, (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_15Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (40 / 4141 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1466 / 28987 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (14604 / 202909 : ℚ)
  else 0

def foldGlobal_3_15Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_15_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_15Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_15Network foldGlobal_3_15Generator (-1 : ℚ)
    foldGlobal_3_15Multiplier foldGlobal_3_15Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_16Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .y), (.x, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_16Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_16Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-32 / 207 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-22 / 345 : ℚ)
  else 0

def foldGlobal_3_16Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_16_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_16Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_16Network foldGlobal_3_16Generator 1
    foldGlobal_3_16Multiplier foldGlobal_3_16Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_17Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_17Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_17Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-20 / 37 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-416 / 555 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-24 / 37 : ℚ)
  else 0

def foldGlobal_3_17Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_17_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_17Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_17Network foldGlobal_3_17Generator 1
    foldGlobal_3_17Multiplier foldGlobal_3_17Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_18Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_18Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_18Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-25 / 56 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-15 / 28 : ℚ)
  else 0

def foldGlobal_3_18Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_18_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_18Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_18Network foldGlobal_3_18Generator 1
    foldGlobal_3_18Multiplier foldGlobal_3_18Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_19Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_19Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_19Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 20 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3 / 10 : ℚ)
  else 0

def foldGlobal_3_19Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_19_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_19Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_19Network foldGlobal_3_19Generator 1
    foldGlobal_3_19Multiplier foldGlobal_3_19Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_20Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.x, .y), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_20Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_20Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (9 / 20 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3 / 10 : ℚ)
  else 0

def foldGlobal_3_20Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_20_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_20Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_20Network foldGlobal_3_20Generator 1
    foldGlobal_3_20Multiplier foldGlobal_3_20Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_21Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.x, .xy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_21Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_21Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 15 : ℚ)
  else 0

def foldGlobal_3_21Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_21_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_21Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_21Network foldGlobal_3_21Generator 1
    foldGlobal_3_21Multiplier foldGlobal_3_21Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_22Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_22Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_22Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 89 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 178 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-52 / 2225 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-3 / 89 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 178 : ℚ)
  else 0

def foldGlobal_3_22Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_22_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_22Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_22Network foldGlobal_3_22Generator 1
    foldGlobal_3_22Multiplier foldGlobal_3_22Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_23Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_23Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_23Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 513 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-8 / 171 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-112 / 12825 : ℚ)
  else 0

def foldGlobal_3_23Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_23_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_23Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_23Network foldGlobal_3_23Generator 1
    foldGlobal_3_23Multiplier foldGlobal_3_23Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_24Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_24Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), 0, (1 / 6 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_24Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (9 / 20 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3 / 10 : ℚ)
  else 0

def foldGlobal_3_24Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_24_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_24Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_24Network foldGlobal_3_24Generator 1
    foldGlobal_3_24Multiplier foldGlobal_3_24Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_25Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.x, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_25Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 7 : ℚ), (2 / 7 : ℚ), 0, (3 / 7 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_25Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-4 / 63 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-34 / 147 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 21 : ℚ)
  else 0

def foldGlobal_3_25Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_25_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_25Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_25Network foldGlobal_3_25Generator 1
    foldGlobal_3_25Multiplier foldGlobal_3_25Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_26Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_26Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 7 : ℚ), (2 / 7 : ℚ), (3 / 7 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_26Multiplier (_a _b : Fin 3) : ℚ :=
  0

def foldGlobal_3_26Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_26_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_26Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_26Network foldGlobal_3_26Generator 1
    foldGlobal_3_26Multiplier foldGlobal_3_26Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_27Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_27Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_27Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-3 / 40 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (27 / 40 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (9 / 20 : ℚ)
  else 0

def foldGlobal_3_27Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_27_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_27Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_27Network foldGlobal_3_27Generator 1
    foldGlobal_3_27Multiplier foldGlobal_3_27Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_28Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_28Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_28Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (27 / 40 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 20 : ℚ)
  else 0

def foldGlobal_3_28Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_28_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_28Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_28Network foldGlobal_3_28Generator 1
    foldGlobal_3_28Multiplier foldGlobal_3_28Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_29Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_29Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_29Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 9 : ℚ)
  else 0

def foldGlobal_3_29Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_29_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_29Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_29Network foldGlobal_3_29Generator 1
    foldGlobal_3_29Multiplier foldGlobal_3_29Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_30Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_30Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_30Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 27 : ℚ)
  else 0

def foldGlobal_3_30Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_30_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_30Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_30Network foldGlobal_3_30Generator (-1 : ℚ)
    foldGlobal_3_30Multiplier foldGlobal_3_30Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_31Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_31Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_31Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 13 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-2 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-10 / 117 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 39 : ℚ)
  else 0

def foldGlobal_3_31Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_31_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_31Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_31Network foldGlobal_3_31Generator (-1 : ℚ)
    foldGlobal_3_31Multiplier foldGlobal_3_31Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_32Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.zero, .xy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_32Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_32Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 33 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (16 / 99 : ℚ)
  else 0

def foldGlobal_3_32Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_32_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_32Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_32Network foldGlobal_3_32Generator (-1 : ℚ)
    foldGlobal_3_32Multiplier foldGlobal_3_32Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_33Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .xx), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_33Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_33Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-80 / 141 : ℚ)
  else 0

def foldGlobal_3_33Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_33_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_33Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_33Network foldGlobal_3_33Generator 1
    foldGlobal_3_33Multiplier foldGlobal_3_33Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_34Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_34Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_34Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-80 / 141 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 47 : ℚ)
  else 0

def foldGlobal_3_34Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_34_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_34Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_34Network foldGlobal_3_34Generator 1
    foldGlobal_3_34Multiplier foldGlobal_3_34Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_35Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_35Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_35Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 10 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 10 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 10 : ℚ)
  else 0

def foldGlobal_3_35Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_35_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_35Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_35Network foldGlobal_3_35Generator 1
    foldGlobal_3_35Multiplier foldGlobal_3_35Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_36Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .y), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_36Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_36Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 28 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 28 : ℚ)
  else 0

def foldGlobal_3_36Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_36_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_36Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_36Network foldGlobal_3_36Generator 1
    foldGlobal_3_36Multiplier foldGlobal_3_36Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_37Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_37Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_37Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-6 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-80 / 141 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 47 : ℚ)
  else 0

def foldGlobal_3_37Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_37_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_37Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_37Network foldGlobal_3_37Generator 1
    foldGlobal_3_37Multiplier foldGlobal_3_37Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_38Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_38Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_38Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 28 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else 0

def foldGlobal_3_38Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_38_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_38Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_38Network foldGlobal_3_38Generator 1
    foldGlobal_3_38Multiplier foldGlobal_3_38Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_39Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_39Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_39Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-9 / 32 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-9 / 32 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-3 / 32 : ℚ)
  else 0

def foldGlobal_3_39Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_39_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_39Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_39Network foldGlobal_3_39Generator 1
    foldGlobal_3_39Multiplier foldGlobal_3_39Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_40Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_40Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_40Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-33 / 100 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-12 / 25 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-6 / 25 : ℚ)
  else 0

def foldGlobal_3_40Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_40_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_40Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_40Network foldGlobal_3_40Generator 1
    foldGlobal_3_40Multiplier foldGlobal_3_40Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_41Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_41Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_41Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 13 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 13 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 13 : ℚ)
  else 0

def foldGlobal_3_41Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_41_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_41Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_41Network foldGlobal_3_41Generator 1
    foldGlobal_3_41Multiplier foldGlobal_3_41Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_42Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_42Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_42Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 16 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 16 : ℚ)
  else 0

def foldGlobal_3_42Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_42_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_42Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_42Network foldGlobal_3_42Generator 1
    foldGlobal_3_42Multiplier foldGlobal_3_42Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_43Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_43Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_43Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-29 / 88 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-29 / 88 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-25 / 176 : ℚ)
  else 0

def foldGlobal_3_43Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_43_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_43Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_43Network foldGlobal_3_43Generator 1
    foldGlobal_3_43Multiplier foldGlobal_3_43Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_44Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_44Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_44Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-17 / 44 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else 0

def foldGlobal_3_44Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_44_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_44Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_44Network foldGlobal_3_44Generator 1
    foldGlobal_3_44Multiplier foldGlobal_3_44Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_45Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_45Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_45Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-80 / 141 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 47 : ℚ)
  else 0

def foldGlobal_3_45Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_45_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_45Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_45Network foldGlobal_3_45Generator 1
    foldGlobal_3_45Multiplier foldGlobal_3_45Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_46Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_46Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_46Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 10 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 10 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 10 : ℚ)
  else 0

def foldGlobal_3_46Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_46_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_46Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_46Network foldGlobal_3_46Generator 1
    foldGlobal_3_46Multiplier foldGlobal_3_46Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_47Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_47Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 2 : ℚ), 0, (1 / 6 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_47Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 15 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 15 : ℚ)
  else 0

def foldGlobal_3_47Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_47_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_47Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_47Network foldGlobal_3_47Generator 1
    foldGlobal_3_47Multiplier foldGlobal_3_47Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_48Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.x, .yy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_48Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0]]

def foldGlobal_3_48Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-9 / 16 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-13 / 16 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-9 / 16 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else 0

def foldGlobal_3_48Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_48_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_48Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_48Network foldGlobal_3_48Generator 1
    foldGlobal_3_48Multiplier foldGlobal_3_48Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_49Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .y), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_49Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_49Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-80 / 141 : ℚ)
  else 0

def foldGlobal_3_49Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_49_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_49Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_49Network foldGlobal_3_49Generator 1
    foldGlobal_3_49Multiplier foldGlobal_3_49Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
