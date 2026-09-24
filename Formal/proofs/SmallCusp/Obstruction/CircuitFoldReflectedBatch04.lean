import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_3_200Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .yy), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_200Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_200Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-15 / 28 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-25 / 56 : ℚ)
  else 0

def foldGlobal_3_200Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_200_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_200Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_200Network foldGlobal_3_200Generator 1
    foldGlobal_3_200Multiplier foldGlobal_3_200Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_201Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_201Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_201Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-24 / 325 : ℚ)
  else 0

def foldGlobal_3_201Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_201_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_201Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_201Network foldGlobal_3_201Generator 1
    foldGlobal_3_201Multiplier foldGlobal_3_201Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_202Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_202Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0]]

def foldGlobal_3_202Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 18 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-4 / 9 : ℚ)
  else 0

def foldGlobal_3_202Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_202_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_202Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_202Network foldGlobal_3_202Generator 1
    foldGlobal_3_202Multiplier foldGlobal_3_202Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_203Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .yy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_203Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_203Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8 / 27 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-16 / 81 : ℚ)
  else 0

def foldGlobal_3_203Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_203_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_203Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_203Network foldGlobal_3_203Generator 1
    foldGlobal_3_203Multiplier foldGlobal_3_203Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_204Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_204Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_204Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-25 / 56 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-15 / 28 : ℚ)
  else 0

def foldGlobal_3_204Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_204_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_204Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_204Network foldGlobal_3_204Generator 1
    foldGlobal_3_204Multiplier foldGlobal_3_204Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_205Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .yy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_205Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_205Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-15 / 28 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-25 / 56 : ℚ)
  else 0

def foldGlobal_3_205Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_205_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_205Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_205Network foldGlobal_3_205Generator 1
    foldGlobal_3_205Multiplier foldGlobal_3_205Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_206Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_206Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)]]

def foldGlobal_3_206Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 49 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (2 / 49 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 49 : ℚ)
  else 0

def foldGlobal_3_206Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_206_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_206Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_206Network foldGlobal_3_206Generator 1
    foldGlobal_3_206Multiplier foldGlobal_3_206Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_207Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_207Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_207Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 36 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 36 : ℚ)
  else 0

def foldGlobal_3_207Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 2, 2⟩}

theorem foldGlobal_3_207_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_207Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_207Network foldGlobal_3_207Generator 1
    foldGlobal_3_207Multiplier foldGlobal_3_207Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_208Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_208Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_208Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (1 / 52 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 52 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 52 : ℚ)
  else 0

def foldGlobal_3_208Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 2, 2⟩}

theorem foldGlobal_3_208_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_208Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_208Network foldGlobal_3_208Generator 1
    foldGlobal_3_208Multiplier foldGlobal_3_208Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_209Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_209Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 6 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_209Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-3 / 104 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-77 / 156 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 13 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-23 / 104 : ℚ)
  else 0

def foldGlobal_3_209Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_209_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_209Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_209Network foldGlobal_3_209Generator 1
    foldGlobal_3_209Multiplier foldGlobal_3_209Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_210Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.x, .xx), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_210Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_210Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-25 / 111 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-64 / 333 : ℚ)
  else 0

def foldGlobal_3_210Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_210_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_210Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_210Network foldGlobal_3_210Generator 1
    foldGlobal_3_210Multiplier foldGlobal_3_210Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_211Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.x, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_211Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), 0, (2 / 7 : ℚ), 0, (3 / 7 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_211Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-66184 / 659491 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-41912 / 471065 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (360 / 13459 : ℚ)
  else 0

def foldGlobal_3_211Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_211_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_211Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_211Network foldGlobal_3_211Generator 1
    foldGlobal_3_211Multiplier foldGlobal_3_211Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_212Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_212Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(2 / 7 : ℚ), 0, (2 / 7 : ℚ), (3 / 7 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_212Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-112 / 207 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-32 / 23 : ℚ)
  else 0

def foldGlobal_3_212Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_212_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_212Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_212Network foldGlobal_3_212Generator 1
    foldGlobal_3_212Multiplier foldGlobal_3_212Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_213Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_213Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_213Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (32 / 35 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (2 / 7 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-3 / 35 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (3 / 35 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (86 / 315 : ℚ)
  else 0

def foldGlobal_3_213Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_213_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_213Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_213Network foldGlobal_3_213Generator 1
    foldGlobal_3_213Multiplier foldGlobal_3_213Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_214Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_214Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)]]

def foldGlobal_3_214Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (125 / 218 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (125 / 218 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8 / 109 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (128 / 327 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 109 : ℚ)
  else 0

def foldGlobal_3_214Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_214_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_214Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_214Network foldGlobal_3_214Generator 1
    foldGlobal_3_214Multiplier foldGlobal_3_214Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_215Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_215Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_215Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (125 / 218 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (125 / 218 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8 / 109 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (128 / 327 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 109 : ℚ)
  else 0

def foldGlobal_3_215Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_215_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_215Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_215Network foldGlobal_3_215Generator 1
    foldGlobal_3_215Multiplier foldGlobal_3_215Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_216Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_216Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_216Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (89 / 92 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (5 / 46 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (143 / 828 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (3 / 92 : ℚ)
  else 0

def foldGlobal_3_216Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_216_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_216Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_216Network foldGlobal_3_216Generator 1
    foldGlobal_3_216Multiplier foldGlobal_3_216Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_217Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_217Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0]]

def foldGlobal_3_217Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (27 / 50 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (27 / 50 : ℚ)
  else 0

def foldGlobal_3_217Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_217_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_217Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_217Network foldGlobal_3_217Generator 1
    foldGlobal_3_217Multiplier foldGlobal_3_217Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_218Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_218Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_218Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (27 / 50 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (27 / 50 : ℚ)
  else 0

def foldGlobal_3_218Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_218_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_218Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_218Network foldGlobal_3_218Generator 1
    foldGlobal_3_218Multiplier foldGlobal_3_218Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_219Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_219Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_219Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (88 / 89 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (10 / 267 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (106 / 801 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 89 : ℚ)
  else 0

def foldGlobal_3_219Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_219_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_219Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_219Network foldGlobal_3_219Generator 1
    foldGlobal_3_219Multiplier foldGlobal_3_219Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_220Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_220Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_220Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (17 / 32 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (17 / 32 : ℚ)
  else 0

def foldGlobal_3_220Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_220_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_220Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_220Network foldGlobal_3_220Generator 1
    foldGlobal_3_220Multiplier foldGlobal_3_220Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_221Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_221Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_221Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (17 / 32 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (17 / 32 : ℚ)
  else 0

def foldGlobal_3_221Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_221_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_221Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_221Network foldGlobal_3_221Generator 1
    foldGlobal_3_221Multiplier foldGlobal_3_221Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_222Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_222Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_222Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (9 / 32 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-17 / 32 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-9 / 32 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (5 / 32 : ℚ)
  else 0

def foldGlobal_3_222Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_222_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_222Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_222Network foldGlobal_3_222Generator 1
    foldGlobal_3_222Multiplier foldGlobal_3_222Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_223Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_223Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ)]]

def foldGlobal_3_223Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 44 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1 / 44 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 44 : ℚ)
  else 0

def foldGlobal_3_223Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_223_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_223Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_223Network foldGlobal_3_223Generator 1
    foldGlobal_3_223Multiplier foldGlobal_3_223Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_224Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_224Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_224Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 2 : ℚ)
  else 0

def foldGlobal_3_224Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_224_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_224Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_224Network foldGlobal_3_224Generator 1
    foldGlobal_3_224Multiplier foldGlobal_3_224Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_225Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_225Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_225Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (1 / 62 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 62 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 62 : ℚ)
  else 0

def foldGlobal_3_225Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 2, 2⟩}

theorem foldGlobal_3_225_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_225Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_225Network foldGlobal_3_225Generator 1
    foldGlobal_3_225Multiplier foldGlobal_3_225Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_226Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_226Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_226Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else 0

def foldGlobal_3_226Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_226_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_226Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_226Network foldGlobal_3_226Generator 1
    foldGlobal_3_226Multiplier foldGlobal_3_226Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_227Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.y, .yy), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_227Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_227Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (1 / 80 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 80 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 80 : ℚ)
  else 0

def foldGlobal_3_227Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 2, 2⟩}

theorem foldGlobal_3_227_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_227Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_227Network foldGlobal_3_227Generator 1
    foldGlobal_3_227Multiplier foldGlobal_3_227Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_228Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_228Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 5 : ℚ), 0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ)]]

def foldGlobal_3_228Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-15 / 46 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-9 / 230 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-3 / 23 : ℚ)
  else 0

def foldGlobal_3_228Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_228_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_228Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_228Network foldGlobal_3_228Generator (-1 : ℚ)
    foldGlobal_3_228Multiplier foldGlobal_3_228Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_229Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_229Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_3_229Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 39 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-8 / 39 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 3 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-8 / 39 : ℚ)
  else 0

def foldGlobal_3_229Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_229_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_229Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_229Network foldGlobal_3_229Generator (-1 : ℚ)
    foldGlobal_3_229Multiplier foldGlobal_3_229Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_230Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_230Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 5 : ℚ), 0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_230Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 42 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-5 / 42 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-25 / 126 : ℚ)
  else 0

def foldGlobal_3_230Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_230_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_230Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_230Network foldGlobal_3_230Generator (-1 : ℚ)
    foldGlobal_3_230Multiplier foldGlobal_3_230Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_231Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_231Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_3_231Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 24 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 6 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 24 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 24 : ℚ)
  else 0

def foldGlobal_3_231Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_231_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_231Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_231Network foldGlobal_3_231Generator (-1 : ℚ)
    foldGlobal_3_231Multiplier foldGlobal_3_231Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_232Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .xx), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_232Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 5 : ℚ), 0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_232Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-3 / 224 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-5 / 56 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-25 / 224 : ℚ)
  else 0

def foldGlobal_3_232Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_232_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_232Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_232Network foldGlobal_3_232Generator (-1 : ℚ)
    foldGlobal_3_232Multiplier foldGlobal_3_232Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_233Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_233Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)]]

def foldGlobal_3_233Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 20 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 4 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 20 : ℚ)
  else 0

def foldGlobal_3_233Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_233_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_233Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_233Network foldGlobal_3_233Generator (-1 : ℚ)
    foldGlobal_3_233Multiplier foldGlobal_3_233Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_234Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_234Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_234Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 20 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 4 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 20 : ℚ)
  else 0

def foldGlobal_3_234Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_234_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_234Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_234Network foldGlobal_3_234Generator (-1 : ℚ)
    foldGlobal_3_234Multiplier foldGlobal_3_234Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_235Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_235Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_235Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 28 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 28 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 28 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 28 : ℚ)
  else 0

def foldGlobal_3_235Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_235_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_235Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_235Network foldGlobal_3_235Generator (-1 : ℚ)
    foldGlobal_3_235Multiplier foldGlobal_3_235Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_236Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_236Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_236Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 117 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 117 : ℚ)
  else 0

def foldGlobal_3_236Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_236_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_236Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_236Network foldGlobal_3_236Generator (-1 : ℚ)
    foldGlobal_3_236Multiplier foldGlobal_3_236Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_237Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.y, .xy), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_237Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_237Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 36 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 36 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 36 : ℚ)
  else 0

def foldGlobal_3_237Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_237_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_237Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_237Network foldGlobal_3_237Generator (-1 : ℚ)
    foldGlobal_3_237Multiplier foldGlobal_3_237Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_238Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .zero), (.xy, .y), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_238Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_3_238Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 2 then (-1 / 12 : ℚ)
  else 0

def foldGlobal_3_238Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_238_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_238Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_238Network foldGlobal_3_238Generator (-1 : ℚ)
    foldGlobal_3_238Multiplier foldGlobal_3_238Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_239Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .zero), (.xy, .y), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_239Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_239Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 2 then (-2 / 25 : ℚ)
  else 0

def foldGlobal_3_239Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_239_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_239Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_239Network foldGlobal_3_239Generator (-1 : ℚ)
    foldGlobal_3_239Multiplier foldGlobal_3_239Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_240Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .zero), (.xy, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_240Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(2 / 7 : ℚ), 0, 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_240Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-3 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4 / 35 : ℚ)
  else 0

def foldGlobal_3_240Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_240_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_240Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_240Network foldGlobal_3_240Generator (-1 : ℚ)
    foldGlobal_3_240Multiplier foldGlobal_3_240Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_241Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_241Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_241Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 8 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 3 : ℚ)
  else 0

def foldGlobal_3_241Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_241_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_241Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_241Network foldGlobal_3_241Generator (-1 : ℚ)
    foldGlobal_3_241Multiplier foldGlobal_3_241Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_242Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .x), (.xy, .y), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_242Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_3_242Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-1 / 24 : ℚ)
  else 0

def foldGlobal_3_242Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_242_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_242Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_242Network foldGlobal_3_242Generator (-1 : ℚ)
    foldGlobal_3_242Multiplier foldGlobal_3_242Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_243Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .x), (.xy, .y), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_243Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_243Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-2 / 35 : ℚ)
  else 0

def foldGlobal_3_243Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_243_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_243Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_243Network foldGlobal_3_243Generator (-1 : ℚ)
    foldGlobal_3_243Multiplier foldGlobal_3_243Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_244Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .x), (.xy, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_244Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(2 / 7 : ℚ), 0, 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_244Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-4 / 63 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (104 / 441 : ℚ)
  else 0

def foldGlobal_3_244Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_244_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_244Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_244Network foldGlobal_3_244Generator (-1 : ℚ)
    foldGlobal_3_244Multiplier foldGlobal_3_244Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_245Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .x), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_245Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_245Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-4 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-3 / 112 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else 0

def foldGlobal_3_245Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_245_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_245Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_245Network foldGlobal_3_245Generator (-1 : ℚ)
    foldGlobal_3_245Multiplier foldGlobal_3_245Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_246Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .y), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_246Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 6 : ℚ)]]

def foldGlobal_3_246Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-1 / 36 : ℚ)
  else 0

def foldGlobal_3_246Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_246_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_246Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_246Network foldGlobal_3_246Generator (-1 : ℚ)
    foldGlobal_3_246Multiplier foldGlobal_3_246Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_247Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_247Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_247Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-2 / 45 : ℚ)
  else 0

def foldGlobal_3_247Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_247_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_247Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_247Network foldGlobal_3_247Generator (-1 : ℚ)
    foldGlobal_3_247Multiplier foldGlobal_3_247Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_248Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .y), (.xy, .xx), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_248Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![(2 / 7 : ℚ), 0, (4 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_3_248Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-1 / 28 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (10 / 49 : ℚ)
  else 0

def foldGlobal_3_248Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_248_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_248Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_248Network foldGlobal_3_248Generator (-1 : ℚ)
    foldGlobal_3_248Multiplier foldGlobal_3_248Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_249Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_249Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 6 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_249Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-5 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-5 / 12 : ℚ)
  else 0

def foldGlobal_3_249Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_249_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_249Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_249Network foldGlobal_3_249Generator 1
    foldGlobal_3_249Multiplier foldGlobal_3_249Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
