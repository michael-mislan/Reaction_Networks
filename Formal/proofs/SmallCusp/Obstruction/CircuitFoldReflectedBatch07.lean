import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_3_350Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_350Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_350Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (5 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (7 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (3 / 4 : ℚ)
  else 0

def foldGlobal_3_350Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_350_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_350Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_350Network foldGlobal_3_350Generator (-1 : ℚ)
    foldGlobal_3_350Multiplier foldGlobal_3_350Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_351Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_351Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_351Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (41 / 78 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (9 / 13 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 39 : ℚ)
  else 0

def foldGlobal_3_351Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_351_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_351Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_351Network foldGlobal_3_351Generator (-1 : ℚ)
    foldGlobal_3_351Multiplier foldGlobal_3_351Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_352Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_352Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0]]

def foldGlobal_3_352Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (35 / 66 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 33 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (23 / 33 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 33 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4 / 33 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2 / 9 : ℚ)
  else 0

def foldGlobal_3_352Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_352_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_352Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_352Network foldGlobal_3_352Generator (-1 : ℚ)
    foldGlobal_3_352Multiplier foldGlobal_3_352Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_353Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_353Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_353Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (67 / 126 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (44 / 63 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (16 / 63 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (2 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 63 : ℚ)
  else 0

def foldGlobal_3_353Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_353_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_353Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_353Network foldGlobal_3_353Generator (-1 : ℚ)
    foldGlobal_3_353Multiplier foldGlobal_3_353Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_354Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_354Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0]]

def foldGlobal_3_354Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (91 / 150 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-6 / 25 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (58 / 75 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8 / 75 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-8 / 75 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2 / 9 : ℚ)
  else 0

def foldGlobal_3_354Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_354_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_354Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_354Network foldGlobal_3_354Generator (-1 : ℚ)
    foldGlobal_3_354Multiplier foldGlobal_3_354Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_355Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_355Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_355Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (94 / 81 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (40 / 81 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (49 / 81 : ℚ)
  else 0

def foldGlobal_3_355Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_355_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_355Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_355Network foldGlobal_3_355Generator (-1 : ℚ)
    foldGlobal_3_355Multiplier foldGlobal_3_355Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_356Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_356Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ), 0]]

def foldGlobal_3_356Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (11 / 12 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (41 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (17 / 36 : ℚ)
  else 0

def foldGlobal_3_356Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_356_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_356Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_356Network foldGlobal_3_356Generator (-1 : ℚ)
    foldGlobal_3_356Multiplier foldGlobal_3_356Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_357Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_357Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_357Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (53 / 45 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (23 / 45 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (13 / 45 : ℚ)
  else 0

def foldGlobal_3_357Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_357_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_357Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_357Network foldGlobal_3_357Generator (-1 : ℚ)
    foldGlobal_3_357Multiplier foldGlobal_3_357Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_358Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_358Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_358Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (17 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (5 / 18 : ℚ)
  else 0

def foldGlobal_3_358Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_358_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_358Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_358Network foldGlobal_3_358Generator (-1 : ℚ)
    foldGlobal_3_358Multiplier foldGlobal_3_358Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_359Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_359Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ), 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_3_359Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (212 / 207 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (74 / 207 : ℚ)
  else 0

def foldGlobal_3_359Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_359_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_359Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_359Network foldGlobal_3_359Generator (-1 : ℚ)
    foldGlobal_3_359Multiplier foldGlobal_3_359Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_360Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_360Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ), 0]]

def foldGlobal_3_360Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (10 / 27 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (46 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (34 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (16 / 27 : ℚ)
  else 0

def foldGlobal_3_360Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_360_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_360Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_360Network foldGlobal_3_360Generator (-1 : ℚ)
    foldGlobal_3_360Multiplier foldGlobal_3_360Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_361Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_361Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_361Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (8 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (10 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (5 / 9 : ℚ)
  else 0

def foldGlobal_3_361Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_361_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_361Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_361Network foldGlobal_3_361Generator (-1 : ℚ)
    foldGlobal_3_361Multiplier foldGlobal_3_361Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_362Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_362Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_362Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (94 / 81 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (49 / 81 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (22 / 81 : ℚ)
  else 0

def foldGlobal_3_362Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_362_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_362Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_362Network foldGlobal_3_362Generator (-1 : ℚ)
    foldGlobal_3_362Multiplier foldGlobal_3_362Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_363Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_363Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_363Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (17 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (7 / 18 : ℚ)
  else 0

def foldGlobal_3_363Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_363_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_363Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_363Network foldGlobal_3_363Generator (-1 : ℚ)
    foldGlobal_3_363Multiplier foldGlobal_3_363Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_364Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_364Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_3_364Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (212 / 207 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (97 / 207 : ℚ)
  else 0

def foldGlobal_3_364Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_364_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_364Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_364Network foldGlobal_3_364Generator (-1 : ℚ)
    foldGlobal_3_364Multiplier foldGlobal_3_364Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_365Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .x), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_365Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_365Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (22 / 81 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (130 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (94 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (49 / 81 : ℚ)
  else 0

def foldGlobal_3_365Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_365_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_365Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_365Network foldGlobal_3_365Generator (-1 : ℚ)
    foldGlobal_3_365Multiplier foldGlobal_3_365Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_366Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_366Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_366Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (11 / 12 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (41 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 4 : ℚ)
  else 0

def foldGlobal_3_366Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_366_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_366Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_366Network foldGlobal_3_366Generator (-1 : ℚ)
    foldGlobal_3_366Multiplier foldGlobal_3_366Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_367Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_367Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_367Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (13 / 18 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (17 / 18 : ℚ)
  else 0

def foldGlobal_3_367Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_367_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_367Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_367Network foldGlobal_3_367Generator (-1 : ℚ)
    foldGlobal_3_367Multiplier foldGlobal_3_367Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_368Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_368Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_3_368Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (28 / 207 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (166 / 207 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (212 / 207 : ℚ)
  else 0

def foldGlobal_3_368Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_368_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_368Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_368Network foldGlobal_3_368Generator (-1 : ℚ)
    foldGlobal_3_368Multiplier foldGlobal_3_368Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_369Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_369Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_369Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (17 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1 / 18 : ℚ)
  else 0

def foldGlobal_3_369Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_369_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_369Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_369Network foldGlobal_3_369Generator (-1 : ℚ)
    foldGlobal_3_369Multiplier foldGlobal_3_369Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_370Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_370Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_3_370Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (212 / 207 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (28 / 207 : ℚ)
  else 0

def foldGlobal_3_370Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_370_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_370Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_370Network foldGlobal_3_370Generator (-1 : ℚ)
    foldGlobal_3_370Multiplier foldGlobal_3_370Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_371Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_371Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_371Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (13 / 45 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (73 / 45 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (53 / 45 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (13 / 45 : ℚ)
  else 0

def foldGlobal_3_371Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_371_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_371Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_371Network foldGlobal_3_371Generator (-1 : ℚ)
    foldGlobal_3_371Multiplier foldGlobal_3_371Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_372Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_372Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_372Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else 0

def foldGlobal_3_372Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_372_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_372Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_372Network foldGlobal_3_372Generator (-1 : ℚ)
    foldGlobal_3_372Multiplier foldGlobal_3_372Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_373Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.yy, .x), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_373Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0]]

def foldGlobal_3_373Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (25 / 18 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (17 / 18 : ℚ)
  else 0

def foldGlobal_3_373Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_373_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_373Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_373Network foldGlobal_3_373Generator (-1 : ℚ)
    foldGlobal_3_373Multiplier foldGlobal_3_373Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_374Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_374Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_374Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (118 / 117 : ℚ)
  else 0

def foldGlobal_3_374Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_374_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_374Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_374Network foldGlobal_3_374Generator (-1 : ℚ)
    foldGlobal_3_374Multiplier foldGlobal_3_374Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_375Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.yy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_375Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ), 0]]

def foldGlobal_3_375Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (28 / 207 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (304 / 207 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (212 / 207 : ℚ)
  else 0

def foldGlobal_3_375Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_375_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_375Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_375Network foldGlobal_3_375Generator (-1 : ℚ)
    foldGlobal_3_375Multiplier foldGlobal_3_375Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_376Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_376Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_376Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (11 / 26 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (20 / 39 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (92 / 117 : ℚ)
  else 0

def foldGlobal_3_376Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_376_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_376Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_376Network foldGlobal_3_376Generator (-1 : ℚ)
    foldGlobal_3_376Multiplier foldGlobal_3_376Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_377Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_377Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_377Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (57 / 154 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (200 / 231 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (86 / 99 : ℚ)
  else 0

def foldGlobal_3_377Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_377_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_377Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_377Network foldGlobal_3_377Generator (-1 : ℚ)
    foldGlobal_3_377Multiplier foldGlobal_3_377Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_378Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_378Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_378Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (11 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (11 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (3 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 9 : ℚ)
  else 0

def foldGlobal_3_378Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_378_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_378Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_378Network foldGlobal_3_378Generator (-1 : ℚ)
    foldGlobal_3_378Multiplier foldGlobal_3_378Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_379Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_379Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_379Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (2 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (4 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 6 : ℚ)
  else 0

def foldGlobal_3_379Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_379_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_379Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_379Network foldGlobal_3_379Generator (-1 : ℚ)
    foldGlobal_3_379Multiplier foldGlobal_3_379Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_380Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_380Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0]]

def foldGlobal_3_380Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 183 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-8 / 183 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (23 / 61 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8 / 183 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-68 / 549 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2 / 9 : ℚ)
  else 0

def foldGlobal_3_380Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_380_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_380Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_380Network foldGlobal_3_380Generator (-1 : ℚ)
    foldGlobal_3_380Multiplier foldGlobal_3_380Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_381Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_381Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_381Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (58 / 45 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (38 / 45 : ℚ)
  else 0

def foldGlobal_3_381Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_381_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_381Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_381Network foldGlobal_3_381Generator (-1 : ℚ)
    foldGlobal_3_381Multiplier foldGlobal_3_381Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_382Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_382Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_382Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (58 / 45 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (38 / 45 : ℚ)
  else 0

def foldGlobal_3_382Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_382_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_382Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_382Network foldGlobal_3_382Generator (-1 : ℚ)
    foldGlobal_3_382Multiplier foldGlobal_3_382Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_383Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_383Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 2 : ℚ), 0]]

def foldGlobal_3_383Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4 / 117 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (56 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (140 / 117 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (88 / 117 : ℚ)
  else 0

def foldGlobal_3_383Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_383_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_383Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_383Network foldGlobal_3_383Generator (-1 : ℚ)
    foldGlobal_3_383Multiplier foldGlobal_3_383Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_384Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_384Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_384Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (107 / 90 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (19 / 40 : ℚ)
  else 0

def foldGlobal_3_384Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_384_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_384Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_384Network foldGlobal_3_384Generator (-1 : ℚ)
    foldGlobal_3_384Multiplier foldGlobal_3_384Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_385Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_385Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_385Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (107 / 90 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (19 / 40 : ℚ)
  else 0

def foldGlobal_3_385Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_385_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_385Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_385Network foldGlobal_3_385Generator (-1 : ℚ)
    foldGlobal_3_385Multiplier foldGlobal_3_385Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_386Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .x), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_386Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0]]

def foldGlobal_3_386Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 40 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (169 / 360 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (107 / 90 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (19 / 40 : ℚ)
  else 0

def foldGlobal_3_386Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_386_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_386Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_386Network foldGlobal_3_386Generator (-1 : ℚ)
    foldGlobal_3_386Multiplier foldGlobal_3_386Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_387Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .xx), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_387Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_387Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (26 / 45 : ℚ)
  else 0

def foldGlobal_3_387Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_387_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_387Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_387Network foldGlobal_3_387Generator (-1 : ℚ)
    foldGlobal_3_387Multiplier foldGlobal_3_387Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_388Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_388Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_388Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (356 / 513 : ℚ)
  else 0

def foldGlobal_3_388Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_388_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_388Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_388Network foldGlobal_3_388Generator (-1 : ℚ)
    foldGlobal_3_388Multiplier foldGlobal_3_388Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_389Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_389Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_389Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (58 / 45 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (38 / 45 : ℚ)
  else 0

def foldGlobal_3_389Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_389_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_389Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_389Network foldGlobal_3_389Generator (-1 : ℚ)
    foldGlobal_3_389Multiplier foldGlobal_3_389Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_390Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_390Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_390Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (58 / 45 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (38 / 45 : ℚ)
  else 0

def foldGlobal_3_390Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_390_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_390Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_390Network foldGlobal_3_390Generator (-1 : ℚ)
    foldGlobal_3_390Multiplier foldGlobal_3_390Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_391Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .y), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_391Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_391Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4 / 117 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (56 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (140 / 117 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (88 / 117 : ℚ)
  else 0

def foldGlobal_3_391Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_391_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_391Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_391Network foldGlobal_3_391Generator (-1 : ℚ)
    foldGlobal_3_391Multiplier foldGlobal_3_391Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_392Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_392Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_392Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4 / 9 : ℚ)
  else 0

def foldGlobal_3_392Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_392_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_392Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_392Network foldGlobal_3_392Generator (-1 : ℚ)
    foldGlobal_3_392Multiplier foldGlobal_3_392Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_393Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .yy), (.yy, .x), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_393Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0]]

def foldGlobal_3_393Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (26 / 45 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (26 / 45 : ℚ)
  else 0

def foldGlobal_3_393Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_393_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_393Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_393Network foldGlobal_3_393Generator (-1 : ℚ)
    foldGlobal_3_393Multiplier foldGlobal_3_393Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_394Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_394Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_394Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (52 / 81 : ℚ)
  else 0

def foldGlobal_3_394Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_394_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_394Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_394Network foldGlobal_3_394Generator (-1 : ℚ)
    foldGlobal_3_394Multiplier foldGlobal_3_394Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_395Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xy, .yy), (.yy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_395Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ), 0]]

def foldGlobal_3_395Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (128 / 513 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (356 / 513 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (356 / 513 : ℚ)
  else 0

def foldGlobal_3_395Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_395_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_395Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_395Network foldGlobal_3_395Generator (-1 : ℚ)
    foldGlobal_3_395Multiplier foldGlobal_3_395Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_396Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_396Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_396Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-200 / 261 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-3784 / 2175 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-32 / 261 : ℚ)
  else 0

def foldGlobal_3_396Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_396_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_396Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_396Network foldGlobal_3_396Generator 1
    foldGlobal_3_396Multiplier foldGlobal_3_396Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_397Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_397Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_397Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 111 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (12 / 37 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 111 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 37 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 111 : ℚ)
  else 0

def foldGlobal_3_397Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_397_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_397Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_397Network foldGlobal_3_397Generator 1
    foldGlobal_3_397Multiplier foldGlobal_3_397Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_398Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_398Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)]]

def foldGlobal_3_398Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (9 / 32 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 32 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (9 / 32 : ℚ)
  else 0

def foldGlobal_3_398Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_398_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_398Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_398Network foldGlobal_3_398Generator (-1 : ℚ)
    foldGlobal_3_398Multiplier foldGlobal_3_398Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_399Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_399Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)]]

def foldGlobal_3_399Multiplier (_a _b : Fin 3) : ℚ :=
  0

def foldGlobal_3_399Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_399_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_399Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_399Network foldGlobal_3_399Generator (-1 : ℚ)
    foldGlobal_3_399Multiplier foldGlobal_3_399Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
