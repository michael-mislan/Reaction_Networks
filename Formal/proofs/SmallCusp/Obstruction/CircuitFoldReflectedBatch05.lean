import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_3_250Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.x, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_250Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)]]

def foldGlobal_3_250Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-25 / 111 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-64 / 333 : ℚ)
  else 0

def foldGlobal_3_250Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_250_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_250Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_250Network foldGlobal_3_250Generator 1
    foldGlobal_3_250Multiplier foldGlobal_3_250Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_251Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_251Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 6 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 3 : ℚ)]]

def foldGlobal_3_251Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-3 / 80 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-77 / 80 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 10 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-71 / 120 : ℚ)
  else 0

def foldGlobal_3_251Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_251_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_251Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_251Network foldGlobal_3_251Generator 1
    foldGlobal_3_251Multiplier foldGlobal_3_251Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_252Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_252Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), 0, (2 / 7 : ℚ), (3 / 7 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_252Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-32 / 49 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-32 / 25 : ℚ)
  else 0

def foldGlobal_3_252Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_252_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_252Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_252Network foldGlobal_3_252Generator 1
    foldGlobal_3_252Multiplier foldGlobal_3_252Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_253Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xy), (.x, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_253Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(2 / 7 : ℚ), 0, (2 / 7 : ℚ), 0, (3 / 7 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_253Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-66184 / 659491 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-41912 / 471065 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (360 / 13459 : ℚ)
  else 0

def foldGlobal_3_253Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_253_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_253Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_253Network foldGlobal_3_253Generator 1
    foldGlobal_3_253Multiplier foldGlobal_3_253Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_254Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_254Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), 0, (2 / 7 : ℚ), (3 / 7 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_254Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-72 / 49 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-56 / 45 : ℚ)
  else 0

def foldGlobal_3_254Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_254_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_254Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_254Network foldGlobal_3_254Generator 1
    foldGlobal_3_254Multiplier foldGlobal_3_254Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_255Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_255Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), 0, (2 / 7 : ℚ), (3 / 7 : ℚ), 0],
  ![0, (2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_255Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1579 / 392 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-128 / 81 : ℚ)
  else 0

def foldGlobal_3_255Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_255_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_255Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_255Network foldGlobal_3_255Generator 1
    foldGlobal_3_255Multiplier foldGlobal_3_255Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_256Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .yy), (.xy, .xx), (.yy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_256Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(2 / 7 : ℚ), (2 / 7 : ℚ), 0, (3 / 7 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0]]

def foldGlobal_3_256Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1975 / 2596 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (30299 / 136290 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-7984 / 31801 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-30494 / 159005 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (24 / 4543 : ℚ)
  else 0

def foldGlobal_3_256Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_256_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_256Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_256Network foldGlobal_3_256Generator 1
    foldGlobal_3_256Multiplier foldGlobal_3_256Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_257Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .yy), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_257Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), (2 / 7 : ℚ), 0, (3 / 7 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_257Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-7984 / 31801 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-30494 / 159005 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (24 / 4543 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1975 / 2596 : ℚ)
  else 0

def foldGlobal_3_257Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_257_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_257Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_257Network foldGlobal_3_257Generator 1
    foldGlobal_3_257Multiplier foldGlobal_3_257Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_258Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_258Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_258Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (1 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 21 : ℚ)
  else 0

def foldGlobal_3_258Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_258_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_258Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_258Network foldGlobal_3_258Generator 1
    foldGlobal_3_258Multiplier foldGlobal_3_258Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_259Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_259Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_259Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (2 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (2 / 81 : ℚ)
  else 0

def foldGlobal_3_259Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_259_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_259Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_259Network foldGlobal_3_259Generator 1
    foldGlobal_3_259Multiplier foldGlobal_3_259Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_260Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xx, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_260Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_260Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (8 / 429 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (272 / 2145 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (464 / 3575 : ℚ)
  else 0

def foldGlobal_3_260Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_260_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_260Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_260Network foldGlobal_3_260Generator (-1 : ℚ)
    foldGlobal_3_260Multiplier foldGlobal_3_260Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_261Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xx, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_261Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (4 / 7 : ℚ), 0, (1 / 7 : ℚ), (2 / 7 : ℚ)]]

def foldGlobal_3_261Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (32 / 569 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (825 / 4552 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (2873 / 3983 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16640 / 27881 : ℚ)
  else 0

def foldGlobal_3_261Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_261_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_261Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_261Network foldGlobal_3_261Generator (-1 : ℚ)
    foldGlobal_3_261Multiplier foldGlobal_3_261Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_262Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xx, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_262Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_262Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (4 / 17 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (236 / 425 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (174 / 85 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (30 / 17 : ℚ)
  else 0

def foldGlobal_3_262Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_262_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_262Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_262Network foldGlobal_3_262Generator (-1 : ℚ)
    foldGlobal_3_262Multiplier foldGlobal_3_262Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_263Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_263Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0]]

def foldGlobal_3_263Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 2 then (1 / 10 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (11 / 50 : ℚ)
  else 0

def foldGlobal_3_263Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 2⟩}

theorem foldGlobal_3_263_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_263Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_263Network foldGlobal_3_263Generator (-1 : ℚ)
    foldGlobal_3_263Multiplier foldGlobal_3_263Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_264Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xx, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_264Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_3_264Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (2 / 111 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (13 / 111 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (9 / 74 : ℚ)
  else 0

def foldGlobal_3_264Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_264_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_264Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_264Network foldGlobal_3_264Generator (-1 : ℚ)
    foldGlobal_3_264Multiplier foldGlobal_3_264Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_265Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xx, .y), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_265Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 6 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_265Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (13 / 184 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 46 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (241 / 276 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (52 / 69 : ℚ)
  else 0

def foldGlobal_3_265Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_265_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_265Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_265Network foldGlobal_3_265Generator (-1 : ℚ)
    foldGlobal_3_265Multiplier foldGlobal_3_265Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_266Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xx, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_266Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_266Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (6 / 25 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (14 / 25 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (154 / 75 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (26 / 15 : ℚ)
  else 0

def foldGlobal_3_266Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_266_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_266Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_266Network foldGlobal_3_266Generator (-1 : ℚ)
    foldGlobal_3_266Multiplier foldGlobal_3_266Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_267Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_267Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0]]

def foldGlobal_3_267Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 2 then (1 / 11 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (5 / 22 : ℚ)
  else 0

def foldGlobal_3_267Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 2⟩}

theorem foldGlobal_3_267_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_267Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_267Network foldGlobal_3_267Generator (-1 : ℚ)
    foldGlobal_3_267Multiplier foldGlobal_3_267Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_268Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_268Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_268Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (13 / 200 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (19 / 100 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (58 / 75 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (143 / 225 : ℚ)
  else 0

def foldGlobal_3_268Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_268_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_268Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_268Network foldGlobal_3_268Generator (-1 : ℚ)
    foldGlobal_3_268Multiplier foldGlobal_3_268Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_269Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_269Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_269Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (27 / 58 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (6 / 29 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 29 : ℚ)
  else 0

def foldGlobal_3_269Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_269_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_269Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_269Network foldGlobal_3_269Generator (-1 : ℚ)
    foldGlobal_3_269Multiplier foldGlobal_3_269Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_270Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_270Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_270Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (2 / 249 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (265 / 1992 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (433 / 2490 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (448 / 6225 : ℚ)
  else 0

def foldGlobal_3_270Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_270_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_270Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_270Network foldGlobal_3_270Generator (-1 : ℚ)
    foldGlobal_3_270Multiplier foldGlobal_3_270Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_271Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_271Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![0, (4 / 7 : ℚ), 0, (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_271Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (4 / 167 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1436 / 4175 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (2196 / 5845 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1140 / 8183 : ℚ)
  else 0

def foldGlobal_3_271Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_271_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_271Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_271Network foldGlobal_3_271Generator (-1 : ℚ)
    foldGlobal_3_271Multiplier foldGlobal_3_271Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_272Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xy, .x), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_272Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)]]

def foldGlobal_3_272Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 2 ∧ b.val = 2 then (3 / 16 : ℚ)
  else 0

def foldGlobal_3_272Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 2, 2, 2⟩}

theorem foldGlobal_3_272_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_272Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_272Network foldGlobal_3_272Generator (-1 : ℚ)
    foldGlobal_3_272Multiplier foldGlobal_3_272Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_273Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xy, .x), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_273Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)]]

def foldGlobal_3_273Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 2 ∧ b.val = 2 then (12 / 25 : ℚ)
  else 0

def foldGlobal_3_273Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 2, 2, 2⟩}

theorem foldGlobal_3_273_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_273Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_273Network foldGlobal_3_273Generator (-1 : ℚ)
    foldGlobal_3_273Multiplier foldGlobal_3_273Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_274Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xy, .y), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_274Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_274Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (1 / 80 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (11 / 80 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (19 / 80 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (9 / 80 : ℚ)
  else 0

def foldGlobal_3_274Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_274_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_274Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_274Network foldGlobal_3_274Generator (-1 : ℚ)
    foldGlobal_3_274Multiplier foldGlobal_3_274Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_275Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xy, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_275Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_275Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (4 / 85 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (156 / 425 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (252 / 425 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (116 / 425 : ℚ)
  else 0

def foldGlobal_3_275Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_275_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_275Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_275Network foldGlobal_3_275Generator (-1 : ℚ)
    foldGlobal_3_275Multiplier foldGlobal_3_275Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_276Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .zero), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_276Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_276Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (3 / 146 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (85 / 584 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (151 / 438 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (40 / 219 : ℚ)
  else 0

def foldGlobal_3_276Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_276_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_276Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_276Network foldGlobal_3_276Generator (-1 : ℚ)
    foldGlobal_3_276Multiplier foldGlobal_3_276Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_277Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_277Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)]]

def foldGlobal_3_277Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-53 / 234 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-79 / 234 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 234 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-121 / 936 : ℚ)
  else 0

def foldGlobal_3_277Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_277_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_277Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_277Network foldGlobal_3_277Generator 1
    foldGlobal_3_277Multiplier foldGlobal_3_277Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_278Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_278Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_278Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-8 / 33 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2 / 99 : ℚ)
  else 0

def foldGlobal_3_278Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_278_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_278Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_278Network foldGlobal_3_278Generator 1
    foldGlobal_3_278Multiplier foldGlobal_3_278Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_279Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_279Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)]]

def foldGlobal_3_279Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-25 / 48 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-25 / 48 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-7 / 48 : ℚ)
  else 0

def foldGlobal_3_279Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_279_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_279Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_279Network foldGlobal_3_279Generator 1
    foldGlobal_3_279Multiplier foldGlobal_3_279Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_280Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_280Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_280Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-13 / 22 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else 0

def foldGlobal_3_280Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_280_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_280Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_280Network foldGlobal_3_280Generator 1
    foldGlobal_3_280Multiplier foldGlobal_3_280Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_281Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_281Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)]]

def foldGlobal_3_281Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-6 / 11 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-6 / 11 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-15 / 88 : ℚ)
  else 0

def foldGlobal_3_281Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_281_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_281Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_281Network foldGlobal_3_281Generator 1
    foldGlobal_3_281Multiplier foldGlobal_3_281Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_282Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_282Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_282Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-13 / 22 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else 0

def foldGlobal_3_282Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_282_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_282Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_282Network foldGlobal_3_282Generator 1
    foldGlobal_3_282Multiplier foldGlobal_3_282Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_283Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xx, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_283Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 7 : ℚ), 0, (1 / 7 : ℚ), (4 / 7 : ℚ)]]

def foldGlobal_3_283Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (16 / 195 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (16 / 105 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (16 / 585 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (8 / 585 : ℚ)
  else 0

def foldGlobal_3_283Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_283_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_283Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_283Network foldGlobal_3_283Generator (-1 : ℚ)
    foldGlobal_3_283Multiplier foldGlobal_3_283Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_284Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xx, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_284Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_284Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (7984 / 4095 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (9911 / 6825 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (12634 / 11375 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (28369 / 11375 : ℚ)
  else 0

def foldGlobal_3_284Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_284_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_284Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_284Network foldGlobal_3_284Generator (-1 : ℚ)
    foldGlobal_3_284Multiplier foldGlobal_3_284Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_285Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_285Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 7 : ℚ), (1 / 7 : ℚ), (4 / 7 : ℚ), 0]]

def foldGlobal_3_285Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (51 / 49 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (53 / 98 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (80 / 343 : ℚ)
  else 0

def foldGlobal_3_285Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_285_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_285Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_285Network foldGlobal_3_285Generator (-1 : ℚ)
    foldGlobal_3_285Multiplier foldGlobal_3_285Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_286Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_286Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 7 : ℚ), (1 / 7 : ℚ), (4 / 7 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_286Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (4 / 35 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 15 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (13 / 140 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 75 : ℚ)
  else 0

def foldGlobal_3_286Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_286_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_286Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_286Network foldGlobal_3_286Generator (-1 : ℚ)
    foldGlobal_3_286Multiplier foldGlobal_3_286Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_287Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xx, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_287Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 5 : ℚ), 0, (1 / 5 : ℚ), (3 / 5 : ℚ)]]

def foldGlobal_3_287Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (8 / 93 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (64 / 465 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (8 / 279 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 279 : ℚ)
  else 0

def foldGlobal_3_287Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_287_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_287Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_287Network foldGlobal_3_287Generator (-1 : ℚ)
    foldGlobal_3_287Multiplier foldGlobal_3_287Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_288Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xx, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_288Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (2 / 7 : ℚ), 0, (2 / 7 : ℚ), (3 / 7 : ℚ)]]

def foldGlobal_3_288Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (20 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (4 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-16 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 7 : ℚ)
  else 0

def foldGlobal_3_288Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_288_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_288Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_288Network foldGlobal_3_288Generator (-1 : ℚ)
    foldGlobal_3_288Multiplier foldGlobal_3_288Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_289Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_289Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0]]

def foldGlobal_3_289Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (26 / 25 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (27 / 50 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (53 / 125 : ℚ)
  else 0

def foldGlobal_3_289Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_289_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_289Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_289Network foldGlobal_3_289Generator (-1 : ℚ)
    foldGlobal_3_289Multiplier foldGlobal_3_289Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_290Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_290Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_290Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (8 / 95 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (16 / 285 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (116 / 1425 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16 / 1425 : ℚ)
  else 0

def foldGlobal_3_290Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_290_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_290Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_290Network foldGlobal_3_290Generator (-1 : ℚ)
    foldGlobal_3_290Multiplier foldGlobal_3_290Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_291Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_291Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0]]

def foldGlobal_3_291Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (21 / 20 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (3 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (11 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 4 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 20 : ℚ)
  else 0

def foldGlobal_3_291Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_291_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_291Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_291Network foldGlobal_3_291Generator (-1 : ℚ)
    foldGlobal_3_291Multiplier foldGlobal_3_291Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_292Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_292Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_292Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (125 / 266 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (24 / 133 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (30 / 133 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 133 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (20 / 133 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 133 : ℚ)
  else 0

def foldGlobal_3_292Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_292_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_292Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_292Network foldGlobal_3_292Generator (-1 : ℚ)
    foldGlobal_3_292Multiplier foldGlobal_3_292Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_293Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_293Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (4 / 9 : ℚ), 0, (2 / 9 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_293Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4624 / 2709 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (760 / 903 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (5424 / 7525 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (64 / 45 : ℚ)
  else 0

def foldGlobal_3_293Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_293_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_293Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_293Network foldGlobal_3_293Generator (-1 : ℚ)
    foldGlobal_3_293Multiplier foldGlobal_3_293Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_294Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xy, .x), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_294Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_294Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (11536 / 6651 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1600 / 2217 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (12736 / 18475 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (15736 / 18475 : ℚ)
  else 0

def foldGlobal_3_294Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_294_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_294Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_294Network foldGlobal_3_294Generator (-1 : ℚ)
    foldGlobal_3_294Multiplier foldGlobal_3_294Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_295Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .zero), (.xy, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_295Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_295Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (728 / 423 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (110 / 141 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (828 / 1175 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 3 : ℚ)
  else 0

def foldGlobal_3_295Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_295_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_295Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_295Network foldGlobal_3_295Generator (-1 : ℚ)
    foldGlobal_3_295Multiplier foldGlobal_3_295Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_296Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_296Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0]]

def foldGlobal_3_296Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-21 / 40 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-41 / 40 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-21 / 40 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 8 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 40 : ℚ)
  else 0

def foldGlobal_3_296Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_296_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_296Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_296Network foldGlobal_3_296Generator 1
    foldGlobal_3_296Multiplier foldGlobal_3_296Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_297Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_297Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0]]

def foldGlobal_3_297Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-55 / 78 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-20 / 13 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-128 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 3 : ℚ)
  else 0

def foldGlobal_3_297Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_297_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_297Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_297Network foldGlobal_3_297Generator 1
    foldGlobal_3_297Multiplier foldGlobal_3_297Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_298Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_298Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0]]

def foldGlobal_3_298Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-5 / 8 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-9 / 8 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-5 / 8 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else 0

def foldGlobal_3_298Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_298_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_298Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_298Network foldGlobal_3_298Generator 1
    foldGlobal_3_298Multiplier foldGlobal_3_298Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_299Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_299Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 2 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_3_299Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4358 / 1593 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (550 / 531 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (904 / 531 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (16442 / 4425 : ℚ)
  else 0

def foldGlobal_3_299Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_299_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_299Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_299Network foldGlobal_3_299Generator (-1 : ℚ)
    foldGlobal_3_299Multiplier foldGlobal_3_299Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
