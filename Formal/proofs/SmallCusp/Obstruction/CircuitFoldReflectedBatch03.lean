import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_3_150Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_150Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_150Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 53 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (8 / 53 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-8 / 53 : ℚ)
  else 0

def foldGlobal_3_150Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_150_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_150Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_150Network foldGlobal_3_150Generator 1
    foldGlobal_3_150Multiplier foldGlobal_3_150Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_151Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_151Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_151Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (1 / 11 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 11 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 11 : ℚ)
  else 0

def foldGlobal_3_151Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 2, 2⟩}

theorem foldGlobal_3_151_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_151Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_151Network foldGlobal_3_151Generator 1
    foldGlobal_3_151Multiplier foldGlobal_3_151Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_152Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_152Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_152Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-3 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 2 : ℚ)
  else 0

def foldGlobal_3_152Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_152_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_152Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_152Network foldGlobal_3_152Generator 1
    foldGlobal_3_152Multiplier foldGlobal_3_152Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_153Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_153Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_153Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (2 / 51 : ℚ)
  else 0

def foldGlobal_3_153Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_153_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_153Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_153Network foldGlobal_3_153Generator (-1 : ℚ)
    foldGlobal_3_153Multiplier foldGlobal_3_153Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_154Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_154Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_154Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-5 / 36 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 36 : ℚ)
  else 0

def foldGlobal_3_154Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 2⟩}

theorem foldGlobal_3_154_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_154Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_154Network foldGlobal_3_154Generator (-1 : ℚ)
    foldGlobal_3_154Multiplier foldGlobal_3_154Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_155Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_155Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_155Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (8 / 207 : ℚ)
  else 0

def foldGlobal_3_155Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_155_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_155Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_155Network foldGlobal_3_155Generator (-1 : ℚ)
    foldGlobal_3_155Multiplier foldGlobal_3_155Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_156Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_156Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_156Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 80 : ℚ)
  else 0

def foldGlobal_3_156Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_156_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_156Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_156Network foldGlobal_3_156Generator (-1 : ℚ)
    foldGlobal_3_156Multiplier foldGlobal_3_156Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_157Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_157Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_157Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 171 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-10 / 171 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 76 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (8 / 57 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2 / 19 : ℚ)
  else 0

def foldGlobal_3_157Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_157_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_157Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_157Network foldGlobal_3_157Generator (-1 : ℚ)
    foldGlobal_3_157Multiplier foldGlobal_3_157Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_158Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_158Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_158Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 80 : ℚ)
  else 0

def foldGlobal_3_158Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_158_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_158Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_158Network foldGlobal_3_158Generator (-1 : ℚ)
    foldGlobal_3_158Multiplier foldGlobal_3_158Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_159Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_159Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 6 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_159Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 11 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 11 : ℚ)
  else 0

def foldGlobal_3_159Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_159_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_159Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_159Network foldGlobal_3_159Generator (-1 : ℚ)
    foldGlobal_3_159Multiplier foldGlobal_3_159Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_160Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_160Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 6 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_160Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 72 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-5 / 72 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 72 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 8 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 8 : ℚ)
  else 0

def foldGlobal_3_160Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_160_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_160Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_160Network foldGlobal_3_160Generator (-1 : ℚ)
    foldGlobal_3_160Multiplier foldGlobal_3_160Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_161Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_161Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 6 : ℚ), (1 / 2 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_161Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 5 : ℚ)
  else 0

def foldGlobal_3_161Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_161_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_161Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_161Network foldGlobal_3_161Generator (-1 : ℚ)
    foldGlobal_3_161Multiplier foldGlobal_3_161Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_162Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_162Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_162Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 11 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 11 : ℚ)
  else 0

def foldGlobal_3_162Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_162_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_162Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_162Network foldGlobal_3_162Generator (-1 : ℚ)
    foldGlobal_3_162Multiplier foldGlobal_3_162Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_163Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_163Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_163Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 36 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-5 / 36 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (2 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 36 : ℚ)
  else 0

def foldGlobal_3_163Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_163_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_163Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_163Network foldGlobal_3_163Generator (-1 : ℚ)
    foldGlobal_3_163Multiplier foldGlobal_3_163Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_164Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_164Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_164Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 5 : ℚ)
  else 0

def foldGlobal_3_164Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_164_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_164Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_164Network foldGlobal_3_164Generator (-1 : ℚ)
    foldGlobal_3_164Multiplier foldGlobal_3_164Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_165Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .x), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_165Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (3 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_165Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (6 / 125 : ℚ)
  else 0

def foldGlobal_3_165Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_165_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_165Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_165Network foldGlobal_3_165Generator (-1 : ℚ)
    foldGlobal_3_165Multiplier foldGlobal_3_165Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_166Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .x), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_166Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0]]

def foldGlobal_3_166Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 2 ∧ b.val = 2 then (8 / 63 : ℚ)
  else 0

def foldGlobal_3_166Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 2, 2, 2⟩}

theorem foldGlobal_3_166_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_166Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_166Network foldGlobal_3_166Generator (-1 : ℚ)
    foldGlobal_3_166Multiplier foldGlobal_3_166Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_167Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .x), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_167Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (4 / 7 : ℚ), (2 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_3_167Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (4 / 39 : ℚ)
  else 0

def foldGlobal_3_167Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_167_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_167Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_167Network foldGlobal_3_167Generator (-1 : ℚ)
    foldGlobal_3_167Multiplier foldGlobal_3_167Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_168Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_168Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (3 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_168Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (6 / 125 : ℚ)
  else 0

def foldGlobal_3_168Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_168_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_168Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_168Network foldGlobal_3_168Generator (-1 : ℚ)
    foldGlobal_3_168Multiplier foldGlobal_3_168Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_169Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_169Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_169Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (8 / 63 : ℚ)
  else 0

def foldGlobal_3_169Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_169_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_169Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_169Network foldGlobal_3_169Generator (-1 : ℚ)
    foldGlobal_3_169Multiplier foldGlobal_3_169Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_170Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .xx), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_170Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (4 / 7 : ℚ), (2 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_3_170Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4 / 39 : ℚ)
  else 0

def foldGlobal_3_170Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_170_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_170Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_170Network foldGlobal_3_170Generator (-1 : ℚ)
    foldGlobal_3_170Multiplier foldGlobal_3_170Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_171Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .y), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_171Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0]]

def foldGlobal_3_171Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 13 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-2 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-10 / 117 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 39 : ℚ)
  else 0

def foldGlobal_3_171Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_171_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_171Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_171Network foldGlobal_3_171Generator (-1 : ℚ)
    foldGlobal_3_171Multiplier foldGlobal_3_171Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_172Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.yy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_172Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (3 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_172Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 45 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-104 / 1125 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 375 : ℚ)
  else 0

def foldGlobal_3_172Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_172_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_172Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_172Network foldGlobal_3_172Generator (-1 : ℚ)
    foldGlobal_3_172Multiplier foldGlobal_3_172Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_173Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.yy, .x), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_173Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, (4 / 7 : ℚ), (2 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_3_173Multiplier (_a _b : Fin 3) : ℚ :=
  0

def foldGlobal_3_173Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_173_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_173Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_173Network foldGlobal_3_173Generator (-1 : ℚ)
    foldGlobal_3_173Multiplier foldGlobal_3_173Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_174Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.yy, .zero), (.yy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_174Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0]]

def foldGlobal_3_174Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 103 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-28 / 309 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-10 / 103 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 103 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-40 / 309 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2 / 103 : ℚ)
  else 0

def foldGlobal_3_174Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_174_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_174Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_174Network foldGlobal_3_174Generator (-1 : ℚ)
    foldGlobal_3_174Multiplier foldGlobal_3_174Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_175Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.yy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_175Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (4 / 7 : ℚ), (2 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_3_175Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-392 / 2673 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-44 / 243 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (64 / 2673 : ℚ)
  else 0

def foldGlobal_3_175Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_175_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_175Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_175Network foldGlobal_3_175Generator (-1 : ℚ)
    foldGlobal_3_175Multiplier foldGlobal_3_175Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_176Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.yy, .xx), (.yy, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_176Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_176Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4 / 117 : ℚ)
  else 0

def foldGlobal_3_176Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_176_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_176Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_176Network foldGlobal_3_176Generator (-1 : ℚ)
    foldGlobal_3_176Multiplier foldGlobal_3_176Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_177Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .x), (.xy, .y), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_177Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_177Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 64 : ℚ)
  else 0

def foldGlobal_3_177Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_177_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_177Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_177Network foldGlobal_3_177Generator (-1 : ℚ)
    foldGlobal_3_177Multiplier foldGlobal_3_177Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_178Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .x), (.xy, .y), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_178Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)]]

def foldGlobal_3_178Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 4 : ℚ)
  else 0

def foldGlobal_3_178Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_178_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_178Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_178Network foldGlobal_3_178Generator (-1 : ℚ)
    foldGlobal_3_178Multiplier foldGlobal_3_178Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_179Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .x), (.xy, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_179Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_179Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 125 : ℚ)
  else 0

def foldGlobal_3_179Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_179_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_179Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_179Network foldGlobal_3_179Generator (-1 : ℚ)
    foldGlobal_3_179Multiplier foldGlobal_3_179Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_180Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .x), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_180Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_180Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 2 ∧ b.val = 2 then (1 / 18 : ℚ)
  else 0

def foldGlobal_3_180Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_180_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_180Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_180Network foldGlobal_3_180Generator (-1 : ℚ)
    foldGlobal_3_180Multiplier foldGlobal_3_180Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_181Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .y), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_181Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_181Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 96 : ℚ)
  else 0

def foldGlobal_3_181Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_181_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_181Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_181Network foldGlobal_3_181Generator (-1 : ℚ)
    foldGlobal_3_181Multiplier foldGlobal_3_181Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_182Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_182Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_182Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 4 : ℚ)
  else 0

def foldGlobal_3_182Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_182_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_182Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_182Network foldGlobal_3_182Generator (-1 : ℚ)
    foldGlobal_3_182Multiplier foldGlobal_3_182Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_183Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .y), (.xy, .xx), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_183Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_183Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (16 / 375 : ℚ)
  else 0

def foldGlobal_3_183Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_183_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_183Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_183Network foldGlobal_3_183Generator (-1 : ℚ)
    foldGlobal_3_183Multiplier foldGlobal_3_183Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_184Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_184Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_184Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-24 / 325 : ℚ)
  else 0

def foldGlobal_3_184Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_184_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_184Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_184Network foldGlobal_3_184Generator 1
    foldGlobal_3_184Multiplier foldGlobal_3_184Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_185Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .xx), (.y, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_185Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_185Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-27 / 125 : ℚ)
  else 0

def foldGlobal_3_185Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_185_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_185Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_185Network foldGlobal_3_185Generator 1
    foldGlobal_3_185Multiplier foldGlobal_3_185Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_186Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_186Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_186Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-10 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-50 / 63 : ℚ)
  else 0

def foldGlobal_3_186Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_186_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_186Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_186Network foldGlobal_3_186Generator 1
    foldGlobal_3_186Multiplier foldGlobal_3_186Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_187Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .y), (.y, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_187Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_187Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-10 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-50 / 63 : ℚ)
  else 0

def foldGlobal_3_187Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_187_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_187Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_187Network foldGlobal_3_187Generator 1
    foldGlobal_3_187Multiplier foldGlobal_3_187Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_188Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_188Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_188Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-5 / 14 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-25 / 56 : ℚ)
  else 0

def foldGlobal_3_188Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_188_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_188Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_188Network foldGlobal_3_188Generator 1
    foldGlobal_3_188Multiplier foldGlobal_3_188Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_189Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_189Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_189Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-5 / 14 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-25 / 56 : ℚ)
  else 0

def foldGlobal_3_189Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_189_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_189Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_189Network foldGlobal_3_189Generator 1
    foldGlobal_3_189Multiplier foldGlobal_3_189Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_190Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_190Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_190Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-10 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-50 / 63 : ℚ)
  else 0

def foldGlobal_3_190Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_190_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_190Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_190Network foldGlobal_3_190Generator 1
    foldGlobal_3_190Multiplier foldGlobal_3_190Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_191Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.y, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_191Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_191Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-10 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-50 / 63 : ℚ)
  else 0

def foldGlobal_3_191Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_191_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_191Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_191Network foldGlobal_3_191Generator 1
    foldGlobal_3_191Multiplier foldGlobal_3_191Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_192Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .y), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_192Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_192Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-24 / 325 : ℚ)
  else 0

def foldGlobal_3_192Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_192_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_192Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_192Network foldGlobal_3_192Generator 1
    foldGlobal_3_192Multiplier foldGlobal_3_192Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_193Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .xy), (.xx, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_193Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0]]

def foldGlobal_3_193Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-25 / 56 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-15 / 28 : ℚ)
  else 0

def foldGlobal_3_193Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_193_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_193Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_193Network foldGlobal_3_193Generator 1
    foldGlobal_3_193Multiplier foldGlobal_3_193Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_194Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .yy), (.xx, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_194Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_194Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-15 / 28 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-25 / 56 : ℚ)
  else 0

def foldGlobal_3_194Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_194_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_194Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_194Network foldGlobal_3_194Generator 1
    foldGlobal_3_194Multiplier foldGlobal_3_194Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_195Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_195Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_195Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-24 / 175 : ℚ)
  else 0

def foldGlobal_3_195Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_195_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_195Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_195Network foldGlobal_3_195Generator 1
    foldGlobal_3_195Multiplier foldGlobal_3_195Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_196Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .xy), (.xx, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_196Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_196Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-24 / 325 : ℚ)
  else 0

def foldGlobal_3_196Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_196_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_196Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_196Network foldGlobal_3_196Generator 1
    foldGlobal_3_196Multiplier foldGlobal_3_196Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_197Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xy), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_197Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0]]

def foldGlobal_3_197Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-5 / 12 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-5 / 12 : ℚ)
  else 0

def foldGlobal_3_197Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_197_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_197Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_197Network foldGlobal_3_197Generator 1
    foldGlobal_3_197Multiplier foldGlobal_3_197Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_198Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .yy), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_198Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_198Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-8 / 27 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-16 / 81 : ℚ)
  else 0

def foldGlobal_3_198Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_198_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_198Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_198Network foldGlobal_3_198Generator 1
    foldGlobal_3_198Multiplier foldGlobal_3_198Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_199Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.y, .xy), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_199Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_199Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-25 / 56 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-15 / 28 : ℚ)
  else 0

def foldGlobal_3_199Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_199_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_199Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_199Network foldGlobal_3_199Generator 1
    foldGlobal_3_199Multiplier foldGlobal_3_199Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
