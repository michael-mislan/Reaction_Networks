import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_3_300Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_300Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_300Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (626 / 231 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (50 / 77 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (127 / 77 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (7242 / 1925 : ℚ)
  else 0

def foldGlobal_3_300Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_300_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_300Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_300Network foldGlobal_3_300Generator (-1 : ℚ)
    foldGlobal_3_300Multiplier foldGlobal_3_300Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_301Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_301Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0]]

def foldGlobal_3_301Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 49 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (122 / 147 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (744 / 245 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1216 / 441 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (200 / 147 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4504 / 1225 : ℚ)
  else 0

def foldGlobal_3_301Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_301_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_301Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_301Network foldGlobal_3_301Generator (-1 : ℚ)
    foldGlobal_3_301Multiplier foldGlobal_3_301Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_302Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_302Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_302Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1057 / 387 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (125 / 129 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (725 / 774 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4003 / 1075 : ℚ)
  else 0

def foldGlobal_3_302Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_302_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_302Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_302Network foldGlobal_3_302Generator (-1 : ℚ)
    foldGlobal_3_302Multiplier foldGlobal_3_302Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_303Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_303Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_303Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (272 / 75 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (848 / 375 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (624 / 125 : ℚ)
  else 0

def foldGlobal_3_303Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_303_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_303Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_303Network foldGlobal_3_303Generator (-1 : ℚ)
    foldGlobal_3_303Multiplier foldGlobal_3_303Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_304Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_304Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_304Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (4 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (96 / 25 : ℚ)
  else 0

def foldGlobal_3_304Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_304_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_304Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_304Network foldGlobal_3_304Generator (-1 : ℚ)
    foldGlobal_3_304Multiplier foldGlobal_3_304Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_305Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_305Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0]]

def foldGlobal_3_305Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (16 / 125 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (548 / 375 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (4504 / 625 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (272 / 75 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (624 / 125 : ℚ)
  else 0

def foldGlobal_3_305Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_305_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_305Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_305Network foldGlobal_3_305Generator (-1 : ℚ)
    foldGlobal_3_305Multiplier foldGlobal_3_305Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_306Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_306Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_306Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (7334 / 8631 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (12512 / 4795 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (2249 / 4795 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (8728 / 4795 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (11982 / 23975 : ℚ)
  else 0

def foldGlobal_3_306Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_306_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_306Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_306Network foldGlobal_3_306Generator (-1 : ℚ)
    foldGlobal_3_306Multiplier foldGlobal_3_306Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_307Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_307Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_307Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (8 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (8 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (32 / 49 : ℚ)
  else 0

def foldGlobal_3_307Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_307_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_307Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_307Network foldGlobal_3_307Generator (-1 : ℚ)
    foldGlobal_3_307Multiplier foldGlobal_3_307Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_308Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_308Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0]]

def foldGlobal_3_308Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (5560 / 6579 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (3212 / 6579 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (2200 / 731 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1316 / 731 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (70936 / 18275 : ℚ)
  else 0

def foldGlobal_3_308Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_308_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_308Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_308Network foldGlobal_3_308Generator (-1 : ℚ)
    foldGlobal_3_308Multiplier foldGlobal_3_308Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_309Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_309Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 2 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_3_309Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (601 / 102 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (110 / 153 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1301 / 459 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (479 / 306 : ℚ)
  else 0

def foldGlobal_3_309Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_309_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_309Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_309Network foldGlobal_3_309Generator (-1 : ℚ)
    foldGlobal_3_309Multiplier foldGlobal_3_309Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_310Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_310Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_310Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (255 / 43 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (20 / 43 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (358 / 129 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (68 / 43 : ℚ)
  else 0

def foldGlobal_3_310Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_310_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_310Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_310Network foldGlobal_3_310Generator (-1 : ℚ)
    foldGlobal_3_310Multiplier foldGlobal_3_310Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_311Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_311Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, 0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_311Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (71 / 12 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (35 / 12 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (5 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 12 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (3 / 4 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (151 / 54 : ℚ)
  else 0

def foldGlobal_3_311Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_311_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_311Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_311Network foldGlobal_3_311Generator (-1 : ℚ)
    foldGlobal_3_311Multiplier foldGlobal_3_311Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_312Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_312Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_312Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (112 / 19 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (40 / 57 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (484 / 171 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (136 / 171 : ℚ)
  else 0

def foldGlobal_3_312Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_312_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_312Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_312Network foldGlobal_3_312Generator (-1 : ℚ)
    foldGlobal_3_312Multiplier foldGlobal_3_312Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_313Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_313Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_313Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (304 / 41 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (148 / 41 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1546 / 615 : ℚ)
  else 0

def foldGlobal_3_313Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_313_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_313Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_313Network foldGlobal_3_313Generator (-1 : ℚ)
    foldGlobal_3_313Multiplier foldGlobal_3_313Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_314Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_314Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_314Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1578 / 211 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2312 / 633 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (11140 / 4431 : ℚ)
  else 0

def foldGlobal_3_314Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_314_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_314Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_314Network foldGlobal_3_314Generator (-1 : ℚ)
    foldGlobal_3_314Multiplier foldGlobal_3_314Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_315Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_315Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_315Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (690 / 89 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (932 / 89 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (52 / 267 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (136 / 89 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1024 / 267 : ℚ)
  else 0

def foldGlobal_3_315Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_315_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_315Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_315Network foldGlobal_3_315Generator (-1 : ℚ)
    foldGlobal_3_315Multiplier foldGlobal_3_315Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_316Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_316Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_316Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (35 / 54 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (40 / 27 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (22 / 15 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (28 / 27 : ℚ)
  else 0

def foldGlobal_3_316Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_316_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_316Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_316Network foldGlobal_3_316Generator (-1 : ℚ)
    foldGlobal_3_316Multiplier foldGlobal_3_316Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_317Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .y), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_317Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_317Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (25 / 42 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (10 / 7 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (7 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (62 / 63 : ℚ)
  else 0

def foldGlobal_3_317Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_317_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_317Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_317Network foldGlobal_3_317Generator (-1 : ℚ)
    foldGlobal_3_317Multiplier foldGlobal_3_317Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_318Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_318Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_318Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (7 / 10 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (23 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then 2
  else if a.val = 1 ∧ b.val = 1 then (49 / 45 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 3 : ℚ)
  else 0

def foldGlobal_3_318Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_318_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_318Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_318Network foldGlobal_3_318Generator (-1 : ℚ)
    foldGlobal_3_318Multiplier foldGlobal_3_318Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_319Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .y), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_319Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_319Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4 / 7 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (59 / 42 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 14 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (121 / 126 : ℚ)
  else 0

def foldGlobal_3_319Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_319_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_319Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_319Network foldGlobal_3_319Generator (-1 : ℚ)
    foldGlobal_3_319Multiplier foldGlobal_3_319Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_320Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .y), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_320Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 3 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_3_320Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (19 / 12 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (7 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (41 / 36 : ℚ)
  else 0

def foldGlobal_3_320Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_320_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_320Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_320Network foldGlobal_3_320Generator (-1 : ℚ)
    foldGlobal_3_320Multiplier foldGlobal_3_320Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_321Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .y), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_321Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_321Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (19 / 12 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (29 / 14 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (41 / 36 : ℚ)
  else 0

def foldGlobal_3_321Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_321_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_321Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_321Network foldGlobal_3_321Generator (-1 : ℚ)
    foldGlobal_3_321Multiplier foldGlobal_3_321Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_322Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_322Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_322Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (19 / 12 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (27 / 10 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (41 / 36 : ℚ)
  else 0

def foldGlobal_3_322Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_322_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_322Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_322Network foldGlobal_3_322Generator (-1 : ℚ)
    foldGlobal_3_322Multiplier foldGlobal_3_322Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_323Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_323Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_323Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (9 / 13 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (41 / 78 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 39 : ℚ)
  else 0

def foldGlobal_3_323Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_323_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_323Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_323Network foldGlobal_3_323Generator (-1 : ℚ)
    foldGlobal_3_323Multiplier foldGlobal_3_323Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_324Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .y), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_324Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_324Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 53 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-22 / 159 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-2 / 53 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (112 / 159 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (57 / 106 : ℚ)
  else 0

def foldGlobal_3_324Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_324_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_324Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_324Network foldGlobal_3_324Generator (-1 : ℚ)
    foldGlobal_3_324Multiplier foldGlobal_3_324Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_325Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .y), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_325Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_325Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (28 / 117 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (80 / 117 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (2 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (121 / 234 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 117 : ℚ)
  else 0

def foldGlobal_3_325Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_325_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_325Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_325Network foldGlobal_3_325Generator (-1 : ℚ)
    foldGlobal_3_325Multiplier foldGlobal_3_325Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_326Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .y), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_326Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_326Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-128 / 1149 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-496 / 3447 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-128 / 1149 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (298 / 383 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1405 / 2298 : ℚ)
  else 0

def foldGlobal_3_326Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_326_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_326Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_326Network foldGlobal_3_326Generator (-1 : ℚ)
    foldGlobal_3_326Multiplier foldGlobal_3_326Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_327Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_327Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_327Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (9 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (17 / 10 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 4 : ℚ)
  else 0

def foldGlobal_3_327Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_327_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_327Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_327Network foldGlobal_3_327Generator (-1 : ℚ)
    foldGlobal_3_327Multiplier foldGlobal_3_327Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_328Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_328Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_328Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (7 / 10 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (11 / 5 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (3 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (11 / 5 : ℚ)
  else 0

def foldGlobal_3_328Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_328_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_328Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_328Network foldGlobal_3_328Generator (-1 : ℚ)
    foldGlobal_3_328Multiplier foldGlobal_3_328Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_329Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_329Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_329Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (9 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (11 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (7 / 6 : ℚ)
  else 0

def foldGlobal_3_329Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_329_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_329Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_329Network foldGlobal_3_329Generator (-1 : ℚ)
    foldGlobal_3_329Multiplier foldGlobal_3_329Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_330Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .y), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_330Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)]]

def foldGlobal_3_330Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 5 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (21 / 10 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (21 / 10 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 10 : ℚ)
  else 0

def foldGlobal_3_330Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_330_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_330Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_330Network foldGlobal_3_330Generator (-1 : ℚ)
    foldGlobal_3_330Multiplier foldGlobal_3_330Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_331Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_331Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 3 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_3_331Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (5 / 8 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (17 / 8 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (13 / 12 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (17 / 8 : ℚ)
  else 0

def foldGlobal_3_331Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_331_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_331Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_331Network foldGlobal_3_331Generator (-1 : ℚ)
    foldGlobal_3_331Multiplier foldGlobal_3_331Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_332Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_332Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_332Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (9 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (11 / 7 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 4 : ℚ)
  else 0

def foldGlobal_3_332Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_332_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_332Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_332Network foldGlobal_3_332Generator (-1 : ℚ)
    foldGlobal_3_332Multiplier foldGlobal_3_332Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_333Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_333Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_333Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (9 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (11 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 4 : ℚ)
  else 0

def foldGlobal_3_333Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_333_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_333Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_333Network foldGlobal_3_333Generator (-1 : ℚ)
    foldGlobal_3_333Multiplier foldGlobal_3_333Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_334Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_334Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![0, (1 / 6 : ℚ), (1 / 2 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_334Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (15 / 7 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (15 / 7 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 2 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 7 : ℚ)
  else 0

def foldGlobal_3_334Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_334_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_334Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_334Network foldGlobal_3_334Generator (-1 : ℚ)
    foldGlobal_3_334Multiplier foldGlobal_3_334Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_335Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_335Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0]]

def foldGlobal_3_335Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (13 / 6 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (13 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 2 : ℚ)
  else 0

def foldGlobal_3_335Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_335_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_335Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_335Network foldGlobal_3_335Generator (-1 : ℚ)
    foldGlobal_3_335Multiplier foldGlobal_3_335Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_336Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_336Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ)]]

def foldGlobal_3_336Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (21 / 10 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (21 / 10 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (3 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 2 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 10 : ℚ)
  else 0

def foldGlobal_3_336Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_336_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_336Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_336Network foldGlobal_3_336Generator (-1 : ℚ)
    foldGlobal_3_336Multiplier foldGlobal_3_336Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_337Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .y), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_337Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0]]

def foldGlobal_3_337Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (46 / 19 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-8 / 19 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (46 / 19 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-64 / 57 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-8 / 19 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 2 : ℚ)
  else 0

def foldGlobal_3_337Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_337_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_337Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_337Network foldGlobal_3_337Generator (-1 : ℚ)
    foldGlobal_3_337Multiplier foldGlobal_3_337Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_338Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_338Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_338Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1402 / 141 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (362 / 423 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1546 / 1269 : ℚ)
  else 0

def foldGlobal_3_338Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_338_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_338Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_338Network foldGlobal_3_338Generator (-1 : ℚ)
    foldGlobal_3_338Multiplier foldGlobal_3_338Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_339Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_339Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_339Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (5690 / 577 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1954 / 1731 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (7130 / 5193 : ℚ)
  else 0

def foldGlobal_3_339Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_339_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_339Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_339Network foldGlobal_3_339Generator (-1 : ℚ)
    foldGlobal_3_339Multiplier foldGlobal_3_339Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_340Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .y), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_340Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_340Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (184 / 19 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (286 / 57 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (98 / 57 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (6 / 19 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (130 / 171 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (292 / 171 : ℚ)
  else 0

def foldGlobal_3_340Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_340_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_340Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_340Network foldGlobal_3_340Generator (-1 : ℚ)
    foldGlobal_3_340Multiplier foldGlobal_3_340Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_341Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_341Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_3_341Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (171 / 118 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (178 / 177 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (250 / 177 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (145 / 531 : ℚ)
  else 0

def foldGlobal_3_341Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_341_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_341Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_341Network foldGlobal_3_341Generator (-1 : ℚ)
    foldGlobal_3_341Multiplier foldGlobal_3_341Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_342Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_342Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_342Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (109 / 74 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (94 / 111 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (458 / 333 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (40 / 111 : ℚ)
  else 0

def foldGlobal_3_342Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_342_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_342Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_342Network foldGlobal_3_342Generator (-1 : ℚ)
    foldGlobal_3_342Multiplier foldGlobal_3_342Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_343Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_343Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_343Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (169 / 118 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (66 / 59 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (764 / 531 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 59 : ℚ)
  else 0

def foldGlobal_3_343Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_343_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_343Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_343Network foldGlobal_3_343Generator (-1 : ℚ)
    foldGlobal_3_343Multiplier foldGlobal_3_343Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_344Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_344Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_344Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (296 / 149 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (63 / 149 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2114 / 1341 : ℚ)
  else 0

def foldGlobal_3_344Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_344_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_344Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_344Network foldGlobal_3_344Generator (-1 : ℚ)
    foldGlobal_3_344Multiplier foldGlobal_3_344Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_345Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xx), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_345Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_345Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (418 / 217 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (179 / 217 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (466 / 279 : ℚ)
  else 0

def foldGlobal_3_345Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_345_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_345Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_345Network foldGlobal_3_345Generator (-1 : ℚ)
    foldGlobal_3_345Multiplier foldGlobal_3_345Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_346Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_346Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_346Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (23 / 40 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (43 / 40 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (5 / 8 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (23 / 40 : ℚ)
  else 0

def foldGlobal_3_346Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_346_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_346Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_346Network foldGlobal_3_346Generator (-1 : ℚ)
    foldGlobal_3_346Multiplier foldGlobal_3_346Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_347Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_347Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_347Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4 / 7 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (15 / 14 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (2 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 7 : ℚ)
  else 0

def foldGlobal_3_347Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_347_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_347Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_347Network foldGlobal_3_347Generator (-1 : ℚ)
    foldGlobal_3_347Multiplier foldGlobal_3_347Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_348Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_348Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)]]

def foldGlobal_3_348Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 5 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (11 / 10 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (3 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 10 : ℚ)
  else 0

def foldGlobal_3_348Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_348_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_348Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_348Network foldGlobal_3_348Generator (-1 : ℚ)
    foldGlobal_3_348Multiplier foldGlobal_3_348Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_349Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .xy), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_349Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_349Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (7 / 10 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (6 / 5 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (3 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (7 / 10 : ℚ)
  else 0

def foldGlobal_3_349Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_349_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_349Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_349Network foldGlobal_3_349Generator (-1 : ℚ)
    foldGlobal_3_349Multiplier foldGlobal_3_349Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
