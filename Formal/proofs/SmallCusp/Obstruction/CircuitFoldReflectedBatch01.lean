import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_3_50Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .xy), (.xx, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_50Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)]]

def foldGlobal_3_50Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-5 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 18 : ℚ)
  else 0

def foldGlobal_3_50Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_50_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_50Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_50Network foldGlobal_3_50Generator 1
    foldGlobal_3_50Multiplier foldGlobal_3_50Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_51Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .yy), (.xx, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_51Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_51Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-5 / 18 : ℚ)
  else 0

def foldGlobal_3_51Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_51_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_51Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_51Network foldGlobal_3_51Generator 1
    foldGlobal_3_51Multiplier foldGlobal_3_51Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_52Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_52Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_52Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 8 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 8 : ℚ)
  else 0

def foldGlobal_3_52Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_52_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_52Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_52Network foldGlobal_3_52Generator 1
    foldGlobal_3_52Multiplier foldGlobal_3_52Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_53Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_53Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_53Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 38 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 38 : ℚ)
  else 0

def foldGlobal_3_53Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_53_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_53Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_53Network foldGlobal_3_53Generator 1
    foldGlobal_3_53Multiplier foldGlobal_3_53Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_54Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .xy), (.xx, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_54Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_54Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-80 / 141 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-116 / 235 : ℚ)
  else 0

def foldGlobal_3_54Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_54_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_54Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_54Network foldGlobal_3_54Generator 1
    foldGlobal_3_54Multiplier foldGlobal_3_54Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_55Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_55Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_55Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-80 / 141 : ℚ)
  else 0

def foldGlobal_3_55Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_55_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_55Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_55Network foldGlobal_3_55Generator 1
    foldGlobal_3_55Multiplier foldGlobal_3_55Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_56Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .xy), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_56Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)]]

def foldGlobal_3_56Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-5 / 18 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 18 : ℚ)
  else 0

def foldGlobal_3_56Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_56_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_56Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_56Network foldGlobal_3_56Generator 1
    foldGlobal_3_56Multiplier foldGlobal_3_56Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_57Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .x), (.y, .yy), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_57Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_57Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 32 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 32 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-7 / 48 : ℚ)
  else 0

def foldGlobal_3_57Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_57_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_57Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_57Network foldGlobal_3_57Generator 1
    foldGlobal_3_57Multiplier foldGlobal_3_57Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_58Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .xy), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_58Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_58Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 26 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-7 / 26 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-10 / 39 : ℚ)
  else 0

def foldGlobal_3_58Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_58_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_58Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_58Network foldGlobal_3_58Generator 1
    foldGlobal_3_58Multiplier foldGlobal_3_58Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_59Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.y, .yy), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_59Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_59Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 26 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-7 / 26 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-10 / 39 : ℚ)
  else 0

def foldGlobal_3_59Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_59_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_59Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_59Network foldGlobal_3_59Generator 1
    foldGlobal_3_59Multiplier foldGlobal_3_59Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_60Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_60Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_60Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-11 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-4 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-3 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-26 / 135 : ℚ)
  else 0

def foldGlobal_3_60Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_60_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_60Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_60Network foldGlobal_3_60Generator 1
    foldGlobal_3_60Multiplier foldGlobal_3_60Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_61Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_61Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_61Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 47 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-80 / 141 : ℚ)
  else 0

def foldGlobal_3_61Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_61_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_61Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_61Network foldGlobal_3_61Generator 1
    foldGlobal_3_61Multiplier foldGlobal_3_61Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_62Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_62Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_62Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-645 / 1748 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-2020 / 1311 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-839 / 874 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1592 / 1311 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1829 / 3933 : ℚ)
  else 0

def foldGlobal_3_62Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_62_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_62Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_62Network foldGlobal_3_62Generator 1
    foldGlobal_3_62Multiplier foldGlobal_3_62Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_63Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_63Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_63Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 24 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 24 : ℚ)
  else 0

def foldGlobal_3_63Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_63_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_63Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_63Network foldGlobal_3_63Generator 1
    foldGlobal_3_63Multiplier foldGlobal_3_63Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_64Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_64Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_64Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 36 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (13 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-5 / 36 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 36 : ℚ)
  else 0

def foldGlobal_3_64Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_64_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_64Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_64Network foldGlobal_3_64Generator (-1 : ℚ)
    foldGlobal_3_64Multiplier foldGlobal_3_64Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_65Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_65Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_65Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-5 / 19 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 19 : ℚ)
  else 0

def foldGlobal_3_65Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_65_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_65Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_65Network foldGlobal_3_65Generator 1
    foldGlobal_3_65Multiplier foldGlobal_3_65Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_66Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.y, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_66Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_66Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 27 : ℚ)
  else 0

def foldGlobal_3_66Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_66_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_66Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_66Network foldGlobal_3_66Generator 1
    foldGlobal_3_66Multiplier foldGlobal_3_66Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_67Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_67Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_3_67Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 80 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-17 / 40 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 8 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-19 / 80 : ℚ)
  else 0

def foldGlobal_3_67Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_67_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_67Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_67Network foldGlobal_3_67Generator 1
    foldGlobal_3_67Multiplier foldGlobal_3_67Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_68Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xx), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_68Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_68Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-54 / 215 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-272 / 1075 : ℚ)
  else 0

def foldGlobal_3_68Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_68_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_68Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_68Network foldGlobal_3_68Generator 1
    foldGlobal_3_68Multiplier foldGlobal_3_68Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_69Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_69Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_69Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 95 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-28 / 285 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3 / 95 : ℚ)
  else 0

def foldGlobal_3_69Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_69_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_69Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_69Network foldGlobal_3_69Generator 1
    foldGlobal_3_69Multiplier foldGlobal_3_69Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_70Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_70Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0]]

def foldGlobal_3_70Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 12 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 12 : ℚ)
  else 0

def foldGlobal_3_70Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_70_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_70Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_70Network foldGlobal_3_70Generator 1
    foldGlobal_3_70Multiplier foldGlobal_3_70Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_71Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.y, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_71Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_71Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 13 : ℚ)
  else 0

def foldGlobal_3_71Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_71_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_71Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_71Network foldGlobal_3_71Generator 1
    foldGlobal_3_71Multiplier foldGlobal_3_71Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_72Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.x, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_72Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_72Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-463 / 3438 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-299 / 2865 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (15 / 382 : ℚ)
  else 0

def foldGlobal_3_72Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_72_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_72Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_72Network foldGlobal_3_72Generator 1
    foldGlobal_3_72Multiplier foldGlobal_3_72Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_73Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_73Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_73Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 277 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 277 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 277 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (504 / 6925 : ℚ)
  else 0

def foldGlobal_3_73Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_73_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_73Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_73Network foldGlobal_3_73Generator (-1 : ℚ)
    foldGlobal_3_73Multiplier foldGlobal_3_73Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_74Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_74Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_74Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (4 / 243 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 27 : ℚ)
  else 0

def foldGlobal_3_74Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_74_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_74Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_74Network foldGlobal_3_74Generator (-1 : ℚ)
    foldGlobal_3_74Multiplier foldGlobal_3_74Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_75Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xx), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_75Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_3_75Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4 / 281 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 281 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4 / 281 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2052 / 13769 : ℚ)
  else 0

def foldGlobal_3_75Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_75_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_75Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_75Network foldGlobal_3_75Generator (-1 : ℚ)
    foldGlobal_3_75Multiplier foldGlobal_3_75Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_76Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_76Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_76Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-5 / 19 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 19 : ℚ)
  else 0

def foldGlobal_3_76Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_76_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_76Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_76Network foldGlobal_3_76Generator 1
    foldGlobal_3_76Multiplier foldGlobal_3_76Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_77Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_77Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_77Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-4 / 27 : ℚ)
  else 0

def foldGlobal_3_77Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_77_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_77Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_77Network foldGlobal_3_77Generator 1
    foldGlobal_3_77Multiplier foldGlobal_3_77Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_78Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_78Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_78Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 2 ∧ b.val = 2 then (1 / 15 : ℚ)
  else 0

def foldGlobal_3_78Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_78_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_78Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_78Network foldGlobal_3_78Generator 1
    foldGlobal_3_78Multiplier foldGlobal_3_78Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_79Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_79Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_79Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 67 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-59 / 134 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-28 / 201 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-259 / 603 : ℚ)
  else 0

def foldGlobal_3_79Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_79_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_79Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_79Network foldGlobal_3_79Generator 1
    foldGlobal_3_79Multiplier foldGlobal_3_79Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_80Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_80Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)]]

def foldGlobal_3_80Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-54 / 215 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-272 / 1075 : ℚ)
  else 0

def foldGlobal_3_80Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_80_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_80Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_80Network foldGlobal_3_80Generator 1
    foldGlobal_3_80Multiplier foldGlobal_3_80Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_81Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_81Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 2 : ℚ), 0, (1 / 6 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_81Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 2 ∧ b.val = 2 then (8 / 81 : ℚ)
  else 0

def foldGlobal_3_81Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_81_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_81Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_81Network foldGlobal_3_81Generator 1
    foldGlobal_3_81Multiplier foldGlobal_3_81Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_82Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.x, .yy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_82Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)]]

def foldGlobal_3_82Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-1 / 44 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-43 / 44 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 11 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-5 / 11 : ℚ)
  else 0

def foldGlobal_3_82Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_82_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_82Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_82Network foldGlobal_3_82Generator 1
    foldGlobal_3_82Multiplier foldGlobal_3_82Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_83Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_83Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_83Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-800 / 261 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-11552 / 6525 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-128 / 261 : ℚ)
  else 0

def foldGlobal_3_83Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_83_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_83Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_83Network foldGlobal_3_83Generator 1
    foldGlobal_3_83Multiplier foldGlobal_3_83Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_84Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_84Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_84Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 81 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 81 : ℚ)
  else 0

def foldGlobal_3_84Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_84_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_84Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_84Network foldGlobal_3_84Generator 1
    foldGlobal_3_84Multiplier foldGlobal_3_84Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_85Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_85Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_85Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (8 / 81 : ℚ)
  else 0

def foldGlobal_3_85Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_85_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_85Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_85Network foldGlobal_3_85Generator 1
    foldGlobal_3_85Multiplier foldGlobal_3_85Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_86Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_86Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_86Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (8 / 81 : ℚ)
  else 0

def foldGlobal_3_86Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_86_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_86Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_86Network foldGlobal_3_86Generator 1
    foldGlobal_3_86Multiplier foldGlobal_3_86Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_87Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_87Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_87Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (9 / 20 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3 / 10 : ℚ)
  else 0

def foldGlobal_3_87Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_87_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_87Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_87Network foldGlobal_3_87Generator 1
    foldGlobal_3_87Multiplier foldGlobal_3_87Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_88Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_88Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_88Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (3 / 10 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (9 / 20 : ℚ)
  else 0

def foldGlobal_3_88Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_88_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_88Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_88Network foldGlobal_3_88Generator 1
    foldGlobal_3_88Multiplier foldGlobal_3_88Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_89Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_89Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_89Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 49 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (2 / 49 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 49 : ℚ)
  else 0

def foldGlobal_3_89Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_89_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_89Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_89Network foldGlobal_3_89Generator 1
    foldGlobal_3_89Multiplier foldGlobal_3_89Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_90Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_90Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_90Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 36 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 36 : ℚ)
  else 0

def foldGlobal_3_90Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 2, 2⟩}

theorem foldGlobal_3_90_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_90Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_90Network foldGlobal_3_90Generator 1
    foldGlobal_3_90Multiplier foldGlobal_3_90Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_91Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_91Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_91Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 2 : ℚ)
  else 0

def foldGlobal_3_91Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_91_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_91Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_91Network foldGlobal_3_91Generator 1
    foldGlobal_3_91Multiplier foldGlobal_3_91Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_92Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_92Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_92Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-4 / 95 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-28 / 285 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3 / 95 : ℚ)
  else 0

def foldGlobal_3_92Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_92_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_92Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_92Network foldGlobal_3_92Generator 1
    foldGlobal_3_92Multiplier foldGlobal_3_92Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_93Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_93Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0]]

def foldGlobal_3_93Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-1 / 12 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 12 : ℚ)
  else 0

def foldGlobal_3_93Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_93_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_93Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_93Network foldGlobal_3_93Generator 1
    foldGlobal_3_93Multiplier foldGlobal_3_93Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_94Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_94Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_94Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-1 / 13 : ℚ)
  else 0

def foldGlobal_3_94Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_94_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_94Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_94Network foldGlobal_3_94Generator 1
    foldGlobal_3_94Multiplier foldGlobal_3_94Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_95Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.y, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_95Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, (1 / 6 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_95Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 2 ∧ b.val = 2 then (1 / 15 : ℚ)
  else 0

def foldGlobal_3_95Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_95_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_95Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_95Network foldGlobal_3_95Generator 1
    foldGlobal_3_95Multiplier foldGlobal_3_95Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_96Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.x, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_96Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_96Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-463 / 3438 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-299 / 2865 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (15 / 382 : ℚ)
  else 0

def foldGlobal_3_96Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_96_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_96Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_96Network foldGlobal_3_96Generator 1
    foldGlobal_3_96Multiplier foldGlobal_3_96Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_97Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_97Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_97Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-56 / 45 : ℚ)
  else 0

def foldGlobal_3_97Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_97_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_97Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_97Network foldGlobal_3_97Generator 1
    foldGlobal_3_97Multiplier foldGlobal_3_97Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_98Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_98Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_98Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 15 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 15 : ℚ)
  else 0

def foldGlobal_3_98Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_98_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_98Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_98Network foldGlobal_3_98Generator 1
    foldGlobal_3_98Multiplier foldGlobal_3_98Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_99Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_99Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_99Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (1 / 15 : ℚ)
  else 0

def foldGlobal_3_99Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_99_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_99Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_99Network foldGlobal_3_99Generator 1
    foldGlobal_3_99Multiplier foldGlobal_3_99Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
