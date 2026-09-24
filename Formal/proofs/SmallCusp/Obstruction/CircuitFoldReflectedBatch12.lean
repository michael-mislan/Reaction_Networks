import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_4_600Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_600Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_600Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1291 / 5445 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (112 / 1815 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 605 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (709 / 1815 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (629 / 2420 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2474 / 1815 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (637 / 4840 : ℚ)
  else 0

def foldGlobal_4_600Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_600_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_600Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_600Network foldGlobal_4_600Generator 1
    foldGlobal_4_600Multiplier foldGlobal_4_600Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_601Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_601Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_4_601Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (134 / 195 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (1 / 39 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 975 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (86 / 195 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (194 / 585 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (2 / 15 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-4 / 975 : ℚ)
  else 0

def foldGlobal_4_601Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 3⟩}

theorem foldGlobal_4_601_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_601Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_601Network foldGlobal_4_601Generator 1
    foldGlobal_4_601Multiplier foldGlobal_4_601Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_602Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_602Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_602Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 1664 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (69 / 208 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-7 / 2496 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (311 / 1664 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (13 / 128 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (859 / 2496 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 1664 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (15 / 832 : ℚ)
  else 0

def foldGlobal_4_602Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_602_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_602Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_602Network foldGlobal_4_602Generator 1
    foldGlobal_4_602Multiplier foldGlobal_4_602Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_603Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .y), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_603Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 6 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_603Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (301 / 20814 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (3759 / 13876 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-189995 / 62442 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-3945 / 6938 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4049 / 27752 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-11825 / 72849 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-23483 / 31221 : ℚ)
  else 0

def foldGlobal_4_603Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 3⟩}

theorem foldGlobal_4_603_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_603Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_603Network foldGlobal_4_603Generator 1
    foldGlobal_4_603Multiplier foldGlobal_4_603Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_604Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_604Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_4_604Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (1 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (3 / 8 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 24 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (19 / 72 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-19 / 216 : ℚ)
  else 0

def foldGlobal_4_604Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 3⟩}

theorem foldGlobal_4_604_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_604Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_604Network foldGlobal_4_604Generator 1
    foldGlobal_4_604Multiplier foldGlobal_4_604Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_605Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .xy), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_605Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_605Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 60 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-2 / 45 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (1 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (17 / 120 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (11 / 60 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-19 / 540 : ℚ)
  else 0

def foldGlobal_4_605Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_605_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_605Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_605Network foldGlobal_4_605Generator 1
    foldGlobal_4_605Multiplier foldGlobal_4_605Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_606Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .zero), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_606Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 6 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_606Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-281 / 564 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-491 / 282 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (35 / 141 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (81 / 376 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1 / 4 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-1 / 141 : ℚ)
  else 0

def foldGlobal_4_606Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_606_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_606Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_606Network foldGlobal_4_606Generator (-1 : ℚ)
    foldGlobal_4_606Multiplier foldGlobal_4_606Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_607Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_607Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_607Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-31 / 66 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (76 / 99 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-163 / 220 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-133 / 594 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-289 / 990 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-5 / 33 : ℚ)
  else 0

def foldGlobal_4_607Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_607_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_607Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_607Network foldGlobal_4_607Generator (-1 : ℚ)
    foldGlobal_4_607Multiplier foldGlobal_4_607Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_608Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .x), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_608Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![(1 / 6 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_608Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (281 / 4560 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (189 / 760 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-28 / 57 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (71 / 285 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (33 / 152 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1 / 6 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-1 / 190 : ℚ)
  else 0

def foldGlobal_4_608Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_608_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_608Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_608Network foldGlobal_4_608Generator (-1 : ℚ)
    foldGlobal_4_608Multiplier foldGlobal_4_608Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_609Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xy, .x), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_609Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_609Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1005 / 8552 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1643 / 4276 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-2663 / 5345 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-646 / 3207 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 9 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-10352 / 26725 : ℚ)
  else 0

def foldGlobal_4_609Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_609_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_609Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_609Network foldGlobal_4_609Generator (-1 : ℚ)
    foldGlobal_4_609Multiplier foldGlobal_4_609Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_610Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .y), (.x, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_610Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(2 / 7 : ℚ), 0, (2 / 7 : ℚ), 0, (3 / 7 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_610Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 12 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-92 / 2835 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 15 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-736 / 6615 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-172 / 14175 : ℚ)
  else 0

def foldGlobal_4_610Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 3⟩}

theorem foldGlobal_4_610_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_610Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_610Network foldGlobal_4_610Generator 1
    foldGlobal_4_610Multiplier foldGlobal_4_610Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_611Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .yy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_611Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(2 / 7 : ℚ), (2 / 7 : ℚ), 0, 0, (3 / 7 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_611Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-16 / 10857 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-130684 / 683991 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-17464 / 54285 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1316104 / 14363811 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-358192 / 2442825 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (40 / 3619 : ℚ)
  else 0

def foldGlobal_4_611Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_611_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_611Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_611Network foldGlobal_4_611Generator 1
    foldGlobal_4_611Multiplier foldGlobal_4_611Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_612Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .yy), (.xy, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_612Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (1 / 5 : ℚ), (3 / 5 : ℚ), 0, 0],
  ![(2 / 7 : ℚ), (2 / 7 : ℚ), 0, 0, (3 / 7 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_612Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 50 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 35 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-2 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-4 / 25 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 7 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-6 / 35 : ℚ)
  else 0

def foldGlobal_4_612Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_612_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_612Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_612Network foldGlobal_4_612Generator 1
    foldGlobal_4_612Multiplier foldGlobal_4_612Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_613Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .yy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_613Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 7 : ℚ), (2 / 7 : ℚ), 0, 0, (3 / 7 : ℚ)],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_4_613Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-33 / 196 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-5 / 42 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-19 / 315 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-2 / 9 : ℚ)
  else 0

def foldGlobal_4_613Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 3⟩}

theorem foldGlobal_4_613_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_613Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_613Network foldGlobal_4_613Generator 1
    foldGlobal_4_613Multiplier foldGlobal_4_613Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_614Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .yy), (.xy, .xx), (.yy, .zero), (.yy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_614Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 7 : ℚ), (2 / 7 : ℚ), 0, (3 / 7 : ℚ), 0],
  ![(1 / 5 : ℚ), (1 / 5 : ℚ), 0, 0, (3 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_614Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 49 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-16 / 385 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-882 / 6875 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-28 / 275 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-12 / 275 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-2 / 55 : ℚ)
  else 0

def foldGlobal_4_614Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_614_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_614Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_614Network foldGlobal_4_614Generator 1
    foldGlobal_4_614Multiplier foldGlobal_4_614Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_615Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_615Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_4_615Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (1276 / 1251 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-317 / 417 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (442 / 1251 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-669 / 556 : ℚ)
  else 0

def foldGlobal_4_615Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩, ⟨3, 3, 3, 3⟩}

theorem foldGlobal_4_615_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_615Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_615Network foldGlobal_4_615Generator (-1 : ℚ)
    foldGlobal_4_615Multiplier foldGlobal_4_615Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_616Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_616Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_616Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (17 / 18 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (7 / 18 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 18 : ℚ)
  else 0

def foldGlobal_4_616Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩, ⟨3, 3, 3, 3⟩}

theorem foldGlobal_4_616_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_616Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_616Network foldGlobal_4_616Generator (-1 : ℚ)
    foldGlobal_4_616Multiplier foldGlobal_4_616Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_617Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_617Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_617Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-11 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-22 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (49 / 54 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (1 / 54 : ℚ)
  else 0

def foldGlobal_4_617Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩, ⟨2, 2, 2, 2⟩, ⟨3, 3, 3, 3⟩}

theorem foldGlobal_4_617_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_617Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_617Network foldGlobal_4_617Generator (-1 : ℚ)
    foldGlobal_4_617Multiplier foldGlobal_4_617Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_618Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_618Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_618Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (17 / 18 : ℚ)
  else 0

def foldGlobal_4_618Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩, ⟨3, 3, 3, 3⟩}

theorem foldGlobal_4_618_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_618Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_618Network foldGlobal_4_618Generator (-1 : ℚ)
    foldGlobal_4_618Multiplier foldGlobal_4_618Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_619Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_619Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, 0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_619Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (8 / 9 : ℚ)
  else 0

def foldGlobal_4_619Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩, ⟨2, 2, 2, 2⟩, ⟨3, 3, 3, 3⟩}

theorem foldGlobal_4_619_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_619Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_619Network foldGlobal_4_619Generator (-1 : ℚ)
    foldGlobal_4_619Multiplier foldGlobal_4_619Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_620Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_620Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_620Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (493 / 1008 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-5 / 112 : ℚ)
  else 0

def foldGlobal_4_620Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩, ⟨3, 3, 3, 3⟩}

theorem foldGlobal_4_620_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_620Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_620Network foldGlobal_4_620Generator (-1 : ℚ)
    foldGlobal_4_620Multiplier foldGlobal_4_620Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_621Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_621Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, 0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_621Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (4 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (16 / 21 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-24 / 25 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (16 / 49 : ℚ)
  else 0

def foldGlobal_4_621Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩, ⟨2, 2, 2, 2⟩, ⟨3, 3, 3, 3⟩}

theorem foldGlobal_4_621_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_621Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_621Network foldGlobal_4_621Generator (-1 : ℚ)
    foldGlobal_4_621Multiplier foldGlobal_4_621Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_622Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_622Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_622Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (1 / 8 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (437 / 2480 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-469 / 3720 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (81 / 1240 : ℚ)
  else 0

def foldGlobal_4_622Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩, ⟨2, 2, 2, 3⟩, ⟨3, 3, 3, 3⟩}

theorem foldGlobal_4_622_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_622Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_622Network foldGlobal_4_622Generator (-1 : ℚ)
    foldGlobal_4_622Multiplier foldGlobal_4_622Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_623Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xx), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_623Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0, 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_623Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (8 / 25 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4 / 15 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (8 / 35 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-4 / 21 : ℚ)
  else 0

def foldGlobal_4_623Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩, ⟨2, 3, 3, 3⟩, ⟨3, 3, 3, 3⟩}

theorem foldGlobal_4_623_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_623Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_623Network foldGlobal_4_623Generator (-1 : ℚ)
    foldGlobal_4_623Multiplier foldGlobal_4_623Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_624Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_624Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_4_624Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-268 / 273 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1104 / 455 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-704 / 945 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-680 / 2457 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-27008 / 20475 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-32 / 819 : ℚ)
  else 0

def foldGlobal_4_624Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_624_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_624Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_624Network foldGlobal_4_624Generator 1
    foldGlobal_4_624Multiplier foldGlobal_4_624Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_625Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_625Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 3 : ℚ), 0, (1 / 6 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_4_625Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (352 / 171 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (26 / 19 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (358 / 513 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (472 / 513 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (94 / 171 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (242 / 513 : ℚ)
  else 0

def foldGlobal_4_625Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_625_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_625Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_625Network foldGlobal_4_625Generator (-1 : ℚ)
    foldGlobal_4_625Multiplier foldGlobal_4_625Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_626Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_626Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_626Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (340 / 171 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (68 / 57 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (118 / 171 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (52 / 57 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (11 / 19 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (89 / 171 : ℚ)
  else 0

def foldGlobal_4_626Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_626_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_626Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_626Network foldGlobal_4_626Generator (-1 : ℚ)
    foldGlobal_4_626Multiplier foldGlobal_4_626Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_627Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_627Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_627Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (49 / 27 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (14 / 27 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (109 / 243 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (217 / 243 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (10 / 243 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (8 / 243 : ℚ)
  else 0

def foldGlobal_4_627Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_627_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_627Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_627Network foldGlobal_4_627Generator (-1 : ℚ)
    foldGlobal_4_627Multiplier foldGlobal_4_627Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_628Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_628Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (3 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_628Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (2848 / 1359 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (3224 / 2265 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (1928 / 2265 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1256 / 1359 : ℚ)
  else 0

def foldGlobal_4_628Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_628_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_628Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_628Network foldGlobal_4_628Generator (-1 : ℚ)
    foldGlobal_4_628Multiplier foldGlobal_4_628Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_629Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_629Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (4 / 7 : ℚ), (2 / 7 : ℚ), 0, (1 / 7 : ℚ)],
  ![0, 0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_629Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (16 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (284 / 225 : ℚ)
  else 0

def foldGlobal_4_629Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_629_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_629Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_629Network foldGlobal_4_629Generator (-1 : ℚ)
    foldGlobal_4_629Multiplier foldGlobal_4_629Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_630Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_630Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (3 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_630Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (89 / 60 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (91 / 60 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (17 / 60 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (83 / 180 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (127 / 150 : ℚ)
  else 0

def foldGlobal_4_630Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_630_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_630Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_630Network foldGlobal_4_630Generator (-1 : ℚ)
    foldGlobal_4_630Multiplier foldGlobal_4_630Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_631Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .y), (.y, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_631Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (4 / 7 : ℚ), (2 / 7 : ℚ), 0, (1 / 7 : ℚ)],
  ![0, 0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_631Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1300 / 831 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (8080 / 5817 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (64 / 2493 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1172 / 2493 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1272 / 1939 : ℚ)
  else 0

def foldGlobal_4_631Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_631_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_631Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_631Network foldGlobal_4_631Generator (-1 : ℚ)
    foldGlobal_4_631Multiplier foldGlobal_4_631Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_632Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_632Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_4_632Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-13 / 21 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-32 / 21 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-136 / 315 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-58 / 63 : ℚ)
  else 0

def foldGlobal_4_632Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_632_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_632Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_632Network foldGlobal_4_632Generator 1
    foldGlobal_4_632Multiplier foldGlobal_4_632Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_633Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.xx, .zero), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_633Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (4 / 7 : ℚ), (1 / 7 : ℚ), 0, (2 / 7 : ℚ)]]

def foldGlobal_4_633Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (2 / 7 : ℚ)
  else 0

def foldGlobal_4_633Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_633_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_633Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_633Network foldGlobal_4_633Generator (-1 : ℚ)
    foldGlobal_4_633Multiplier foldGlobal_4_633Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_634Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.xx, .y), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_634Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_634Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (451 / 1272 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (15 / 424 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (213 / 848 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (491 / 848 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (685 / 636 : ℚ)
  else 0

def foldGlobal_4_634Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_634_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_634Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_634Network foldGlobal_4_634Generator (-1 : ℚ)
    foldGlobal_4_634Multiplier foldGlobal_4_634Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_635Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_635Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_4_635Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (19 / 12 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (25 / 48 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (131 / 144 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (4 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 48 : ℚ)
  else 0

def foldGlobal_4_635Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_635_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_635Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_635Network foldGlobal_4_635Generator (-1 : ℚ)
    foldGlobal_4_635Multiplier foldGlobal_4_635Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_636Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_636Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_636Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 25 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 25 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-17 / 225 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (118 / 75 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (133 / 200 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (409 / 450 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (53 / 150 : ℚ)
  else 0

def foldGlobal_4_636Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_636_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_636Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_636Network foldGlobal_4_636Generator (-1 : ℚ)
    foldGlobal_4_636Multiplier foldGlobal_4_636Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_637Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_637Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_637Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (23 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (7 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (163 / 180 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (8 / 45 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 60 : ℚ)
  else 0

def foldGlobal_4_637Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_637_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_637Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_637Network foldGlobal_4_637Generator (-1 : ℚ)
    foldGlobal_4_637Multiplier foldGlobal_4_637Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_638Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_638Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_638Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 183 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-8 / 183 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-10 / 183 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-11 / 427 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (340 / 183 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (32 / 61 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (512 / 549 : ℚ)
  else 0

def foldGlobal_4_638Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_638_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_638Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_638Network foldGlobal_4_638Generator (-1 : ℚ)
    foldGlobal_4_638Multiplier foldGlobal_4_638Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_639Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.xx, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_639Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_639Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (129 / 532 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (27 / 266 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (389 / 1064 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (83 / 114 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 133 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (293 / 1596 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (365 / 1197 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (649 / 2128 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (1145 / 1596 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (811 / 1197 : ℚ)
  else 0

def foldGlobal_4_639Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩}

theorem foldGlobal_4_639_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_639Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_639Network foldGlobal_4_639Generator (-1 : ℚ)
    foldGlobal_4_639Multiplier foldGlobal_4_639Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_640Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_640Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_640Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 183 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-4 / 183 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-20 / 549 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-41 / 1708 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (77 / 61 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (4 / 183 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (256 / 549 : ℚ)
  else 0

def foldGlobal_4_640Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_640_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_640Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_640Network foldGlobal_4_640Generator (-1 : ℚ)
    foldGlobal_4_640Multiplier foldGlobal_4_640Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_641Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .xy), (.y, .yy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_641Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_4_641Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 6 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-89 / 388 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-89 / 291 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-241 / 776 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-18 / 97 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-62 / 291 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-107 / 388 : ℚ)
  else 0

def foldGlobal_4_641Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨0, 3, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_641_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_641Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_641Network foldGlobal_4_641Generator 1
    foldGlobal_4_641Multiplier foldGlobal_4_641Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_642Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_642Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_4_642Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-4 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-64 / 27 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-8 / 15 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-128 / 81 : ℚ)
  else 0

def foldGlobal_4_642Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_642_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_642Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_642Network foldGlobal_4_642Generator 1
    foldGlobal_4_642Multiplier foldGlobal_4_642Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_643Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_643Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_4_643Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (17 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (55 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (73 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (26 / 81 : ℚ)
  else 0

def foldGlobal_4_643Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_643_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_643Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_643Network foldGlobal_4_643Generator (-1 : ℚ)
    foldGlobal_4_643Multiplier foldGlobal_4_643Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_644Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_644Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 6 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_644Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (17 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (55 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (73 / 81 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (35 / 81 : ℚ)
  else 0

def foldGlobal_4_644Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_644_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_644Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_644Network foldGlobal_4_644Generator (-1 : ℚ)
    foldGlobal_4_644Multiplier foldGlobal_4_644Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_645Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_645Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 6 : ℚ), (1 / 3 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_645Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (28 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (184 / 405 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (364 / 405 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (32 / 405 : ℚ)
  else 0

def foldGlobal_4_645Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_645_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_645Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_645Network foldGlobal_4_645Generator (-1 : ℚ)
    foldGlobal_4_645Multiplier foldGlobal_4_645Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_646Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_646Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_646Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (8 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (200 / 99 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (128 / 165 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (272 / 297 : ℚ)
  else 0

def foldGlobal_4_646Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_646_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_646Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_646Network foldGlobal_4_646Generator (-1 : ℚ)
    foldGlobal_4_646Multiplier foldGlobal_4_646Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_647Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_647Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (4 / 9 : ℚ), (2 / 9 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_647Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (64 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (8 / 9 : ℚ)
  else 0

def foldGlobal_4_647Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_647_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_647Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_647Network foldGlobal_4_647Generator (-1 : ℚ)
    foldGlobal_4_647Multiplier foldGlobal_4_647Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_648Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_648Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_648Multiplier (a b : Fin 4) : ℚ :=
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

def foldGlobal_4_648Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_648_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_648Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_648Network foldGlobal_4_648Generator 1
    foldGlobal_4_648Multiplier foldGlobal_4_648Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_649Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_649Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (4 / 9 : ℚ), (2 / 9 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_649Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-16556 / 17919 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-2 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-64400 / 53757 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-6928 / 29865 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-87224 / 161271 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-32 / 1991 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (160 / 1991 : ℚ)
  else 0

def foldGlobal_4_649Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 2, 2, 2⟩}

theorem foldGlobal_4_649_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_649Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_649Network foldGlobal_4_649Generator 1
    foldGlobal_4_649Multiplier foldGlobal_4_649Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
