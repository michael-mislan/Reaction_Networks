import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_4_550Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.xy, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_550Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_550Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (382 / 28569 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-82427 / 428535 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-18721 / 47615 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-37552 / 85707 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-37792 / 142845 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (12 / 9523 : ℚ)
  else 0

def foldGlobal_4_550Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_550_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_550Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_550Network foldGlobal_4_550Generator 1
    foldGlobal_4_550Multiplier foldGlobal_4_550Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_551Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.xy, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_551Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_551Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2999 / 41776 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-977 / 46998 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-23207 / 156660 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8194 / 23499 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-2 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-9194 / 39165 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (50 / 2611 : ℚ)
  else 0

def foldGlobal_4_551Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_551_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_551Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_551Network foldGlobal_4_551Generator 1
    foldGlobal_4_551Multiplier foldGlobal_4_551Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_552Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.xy, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_552Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_552Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 577 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1159 / 5193 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-3491 / 11540 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-5831 / 46737 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-6289 / 41544 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (10 / 577 : ℚ)
  else 0

def foldGlobal_4_552Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_552_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_552Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_552Network foldGlobal_4_552Generator 1
    foldGlobal_4_552Multiplier foldGlobal_4_552Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_553Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.xy, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_553Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_4_553Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-253 / 666 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-56 / 555 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-131 / 555 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-152 / 925 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-7 / 25 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (4 / 925 : ℚ)
  else 0

def foldGlobal_4_553Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_553_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_553Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_553Network foldGlobal_4_553Generator 1
    foldGlobal_4_553Multiplier foldGlobal_4_553Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_554Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.xy, .xx), (.yy, .zero), (.yy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_554Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_554Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2600 / 14481 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1271 / 9654 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-238 / 8045 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-383 / 4827 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1201 / 12872 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-342 / 8045 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-569 / 6436 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (12 / 1609 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (55 / 1609 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (265 / 19308 : ℚ)
  else 0

def foldGlobal_4_554Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_554_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_554Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_554Network foldGlobal_4_554Generator 1
    foldGlobal_4_554Multiplier foldGlobal_4_554Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_555Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_555Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_555Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (32 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (24 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 5 : ℚ)
  else 0

def foldGlobal_4_555Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 3⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_555_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_555Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_555Network foldGlobal_4_555Generator (-1 : ℚ)
    foldGlobal_4_555Multiplier foldGlobal_4_555Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_556Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_556Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_556Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (32 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (24 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 5 : ℚ)
  else 0

def foldGlobal_4_556Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 3⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_556_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_556Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_556Network foldGlobal_4_556Generator (-1 : ℚ)
    foldGlobal_4_556Multiplier foldGlobal_4_556Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_557Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_557Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (4 / 7 : ℚ), (1 / 7 : ℚ), 0, (2 / 7 : ℚ)],
  ![0, (3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_557Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (32 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (70 / 51 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 51 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (58 / 119 : ℚ)
  else 0

def foldGlobal_4_557Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_557_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_557Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_557Network foldGlobal_4_557Generator (-1 : ℚ)
    foldGlobal_4_557Multiplier foldGlobal_4_557Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_558Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_558Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, (4 / 7 : ℚ), 0, (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_558Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (32 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (160 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (31 / 39 : ℚ)
  else 0

def foldGlobal_4_558Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_558_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_558Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_558Network foldGlobal_4_558Generator (-1 : ℚ)
    foldGlobal_4_558Multiplier foldGlobal_4_558Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_559Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .zero), (.y, .xx), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_559Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ)]]

def foldGlobal_4_559Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 43 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-233 / 516 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-171 / 86 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 8 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-19 / 172 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-337 / 774 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-79 / 129 : ℚ)
  else 0

def foldGlobal_4_559Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_559_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_559Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_559Network foldGlobal_4_559Generator 1
    foldGlobal_4_559Multiplier foldGlobal_4_559Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_560Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .zero), (.y, .xy), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_560Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_560Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-16 / 201 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-85 / 134 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-76 / 201 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 201 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-89 / 134 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-12 / 67 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-16 / 201 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-130 / 201 : ℚ)
  else 0

def foldGlobal_4_560Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_560_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_560Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_560Network foldGlobal_4_560Generator 1
    foldGlobal_4_560Multiplier foldGlobal_4_560Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_561Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_561Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_561Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-1 / 2 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 8 : ℚ)
  else 0

def foldGlobal_4_561Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩, ⟨3, 3, 3, 3⟩}

theorem foldGlobal_4_561_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_561Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_561Network foldGlobal_4_561Generator 1
    foldGlobal_4_561Multiplier foldGlobal_4_561Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_562Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_562Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, (1 / 6 : ℚ), (1 / 2 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_562Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1822 / 303 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-3716 / 4545 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-6064 / 1515 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-136 / 101 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 303 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (12 / 101 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3233 / 7575 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-148 / 505 : ℚ)
  else 0

def foldGlobal_4_562Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_562_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_562Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_562Network foldGlobal_4_562Generator 1
    foldGlobal_4_562Multiplier foldGlobal_4_562Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_563Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_563Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_563Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 239 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (6593 / 3585 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (18 / 239 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-264 / 239 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4458 / 5975 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-866 / 1195 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-8524 / 5975 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-704 / 1195 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-7698 / 5975 : ℚ)
  else 0

def foldGlobal_4_563Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_563_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_563Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_563Network foldGlobal_4_563Generator 1
    foldGlobal_4_563Multiplier foldGlobal_4_563Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_564Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_564Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_4_564Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (132 / 425 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (44 / 85 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (44 / 425 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-22 / 425 : ℚ)
  else 0

def foldGlobal_4_564Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_564_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_564Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_564Network foldGlobal_4_564Generator 1
    foldGlobal_4_564Multiplier foldGlobal_4_564Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_565Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_565Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_565Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-3 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-20 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-7 / 3 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else 0

def foldGlobal_4_565Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_565_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_565Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_565Network foldGlobal_4_565Generator 1
    foldGlobal_4_565Multiplier foldGlobal_4_565Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_566Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .zero), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_566Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_566Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-4 / 13 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 39 : ℚ)
  else 0

def foldGlobal_4_566Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩, ⟨3, 3, 3, 3⟩}

theorem foldGlobal_4_566_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_566Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_566Network foldGlobal_4_566Generator 1
    foldGlobal_4_566Multiplier foldGlobal_4_566Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_567Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_567Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_4_567Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-131 / 74 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-87 / 148 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-28 / 37 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (3 / 592 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (9 / 148 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-3 / 148 : ℚ)
  else 0

def foldGlobal_4_567Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_567_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_567Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_567Network foldGlobal_4_567Generator 1
    foldGlobal_4_567Multiplier foldGlobal_4_567Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_568Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_568Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 6 : ℚ), (1 / 2 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 2 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_4_568Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (13 / 1359 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (10363 / 6644 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (13 / 151 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-5059 / 2718 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2711 / 4983 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-263 / 453 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1201 / 1359 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-5009 / 2718 : ℚ)
  else 0

def foldGlobal_4_568Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_568_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_568Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_568Network foldGlobal_4_568Generator 1
    foldGlobal_4_568Multiplier foldGlobal_4_568Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_569Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xy), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_569Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_569Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 171 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1 / 19 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (127 / 513 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-35 / 57 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (59 / 456 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-7 / 19 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-289 / 456 : ℚ)
  else 0

def foldGlobal_4_569Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_569_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_569Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_569Network foldGlobal_4_569Generator 1
    foldGlobal_4_569Multiplier foldGlobal_4_569Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_570Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_570Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_570Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (7 / 32 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (7 / 24 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (7 / 96 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-7 / 192 : ℚ)
  else 0

def foldGlobal_4_570Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_570_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_570Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_570Network foldGlobal_4_570Generator 1
    foldGlobal_4_570Multiplier foldGlobal_4_570Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_571Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_571Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_571Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-2 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 2 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-7 / 8 : ℚ)
  else 0

def foldGlobal_4_571Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 2⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_571_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_571Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_571Network foldGlobal_4_571Generator 1
    foldGlobal_4_571Multiplier foldGlobal_4_571Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_572Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .y), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_572Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (3 / 5 : ℚ), (1 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_572Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 5 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 15 : ℚ)
  else 0

def foldGlobal_4_572Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_572_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_572Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_572Network foldGlobal_4_572Generator (-1 : ℚ)
    foldGlobal_4_572Multiplier foldGlobal_4_572Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_573Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_573Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (4 / 7 : ℚ), (2 / 7 : ℚ), 0, (1 / 7 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_573Multiplier (_a _b : Fin 4) : ℚ :=
  0

def foldGlobal_4_573Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩}

theorem foldGlobal_4_573_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_573Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_573Network foldGlobal_4_573Generator (-1 : ℚ)
    foldGlobal_4_573Multiplier foldGlobal_4_573Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_574Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_574Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_574Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 243 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-20 / 243 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-4 / 243 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-17 / 405 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (8 / 81 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 27 : ℚ)
  else 0

def foldGlobal_4_574Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_574_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_574Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_574Network foldGlobal_4_574Generator (-1 : ℚ)
    foldGlobal_4_574Multiplier foldGlobal_4_574Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_575Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .zero), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_575Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (4 / 7 : ℚ), (2 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_4_575Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (16 / 135 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 45 : ℚ)
  else 0

def foldGlobal_4_575Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 3⟩}

theorem foldGlobal_4_575_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_575Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_575Network foldGlobal_4_575Generator (-1 : ℚ)
    foldGlobal_4_575Multiplier foldGlobal_4_575Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_576Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .x), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_576Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_576Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (1 / 36 : ℚ)
  else 0

def foldGlobal_4_576Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨1, 1, 1, 2⟩, ⟨1, 1, 1, 3⟩}

theorem foldGlobal_4_576_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_576Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_576Network foldGlobal_4_576Generator (-1 : ℚ)
    foldGlobal_4_576Multiplier foldGlobal_4_576Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_577Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xy, .x), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_577Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_577Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 2 ∧ b.val = 2 then (5 / 54 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (1 / 9 : ℚ)
  else 0

def foldGlobal_4_577Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 2, 2, 2⟩, ⟨0, 3, 3, 3⟩, ⟨1, 2, 2, 2⟩}

theorem foldGlobal_4_577_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_577Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_577Network foldGlobal_4_577Generator (-1 : ℚ)
    foldGlobal_4_577Multiplier foldGlobal_4_577Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_578Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_578Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_578Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-55 / 288 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-5 / 96 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-2 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-7 / 32 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1 / 6 : ℚ)
  else 0

def foldGlobal_4_578Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_578_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_578Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_578Network foldGlobal_4_578Generator 1
    foldGlobal_4_578Multiplier foldGlobal_4_578Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_579Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_579Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 6 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_4_579Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-331 / 5544 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-73 / 336 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-103 / 672 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-157 / 616 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-317 / 1232 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-83 / 1232 : ℚ)
  else 0

def foldGlobal_4_579Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_579_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_579Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_579Network foldGlobal_4_579Generator 1
    foldGlobal_4_579Multiplier foldGlobal_4_579Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_580Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.y, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_580Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(2 / 7 : ℚ), (4 / 7 : ℚ), 0, 0, (1 / 7 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_4_580Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-96 / 469 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-3643 / 59094 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1292 / 7035 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-110144 / 206829 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-7253 / 16415 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-3352 / 11725 : ℚ)
  else 0

def foldGlobal_4_580Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_580_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_580Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_580Network foldGlobal_4_580Generator 1
    foldGlobal_4_580Multiplier foldGlobal_4_580Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_581Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_581Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 6 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_4_581Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-773 / 5176 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-5623 / 15528 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1647 / 10352 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-865 / 2588 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-703 / 5176 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1 / 6 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-1273 / 5176 : ℚ)
  else 0

def foldGlobal_4_581Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_581_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_581Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_581Network foldGlobal_4_581Generator 1
    foldGlobal_4_581Multiplier foldGlobal_4_581Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_582Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_582Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_4_582Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-15 / 56 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-57 / 320 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 6 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-373 / 700 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-4 / 15 : ℚ)
  else 0

def foldGlobal_4_582Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_582_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_582Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_582Network foldGlobal_4_582Generator 1
    foldGlobal_4_582Multiplier foldGlobal_4_582Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_583Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.x, .yy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_583Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 6 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0]]

def foldGlobal_4_583Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-121 / 124 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-6 / 31 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-35 / 124 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-55 / 248 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-641 / 1860 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 4 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1389 / 3100 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1 / 2 : ℚ)
  else 0

def foldGlobal_4_583Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_583_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_583Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_583Network foldGlobal_4_583Generator 1
    foldGlobal_4_583Multiplier foldGlobal_4_583Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_584Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_584Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(2 / 7 : ℚ), 0, (2 / 7 : ℚ), (3 / 7 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_4_584Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-800 / 6993 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-32 / 259 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-40 / 333 : ℚ)
  else 0

def foldGlobal_4_584Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_584_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_584Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_584Network foldGlobal_4_584Generator 1
    foldGlobal_4_584Multiplier foldGlobal_4_584Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_585Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_585Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(2 / 7 : ℚ), 0, (2 / 7 : ℚ), (3 / 7 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_4_585Multiplier (_a _b : Fin 4) : ℚ :=
  0

def foldGlobal_4_585Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_585_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_585Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_585Network foldGlobal_4_585Generator 1
    foldGlobal_4_585Multiplier foldGlobal_4_585Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_586Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xy), (.xx, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_586Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 6 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_586Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-5 / 14 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-5 / 14 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-15 / 112 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-15 / 112 : ℚ)
  else 0

def foldGlobal_4_586Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_586_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_586Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_586Network foldGlobal_4_586Generator 1
    foldGlobal_4_586Multiplier foldGlobal_4_586Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_587Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .yy), (.xx, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_587Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 6 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_587Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8 / 81 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-16 / 81 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-2 / 27 : ℚ)
  else 0

def foldGlobal_4_587Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_587_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_587Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_587Network foldGlobal_4_587Generator 1
    foldGlobal_4_587Multiplier foldGlobal_4_587Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_588Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xx), (.xx, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_588Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_588Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-7 / 225 : ℚ)
  else 0

def foldGlobal_4_588Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_588_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_588Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_588Network foldGlobal_4_588Generator 1
    foldGlobal_4_588Multiplier foldGlobal_4_588Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_589Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_589Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_4_589Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-3886 / 9995 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-2567 / 7996 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-7783 / 11994 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-16511 / 49975 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-37665 / 31984 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1809 / 3998 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-31345 / 35982 : ℚ)
  else 0

def foldGlobal_4_589Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_589_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_589Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_589Network foldGlobal_4_589Generator 1
    foldGlobal_4_589Multiplier foldGlobal_4_589Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_590Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_590Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(2 / 7 : ℚ), (4 / 7 : ℚ), 0, 0, (1 / 7 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_4_590Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-608 / 535 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-16 / 21 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-4 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1968 / 2675 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-4912 / 5243 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-794 / 749 : ℚ)
  else 0

def foldGlobal_4_590Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 3⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_590_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_590Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_590Network foldGlobal_4_590Generator 1
    foldGlobal_4_590Multiplier foldGlobal_4_590Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_591Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .x), (.y, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_591Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_591Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 16 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-25 / 96 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 4 : ℚ)
  else 0

def foldGlobal_4_591Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_591_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_591Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_591Network foldGlobal_4_591Generator 1
    foldGlobal_4_591Multiplier foldGlobal_4_591Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_592Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_592Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 6 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_592Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 348 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-5 / 1044 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1 / 348 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-6389 / 26100 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-483 / 1160 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-79 / 290 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-269 / 1566 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-121 / 783 : ℚ)
  else 0

def foldGlobal_4_592Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_592_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_592Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_592Network foldGlobal_4_592Generator 1
    foldGlobal_4_592Multiplier foldGlobal_4_592Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_593Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .xx), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_593Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ)],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_4_593Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-653 / 650 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-11 / 13 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-83 / 208 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-5 / 26 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-95 / 234 : ℚ)
  else 0

def foldGlobal_4_593Witnesses : Finset (QuarticWitness 4) :=
  {⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_593_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_593Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_593Network foldGlobal_4_593Generator 1
    foldGlobal_4_593Multiplier foldGlobal_4_593Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_594Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_594Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(1 / 5 : ℚ), 0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_594Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 585 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-38 / 1755 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1826 / 5265 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-1826 / 5265 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 585 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-8 / 351 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-8 / 351 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-682 / 3159 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-562 / 3159 : ℚ)
  else 0

def foldGlobal_4_594Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_594_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_594Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_594Network foldGlobal_4_594Generator 1
    foldGlobal_4_594Multiplier foldGlobal_4_594Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_595Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_595Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![(1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ), 0, 0],
  ![(2 / 7 : ℚ), (4 / 7 : ℚ), 0, 0, (1 / 7 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_4_595Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-2 / 5 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-8 / 21 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-4 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-33 / 50 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-7 / 15 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-8 / 7 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1 / 3 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-13 / 36 : ℚ)
  else 0

def foldGlobal_4_595Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 3⟩, ⟨0, 1, 1, 1⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_595_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_595Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_595Network foldGlobal_4_595Generator 1
    foldGlobal_4_595Multiplier foldGlobal_4_595Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_596Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_596Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_596Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else 0

def foldGlobal_4_596Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_596_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_596Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_596Network foldGlobal_4_596Generator 1
    foldGlobal_4_596Multiplier foldGlobal_4_596Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_597Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .yy), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_597Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_597Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 6 : ℚ)
  else 0

def foldGlobal_4_597Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_597_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_597Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_597Network foldGlobal_4_597Generator 1
    foldGlobal_4_597Multiplier foldGlobal_4_597Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_598Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_598Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(2 / 5 : ℚ), 0, (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_598Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-25 / 528 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 66 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (23 / 66 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-5 / 88 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (7 / 22 : ℚ)
  else 0

def foldGlobal_4_598Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_598_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_598Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_598Network foldGlobal_4_598Generator 1
    foldGlobal_4_598Multiplier foldGlobal_4_598Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_599Network : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .xx), (.xx, .zero), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_599Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (2 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_599Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-5 / 256 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (7 / 80 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-3 / 128 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (26 / 75 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (29 / 160 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (83 / 480 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (1 / 160 : ℚ)
  else 0

def foldGlobal_4_599Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_599_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_599Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_599Network foldGlobal_4_599Generator 1
    foldGlobal_4_599Multiplier foldGlobal_4_599Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
