import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_4_650Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_650Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (1 / 5 : ℚ), (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_650Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (33 / 40 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (8 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (89 / 60 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (17 / 60 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (83 / 180 : ℚ)
  else 0

def foldGlobal_4_650Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_650_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_650Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_650Network foldGlobal_4_650Generator (-1 : ℚ)
    foldGlobal_4_650Multiplier foldGlobal_4_650Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_651Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_651Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (4 / 9 : ℚ), (2 / 9 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (2 / 7 : ℚ), (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_651Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (4 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 9 : ℚ)
  else 0

def foldGlobal_4_651Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_651_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_651Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_651Network foldGlobal_4_651Generator (-1 : ℚ)
    foldGlobal_4_651Multiplier foldGlobal_4_651Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_652Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_652Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_652Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-837 / 1262 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-364 / 631 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-887 / 3155 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 3 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-683 / 1893 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-4 / 631 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (20 / 631 : ℚ)
  else 0

def foldGlobal_4_652Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 2, 2, 2⟩}

theorem foldGlobal_4_652_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_652Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_652Network foldGlobal_4_652Generator 1
    foldGlobal_4_652Multiplier foldGlobal_4_652Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_653Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.x, .yy), (.y, .yy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_653Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_4_653Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-28 / 29 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-56 / 87 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-47 / 116 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 4 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-6 / 29 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-15 / 58 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-9 / 29 : ℚ)
  else 0

def foldGlobal_4_653Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 2, 2, 2⟩, ⟨1, 3, 3, 3⟩}

theorem foldGlobal_4_653_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_653Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_653Network foldGlobal_4_653Generator 1
    foldGlobal_4_653Multiplier foldGlobal_4_653Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_654Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_654Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_654Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (8 / 279 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (64 / 93 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (26 / 93 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 31 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (97 / 186 : ℚ)
  else 0

def foldGlobal_4_654Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_654_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_654Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_654Network foldGlobal_4_654Generator (-1 : ℚ)
    foldGlobal_4_654Multiplier foldGlobal_4_654Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_655Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .y), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_655Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_655Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (5 / 7 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (23 / 42 : ℚ)
  else 0

def foldGlobal_4_655Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_655_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_655Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_655Network foldGlobal_4_655Generator (-1 : ℚ)
    foldGlobal_4_655Multiplier foldGlobal_4_655Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_656Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_656Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_656Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1088 / 3165 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (146 / 211 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (640 / 1899 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (665 / 1266 : ℚ)
  else 0

def foldGlobal_4_656Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_656_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_656Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_656Network foldGlobal_4_656Generator (-1 : ℚ)
    foldGlobal_4_656Multiplier foldGlobal_4_656Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_657Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_657Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_657Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (41 / 20 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (41 / 20 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1 / 30 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (9 / 40 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-3 / 10 : ℚ)
  else 0

def foldGlobal_4_657Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_657_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_657Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_657Network foldGlobal_4_657Generator (-1 : ℚ)
    foldGlobal_4_657Multiplier foldGlobal_4_657Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_658Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .y), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_658Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 6 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_658Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (67 / 32 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (67 / 32 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 2 : ℚ)
  else 0

def foldGlobal_4_658Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_658_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_658Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_658Network foldGlobal_4_658Generator (-1 : ℚ)
    foldGlobal_4_658Multiplier foldGlobal_4_658Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_659Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_659Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_659Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (102 / 49 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (102 / 49 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (96 / 245 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (8 / 21 : ℚ)
  else 0

def foldGlobal_4_659Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_659_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_659Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_659Network foldGlobal_4_659Generator (-1 : ℚ)
    foldGlobal_4_659Multiplier foldGlobal_4_659Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_660Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_660Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 2 : ℚ), 0, (1 / 6 : ℚ)],
  ![0, (4 / 9 : ℚ), 0, (1 / 3 : ℚ), (2 / 9 : ℚ)]]

def foldGlobal_4_660Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (32 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (2 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (8 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (64 / 25 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 15 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (16 / 45 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (8 / 27 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (16 / 81 : ℚ)
  else 0

def foldGlobal_4_660Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_660_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_660Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_660Network foldGlobal_4_660Generator (-1 : ℚ)
    foldGlobal_4_660Multiplier foldGlobal_4_660Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_661Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_661Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_661Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (12602 / 3249 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (457 / 1083 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (2764 / 3249 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (26104 / 9025 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1778 / 1805 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (3368 / 5415 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1019 / 722 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (2636 / 1083 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (6136 / 3249 : ℚ)
  else 0

def foldGlobal_4_661Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_661_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_661Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_661Network foldGlobal_4_661Generator (-1 : ℚ)
    foldGlobal_4_661Multiplier foldGlobal_4_661Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_662Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xx, .yy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_662Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_4_662Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (32 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (64 / 25 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-8 / 15 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-8 / 25 : ℚ)
  else 0

def foldGlobal_4_662Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_662_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_662Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_662Network foldGlobal_4_662Generator (-1 : ℚ)
    foldGlobal_4_662Multiplier foldGlobal_4_662Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_663Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xx, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_663Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (2 / 7 : ℚ), 0, (3 / 7 : ℚ), (2 / 7 : ℚ)]]

def foldGlobal_4_663Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (284 / 63 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (32 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (172 / 105 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (344 / 147 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (32 / 25 : ℚ)
  else 0

def foldGlobal_4_663Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_663_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_663Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_663Network foldGlobal_4_663Generator (-1 : ℚ)
    foldGlobal_4_663Multiplier foldGlobal_4_663Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_664Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xx, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_664Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ), 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), 0, (1 / 7 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_664Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (32 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-4 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-28 / 15 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (32 / 25 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-576 / 49 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-1152 / 35 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-576 / 25 : ℚ)
  else 0

def foldGlobal_4_664Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_664_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_664Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_664Network foldGlobal_4_664Generator (-1 : ℚ)
    foldGlobal_4_664Multiplier foldGlobal_4_664Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_665Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_665Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_665Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (41 / 78 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (9 / 13 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (7 / 39 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (20 / 117 : ℚ)
  else 0

def foldGlobal_4_665Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_665_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_665Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_665Network foldGlobal_4_665Generator (-1 : ℚ)
    foldGlobal_4_665Multiplier foldGlobal_4_665Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_666Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_666Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 2 : ℚ), (1 / 6 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_666Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (53 / 102 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (151 / 102 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (41 / 51 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (79 / 204 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (139 / 153 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (40 / 51 : ℚ)
  else 0

def foldGlobal_4_666Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_666_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_666Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_666Network foldGlobal_4_666Generator (-1 : ℚ)
    foldGlobal_4_666Multiplier foldGlobal_4_666Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_667Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_667Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_667Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (71 / 138 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (37 / 23 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (29 / 46 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (17 / 23 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (187 / 207 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (227 / 276 : ℚ)
  else 0

def foldGlobal_4_667Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_667_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_667Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_667Network foldGlobal_4_667Generator (-1 : ℚ)
    foldGlobal_4_667Multiplier foldGlobal_4_667Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_668Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_668Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_668Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (233 / 190 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (81 / 95 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (278 / 285 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (364 / 285 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 95 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1072 / 855 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (2 / 95 : ℚ)
  else 0

def foldGlobal_4_668Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_668_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_668Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_668Network foldGlobal_4_668Generator (-1 : ℚ)
    foldGlobal_4_668Multiplier foldGlobal_4_668Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_669Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_669Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_669Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (27 / 46 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (124 / 69 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (124 / 115 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (34 / 23 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (260 / 207 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (196 / 345 : ℚ)
  else 0

def foldGlobal_4_669Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_669_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_669Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_669Network foldGlobal_4_669Generator (-1 : ℚ)
    foldGlobal_4_669Multiplier foldGlobal_4_669Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_670Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_670Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_670Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (31 / 16 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (3 / 8 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (11 / 9 : ℚ)
  else 0

def foldGlobal_4_670Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_670_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_670Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_670Network foldGlobal_4_670Generator (-1 : ℚ)
    foldGlobal_4_670Multiplier foldGlobal_4_670Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_671Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_671Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 6 : ℚ), (1 / 2 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 2 : ℚ), (1 / 6 : ℚ)]]

def foldGlobal_4_671Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 2 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (146 / 87 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (25 / 87 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (82 / 87 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (244 / 261 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (215 / 261 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-4 / 87 : ℚ)
  else 0

def foldGlobal_4_671Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_671_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_671Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_671Network foldGlobal_4_671Generator (-1 : ℚ)
    foldGlobal_4_671Multiplier foldGlobal_4_671Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_672Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_672Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), 0, (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_672Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 73 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 73 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-10 / 219 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-7 / 146 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (117 / 73 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (46 / 73 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (593 / 657 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (239 / 292 : ℚ)
  else 0

def foldGlobal_4_672Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_672_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_672Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_672Network foldGlobal_4_672Generator (-1 : ℚ)
    foldGlobal_4_672Multiplier foldGlobal_4_672Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_673Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_673Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ)],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_673Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (233 / 190 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (278 / 285 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (81 / 95 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (364 / 285 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1072 / 855 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (2 / 95 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-2 / 95 : ℚ)
  else 0

def foldGlobal_4_673Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_673_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_673Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_673Network foldGlobal_4_673Generator (-1 : ℚ)
    foldGlobal_4_673Multiplier foldGlobal_4_673Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_674Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_674Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_674Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 57 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-4 / 57 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-20 / 171 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-32 / 399 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (100 / 57 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (12 / 19 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (238 / 171 : ℚ)
  else 0

def foldGlobal_4_674Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_674_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_674Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_674Network foldGlobal_4_674Generator (-1 : ℚ)
    foldGlobal_4_674Multiplier foldGlobal_4_674Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_675Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_675Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 6 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_675Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1301 / 441 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (34 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (974 / 441 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (517 / 441 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (223 / 441 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (2477 / 2205 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (535 / 294 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (559 / 490 : ℚ)
  else 0

def foldGlobal_4_675Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_675_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_675Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_675Network foldGlobal_4_675Generator (-1 : ℚ)
    foldGlobal_4_675Multiplier foldGlobal_4_675Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_676Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_676Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ)]]

def foldGlobal_4_676Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (292 / 99 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (98 / 33 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (491 / 297 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (116 / 99 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (19 / 33 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (731 / 891 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (83 / 66 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (265 / 297 : ℚ)
  else 0

def foldGlobal_4_676Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_676_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_676Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_676Network foldGlobal_4_676Generator (-1 : ℚ)
    foldGlobal_4_676Multiplier foldGlobal_4_676Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_677Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_677Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_677Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (703 / 234 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (304 / 117 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (257 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (287 / 234 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (191 / 234 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (34 / 39 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (127 / 117 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (77 / 117 : ℚ)
  else 0

def foldGlobal_4_677Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_677_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_677Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_677Network foldGlobal_4_677Generator (-1 : ℚ)
    foldGlobal_4_677Multiplier foldGlobal_4_677Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_678Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_678Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 5 : ℚ), (3 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_678Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (757 / 234 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (47 / 30 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (23 / 30 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (341 / 234 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (29 / 39 : ℚ)
  else 0

def foldGlobal_4_678Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_678_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_678Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_678Network foldGlobal_4_678Generator (-1 : ℚ)
    foldGlobal_4_678Multiplier foldGlobal_4_678Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_679Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_679Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 7 : ℚ), (4 / 7 : ℚ), 0, (1 / 7 : ℚ)],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_679Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3578 / 1089 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (3848 / 2541 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (1912 / 2541 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1642 / 1089 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (1192 / 2541 : ℚ)
  else 0

def foldGlobal_4_679Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_679_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_679Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_679Network foldGlobal_4_679Generator (-1 : ℚ)
    foldGlobal_4_679Multiplier foldGlobal_4_679Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_680Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .x), (.y, .yy), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_680Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_4_680Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 84 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (29 / 84 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (2 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (5 / 28 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (5 / 63 : ℚ)
  else 0

def foldGlobal_4_680Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_680_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_680Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_680Network foldGlobal_4_680Generator (-1 : ℚ)
    foldGlobal_4_680Multiplier foldGlobal_4_680Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_681Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_681Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, 0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_4_681Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (125 / 234 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (37 / 27 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (224 / 585 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (137 / 234 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (56 / 117 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (344 / 1755 : ℚ)
  else 0

def foldGlobal_4_681Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_681_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_681Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_681Network foldGlobal_4_681Generator (-1 : ℚ)
    foldGlobal_4_681Multiplier foldGlobal_4_681Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_682Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .xy), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_682Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)],
  ![0, 0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_682Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (5 / 4 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (19 / 70 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (17 / 75 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (43 / 90 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 105 : ℚ)
  else 0

def foldGlobal_4_682Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_682_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_682Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_682Network foldGlobal_4_682Generator (-1 : ℚ)
    foldGlobal_4_682Multiplier foldGlobal_4_682Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_683Network : CodedBimolNetwork where
  reaction := ![(.x, .zero), (.y, .xx), (.y, .yy), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_683Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_683Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 33 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 33 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-5 / 66 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-16 / 231 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 2 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (27 / 22 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (3 / 11 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (47 / 99 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-2 / 77 : ℚ)
  else 0

def foldGlobal_4_683Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 3, 3⟩}

theorem foldGlobal_4_683_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_683Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_683Network foldGlobal_4_683Generator (-1 : ℚ)
    foldGlobal_4_683Multiplier foldGlobal_4_683Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_684Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_684Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 3 : ℚ), 0, (1 / 6 : ℚ)]]

def foldGlobal_4_684Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (5 / 19 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (5 / 19 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (1 / 6 : ℚ)
  else 0

def foldGlobal_4_684Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_684_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_684Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_684Network foldGlobal_4_684Generator (-1 : ℚ)
    foldGlobal_4_684Multiplier foldGlobal_4_684Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_685Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.xx, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_685Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (4 / 7 : ℚ), (2 / 7 : ℚ), 0, (1 / 7 : ℚ)]]

def foldGlobal_4_685Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (5 / 36 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (5 / 12 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (115 / 252 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (5 / 36 : ℚ)
  else 0

def foldGlobal_4_685Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 2, 2, 2⟩}

theorem foldGlobal_4_685_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_685Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_685Network foldGlobal_4_685Generator (-1 : ℚ)
    foldGlobal_4_685Multiplier foldGlobal_4_685Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_686Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_686Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, 0, (1 / 4 : ℚ)],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_4_686Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 288 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1 / 32 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (73 / 288 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (41 / 144 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (17 / 288 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (9 / 32 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (3 / 8 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (5 / 18 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (73 / 144 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (25 / 72 : ℚ)
  else 0

def foldGlobal_4_686Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_686_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_686Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_686Network foldGlobal_4_686Generator (-1 : ℚ)
    foldGlobal_4_686Multiplier foldGlobal_4_686Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_687Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_687Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(2 / 5 : ℚ), (2 / 5 : ℚ), 0, 0, (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_4_687Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (32 / 3737 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (192 / 3737 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (1056 / 18685 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (352 / 3737 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (3392 / 18685 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (12448 / 93425 : ℚ)
  else 0

def foldGlobal_4_687Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 2⟩, ⟨0, 0, 0, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_687_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_687Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_687Network foldGlobal_4_687Generator (-1 : ℚ)
    foldGlobal_4_687Multiplier foldGlobal_4_687Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_688Network : CodedBimolNetwork where
  reaction := ![(.x, .y), (.x, .xx), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_688Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, 0, (1 / 3 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_688Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1487 / 1116 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-415 / 1116 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (1373 / 2604 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1 / 7 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 93 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-39 / 217 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (145 / 6076 : ℚ)
  else 0

def foldGlobal_4_688Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 2, 2, 2⟩, ⟨1, 3, 3, 3⟩}

theorem foldGlobal_4_688_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_688Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_688Network foldGlobal_4_688Generator (-1 : ℚ)
    foldGlobal_4_688Multiplier foldGlobal_4_688Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_689Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_689Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_689Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-2 / 15 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-2 / 15 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 2105 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-3832 / 31575 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-163 / 1263 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3707 / 52625 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (1116 / 52625 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (468 / 52625 : ℚ)
  else 0

def foldGlobal_4_689Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨0, 3, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_689_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_689Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_689Network foldGlobal_4_689Generator (-1 : ℚ)
    foldGlobal_4_689Multiplier foldGlobal_4_689Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_690Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .xy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_690Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (4 / 7 : ℚ), 0, (2 / 7 : ℚ), (1 / 7 : ℚ)],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_690Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-4 / 21 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-4 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (96 / 5899 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-18124 / 123879 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-21580 / 123879 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (33504 / 289051 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (26592 / 289051 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (11616 / 289051 : ℚ)
  else 0

def foldGlobal_4_690Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 1, 1⟩, ⟨0, 2, 2, 2⟩, ⟨0, 3, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_690_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_690Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_690Network foldGlobal_4_690Generator (-1 : ℚ)
    foldGlobal_4_690Multiplier foldGlobal_4_690Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_691Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_691Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 7 : ℚ), (1 / 7 : ℚ), (4 / 7 : ℚ), 0],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_691Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (2360 / 4319 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (360 / 4319 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (600 / 4319 : ℚ)
  else 0

def foldGlobal_4_691Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 3⟩, ⟨1, 2, 2, 2⟩}

theorem foldGlobal_4_691_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_691Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_691Network foldGlobal_4_691Generator (-1 : ℚ)
    foldGlobal_4_691Multiplier foldGlobal_4_691Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_692Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_692Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(2 / 5 : ℚ), 0, (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_692Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (17 / 150 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (254 / 1125 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (14 / 225 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (56 / 375 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (8 / 125 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (8 / 375 : ℚ)
  else 0

def foldGlobal_4_692Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 2, 2, 2⟩, ⟨2, 2, 2, 2⟩}

theorem foldGlobal_4_692_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_692Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_692Network foldGlobal_4_692Generator (-1 : ℚ)
    foldGlobal_4_692Multiplier foldGlobal_4_692Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_693Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_693Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (3 / 5 : ℚ), (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_693Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1163 / 1552 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 3 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1363 / 4656 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (211 / 776 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-2 / 15 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (9 / 1552 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (-2969 / 23280 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (117 / 9700 : ℚ)
  else 0

def foldGlobal_4_693Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 2⟩, ⟨1, 2, 2, 2⟩, ⟨1, 3, 3, 3⟩}

theorem foldGlobal_4_693_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_693Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_693Network foldGlobal_4_693Generator (-1 : ℚ)
    foldGlobal_4_693Multiplier foldGlobal_4_693Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_694Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.x, .yy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_694Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (4 / 9 : ℚ), 0, (2 / 9 : ℚ), (1 / 3 : ℚ)],
  ![0, 0, (4 / 7 : ℚ), (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_694Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (-4 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (-4 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-4 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-4 / 21 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (709 / 756 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (16 / 63 : ℚ)
  else 0

def foldGlobal_4_694Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 1, 2, 2⟩, ⟨0, 2, 2, 2⟩, ⟨0, 3, 3, 3⟩, ⟨1, 1, 2, 2⟩}

theorem foldGlobal_4_694_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_694Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_694Network foldGlobal_4_694Generator (-1 : ℚ)
    foldGlobal_4_694Multiplier foldGlobal_4_694Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_695Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_695Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(1 / 4 : ℚ), 0, 0, (1 / 2 : ℚ), (1 / 4 : ℚ)],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (1 / 5 : ℚ), 0, (3 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_695Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (32 / 15 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 5 : ℚ)
  else 0

def foldGlobal_4_695Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 3⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_695_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_695Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_695Network foldGlobal_4_695Generator (-1 : ℚ)
    foldGlobal_4_695Multiplier foldGlobal_4_695Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_696Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_696Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(2 / 5 : ℚ), 0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (2 / 7 : ℚ), 0, (4 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_696Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (32 / 15 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-22 / 125 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-14 / 125 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 5 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-116 / 245 : ℚ)
  else 0

def foldGlobal_4_696Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 3⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_696_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_696Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_696Network foldGlobal_4_696Generator (-1 : ℚ)
    foldGlobal_4_696Multiplier foldGlobal_4_696Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_697Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_697Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (4 / 7 : ℚ), (1 / 7 : ℚ), 0, (2 / 7 : ℚ)],
  ![0, (3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_4_697Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (16 / 21 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-49 / 450 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-2 / 15 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1714 / 3675 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (4 / 35 : ℚ)
  else 0

def foldGlobal_4_697Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 2⟩}

theorem foldGlobal_4_697_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_697Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_697Network foldGlobal_4_697Generator (-1 : ℚ)
    foldGlobal_4_697Multiplier foldGlobal_4_697Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_698Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .zero), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_698Generator : Fin 4 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ)],
  ![0, (4 / 7 : ℚ), 0, (2 / 7 : ℚ), (1 / 7 : ℚ)]]

def foldGlobal_4_698Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (8 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (4 / 281 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (1304 / 843 : ℚ)
  else if a.val = 0 ∧ b.val = 3 then (300 / 1967 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 281 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-58 / 843 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (-1040 / 5901 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (558 / 281 : ℚ)
  else if a.val = 2 ∧ b.val = 3 then (154 / 281 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (2052 / 13769 : ℚ)
  else 0

def foldGlobal_4_698Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 2⟩, ⟨0, 0, 1, 3⟩, ⟨0, 0, 2, 2⟩, ⟨0, 0, 3, 3⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_698_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_698Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_698Network foldGlobal_4_698Generator (-1 : ℚ)
    foldGlobal_4_698Multiplier foldGlobal_4_698Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_4_699Network : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .zero), (.xy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_4_699Generator : Fin 4 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)]]

def foldGlobal_4_699Multiplier (a b : Fin 4) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (24 / 275 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (8 / 55 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (8 / 275 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (4 / 275 : ℚ)
  else if a.val = 1 ∧ b.val = 3 then (42 / 275 : ℚ)
  else if a.val = 3 ∧ b.val = 3 then (-4 / 275 : ℚ)
  else 0

def foldGlobal_4_699Witnesses : Finset (QuarticWitness 4) :=
  {⟨0, 0, 1, 1⟩, ⟨0, 0, 2, 2⟩, ⟨1, 1, 1, 1⟩}

theorem foldGlobal_4_699_noCusp : ¬ AdmitsTransverseCusp foldGlobal_4_699Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_4_699Network foldGlobal_4_699Generator 1
    foldGlobal_4_699Multiplier foldGlobal_4_699Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
