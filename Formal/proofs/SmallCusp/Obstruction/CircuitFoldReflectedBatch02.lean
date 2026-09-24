import proofs.SmallCusp.Obstruction.RationalCircuitFoldChecker

open scoped BigOperators

namespace SmallCusp


def foldGlobal_3_100Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_100Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_100Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (1 / 15 : ℚ)
  else 0

def foldGlobal_3_100Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_100_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_100Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_100Network foldGlobal_3_100Generator 1
    foldGlobal_3_100Multiplier foldGlobal_3_100Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_101Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_101Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_101Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 5 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (4 / 15 : ℚ)
  else 0

def foldGlobal_3_101Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_101_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_101Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_101Network foldGlobal_3_101Generator 1
    foldGlobal_3_101Multiplier foldGlobal_3_101Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_102Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_102Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_102Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (4 / 15 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2 / 5 : ℚ)
  else 0

def foldGlobal_3_102Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_102_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_102Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_102Network foldGlobal_3_102Generator 1
    foldGlobal_3_102Multiplier foldGlobal_3_102Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_103Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_103Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0]]

def foldGlobal_3_103Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 4 : ℚ)
  else 0

def foldGlobal_3_103Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_103_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_103Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_103Network foldGlobal_3_103Generator 1
    foldGlobal_3_103Multiplier foldGlobal_3_103Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_104Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_104Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_104Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 2 ∧ b.val = 2 then (1 / 9 : ℚ)
  else 0

def foldGlobal_3_104Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 2, 2, 2⟩}

theorem foldGlobal_3_104_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_104Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_104Network foldGlobal_3_104Generator 1
    foldGlobal_3_104Multiplier foldGlobal_3_104Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_105Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_105Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_105Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 4 : ℚ)
  else 0

def foldGlobal_3_105Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_105_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_105Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_105Network foldGlobal_3_105Generator 1
    foldGlobal_3_105Multiplier foldGlobal_3_105Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_106Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_106Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 9 : ℚ), (4 / 9 : ℚ), (1 / 3 : ℚ), 0],
  ![0, 0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ)]]

def foldGlobal_3_106Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-128 / 81 : ℚ)
  else 0

def foldGlobal_3_106Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 2⟩}

theorem foldGlobal_3_106_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_106Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_106Network foldGlobal_3_106Generator 1
    foldGlobal_3_106Multiplier foldGlobal_3_106Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_107Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .zero), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_107Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_107Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 9 : ℚ)
  else 0

def foldGlobal_3_107Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_107_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_107Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_107Network foldGlobal_3_107Generator 1
    foldGlobal_3_107Multiplier foldGlobal_3_107Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_108Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_108Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_108Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (1 / 9 : ℚ)
  else 0

def foldGlobal_3_108Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_108_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_108Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_108Network foldGlobal_3_108Generator 1
    foldGlobal_3_108Multiplier foldGlobal_3_108Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_109Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_109Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_109Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (4 / 39 : ℚ)
  else 0

def foldGlobal_3_109Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_109_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_109Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_109Network foldGlobal_3_109Generator 1
    foldGlobal_3_109Multiplier foldGlobal_3_109Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_110Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .x), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_110Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_110Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 43 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 129 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8 / 129 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 129 : ℚ)
  else 0

def foldGlobal_3_110Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_110_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_110Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_110Network foldGlobal_3_110Generator 1
    foldGlobal_3_110Multiplier foldGlobal_3_110Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_111Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .x), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_111Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_111Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-16 / 81 : ℚ)
  else 0

def foldGlobal_3_111Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_111_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_111Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_111Network foldGlobal_3_111Generator 1
    foldGlobal_3_111Multiplier foldGlobal_3_111Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_112Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xx), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_112Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_112Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 43 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 129 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-8 / 129 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 129 : ℚ)
  else 0

def foldGlobal_3_112Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_112_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_112Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_112Network foldGlobal_3_112Generator 1
    foldGlobal_3_112Multiplier foldGlobal_3_112Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_113Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xx), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_113Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 2 : ℚ), (1 / 6 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_113Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 27 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-16 / 81 : ℚ)
  else 0

def foldGlobal_3_113Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_113_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_113Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_113Network foldGlobal_3_113Generator 1
    foldGlobal_3_113Multiplier foldGlobal_3_113Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_114Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_114Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_114Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-2 / 37 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1 / 148 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-2 / 37 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 148 : ℚ)
  else 0

def foldGlobal_3_114Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_114_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_114Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_114Network foldGlobal_3_114Generator 1
    foldGlobal_3_114Multiplier foldGlobal_3_114Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_115Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .xy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_115Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 4 : ℚ), (1 / 2 : ℚ), (1 / 4 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_115Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 9 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 9 : ℚ)
  else 0

def foldGlobal_3_115Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_115_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_115Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_115Network foldGlobal_3_115Generator 1
    foldGlobal_3_115Multiplier foldGlobal_3_115Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_116Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .yy), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_116Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_116Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-1 / 89 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 89 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 89 : ℚ)
  else 0

def foldGlobal_3_116Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_116_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_116Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_116Network foldGlobal_3_116Generator 1
    foldGlobal_3_116Multiplier foldGlobal_3_116Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_117Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.y, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_117Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_117Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-1 / 72 : ℚ)
  else 0

def foldGlobal_3_117Witnesses : Finset (QuarticWitness 3) :=
  {⟨1, 1, 1, 1⟩}

theorem foldGlobal_3_117_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_117Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_117Network foldGlobal_3_117Generator 1
    foldGlobal_3_117Multiplier foldGlobal_3_117Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_118Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .xx), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_118Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_118Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-8 / 113 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-4 / 113 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1 / 113 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 113 : ℚ)
  else 0

def foldGlobal_3_118Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_118_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_118Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_118Network foldGlobal_3_118Generator 1
    foldGlobal_3_118Multiplier foldGlobal_3_118Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_119Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .xx), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_119Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_119Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 89 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 89 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 89 : ℚ)
  else 0

def foldGlobal_3_119Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_119_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_119Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_119Network foldGlobal_3_119Generator 1
    foldGlobal_3_119Multiplier foldGlobal_3_119Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_120Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.yy, .x), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_120Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)]]

def foldGlobal_3_120Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 6 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 12 : ℚ)
  else 0

def foldGlobal_3_120Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_120_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_120Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_120Network foldGlobal_3_120Generator 1
    foldGlobal_3_120Multiplier foldGlobal_3_120Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_121Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.yy, .xx), (.yy, .xy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_121Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), (1 / 2 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)]]

def foldGlobal_3_121Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 88 : ℚ)
  else 0

def foldGlobal_3_121Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_121_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_121Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_121Network foldGlobal_3_121Generator 1
    foldGlobal_3_121Multiplier foldGlobal_3_121Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_122Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .x), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_122Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_122Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1562 / 8739 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-5792 / 24275 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-2048 / 14565 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-328 / 971 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-432 / 24275 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (432 / 24275 : ℚ)
  else 0

def foldGlobal_3_122Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_122_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_122Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_122Network foldGlobal_3_122Generator 1
    foldGlobal_3_122Multiplier foldGlobal_3_122Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_123Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .xx), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_123Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (4 / 9 : ℚ), (2 / 9 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_123Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-562 / 1377 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-1448 / 5805 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-136852 / 177633 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-16 / 6579 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (16 / 6579 : ℚ)
  else 0

def foldGlobal_3_123Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_123_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_123Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_123Network foldGlobal_3_123Generator 1
    foldGlobal_3_123Multiplier foldGlobal_3_123Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_124Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_124Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_124Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-3232 / 16947 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-476 / 2421 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (-4132 / 28245 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-5332 / 16947 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-32 / 1883 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (32 / 1883 : ℚ)
  else 0

def foldGlobal_3_124Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_124_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_124Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_124Network foldGlobal_3_124Generator 1
    foldGlobal_3_124Multiplier foldGlobal_3_124Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_125Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_125Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_125Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (9 / 20 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (3 / 10 : ℚ)
  else 0

def foldGlobal_3_125Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_125_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_125Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_125Network foldGlobal_3_125Generator 1
    foldGlobal_3_125Multiplier foldGlobal_3_125Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_126Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_126Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), (1 / 6 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, (1 / 3 : ℚ), (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_126Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (3 / 10 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (9 / 20 : ℚ)
  else 0

def foldGlobal_3_126Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_126_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_126Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_126Network foldGlobal_3_126Generator 1
    foldGlobal_3_126Multiplier foldGlobal_3_126Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_127Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_127Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0]]

def foldGlobal_3_127Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 44 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (1 / 44 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-1 / 44 : ℚ)
  else 0

def foldGlobal_3_127Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_127_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_127Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_127Network foldGlobal_3_127Generator 1
    foldGlobal_3_127Multiplier foldGlobal_3_127Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_128Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_128Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 4 : ℚ), (1 / 4 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_128Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (1 / 62 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 62 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 62 : ℚ)
  else 0

def foldGlobal_3_128Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 2, 2⟩}

theorem foldGlobal_3_128_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_128Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_128Network foldGlobal_3_128Generator 1
    foldGlobal_3_128Multiplier foldGlobal_3_128Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_129Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_129Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ), 0],
  ![0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ), (1 / 2 : ℚ)],
  ![0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_129Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 1 then (-1 / 4 : ℚ)
  else 0

def foldGlobal_3_129Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_129_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_129Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_129Network foldGlobal_3_129Generator 1
    foldGlobal_3_129Multiplier foldGlobal_3_129Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_130Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_130Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, 0, (2 / 3 : ℚ), 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), 0, (2 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_130Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 1 ∧ b.val = 1 then (-982 / 3447 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-344 / 1915 : ℚ)
  else 0

def foldGlobal_3_130Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 1, 1, 1⟩}

theorem foldGlobal_3_130_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_130Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_130Network foldGlobal_3_130Generator 1
    foldGlobal_3_130Multiplier foldGlobal_3_130Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_131Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.xy, .xx), (.yy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_131Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0]]

def foldGlobal_3_131Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-3621 / 4732 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (3747 / 23660 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1219 / 3549 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-1294 / 5915 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (8 / 1183 : ℚ)
  else 0

def foldGlobal_3_131Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_131_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_131Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_131Network foldGlobal_3_131Generator 1
    foldGlobal_3_131Multiplier foldGlobal_3_131Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_132Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.xy, .xx), (.yy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_132Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (2 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_132Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1219 / 3549 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1294 / 5915 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (8 / 1183 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-3621 / 4732 : ℚ)
  else 0

def foldGlobal_3_132Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_132_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_132Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_132Network foldGlobal_3_132Generator 1
    foldGlobal_3_132Multiplier foldGlobal_3_132Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_133Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_133Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_3_133Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 : ℚ)
  else 0

def foldGlobal_3_133Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_133_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_133Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_133Network foldGlobal_3_133Generator 1
    foldGlobal_3_133Multiplier foldGlobal_3_133Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_134Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .y), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_134Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, 0, (1 / 5 : ℚ), (1 / 5 : ℚ)]]

def foldGlobal_3_134Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-1 / 8 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (1 / 8 : ℚ)
  else 0

def foldGlobal_3_134Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_134_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_134Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_134Network foldGlobal_3_134Generator 1
    foldGlobal_3_134Multiplier foldGlobal_3_134Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_135Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xx, .xy), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_135Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), 0, (2 / 5 : ℚ)]]

def foldGlobal_3_135Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-256 / 261 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-256 / 261 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-256 / 261 : ℚ)
  else 0

def foldGlobal_3_135Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_135_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_135Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_135Network foldGlobal_3_135Generator 1
    foldGlobal_3_135Multiplier foldGlobal_3_135Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_136Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_136Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_136Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (-4 / 39 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 39 : ℚ)
  else 0

def foldGlobal_3_136Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_136_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_136Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_136Network foldGlobal_3_136Generator 1
    foldGlobal_3_136Multiplier foldGlobal_3_136Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_137Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_137Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![0, 0, 0, (2 / 3 : ℚ), (1 / 3 : ℚ)],
  ![0, (2 / 5 : ℚ), (1 / 5 : ℚ), (2 / 5 : ℚ), 0]]

def foldGlobal_3_137Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (32 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (2344 / 475 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (824 / 475 : ℚ)
  else 0

def foldGlobal_3_137Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_137_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_137Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_137Network foldGlobal_3_137Generator (-1 : ℚ)
    foldGlobal_3_137Multiplier foldGlobal_3_137Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_138Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .zero), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_138Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(2 / 3 : ℚ), 0, (1 / 3 : ℚ), 0, 0],
  ![0, (2 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_138Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (32 / 9 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (-1 / 36 : ℚ)
  else if a.val = 0 ∧ b.val = 2 then (49 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 36 : ℚ)
  else if a.val = 1 ∧ b.val = 2 then (-5 / 36 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 36 : ℚ)
  else 0

def foldGlobal_3_138Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 1, 1⟩}

theorem foldGlobal_3_138_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_138Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_138Network foldGlobal_3_138Generator (-1 : ℚ)
    foldGlobal_3_138Multiplier foldGlobal_3_138Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_139Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_139Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), 0, (1 / 5 : ℚ)],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_139Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4 / 39 : ℚ)
  else 0

def foldGlobal_3_139Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_139_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_139Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_139Network foldGlobal_3_139Generator 1
    foldGlobal_3_139Multiplier foldGlobal_3_139Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_140Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.y, .xx), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_140Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![0, 0, (1 / 2 : ℚ), (1 / 2 : ℚ), 0],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0]]

def foldGlobal_3_140Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-9 / 8 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-3 / 4 : ℚ)
  else 0

def foldGlobal_3_140Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_140_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_140Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_140Network foldGlobal_3_140Generator 1
    foldGlobal_3_140Multiplier foldGlobal_3_140Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_141Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.y, .xy), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_141Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 3 : ℚ), (1 / 3 : ℚ), (1 / 3 : ℚ), 0]]

def foldGlobal_3_141Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (1 / 4 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-9 / 8 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-9 / 8 : ℚ)
  else 0

def foldGlobal_3_141Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_141_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_141Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_141Network foldGlobal_3_141Generator 1
    foldGlobal_3_141Multiplier foldGlobal_3_141Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_142Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .x), (.y, .yy), (.xx, .y), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_142Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![0, (1 / 2 : ℚ), (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_142Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 14 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-9 / 7 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-27 / 28 : ℚ)
  else 0

def foldGlobal_3_142Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 2⟩}

theorem foldGlobal_3_142_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_142Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_142Network foldGlobal_3_142Generator 1
    foldGlobal_3_142Multiplier foldGlobal_3_142Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_143Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_143Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ), 0]]

def foldGlobal_3_143Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (27 / 40 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (9 / 20 : ℚ)
  else 0

def foldGlobal_3_143Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_143_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_143Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_143Network foldGlobal_3_143Generator 1
    foldGlobal_3_143Multiplier foldGlobal_3_143Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_144Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_144Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(3 / 5 : ℚ), 0, (1 / 5 : ℚ), (1 / 5 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_144Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (9 / 20 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (27 / 40 : ℚ)
  else 0

def foldGlobal_3_144Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_144_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_144Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_144Network foldGlobal_3_144Generator 1
    foldGlobal_3_144Multiplier foldGlobal_3_144Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_145Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .x), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_145Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_145Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (3 / 10 : ℚ)
  else if a.val = 0 ∧ b.val = 1 then (3 / 10 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (-3 / 10 : ℚ)
  else 0

def foldGlobal_3_145Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_145_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_145Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_145Network foldGlobal_3_145Generator 1
    foldGlobal_3_145Multiplier foldGlobal_3_145Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_146Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .x), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_146Generator : Fin 3 → Fin 5 → ℚ := ![
  ![0, (1 / 2 : ℚ), 0, (1 / 2 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![(1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ), (1 / 3 : ℚ)]]

def foldGlobal_3_146Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 2 then (1 / 7 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (-1 / 7 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (1 / 7 : ℚ)
  else 0

def foldGlobal_3_146Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 2, 2⟩}

theorem foldGlobal_3_146_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_146Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_146Network foldGlobal_3_146Generator 1
    foldGlobal_3_146Multiplier foldGlobal_3_146Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_147Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xx, .yy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_147Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, 0, (1 / 3 : ℚ)],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), 0, (1 / 4 : ℚ)],
  ![(4 / 7 : ℚ), 0, 0, (1 / 7 : ℚ), (2 / 7 : ℚ)]]

def foldGlobal_3_147Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4 / 39 : ℚ)
  else 0

def foldGlobal_3_147Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_147_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_147Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_147Network foldGlobal_3_147Generator 1
    foldGlobal_3_147Multiplier foldGlobal_3_147Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_148Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .zero), (.xy, .y)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_148Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 2 : ℚ), 0, 0, 0, (1 / 2 : ℚ)],
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0]]

def foldGlobal_3_148Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (2 / 3 : ℚ)
  else if a.val = 1 ∧ b.val = 1 then (4 / 9 : ℚ)
  else 0

def foldGlobal_3_148Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 1⟩}

theorem foldGlobal_3_148_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_148Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_148Network foldGlobal_3_148Generator 1
    foldGlobal_3_148Multiplier foldGlobal_3_148Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def foldGlobal_3_149Network : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .zero), (.xy, .yy)]
  noSelf := by decide
  injective := by decide

def foldGlobal_3_149Generator : Fin 3 → Fin 5 → ℚ := ![
  ![(1 / 3 : ℚ), (1 / 3 : ℚ), 0, (1 / 3 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, (1 / 4 : ℚ), (1 / 4 : ℚ), 0],
  ![(1 / 2 : ℚ), 0, 0, (1 / 4 : ℚ), (1 / 4 : ℚ)]]

def foldGlobal_3_149Multiplier (a b : Fin 3) : ℚ :=
  if a.val = 0 ∧ b.val = 0 then (4 / 9 : ℚ)
  else if a.val = 2 ∧ b.val = 2 then (2 / 3 : ℚ)
  else 0

def foldGlobal_3_149Witnesses : Finset (QuarticWitness 3) :=
  {⟨0, 0, 0, 0⟩}

theorem foldGlobal_3_149_noCusp : ¬ AdmitsTransverseCusp foldGlobal_3_149Network.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    foldGlobal_3_149Network foldGlobal_3_149Generator 1
    foldGlobal_3_149Multiplier foldGlobal_3_149Witnesses
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


end SmallCusp
