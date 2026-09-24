import proofs.SmallCusp.Equivalence.CodedSimple

namespace SmallCusp

inductive CuspOutcome where
  | cusp | determinant | fold | cubic
  deriving DecidableEq, Repr

/-- The 30 directed non-self bimolecular reactions, in the exact order used
by the finite source generator. -/
def bimolReactionCatalogue : Fin 30 → BimolReactionCode := ![
  (.zero,.x), (.zero,.y), (.zero,.xx), (.zero,.xy), (.zero,.yy),
  (.x,.zero), (.x,.y), (.x,.xx), (.x,.xy), (.x,.yy),
  (.y,.zero), (.y,.x), (.y,.xx), (.y,.xy), (.y,.yy),
  (.xx,.zero), (.xx,.x), (.xx,.y), (.xx,.xy), (.xx,.yy),
  (.xy,.zero), (.xy,.x), (.xy,.y), (.xy,.xx), (.xy,.yy),
  (.yy,.zero), (.yy,.x), (.yy,.y), (.yy,.xx), (.yy,.xy)]

theorem bimolReactionCatalogue_noSelf (r : Fin 30) :
    (bimolReactionCatalogue r).1 ≠ (bimolReactionCatalogue r).2 := by
  fin_cases r <;> decide

theorem bimolReactionCatalogue_injective :
    Function.Injective bimolReactionCatalogue := by
  intro r s h
  fin_cases r <;> fin_cases s <;>
    simp_all [bimolReactionCatalogue]

/-- Compact proof-carrying indices for two literal five-generator sources and
the explicit bijection between their simply-equivalent rays. -/
structure SourceCoverageRecord where
  sourceIndices : Fin 5 → Fin 30
  targetIndices : Fin 5 → Fin 30
  matching : Fin 5 → Fin 5
  outcome : CuspOutcome
  targetIndex : ℕ
  swapTarget : Bool

def SourceCoverageRecord.sourceReaction (R : SourceCoverageRecord) (r : Fin 5) :
    BimolReactionCode := bimolReactionCatalogue (R.sourceIndices r)

def SourceCoverageRecord.orientedTargetReaction
    (R : SourceCoverageRecord) (r : Fin 5) : BimolReactionCode :=
  if R.swapTarget then
    swapBimolReaction (bimolReactionCatalogue (R.targetIndices r))
  else bimolReactionCatalogue (R.targetIndices r)

def SourceCoverageRecord.sourceStoich
    (R : SourceCoverageRecord) (i : Species) (r : Fin 5) : ℤ :=
  ((R.sourceReaction r).2.decode i : ℤ) -
    ((R.sourceReaction r).1.decode i : ℤ)

def SourceCoverageRecord.orientedTargetStoich
    (R : SourceCoverageRecord) (i : Species) (r : Fin 5) : ℤ :=
  ((R.orientedTargetReaction r).2.decode i : ℤ) -
    ((R.orientedTargetReaction r).1.decode i : ℤ)

def SourceCoverageRecord.directRayScale
    (R : SourceCoverageRecord) (r s : Fin 5) : ℚ :=
  if R.sourceStoich 0 r ≠ 0 then
    (R.orientedTargetStoich 0 s : ℚ) / (R.sourceStoich 0 r : ℚ)
  else
    (R.orientedTargetStoich 1 s : ℚ) / (R.sourceStoich 1 r : ℚ)

def defaultCodedBimolNetwork : CodedBimolNetwork where
  reaction := ![(.zero,.x), (.zero,.y), (.zero,.xx), (.zero,.xy), (.zero,.yy)]
  noSelf := by decide
  injective := by decide

def SourceCoverageRecord.sourceNetwork (R : SourceCoverageRecord) :
    CodedBimolNetwork :=
  if h : Function.Injective R.sourceIndices then
    { reaction := fun r => bimolReactionCatalogue (R.sourceIndices r)
      noSelf := fun r => bimolReactionCatalogue_noSelf (R.sourceIndices r)
      injective := fun _ _ he => h (bimolReactionCatalogue_injective he) }
  else defaultCodedBimolNetwork

def SourceCoverageRecord.targetNetwork (R : SourceCoverageRecord) :
    CodedBimolNetwork :=
  if h : Function.Injective R.targetIndices then
    { reaction := fun r => bimolReactionCatalogue (R.targetIndices r)
      noSelf := fun r => bimolReactionCatalogue_noSelf (R.targetIndices r)
      injective := fun _ _ he => h (bimolReactionCatalogue_injective he) }
  else defaultCodedBimolNetwork

def SourceCoverageRecord.orientedTargetCode (R : SourceCoverageRecord) :
    CodedBimolNetwork :=
  if R.swapTarget then swapCodedNetwork R.targetNetwork else R.targetNetwork

theorem SourceCoverageRecord.sourceNetwork_reaction
    (R : SourceCoverageRecord) (h : Function.Injective R.sourceIndices) (r : Fin 5) :
    R.sourceNetwork.reaction r = R.sourceReaction r := by
  simp [SourceCoverageRecord.sourceNetwork, SourceCoverageRecord.sourceReaction, h]

theorem SourceCoverageRecord.orientedTargetCode_reaction
    (R : SourceCoverageRecord) (h : Function.Injective R.targetIndices) (r : Fin 5) :
    R.orientedTargetCode.reaction r = R.orientedTargetReaction r := by
  by_cases hs : R.swapTarget
  · simp [SourceCoverageRecord.orientedTargetCode,
      SourceCoverageRecord.targetNetwork,
      SourceCoverageRecord.orientedTargetReaction, h, hs, swapCodedNetwork]
  · simp [SourceCoverageRecord.orientedTargetCode,
      SourceCoverageRecord.targetNetwork,
      SourceCoverageRecord.orientedTargetReaction, h, hs]

def SourceCoverageRecord.Docked (R : SourceCoverageRecord) : Prop :=
  Function.Injective R.sourceIndices ∧
    Function.Injective R.targetIndices ∧
    Function.Bijective R.matching ∧
    (∀ r, (R.orientedTargetReaction (R.matching r)).1 =
      (R.sourceReaction r).1) ∧
    (∀ r, 0 < R.directRayScale r (R.matching r)) ∧
    (∀ i r, (R.orientedTargetStoich i (R.matching r) : ℚ) =
      R.directRayScale r (R.matching r) * (R.sourceStoich i r : ℚ))

instance sourceCoverageRecord_docked_decidable (R : SourceCoverageRecord) :
    Decidable R.Docked := by
  unfold SourceCoverageRecord.Docked
  infer_instance

/-- Division-free positive-ray test.  This is equivalent to the rational
scaling clauses needed by `Docked`, but its closed instances evaluate using
only small integer products and equalities. -/
def SourceCoverageRecord.PositiveAlignedFast
    (R : SourceCoverageRecord) (r s : Fin 5) : Prop :=
  if R.sourceStoich 0 r ≠ 0 then
    0 < R.orientedTargetStoich 0 s * R.sourceStoich 0 r ∧
      R.orientedTargetStoich 1 s * R.sourceStoich 0 r =
        R.orientedTargetStoich 0 s * R.sourceStoich 1 r
  else
    R.orientedTargetStoich 0 s = 0 ∧
      0 < R.orientedTargetStoich 1 s * R.sourceStoich 1 r

def SourceCoverageRecord.DockedFast (R : SourceCoverageRecord) : Prop :=
  Function.Injective R.sourceIndices ∧
    Function.Injective R.targetIndices ∧
    Function.Bijective R.matching ∧
    (∀ r, (R.orientedTargetReaction (R.matching r)).1 =
      (R.sourceReaction r).1) ∧
    (∀ r, R.PositiveAlignedFast r (R.matching r))

instance sourceCoverageRecord_dockedFast_decidable (R : SourceCoverageRecord) :
    Decidable R.DockedFast := by
  unfold SourceCoverageRecord.DockedFast SourceCoverageRecord.PositiveAlignedFast
  infer_instance

theorem SourceCoverageRecord.positiveAlignedFast_implies_scale
    (R : SourceCoverageRecord) (r s : Fin 5)
    (h : R.PositiveAlignedFast r s) :
    0 < R.directRayScale r s ∧
      ∀ i, (R.orientedTargetStoich i s : ℚ) =
        R.directRayScale r s * (R.sourceStoich i r : ℚ) := by
  unfold SourceCoverageRecord.PositiveAlignedFast at h
  by_cases hs0 : R.sourceStoich 0 r ≠ 0
  · rw [if_pos hs0] at h
    rcases h with ⟨hpos, hcross⟩
    have hs0q : (R.sourceStoich 0 r : ℚ) ≠ 0 := by exact_mod_cast hs0
    have hposq : (0 : ℚ) <
        (R.orientedTargetStoich 0 s : ℚ) * (R.sourceStoich 0 r : ℚ) := by
      exact_mod_cast hpos
    have hscale : R.directRayScale r s =
        (R.orientedTargetStoich 0 s : ℚ) / (R.sourceStoich 0 r : ℚ) := by
      rw [SourceCoverageRecord.directRayScale, if_pos hs0]
    constructor
    · rw [hscale]
      exact (div_pos_iff.mpr (mul_pos_iff.mp hposq))
    · intro i
      fin_cases i
      · simp only [Fin.zero_eta]
        rw [hscale]
        field_simp [hs0q]
      · simp only [Fin.mk_one]
        rw [hscale]
        field_simp [hs0q]
        exact_mod_cast hcross
  · rw [if_neg hs0] at h
    rcases h with ⟨ht0, hpos⟩
    have hs1 : R.sourceStoich 1 r ≠ 0 := by
      intro hs1
      rw [hs1, mul_zero] at hpos
      omega
    have hs1q : (R.sourceStoich 1 r : ℚ) ≠ 0 := by exact_mod_cast hs1
    have hposq : (0 : ℚ) <
        (R.orientedTargetStoich 1 s : ℚ) * (R.sourceStoich 1 r : ℚ) := by
      exact_mod_cast hpos
    have hscale : R.directRayScale r s =
        (R.orientedTargetStoich 1 s : ℚ) / (R.sourceStoich 1 r : ℚ) := by
      rw [SourceCoverageRecord.directRayScale, if_neg hs0]
    constructor
    · rw [hscale]
      exact (div_pos_iff.mpr (mul_pos_iff.mp hposq))
    · intro i
      fin_cases i
      · simp only [Fin.zero_eta]
        rw [hscale]
        rw [show (R.orientedTargetStoich 0 s : ℚ) = 0 by exact_mod_cast ht0]
        rw [show (R.sourceStoich 0 r : ℚ) = 0 by exact_mod_cast not_ne_iff.mp hs0]
        ring
      · simp only [Fin.mk_one]
        rw [hscale]
        field_simp [hs1q]

theorem SourceCoverageRecord.dockedFast_implies_docked
    (R : SourceCoverageRecord) (hR : R.DockedFast) : R.Docked := by
  rcases hR with ⟨hsource, htarget, hmatching, hreact, haligned⟩
  refine ⟨hsource, htarget, hmatching, hreact, ?_, ?_⟩
  · intro r
    exact (R.positiveAlignedFast_implies_scale r (R.matching r)
      (haligned r)).1
  · intro i r
    exact (R.positiveAlignedFast_implies_scale r (R.matching r)
      (haligned r)).2 i

theorem SourceCoverageRecord.docked_implies_codedSimplyEquivalent
    (R : SourceCoverageRecord) (hR : R.Docked) :
    CodedSimplyEquivalent R.sourceNetwork R.orientedTargetCode := by
  rcases hR with ⟨hsource, htarget, hmatching, hreact, hpos, hstoich⟩
  let e : Equiv.Perm (Fin 5) := Equiv.ofBijective R.matching hmatching
  refine ⟨e, ?_, ?_, ?_⟩
  · intro r
    simpa [e, R.sourceNetwork_reaction hsource,
      R.orientedTargetCode_reaction htarget] using hreact r
  · intro r
    simpa [e, codedRayScale, codedStoich,
      R.sourceNetwork_reaction hsource,
      R.orientedTargetCode_reaction htarget,
      SourceCoverageRecord.sourceStoich,
      SourceCoverageRecord.orientedTargetStoich,
      SourceCoverageRecord.directRayScale, hsource, htarget] using hpos r
  · intro i r
    simpa [e, codedRayScale, codedStoich,
      R.sourceNetwork_reaction hsource,
      R.orientedTargetCode_reaction htarget,
      SourceCoverageRecord.sourceStoich,
      SourceCoverageRecord.orientedTargetStoich,
      SourceCoverageRecord.directRayScale, hsource, htarget] using hstoich i r

end SmallCusp
