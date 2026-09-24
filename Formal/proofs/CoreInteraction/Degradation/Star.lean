import proofs.DegradationControl.PerronExistence

/-!
Exact degradation-star elimination.  The internal solve witnesses are retained
as data; no matrix inverse or division by a matrix occurs in the trusted path.
-/

namespace CoreInteraction.Degradation

open DegradationControl

variable {I J : Type} [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]

structure StarData (I J : Type) where
  rootDiagonal : ℝ
  internal : I → Matrix J J ℝ
  toRoot : I → J → ℝ
  fromRoot : I → J → ℝ

def StarData.matrix (D : StarData I J) :
    Matrix (Unit ⊕ (I × J)) (Unit ⊕ (I × J)) ℝ
  | Sum.inl _, Sum.inl _ => D.rootDiagonal
  | Sum.inl _, Sum.inr ij => D.toRoot ij.1 ij.2
  | Sum.inr ij, Sum.inl _ => D.fromRoot ij.1 ij.2
  | Sum.inr ij, Sum.inr kl =>
      if ij.1 = kl.1 then D.internal ij.1 ij.2 kl.2 else 0

def StarData.vector (_D : StarData I J) (z : ℝ)
    (u : I → J → ℝ) : Unit ⊕ (I × J) → ℝ
  | Sum.inl _ => z
  | Sum.inr ij => u ij.1 ij.2

/-- The coordinate vector of the shared root. -/
def StarData.rootBasis (_D : StarData I J) : Unit ⊕ (I × J) → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => 0

def StarData.load (D : StarData I J) (u : I → J → ℝ) : ℝ :=
  ∑ i, ∑ j, D.toRoot i j * u i j

def StarData.schurLoad (D : StarData I J) (u : I → J → ℝ) : ℝ :=
  D.rootDiagonal + D.load u

def StarData.rootAction (D : StarData I J) (z : ℝ)
    (u : I → J → ℝ) : ℝ :=
  D.rootDiagonal * z + D.load u

def StarData.SolveWitness (D : StarData I J) (u : I → J → ℝ) : Prop :=
  ∀ i j, Matrix.mulVec (D.internal i) (u i) j = -D.fromRoot i j

def StarData.PositiveInternal (_D : StarData I J) (u : I → J → ℝ) : Prop :=
  ∀ i j, 0 < u i j

def StarData.PositiveRootCoupling (D : StarData I J) : Prop :=
  ∀ i j, 0 < D.fromRoot i j

omit [DecidableEq J] in
theorem StarData.mulVec_root (D : StarData I J) (z : ℝ)
    (u : I → J → ℝ) :
    Matrix.mulVec D.matrix (D.vector z u) (Sum.inl ()) = D.rootAction z u := by
  simp [Matrix.mulVec, dotProduct, StarData.matrix, StarData.vector, StarData.rootAction,
    StarData.load, Fintype.sum_prod_type]

omit [DecidableEq J] in
theorem StarData.mulVec_internal (D : StarData I J) (z : ℝ)
    (u : I → J → ℝ) (i : I) (j : J) :
    Matrix.mulVec D.matrix (D.vector z u) (Sum.inr (i, j)) =
      D.fromRoot i j * z + Matrix.mulVec (D.internal i) (u i) j := by
  simp [Matrix.mulVec, dotProduct, StarData.matrix, StarData.vector,
    Fintype.sum_prod_type]

omit [DecidableEq J] in
theorem StarData.internal_action_of_solve (D : StarData I J)
    (z : ℝ) (u : I → J → ℝ) (hu : D.SolveWitness u) (i : I) (j : J) :
    Matrix.mulVec D.matrix (D.vector z u) (Sum.inr (i, j)) =
      D.fromRoot i j * (z - 1) := by
  rw [D.mulVec_internal]
  rw [hu i j]
  ring

omit [DecidableEq J] in
/-- Exact block elimination identity.  The positive solve vector cancels every
internal row, leaving precisely the scalar Schur load at the shared root. -/
theorem StarData.mulVec_solveVector (D : StarData I J)
    (u : I → J → ℝ) (hu : D.SolveWitness u) :
    D.matrix.mulVec (D.vector 1 u) = D.schurLoad u • D.rootBasis := by
  funext v
  rcases v with _ | ⟨i, j⟩
  · simp [D.mulVec_root, StarData.rootAction, StarData.schurLoad,
      StarData.rootBasis]
  · rw [D.internal_action_of_solve 1 u hu i j]
    simp [StarData.rootBasis]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem StarData.vector_strictlyPositive (D : StarData I J)
    {z : ℝ} {u : I → J → ℝ} (hz : 0 < z) (hu : D.PositiveInternal u) :
    StrictlyPositive (D.vector z u) := by
  rintro (_ | ⟨i, j⟩)
  · simpa [StarData.vector] using hz
  · simpa [StarData.vector] using hu i j

theorem StarData.growthCertificate_of_ratio (D : StarData I J)
    (u : I → J → ℝ) (hu : D.SolveWitness u)
    (hupos : D.PositiveInternal u) (hc : D.PositiveRootCoupling)
    (z : ℝ) (hz : 1 < z) (hroot : 0 < D.rootAction z u) :
    GrowthCertificate D.matrix := by
  refine ⟨D.vector z u, D.vector_strictlyPositive (lt_trans zero_lt_one hz) hupos, ?_⟩
  rintro (_ | ⟨i, j⟩)
  · simpa [D.mulVec_root] using hroot
  · rw [D.internal_action_of_solve z u hu i j]
    exact mul_pos (hc i j) (sub_pos.mpr hz)

theorem StarData.criticalCertificate_of_schur_eq_zero (D : StarData I J)
    (u : I → J → ℝ) (hu : D.SolveWitness u)
    (hupos : D.PositiveInternal u) (hzero : D.schurLoad u = 0) :
    CriticalCertificate D.matrix := by
  refine ⟨D.vector 1 u, D.vector_strictlyPositive zero_lt_one hupos, ?_⟩
  funext v
  rcases v with _ | ⟨i, j⟩
  · simpa [D.mulVec_root, StarData.rootAction, StarData.schurLoad] using hzero
  · rw [D.internal_action_of_solve 1 u hu i j]
    simp

theorem StarData.extinctionCertificate_of_ratio (D : StarData I J)
    (u : I → J → ℝ) (hu : D.SolveWitness u)
    (hupos : D.PositiveInternal u) (hc : D.PositiveRootCoupling)
    (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) (hroot : D.rootAction z u < 0) :
    ExtinctionCertificate D.matrix := by
  refine ⟨D.vector z u, D.vector_strictlyPositive hz0 hupos, ?_⟩
  rintro (_ | ⟨i, j⟩)
  · simpa [D.mulVec_root] using hroot
  · rw [D.internal_action_of_solve z u hu i j]
    exact mul_neg_of_pos_of_neg (hc i j) (sub_neg.mpr hz1)

lemma exists_growth_ratio (m L : ℝ) (hk : 0 < m + L) :
    ∃ z, 1 < z ∧ 0 < m * z + L := by
  by_cases hm : 0 ≤ m
  · exact ⟨2, by norm_num, by nlinarith⟩
  · have hmneg : m < 0 := lt_of_not_ge hm
    let e := (m + L) / (-2 * m)
    have he : 0 < e := div_pos hk (by nlinarith)
    refine ⟨1 + e, by linarith, ?_⟩
    have hmne : m ≠ 0 := ne_of_lt hmneg
    dsimp [e]
    field_simp [hmne]
    nlinarith

lemma exists_extinction_ratio (m L : ℝ) (hk : m + L < 0) :
    ∃ z, 0 < z ∧ z < 1 ∧ m * z + L < 0 := by
  by_cases hm : 0 ≤ m
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    nlinarith
  · have hmneg : m < 0 := lt_of_not_ge hm
    let e := (m + L) / (2 * m)
    have he : 0 < e := div_pos_of_neg_of_neg hk (by nlinarith)
    by_cases hesmall : e ≤ 1 / 2
    · refine ⟨1 - e, by linarith, by linarith, ?_⟩
      have hmne : m ≠ 0 := ne_of_lt hmneg
      dsimp [e]
      field_simp [hmne]
      nlinarith
    · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      have helarge : 1 / 2 < e := lt_of_not_ge hesmall
      have hmne : m ≠ 0 := ne_of_lt hmneg
      have heq : e * (2 * m) = m + L := by
        dsimp [e]
        field_simp [hmne]
      nlinarith

/-- `CIC-DEG-STAR`: the exact Schur load, computed from solve witnesses,
selects a strict growth certificate, a positive nullvector, or a strict
extinction certificate for the full finite star. -/
theorem StarData.schurLoad_trichotomy (D : StarData I J)
    (u : I → J → ℝ) (hu : D.SolveWitness u)
    (hupos : D.PositiveInternal u) (hc : D.PositiveRootCoupling) :
    (0 < D.schurLoad u → GrowthCertificate D.matrix) ∧
    (D.schurLoad u = 0 → CriticalCertificate D.matrix) ∧
    (D.schurLoad u < 0 → ExtinctionCertificate D.matrix) := by
  constructor
  · intro hk
    obtain ⟨z, hz, hroot⟩ := exists_growth_ratio D.rootDiagonal (D.load u) hk
    exact D.growthCertificate_of_ratio u hu hupos hc z hz hroot
  constructor
  · exact D.criticalCertificate_of_schur_eq_zero u hu hupos
  · intro hk
    obtain ⟨z, hz0, hz1, hroot⟩ :=
      exists_extinction_ratio D.rootDiagonal (D.load u) hk
    exact D.extinctionCertificate_of_ratio u hu hupos hc z hz0 hz1 hroot

omit [DecidableEq J] in
/-- Pairing the exact Schur elimination identity with any left eigenvector
reduces the full matrix equation to one scalar equality. -/
theorem StarData.schurLoad_leftEigenvector_pairing (D : StarData I J)
    (u : I → J → ℝ) (hu : D.SolveWitness u)
    {lam : ℝ} {w : Unit ⊕ (I × J) → ℝ}
    (hwe : D.matrix.transpose.mulVec w = lam • w) :
    lam * dotProduct w (D.vector 1 u) =
      D.schurLoad u * w (Sum.inl ()) := by
  have hbil := Matrix.dotProduct_transpose_mulVec D.matrix (D.vector 1 u) w
  rw [hwe, D.mulVec_solveVector u hu] at hbil
  calc
    lam * dotProduct w (D.vector 1 u) =
        dotProduct (D.vector 1 u) (lam • w) := by
      simp [dotProduct_smul, dotProduct_comm, smul_eq_mul]
    _ = dotProduct w (D.schurLoad u • D.rootBasis) := hbil
    _ = D.schurLoad u * w (Sum.inl ()) := by
      simp [dotProduct, StarData.rootBasis, Fintype.sum_sum_type,
        smul_eq_mul, mul_comm]

/-- `CIC-DEG-STAR-EXACT`: under the standard irreducible-Metzler hypotheses,
the scalar Schur load has exactly the sign of the real spectral bound. -/
theorem StarData.schurLoad_spectralTrichotomy (D : StarData I J)
    (u : I → J → ℝ) (hu : D.SolveWitness u)
    (hupos : D.PositiveInternal u) (hc : D.PositiveRootCoupling)
    (hM : IsMetzler D.matrix)
    (hirr : HasIrreducibleNonnegativeShift D.matrix) :
    (0 < D.schurLoad u ↔ HasPositiveRealSpectralBound D.matrix) ∧
    (D.schurLoad u = 0 ↔ IsRealSpectralBound D.matrix 0) ∧
    (D.schurLoad u < 0 ↔ HasNegativeRealSpectralBound D.matrix) := by
  have hv : StrictlyPositive (D.vector 1 u) :=
    D.vector_strictlyPositive zero_lt_one hupos
  have hcert := D.schurLoad_trichotomy u hu hupos hc
  constructor
  · constructor
    · intro hk
      exact (irreducibleMetzler_positiveSpectralBound_iff_growthCertificate
        D.matrix hM hirr).2 (hcert.1 hk)
    · rintro ⟨lam, hlam, hs⟩
      obtain ⟨w, hw, hwe⟩ :=
        irreducibleMetzler_positiveLeftEigenvector_at_spectralBound
          D.matrix hM hirr hs
      have hpair := D.schurLoad_leftEigenvector_pairing u hu hwe
      have hwv : 0 < dotProduct w (D.vector 1 u) :=
        dotProduct_pos_of_strictlyPositive hw.1 hv
      have hwr : 0 < w (Sum.inl ()) := hw.1 _
      nlinarith
  constructor
  · constructor
    · intro hk
      exact (irreducibleMetzler_zeroSpectralBound_iff_criticalCertificate
        D.matrix hM hirr).2 (hcert.2.1 hk)
    · intro hs
      obtain ⟨w, hw, hwe⟩ :=
        irreducibleMetzler_positiveLeftEigenvector_at_spectralBound
          D.matrix hM hirr hs
      have hpair := D.schurLoad_leftEigenvector_pairing u hu hwe
      have hwr : 0 < w (Sum.inl ()) := hw.1 _
      nlinarith
  · constructor
    · intro hk
      exact (irreducibleMetzler_negativeSpectralBound_iff_extinctionCertificate
        D.matrix hM hirr).2 (hcert.2.2 hk)
    · rintro ⟨lam, hlam, hs⟩
      obtain ⟨w, hw, hwe⟩ :=
        irreducibleMetzler_positiveLeftEigenvector_at_spectralBound
          D.matrix hM hirr hs
      have hpair := D.schurLoad_leftEigenvector_pairing u hu hwe
      have hwv : 0 < dotProduct w (D.vector 1 u) :=
        dotProduct_pos_of_strictlyPositive hw.1 hv
      have hwr : 0 < w (Sum.inl ()) := hw.1 _
      nlinarith

/-- A source-faithful star packages an explicit unary-reaction list and exact
degradation vector whose generated Metzler matrix is the arrowhead matrix. -/
structure SourceStarData (I J : Type) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] where
  star : StarData I J
  reactions : List (DegradationControl.UnaryReaction (Unit ⊕ (I × J)))
  degradation : Unit ⊕ (I × J) → ℝ
  source_eq : DegradationControl.degradedMatrix
    (DegradationControl.reactionPart reactions) degradation = star.matrix

/-- Source-level adapter: once the finite source equality is checked, the
solve-witness Schur theorem applies to the literal reaction-derived matrix. -/
theorem SourceStarData.schurLoad_trichotomy (S : SourceStarData I J)
    (u : I → J → ℝ) (hu : S.star.SolveWitness u)
    (hupos : S.star.PositiveInternal u)
    (hc : S.star.PositiveRootCoupling) :
    (0 < S.star.schurLoad u →
      GrowthCertificate (DegradationControl.degradedMatrix
        (DegradationControl.reactionPart S.reactions) S.degradation)) ∧
    (S.star.schurLoad u = 0 →
      CriticalCertificate (DegradationControl.degradedMatrix
        (DegradationControl.reactionPart S.reactions) S.degradation)) ∧
    (S.star.schurLoad u < 0 →
      ExtinctionCertificate (DegradationControl.degradedMatrix
        (DegradationControl.reactionPart S.reactions) S.degradation)) := by
  rw [S.source_eq]
  exact S.star.schurLoad_trichotomy u hu hupos hc

/-- Source-faithful exact spectral theorem.  Nonnegative unary reactions make
the literal source matrix Metzler, while source irreducibility supplies the
positive left Perron vector used by the Schur pairing argument. -/
theorem SourceStarData.schurLoad_spectralTrichotomy (S : SourceStarData I J)
    (u : I → J → ℝ) (hu : S.star.SolveWitness u)
    (hupos : S.star.PositiveInternal u)
    (hc : S.star.PositiveRootCoupling)
    (hrs : ∀ r ∈ S.reactions, DegradationControl.NonnegativeReaction r)
    (hsource : DegradationControl.SourceIrreducible S.reactions) :
    (0 < S.star.schurLoad u ↔
      HasPositiveRealSpectralBound (DegradationControl.degradedMatrix
        (DegradationControl.reactionPart S.reactions) S.degradation)) ∧
    (S.star.schurLoad u = 0 ↔
      IsRealSpectralBound (DegradationControl.degradedMatrix
        (DegradationControl.reactionPart S.reactions) S.degradation) 0) ∧
    (S.star.schurLoad u < 0 ↔
      HasNegativeRealSpectralBound (DegradationControl.degradedMatrix
        (DegradationControl.reactionPart S.reactions) S.degradation)) := by
  have hA : IsMetzler (DegradationControl.reactionPart S.reactions) := by
    intro i j hij
    exact DegradationControl.reactionPart_offDiag_nonneg S.reactions hrs hij
  have hM : IsMetzler (DegradationControl.degradedMatrix
      (DegradationControl.reactionPart S.reactions) S.degradation) :=
    DegradationControl.degradedMatrix_isMetzler hA S.degradation
  have hirr := DegradationControl.sourceIrreducible_hasIrreducibleNonnegativeShift
    S.reactions S.degradation hrs hsource
  rw [S.source_eq] at hM hirr ⊢
  exact S.star.schurLoad_spectralTrichotomy u hu hupos hc hM hirr

end CoreInteraction.Degradation
