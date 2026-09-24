import proofs.OptimalAffinityRealizability.LocalBranch

namespace OptimalAffinityRealizability

noncomputable section

def quadraticExponent (a b s : ℝ) : ℝ := s * a + (s ^ 2 / 2) * b

def expQuadraticDerivative (c a b s : ℝ) : ℝ :=
  c * Real.exp (quadraticExponent a b s) * (a + s * b)

theorem expQuadratic_hasDerivAt (c a b s : ℝ) :
    HasDerivAt (fun t => c * Real.exp (quadraticExponent a b t))
      (expQuadraticDerivative c a b s) s := by
  have hq : HasDerivAt (quadraticExponent a b) (a + s * b) s := by
    unfold quadraticExponent
    convert ((hasDerivAt_id s).mul_const a).add
      (((hasDerivAt_pow 2 s).div_const 2).mul_const b) using 1
    all_goals ring
  have he := (Real.hasDerivAt_exp (quadraticExponent a b s)).comp s hq
  convert he.const_mul c using 1
  all_goals simp [expQuadraticDerivative]
  all_goals ring

theorem expQuadraticDerivative_hasDerivAt_zero (c a b : ℝ) :
    HasDerivAt (expQuadraticDerivative c a b) (c * (a ^ 2 + b)) 0 := by
  have hq : HasDerivAt (quadraticExponent a b) a 0 := by
    unfold quadraticExponent
    convert ((hasDerivAt_id (x := (0 : ℝ))).mul_const a).add
      (((hasDerivAt_pow 2 (0 : ℝ)).div_const 2).mul_const b) using 1
    all_goals ring
  have he := (Real.hasDerivAt_exp (quadraticExponent a b 0)).comp 0 hq
  have hl : HasDerivAt (fun s : ℝ => a + s * b) b 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).mul_const b |>.const_add a
  have hprod := he.mul hl
  unfold expQuadraticDerivative
  let d := c * (Real.exp (quadraticExponent a b 0) * a * (a + 0 * b) +
    (Real.exp ∘ quadraticExponent a b) 0 * b)
  have hc : HasDerivAt
      (fun s => c * Real.exp (quadraticExponent a b s) * (a + s * b)) d 0 := by
    apply (hprod.const_mul c).congr_of_eventuallyEq
    filter_upwards [] with s
    simp only [Pi.mul_apply, Function.comp_apply]
    ring
  have hd : d = c * (a ^ 2 + b) := by
    dsimp [d]
    simp [quadraticExponent]
    exact Or.inl (pow_two a).symm
  exact hc.congr_deriv hd

def secondOrderLogPath {n : ℕ} (u v : Fin n → ℝ) (s : ℝ) : Fin n → ℝ :=
  s • u + (s ^ 2 / 2) • v

theorem mulVec_secondOrderLogPath {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u v : Fin n → ℝ) (s : ℝ) (i : Fin n) :
    A.mulVec (secondOrderLogPath u v s) i =
      quadraticExponent (A.mulVec u i) (A.mulVec v i) s := by
  unfold secondOrderLogPath quadraticExponent
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  rfl

def reactionCurrentQuadraticDerivative {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q u v : Fin n → ℝ) (i : Fin n) (s : ℝ) : ℝ :=
  expQuadraticDerivative (reconstructedForwardFlow J g q i)
      (source.reactant.transpose.mulVec u i)
      (source.reactant.transpose.mulVec v i) s -
    expQuadraticDerivative (reconstructedReverseFlow J g q i)
      (source.product.transpose.mulVec u i)
      (source.product.transpose.mulVec v i) s

def reactionCurrentSecondJet {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q u v : Fin n → ℝ) (i : Fin n) : ℝ :=
  (literalCurrentJacobian source J g q).mulVec v i +
    reconstructedForwardFlow J g q i *
      (source.reactant.transpose.mulVec u i) ^ 2 -
    reconstructedReverseFlow J g q i *
      (source.product.transpose.mulVec u i) ^ 2

theorem reconstructedLogReactionCurrent_secondDerivative_quadraticPath
    {n : ℕ} (source : SquareSource n) (J : ℝ) (g q u v : Fin n → ℝ)
    (i : Fin n) :
    HasDerivAt
        (fun s => reconstructedLogReactionCurrent source J g q
          (secondOrderLogPath u v s) i)
        (reactionCurrentQuadraticDerivative source J g q u v i 0) 0 ∧
      HasDerivAt (reactionCurrentQuadraticDerivative source J g q u v i)
        (reactionCurrentSecondJet source J g q u v i) 0 := by
  constructor
  · have hf := expQuadratic_hasDerivAt (reconstructedForwardFlow J g q i)
      (source.reactant.transpose.mulVec u i)
      (source.reactant.transpose.mulVec v i) 0
    have hr := expQuadratic_hasDerivAt (reconstructedReverseFlow J g q i)
      (source.product.transpose.mulVec u i)
      (source.product.transpose.mulVec v i) 0
    have hsub := hf.sub hr
    unfold reactionCurrentQuadraticDerivative
    apply hsub.congr_of_eventuallyEq
    filter_upwards [] with s
    simp only [reconstructedLogReactionCurrent, reconstructedLogForwardFlow,
      reconstructedLogReverseFlow, Pi.sub_apply]
    rw [mulVec_secondOrderLogPath, mulVec_secondOrderLogPath]
  · have hf := expQuadraticDerivative_hasDerivAt_zero
      (reconstructedForwardFlow J g q i)
      (source.reactant.transpose.mulVec u i)
      (source.reactant.transpose.mulVec v i)
    have hr := expQuadraticDerivative_hasDerivAt_zero
      (reconstructedReverseFlow J g q i)
      (source.product.transpose.mulVec u i)
      (source.product.transpose.mulVec v i)
    have hsub := hf.sub hr
    unfold reactionCurrentQuadraticDerivative
    apply hsub.congr_deriv
    unfold reactionCurrentSecondJet literalCurrentJacobian
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [Pi.sub_apply, Matrix.mulVec_diagonal]
    ring

def curvatureWeight {n : ℕ} (source : SquareSource n) (g u : Fin n → ℝ) :
    Fin n → ℝ := fun i =>
  g i * (source.reactant.transpose.mulVec u i) *
    (source.product.transpose.mulVec u i)

theorem reactionCurrentSecondJet_eq_acceleration_sub_curvature
    {n : ℕ} (source : SquareSource n) (J : ℝ) (g q u v : Fin n → ℝ)
    (hq : ∀ i, 1 < q i)
    (hratio : ∀ i, source.product.transpose.mulVec u i =
      q i * source.reactant.transpose.mulVec u i) (i : Fin n) :
    reactionCurrentSecondJet source J g q u v i =
      (literalCurrentJacobian source J g q).mulVec v i -
        J * curvatureWeight source g u i := by
  unfold reactionCurrentSecondJet curvatureWeight
  rw [hratio i]
  unfold reconstructedForwardFlow reconstructedReverseFlow
  unfold OptimalAffinityCorrected.reconstructedForwardFlux
    OptimalAffinityCorrected.reconstructedReverseFlux
  field_simp [ne_of_gt (sub_pos.mpr (hq i))]
  ring

theorem leftNull_curvature_formula
    {n : ℕ} (source : SquareSource n) (J J₂ : ℝ)
    (g q u v lambda : Fin n → ℝ)
    (hq : ∀ i, 1 < q i)
    (hratio : ∀ i, source.product.transpose.mulVec u i =
      q i * source.reactant.transpose.mulVec u i)
    (hannih : ∀ w : Fin n → ℝ,
      dotProduct lambda
        ((literalCurrentJacobian source J g q).mulVec w) = 0)
    (hcoupled : reactionCurrentSecondJet source J g q u v = J₂ • g)
    (hdenom : dotProduct lambda g ≠ 0) :
    J₂ = -J * dotProduct lambda (curvatureWeight source g u) /
      dotProduct lambda g := by
  apply (eq_div_iff hdenom).2
  have hjet : reactionCurrentSecondJet source J g q u v =
      (literalCurrentJacobian source J g q).mulVec v -
        J • curvatureWeight source g u := by
    funext i
    simpa using reactionCurrentSecondJet_eq_acceleration_sub_curvature
      source J g q u v hq hratio i
  calc
    J₂ * dotProduct lambda g =
        dotProduct lambda (J₂ • g) := by
          simp [dotProduct_smul]
    _ = dotProduct lambda (reactionCurrentSecondJet source J g q u v) := by
      rw [hcoupled]
    _ = dotProduct lambda
        ((literalCurrentJacobian source J g q).mulVec v -
          J • curvatureWeight source g u) := by rw [hjet]
    _ = -J * dotProduct lambda (curvatureWeight source g u) := by
      rw [dotProduct_sub, dotProduct_smul, hannih v]
      ring

theorem dotProduct_pos_of_nonnegative_nonzero_left {n : ℕ}
    (lambda x : Fin n → ℝ) (hlambda : ∀ i, 0 ≤ lambda i)
    (hlambda0 : lambda ≠ 0) (hx : ∀ i, 0 < x i) :
    0 < dotProduct lambda x := by
  have hex : ∃ i, 0 < lambda i := by
    by_contra h
    push Not at h
    apply hlambda0
    funext i
    exact le_antisymm (h i) (hlambda i)
  rw [dotProduct]
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (hlambda i) (le_of_lt (hx i))
  · obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_univ i, mul_pos hi (hx i)⟩

theorem leftNull_curvature_strictly_negative
    {n : ℕ} (source : SquareSource n) (J J₂ : ℝ)
    (g q u v lambda : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hf : ∀ i, 0 < source.reactant.transpose.mulVec u i)
    (hh : ∀ i, 0 < source.product.transpose.mulVec u i)
    (hlambda : ∀ i, 0 ≤ lambda i) (hlambda0 : lambda ≠ 0)
    (hq : ∀ i, 1 < q i)
    (hratio : ∀ i, source.product.transpose.mulVec u i =
      q i * source.reactant.transpose.mulVec u i)
    (hannih : ∀ w : Fin n → ℝ,
      dotProduct lambda ((literalCurrentJacobian source J g q).mulVec w) = 0)
    (hcoupled : reactionCurrentSecondJet source J g q u v = J₂ • g) :
    J₂ < 0 := by
  have hdenom : 0 < dotProduct lambda g :=
    dotProduct_pos_of_nonnegative_nonzero_left lambda g hlambda hlambda0 hg
  have hw : ∀ i, 0 < curvatureWeight source g u i := by
    intro i
    exact mul_pos (mul_pos (hg i) (hf i)) (hh i)
  have hnumer : 0 < dotProduct lambda (curvatureWeight source g u) :=
    dotProduct_pos_of_nonnegative_nonzero_left lambda
      (curvatureWeight source g u) hlambda hlambda0 hw
  rw [leftNull_curvature_formula source J J₂ g q u v lambda hq hratio
    hannih hcoupled (ne_of_gt hdenom)]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hJ) hnumer) hdenom

end
end OptimalAffinityRealizability
