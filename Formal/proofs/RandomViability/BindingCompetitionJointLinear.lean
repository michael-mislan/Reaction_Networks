import proofs.RandomViability.BindingCompetitionJointModel

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal
variable {V C : ℕ}
variable (Q : FiniteKernel (CompetitionWindowState V (competitionWindowCap V) × CompetitionGrossCounters C))

theorem competition_joint_steps_nonneg (t : ℝ≥0) (f : CompetitionJointState V C → ℝ)
    (hf : ∀ X, 0 ≤ f X) (n : ℕ) (X : CompetitionJointState V C) :
    0 ≤ competitionJointSteps Q t n f X := by
  induction n generalizing X with
  | zero => exact hf X
  | succ n ih => exact Q.poissonized_nonneg t _ (fun Y => ih (competitionJointBoundary Y X.2)) X.1

theorem competition_joint_steps_mono (t : ℝ≥0) (f g : CompetitionJointState V C → ℝ)
    (hf : ∀ X, 0 ≤ f X) (hg : ∀ X, 0 ≤ g X) (hfg : ∀ X, f X ≤ g X)
    (n : ℕ) (X : CompetitionJointState V C) :
    competitionJointSteps Q t n f X ≤ competitionJointSteps Q t n g X := by
  induction n generalizing X with
  | zero => exact hfg X
  | succ n ih =>
    exact Q.poissonized_mono t _ _
      (fun Y => competition_joint_steps_nonneg Q t f hf n _)
      (fun Y => competition_joint_steps_nonneg Q t g hg n _)
      (fun Y => ih (competitionJointBoundary Y X.2)) X.1

theorem competition_joint_steps_scale (t : ℝ≥0) (a : ℝ) (f : CompetitionJointState V C → ℝ)
    (n : ℕ) (X : CompetitionJointState V C) :
    competitionJointSteps Q t n (fun Y => a*f Y) X=a*competitionJointSteps Q t n f X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change Q.poissonized t (fun Y => competitionJointSteps Q t n (fun Z => a*f Z) (competitionJointBoundary Y X.2)) X.1 = _
    simp_rw [ih]
    exact Q.poissonized_scale t a _ X.1

theorem competition_joint_steps_add (t : ℝ≥0) (f g : CompetitionJointState V C → ℝ)
    (hf : ∀ X, 0 ≤ f X) (hg : ∀ X, 0 ≤ g X) (n : ℕ) (X : CompetitionJointState V C) :
    competitionJointSteps Q t n (fun Y => f Y+g Y) X=
      competitionJointSteps Q t n f X+competitionJointSteps Q t n g X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change Q.poissonized t (fun Y => competitionJointSteps Q t n (fun Z => f Z+g Z) (competitionJointBoundary Y X.2)) X.1 = _
    simp_rw [ih]
    exact Q.poissonized_add t _ _ (fun Y => competition_joint_steps_nonneg Q t f hf n _)
      (fun Y => competition_joint_steps_nonneg Q t g hg n _) X.1

theorem competition_joint_steps_const (t : ℝ≥0) (a : ℝ) (n : ℕ) (X : CompetitionJointState V C) :
    competitionJointSteps Q t n (fun _ => a) X=a := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change Q.poissonized t (fun Y => competitionJointSteps Q t n (fun _ => a) (competitionJointBoundary Y X.2)) X.1 = _
    simp_rw [ih]
    exact Q.poissonized_const t a X.1

theorem competition_joint_steps_growth (t : ℝ≥0) (f : CompetitionJointState V C → ℝ)
    (hf : ∀ X, 0 ≤ f X) (a : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ X, competitionJointAdvance Q t f X ≤ a*f X)
    (n : ℕ) (X : CompetitionJointState V C) :
    competitionJointSteps Q t n f X ≤ a^n*f X := by
  induction n generalizing X with
  | zero => simp [competitionJointSteps]
  | succ n ih =>
    have hm := Q.poissonized_mono t _ (fun Y => a^n*f (competitionJointBoundary Y X.2))
      (fun Y => competition_joint_steps_nonneg Q t f hf n _)
      (fun Y => mul_nonneg (pow_nonneg ha n) (hf _))
      (fun Y => ih (competitionJointBoundary Y X.2)) X.1
    rw [Q.poissonized_scale] at hm
    have hh := mul_le_mul_of_nonneg_left (hstep X) (pow_nonneg ha n)
    change competitionJointSteps Q t (n+1) f X ≤ _
    apply hm.trans (hh.trans_eq ?_)
    rw [pow_succ]
    ring

variable (S : FiniteKernel (CompetitionCounts V × CompetitionGrossCounters C))

theorem competition_joint_law_nonneg (q s : ℝ≥0) (m : ℕ) (f : CompetitionJointState V C → ℝ)
    (hf : ∀ X, 0 ≤ f X) (X : CompetitionCounts V × CompetitionGrossCounters C) :
    0 ≤ competitionJointLaw S Q q s m f X := by
  apply S.poissonized_nonneg
  intro Y
  apply competition_joint_steps_nonneg
  intro Z
  exact Q.poissonized_nonneg (q*s) _ (fun W => hf (W,Z.2)) Z.1

theorem competition_joint_law_mono (q s : ℝ≥0) (m : ℕ) (f g : CompetitionJointState V C → ℝ)
    (hf : ∀ X, 0 ≤ f X) (hg : ∀ X, 0 ≤ g X) (hfg : ∀ X, f X ≤ g X)
    (X : CompetitionCounts V × CompetitionGrossCounters C) :
    competitionJointLaw S Q q s m f X ≤ competitionJointLaw S Q q s m g X := by
  have hfn (Z : CompetitionJointState V C) : 0 ≤ competitionJointFinal Q q s f Z :=
    Q.poissonized_nonneg (q*s) _ (fun W => hf (W,Z.2)) Z.1
  have hgn (Z : CompetitionJointState V C) : 0 ≤ competitionJointFinal Q q s g Z :=
    Q.poissonized_nonneg (q*s) _ (fun W => hg (W,Z.2)) Z.1
  apply S.poissonized_mono (q*500) _ _
    (fun Y => competition_joint_steps_nonneg Q q _ hfn m _)
    (fun Y => competition_joint_steps_nonneg Q q _ hgn m _)
  intro Y
  apply competition_joint_steps_mono Q q _ _ hfn hgn
  intro Z
  exact Q.poissonized_mono (q*s) _ _ (fun W => hf (W,Z.2)) (fun W => hg (W,Z.2))
    (fun W => hfg (W,Z.2)) Z.1

theorem competition_joint_law_scale (q s : ℝ≥0) (m : ℕ) (a : ℝ) (f : CompetitionJointState V C → ℝ)
    (X : CompetitionCounts V × CompetitionGrossCounters C) :
    competitionJointLaw S Q q s m (fun Y => a*f Y) X=a*competitionJointLaw S Q q s m f X := by
  unfold competitionJointLaw
  have he : competitionJointFinal Q q s (fun Y => a*f Y)=(fun Y => a*competitionJointFinal Q q s f Y) := by
    funext Y
    exact Q.poissonized_scale (q*s) a _ Y.1
  rw [he]
  simp_rw [competition_joint_steps_scale]
  exact S.poissonized_scale (q*500) a _ X

theorem competition_joint_law_add (q s : ℝ≥0) (m : ℕ) (f g : CompetitionJointState V C → ℝ)
    (hf : ∀ X, 0 ≤ f X) (hg : ∀ X, 0 ≤ g X)
    (X : CompetitionCounts V × CompetitionGrossCounters C) :
    competitionJointLaw S Q q s m (fun Y => f Y+g Y) X=
      competitionJointLaw S Q q s m f X+competitionJointLaw S Q q s m g X := by
  have hfn (Z : CompetitionJointState V C) : 0 ≤ competitionJointFinal Q q s f Z :=
    Q.poissonized_nonneg (q*s) _ (fun W => hf (W,Z.2)) Z.1
  have hgn (Z : CompetitionJointState V C) : 0 ≤ competitionJointFinal Q q s g Z :=
    Q.poissonized_nonneg (q*s) _ (fun W => hg (W,Z.2)) Z.1
  have he : competitionJointFinal Q q s (fun Y => f Y+g Y)=
      (fun Y => competitionJointFinal Q q s f Y+competitionJointFinal Q q s g Y) := by
    funext Y
    exact Q.poissonized_add (q*s) _ _ (fun Z => hf (Z,Y.2)) (fun Z => hg (Z,Y.2)) Y.1
  unfold competitionJointLaw
  rw [he]
  simp_rw [competition_joint_steps_add Q q _ _ hfn hgn]
  exact S.poissonized_add (q*500) _ _
    (fun Y => competition_joint_steps_nonneg Q q _ hfn m _)
    (fun Y => competition_joint_steps_nonneg Q q _ hgn m _) X

theorem competition_joint_law_const (q s : ℝ≥0) (m : ℕ) (a : ℝ)
    (X : CompetitionCounts V × CompetitionGrossCounters C) :
    competitionJointLaw S Q q s m (fun _ => a) X=a := by
  have he : competitionJointFinal Q q s (fun _ => a)=(fun _ => a) := by
    funext Y
    exact Q.poissonized_const (q*s) a Y.1
  unfold competitionJointLaw
  rw [he]
  simp_rw [competition_joint_steps_const]
  exact S.poissonized_const (q*500) a X

end
end RandomViability.Binding
