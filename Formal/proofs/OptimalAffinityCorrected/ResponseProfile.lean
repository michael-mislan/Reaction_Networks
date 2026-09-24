import Mathlib

/-!
The response-profile replacement for a scalar gross amplification factor.
For a response matrix `T`, production weights `g`, and a positive forward
response row `f`, the local exponential affinities are the componentwise
ratios `(f T)_j / f_j`.  The constrained infimum of their weighted product is
therefore a kinetics-independent lower bound at every optimum represented by
the cone.
-/

namespace OptimalAffinityCorrected

open scoped BigOperators
noncomputable section

def responseImage {n : ℕ} (T : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (j : Fin n) : ℝ :=
  ∑ i, f i * T i j

def responseRatio {n : ℕ} (T : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (j : Fin n) : ℝ :=
  responseImage T f j / f j

def responseObjective {n : ℕ} (T : Fin n → Fin n → ℝ)
    (g : Fin n → ℕ) (f : Fin n → ℝ) : ℝ :=
  ∏ j, (responseRatio T f j) ^ (g j)

def ForwardResponse {n : ℕ} (T : Fin n → Fin n → ℝ)
    (f : Fin n → ℝ) : Prop :=
  ∀ j, 0 < f j ∧ 1 < responseRatio T f j

def responseValueSet {n : ℕ} (T : Fin n → Fin n → ℝ)
    (g : Fin n → ℕ) : Set ℝ :=
  {z | ∃ f, ForwardResponse T f ∧ z = responseObjective T g f}

noncomputable def responseProfileBound {n : ℕ} (T : Fin n → Fin n → ℝ)
    (g : Fin n → ℕ) : ℝ :=
  sInf (responseValueSet T g)

theorem responseObjective_pos {n : ℕ} (T : Fin n → Fin n → ℝ)
    (g : Fin n → ℕ) (f : Fin n → ℝ) (hf : ForwardResponse T f) :
    0 < responseObjective T g f := by
  apply Finset.prod_pos
  intro j hj
  exact pow_pos (lt_trans zero_lt_one (hf j).2) _

theorem responseValueSet_bddBelow {n : ℕ} (T : Fin n → Fin n → ℝ)
    (g : Fin n → ℕ) : BddBelow (responseValueSet T g) := by
  refine ⟨0, ?_⟩
  intro z hz
  rcases hz with ⟨f, hf, rfl⟩
  exact (responseObjective_pos T g f hf).le

theorem responseProfileBound_le_objective {n : ℕ}
    (T : Fin n → Fin n → ℝ) (g : Fin n → ℕ) (f : Fin n → ℝ)
    (hf : ForwardResponse T f) :
    responseProfileBound T g ≤ responseObjective T g f := by
  apply csInf_le (responseValueSet_bddBelow T g)
  exact ⟨f, hf, rfl⟩

theorem responseProfileBound_isGLB {n : ℕ}
    (T : Fin n → Fin n → ℝ) (g : Fin n → ℕ)
    (hne : (responseValueSet T g).Nonempty) :
    IsGLB (responseValueSet T g) (responseProfileBound T g) := by
  exact isGLB_csInf hne (responseValueSet_bddBelow T g)

theorem grossBound_holdsOnResponseCone_iff {n : ℕ}
    (T : Fin n → Fin n → ℝ) (g : Fin n → ℕ) (gross : ℝ)
    (hne : (responseValueSet T g).Nonempty) :
    (∀ f, ForwardResponse T f → gross ≤ responseObjective T g f) ↔
      gross ≤ responseProfileBound T g := by
  constructor
  · intro h
    unfold responseProfileBound
    apply le_csInf hne
    intro z hz
    rcases hz with ⟨f, hf, rfl⟩
    exact h f hf
  · intro h f hf
    exact h.trans (responseProfileBound_le_objective T g f hf)

theorem responseProfileBound_applies_at_optimum {n : ℕ}
    (T : Fin n → Fin n → ℝ) (g : Fin n → ℕ) (f : Fin n → ℝ)
    (expAffinity : ℝ) (hf : ForwardResponse T f)
    (hopt : expAffinity = responseObjective T g f) :
    responseProfileBound T g ≤ expAffinity := by
  rw [hopt]
  exact responseProfileBound_le_objective T g f hf

theorem grossBound_criterion {n : ℕ}
    (T : Fin n → Fin n → ℝ) (g : Fin n → ℕ) (f : Fin n → ℝ)
    (gross expAffinity : ℝ) (hf : ForwardResponse T f)
    (hopt : expAffinity = responseObjective T g f)
    (hstruct : gross ≤ responseProfileBound T g) :
    gross ≤ expAffinity :=
  hstruct.trans (responseProfileBound_applies_at_optimum T g f expAffinity hf hopt)

end
end OptimalAffinityCorrected
