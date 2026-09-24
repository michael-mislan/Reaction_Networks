import proofs.FiniteCopyReactor.PhaseComparison

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

@[ext] structure PhaseWeights where
  x : ℝ
  c1 : ℝ
  c2 : ℝ
  z : ℝ

def PhaseWeights.Nonneg (w : PhaseWeights) : Prop :=
  0 ≤ w.x ∧ 0 ≤ w.c1 ∧ 0 ≤ w.c2 ∧ 0 ≤ w.z

def PhaseWeights.mass (w : PhaseWeights) : ℝ := w.x+w.c1+w.c2+w.z
def PhaseWeights.obs (w : PhaseWeights) (N : Counts) : ℝ :=
  w.x*(N 2)+w.c1*(N 3)+w.c2*(N 4)+w.z*(N 5)

def phaseWeightStep (q : ℝ) (w : PhaseWeights) : PhaseWeights :=
  ⟨(1-70/q)*w.x, (1-70/q)*w.c1+(20/q)*w.x,
   (1-70/q)*w.c2+(20/q)*w.c1+(20/q)*w.z,
   (1-70/q)*w.z+(38/q)*w.x⟩

def phaseWeights (q : ℝ) : ℕ → PhaseWeights
  | 0 => ⟨1,0,0,0⟩
  | n+1 => phaseWeightStep q (phaseWeights q n)

theorem phase_step_nonneg (q : ℝ) (hq : 0 < q) (hq70 : 70 ≤ q)
    (w : PhaseWeights) (hw : w.Nonneg) : (phaseWeightStep q w).Nonneg := by
  have ha : 0 ≤ 1-70/q := sub_nonneg.mpr ((div_le_one hq).mpr hq70)
  rcases hw with ⟨hx,h1,h2,hz⟩
  dsimp [PhaseWeights.Nonneg,phaseWeightStep]
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem phase_step_mass (q : ℝ) (hq : 0 < q) (w : PhaseWeights) (hw : w.Nonneg) :
    (phaseWeightStep q w).mass ≤ w.mass := by
  rcases hw with ⟨hx,h1,h2,hz⟩
  have he : w.mass-(phaseWeightStep q w).mass =
      (12*w.x+50*w.c1+70*w.c2+50*w.z)/q := by
    dsimp [phaseWeightStep,PhaseWeights.mass]
    ring
  have hh : 0 ≤ w.mass-(phaseWeightStep q w).mass := by rw [he]; positivity
  linarith

theorem phase_weights_bounds (q : ℝ) (hq : 0 < q) (hq70 : 70 ≤ q) (n : ℕ) :
    (phaseWeights q n).Nonneg ∧ (phaseWeights q n).mass ≤ 1 := by
  induction n with
  | zero => norm_num [phaseWeights,PhaseWeights.Nonneg,PhaseWeights.mass]
  | succ n ih => exact ⟨phase_step_nonneg q hq hq70 _ ih.1,
      (phase_step_mass q hq _ ih.1).trans ih.2⟩

def phaseWeightsClosed (q : ℝ) (n : ℕ) : PhaseWeights :=
  let a := 1-70/q
  ⟨a^n,a^n*(20*(n:ℝ))/(q*a),a^n*(580*(n:ℝ)*((n:ℝ)-1))/(q^2*a^2),
    a^n*(38*(n:ℝ))/(q*a)⟩

theorem phase_weights_closed (q : ℝ) (hq : 0 < q) (hqa : 70 < q) (n : ℕ) :
    phaseWeights q n=phaseWeightsClosed q n := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have ha : 1-70/q ≠ 0 := ne_of_gt (sub_pos.mpr ((div_lt_one hq).mpr hqa))
  induction n with
  | zero => simp [phaseWeights,phaseWeightsClosed]
  | succ n ih =>
    rw [phaseWeights,ih]
    apply PhaseWeights.ext
    all_goals dsimp [phaseWeightStep,phaseWeightsClosed]
    all_goals generalize he : 1-70/q=a at *
    all_goals rw [pow_succ]
    all_goals push_cast
    all_goals field_simp [hq0,ha]
    all_goals ring

end
end FiniteCopyReactor
