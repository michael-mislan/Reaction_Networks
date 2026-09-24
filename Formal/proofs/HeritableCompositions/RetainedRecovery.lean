import proofs.HeritableCompositions.SourceAffine
import proofs.HeritableCompositions.StoppedCutoff
import proofs.HeritableCompositions.KilledRecovery

namespace HeritableCompositions
open FiniteCopy

noncomputable def retainedUnrecovered (N : ℕ) (s : Point) (E : Point → ℝ) :
    Set (StoppedCompartment (growthDomain N s E outerEnergy)) :=
  {c | match c with
    | none => False
    | some c => c.val.2 < 2*N ∧ innerEnergy < E (fun i => concentration c.val.2 c.val.1 i-s i)}

theorem retained_recovery_bound (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ) (s : Point) (E : Point → ℝ)
    (hgen : ∀ c ∈ growthDomain N s E outerEnergy, c.2 < 2*N →
      compartmentGenerator γ (fun d => Real.exp ((N : ℝ)*localAlpha*E (fun i => concentration d.2 d.1 i-s i))) c ≤
      -((N : ℝ)*localAlpha*innerEnergy/672)*Real.exp ((N : ℝ)*localAlpha*E (fun i => concentration c.2 c.1 i-s i))+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)))
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N (growthDomain N s E outerEnergy)).total c ≤ q)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N s E outerEnergy}) (hc : c.val.2 < 2*N)
    (hbirth : E (fun i => concentration c.val.2 c.val.1 i-s i) ≤ 4*innerEnergy) :
    ((stoppedGrowthModel γ hγ N (growthDomain N s E outerEnergy)).uniformize q hq hclock).poissonized
      (q*4032) (FiniteKernel.eventIndicator (retainedUnrecovered N s E)) (some c) ≤
      3*Real.exp (-((N : ℝ)*localAlpha*innerEnergy)/2) := by
  classical
  let u := (N : ℝ)*localAlpha*innerEnergy
  let f := fun d : Compartment => Real.exp ((N : ℝ)*localAlpha*E (fun i => concentration d.2 d.1 i-s i))
  have hu : 0 ≤ u := by dsimp [u,localAlpha,innerEnergy,outerEnergy]; positivity
  have hA : ∀ d ∈ retainedUnrecovered N s E, Real.exp u ≤
      activeObservable N (growthDomain N s E outerEnergy) f d := by
    intro d hd
    cases d with
    | none => exact False.elim hd
    | some d =>
      change d.val.2 < 2*N ∧ _ at hd
      simp only [activeObservable,if_pos hd.1]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (le_of_lt hd.2) (by unfold localAlpha; positivity)
  have h := retained_affine_event γ hγ N (growthDomain N s E outerEnergy) f
    (fun _ => (Real.exp_pos _).le) (u/672) (2*Real.exp (u/2)) (by positivity) (by positivity)
    hgen q 4032 hq hclock hk (retainedUnrecovered N s E) (Real.exp u) hA c hc
  have ht : -(u/672)*(4032 : NNReal) = -6*u := by norm_num; ring
  rw [ht] at h
  apply fixed_time_recovery_tail u _ (f c.val) hu _ h
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hbirth
    (by unfold localAlpha; positivity : 0 ≤ (N : ℝ)*localAlpha)
  dsimp [u]
  nlinarith only [hh]

end HeritableCompositions
