import proofs.HeritableCompositions.GrowthCertificate
import proofs.HeritableCompositions.RetainedRecovery
import proofs.HeritableCompositions.RetainedClock
import proofs.HeritableCompositions.ExitTail
import proofs.HeritableCompositions.GenerationBudget
import proofs.HeritableCompositions.KernelComposition

namespace HeritableCompositions
open FiniteCopy

theorem certificate_exit {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 ≤ γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (b : ℝ) (hb : b ≤ outerEnergy) (hbmin : 2*innerEnergy ≤ b)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy b)).total x ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N C.center C.energy b})
    (hgap : C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ b-innerEnergy/2) :
    ((stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy b)).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {none}) (some c) ≤ (1+(t : ℝ))*Real.exp (-(N : ℝ)*heredityExponent) := by
  have hgen (d) (hd : d ∈ growthDomain N C.center C.energy b) (_ : d.2 < 2*N) :
      compartmentGenerator γ (fun e => Real.exp ((N : ℝ)*localAlpha*C.energy (fun i => concentration e.2 e.1 i-C.center i))) d ≤
      growingCeiling N γ := by
    have hm := (mem_growthDomain N hN d C.center C.center_upper C.energy C.energy_lower b hb).mp hd
    exact C.ceiling N hN d hm.1 (hm.2.2.trans_le hb)
  have hraw := growth_energy_exit_bound γ hγ N hN C.center C.center_upper C.energy C.energy_lower
    b (growingCeiling N γ) hb (growingCeiling_nonneg N γ (Nat.cast_nonneg N)) hgen q t hq hclock c
  have h := growth_exit_tail N γ b _ t _ (Nat.cast_nonneg N) t.property hγ hγmax hbmin hgap hraw
  simpa only [heredity_error_eq] using h

theorem certificate_recovery {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 ≤ γ)
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy outerEnergy)).total x ≤ q)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N C.center C.energy outerEnergy}) (hc : c.val.2 < 2*N)
    (hbirth : C.energy (fun i => concentration c.val.2 c.val.1 i-C.center i) ≤ 4*innerEnergy) :
    ((stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy outerEnergy)).uniformize q hq hclock).poissonized (q*4032)
      (FiniteKernel.eventIndicator (retainedUnrecovered N C.center C.energy)) (some c) ≤
      3*Real.exp (-(N : ℝ)*heredityExponent) := by
  rw [heredity_error_eq]
  apply retained_recovery_bound γ hγ N C.center C.energy _ q hq hclock hk c hc hbirth
  intro d hd _
  have hm := (mem_growthDomain N hN d C.center C.center_upper C.energy C.energy_lower outerEnergy le_rfl).mp hd
  exact C.affine N hN hlarge d hm.1 hm.2.2

theorem certificate_early {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 ≤ γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy outerEnergy)).total x ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N C.center C.energy outerEnergy}) (hc : c.val.2=N) :
    ((stoppedGrowthModel γ hγ N (growthDomain N C.center C.energy outerEnergy)).uniformize q hq hclock).poissonized (q*4032)
      (FiniteKernel.eventIndicator (divisionRecorded N (growthDomain N C.center C.energy outerEnergy))) (some c) ≤
      Real.exp (-(N : ℝ)*heredityExponent) := by
  apply (early_division_tail γ (γ*4) hγ (by positivity) N _
    (fun d hd _ => (C.rates N hN outerEnergy le_rfl d hd).2)
    q 4032 hq (first_phase_clock_budget γ hγmax) hclock c hc).trans
  exact early_error_weaken N

theorem certificate_late {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy (2*innerEnergy))).total x ≤ q)
    (hk : 19*(γ*(99/100))*(N : ℝ)/400 ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N C.center C.energy (2*innerEnergy)}) (hc : c.val.2 < 2*N) :
    ((stoppedGrowthModel γ hγ.le N (growthDomain N C.center C.energy (2*innerEnergy))).uniformize q hq hclock).poissonized
      (q*secondDuration γ hγ hγmax) (FiniteKernel.eventIndicator (activeLiving N (growthDomain N C.center C.energy (2*innerEnergy))))
      (some c) ≤ Real.exp (-(N : ℝ)*heredityExponent) := by
  have hb : 2*innerEnergy ≤ outerEnergy := by norm_num [innerEnergy,outerEnergy]
  have hm := (mem_growthDomain N hN c.val C.center C.center_upper C.energy C.energy_lower (2*innerEnergy) hb).mp c.property
  apply (retained_late_tail γ (γ*(99/100)) hγ.le (by positivity) N _
    (fun d hd _ => (C.rates N hN (2*innerEnergy) hb d hd).1) q (secondDuration γ hγ hγmax)
    hq (second_phase_clock_budget γ hγ hγmax) hclock hk c hm.1 hc).trans
  exact clock_error_weaken N

end HeritableCompositions
