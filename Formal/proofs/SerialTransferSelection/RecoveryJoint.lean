import proofs.SerialTransferSelection.RecoveryExit
import proofs.SerialTransferSelection.RecoverySize
import proofs.ResourceLimitedCompetition.ProbabilityUnion

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy CoreCouplingCAC Set ResourceLimitedCompetition

def readyRecoverySet (N m : ℕ) (s : Point) (E : Point → ℝ) :
    Set (StoppedCompartment (growthDomain N s E outerEnergy)) :=
  {x | match x with
    | none => False
    | some c => c.val.2 = m ∧ E (fun i => concentration c.val.2 c.val.1 i-s i) ≤ innerEnergy}

noncomputable def recoveryError (u : ℝ) : ℝ :=
  Real.exp (-u)+2*Real.exp (-u/2)+Real.exp (-8*u)+16*u*Real.exp (-31*u/2)

/-- Actual fixed-time return, including exit mass and exact size preservation,
on one unrenormalized finite stopped count law. -/
theorem endpoint_joint_recovery (N : ℕ) (hN : 1 ≤ N)
    (s : Point) (hs : ∀ i, s i ≤ 34) (E : Point → ℝ)
    (hE : ∀ y, (1/200)*normSq y ≤ E y)
    (hgen : ∀ c ∈ growthDomain N s E outerEnergy, c.2 < 2*N →
      compartmentGenerator 0 (fun d => Real.exp ((N : ℝ)*localAlpha*
        E (fun i => concentration d.2 d.1 i-s i))) c ≤
      -((N : ℝ)*localAlpha*innerEnergy/672)*Real.exp ((N : ℝ)*localAlpha*
        E (fun i => concentration c.2 c.1 i-s i))+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)))
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel 0 (by norm_num) N (growthDomain N s E outerEnergy)).total c ≤ q)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N s E outerEnergy})
    (hc : c.val.2 < 2*N)
    (hendpoint : E (fun i => concentration c.val.2 c.val.1 i-s i) ≤ 8*innerEnergy) :
    1-recoveryError ((N : ℝ)*localAlpha*innerEnergy) ≤
      ((stoppedGrowthModel 0 (by norm_num) N (growthDomain N s E outerEnergy)).uniformize q hq hclock).poissonized
        (q*5376) (FiniteKernel.eventIndicator (readyRecoverySet N c.val.2 s E)) (some c) := by
  classical
  let D := growthDomain N s E outerEnergy
  let B : Fin 3 → Set (StoppedCompartment D) :=
    ![{none}, wrongRecoverySize D c.val.2, retainedUnrecovered N s E]
  have hcover : ∀ x ∈ (readyRecoverySet N c.val.2 s E)ᶜ, ∃ i, x ∈ B i := by
    intro x hx
    cases x with
    | none => exact ⟨0, rfl⟩
    | some d =>
      by_cases hm : d.val.2 = c.val.2
      · refine ⟨2, ?_⟩
        change d.val.2 < 2*N ∧ innerEnergy < E (fun i => concentration d.val.2 d.val.1 i-s i)
        refine ⟨hm ▸ hc, ?_⟩
        change ¬ (d.val.2 = c.val.2 ∧ _) at hx
        exact lt_of_not_ge (fun he => hx ⟨hm,he⟩)
      · exact ⟨1, hm⟩
  have h := poissonized_event_cover
    ((stoppedGrowthModel 0 (by norm_num) N D).uniformize q hq hclock)
    (q*5376) (readyRecoverySet N c.val.2 s E)ᶜ B hcover (some c)
  rw [Fin.sum_univ_three] at h
  have he := endpoint_exit_recovery 0 (by norm_num) N hN s hs E hE hgen q hq hclock c hendpoint
  have ht := endpoint_terminal_recovery 0 (by norm_num) N s E hgen q hq hclock hk c hc hendpoint
  have hm := zero_growth_size_probability N D q 5376 hq hclock c
  apply probability_complement_lower _ (q*5376) (readyRecoverySet N c.val.2 s E)
    (recoveryError ((N : ℝ)*localAlpha*innerEnergy)) (some c)
  dsimp [B, D] at h hm
  unfold recoveryError
  linarith only [h, he, ht, hm]

end SerialTransferSelection
