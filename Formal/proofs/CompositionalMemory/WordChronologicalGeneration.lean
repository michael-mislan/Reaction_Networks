import proofs.CompositionalMemory.RetainedChronologicalBind
import proofs.CompositionalMemory.WordGenerationLaw

namespace CompositionalMemory
open Classical RandomViability FiniteCopy HeritableCompositions MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def wordPhysicalPhaseTwo {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hw : ∀ i j,0 ≤ w i j) (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a,center i a ≤ 34) (σ : Fin k → Bool) (t : NNReal)
    (s : {s : ModularCountState k // s ∈ productDomain N center (wordEnergy σ) (2*innerEnergy)})
    (H : WordBirthOutcome N center σ → ℝ) : ℝ≥0∞ :=
  physicalSafeDeadline (frozenCountNext N) (frozenCountRate γ w N)
    (frozen_count_rate_nonneg γ w hγ hw N) (frozen_count_total_positive γ w hγ hw N)
    (productDomain N center (wordEnergy σ) (2*innerEnergy) : Set (ModularCountState k))
    (liftRetainedNonneg (productDomain N center (wordEnergy σ) (2*innerEnergy))
      (fun x => ENNReal.ofReal ((wordAfterDivision N hN center hc σ x).expect H))) s.val t

theorem word_physical_phase_two_eq {k : ℕ} (hk : 1 ≤ k) (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hw : ∀ i j,0 ≤ w i j) (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a,center i a ≤ 34) (σ : Fin k → Bool)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x,(retainedModularModel γ w hγ hw N (productDomain N center (wordEnergy σ) (2*innerEnergy))).total x ≤ q)
    (H : WordBirthOutcome N center σ → ℝ) (hH0 : H none=0) (hH : ∀ x,0 ≤ H x ∧ H x ≤ 1)
    (s : {s : ModularCountState k // s ∈ productDomain N center (wordEnergy σ) (2*innerEnergy)}) :
    wordPhysicalPhaseTwo γ w hw hγ N hN center hc σ t s H=
      ENNReal.ofReal ((wordPhaseTwoLaw γ w hw hγ N hN center hc σ q t hq hclock s).expect H) := by
  exact retained_chronological_bind γ w hγ hw N _
    (product_domain_membrane_positive hk N hN center (wordEnergy σ) (2*innerEnergy)) q t hq hclock
    (wordAfterDivision N hN center hc σ) H
    (by simpa only [wordAfterDivision,FiniteLaw.expect_pure] using hH0) hH s

def wordPhysicalAfterRecovery {k : ℕ} (hk : 1 ≤ k) (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hw : ∀ i j,0 ≤ w i j) (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a,center i a ≤ 34) (σ : Fin k → Bool) (t : NNReal)
    (H : WordBirthOutcome N center σ → ℝ) :
    StoppedModularState (productDomain N center (wordEnergy σ) outerEnergy) → ℝ≥0∞
  | none => 0
  | some s => if h : s.val.2 < 2*(k*N) ∧ ∀ i,
      wordEnergy σ i (fun a => modularConcentration s.val i a-center i a) ≤ innerEnergy then
      wordPhysicalPhaseTwo γ w hw hγ N hN center hc σ t (wordEnterInner hk N hN center hc σ s h.2) H
    else 0

theorem word_physical_after_recovery_eq {k : ℕ} (hk : 1 ≤ k) (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hw : ∀ i j,0 ≤ w i j) (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a,center i a ≤ 34) (σ : Fin k → Bool)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x,(retainedModularModel γ w hγ hw N (productDomain N center (wordEnergy σ) (2*innerEnergy))).total x ≤ q)
    (H : WordBirthOutcome N center σ → ℝ) (hH0 : H none=0) (hH : ∀ x,0 ≤ H x ∧ H x ≤ 1)
    (s : StoppedModularState (productDomain N center (wordEnergy σ) outerEnergy)) :
    wordPhysicalAfterRecovery hk γ w hw hγ N hN center hc σ t H s=
      ENNReal.ofReal ((wordAfterRecovery hk γ w hw hγ N hN center hc σ q t hq hclock s).expect H) := by
  cases s with
  | none => simp [wordPhysicalAfterRecovery,wordAfterRecovery,FiniteLaw.expect_pure,hH0]
  | some s =>
    simp only [wordPhysicalAfterRecovery,wordAfterRecovery]
    split_ifs with h
    · exact word_physical_phase_two_eq hk γ w hw hγ N hN center hc σ q t hq hclock H hH0 hH _
    · simp [FiniteLaw.expect_pure,hH0]

/-- Both growth intervals use the unbounded nonexplosive frozen trajectory; the continuation
performs the recovery gate and the source complementary daughter partition. -/
def wordPhysicalGeneration {k : ℕ} (hk : 1 ≤ k) (γ : ℝ) (hγ : 0 < γ)
    (w : Fin k → Fin k → ℝ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a,center i a ≤ 34) (σ : Fin k → Bool)
    (H : WordBirthOutcome N center σ → ℝ) (b : WordBirthCount N center σ) : ℝ≥0∞ :=
  physicalSafeDeadline (frozenCountNext N) (frozenCountRate γ w N)
    (frozen_count_rate_nonneg γ w hγ.le hw N) (frozen_count_total_positive γ w hγ.le hw N)
    (productDomain N center (wordEnergy σ) outerEnergy : Set (ModularCountState k))
    (liftRetainedNonneg (productDomain N center (wordEnergy σ) outerEnergy)
      (wordPhysicalAfterRecovery hk γ w hw hγ.le N hN center hc σ (modularDeadline γ hγ) H))
    (wordBirthAsOuter hk N hN center hc σ b).val 2688

/-- Full two-phase actual-process identification, with no assumed transmission kernel. -/
theorem word_physical_generation_eq {k : ℕ} (hk : 1 ≤ k) (γ : ℝ) (hγ : 0 < γ)
    (w : Fin k → Fin k → ℝ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a,center i a ≤ 34) (σ : Fin k → Bool)
    (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀ : ℝ)) (hq₁ : 0 < (q₁ : ℝ))
    (hc₀ : ∀ x,(retainedModularModel γ w hγ.le hw N (productDomain N center (wordEnergy σ) outerEnergy)).total x ≤ q₀)
    (hc₁ : ∀ x,(retainedModularModel γ w hγ.le hw N (productDomain N center (wordEnergy σ) (2*innerEnergy))).total x ≤ q₁)
    (H : WordBirthOutcome N center σ → ℝ) (hH0 : H none=0) (hH : ∀ x,0 ≤ H x ∧ H x ≤ 1)
    (b : WordBirthCount N center σ) :
    wordPhysicalGeneration hk γ hγ w hw N hN center hc σ H b=
      ENNReal.ofReal ((wordGenerationLaw hk γ hγ w hw N hN center hc σ q₀ q₁ hq₀ hq₁ hc₀ hc₁ b).expect H) := by
  unfold wordPhysicalGeneration
  have he : wordPhysicalAfterRecovery hk γ w hw hγ.le N hN center hc σ (modularDeadline γ hγ) H=
      (fun s => ENNReal.ofReal ((wordAfterRecovery hk γ w hw hγ.le N hN center hc σ q₁
        (modularDeadline γ hγ) hq₁ hc₁ s).expect H)) := by
    funext s
    exact word_physical_after_recovery_eq hk γ w hw hγ.le N hN center hc σ q₁
      (modularDeadline γ hγ) hq₁ hc₁ H hH0 hH s
  rw [he]
  exact retained_chronological_bind γ w hγ.le hw N _
    (product_domain_membrane_positive hk N hN center (wordEnergy σ) outerEnergy)
    q₀ 2688 hq₀ hc₀
    (wordAfterRecovery hk γ w hw hγ.le N hN center hc σ q₁ (modularDeadline γ hγ) hq₁ hc₁) H
    (by simpa only [wordAfterRecovery,FiniteLaw.expect_pure] using hH0) hH
    (wordBirthAsOuter hk N hN center hc σ b)

end
end CompositionalMemory
