import proofs.RandomViability.PhysicalFoodStopping

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

def foodCrossingBy {n : ℕ} (b : ℕ) (T : ℝ) (K : ℕ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∃ j, j ≤ K ∧
    (∀ i < j, incomingSum (fun l => trajectoryFoodInput (z (l+1)).2.1) i < b) ∧
    b ≤ incomingSum (fun l => trajectoryFoodInput (z (l+1)).2.1) j ∧
    waitingSum (fun l => (z (l+1)).2.2) j ≤ T

def foodCrossingEvent {n : ℕ} (b : ℕ) (T : ℝ) :
    Set (ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :=
  ⋃ K, {z | foodCrossingBy b T K z}

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem food_crossing_weighted_probability (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (b K : ℕ) (T : ℝ) :
    ENNReal.ofReal ((2 : ℝ)^b * Real.exp (-(14*(D : ℝ)*V)*T)) *
      physicalTrajectoryLaw hn c V D hV hD basal cat N {z | foodCrossingBy b T K z} ≤ 1 := by
  let a := ENNReal.ofReal ((2 : ℝ)^b * Real.exp (-(14*(D : ℝ)*V)*T))
  have ht := stopped_physical_product_tail hn c V D hV hD basal cat N
    (foodBudgetStop b) (foodHistorySum_stop_measurable b) K a
  have hsub : {z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) | foodCrossingBy b T K z} ⊆
      {z | a ≤ trajectoryProduct (fun k h y => if foodBudgetStop b k h then 1 else
        jumpMultiplier (fun ch => (2 : ℝ)^foodInputMass ch) (14*(D : ℝ)*V) y) K z} := by
    intro z hz
    obtain ⟨j, hjK, hbefore, hcross, htime⟩ := hz
    change a ≤ _
    rw [physical_stopped_product_eq]
    exact food_crossing_multiplier_lower _ _ (14*(D : ℝ)*V) T (by positivity) b j K hjK hbefore hcross htime
  exact (mul_le_mul_right (measure_mono hsub) a).trans ht

theorem food_crossing_probability (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (b K : ℕ) (T : ℝ) :
    physicalTrajectoryLaw hn c V D hV hD basal cat N {z | foodCrossingBy b T K z} ≤
      ENNReal.ofReal (Real.exp ((14*(D : ℝ)*V)*T)/(2 : ℝ)^b) := by
  let a := ENNReal.ofReal ((2 : ℝ)^b * Real.exp (-(14*(D : ℝ)*V)*T))
  let B := ENNReal.ofReal (Real.exp ((14*(D : ℝ)*V)*T)/(2 : ℝ)^b)
  have ha : B*a = 1 := by
    dsimp [B, a]
    rw [← ENNReal.ofReal_mul (by positivity)]
    have he : Real.exp ((14*(D : ℝ)*V)*T)/(2 : ℝ)^b *
        ((2 : ℝ)^b * Real.exp (-(14*(D : ℝ)*V)*T)) = 1 := by
      rw [neg_mul, Real.exp_neg]
      field_simp
    rw [he, ENNReal.ofReal_one]
  have ht := food_crossing_weighted_probability hn c V D hV hD basal cat N b K T
  calc
    _ = B*(a*physicalTrajectoryLaw hn c V D hV hD basal cat N {z | foodCrossingBy b T K z}) := by
      rw [← mul_assoc, ha, one_mul]
    _ ≤ B*1 := mul_le_mul_right ht B
    _ = B := mul_one _

theorem food_crossing_any_jump_probability (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (b : ℕ) (T : ℝ) :
    physicalTrajectoryLaw hn c V D hV hD basal cat N (foodCrossingEvent b T) ≤
      ENNReal.ofReal (Real.exp ((14*(D : ℝ)*V)*T)/(2 : ℝ)^b) := by
  have hm : Monotone (fun K => {z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) | foodCrossingBy b T K z}) := by
    intro K L hKL z hz
    obtain ⟨j, hj, hp, hc, ht⟩ := hz
    exact ⟨j, hj.trans hKL, hp, hc, ht⟩
  rw [foodCrossingEvent, hm.measure_iUnion]
  exact iSup_le (fun K => food_crossing_probability hn c V D hV hD basal cat N b K T)

end
end RandomViability
