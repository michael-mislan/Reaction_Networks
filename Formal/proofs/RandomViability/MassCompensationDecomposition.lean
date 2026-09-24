import proofs.RandomViability.PhysicalStartupNoise

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem count_mass_nonfood_food {n : ℕ} (N : Molecule n → ℕ) :
    (countMass N : ℝ) = countNonfoodMass N+∑ q,foodMassWeight q*(N q : ℝ) := by
  simp only [countMass,Nat.cast_sum,Nat.cast_mul,countNonfoodMass,weightedCountMass,
    sub_mul,Finset.sum_sub_distrib]
  ring

def massConcentrationJump {n : ℕ} (V : NNReal) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) : ℝ :=
  ((countMass (unboundedPhysicalNext N ch) : ℝ)-(countMass N : ℝ))/V

theorem mass_jump_decomposition {n : ℕ} (V : NNReal) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) :
    massConcentrationJump V N ch = nonfoodConcentrationJump V N ch+
      ∑ q,foodMassWeight q*coordinateConcentrationJump V q N ch := by
  unfold massConcentrationJump nonfoodConcentrationJump coordinateConcentrationJump
  rw [count_mass_nonfood_food (unboundedPhysicalNext N ch),count_mass_nonfood_food N]
  simp only [← mul_div_assoc,mul_sub,Finset.sum_sub_distrib,← Finset.sum_div]
  ring

def physicalMassDrift {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) : ℝ :=
  ∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*massConcentrationJump V N ch

theorem physical_mass_drift_decomposition {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    physicalMassDrift c V basal cat N = physicalNonfoodDrift c V basal cat N+
      ∑ q,foodMassWeight q*physicalCoordinateDrift c V basal cat N q := by
  calc
    _ = physicalNonfoodDrift c V basal cat N+
        ∑ ch,∑ q,unboundedPhysicalRate c V 1 basal cat N ch*
          (foodMassWeight q*coordinateConcentrationJump V q N ch) := by
      simp only [physicalMassDrift,mass_jump_decomposition,mul_add,Finset.sum_add_distrib,
        Finset.mul_sum,physicalNonfoodDrift]
    _ = physicalNonfoodDrift c V basal cat N+
        ∑ q,∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*
          (foodMassWeight q*coordinateConcentrationJump V q N ch) := by rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      unfold physicalCoordinateDrift
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ch _
      ring

theorem weighted_compensation_sum {ι : Type*} [Fintype ι]
    (w u v : ι → ℝ) (a b t : ℝ) :
    (a+∑ q,w q*u q)-(b+∑ q,w q*v q)*t = (a-b*t)+∑ q,w q*(u q-v q*t) := by
  simp only [mul_sub,Finset.sum_sub_distrib,← mul_assoc,← Finset.sum_mul]
  ring

def censoredMassCompensation {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (T : ℝ) (k : ℕ)
    (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : ℝ :=
  let N := (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
  if censoredNonfoodStop V T (massExitStop V) k h then 0 else
    (if y.2.2 ≤ T-prefixElapsed k h then y.2.1.elim (fun _ => 0) (massConcentrationJump V N) else 0)-
    physicalMassDrift c V basal cat N*min y.2.2 (T-prefixElapsed k h)

theorem censored_mass_compensation_decomposition {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (T : ℝ) (k : ℕ)
    (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    censoredMassCompensation c V basal cat T k h y =
      censoredNonfoodCompensation c V basal cat T (massExitStop V) k h y+
      ∑ q,foodMassWeight q*censoredCoordinateCompensation c V basal cat q T k h y := by
  let N := (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
  have hi : (if y.2.2 ≤ T-prefixElapsed k h then y.2.1.elim (fun _ => 0) (massConcentrationJump V N) else 0) =
      (if y.2.2 ≤ T-prefixElapsed k h then y.2.1.elim (fun _ => 0) (nonfoodConcentrationJump V N) else 0)+
      ∑ q,foodMassWeight q*(if y.2.2 ≤ T-prefixElapsed k h then
        y.2.1.elim (fun _ => 0) (coordinateConcentrationJump V q N) else 0) := by
    split_ifs
    · cases y.2.1 <;> simp [mass_jump_decomposition]
    · simp
  by_cases hs : censoredNonfoodStop V T (massExitStop V) k h
  · simp only [censoredMassCompensation,censoredNonfoodCompensation,censoredCoordinateCompensation,
      if_pos hs,mul_zero,Finset.sum_const_zero,add_zero]
  · simp only [censoredMassCompensation,censoredNonfoodCompensation,censoredCoordinateCompensation,if_neg hs]
    change (if y.2.2 ≤ T-prefixElapsed k h then y.2.1.elim (fun _ => 0) (massConcentrationJump V N) else 0)-
      physicalMassDrift c V basal cat N*min y.2.2 (T-prefixElapsed k h) = _
    rw [hi,physical_mass_drift_decomposition]
    exact weighted_compensation_sum foodMassWeight
      (fun q => if y.2.2 ≤ T-prefixElapsed k h then y.2.1.elim (fun _ => 0) (coordinateConcentrationJump V q N) else 0)
      (physicalCoordinateDrift c V basal cat N)
      (if y.2.2 ≤ T-prefixElapsed k h then y.2.1.elim (fun _ => 0) (nonfoodConcentrationJump V N) else 0)
      (physicalNonfoodDrift c V basal cat N) (min y.2.2 (T-prefixElapsed k h))

def censoredMassPrefix {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ) : ℝ :=
  ∑ i : Fin K,censoredMassCompensation c V basal cat T
    i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1))

theorem censored_mass_prefix_decomposition {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ) :
    censoredMassPrefix c V basal cat T z K =
      censoredNonfoodPrefix c V basal cat T (massExitStop V) z K+
      ∑ q,foodMassWeight q*censoredCoordinatePrefix c V basal cat q T z K := by
  simp only [censoredMassPrefix,censoredNonfoodPrefix,censoredCoordinatePrefix,
    censored_mass_compensation_decomposition,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end
end RandomViability
