import proofs.DUnstableCores.HopfFactorForest

/-!
# Inverse-free simple-cycle Hopf holonomy

For a directed scalar cycle at frequency `omega`, each local eigenvector
equation has the form

`g * z_in = (-a + i*omega) * z_out`.

Multiplying these relations around the cycle needs no division.  The inductive
trace below records simultaneously the real gain product, the complex phase
product, and its real squared-modulus cost.  A closed trace with nonzero
boundary state forces exact holonomy equality.
-/

namespace DUnstableCores

/-- A proof-carrying inverse-free transport chain.  The final three scalar
indices are, respectively, the product of real edge gains, the product of
complex local phase factors, and the product of their squared moduli. -/
inductive SimpleCycleTransfer (omega : ℝ) :
    ℝ → ℂ → ℝ → ℂ → ℂ → ℕ → Prop
  | nil (z : ℂ) : SimpleCycleTransfer omega 1 1 1 z z 0
  | step {gainProduct : ℝ} {phaseProduct : ℂ} {costProduct : ℝ}
      {z₀ z₁ zₙ : ℂ} {n : ℕ}
      (g a : ℝ)
      (localEq : (g : ℂ) * z₀ =
        (-(a : ℂ) + (omega : ℂ) * Complex.I) * z₁)
      (tail : SimpleCycleTransfer omega gainProduct phaseProduct
        costProduct z₁ zₙ n) :
      SimpleCycleTransfer omega (g * gainProduct)
        ((-(a : ℂ) + (omega : ℂ) * Complex.I) * phaseProduct)
        ((a ^ 2 + omega ^ 2) * costProduct) z₀ zₙ (n + 1)

/-- Successive local relations multiply to one exact endpoint relation. -/
theorem SimpleCycleTransfer.endpoint_balance
    {omega gainProduct costProduct : ℝ} {phaseProduct z₀ zₙ : ℂ} {n : ℕ}
    (h : SimpleCycleTransfer omega gainProduct phaseProduct
      costProduct z₀ zₙ n) :
    (gainProduct : ℂ) * z₀ = phaseProduct * zₙ := by
  induction h with
  | nil z => simp
  | @step gainProduct phaseProduct costProduct z₀ z₁ zₙ n g a
      localEq tail ih =>
      calc
        ((g * gainProduct : ℝ) : ℂ) * z₀ =
            (gainProduct : ℂ) * ((g : ℂ) * z₀) := by
              rw [Complex.ofReal_mul]
              ring
        _ = (gainProduct : ℂ) *
            ((-(a : ℂ) + (omega : ℂ) * Complex.I) * z₁) := by rw [localEq]
        _ = (-(a : ℂ) + (omega : ℂ) * Complex.I) *
            ((gainProduct : ℂ) * z₁) := by ring
        _ = (-(a : ℂ) + (omega : ℂ) * Complex.I) *
            (phaseProduct * zₙ) := by rw [ih]
        _ = ((-(a : ℂ) + (omega : ℂ) * Complex.I) * phaseProduct) * zₙ := by
              ring

/-- The recorded real cost is exactly the squared complex modulus of the
phase product. -/
theorem SimpleCycleTransfer.phase_normSq
    {omega gainProduct costProduct : ℝ} {phaseProduct z₀ zₙ : ℂ} {n : ℕ}
    (h : SimpleCycleTransfer omega gainProduct phaseProduct
      costProduct z₀ zₙ n) :
    Complex.normSq phaseProduct = costProduct := by
  induction h with
  | nil z => simp [Complex.normSq]
  | @step gainProduct phaseProduct costProduct z₀ z₁ zₙ n g a
      localEq tail ih =>
      calc
        Complex.normSq
            ((-(a : ℂ) + (omega : ℂ) * Complex.I) * phaseProduct) =
            Complex.normSq (-(a : ℂ) + (omega : ℂ) * Complex.I) *
              Complex.normSq phaseProduct := Complex.normSq_mul _ _
        _ = (a ^ 2 + omega ^ 2) * costProduct := by
              rw [ih]
              congr 1
              simp [Complex.normSq]
              ring

/-- A closed chain with nonzero boundary state has exact complex holonomy:
the product of real gains equals the product of local Hopf phase factors. -/
theorem SimpleCycleTransfer.closed_holonomy
    {omega gainProduct costProduct : ℝ} {phaseProduct z₀ zₙ : ℂ} {n : ℕ}
    (h : SimpleCycleTransfer omega gainProduct phaseProduct
      costProduct z₀ zₙ n)
    (hclose : zₙ = z₀) (hz : z₀ ≠ 0) :
    (gainProduct : ℂ) = phaseProduct := by
  have hbalance := h.endpoint_balance
  rw [hclose] at hbalance
  exact mul_right_cancel₀ hz hbalance

/-- Public real profile of a closed simple cycle: the phase product is real,
its real part is the gain product, and the squared gain pays exactly the
product of local costs `a_i^2 + omega^2`. -/
theorem SimpleCycleTransfer.closed_holonomy_profile
    {omega gainProduct costProduct : ℝ} {phaseProduct z₀ zₙ : ℂ} {n : ℕ}
    (h : SimpleCycleTransfer omega gainProduct phaseProduct
      costProduct z₀ zₙ n)
    (hclose : zₙ = z₀) (hz : z₀ ≠ 0) :
    phaseProduct.re = gainProduct ∧ phaseProduct.im = 0 ∧
      gainProduct ^ 2 = costProduct := by
  have hhol := h.closed_holonomy hclose hz
  have hnorm := h.phase_normSq
  constructor
  · have hre := congrArg Complex.re hhol
    simpa using hre.symm
  constructor
  · have him := congrArg Complex.im hhol
    simpa using him.symm
  · rw [← hnorm, ← hhol]
    simp [Complex.normSq, pow_two]

end DUnstableCores
