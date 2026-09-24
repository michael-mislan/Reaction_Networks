import proofs.TypeIIL.LogarithmicSecantMatrix

namespace TypeIIL

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Row of the logarithmic two-root equilibrium matrix.  The three terms are
forward mass action, reverse product mass action, and equilibrium routing
through the inverse stoichiometric matrix. -/
noncomputable def logEquilibriumKernelEntry
    [DecidableEq ι] (P : ι → ι → ℕ) (H : ι → ι → ℝ)
    (p q y rho : ι → ℝ) (r i : ι) : ℝ :=
  (if r = i then p r * logSecant (rho r) else 0) -
    q r * logSecant (monomialRatio P rho r) * (P i r : ℝ) -
    H r i * y i * logSecant (rho i)

/-- Exact source-independent docking statement: subtracting two stationary
flow equations and changing to log-ratio coordinates puts `log rho` in the
kernel of the explicitly factored secant matrix. -/
theorem log_equilibrium_kernel_row
    [DecidableEq ι] (P : ι → ι → ℕ) (H : ι → ι → ℝ)
    {p q y rho : ι → ℝ}
    (hrho : ∀ i, 0 < rho i)
    (hbase : ∀ r, p r - q r = ∑ i, H r i * y i)
    (hratio : ∀ r,
      rho r * p r - monomialRatio P rho r * q r =
        ∑ i, H r i * (y i * rho i))
    (r : ι) :
    ∑ i, logEquilibriumKernelEntry P H p q y rho r i * Real.log (rho i) = 0 := by
  have hdiff :
      p r * (rho r - 1) - q r * (monomialRatio P rho r - 1) =
        ∑ i, H r i * y i * (rho i - 1) := by
    calc
      p r * (rho r - 1) - q r * (monomialRatio P rho r - 1) =
          (rho r * p r - monomialRatio P rho r * q r) -
            (p r - q r) := by ring
      _ = (∑ i, H r i * (y i * rho i)) - ∑ i, H r i * y i := by
        rw [hratio r, hbase r]
      _ = ∑ i, H r i * y i * (rho i - 1) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hforward :
      p r * logSecant (rho r) * Real.log (rho r) = p r * (rho r - 1) := by
    rw [mul_assoc, logSecant_mul_log (hrho r)]
  have hreverse :
      q r * logSecant (monomialRatio P rho r) *
          (∑ i, (P i r : ℝ) * Real.log (rho i)) =
        q r * (monomialRatio P rho r - 1) := by
    rw [← log_monomialRatio P hrho r]
    rw [mul_assoc, logSecant_mul_log (monomialRatio_pos P hrho r)]
  have hrouting :
      ∑ i, H r i * y i * logSecant (rho i) * Real.log (rho i) =
        ∑ i, H r i * y i * (rho i - 1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc (H r i * y i), logSecant_mul_log (hrho i)]
  rw [show (∑ i, logEquilibriumKernelEntry P H p q y rho r i *
      Real.log (rho i)) =
      p r * logSecant (rho r) * Real.log (rho r) -
        q r * logSecant (monomialRatio P rho r) *
          (∑ i, (P i r : ℝ) * Real.log (rho i)) -
        ∑ i, H r i * y i * logSecant (rho i) * Real.log (rho i) by
    unfold logEquilibriumKernelEntry
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [ite_mul, zero_mul]
    simp [eq_comm, Finset.mul_sum]
    ring_nf]
  rw [hforward, hreverse, hrouting]
  linarith

end TypeIIL
