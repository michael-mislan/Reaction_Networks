import proofs.PowerLawSmallRAF.SourceActiveRowError

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 100000

def sourceConfigDegrees (n : Nat) (B : SourceMoleculeFibreConfig n) : SourceDegreeConfig n :=
  fun x => ⟨(B x).card, Nat.lt_succ_of_le (Finset.card_le_univ (B x))⟩

private theorem sourceUniformRows_sum (n : Nat) (d : SourceDegreeConfig n) :
    (∑ B : SourceMoleculeFibreConfig n, uniformFixedRowsWeight (fun x => (d x).val) B) = 1 := by
  have hs (x : Molecule n) : (∑ T : Finset (Reaction n), uniformFixedRowWeight (d x) T) = 1 := by
    simpa only [uniformRowCompletionKernel, Finset.card_empty, Nat.zero_le, Finset.empty_subset,
      ite_true, Nat.sub_zero, uniformFixedRowWeight] using
      sum_uniformRowCompletionKernel (d x) (Nat.le_of_lt_succ (d x).isLt) (∅ : Finset (Reaction n))
  simp only [uniformFixedRowsWeight]
  rw [← Fintype.prod_sum (fun x (T : Finset (Reaction n)) => uniformFixedRowWeight (d x) T)]
  simp_rw [hs]
  simp

private theorem sourceUniformRows_degrees (n : Nat) (d : SourceDegreeConfig n)
    (B : SourceMoleculeFibreConfig n)
    (h : uniformFixedRowsWeight (fun x => (d x).val) B ≠ 0) : sourceConfigDegrees n B = d := by
  funext x
  apply Fin.ext
  change (B x).card = (d x).val
  by_contra hx
  have hz : uniformFixedRowWeight (d x) (B x) = 0 := by simp [uniformFixedRowWeight, hx]
  exact h (Finset.prod_eq_zero (Finset.mem_univ x) hz)

/-- Degree statistics have exactly the same expectation in the subset source
and in its degree-vector mixture. No Bernoulli replacement is involved. -/
theorem sourceDegreeStatistics_expectation (a : ℝ) (n : Nat) (F : SourceDegreeConfig n → ℝ) :
    (∑ B : SourceMoleculeFibreConfig n, sourcePowerLawConfigWeight a n B * F (sourceConfigDegrees n B)) =
      ∑ d : SourceDegreeConfig n, sourceDegreeWeight a n d * F d := by
  have hinner (d : SourceDegreeConfig n) :
      (∑ B : SourceMoleculeFibreConfig n,
        uniformFixedRowsWeight (fun x => (d x).val) B * F (sourceConfigDegrees n B)) = F d := by
    calc
      _ = ∑ B : SourceMoleculeFibreConfig n,
          uniformFixedRowsWeight (fun x => (d x).val) B * F d := by
        apply Finset.sum_congr rfl
        intro B _
        by_cases hz : uniformFixedRowsWeight (fun x => (d x).val) B = 0
        · simp only [hz, zero_mul]
        · rw [sourceUniformRows_degrees n d B hz]
      _ = _ := by rw [← Finset.sum_mul, sourceUniformRows_sum, one_mul]
  calc
    _ = ∑ B : SourceMoleculeFibreConfig n, ∑ d : SourceDegreeConfig n,
        sourceDegreeWeight a n d * uniformFixedRowsWeight (fun x => (d x).val) B * F (sourceConfigDegrees n B) := by
      apply Finset.sum_congr rfl
      intro B _
      rw [← Finset.sum_mul]
      congr 1
      exact (uniformFixedRowsWeight_degree_mixture
        (fun (_ : Molecule n) d => cappedZipfDegreeMass a (sourceReactionCount n) d) B).symm
    _ = ∑ d : SourceDegreeConfig n, sourceDegreeWeight a n d *
        ∑ B : SourceMoleculeFibreConfig n, uniformFixedRowsWeight (fun x => (d x).val) B * F (sourceConfigDegrees n B) := by
      rw [Finset.sum_comm]
      simp only [mul_assoc, Finset.mul_sum]
    _ = _ := by simp_rw [hinner]

end
end PowerLawSmallRAF
