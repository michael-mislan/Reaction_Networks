import proofs.PowerLawSmallRAF.FiniteSeedProbabilityTransport
import proofs.HordijkSteelThreshold.StaticParameterMonotonicity

namespace PowerLawSmallRAF
open Classical MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
noncomputable section

theorem sourceFiniteSeedMass_mono (n N m : Nat) (hNn : N ≤ n)
    {a b : I} (hab : a ≤ b) :
    sourceFiniteSeedMass (a : ℝ) n N m ≤ sourceFiniteSeedMass (b : ℝ) n N m := by
  rw [sourceFiniteSeedMass_eq_static n N m hNn a,
    sourceFiniteSeedMass_eq_static n N m hNn b]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply static_increasing_event_mono N hab (fun H =>
    ∀ w ∈ actualBinaryWords m, ∃ x ∈ temporaryReactionClosure 2 H, moleculeWord x = w)
  intro S T hST hS w hw
  obtain ⟨x,hx,he⟩ := hS w hw
  exact ⟨x,temporaryReactionClosure_mono hST hx,he⟩

theorem sourceAboveSeedFailureMass_antitone {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1)
    (n m L : Nat) (hLn : L ≤ n) :
    sourceAboveSeedFailureMass q n m L ≤ sourceAboveSeedFailureMass p n m L := by
  rw [sourceAboveSeedFailureMass_eq,sourceAboveSeedFailureMass_eq,
    sourceAboveSeedMarkMass_eq_product q n m L hLn,
    sourceAboveSeedMarkMass_eq_product p n m L hLn]
  apply sub_le_sub_left
  apply Finset.prod_le_prod
  · intro w _
    exact sub_nonneg.mpr (pow_le_one₀ (by linarith) (by linarith))
  · intro w _
    exact sub_le_sub_left (pow_le_pow_left₀ (by linarith) (by linarith) _) 1

def sourceSeedExtensionMass (p : ℝ) (n N m L : Nat) : ℝ :=
  ∑ H : Finset (Reaction n), if sourceFiniteSeedEvent n N m H ∧
    SourceAboveSeedMarked n m L H then bernoulliSubsetRowWeight p H else 0

theorem sourceSeedExtensionMass_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n N m L : Nat) : 0 ≤ sourceSeedExtensionMass p n N m L := by
  apply Finset.sum_nonneg
  intro H _
  split_ifs
  · exact bernoulliSubsetRowWeight_nonneg hp hp1 H
  · exact le_rfl

theorem sourceSeedExtensionMass_lower {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n N m L : Nat) :
    sourceFiniteSeedMass p n N m - sourceAboveSeedFailureMass p n m L ≤
      sourceSeedExtensionMass p n N m L := by
  unfold sourceFiniteSeedMass sourceAboveSeedFailureMass sourceSeedExtensionMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro H _
  have hw := bernoulliSubsetRowWeight_nonneg hp hp1 H
  by_cases hs : sourceFiniteSeedEvent n N m H <;>
    by_cases he : SourceAboveSeedMarked n m L H <;> simp [hs,he,hw]

/-- Seed and extension may share channels. Subtract the unconditional
extension failure; no conditional independence is assumed. -/
theorem sourceSeedExtensionMass_floor (n N m L : Nat) (hNn : N ≤ n) (hLn : L ≤ n)
    {a b : I} (hab : a ≤ b) :
    sourceFiniteSeedMass (a : ℝ) n N m - sourceAboveSeedFailureMass (a : ℝ) n m L ≤
      sourceSeedExtensionMass (b : ℝ) n N m L := by
  have hs := sourceFiniteSeedMass_mono n N m hNn hab
  have he := sourceAboveSeedFailureMass_antitone a.property.1 hab b.property.2 n m L hLn
  have hl := sourceSeedExtensionMass_lower b.property.1 b.property.2 n N m L
  linarith

end
end PowerLawSmallRAF
