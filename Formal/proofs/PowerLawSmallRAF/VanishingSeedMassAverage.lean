import proofs.PowerLawSmallRAF.FiniteSeedMassMonotonicity
import proofs.PowerLawSmallRAF.VanishingLowUnion

namespace PowerLawSmallRAF
open Classical MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
open Filter Topology
noncomputable section

theorem sourceVanishingLowUnionParameter_bounds (n : Nat) (hn : 4 ≤ n)
    (d : SourceDegreeConfig n) :
    0 ≤ sourceVanishingLowUnionParameter n d ∧ sourceVanishingLowUnionParameter n d ≤ 1 :=
  bernoulliUnionParameter_bounds _
    (fun x => (sourceVanishingLowOwnerParameter_bounds n hn d x).1)
    (fun x => (sourceVanishingLowOwnerParameter_bounds n hn d x).2)

def sourceVanishingSeedExtensionMass (n N m L : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    sourceSeedExtensionMass (sourceVanishingLowUnionParameter n d) n N m L

/-- Discard low-openness degree configurations explicitly. This averages
the actual degree law without substituting its mean into an iid formula. -/
theorem sourceVanishingSeedExtensionMass_lower (n N m L : Nat)
    (hn : 4 ≤ n) (hNn : N ≤ n) (hLn : L ≤ n)
    (a : I) (t r : ℝ) (hat : (a : ℝ) ≤ 1-Real.exp (-t))
    (hr : r ≤ sourceFiniteSeedMass (a : ℝ) n N m - sourceAboveSeedFailureMass (a : ℝ) n m L) :
    r*(1-sourceVanishingLowUnionFailureMass t n) ≤ sourceVanishingSeedExtensionMass n N m L := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have hh := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
    linarith
  have hp (d : SourceDegreeConfig n) :
      r*(1-(if sourceVanishingLowUnionParameter n d < 1-Real.exp (-t) then 1 else 0)) ≤
        sourceSeedExtensionMass (sourceVanishingLowUnionParameter n d) n N m L := by
    have hq := sourceVanishingLowUnionParameter_bounds n hn d
    by_cases hb : sourceVanishingLowUnionParameter n d < 1-Real.exp (-t)
    · simp only [if_pos hb,sub_self,mul_zero]
      exact sourceSeedExtensionMass_nonneg hq.1 hq.2 n N m L
    · simp only [if_neg hb,sub_zero,mul_one]
      let b : I := ⟨sourceVanishingLowUnionParameter n d,hq⟩
      exact hr.trans (sourceSeedExtensionMass_floor n N m L hNn hLn
        (a := a) (b := b) (hat.trans (le_of_not_gt hb)))
  have he : (∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
      (r*(1-(if sourceVanishingLowUnionParameter n d < 1-Real.exp (-t) then 1 else 0)))) =
      r*(1-sourceVanishingLowUnionFailureMass t n) := by
    calc
      _ = r*((∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d) -
          ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
            (if sourceVanishingLowUnionParameter n d < 1-Real.exp (-t) then 1 else 0)) := by
        rw [← Finset.sum_sub_distrib,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = _ := by rw [sourceDegreeWeight_sum_eq_one _ _ ha hn]; rfl
  rw [← he]
  apply Finset.sum_le_sum
  intro d _
  exact mul_le_mul_of_nonneg_left (hp d) (sourceDegreeWeight_nonneg _ _ ha d)

/-- One fixed reversible seed captures any prescribed mass below iid
survival, up to an arbitrary extension error and a vanishing source-degree
exception. The estimate is uniform in the growing nucleus cutoff. -/
theorem source_vanishing_seed_survival_average (a : I) (ha : 1/2 < (a : ℝ))
    (t : ℝ) (hat : (a : ℝ) ≤ 1-Real.exp (-t))
    (ε : ℝ) (hε : 0 < ε) (c : ENNReal) (hc : c < staticSurvival a) :
    ∃ m N : Nat, 2 ≤ m ∧ m ≤ N ∧
      ∀ n L : Nat, 4 ≤ n → N ≤ n → L ≤ n →
        (c.toReal-ε)*(1-sourceVanishingLowUnionFailureMass t n) ≤
          sourceVanishingSeedExtensionMass n N m L := by
  obtain ⟨m,N,hm,hNm,hs,he⟩ := source_fixed_seed_uniform_survival_mass a ha ε hε c hc
  refine ⟨m,N,hm,hNm,?_⟩
  intro n L hn hNn hLn
  apply sourceVanishingSeedExtensionMass_lower n N m L hn hNn hLn a t _ hat
  have h1 := hs n hNn
  have h2 := he n L hLn
  linarith

end
end PowerLawSmallRAF
