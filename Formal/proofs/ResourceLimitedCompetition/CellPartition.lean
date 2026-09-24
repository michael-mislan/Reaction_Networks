import proofs.ResourceLimitedCompetition.PopulationSupport
import proofs.HeritableCompositions.PartitionFailure

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set

noncomputable def partitionError (N : ℕ) : ℝ :=
  8*Real.exp (-(N : ℝ)*(1/1000000)^2/35)

theorem partitionError_nonneg (N : ℕ) : 0 ≤ partitionError N := by
  unfold partitionError
  positivity

abbrev goodBirths (N : ℕ) (zL zH : ℝ) (tag : Bool) (n d : Counts) : Prop :=
  cellEnergy zL zH ⟨tag,(d,N)⟩ < 4*innerEnergy ∧
    cellEnergy zL zH ⟨tag,((fun j => n j-d j),N)⟩ < 4*innerEnergy

theorem cell_partition_failure (N : ℕ) (hN : 0 < N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (tag : Bool) (n : Counts)
    (hp : cellEnergy zL zH ⟨tag,(n,2*N)⟩ ≤ 2*innerEnergy) :
    (∑ d ∈ daughterDraws n, daughterWeight n d*
      (if ¬goodBirths N zL zH tag n d then 1 else 0)) ≤ partitionError N := by
  classical
  cases tag with
  | false =>
    simpa only [goodBirths,cellEnergy,Bool.false_eq_true,if_false,partitionError]
      using low_partition_failure n N hN _ (lowroot_upper zL hzL) hp
  | true =>
    simpa only [goodBirths,cellEnergy,if_true,partitionError]
      using high_partition_failure n N hN _ (highroot_upper zH hzH) hp

theorem active_divisions_strict (N M : ℕ) (zL zH : ℝ)
    (s : ActiveState (activeDomain N M zL zH)) : s.val.divisions < 3*M := by
  have hs := activeDomain_safe N M zL zH s.val s.property
  have hl := membrane_lower N s.val.live (fun c hc => (hs.2.2.2.2.1 c hc).1)
  have hq := hs.1
  have hres := hs.2.2.1
  have hw : membrane s.val.live < 4*(N*M) := by omega
  have hn : N*s.val.live.length < N*(4*M) := by nlinarith only [hl,hw]
  have hcount : s.val.live.length < 4*M := Nat.lt_of_mul_lt_mul_left hn
  have hd := hs.2.2.2.1
  omega

end ResourceLimitedCompetition
