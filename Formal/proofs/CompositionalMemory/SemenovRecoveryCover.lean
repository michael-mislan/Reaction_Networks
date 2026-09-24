import proofs.CompositionalMemory.SemenovRecoveryPieces
import proofs.CompositionalMemory.SemenovRecoverySeries

namespace CompositionalMemory.Semenov.SemenovRecoveryCover
open SemenovRecoveryPieces

def lowSeries (i : ℕ) : RecoveryPiece false := lowPieces (Fin.ofNat 16 i)

theorem low_joins (i : ℕ) (hi : i+1<16) :
    (lowSeries i).right=(lowSeries (i+1)).left ∧
    (lowSeries i).zRight=(lowSeries (i+1)).zLeft ∧
    (lowSeries i).pRight=(lowSeries (i+1)).pLeft := by
  have hlt : i<15 := by omega
  interval_cases i
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (0 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (0 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (0 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (1 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (1 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (1 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (2 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (2 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (2 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (3 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (3 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (3 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (4 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (4 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (4 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (5 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (5 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (5 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (6 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (6 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (6 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (7 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (7 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (7 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (8 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (8 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (8 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (9 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (9 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (9 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (10 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (10 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (10 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (11 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (11 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (11 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (12 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (12 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (12 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (13 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (13 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (13 : Fin 15) j))⟩
  · exact ⟨SemenovCoverChecks.low_checks.2.1 (14 : Fin 15),
      funext (SemenovCoverChecks.low_checks.2.2.1 (14 : Fin 15)),
      funext (fun j => funext (SemenovCoverChecks.low_checks.2.2.2.1 (14 : Fin 15) j))⟩

def lowTimeDifference (i : ℕ) : ℚ :=
  SemenovCoverChecks.low_rightTime (Fin.ofNat 16 i)-
    SemenovCoverChecks.low_leftTime (Fin.ofNat 16 i)

theorem low_duration_coe (i : ℕ) (hi : i<16) :
    ((lowSeries i).duration : ℝ)=(lowTimeDifference i : ℝ) := by
  interval_cases i <;> rfl

theorem low_rational_duration_total :
    (∑ i ∈ Finset.range 16,lowTimeDifference i)=(500 : ℚ) := by
  native_decide

theorem low_duration_total : (∑ i ∈ Finset.range 16,(lowSeries i).duration)=(500 : NNReal) := by
  apply NNReal.coe_injective
  push_cast
  calc
    (∑ i ∈ Finset.range 16,((lowSeries i).duration : ℝ)) =
        ∑ i ∈ Finset.range 16,(lowTimeDifference i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact low_duration_coe i (Finset.mem_range.mp hi)
    _ = 500 := by exact_mod_cast low_rational_duration_total

theorem low_recovery (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    finiteTimeExpectation (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
      500 (rightObservable (lowSeries 15)) s ≤
      leftObservable (lowSeries 0) s+1000*RecoveryPiece.driftCost := by
  have hh := recovery_series_total_bound lowSeries 16 low_joins 500 low_duration_total s
  norm_num only [seriesObservable,NNReal.coe_ofNat] at hh
  exact hh

def highSeries (i : ℕ) : RecoveryPiece true := highPieces (Fin.ofNat 22 i)

theorem high_joins (i : ℕ) (hi : i+1<22) :
    (highSeries i).right=(highSeries (i+1)).left ∧
    (highSeries i).zRight=(highSeries (i+1)).zLeft ∧
    (highSeries i).pRight=(highSeries (i+1)).pLeft := by
  have hlt : i<21 := by omega
  interval_cases i
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (0 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (0 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (0 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (1 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (1 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (1 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (2 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (2 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (2 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (3 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (3 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (3 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (4 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (4 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (4 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (5 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (5 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (5 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (6 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (6 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (6 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (7 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (7 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (7 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (8 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (8 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (8 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (9 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (9 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (9 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (10 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (10 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (10 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (11 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (11 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (11 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (12 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (12 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (12 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (13 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (13 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (13 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (14 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (14 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (14 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (15 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (15 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (15 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (16 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (16 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (16 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (17 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (17 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (17 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (18 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (18 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (18 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (19 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (19 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (19 : Fin 21) j))⟩
  · exact ⟨SemenovCoverChecks.high_checks.2.1 (20 : Fin 21),
      funext (SemenovCoverChecks.high_checks.2.2.1 (20 : Fin 21)),
      funext (fun j => funext (SemenovCoverChecks.high_checks.2.2.2.1 (20 : Fin 21) j))⟩

def highTimeDifference (i : ℕ) : ℚ :=
  SemenovCoverChecks.high_rightTime (Fin.ofNat 22 i)-
    SemenovCoverChecks.high_leftTime (Fin.ofNat 22 i)

theorem high_duration_coe (i : ℕ) (hi : i<22) :
    ((highSeries i).duration : ℝ)=(highTimeDifference i : ℝ) := by
  interval_cases i <;> rfl

theorem high_rational_duration_total :
    (∑ i ∈ Finset.range 22,highTimeDifference i)=(500 : ℚ) := by
  native_decide

theorem high_duration_total : (∑ i ∈ Finset.range 22,(highSeries i).duration)=(500 : NNReal) := by
  apply NNReal.coe_injective
  push_cast
  calc
    (∑ i ∈ Finset.range 22,((highSeries i).duration : ℝ)) =
        ∑ i ∈ Finset.range 22,(highTimeDifference i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact high_duration_coe i (Finset.mem_range.mp hi)
    _ = 500 := by exact_mod_cast high_rational_duration_total

theorem high_recovery (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    finiteTimeExpectation (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
      500 (rightObservable (highSeries 21)) s ≤
      leftObservable (highSeries 0) s+1000*RecoveryPiece.driftCost := by
  have hh := recovery_series_total_bound highSeries 22 high_joins 500 high_duration_total s
  norm_num only [seriesObservable,NNReal.coe_ofNat] at hh
  exact hh

end CompositionalMemory.Semenov.SemenovRecoveryCover
