import proofs.CompositionalMemory.SemenovScalarBounds
import proofs.CompositionalMemory.SemenovCountSource

namespace CompositionalMemory.Semenov

def recoveryVolume : ℕ := 24000000000000000000
def recoveryCountCap : ℕ := 20000000000000000000
def recoveryFeedQuota : ℕ := 12000000000000000000
def recoveryEta (high : Bool) : ℚ := if high then 9/100000000000000 else 6/1000000000000
def recoveryL (high : Bool) : ℚ := if high then 5148 else 4537
def recoveryQ (high : Bool) : ℚ := if high then 713/1000 else 61/100
def recoveryH (high : Bool) : ℚ := if high then 1290 else 2084
def recoveryRoot (high : Bool) : ℚ := if high then 120000000 else 19000000
def recoveryForce (high : Bool) : ℚ := if high then 1/20000000000 else 3/50000000000
def recoveryRefillRatio (high : Bool) : ℚ := if high then 13/50 else 9/100
def recoveryInitialL (high : Bool) : ℚ := if high then 3818 else 1601
def recoveryVariance (high : Bool) : ℚ := if high then 57/500 else 23/200

theorem recovery_parameter_checks (high : Bool) :
    0 < recoveryEta high ∧ 0 < recoveryL high ∧ 0 ≤ recoveryRoot high ∧
      recoveryH high/recoveryEta high ≤ (recoveryRoot high)^2 ∧
      0 ≤ recoveryRefillRatio high ∧ recoveryRefillRatio high ≤ 1 := by
  cases high <;> norm_num [recoveryEta,recoveryL,recoveryRoot,recoveryH,recoveryRefillRatio]

theorem recovery_scalar_drift_bound (high : Bool) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    6*x^10*(-x^2/(2*(recoveryL high : ℝ))+
      (recoveryQ high : ℝ)/((recoveryVolume : ℝ)*(recoveryEta high : ℝ))+
      100*(recoveryForce high : ℝ)^2/(recoveryEta high : ℝ))+
      sixthRemainderCoefficient (x^2) ((recoveryRoot high : ℝ)*
        (2*x/(recoveryVolume : ℝ)+(recoveryRoot high : ℝ)/(recoveryVolume : ℝ)^2))*
      ((recoveryVolume : ℝ)*((recoveryQ high : ℝ)/(recoveryEta high : ℝ))*
        (2*x/(recoveryVolume : ℝ)+(recoveryRoot high : ℝ)/(recoveryVolume : ℝ)^2)^2) ≤
      (1/1000000000 : ℝ) := by
  cases high
  · convert SemenovScalar.low_drift_bound x hx hx1 using 1
    norm_num [recoveryL,recoveryQ,recoveryVolume,recoveryEta,recoveryForce,recoveryRoot,
      SemenovScalar.lowDrift,sixthRemainderCoefficient]
    ring_nf
    simp
  · convert SemenovScalar.high_drift_bound x hx hx1 using 1
    norm_num [recoveryL,recoveryQ,recoveryVolume,recoveryEta,recoveryForce,recoveryRoot,
      SemenovScalar.highDrift,sixthRemainderCoefficient]
    ring_nf
    simp

theorem feed_mean_below_half_quota (t : ℝ) (ht : t ≤ 500) :
    (recoveryVolume : ℝ)*(15231/100000)/2+
      (recoveryVolume : ℝ)*(1/500)*(15231/100000)*t ≤ (recoveryFeedQuota : ℝ)/2 := by
  norm_num [recoveryVolume,recoveryFeedQuota] at *
  linarith only [ht]

end CompositionalMemory.Semenov
