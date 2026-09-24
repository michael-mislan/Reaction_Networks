import proofs.MultiConsumerPermanence.AggregateIdentities
import proofs.CoreCouplingGlobal.ScalarComparison

namespace MultiConsumerPermanence
open Filter Topology

/-- Total persistence implies individual persistence under the reference scalar
consumer equations. This uses physical-time differential comparison and permits
arbitrary common environmental fluctuations. -/
theorem individual_floor_from_total
    (S Q x g : ℝ → ℝ) (T n s M : ℝ)
    (hn : 0 < n) (hs : 0 < s) (hM : 0 < M)
    (hx : ∀ t, T ≤ t → 0 < x t)
    (hS : ∀ t, T ≤ t → s ≤ S t ∧ S t ≤ M)
    (hc : ∀ t, T ≤ t → (S t)^2 ≤ n*Q t)
    (dS : ∀ t, T ≤ t → HasDerivAt S (g t*S t-n*Q t) t)
    (dx : ∀ t, T ≤ t → HasDerivAt x (x t*(g t-n*x t)) t) :
    ∀ᶠ t in atTop, s^2/(2*n*M) < x t := by
  let u := fun t => S t/x t
  let v := fun t => ((g t*S t-n*Q t)*x t-S t*(x t*(g t-n*x t)))/(x t)^2
  have hu : ∀ᶠ t in atTop, u t < 2*n*M/s := by
    apply CoreCouplingGlobal.eventual_upper_of_linear_drift u v T (n*M) s
      (2*n*M/s) hs
    · apply (div_lt_div_iff_of_pos_right hs).2
      nlinarith only [mul_pos hn hM]
    · intro t ht
      exact (dS t ht).div (dx t ht) (ne_of_gt (hx t ht))
    · intro t ht
      have hd := ratio_drift (S t) (Q t) (x t) (g t) n (hx t ht) (hc t ht)
      have htotal := mul_le_mul_of_nonneg_left (hS t ht).2 hn.le
      have hu0 : 0 ≤ u t := div_nonneg (hs.le.trans (hS t ht).1) (hx t ht).le
      have hl := mul_le_mul_of_nonneg_right (hS t ht).1 hu0
      change v t ≤ n*M-s*u t
      change v t ≤ n*S t-S t*u t at hd
      linarith only [hd,htotal,hl]
  filter_upwards [hu,eventually_ge_atTop T] with t ht htT
  have hxt := hx t htT
  have hh : S t < (2*n*M/s)*x t := (div_lt_iff₀ hxt).mp ht
  have hlow := (hS t htT).1
  apply (div_lt_iff₀ (by positivity : 0 < 2*n*M)).2
  have hmul := mul_lt_mul_of_pos_right (hlow.trans_lt hh) hs
  field_simp at hmul
  nlinarith only [hmul]

end MultiConsumerPermanence
