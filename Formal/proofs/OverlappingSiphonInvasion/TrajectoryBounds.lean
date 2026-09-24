import proofs.OverlappingSiphonInvasion.Source
import proofs.RobustPermanence.LogCorrector

noncomputable section
namespace OverlappingSiphonInvasion
open Filter Topology

/-- The source ODE and strict positivity, with no asymptotic hypotheses. Global
existence from initial data is a separate theorem, not built into permanence. -/
structure IsTrajectory (p : Rates) (X : ℝ → State) : Prop where
  positive : ∀ t, 0 ≤ t → ∀ i, 0 < X t i
  derivative : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun t => X t i) (field p (X t) i) t

def total (x : State) : ℝ := x 0+x 1+x 2+x 3
def infected (x : State) : ℝ := x 1+x 2+x 3

theorem lower_of_linear (y v : ℝ → ℝ) (T C k R : ℝ)
    (hk : 0 < k) (hR : R < C/k)
    (hd : ∀ t, T ≤ t → HasDerivAt y (v t) t)
    (hb : ∀ t, T ≤ t → C-k*y t ≤ v t) :
    ∀ᶠ t in atTop, R < y t := by
  have h := CoreCouplingGlobal.eventual_upper_of_linear_drift
    (fun t => -y t) (fun t => -v t) T (-C) k (-R) hk
    (by simpa only [neg_div] using neg_lt_neg hR)
    (fun t ht => (hd t ht).neg)
    (fun t ht => by have hh := hb t ht; linarith)
  filter_upwards [h] with t ht
  linarith

theorem total_derivative (X : ℝ → State) (h : IsTrajectory (witness 1) X)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun t => total (X t)) (4-total (X t)) t := by
  convert (((h.derivative t ht 0).add (h.derivative t ht 1)).add
    (h.derivative t ht 2)).add (h.derivative t ht 3) using 1
  rw [total_field]
  simp [witness, total]
  ring

theorem eventually_total_close (X : ℝ → State) (h : IsTrajectory (witness 1) X) :
    ∀ᶠ t in atTop, |total (X t)-4| ≤ 1/1000 := by
  have hu := CoreCouplingGlobal.eventual_upper_of_linear_drift
    (fun t => total (X t)) (fun t => 4-total (X t)) 0 4 1 (4+1/1000)
    (by norm_num) (by norm_num) (total_derivative X h)
    (fun t _ => by simp)
  have hl := lower_of_linear (fun t => total (X t)) (fun t => 4-total (X t))
    0 4 1 (4-1/1000) (by norm_num) (by norm_num) (total_derivative X h)
    (fun t _ => by simp)
  filter_upwards [hu,hl] with t ht ht'
  rw [abs_le]
  constructor <;> linarith

theorem infected_field (x : State) :
    field (witness 1) x 1+field (witness 1) x 2+field (witness 1) x 3 =
      x 0*(2*x 1+x 2+21*x 3/10)-infected x := by
  simp [field, witness, infected]
  ring

theorem infected_derivative (X : ℝ → State) (h : IsTrajectory (witness 1) X)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun t => infected (X t))
      (X t 0*(2*X t 1+X t 2+21*X t 3/10)-infected (X t)) t := by
  convert ((h.derivative t ht 1).add (h.derivative t ht 2)).add
    (h.derivative t ht 3) using 1
  exact (infected_field (X t)).symm

theorem infected_logistic (x : State) (hx : ∀ i, 0 ≤ x i) (hN : 39/10 ≤ total x) :
    infected x*(29/10-infected x) ≤
      x 0*(2*x 1+x 2+21*x 3/10)-infected x := by
  have hs := hx 0
  have ha := hx 1
  have hb := hx 2
  have hc := hx 3
  have hI : 0 ≤ infected x := by dsimp [infected]; positivity
  have hh := mul_nonneg hs (show 0 ≤ x 1+11*x 3/10 by positivity)
  have hmul := mul_nonneg (sub_nonneg.mpr hN) hI
  dsimp [infected,total] at *
  nlinarith only [hh,hmul]

theorem eventually_infected_bounds (X : ℝ → State) (h : IsTrajectory (witness 1) X) :
    ∀ᶠ t in atTop, 1 ≤ infected (X t) ∧ infected (X t) ≤ 5 := by
  obtain ⟨T,hT⟩ := eventually_atTop.1 ((eventually_total_close X h).and (eventually_ge_atTop (0:ℝ)))
  have hl := RobustPermanence.eventual_lower_of_logistic_drift
    (fun t => infected (X t))
    (fun t => X t 0*(2*X t 1+X t 2+21*X t 3/10)-infected (X t)) T (29/10) 1
    (by norm_num) (by norm_num)
    (fun t ht => by
      dsimp [infected]
      exact add_pos (add_pos (h.positive t (hT t ht).2 1)
        (h.positive t (hT t ht).2 2)) (h.positive t (hT t ht).2 3))
    (fun t ht => infected_derivative X h t (hT t ht).2)
    (fun t ht => by
      simpa only [one_mul] using infected_logistic (X t)
        (fun i => (h.positive t (hT t ht).2 i).le)
        (by have hh := (abs_le.mp (hT t ht).1).1; linarith))
  filter_upwards [hl,eventually_ge_atTop T] with t ht htT
  have hn := (abs_le.mp (hT t htT).1).2
  have hs := h.positive t (hT t htT).2 0
  constructor
  · norm_num at ht
    linarith
  · dsimp [total,infected] at *
    linarith

theorem eventually_susceptible_floor (X : ℝ → State) (h : IsTrajectory (witness 1) X) :
    ∀ᶠ t in atTop, 1/6 ≤ X t 0 := by
  obtain ⟨T,hT⟩ := eventually_atTop.1 ((eventually_total_close X h).and (eventually_ge_atTop (0:ℝ)))
  have hl := lower_of_linear (fun t => X t 0) (fun t => field (witness 1) (X t) 0)
    T 4 12 (1/6) (by norm_num) (by norm_num)
    (fun t ht => h.derivative t (hT t ht).2 0) (by
      intro t ht
      have hp := h.positive t (hT t ht).2
      have h0 := (hp 0).le
      have h1 := (hp 1).le
      have h2 := (hp 2).le
      have h3 := (hp 3).le
      have hn := (abs_le.mp (hT t ht).1).2
      have hcoef : 1+2*X t 1+X t 2+21*X t 3/10 ≤ 12 := by
        dsimp [total] at hn
        linarith
      have hm := mul_le_mul_of_nonneg_left hcoef h0
      simp [field,witness]
      nlinarith only [hm])
  filter_upwards [hl] with t ht
  exact ht.le

end OverlappingSiphonInvasion
