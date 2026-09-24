import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace InheritedCellAssay.PositiveMoments

theorem le_initial_of_derivative_nonpos (f df : ℝ → ℝ) (T : ℝ)
    (hd : ∀ t, HasDerivAt f (df t) t)
    (hle : ∀ t ∈ Set.Icc 0 T, df t ≤ 0) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    f t ≤ f 0 := by
  have hm := antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) T)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [(hd x).deriv]; exact hle x (interior_subset hx))
  exact hm ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

theorem le_exp_of_deriv_le (f df : ℝ → ℝ) (k T : ℝ)
    (hd : ∀ t, HasDerivAt f (df t) t)
    (hle : ∀ t ∈ Set.Icc 0 T, df t ≤ k*f t) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    f t ≤ f 0*Real.exp (k*t) := by
  have he (s : ℝ) : HasDerivAt (fun x => Real.exp (-k*x))
      ((-k)*Real.exp (-k*s)) s := by
    convert ((hasDerivAt_id s).const_mul (-k)).exp using 1
    simp only [id_eq]
    ring
  have hp (s : ℝ) := (he s).mul (hd s)
  have hh := le_initial_of_derivative_nonpos _ _ T hp (fun s hs => by
    have h := mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg (-k*s))
      (sub_nonpos.mpr (hle s hs))
    nlinarith) t ht
  change Real.exp (-k*t)*f t ≤ Real.exp (-k*0)*f 0 at hh
  simp only [mul_zero, Real.exp_zero, one_mul] at hh
  apply le_of_mul_le_mul_left (a := Real.exp (-k*t)) _ (Real.exp_pos (-k*t))
  calc
    _ ≤ f 0 := hh
    _ = Real.exp (-k*t)*(f 0*Real.exp (k*t)) := by
      rw [mul_left_comm, ← Real.exp_add]
      simp

/-- Ordinary first-moment equations at the stated positive-switch parameters.
    This interface is separate from the still-required trajectory moment identity. -/
structure MomentODE where
  S : ℝ → ℝ
  R : ℝ → ℝ
  initialS : S 0 = 19/24
  initialR : R 0 = 5/24
  derivS : ∀ t, HasDerivAt S (-(301/1000)*S t+(1/100000)*R t) t
  derivR : ∀ t, HasDerivAt R ((1/1000)*S t+(9999/100000)*R t) t
  nonnegS : ∀ t, 0 ≤ t → 0 ≤ S t
  nonnegR : ∀ t, 0 ≤ t → 0 ≤ R t

theorem total_upper (M : MomentODE) (t : ℝ) (ht : 0 ≤ t) :
    M.S t+M.R t ≤ Real.exp (t/10) := by
  have hh := le_exp_of_deriv_le (fun s => M.S s+M.R s)
    (fun s => -(301/1000)*M.S s+(1/100000)*M.R s+
      ((1/1000)*M.S s+(9999/100000)*M.R s)) (1/10) t
    (fun s => (M.derivS s).add (M.derivR s))
    (fun s hs => by have := M.nonnegS s hs.1; linarith) t ⟨ht,le_rfl⟩
  norm_num [M.initialS, M.initialR] at hh
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using hh

private theorem exp_cancel (k t : ℝ) : Real.exp (-k*t)*Real.exp (k*t) = 1 := by
  rw [← Real.exp_add]
  ring_nf
  exact Real.exp_zero

private theorem exp_deriv (k t : ℝ) :
    HasDerivAt (fun s => Real.exp (k*s)) (k*Real.exp (k*t)) t := by
  convert ((hasDerivAt_id t).const_mul k).exp using 1
  simp only [id_eq]
  ring

theorem resistant_upper (M : MomentODE) (t : ℝ) (ht : t ∈ Set.Icc 0 7) :
    M.R t ≤ (26/25)*(5/24)*Real.exp ((1/10)*t) := by
  let f := fun s => Real.exp (-(1/10)*s)*M.R s-s/1000
  have hd (s : ℝ) := ((exp_deriv (-(1/10)) s).mul (M.derivR s)).sub
    ((hasDerivAt_id s).div_const 1000)
  have hi := le_initial_of_derivative_nonpos f _ 7 hd (fun s hs => by
    have hmu := total_upper M s hs.1
    have hr := M.nonnegR s hs.1
    have hS : M.S s ≤ Real.exp ((1/10)*s) := by
      have he : s/10 = (1/10)*s := by ring
      rw [he] at hmu
      linarith
    have hSe := mul_le_mul_of_nonneg_left hS (Real.exp_nonneg (-(1/10)*s))
    rw [exp_cancel] at hSe
    have hRe := mul_nonneg (Real.exp_nonneg (-(1/10)*s)) hr
    nlinarith) t ht
  change Real.exp (-(1/10)*t)*M.R t-t/1000 ≤
    Real.exp (-(1/10)*0)*M.R 0-0/1000 at hi
  norm_num [M.initialR] at hi
  apply le_of_mul_le_mul_left (a := Real.exp (-(1/10)*t)) _ (Real.exp_pos _)
  have hh : Real.exp (-(1/10)*t)*((26/25)*(5/24)*Real.exp ((1/10)*t)) =
      (26/25)*(5/24) := by
    calc
      _ = ((26/25)*(5/24))*(Real.exp (-(1/10)*t)*Real.exp ((1/10)*t)) := by ring
      _ = _ := by rw [exp_cancel]; ring
  rw [hh]
  simp only [neg_mul]
  linarith [ht.2]

theorem sensitive_upper (M : MomentODE) (t : ℝ) (ht : 0 ≤ t) :
    M.S t ≤ (19/24)*Real.exp (-(3/10)*t)+(1/40000)*Real.exp ((1/10)*t) := by
  let f := fun s => Real.exp ((3/10)*s)*M.S s-(1/40000)*Real.exp ((4/10)*s)
  have hd (s : ℝ) := ((exp_deriv (3/10) s).mul (M.derivS s)).sub
    ((exp_deriv (4/10) s).const_mul (1/40000))
  have hi := le_initial_of_derivative_nonpos f _ t hd (fun s hs => by
    have hmu := total_upper M s hs.1
    have hS := M.nonnegS s hs.1
    have hR : M.R s ≤ Real.exp ((1/10)*s) := by
      have he : s/10 = (1/10)*s := by ring
      rw [he] at hmu
      linarith
    have hRe := mul_le_mul_of_nonneg_left hR (Real.exp_nonneg ((3/10)*s))
    have he : Real.exp ((3/10)*s)*Real.exp ((1/10)*s) = Real.exp ((4/10)*s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at hRe
    have hSe := mul_nonneg (Real.exp_nonneg ((3/10)*s)) hS
    nlinarith) t ⟨ht,le_rfl⟩
  change Real.exp ((3/10)*t)*M.S t-(1/40000)*Real.exp ((4/10)*t) ≤
    Real.exp ((3/10)*0)*M.S 0-(1/40000)*Real.exp ((4/10)*0) at hi
  norm_num [M.initialS] at hi
  apply le_of_mul_le_mul_left (a := Real.exp ((3/10)*t)) _ (Real.exp_pos _)
  have he : Real.exp ((3/10)*t)*Real.exp ((1/10)*t) = Real.exp ((4/10)*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hc : Real.exp ((3/10)*t)*Real.exp (-(3/10)*t) = 1 := by
    rw [mul_comm, exp_cancel]
  nlinarith [he,hc]

theorem total_lower (M : MomentODE) (t : ℝ) (ht : t ∈ Set.Icc 0 7) :
    (993/1000)*((19/24)*Real.exp (-(3/10)*t)+(5/24)*Real.exp ((1/10)*t)) ≤
      M.S t+M.R t := by
  have hs := le_exp_of_deriv_le (fun s => -M.S s)
    (fun s => -(-(301/1000)*M.S s+(1/100000)*M.R s)) (-(301/1000)) 7
    (fun s => (M.derivS s).neg)
    (fun s hs => by have := M.nonnegR s hs.1; linarith) t ht
  have hr := le_exp_of_deriv_le (fun s => -M.R s)
    (fun s => -((1/1000)*M.S s+(9999/100000)*M.R s)) (9999/100000) 7
    (fun s => (M.derivR s).neg)
    (fun s hs => by have := M.nonnegS s hs.1; linarith) t ht
  norm_num [M.initialS, M.initialR] at hs hr
  have heS : Real.exp (-(1/1000)*t)*Real.exp (-(3/10)*t) =
      Real.exp (-(301/1000)*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heR : Real.exp (-(1/1000)*t)*Real.exp ((1/10)*t) ≤
      Real.exp ((9999/100000)*t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [ht.1]
  have he : (993/1000 : ℝ) ≤ Real.exp (-(1/1000)*t) := by
    have hh := Real.add_one_le_exp (-(1/1000)*t)
    linarith [ht.2]
  have hS := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-(3/10)*t))
  have hR := mul_le_mul_of_nonneg_right he (Real.exp_nonneg ((1/10)*t))
  rw [heS] at hS
  have hRR := hR.trans heR
  simp only [neg_mul] at hS
  simp only [neg_mul]
  nlinarith

end InheritedCellAssay.PositiveMoments
