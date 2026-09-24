import proofs.CoreCouplingCAC.RootTransform
import Mathlib.Algebra.Polynomial.FieldDivision

open Polynomial
namespace CoreCouplingCAC

theorem three_positive_roots_exhaust (P : ℝ[X]) (hP : P ≠ 0)
    (hb : P.roots.countP (0 < ·) ≤ 3) (a b c : ℝ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hra : P.eval a = 0) (hrb : P.eval b = 0) (hrc : P.eval c = 0) :
    ∀ t, 0 < t → P.eval t = 0 →
      (t = a ∨ t = b ∨ t = c) ∧ P.derivative.eval t ≠ 0 := by
  classical
  have hac := hab.trans hbc
  have hbpos := ha.trans hab
  have hcpos := hbpos.trans hbc
  let s : Multiset ℝ := {a,b,c}
  have hn : s.Nodup := by simp [s,hab.ne,hbc.ne,hac.ne]
  have hle : s ≤ P.roots.filter (0 < ·) := by
    apply (Multiset.le_iff_subset hn).2
    intro x hx
    have hmem : x = a ∨ x = b ∨ x = c := by simpa [s] using hx
    rcases hmem with rfl | rfl | rfl
    · simp [ha,(mem_roots hP).2 hra]
    · simp [hbpos,(mem_roots hP).2 hrb]
    · simp [hcpos,(mem_roots hP).2 hrc]
  have heq : s = P.roots.filter (0 < ·) := Multiset.eq_of_le_of_card_le hle (by simpa [s,Multiset.countP_eq_card_filter] using hb)
  intro t ht hrt
  have hm : t ∈ P.roots.filter (0 < ·) := by simp [ht,(mem_roots hP).2 hrt]
  have hcases : t = a ∨ t = b ∨ t = c := by rw [← heq] at hm; simpa [s] using hm
  refine ⟨hcases,?_⟩
  have hc : P.roots.count t ≤ 1 := by
    have h := (Multiset.nodup_iff_count_le_one.1 hn) t
    rw [heq] at h
    simpa [ht] using h
  intro hd
  have hgt := (one_lt_rootMultiplicity_iff_isRoot hP).2 ⟨hrt,hd⟩
  rw [← count_roots] at hgt
  omega

theorem creation_tail_positive (e z : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hr : e ≤ (1/50000:ℝ)) (hz : 8 ≤ z) : 0 < residual (varyRates e) z := by
  have hzp : 0 < z := by linarith
  have hB : reducedB (varyRates e) z ≤ 6 := by
    dsimp [reducedB,varyRates,witnessRates]
    apply (div_le_iff₀ (by positivity : 0 < z+2)).2
    linarith
  have hK : 0 < reducedK (varyRates e) z := by
    change 0 < reducedK witnessRates z
    rw [witness_K]
    apply div_pos _ (by norm_num)
    have h := mul_pos hzp (show 0 < 20004*z-159984 by linarith)
    nlinarith only [h]
  have hmul := mul_le_mul_of_nonneg_left hB (show 0 ≤ 1+e by linarith)
  have hs : 0 ≤ e*(reducedA (varyRates e) z)^2 := mul_nonneg (by linarith) (sq_nonneg _)
  change 0 < 27-(1+e)*reducedB (varyRates e) z+reducedK (varyRates e) z+e*(reducedA (varyRates e) z)^2
  linarith only [hmul,hK,hs,hr]

theorem positive_stationary_residual (p : Rates) (hp : p.Positive) (x : State)
    (hx : x.Positive) (hs : Stationary p x) : residual p x.z = 0 := by
  have hz : x.z+2 ≠ 0 := by have := hx.2.2.1; positivity
  have hd : 2+p.d ≠ 0 := by have := hp.2.2.2.2.2; positivity
  have hr := stationary_reconstruction p x hz hd hs
  have hh := hs.2.1
  rw [hr] at hh
  exact (lift_residual p x.z hz hd).2.1.symm.trans hh

noncomputable def rootParameter (x : State) : ℝ := x.z/(8-x.z)

theorem mobius_inverse (z : ℝ) (hz : z < 8) : 8*(z/(8-z))/(1+z/(8-z)) = z := by
  have h : 8-z ≠ 0 := by linarith
  field_simp
  ring

theorem stationary_root_parameter (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hr : e ≤ (1/50000:ℝ))
    (x : State) (hx : x.Positive) (hs : Stationary (varyRates e) x) :
    x.z < 8 ∧ 0 < rootParameter x ∧ (countPoly e).eval (rootParameter x) = 0 := by
  have hp := varyRates_positive e (by linarith)
  have he := positive_stationary_residual _ hp x hx hs
  have hz : x.z < 8 := by
    by_contra h
    have ht := creation_tail_positive e x.z hl hr (le_of_not_gt h)
    linarith only [ht,he]
  have ht : 0 < rootParameter x := div_pos hx.2.2.1 (by linarith)
  refine ⟨hz,ht,?_⟩
  rw [count_transform e _ ht.le]
  change 44448889*(1+rootParameter x)^6*(8*(x.z/(8-x.z))/(1+x.z/(8-x.z))+2)^2*
    residual (varyRates e) (8*(x.z/(8-x.z))/(1+x.z/(8-x.z))) = 0
  rw [mobius_inverse x.z hz,he]
  ring

theorem rootParameter_order (x y : State) (_hx : x.z < 8) (hy : y.z < 8) (hxy : x.z < y.z) :
    rootParameter x < rootParameter y := by
  apply (div_lt_div_iff₀ (by linarith : 0 < 8-x.z) (by linarith : 0 < 8-y.z)).2
  nlinarith only [hxy]

theorem rootParameter_stationary_injective (e : ℝ) (he : 0 < e) (x y : State)
    (hx : x.Positive) (hy : y.Positive) (hsx : Stationary (varyRates e) x)
    (hsy : Stationary (varyRates e) y) (hzx : x.z < 8) (hzy : y.z < 8)
    (h : rootParameter x = rootParameter y) : x = y := by
  have hz : x.z = y.z := by
    have hi := congrArg (fun t : ℝ => 8*t/(1+t)) h
    change 8*(x.z/(8-x.z))/(1+x.z/(8-x.z)) = 8*(y.z/(8-y.z))/(1+y.z/(8-y.z)) at hi
    simpa only [mobius_inverse x.z hzx,mobius_inverse y.z hzy] using hi
  have hp := varyRates_positive e he
  have hd : 2+(varyRates e).d ≠ 0 := by norm_num [varyRates,witnessRates]
  rw [stationary_reconstruction _ x (by have := hx.2.2.1; positivity) hd hsx,
    stationary_reconstruction _ y (by have := hy.2.2.1; positivity) hd hsy,hz]

/-- Exactly three positive equilibria on the entire coupling interval. The
transformed polynomial roots corresponding to all these equilibria are simple. -/
theorem exactly_three_positive_equilibria (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hr : e ≤ (1/50000:ℝ)) :
    ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
      Stationary (varyRates e) x ∧ Stationary (varyRates e) y ∧ Stationary (varyRates e) w ∧
      x.z < y.z ∧ y.z < w.z ∧
      ∀ s : State, s.Positive → Stationary (varyRates e) s →
        (s = x ∨ s = y ∨ s = w) ∧ (countPoly e).derivative.eval (rootParameter s) ≠ 0 := by
  obtain ⟨x,y,w,hx,hy,hw,hsx,hsy,hsw,hxy,hyw⟩ := creation_interval e hl hr
  have hpx := stationary_root_parameter e hl hr x hx hsx
  have hpy := stationary_root_parameter e hl hr y hy hsy
  have hpw := stationary_root_parameter e hl hr w hw hsw
  have hP : countPoly e ≠ 0 := by
    intro h
    have hd := count_degree e (count_coeff_signs e hl hr).2.2.2.2.2.2
    rw [h,degree_zero] at hd
    norm_num at hd
  have hall := three_positive_roots_exhaust (countPoly e) hP (positive_count_bound e hl hr)
    (rootParameter x) (rootParameter y) (rootParameter w) hpx.2.1
    (rootParameter_order x y hpx.1 hpy.1 hxy) (rootParameter_order y w hpy.1 hpw.1 hyw)
    hpx.2.2 hpy.2.2 hpw.2.2
  refine ⟨x,y,w,hx,hy,hw,hsx,hsy,hsw,hxy,hyw,?_⟩
  intro s hs hss
  have hps := stationary_root_parameter e hl hr s hs hss
  obtain ⟨hcases,hderiv⟩ := hall (rootParameter s) hps.2.1 hps.2.2
  refine ⟨?_,hderiv⟩
  rcases hcases with h | h | h
  · exact Or.inl (rootParameter_stationary_injective e (by linarith) s x hs hx hss hsx hps.1 hpx.1 h)
  · exact Or.inr (Or.inl (rootParameter_stationary_injective e (by linarith) s y hs hy hss hsy hps.1 hpy.1 h))
  · exact Or.inr (Or.inr (rootParameter_stationary_injective e (by linarith) s w hs hw hss hsw hps.1 hpw.1 h))

end CoreCouplingCAC
