import proofs.ResourceLimitedCompetition.AffineGrowthGenerator

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

noncomputable def spatialWeight (lam : ℝ) (N m : ℕ) : ℝ :=
  Real.exp (lam*((m : ℝ)-2*(N : ℝ)))

theorem spatialWeight_succ (lam : ℝ) (N m : ℕ) :
    spatialWeight lam N (m+1) = spatialWeight lam N m*Real.exp lam := by
  unfold spatialWeight
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

theorem spatial_generator_identity (β lam : ℝ) (N : ℕ)
    (f : Compartment → ℝ) (c : Compartment) :
    compartmentGenerator β (fun d => spatialWeight lam N d.2*f d) c =
      spatialWeight lam N c.2*compartmentGenerator β f c +
      β*(c.1 2 : ℝ)*spatialWeight lam N c.2*(Real.exp lam-1)*
        f (nextCompartment c (.inr ())) := by
  classical
  unfold compartmentGenerator
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [Fintype.sum_unique]
  have hres : (∑ r : Fin 13, propensity β c (.inl r)*
      (spatialWeight lam N (nextCompartment c (.inl r)).2*f (nextCompartment c (.inl r))-
        spatialWeight lam N c.2*f c)) =
      spatialWeight lam N c.2*(∑ r : Fin 13, propensity β c (.inl r)*
        (f (nextCompartment c (.inl r))-f c)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    change _*(spatialWeight lam N c.2*_-spatialWeight lam N c.2*_)=_
    ring
  rw [hres]
  change _ + β*(c.1 2 : ℝ)*(spatialWeight lam N (c.2+1)*_ - _) = _
  rw [spatialWeight_succ]
  simp only [propensity]
  ring

theorem exp_half_le_two : Real.exp (1/2 : ℝ) ≤ 2 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (by norm_num : |(1/2 : ℝ)| ≤ 1))).2
  norm_num at h ⊢
  linarith only [h]

/-- Scalar form of the existing source quadratic growth jump. -/
theorem membrane_exponential_ratio (N m Eold Enew L Q : ℝ)
    (hN : 0 ≤ N) (hm : 1 ≤ m) (hNm : N ≤ m)
    (hL : L ≤ 36) (hQ : 0 ≤ Q) (hQmax : Q ≤ 211722)
    (hE : Enew=Eold+(1/(m+1))*L+(1/(m+1))^2*Q) :
    Real.exp (N*localAlpha*Enew) ≤ 2*Real.exp (N*localAlpha*Eold) := by
  have hm1 : 0 < m+1 := by linarith only [hm]
  have hq : 0 ≤ 1/(m+1) := by positivity
  have hq1 : 1/(m+1) ≤ 1 := (div_le_one hm1).mpr (by linarith only [hm])
  have hk : 0 ≤ N/(m+1) := div_nonneg hN hm1.le
  have hk1 : N/(m+1) ≤ 1 := (div_le_one hm1).mpr (by linarith only [hNm])
  have hsum : L+(1/(m+1))*Q ≤ 211758 := by
    have hp := mul_le_mul hq1 hQmax hQ (by norm_num : (0 : ℝ) ≤ 1)
    linarith only [hL,hp]
  have hprod := mul_le_mul_of_nonneg_left hsum hk
  have hsmall : N*localAlpha*(Enew-Eold) ≤ 1/2 := by
    have hid : N*localAlpha*(Enew-Eold) =
        localAlpha*(N/(m+1))*(L+(1/(m+1))*Q) := by rw [hE]; ring
    rw [hid]
    unfold localAlpha
    nlinarith only [hprod,hk1]
  have he := (Real.exp_le_exp.mpr hsmall).trans exp_half_le_two
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (N*localAlpha*Eold)).le
  rw [← Real.exp_add] at hh
  convert hh using 1
  congr 1
  ring

theorem spatial_barrier_drift (β lam rate N k W Wnext g C LW : ℝ)
    (hN : 0 ≤ N) (hβmax : β ≤ 1/100000000000)
    (hlam : lam=1/1000000000000000) (hr : 0 ≤ rate) (hrmax : rate ≤ 8*β*N)
    (hW : 0 ≤ W) (hnext : 0 ≤ Wnext) (hratio : Wnext ≤ 2*W)
    (hg : 0 ≤ g) (hg1 : g ≤ 1) (hC : 0 ≤ C)
    (hk : k=N*localAlpha*innerEnergy/672)
    (hgen : LW ≤ -k*W+k*C) :
    g*LW+rate*g*(Real.exp lam-1)*Wnext ≤ -(k/2)*(g*W)+k*C := by
  subst lam
  have hex0 : 0 ≤ Real.exp (1/1000000000000000 : ℝ)-1 := by
    have h := Real.add_one_le_exp (1/1000000000000000 : ℝ)
    linarith only [h]
  have hex : Real.exp (1/1000000000000000 : ℝ)-1 ≤ 2/1000000000000000 := by
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
      (by norm_num : |(1/1000000000000000 : ℝ)| ≤ 1))).2
    linarith only [h]
  have hterm := mul_le_mul hex hratio hnext (by norm_num : (0:ℝ) ≤ 2/1000000000000000)
  have hterm' := mul_le_mul_of_nonneg_left hterm (mul_nonneg hr hg)
  have hrate := mul_le_mul_of_nonneg_right hrmax (mul_nonneg hg hW)
  have hbet := mul_le_mul_of_nonneg_right hβmax (mul_nonneg hN (mul_nonneg hg hW))
  have hbase := mul_le_mul_of_nonneg_left hgen hg
  have hk0 : 0 ≤ k := by rw [hk]; unfold localAlpha innerEnergy outerEnergy; positivity
  have hfloor := mul_le_mul_of_nonneg_right hg1 (mul_nonneg hk0 hC)
  have hpos := mul_nonneg hN (mul_nonneg hg hW)
  rw [hk] at hbase hfloor ⊢
  unfold localAlpha innerEnergy outerEnergy at hbase hfloor ⊢
  nlinarith only [hterm',hrate,hbet,hbase,hfloor,hpos]

end ResourceLimitedCompetition

