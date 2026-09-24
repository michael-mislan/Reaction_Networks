import proofs.CoreCouplingGlobal.CurveEnergy
import proofs.CoreCouplingGlobal.ResidualGaps

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

theorem stationary_curve_energy (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (s : State) (hs : s.Positive)
    (heq : Stationary (flagshipRates e) s) :
    statePotential e p s = curveEnergy e p s.z := by
  obtain ⟨hr,hH,_⟩ := positive_stationary_barrier_identities e he hu s hs heq
  have ha := heq.1
  have hb := heq.2.1
  dsimp [fA,fB,flagshipRates] at ha hb
  have hB : s.B = 60/(s.z+2) := by
    apply (eq_div_iff (by have := hs.2.2.1; positivity : s.z+2 ≠ 0)).2
    linear_combination -ha-2*hb
  unfold statePotential curveEnergy
  rw [hr,hH,hB]

theorem bracketed_well_energy (e : ℝ) (p : PotentialPrimitives e)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000)
    (low mid high : State) (hloP : low.Positive) (hmP : mid.Positive) (hhiP : high.Positive)
    (hloS : Stationary (flagshipRates e) low) (hmS : Stationary (flagshipRates e) mid)
    (hhiS : Stationary (flagshipRates e) high)
    (hlo : low.z ∈ Icc (9/10:ℝ) (11/10)) (hm : mid.z ∈ Icc (19/10:ℝ) (21/10))
    (hhi : high.z ∈ Icc (29/10:ℝ) (31/10))
    (hall : ∀ s : State, s.Positive → Stationary (flagshipRates e) s → s = low ∨ s = mid ∨ s = high) :
    statePotential e p low < statePotential e p mid ∧ statePotential e p high < statePotential e p mid := by
  have he : 0 ≤ e := by linarith
  have heq : varyRates e = flagshipRates e := rfl
  have hp := varyRates_positive e (by linarith)
  have hsl : residual (varyRates e) low.z = 0 := positive_stationary_residual _ hp low hloP (by simpa only [heq] using hloS)
  have hsm : residual (varyRates e) mid.z = 0 := positive_stationary_residual _ hp mid hmP (by simpa only [heq] using hmS)
  have hsh : residual (varyRates e) high.z = 0 := positive_stationary_residual _ hp high hhiP (by simpa only [heq] using hhiS)
  have hall' : ∀ s : State, s.Positive → Stationary (varyRates e) s → s = low ∨ s = mid ∨ s = high := by
    simpa only [heq] using hall
  obtain ⟨hpos,hneg⟩ := residual_between_bracketed_roots e hl hu low mid high hlo hm hhi hsl hsm hsh hall'
  rw [stationary_curve_energy e p he hu low hloP hloS,
    stationary_curve_energy e p he hu mid hmP hmS,stationary_curve_energy e p he hu high hhiP hhiS]
  let df := fun z => -reducedZ e (60/(z+2)) z/((z+1)*(z+2))
  have hlm : low.z < mid.z := by linarith [hlo.2,hm.1]
  have hmh : mid.z < high.z := by linarith [hm.2,hhi.1]
  constructor
  · obtain ⟨t,ht,heSlope⟩ := exists_hasDerivAt_eq_slope (curveEnergy e p) df hlm
      (fun t ht => (curveEnergy_hasDerivAt e p he hu t
        ⟨by linarith [ht.1,hlo.1],by linarith [ht.2,hm.2]⟩).continuousAt.continuousWithinAt)
      (fun t ht => curveEnergy_hasDerivAt e p he hu t
        ⟨by linarith [ht.1,hlo.1],by linarith [ht.2,hm.2]⟩)
    have hd : 0 < df t := (curveEnergy_derivative_sign e t he hu
      ⟨by linarith [ht.1,hlo.1],by linarith [ht.2,hm.2]⟩).1.2 (hpos t ht)
    have hmul := mul_pos hd (sub_pos.mpr hlm)
    have hid := (eq_div_iff (by linarith : mid.z-low.z ≠ 0)).1 heSlope
    nlinarith
  · obtain ⟨t,ht,heSlope⟩ := exists_hasDerivAt_eq_slope (curveEnergy e p) df hmh
      (fun t ht => (curveEnergy_hasDerivAt e p he hu t
        ⟨by linarith [ht.1,hm.1],by linarith [ht.2,hhi.2]⟩).continuousAt.continuousWithinAt)
      (fun t ht => curveEnergy_hasDerivAt e p he hu t
        ⟨by linarith [ht.1,hm.1],by linarith [ht.2,hhi.2]⟩)
    have hd : df t < 0 := (curveEnergy_derivative_sign e t he hu
      ⟨by linarith [ht.1,hm.1],by linarith [ht.2,hhi.2]⟩).2.2 (hneg t ht)
    have hmul := mul_neg_of_neg_of_pos hd (sub_pos.mpr hmh)
    have hid := (eq_div_iff (by linarith : high.z-mid.z ≠ 0)).1 heSlope
    nlinarith

end CoreCouplingGlobal
