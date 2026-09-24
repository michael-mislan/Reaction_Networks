import proofs.RAF1519.Refinement.MarkNoise
import proofs.RAF1519.Refinement.CountNoise

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators ENNReal

theorem mark_exponent_root_margin (V Δ : ℝ) (hV : 0 ≤ V) (hΔ : 0 ≤ Δ) :
    -V/160000000 ≤ -V/(200000000000000*(1+Δ)^3) := by
  have hc : 1 ≤ (1+Δ)^3 := one_le_pow₀ (by linarith : (1:ℝ) ≤ 1+Δ)
  have hd : (160000000:ℝ) ≤ 200000000000000*(1+Δ)^3 := by linarith
  have hh := div_le_div_of_nonneg_left hV (by norm_num : (0:ℝ) < 160000000) hd
  simpa only [neg_div] using neg_le_neg hh

theorem molecular_operating_noise_tail {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hsym : ∀ i j, k i j=k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (initial : MolecularState n)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV initial
      ((⋃ p, countIntervalFailure r d k V Δ p stop) ∪
       (⋃ p : Fin n × PhysicalMark, markIntervalFailure r d k V p.1 p.2 stop)) ≤
      24*n*ENNReal.ofReal (Real.exp (-V/(200000000000000*(1+Δ)^3))) := by
  have hc := molecular_all_coordinate_tail hn r d k V Δ hr hd hk hV hΔ hsym hdegree initial stop hstop
  have hm := molecular_all_mark_tail hn r d k V (fun i => (hr i).1) hd hk hV initial stop hstop
  have he := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mark_exponent_root_margin V Δ hV.le hΔ))
  have hm' := hm.trans (mul_le_mul_right he (10*(n:ℝ≥0∞)))
  exact (measure_union_le _ _).trans ((add_le_add hc hm').trans_eq (by ring))

end
end RAF1519.Refinement
