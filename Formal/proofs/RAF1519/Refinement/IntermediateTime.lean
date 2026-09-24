import proofs.RAF1519.Refinement.IntermediatePath

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

theorem intermediate_time_bound {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (hD : ∀ i, ((z 0).1 (i,6):ℝ)/V ≤ 1101/100000)
    (K : ℕ) (T : ℝ) (hT0 : 0 ≤ T) (hT : T ≤ 4)
    (hK : T < prefixElapsed K (Preorder.frestrictLe K z)) (i : Fin n) :
    countPath V z T (i,6) < 9/1000+(201/100000)*Real.exp (-(151/50)*T)+3/100000 := by
  have hh0 := fun j => (hh j).le
  have hs := material_no_exit r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0
  have heps := (count_tolerance_positive Δ hΔ).le
  have hb := graph_damped_upper k hk hsym (fun j => 1+d j*(1+1/100)/(1/100)) (151/50)
    (by norm_num) (fun j => (kappa_bounds (d j) (hd j).1 (hd j).2).1)
    (fun t j => countDriftPrimitive r d k V z K (j,6) t)
    (fun t j => ∑ a, molecularRate r d k V (z (countPathIndex z t)).1 a*
      molecularIncrement r d k V (j,6) (z (countPathIndex z t)).1 a)
    T (9/1000) (201/100000) ((2*Δ+126/25)*countTolerance Δ) (by norm_num) (by positivity)
    (fun j => (countDriftPrimitive_continuous r d k V z K (j,6)).continuousOn)
    (fun t ht j => countPrimitive_path_derivative r d k V z hh0 K (j,6) t ht.1 (ht.2.trans hK))
    (fun j => by dsimp only; rw [countDriftPrimitive_zero r d k V z hh0 K]; linarith [hD j])
    (fun t ht j => intermediate_primitive_drift_bound r d k V Δ hV hΔ hd hk hsym hdegree
      z hh hc hnoise hs K t ht.1 (ht.2.le.trans hT) (ht.2.trans hK) j)
    T ⟨hT0,le_rfl⟩ i
  have hn := countPath_noise_after_material_no_exit r d k V Δ hV z hh hc hnoise hs K T hT0 hT hK (i,6)
  have hp := (le_abs_self _).trans_lt hn
  have he := noise_amplification Δ hΔ
  change countTolerance Δ*(1+((126/25)+2*Δ)/(151/50)) < 3/100000 at he
  have hid : (2*Δ+126/25)*countTolerance Δ/(151/50)+countTolerance Δ =
      countTolerance Δ*(1+((126/25)+2*Δ)/(151/50)) := by ring
  linarith

theorem intermediate_decay_four : Real.exp (-(151/50)*4) ≤ 1/125000 := by
  have he : 50 ≤ Real.exp 4 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 4) 8
    norm_num [Finset.sum_range_succ] at h
    linarith
  have he12 : 125000 ≤ Real.exp 12 := by
    calc
      (125000:ℝ) = 50*50*50 := by norm_num
      _ ≤ Real.exp 4*Real.exp 4*Real.exp 4 :=
        mul_le_mul (mul_le_mul he he (by norm_num) (Real.exp_pos 4).le) he (by norm_num)
          (mul_nonneg (Real.exp_pos 4).le (Real.exp_pos 4).le)
      _ = Real.exp 12 := by rw [← Real.exp_add,← Real.exp_add]; norm_num
  have heT : 125000 ≤ Real.exp ((151/50)*4) :=
    he12.trans (Real.exp_le_exp.mpr (by norm_num))
  rw [neg_mul,Real.exp_neg,inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith

theorem intermediate_envelope_margins (t x : ℝ) (ht : 0 ≤ t)
    (hx : x < 9/1000+(201/100000)*Real.exp (-(151/50)*t)+3/100000) :
    x < 1104/100000 ∧ (t=4 → x < 904/100000) := by
  have he : Real.exp (-(151/50)*t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  constructor
  · linarith
  · intro h4
    subst t
    have hm := intermediate_decay_four
    have hb := intermediate_return_margin.1
    linarith

end
end RAF1519.Refinement
