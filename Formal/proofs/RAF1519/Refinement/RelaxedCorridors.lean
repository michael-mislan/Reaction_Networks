import proofs.RAF1519.Refinement.TolerancePath
import proofs.RAF1519.Refinement.CountFreeFloor

namespace RAF1519.Refinement.Relaxed
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

abbrev countTolerance := relaxedTolerance
abbrev countIntervalFailure {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V Δ : ℝ) := intervalFailureAt r d k V (countTolerance Δ)

theorem count_tolerance_positive (Δ : ℝ) (hΔ : 0 ≤ Δ) : 0 < countTolerance Δ := by
  unfold countTolerance relaxedTolerance
  positivity

theorem material_allowance (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    18*(1+Δ)*countTolerance Δ=18/10000 := by
  unfold countTolerance relaxedTolerance
  have hn : 1+Δ ≠ 0 := by positivity
  field_simp

theorem material_budget (Δ : ℝ) (hΔ : 0 ≤ Δ) : 18*(1+Δ)*countTolerance Δ ≤ 1/20 := by
  rw [material_allowance Δ hΔ]; norm_num

theorem material_no_exit {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25) :
    ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1 := material_no_exit_budget r d k V Δ (countTolerance Δ) hV hΔ (count_tolerance_positive Δ hΔ).le (material_budget Δ hΔ) hk hsym hdegree z hh hc hnoise h0

theorem countPath_noise_after_material_no_exit {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (hsafe : ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hT : t ≤ 4)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z)) (p : Fin n × Fin 7) :
    |countPath V z t p-countDriftPrimitive r d k V z K p t| < countTolerance Δ := noise_after_material_at r d k V (countTolerance Δ) hV z hh hc hnoise hsafe K t ht hT hK p

theorem material_time_bound {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (K : ℕ) (T : ℝ) (hT0 : 0 ≤ T) (hT : T ≤ 4)
    (hK : T < prefixElapsed K (Preorder.frestrictLe K z)) (b : Bool) (i : Fin n) :
    |countMaterial b V z T i-1| ≤ (1/25)*Real.exp (-T)+18/10000 := by
  have h := material_time_budget r d k V Δ (countTolerance Δ) hV hΔ (count_tolerance_positive Δ hΔ).le (material_budget Δ hΔ) hk hsym hdegree z hh hc hnoise h0 K T hT0 hT hK b i
  simpa only [material_allowance Δ hΔ] using h

theorem intermediate_primitive_drift_bound {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (hsafe : ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hT : t ≤ 4)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z)) (i : Fin n) :
    (∑ a, molecularRate r d k V (z (countPathIndex z t)).1 a*
      molecularIncrement r d k V (i,6) (z (countPathIndex z t)).1 a) ≤
      graphDiffusion k (fun j => countDriftPrimitive r d k V z K (j,6) t) i-
      (1+d i*(1+1/100)/(1/100))*(countDriftPrimitive r d k V z K (i,6) t-9/1000)+
      (2*Δ+126/25)*countTolerance Δ := by
  let X := fun j => countPath V z t (j,6)
  let F := fun j => countDriftPrimitive r d k V z K (j,6) t
  let c := fun s => countPath V z t (i,s)
  let κ := 1+d i*(1+1/100)/(1/100)
  have hε := (count_tolerance_positive Δ hΔ).le
  have hn : ∀ j, |X j-F j| ≤ countTolerance Δ := fun j =>
    (countPath_noise_after_material_no_exit r d k V Δ hV z hh hc hnoise hsafe K t ht hT hK (j,6)).le
  have hb := graph_killing_noise_bound k hk Δ (countTolerance Δ) κ hε
    (by dsimp [κ]; linarith [(kappa_bounds (d i) (hd i).1 (hd i).2).1]) hdegree
    (fun j => X j-F j) hn i
  rw [graphDiffusion_sub] at hb
  have hb' := (abs_le.mp hb).2
  have hκ := kappa_bounds (d i) (hd i).1 (hd i).2
  have hmul := mul_le_mul_of_nonneg_right hκ.2 hε
  have hcoord := fun s => countPath_coordinate_bound V hV z (fun j => (hh j).le) hsafe K t ht hT hK (i,s)
  have hf := forcing_bound c (fun s => (hcoord s).1) (hcoord 0).2 (hcoord 1).2 (hcoord 2).2
  have hg := forcing_gap (d i) (hd i).2
  have hforcing := mul_le_mul_of_nonneg_left hf (show 0 ≤ d i*(1+1/100) by linarith [(hd i).1])
  rw [molecular_drift_binding r d k V hV.ne' hsym,count_intermediate_filter]
  change d i*(1+1/100)*forcing (1/100) c-κ*X i+graphDiffusion k X i ≤
    graphDiffusion k F i-κ*(F i-9/1000)+(2*Δ+126/25)*countTolerance Δ
  dsimp [κ] at hb' ⊢
  nlinarith

theorem noise_amplification (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    countTolerance Δ*(1+((126/25)+2*Δ)/(151/50)) < 3/10000 := by
  unfold countTolerance relaxedTolerance
  have hp : 0 < 10000*(1+Δ) := by positivity
  rw [show 1/(10000*(1+Δ))*(1+((126/25)+2*Δ)/(151/50)) =
    (1+((126/25)+2*Δ)/(151/50))/(10000*(1+Δ)) by ring]
  apply (div_lt_iff₀ hp).mpr
  linarith

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
    countPath V z T (i,6) < 9/1000+(201/100000)*Real.exp (-(151/50)*T)+3/10000 := by
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
  change countTolerance Δ*(1+((126/25)+2*Δ)/(151/50)) < 3/10000 at he
  have hid : (2*Δ+126/25)*countTolerance Δ/(151/50)+countTolerance Δ =
      countTolerance Δ*(1+((126/25)+2*Δ)/(151/50)) := by ring
  linarith

theorem intermediate_envelope_margins (t x : ℝ) (ht : 0 ≤ t)
    (hx : x < 9/1000+(201/100000)*Real.exp (-(151/50)*t)+3/10000) :
    x < 1131/100000 ∧ (t=4 → x < 931/100000) := by
  have he : Real.exp (-(151/50)*t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  constructor
  · linarith
  · intro h4
    subst t
    have hm := intermediate_decay_four
    linarith

theorem countPath_free_material_lower {n : ℕ} (r d : Fin n → ℝ)
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
    94689/100000 ≤ ProductiveRecovery.A (free (fun s => countPath V z T (i,s))) ∧
    94689/100000 ≤ ProductiveRecovery.B (free (fun s => countPath V z T (i,s))) := by
  have ha := material_time_bound r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0 K T hT0 hT hK false i
  have hb := material_time_bound r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0 K T hT0 hT hK true i
  change |weightedCoordinate weightA (fun s => countPath V z T (i,s))-1| ≤ _ at ha
  change |weightedCoordinate weightB (fun s => countPath V z T (i,s))-1| ≤ _ at hb
  rw [← materialA_weighted] at ha
  rw [← materialB_weighted] at hb
  have he : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT0)
  have hda := (abs_le.mp ha).1
  have hdb := (abs_le.mp hb).1
  have hdi := intermediate_time_bound r d k V Δ hV hΔ hd hk hsym hdegree z hh hc hnoise h0 hD K T hT0 hT hK i
  have hbound := (intermediate_envelope_margins T _ hT0 hdi).1
  constructor
  · rw [materialA] at hda
    linarith
  · rw [materialB] at hdb
    linarith

end
end RAF1519.Refinement.Relaxed
