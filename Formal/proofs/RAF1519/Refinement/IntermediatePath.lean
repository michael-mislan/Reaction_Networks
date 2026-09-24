import proofs.RAF1519.Refinement.MaterialTime
import proofs.RAF1519.Refinement.GraphDampedUpper

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

theorem count_intermediate_filter (r d V : ℝ) (c : State) :
    countDrift r d (1/100) (1/100) V c 6 =
      d*(1+1/100)*forcing (1/100) c-(1+d*(1+1/100)/(1/100))*c 6 := by
  rw [count_drift_correction]
  change field r d (1/100) (1/100) c 6+0 = _
  rw [add_zero]
  exact intermediate_filter r d (1/100) (1/100) c (by norm_num)

theorem countPath_coordinate_bound {n : ℕ} (V : ℝ) (hV : 0 < V)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (hsafe : ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hT : t ≤ 4)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z)) (p : Fin n × Fin 7) :
    0 ≤ countPath V z t p ∧ countPath V z t p ≤ 11/10 := by
  have hi := countPathIndex_spec z hh K t ht hK
  exact ⟨div_nonneg (Nat.cast_nonneg _) hV.le,
    materialSafe_coordinate V hV _ (hsafe _ (hi.2.1.trans hT)) p⟩

/-- The intermediate primitive inherits its source forcing ceiling with the
    graph noise paid explicitly; its observed path need not be differentiable. -/
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

end
end RAF1519.Refinement
