import proofs.RAF1519.Refinement.MaterialEndpoint
import proofs.RAF1519.Refinement.StrictWaiting
import proofs.RAF1519.Refinement.CompensatedMaterial

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

theorem material_prefix_bound {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (j : ℕ) (hT : prefixElapsed j (Preorder.frestrictLe j z) ≤ 4)
    (hprev : ∀ l < j, materialSafe V (z l).1) (b : Bool) (i : Fin n) :
    |materialNode b V (z j).1 i-1| ≤
      (1/25)*Real.exp (-prefixElapsed j (Preorder.frestrictLe j z))+18/100000 := by
  have hh0 : ∀ l, 0 ≤ (z (l+1)).2.2 := fun l => (hh l).le
  have heps := (count_tolerance_positive Δ hΔ).le
  have hclock := holdingClock_strictMono (fun l => (z (l+1)).2.2) hh
  have htime0 : 0 ≤ prefixElapsed j (Preorder.frestrictLe j z) := by
    exact (holdingClock_monotone _ hh0 (Nat.zero_le j))
  have hs : ∀ l < j, ¬coordinateStop (countCorridor V) 4 (materialExit V) l (Preorder.frestrictLe l z) := by
    intro l hl
    apply material_unstopped V hV z l
    · exact (hclock hl).trans_le hT
    · intro q hq
      exact hprev q (lt_of_le_of_lt hq hl)
  have hpath : ∀ t ∈ Set.Ico 0 (prefixElapsed j (Preorder.frestrictLe j z)), ∀ p,
      |countPath V z t p-countDriftPrimitive r d k V z j p t| ≤ countTolerance Δ := by
    intro t ht p
    have hi := countPathIndex_spec z hh0 j t ht.1 ht.2
    exact (countPath_primitive_noise r d k V Δ (materialExit V) z hh0 hc hnoise j t ht.1
      (ht.2.le.trans hT) ht.2 (fun l hl => hs l (lt_of_le_of_lt hl hi.1)) p).le
  have hF := compensated_material_primitive_bound k hk hsym Δ (9*countTolerance Δ) hΔ
    (by positivity) hdegree (countMaterial b V z) (materialPrimitive b r d k V z j)
    (fun t q => 1-countMaterial b V z t q+graphDiffusion k (countMaterial b V z t) q)
    (prefixElapsed j (Preorder.frestrictLe j z)) (1/25)
    (fun q => (materialPrimitive_continuous b r d k V z j q).continuousOn)
    (fun t ht q => materialPrimitive_right_derivative b r d k V hV.ne' hsym z hh0 j q t ht.1 ht.2)
    (fun q => by rw [materialPrimitive_zero b r d k V z hh0 j]; exact h0 b q)
    (fun _ _ _ => rfl)
    (fun t ht q => material_noise_from_coordinates b _ _ _ heps (fun s => hpath t ht (q,s)))
    _ ⟨htime0,le_rfl⟩ i
  have hE : |materialNode b V (z j).1 i-materialPrimitive b r d k V z j
      (prefixElapsed j (Preorder.frestrictLe j z)) i| ≤ 9*countTolerance Δ :=
    material_noise_from_coordinates b _ _ _ heps
      (fun s => (count_endpoint_noise r d k V Δ z hh0 hc hnoise j j le_rfl hT hs (i,s)).le)
  have hb := material_observed_from_primitive _ _ _ _ _ _ hF hE
  have he : (2*Δ+1)*(9*countTolerance Δ)+9*countTolerance Δ = 18/100000 := by
    unfold countTolerance
    have hn : 1+Δ ≠ 0 := by positivity
    field_simp
    ring
  rw [add_assoc,he] at hb
  exact hb

/-- Strong induction excludes the first exit, including a jump at the deadline. -/
theorem material_no_exit {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25) :
    ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hT b i
    have hprev : ∀ l < j, materialSafe V (z l).1 := by
      intro l hl
      exact ih l hl ((holdingClock_monotone _ (fun q => (hh q).le) hl.le).trans hT)
    have hb := material_prefix_bound r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0 j hT hprev b i
    have ht0 : 0 ≤ prefixElapsed j (Preorder.frestrictLe j z) :=
      holdingClock_monotone _ (fun q => (hh q).le) (Nat.zero_le j)
    have hex : Real.exp (-prefixElapsed j (Preorder.frestrictLe j z)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht0)
    linarith

end
end RAF1519.Refinement
