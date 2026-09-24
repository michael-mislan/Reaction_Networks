import proofs.RAF1519.Refinement.NoiseBudget
import proofs.RAF1519.Refinement.MaterialTime

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

theorem countPath_noise_at {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V ε : ℝ)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ intervalFailureAt r d k V ε p stop)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hT : t ≤ 4)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z))
    (hs : ∀ i ≤ countPathIndex z t, ¬coordinateStop (countCorridor V) 4 stop i (Preorder.frestrictLe i z))
    (p : Fin n × Fin 7) :
    |countPath V z t p-countDriftPrimitive r d k V z K p t| < ε := by
  let j := countPathIndex z t
  let s := t-prefixElapsed j (Preorder.frestrictLe j z)
  have hi := countPathIndex_spec z hh K t ht hK
  have hs0 : 0 ≤ s := sub_nonneg.mpr hi.2.1
  have hsh : s ≤ min (z (j+1)).2.2 (4-prefixElapsed j (Preorder.frestrictLe j z)) := by
    apply le_min
    · dsimp [s,j]
      linarith [hi.2.2]
    · exact sub_le_sub_right hT _
  have he := count_minus_compensation_primitive r d k V 4 p (countCorridor V) stop z hh
    K j hi.1 t hT hi.2.1 hi.2.2 (fun i _ => hc i) hs
  have hb : |coordinateWithin (molecularRate r d k V) (molecularIncrement r d k V p)
      (countCorridor V) 4 stop z j s| < ε := by
    apply lt_of_not_ge
    intro hcross
    exact hnoise p ⟨j,s,hs0,hsh,hcross⟩
  have heq : countPath V z t p-countDriftPrimitive r d k V z K p t =
      coordinateWithin (molecularRate r d k V) (molecularIncrement r d k V p)
        (countCorridor V) 4 stop z j s := by
    change ((z j).1 p:ℝ)/V-countDriftPrimitive r d k V z K p t = _
    linarith
  rw [heq]
  exact hb

theorem count_endpoint_noise_at {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V ε : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ intervalFailureAt r d k V ε p (materialExit V))
    (K j : ℕ) (hj : j ≤ K) (hT : prefixElapsed j (Preorder.frestrictLe j z) ≤ 4)
    (hs : ∀ i < j, ¬coordinateStop (countCorridor V) 4 (materialExit V) i (Preorder.frestrictLe i z))
    (p : Fin n × Fin 7) :
    |((z j).1 p:ℝ)/V-countDriftPrimitive r d k V z K p
      (prefixElapsed j (Preorder.frestrictLe j z))| < ε := by
  have he := count_endpoint_primitive r d k V 4 p (countCorridor V) (materialExit V)
    z hh K j hj hT (fun i _ => hc i) hs
  have hb : |coordinatePrefix (molecularRate r d k V) (molecularIncrement r d k V p)
      (countCorridor V) 4 (materialExit V) z j| < ε := by
    apply lt_of_not_ge
    intro hcross
    apply hnoise p
    refine ⟨j,0,le_rfl,le_min (hh j) (sub_nonneg.mpr hT),?_⟩
    simpa only [coordinateWithin,mul_zero,sub_zero,ite_self] using hcross
  have heq : ((z j).1 p:ℝ)/V-countDriftPrimitive r d k V z K p
      (prefixElapsed j (Preorder.frestrictLe j z)) =
      coordinatePrefix (molecularRate r d k V) (molecularIncrement r d k V p)
        (countCorridor V) 4 (materialExit V) z j := by linarith
  rw [heq]
  exact hb

theorem noise_after_material_at {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V ε : ℝ) (hV : 0 < V)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ intervalFailureAt r d k V ε p (materialExit V))
    (hsafe : ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hT : t ≤ 4)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z)) (p : Fin n × Fin 7) :
    |countPath V z t p-countDriftPrimitive r d k V z K p t| < ε := by
  have hh0 := fun i => (hh i).le
  have hi := countPathIndex_spec z hh0 K t ht hK
  have hm := holdingClock_monotone (fun i => (z (i+1)).2.2) hh0
  have hj4 := hi.2.1.trans hT
  have hstop : ∀ q, prefixElapsed q (Preorder.frestrictLe q z) < 4 →
      ¬coordinateStop (countCorridor V) 4 (materialExit V) q (Preorder.frestrictLe q z) := by
    intro q hq
    exact material_unstopped V hV z q hq (fun l hl => hsafe l ((hm hl).trans hq.le))
  by_cases hj : prefixElapsed (countPathIndex z t) (Preorder.frestrictLe (countPathIndex z t) z) < 4
  · exact countPath_noise_at r d k V ε (materialExit V) z hh0 hc hnoise K t ht hT hK
      (fun q hq => hstop q ((hm hq).trans_lt hj)) p
  · have he : prefixElapsed (countPathIndex z t) (Preorder.frestrictLe (countPathIndex z t) z)=t := by linarith
    have hs : ∀ q < countPathIndex z t,
        ¬coordinateStop (countCorridor V) 4 (materialExit V) q (Preorder.frestrictLe q z) := by
      intro q hq
      exact hstop q ((holdingClock_strictMono _ hh hq).trans_le hj4)
    have hb := count_endpoint_noise_at r d k V ε z hh0 hc hnoise K (countPathIndex z t) hi.1.le hj4 hs p
    rw [he] at hb
    exact hb

theorem material_prefix_budget {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ ε : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ intervalFailureAt r d k V ε p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (j : ℕ) (hT : prefixElapsed j (Preorder.frestrictLe j z) ≤ 4)
    (hprev : ∀ l < j, materialSafe V (z l).1) (b : Bool) (i : Fin n) :
    |materialNode b V (z j).1 i-1| ≤
      (1/25)*Real.exp (-prefixElapsed j (Preorder.frestrictLe j z))+18*(1+Δ)*ε := by
  have hh0 : ∀ l, 0 ≤ (z (l+1)).2.2 := fun l => (hh l).le
  have heps := hε
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
      |countPath V z t p-countDriftPrimitive r d k V z j p t| ≤ ε := by
    intro t ht p
    have hi := countPathIndex_spec z hh0 j t ht.1 ht.2
    exact (countPath_noise_at r d k V ε (materialExit V) z hh0 hc hnoise j t ht.1
      (ht.2.le.trans hT) ht.2 (fun l hl => hs l (lt_of_le_of_lt hl hi.1)) p).le
  have hF := compensated_material_primitive_bound k hk hsym Δ (9*ε) hΔ
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
      (prefixElapsed j (Preorder.frestrictLe j z)) i| ≤ 9*ε :=
    material_noise_from_coordinates b _ _ _ heps
      (fun s => (count_endpoint_noise_at r d k V ε z hh0 hc hnoise j j le_rfl hT hs (i,s)).le)
  have hb := material_observed_from_primitive _ _ _ _ _ _ hF hE
  have he : (2*Δ+1)*(9*ε)+9*ε = 18*(1+Δ)*ε := by
    ring
  rw [add_assoc,he] at hb
  exact hb

theorem material_no_exit_budget {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ ε : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε) (hbudget : 18*(1+Δ)*ε ≤ 1/20)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ intervalFailureAt r d k V ε p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25) :
    ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hT b i
    have hprev : ∀ l < j, materialSafe V (z l).1 := by
      intro l hl
      exact ih l hl ((holdingClock_monotone _ (fun q => (hh q).le) hl.le).trans hT)
    have hb := material_prefix_budget r d k V Δ ε hV hΔ hε hk hsym hdegree z hh hc hnoise h0 j hT hprev b i
    have ht0 : 0 ≤ prefixElapsed j (Preorder.frestrictLe j z) :=
      holdingClock_monotone _ (fun q => (hh q).le) (Nat.zero_le j)
    have hex : Real.exp (-prefixElapsed j (Preorder.frestrictLe j z)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht0)
    linarith

theorem material_time_budget {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ ε : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε) (hbudget : 18*(1+Δ)*ε ≤ 1/20)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ intervalFailureAt r d k V ε p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (K : ℕ) (T : ℝ) (hT0 : 0 ≤ T) (hT : T ≤ 4)
    (hK : T < prefixElapsed K (Preorder.frestrictLe K z)) (b : Bool) (i : Fin n) :
    |countMaterial b V z T i-1| ≤ (1/25)*Real.exp (-T)+18*(1+Δ)*ε := by
  have hh0 := fun i => (hh i).le
  have heps := hε
  have hsafe := material_no_exit_budget r d k V Δ ε hV hΔ hε hbudget hk hsym hdegree z hh hc hnoise h0
  have hpath : ∀ t ∈ Set.Icc 0 T, ∀ q,
      |countMaterial b V z t q-materialPrimitive b r d k V z K t q| ≤ 9*ε := by
    intro t ht q
    exact material_noise_from_coordinates b _ _ _ heps (fun s =>
      (noise_after_material_at r d k V ε hV z hh hc hnoise hsafe K t ht.1
        (ht.2.trans hT) (ht.2.trans_lt hK) (q,s)).le)
  have hF := compensated_material_primitive_bound k hk hsym Δ (9*ε) hΔ
    (by positivity) hdegree (countMaterial b V z) (materialPrimitive b r d k V z K)
    (fun t q => 1-countMaterial b V z t q+graphDiffusion k (countMaterial b V z t) q) T (1/25)
    (fun q => (materialPrimitive_continuous b r d k V z K q).continuousOn)
    (fun t ht q => materialPrimitive_right_derivative b r d k V hV.ne' hsym z hh0 K q t ht.1 (ht.2.trans hK))
    (fun q => by rw [materialPrimitive_zero b r d k V z hh0 K]; exact h0 b q)
    (fun _ _ _ => rfl) (fun t ht q => hpath t ⟨ht.1,ht.2.le⟩ q) T ⟨hT0,le_rfl⟩ i
  have hb := material_observed_from_primitive _ _ _ _ _ _ hF (hpath T ⟨hT0,le_rfl⟩ i)
  have he : (2*Δ+1)*(9*ε)+9*ε = 18*(1+Δ)*ε := by
    ring
  rw [add_assoc,he] at hb
  exact hb

end
end RAF1519.Refinement
