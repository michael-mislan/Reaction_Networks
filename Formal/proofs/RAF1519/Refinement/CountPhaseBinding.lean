import proofs.RAF1519.Refinement.SharpPhase
import proofs.RAF1519.Refinement.CountStockFence
import proofs.RAF1519.Refinement.PhaseWindow

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

def phaseSpecies (p : Fin 4) : Fin 7 :=
  match p.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | _ => 5

theorem phaseDot_stock (c : State) :
    phaseDot phaseWeight (fun p => c (phaseSpecies p)) = stock c := by
  change (∑ p : Fin 4, phaseWeight p*c (phaseSpecies p)) = c 2+(9/8)*c 3+(7/5)*c 4+(9/5)*c 5
  rw [Fin.sum_univ_four]
  change 1*c 2+(9/8)*c 3+(7/5)*c 4+(9/5)*c 5 = _
  ring

theorem materialSafe_material_upper {n : ℕ} (V : ℝ) (N : MolecularState n)
    (hs : materialSafe V N) (i : Fin n) :
    materialA (concentration V (fun s => N (i,s))) ≤ 11/10 ∧
    materialB (concentration V (fun s => N (i,s))) ≤ 11/10 := by
  have ha := (abs_le.mp (hs false i)).2
  have hb := (abs_le.mp (hs true i)).2
  change weightedCoordinate weightA (concentration V (fun s => N (i,s)))-1 ≤ _ at ha
  change weightedCoordinate weightB (concentration V (fun s => N (i,s)))-1 ≤ _ at hb
  rw [← materialA_weighted] at ha
  rw [← materialB_weighted] at hb
  constructor <;> linarith

theorem count_phase_matrix_lower (r d V : ℝ) (N : Fin 7 → ℕ) (hV : 0 < V)
    (hr : 19 ≤ r ∧ r ≤ 21) (hd : 1/50 ≤ d ∧ d ≤ 1/25)
    (hA : materialA (concentration V N) ≤ 11/10)
    (hB : materialB (concentration V N) ≤ 11/10) (p : Fin 4) :
    (∑ q, phaseM p q*concentration V N (phaseSpecies q)) ≤
      countDrift r d (1/100) (1/100) V (concentration V N) (phaseSpecies p) := by
  obtain ⟨h1,h2,h3,h4⟩ := count_sharp_phase r d V N hV hr.1 hr.2 (by linarith [hd.1]) hd.2 hA hB
  let c := concentration V N
  rw [Fin.sum_univ_four]
  fin_cases p
  · change (0-48)*c 2+(20-0)*c 3+(0-0)*c 4+(38-0)*c 5 ≤ countDrift r d (1/100) (1/100) V c 2
    linarith
  · change (0-0)*c 2+(5-48)*c 3+(20-0)*c 4+(0-0)*c 5 ≤ countDrift r d (1/100) (1/100) V c 3
    linarith
  · change (0-0)*c 2+(0-0)*c 3+(7-48)*c 4+(2-0)*c 5 ≤ countDrift r d (1/100) (1/100) V c 4
    linarith
  · change (0-0)*c 2+(0-0)*c 3+(20-0)*c 4+(24-48)*c 5 ≤ countDrift r d (1/100) (1/100) V c 5
    linarith

theorem count_phase_path_drift {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : 0 < V)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hsym : ∀ i j, k i j=k j i)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (hsafe : ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hT : t ≤ 4)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z)) (i : Fin n) (p : Fin 4) :
    (∑ q, phaseM p q*countPath V z t (i,phaseSpecies q))+
      graphDiffusion k (fun j => countPath V z t (j,phaseSpecies p)) i ≤
      ∑ a, molecularRate r d k V (z (countPathIndex z t)).1 a*
        molecularIncrement r d k V (i,phaseSpecies p) (z (countPathIndex z t)).1 a := by
  have hi := countPathIndex_spec z hh K t ht hK
  have hm := materialSafe_material_upper V (z (countPathIndex z t)).1 (hsafe _ (hi.2.1.trans hT)) i
  have hp := count_phase_matrix_lower (r i) (d i) V (fun s => (z (countPathIndex z t)).1 (i,s))
    hV (hr i) (hd i) hm.1 hm.2 p
  rw [molecular_drift_binding r d k V hV.ne' hsym]
  change (∑ q, phaseM p q*countPath V z t (i,phaseSpecies q))+_ ≤
    countDrift (r i) (d i) (1/100) (1/100) V
      (concentration V (fun s => (z (countPathIndex z t)).1 (i,s))) (phaseSpecies p)+_
  change (∑ q, phaseM p q*countPath V z t (i,phaseSpecies q)) ≤ _ at hp
  exact add_le_add hp le_rfl

theorem countPrimitive_shift_derivative {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K : ℕ) (a s : ℝ) (ht : 0 ≤ a+s)
    (hK : a+s < prefixElapsed K (Preorder.frestrictLe K z)) (p : Fin n × Fin 7) :
    HasDerivWithinAt (fun u => countDriftPrimitive r d k V z K p (a+u))
      (∑ b, molecularRate r d k V (z (countPathIndex z (a+s))).1 b*
        molecularIncrement r d k V p (z (countPathIndex z (a+s))).1 b) (Set.Ici s) s := by
  have hd := countPrimitive_path_derivative r d k V z hh K p (a+s) ht hK
  have hshift : HasDerivWithinAt (fun u : ℝ => a+u) 1 (Set.Ici s) s := by
    simpa only [id_eq] using ((hasDerivAt_id s).const_add a).hasDerivWithinAt
  have hm : Set.MapsTo (fun u : ℝ => a+u) (Set.Ici s) (Set.Ici (a+s)) := by
    intro u hu
    change s ≤ u at hu
    change a+s ≤ a+u
    linarith
  simpa only [mul_one] using hd.comp s hshift hm

end
end RAF1519.Refinement
