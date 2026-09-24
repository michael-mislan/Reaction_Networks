import proofs.RAF1519.Refinement.NaturalMarks
import proofs.RAF1519.Refinement.IntegerThresholds
import proofs.RAF1519.Refinement.OperatingEvent
import proofs.RAF1519.Refinement.PulseRefill

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

def integerCycleSuccess {n : ℕ} (V : ℕ) (p : Fin n → Intervention)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) : Prop :=
  ∀ i, Ready (1/100) (fun s => countPath V z 4 (i,s)) ∧
    ⌈(V:ℝ)/56⌉₊ ≤ naturalMarkedWindow i .inventory z 3 4 ∧
    ⌈(V:ℝ)/1080⌉₊ ≤ naturalMarkedWindow i .freeX z 3 4 ∧
    naturalMarkedWindow i .foodU z 0 4+pulseDose V (p i) 0 ≤ 5*V ∧
    naturalMarkedWindow i .foodW z 0 4+pulseDose V (p i) 1 ≤ 5*V ∧
    naturalMarkedWindow i .service z 0 4 ≤ ⌊(V:ℝ)/5⌋₊

theorem integerCycleSuccess_of_operating {n : ℕ} (V : ℕ) (hV : 0 < (V:ℝ))
    (p : Fin n → Intervention) (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ j, 0 ≤ (z (j+1)).2.2) (K : ℕ)
    (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z)) (hs : operatingSuccess V z) :
    integerCycleSuccess V p z := by
  have he : ∀ i m a, 0 ≤ a → a ≤ 4 →
      markedWindow V i m z a 4=(naturalMarkedWindow i m z a 4:ℝ)/(V:ℝ) := by
    intro i m a ha hab
    exact markedWindow_natural V i m z hh K a 4 ha hab hK
  intro i
  obtain ⟨hr,hI,hX,hU,hW,hG⟩ := hs i
  rw [he i .inventory 3 (by norm_num) (by norm_num)] at hI
  rw [he i .freeX 3 (by norm_num) (by norm_num)] at hX
  rw [he i .foodU 0 (by norm_num) (by norm_num)] at hU
  rw [he i .foodW 0 (by norm_num) (by norm_num)] at hW
  rw [he i .service 0 (by norm_num) (by norm_num)] at hG
  exact ⟨hr,collection_inventory_integer V _ hV hI,collection_freeX_integer V _ hV hX,
    pulse_food_integer V _ _ hV hU (pulseDose_budget V (p i) 0),
    pulse_food_integer V _ _ hV hW (pulseDose_budget V (p i) 1),gross_service_integer V _ hV hG⟩

end
end RAF1519.Refinement
