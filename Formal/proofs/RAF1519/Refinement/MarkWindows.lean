import proofs.RAF1519.Refinement.MarkPathNoise
import proofs.RAF1519.Refinement.CountOperatingIntegrals

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

/-- Differences of the actual cumulative rewards count jumps in (a,b]. -/
def markedWindow {n : ℕ} (V : ℝ) (i : Fin n) (m : PhysicalMark)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (a b : ℝ) : ℝ :=
  markPath V i m z b-markPath V i m z a

theorem markedWindow_noise {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (hV : V ≠ 0) (i : Fin n) (m : PhysicalMark)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ j, 0 < (z (j+1)).2.2)
    (hnoise : z ∉ markIntervalFailure r d k V i m (materialExit V))
    (hsafe : ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1)
    (K : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 4)
    (hK : b < prefixElapsed K (Preorder.frestrictLe K z)) :
    |markedWindow V i m z a b-
      (∫ t in a..b, markRate m (d i) (fun s => countPath V z t (i,s)))| < 1/1000 := by
  have hna := markPath_noise r d k V i m z hh hnoise hsafe K a ha (hab.trans hb) (hab.trans_lt hK)
  have hnb := markPath_noise r d k V i m z hh hnoise hsafe K b (ha.trans hab) hb hK
  rw [mark_primitive_integral r d k V hV i m z (fun j => (hh j).le) K a b ha hab hK]
  have he : markedWindow V i m z a b-
      (markPrimitive r d k V i m z K b-markPrimitive r d k V i m z K a) =
      (markPath V i m z b-markPrimitive r d k V i m z K b)-
      (markPath V i m z a-markPrimitive r d k V i m z K a) := by
    unfold markedWindow
    ring
  rw [he]
  have hh := abs_sub (markPath V i m z b-markPrimitive r d k V i m z K b)
    (markPath V i m z a-markPrimitive r d k V i m z K a)
  unfold markTolerance at hna hnb
  linarith

/-- Transfer the proved operating compensators to the actual collection and service labels. -/
theorem marked_operating_outputs {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (hV : V ≠ 0) (i : Fin n)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ j, 0 < (z (j+1)).2.2)
    (hnoise : ∀ m, z ∉ markIntervalFailure r d k V i m (materialExit V))
    (hsafe : ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1)
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z))
    (hI : 4/100 ≤ countOutputI V z i) (hX : 7/1000 ≤ countOutputX V z i)
    (hS : countTotalService d V z i ≤ 9/50) :
    39/1000 ≤ markedWindow V i .inventory z 3 4 ∧
    6/1000 ≤ markedWindow V i .freeX z 3 4 ∧
    markedWindow V i .foodU z 0 4 ≤ 4001/1000 ∧
    markedWindow V i .foodW z 0 4 ≤ 4001/1000 ∧
    markedWindow V i .service z 0 4 ≤ 181/1000 := by
  have hi := markedWindow_noise r d k V hV i .inventory z hh (hnoise _) hsafe K 3 4
    (by norm_num) (by norm_num) le_rfl hK
  have hx := markedWindow_noise r d k V hV i .freeX z hh (hnoise _) hsafe K 3 4
    (by norm_num) (by norm_num) le_rfl hK
  have hu := markedWindow_noise r d k V hV i .foodU z hh (hnoise _) hsafe K 0 4
    (by norm_num) (by norm_num) le_rfl hK
  have hw := markedWindow_noise r d k V hV i .foodW z hh (hnoise _) hsafe K 0 4
    (by norm_num) (by norm_num) le_rfl hK
  have hs := markedWindow_noise r d k V hV i .service z hh (hnoise _) hsafe K 0 4
    (by norm_num) (by norm_num) le_rfl hK
  change |markedWindow V i .inventory z 3 4-countOutputI V z i| < 1/1000 at hi
  change |markedWindow V i .freeX z 3 4-countOutputX V z i| < 1/1000 at hx
  change |markedWindow V i .service z 0 4-countTotalService d V z i| < 1/1000 at hs
  norm_num [markRate] at hu hw
  obtain ⟨hi1,hi2⟩ := abs_lt.mp hi
  obtain ⟨hx1,hx2⟩ := abs_lt.mp hx
  obtain ⟨hu1,hu2⟩ := abs_lt.mp hu
  obtain ⟨hw1,hw2⟩ := abs_lt.mp hw
  obtain ⟨hs1,hs2⟩ := abs_lt.mp hs
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

end
end RAF1519.Refinement
