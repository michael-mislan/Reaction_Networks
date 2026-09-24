import proofs.FiniteReservoir.Mission
import proofs.FiniteCopyReactor.SynthesisCorollaries

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery FiniteCopyReactor RandomViability.Binding

theorem returned_final_restart {M : ℕ} {N : CountState M} {V n : ℕ}
    {h : ReturnedHistory M} (hN : Restart V N.1) (hh : h ∈ returnedFinal V M n) :
    Restart V (returnedObservation N h).1.1 := by
  cases h with
  | nil => exact hN
  | cons X h => exact (hh.2 X List.mem_cons_self).1

theorem HistoryTrace.sharp_inventory {M N V policy h} (tr : HistoryTrace M N V policy h)
    (n : ℕ) (hN : Restart V N.1) (hh : h ∈ returnedFinal V M n) :
    (n:ℝ)*(Nat.ceil ((V:ℝ)/56):ℝ)+(Nat.ceil ((V:ℝ)/28):ℝ)-templateStock N.1 ≤ tr.produced := by
  have hi := tr.inventory_lower
  have hf := restart_final_inventory (returned_final_restart hN hh)
  have ht := (returned_joint_totals V M n h hh).1
  linarith

theorem HistoryTrace.sharp_uniform_integer {M N V policy h} (tr : HistoryTrace M N V policy h)
    (n : ℕ) (hN : Restart V N.1) (hh : h ∈ returnedFinal V M n) :
    (n:ℝ)*(Nat.ceil ((V:ℝ)/56):ℝ)+(Nat.ceil ((V:ℝ)/28):ℝ)-
      (Nat.floor (161*(V:ℝ)/160):ℝ) ≤ tr.produced := by
  have hi := (templateStock_le_uCount N.1).trans hN.2.1
  rw [← template_integer_cast] at hi
  have hf : templateInteger N.1 ≤ Nat.floor (161*(V:ℝ)/160) := Nat.le_floor hi
  have hf' : templateStock N.1 ≤ (Nat.floor (161*(V:ℝ)/160):ℝ) := by
    rw [← template_integer_cast]; exact_mod_cast hf
  linarith [tr.sharp_inventory n hN hh]

theorem HistoryTrace.sharp_uniform_real {M N V policy h} (tr : HistoryTrace M N V policy h)
    (n : ℕ) (hN : Restart V N.1) (hh : h ∈ returnedFinal V M n) :
    (((n:ℝ)+2)/56-161/160)*(V:ℝ) ≤ tr.produced := by
  have hp := tr.sharp_inventory n hN hh
  have hi := (templateStock_le_uCount N.1).trans hN.2.1
  have hc := mul_le_mul_of_nonneg_left (Nat.le_ceil ((V:ℝ)/56)) (Nat.cast_nonneg (α:=ℝ) n)
  have hf := Nat.le_ceil ((V:ℝ)/28)
  nlinarith

theorem HistoryTrace.positive_after_55 {M N V policy h} (tr : HistoryTrace M N V policy h)
    (n : ℕ) (hn : 55 ≤ n) (hV : 0 < V) (hN : Restart V N.1) (hh : h ∈ returnedFinal V M n) :
    0 < tr.produced := by
  have hp := tr.sharp_uniform_real n hN hh
  have hn' : (55:ℝ) ≤ n := by exact_mod_cast hn
  have hv : 0 < (V:ℝ) := by exact_mod_cast hV
  nlinarith

theorem HistoryTrace.hundred_all_free {M N policy h}
    (tr : HistoryTrace M N 200000000000 policy h) (hN : Restart 200000000000 N.1)
    (hh : h ∈ returnedFinal 200000000000 M 100) (hi : templateStock N.1=200000000000) :
    164285714343 ≤ tr.produced := by
  have hp := tr.sharp_inventory 100 hN hh
  rw [hi] at hp
  norm_num at hp
  exact hp

end
end FiniteReservoir
