import proofs.FiniteCopyReactor.Resolution

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding

def templateInteger (N : Counts) : ℕ := N 2+N 3+N 4+2*N 5

theorem template_integer_cast (N : Counts) : (templateInteger N:ℝ)=templateStock N := by
  simp [templateInteger,templateStock]

theorem restart_final_inventory {V : ℕ} {N : Counts} (hN : Restart V N) :
    (Nat.ceil ((V:ℝ)/28):ℝ) ≤ templateStock N := by
  have hs := hN.2.2.2.2
  have hc : stockInteger N ≤ 56*templateInteger N := by
    unfold stockInteger templateInteger
    omega
  have hr : (2:ℝ)*V ≤ 56*(templateInteger N:ℝ) := by exact_mod_cast hs.trans hc
  have hh : (V:ℝ)/28 ≤ (templateInteger N:ℝ) := by linarith
  have hi : Nat.ceil ((V:ℝ)/28) ≤ templateInteger N := Nat.ceil_le.mpr hh
  rw [← template_integer_cast]
  exact_mod_cast hi

theorem returned_final_restart {N : Counts} {V n : ℕ} {h : ReturnedHistory}
    (hN : Restart V N) (hh : h ∈ returnedFinal V n) : Restart V (returnedObservation N h).1 := by
  cases h with
  | nil => exact hN
  | cons X h => exact (hh.2 X List.mem_cons_self).1

theorem HistoryTrace.sharp_inventory {N V policy h} (tr : HistoryTrace N V policy h)
    (n : ℕ) (hN : Restart V N) (hh : h ∈ returnedFinal V n) :
    (n:ℝ)*(Nat.ceil ((V:ℝ)/56):ℝ)+(Nat.ceil ((V:ℝ)/28):ℝ)-templateStock N ≤ tr.produced := by
  have hi := tr.inventory_lower
  have hf := restart_final_inventory (returned_final_restart hN hh)
  have ht := (returned_joint_totals V n h hh).1
  linarith

theorem HistoryTrace.sharp_uniform_integer {N V policy h} (tr : HistoryTrace N V policy h)
    (n : ℕ) (hN : Restart V N) (hh : h ∈ returnedFinal V n) :
    (n:ℝ)*(Nat.ceil ((V:ℝ)/56):ℝ)+(Nat.ceil ((V:ℝ)/28):ℝ)-
      (Nat.floor (161*(V:ℝ)/160):ℝ) ≤ tr.produced := by
  have hi := (templateStock_le_uCount N).trans hN.2.1
  rw [← template_integer_cast] at hi
  have hf : templateInteger N ≤ Nat.floor (161*(V:ℝ)/160) := Nat.le_floor hi
  have hf' : templateStock N ≤ (Nat.floor (161*(V:ℝ)/160):ℝ) := by
    rw [← template_integer_cast]; exact_mod_cast hf
  linarith [tr.sharp_inventory n hN hh]

theorem HistoryTrace.sharp_uniform_real {N V policy h} (tr : HistoryTrace N V policy h)
    (n : ℕ) (hN : Restart V N) (hh : h ∈ returnedFinal V n) :
    (((n:ℝ)+2)/56-161/160)*(V:ℝ) ≤ tr.produced := by
  have hp := tr.sharp_inventory n hN hh
  have hi := (templateStock_le_uCount N).trans hN.2.1
  have hc := mul_le_mul_of_nonneg_left (Nat.le_ceil ((V:ℝ)/56)) (Nat.cast_nonneg (α:=ℝ) n)
  have hf := Nat.le_ceil ((V:ℝ)/28)
  nlinarith

theorem HistoryTrace.positive_after_55 {N V policy h} (tr : HistoryTrace N V policy h)
    (n : ℕ) (hn : 55 ≤ n) (hV : 0 < V) (hN : Restart V N) (hh : h ∈ returnedFinal V n) :
    0 < tr.produced := by
  have hp := tr.sharp_uniform_real n hN hh
  have hn' : (55:ℝ) ≤ n := by exact_mod_cast hn
  have hv : 0 < (V:ℝ) := by exact_mod_cast hV
  nlinarith

theorem HistoryTrace.rich_two_cycle {N V policy h} (tr : HistoryTrace N V policy h)
    (hN : Restart V N) (hh : h ∈ returnedFinal V 2) (hi : templateStock N=(8/125)*(V:ℝ)) :
    (13/1750)*(V:ℝ) ≤ tr.produced := by
  have hp := tr.sharp_inventory 2 hN hh
  have hc := Nat.le_ceil ((V:ℝ)/56)
  have hf := Nat.le_ceil ((V:ℝ)/28)
  norm_num only [Nat.cast_ofNat] at hp
  rw [hi] at hp
  linarith

theorem HistoryTrace.hundred_uniform_integer {N policy h}
    (tr : HistoryTrace N 200000000000 policy h) (hN : Restart 200000000000 N)
    (hh : h ∈ returnedFinal 200000000000 100) : 163035714343 ≤ tr.produced := by
  have hp := tr.sharp_uniform_integer 100 hN hh
  norm_num at hp
  exact hp

theorem HistoryTrace.hundred_rich_integer {N policy h}
    (tr : HistoryTrace N 200000000000 policy h) (hN : Restart 200000000000 N)
    (hh : h ∈ returnedFinal 200000000000 100) (hi : templateStock N=12800000000) :
    351485714343 ≤ tr.produced := by
  have hp := tr.sharp_inventory 100 hN hh
  rw [hi] at hp
  norm_num at hp
  exact hp

end
end FiniteCopyReactor
