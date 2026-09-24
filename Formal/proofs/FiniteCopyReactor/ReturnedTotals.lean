import proofs.FiniteCopyReactor.ReturnedSupport

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

def returnedTotal (h : ReturnedHistory) (i : Fin 5) : ℝ := (h.map (fun X => (X.2 i:ℝ))).sum

theorem returned_total_lower (h : ReturnedHistory) (i : Fin 5) (a : ℝ)
    (ha : ∀ X ∈ h,a ≤ (X.2 i:ℝ)) : (h.length:ℝ)*a ≤ returnedTotal h i := by
  induction h with
  | nil => simp [returnedTotal]
  | cons X h ih =>
    have hx := ha X (List.mem_cons_self)
    have hh := ih (fun Y hy => ha Y (List.mem_cons_of_mem X hy))
    simp only [returnedTotal,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    change ((h.length:ℝ)+1)*a ≤ (X.2 i:ℝ)+returnedTotal h i
    nlinarith

theorem returned_total_upper (h : ReturnedHistory) (i : Fin 5) (a : ℝ)
    (ha : ∀ X ∈ h,(X.2 i:ℝ) ≤ a) : returnedTotal h i ≤ (h.length:ℝ)*a := by
  induction h with
  | nil => simp [returnedTotal]
  | cons X h ih =>
    have hx := ha X (List.mem_cons_self)
    have hh := ih (fun Y hy => ha Y (List.mem_cons_of_mem X hy))
    simp only [returnedTotal,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    change (X.2 i:ℝ)+returnedTotal h i ≤ ((h.length:ℝ)+1)*a
    nlinarith

theorem returned_joint_totals (V n : ℕ) (h : ReturnedHistory) (hh : h ∈ returnedFinal V n) :
    (n:ℝ)*(Nat.ceil ((V:ℝ)/56):ℝ) ≤ returnedTotal h 1 ∧
    (n:ℝ)*(Nat.ceil ((V:ℝ)/1080):ℝ) ≤ returnedTotal h 0 ∧
    returnedTotal h 2 ≤ (n:ℝ)*(5*(V:ℝ)) ∧ returnedTotal h 3 ≤ (n:ℝ)*(5*(V:ℝ)) ∧
    returnedTotal h 4 ≤ (n:ℝ)*(Nat.floor ((V:ℝ)/5):ℝ) := by
  obtain ⟨hlen,hgood⟩ := hh
  constructor
  · simpa only [hlen] using returned_total_lower h 1 _ (fun X hx => (hgood X hx).2.1)
  constructor
  · simpa only [hlen] using returned_total_lower h 0 _ (fun X hx => (hgood X hx).2.2.1)
  constructor
  · simpa only [hlen] using returned_total_upper h 2 _ (fun X hx => (hgood X hx).2.2.2.1)
  constructor
  · simpa only [hlen] using returned_total_upper h 3 _ (fun X hx => (hgood X hx).2.2.2.2.1)
  · simpa only [hlen] using returned_total_upper h 4 _ (fun X hx => (hgood X hx).2.2.2.2.2)

/-- All cycles succeed jointly under the full, normalized process law. -/
theorem full_returned_history_success (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) (hscale : 200000000000 ≤ V) (hN : Restart V N) (n : ℕ) :
    ENNReal.ofReal (1-(n:ℝ)*oneCycleError V) ≤
      fullHistoryKernel (returnedHistoryStep N V r d hV (by linarith) hd policy) n [] (returnedFinal V n) := by
  have hs := returned_history_success_lower N V r d hV hr hr' hd hd' policy hscale hN n
  apply hs.trans
  apply successful_history_event_lower _ _ _ n [] (returnedFinal V n) (Set.to_countable _).measurableSet
  simpa only [List.length_nil,Nat.zero_add] using
    returned_success_support N V r d hV (by linarith) hd policy n [] (by simp [returnedGood])

end
end FiniteCopyReactor
