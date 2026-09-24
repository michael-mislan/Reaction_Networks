import proofs.FiniteReservoir.ReturnedSupport

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

def returnedTotal {M : ℕ} (h : (ReturnedHistory M)) (i : Fin 5) : ℝ := (h.map (fun X => (X.2 i:ℝ))).sum

theorem returned_total_lower {M : ℕ} (h : (ReturnedHistory M)) (i : Fin 5) (a : ℝ)
    (ha : ∀ X ∈ h,a ≤ (X.2 i:ℝ)) : (h.length:ℝ)*a ≤ returnedTotal h i := by
  induction h with
  | nil => simp [returnedTotal]
  | cons X h ih =>
    have hx := ha X (List.mem_cons_self)
    have hh := ih (fun Y hy => ha Y (List.mem_cons_of_mem X hy))
    simp only [returnedTotal,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    change ((h.length:ℝ)+1)*a ≤ (X.2 i:ℝ)+returnedTotal h i
    nlinarith

theorem returned_total_upper {M : ℕ} (h : (ReturnedHistory M)) (i : Fin 5) (a : ℝ)
    (ha : ∀ X ∈ h,(X.2 i:ℝ) ≤ a) : returnedTotal h i ≤ (h.length:ℝ)*a := by
  induction h with
  | nil => simp [returnedTotal]
  | cons X h ih =>
    have hx := ha X (List.mem_cons_self)
    have hh := ih (fun Y hy => ha Y (List.mem_cons_of_mem X hy))
    simp only [returnedTotal,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    change (X.2 i:ℝ)+returnedTotal h i ≤ ((h.length:ℝ)+1)*a
    nlinarith

theorem returned_joint_totals (V M n : ℕ) (h : (ReturnedHistory M)) (hh : h ∈ returnedFinal V M n) :
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
theorem full_returned_history_success (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) 
    (policy : (ReturnedHistory M) → Intervention) (hscale : 200000000000 ≤ V) (hN : Restart V N.1) (n : ℕ) :
    ENNReal.ofReal (1-(n:ℝ)*oneCycleError V) ≤
      fullHistoryKernel (returnedHistoryStep M N V params hV policy) n [] (returnedFinal V M n) := by
  have hs := returned_history_success_lower M N V params hV policy hscale hN n
  apply hs.trans
  apply successful_history_event_lower _ _ _ n [] (returnedFinal V M n) (Set.to_countable _).measurableSet
  simpa only [List.length_nil,Nat.zero_add] using
    returned_success_support M N V params hV policy n [] (by simp [returnedGood])

end
end FiniteReservoir
