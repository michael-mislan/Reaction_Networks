import proofs.FiniteReservoir.PhysicalHistoryInventory
import proofs.FiniteReservoir.CandidateParameters

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding FiniteCopyReactor
open scoped ENNReal

/-- One event contains all cycle targets, the returned bath history and actual net synthesis. -/
def OperationalSuccess (M : ℕ) (N : CountState M) (V n : ℕ)
    (policy : ReturnedHistory M → Intervention) : Set (ReturnedHistory M) :=
  {h | h ∈ returnedFinal V M n ∧ Nonempty (HistoryTrace M N V policy h) ∧
    (n:ℝ)*(Nat.ceil ((V:ℝ)/56):ℝ) ≤ returnedTotal h 1 ∧
    (n:ℝ)*(Nat.ceil ((V:ℝ)/1080):ℝ) ≤ returnedTotal h 0 ∧
    returnedTotal h 2 ≤ (n:ℝ)*(5*(V:ℝ)) ∧ returnedTotal h 3 ≤ (n:ℝ)*(5*(V:ℝ)) ∧
    returnedTotal h 4 ≤ (n:ℝ)*(Nat.floor ((V:ℝ)/5):ℝ) ∧
    ∀ tr : HistoryTrace M N V policy h,((n:ℝ)/56-161/160)*(V:ℝ) ≤ tr.produced}

theorem certified_history_operational (M : ℕ) (N : CountState M) (V n : ℕ)
    (policy : ReturnedHistory M → Intervention) (hN : Restart V N.1) :
    certifiedPhysicalHistory M N V n policy ⊆ OperationalSuccess M N V n policy := by
  intro h hh
  obtain ⟨ht,hf,hu,hw,hg⟩ := returned_joint_totals V M n h hh.1
  exact ⟨hh.1,hh.2,ht,hf,hu,hw,hg,fun tr => tr.certified_net_lower n hN hh.1⟩

theorem finite_bath_horizon (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) (policy : ReturnedHistory M → Intervention)
    (hscale : 200000000000 ≤ V) (hN : Restart V N.1) (n : ℕ) :
    ENNReal.ofReal (1-(n:ℝ)*oneCycleError V) ≤
      fullHistoryKernel (returnedHistoryStep M N V params hV policy) n []
        (OperationalSuccess M N V n policy) :=
  (full_source_inventory_success M N V params hV policy hscale hN n).trans
    (measure_mono (certified_history_operational M N V n policy hN))

theorem finite_bath_budget (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) (policy : ReturnedHistory M → Intervention)
    (hscale : 200000000000 ≤ V) (hN : Restart V N.1) (n : ℕ) (δ : ℝ)
    (hb : (n:ℝ)*oneCycleError V ≤ δ) :
    ENNReal.ofReal (1-δ) ≤ fullHistoryKernel (returnedHistoryStep M N V params hV policy) n []
      (OperationalSuccess M N V n policy) :=
  (ENNReal.ofReal_le_ofReal (by linarith : 1-δ ≤ 1-(n:ℝ)*oneCycleError V)).trans
    (finite_bath_horizon M N V params hV policy hscale hN n)

/-- A concrete nonempty pure-fuel mission, uniform over every admitted feedback policy. -/
theorem pure_hundred (R : ℕ) (hR : 0 < R) (policy : ReturnedHistory R → Intervention) :
    let V := 200000000000
    let N : CountState R := (![0,0,V,0,0,0],pureFuel R)
    let params := pureParameters R hR 20 (1/50) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ENNReal.ofReal (999979/1000000:ℝ) ≤
      fullHistoryKernel (returnedHistoryStep R N V params (by norm_num) policy) 100 []
        (OperationalSuccess R N V 100 policy) := by
  dsimp only
  have hb : (100:ℝ)*oneCycleError 200000000000 ≤ 21/1000000 := FiniteCopyReactor.hundred_sharp_budget
  have hN : Restart 200000000000 ![0,0,200000000000,0,0,0] := all_free_restart _
  convert finite_bath_budget R (![0,0,200000000000,0,0,0],pureFuel R) 200000000000
    (pureParameters R hR 20 (1/50) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) policy (by norm_num) hN 100 (21/1000000) hb using 1
  norm_num

end
end FiniteReservoir
