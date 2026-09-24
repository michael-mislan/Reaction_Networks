import proofs.ProductiveRecovery.FreeProduct
import proofs.ProductiveRecovery.NetSynthesis
import proofs.ProductiveRecovery.SourceUniqueness
import proofs.ProductiveRecovery.SourceCorrespondence

namespace ProductiveRecovery
noncomputable section
open MeasureTheory

theorem conditioned_productive_operation (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (p0 : Intervention)
    (protocol : ℕ → State → Intervention) (c : State) (hc : Admitted c) :
    ∃ C : ℝ → State, ∃ s : ℕ → State, ∃ X : ℕ → ℝ → State,
      C 0 = pulse p0 c ∧
      (∀ t, 0 ≤ t → Nonneg (C t)) ∧
      (∀ t, 0 ≤ t → HasDerivAt C (field r d (C t)) t) ∧
      s 0 = C 12 ∧ (∀ n, StrongReturned (s n)) ∧
      (∀ n, X n 0 = pulse (protocol n (s n)) (s n) ∧
        X n 4 = s (n+1) ∧
        (∀ t, 0 ≤ t → Nonneg (X n t)) ∧
        (∀ t, 0 ≤ t → HasDerivAt (X n) (field r d (X n t)) t) ∧
        StrongReturned (X n 3) ∧ StrongReturned (X n 4) ∧
        (∀ t ∈ Set.Icc (3:ℝ) 4, 1/540 ≤ X n t 2) ∧
        1/540 ≤ ∫ t in (3:ℝ)..4, X n t 2) ∧
      ∀ m : ℕ,
        (m:ℝ)/28 ≤ ∑ n ∈ Finset.range m, routineExport (X n) ∧
        12+(1-p0.q+p0.eU)+(∑ n ∈ Finset.range m, routineFoodU (protocol n (s n))) ≤ (2551+951*(m:ℝ))/200 ∧
        12+(1-p0.q+p0.eW)+(∑ n ∈ Finset.range m, routineFoodW (protocol n (s n))) ≤ (2551+951*(m:ℝ))/200 ∧
        serviceOver d 12 C+(∑ n ∈ Finset.range m, routineService d (X n)) ≤ (27+9*(m:ℝ))/50 ∧
        (m:ℝ)/28-11/10 ≤ netOver r d 12 C+(∑ n ∈ Finset.range m, netOver r d 4 (X n)) := by
  obtain ⟨C,hC0,hCn,hC,hret,hU,hW,hG⟩ := exists_conditioning r d hr hr' hd hd' p0 c hc
  obtain ⟨s,X,hs0,hs,hcycle,hsums⟩ := arbitrary_routine_operation r d hr hr' hd hd' protocol (C 12) hret
  refine ⟨C,s,X,hC0,hCn,hC,hs0,hs,?_,?_⟩
  · intro n
    obtain ⟨h0,h4,hn,hX,h3,hret4⟩ := hcycle n
    have hf := routine_free_export r d hr hr' (by linarith) hd' (protocol n (s n))
      (s n) (hs n) (X n) h0 hn hX
    exact ⟨h0,h4,hn,hX,h3,hret4,hf⟩
  · intro m
    obtain ⟨hq,hu,hw,hg⟩ := hsums m
    have hinit := net_over_lower r d 12 (by norm_num) p0 c hc.1 C hC0 hCn hC
    have hnet (n : ℕ) : inventory (s (n+1))-inventory (s n)+routineExport (X n) ≤ netOver r d 4 (X n) := by
      obtain ⟨h0,h4,hn,hX,_⟩ := hcycle n
      have h := routine_net_lower r d (protocol n (s n)) (s n) (hs n).1 (X n) h0 hn hX
      rw [h4] at h
      exact h
    have hsum := synthesis_telescoping (fun n => inventory (s n))
      (fun n => routineExport (X n)) (fun n => netOver r d 4 (X n)) hnet m
    rw [hs0] at hsum
    have hi := inventory_initial_bound c hc
    have hn := inventory_nonnegative (s m) (hs m).1
    exact ⟨hq,by linarith,by linarith,by linarith,by linarith⟩

end
end ProductiveRecovery
