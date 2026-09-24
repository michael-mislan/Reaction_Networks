import proofs.FiniteCopyReactor.CountInventory
import proofs.FiniteCopyReactor.Restart

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding
open scoped BigOperators

/-- Inventory of one pulse followed by any finite supported chronological path. -/
theorem cycle_template_inventory (before : Counts) (V : ℕ) (p : Intervention)
    (o : PulseOutcome before) (n : ℕ) (N : ℕ → Counts) (j : ℕ → CompetitionChannel)
    (h0 : N 0=postPulseCounts before V p o)
    (hs : ∀ k < n,∀ i,reactants (competitionBase (j k)) i ≤ N k i)
    (hn : ∀ k < n,N (k+1)=competitionNext (N k) (j k)) :
    templateStock (N n)+templateStock (categoryCounts before o 1)+
      templateStock (categoryCounts before o 2)+(∑ k ∈ Finset.range n,templateMark (j k))=
      templateStock before+(∑ k ∈ Finset.range n,synthesisMark (j k)) := by
  have hp := pulse_template_inventory before V p o
  have ht := finite_path_inventory n N j hs hn
  rw [h0] at ht
  linarith

/-- Pulse and reaction inventories telescope across actual retained cycle states. -/
theorem cycles_template_inventory (m : ℕ) (stock removed exported produced : ℕ → ℝ)
    (h : ∀ k < m,stock (k+1)+removed k+exported k=stock k+produced k) :
    stock m+(∑ k ∈ Finset.range m,removed k)+(∑ k ∈ Finset.range m,exported k)=
      stock 0+(∑ k ∈ Finset.range m,produced k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hh := ih (fun k hk => h k (by omega))
    have hm := h m (by omega)
    simp only [Finset.sum_range_succ]
    linarith

theorem templateStock_le_uCount (N : Counts) : templateStock N ≤ uCount N := by
  rw [uCount_expansion]
  change (N 2:ℝ)+N 3+N 4+2*N 5 ≤ (N 0:ℝ)+N 2+2*N 3+2*N 4+2*N 5
  linarith [Nat.cast_nonneg (α := ℝ) (N 0),Nat.cast_nonneg (α := ℝ) (N 3),
    Nat.cast_nonneg (α := ℝ) (N 4)]

/-- The certified output inventory forces net internal production beyond initial stock. -/
theorem net_synthesis_from_cycle_inventory (m V : ℕ) (N : Counts) (hN : Restart V N)
    (stock removed exported produced : ℕ → ℝ)
    (h0 : stock 0=templateStock N) (hf : 0 ≤ stock m)
    (hr : ∀ k < m,0 ≤ removed k)
    (he : ∀ k < m,(V:ℝ)/56 ≤ exported k)
    (hi : ∀ k < m,stock (k+1)+removed k+exported k=stock k+produced k) :
    ((m:ℝ)/56-161/160)*(V:ℝ) ≤ ∑ k ∈ Finset.range m,produced k := by
  have hb := (templateStock_le_uCount N).trans hN.2.1
  have hrem : 0 ≤ ∑ k ∈ Finset.range m,removed k :=
    Finset.sum_nonneg (fun k hk => hr k (Finset.mem_range.mp hk))
  have hexp : (m:ℝ)*((V:ℝ)/56) ≤ ∑ k ∈ Finset.range m,exported k := by
    have hh := Finset.sum_le_sum (s := Finset.range m) (fun k hk => he k (Finset.mem_range.mp hk))
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hh
  have ht := cycles_template_inventory m stock removed exported produced hi
  rw [h0] at ht
  nlinarith

end
end FiniteCopyReactor
