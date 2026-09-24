import proofs.FiniteReservoir.SegmentInventory

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor RandomViability.Binding
open scoped BigOperators

/-- Exact signed fuel accounting follows from the literal update and conserved finite bath. -/
theorem bath_step_inventory {M : ℕ} (X Y : CountState M) (j : CompetitionChannel)
    (h : countState Y=FiniteReservoir.next (countState X) j) :
    Y.2.val+reservoirMark 0 j=X.2.val+reservoirMark 1 j := by
  have ht : (FiniteReservoir.next (countState X) j).2.total=M := by
    rw [← h]
    exact bathOf_total Y.2
  have hf := congrArg (fun s : State => s.2.fuel) h
  cases j with
  | inl j => simpa [FiniteReservoir.next,countState,bathOf,reservoirMark] using hf
  | inr j =>
    fin_cases j <;>
      simp [FiniteReservoir.next,countState,bathOf,Bath.forward,Bath.reverse,Bath.total,reservoirMark] at hf ht ⊢ <;>
      have hx := X.2.isLt <;> omega

theorem bath_prefix_inventory {M : ℕ} (n : ℕ) (Z : ℕ → CountState M) (j : ℕ → CompetitionChannel)
    (hn : ∀ k < n,countState (Z (k+1))=FiniteReservoir.next (countState (Z k)) (j k)) :
    (Z n).2.val+(∑ k ∈ Finset.range n,reservoirMark 0 (j k))=
      (Z 0).2.val+(∑ k ∈ Finset.range n,reservoirMark 1 (j k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun k hk => hn k (by omega))
    have hs := bath_step_inventory (Z n) (Z (n+1)) (j n) (hn n (by omega))
    simp only [Finset.sum_range_succ]
    omega

theorem integer_gross_mark (collect : Bool) (j : CompetitionChannel) :
    integerCycleMarks collect j 4=reservoirMark 0 j+reservoirMark 1 j := by
  cases j with
  | inl j =>
    change Nat.floor (0:ℝ)=0+0
    norm_num
  | inr j =>
    fin_cases j <;> change Nat.floor (1:ℝ)=_
    all_goals norm_num [reservoirMark]

theorem gross_prefix_inventory {M : ℕ} (collect : Bool) (n : ℕ)
    (Z : ℕ → JointCounts M) (j : ℕ → CompetitionChannel)
    (hc : ∀ k < n,∀ i,(Z (k+1)).2 i=(Z k).2 i+integerCycleMarks collect (j k) i) :
    (Z n).2 4=(Z 0).2 4+
      (∑ k ∈ Finset.range n,reservoirMark 0 (j k))+(∑ k ∈ Finset.range n,reservoirMark 1 (j k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun k hk => hc k (by omega))
    have hs := hc n (by omega) 4
    rw [integer_gross_mark] at hs
    simp only [Finset.sum_range_succ]
    omega

theorem SegmentTrace.prefix_fuel_bound {M collect X Y} (tr : SegmentTrace (M:=M) collect X Y)
    (k : ℕ) (hk : k ≤ tr.length) :
    (tr.state k).1.2.val ≤ X.1.2.val+Y.2 4-X.2 4 ∧
    X.1.2.val ≤ (tr.state k).1.2.val+Y.2 4-X.2 4 := by
  have hi := bath_prefix_inventory k (fun l => (tr.state l).1) tr.label (fun l hl => tr.physical l (by omega))
  have hg := gross_prefix_inventory collect k tr.state tr.label (fun l hl => tr.counters l (by omega))
  have hmono : (tr.state k).2 4 ≤ (tr.state tr.length).2 4 := by
    have hstep (l : ℕ) (hl : l < tr.length) : (tr.state l).2 4 ≤ (tr.state (l+1)).2 4 := by
      rw [tr.counters l hl 4]
      omega
    have hall (l : ℕ) (hl : l ≤ tr.length) : ∀ i ≤ l,(tr.state i).2 4 ≤ (tr.state l).2 4 := by
      induction l with
      | zero =>
        intro i hi
        have he : i=0 := by omega
        subst i
        rfl
      | succ l ih =>
        intro i hi
        by_cases hh : i=l+1
        · subst i; rfl
        · exact (ih (by omega) i (by omega)).trans (hstep l (by omega))
    exact hall tr.length le_rfl k hk
  dsimp only at hi
  rw [tr.start] at hi hg
  rw [tr.finish] at hmono
  omega

theorem SegmentTrace.counter_gross_mono {M collect X Y} (tr : SegmentTrace (M:=M) collect X Y) :
    X.2 4 ≤ Y.2 4 := by
  have h := gross_prefix_inventory collect tr.length tr.state tr.label tr.counters
  rw [tr.start,tr.finish] at h
  omega

theorem SegmentTrace.prefix_fuel_abs {M collect X Y} (tr : SegmentTrace (M:=M) collect X Y)
    (k : ℕ) (hk : k ≤ tr.length) :
    |((tr.state k).1.2.val:ℝ)-(X.1.2.val:ℝ)| ≤ (Y.2 4:ℝ)-(X.2 4:ℝ) := by
  obtain ⟨ha,hb⟩ := tr.prefix_fuel_bound k hk
  have hc := tr.counter_gross_mono
  have ha' : ((tr.state k).1.2.val:ℝ)+(X.2 4:ℝ) ≤ (X.1.2.val:ℝ)+(Y.2 4:ℝ) := by
    exact_mod_cast (show (tr.state k).1.2.val+X.2 4 ≤ X.1.2.val+Y.2 4 by omega)
  have hb' : (X.1.2.val:ℝ)+(X.2 4:ℝ) ≤ ((tr.state k).1.2.val:ℝ)+(Y.2 4:ℝ) := by
    exact_mod_cast (show X.1.2.val+X.2 4 ≤ (tr.state k).1.2.val+Y.2 4 by omega)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem SegmentTrace.fuel_abs {M collect X Y} (tr : SegmentTrace (M:=M) collect X Y) :
    |(Y.1.2.val:ℝ)-(X.1.2.val:ℝ)| ≤ (Y.2 4:ℝ)-(X.2 4:ℝ) := by
  have h := tr.prefix_fuel_abs tr.length le_rfl
  rwa [tr.finish] at h

end
end FiniteReservoir
