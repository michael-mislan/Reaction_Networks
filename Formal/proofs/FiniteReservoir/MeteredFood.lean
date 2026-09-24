import proofs.FiniteReservoir.Mission

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor RandomViability.Binding

/-- An explicit shutdown convention: all chemistry stops if either metered food inventory is empty. -/
def meteredRate (BU BW usedU usedW : ℕ) (V : ℝ) (M : ℕ) (params : Parameters M)
    (X : CountState M) (j : CompetitionChannel) : ℝ :=
  if usedU < BU ∧ usedW < BW then reactorRate M params V X j else 0

theorem metered_rate_agreement (BU BW usedU usedW : ℕ) (V : ℝ) (M : ℕ) (params : Parameters M)
    (X : CountState M) (hu : usedU < BU) (hw : usedW < BW) :
    meteredRate BU BW usedU usedW V M params X=reactorRate M params V X := by
  funext j
  exact if_pos ⟨hu,hw⟩

theorem SegmentTrace.counter_mono {M collect X Y} (tr : SegmentTrace (M:=M) collect X Y)
    (i : Fin 5) (k : ℕ) (hk : k ≤ tr.length) : (tr.state k).2 i ≤ Y.2 i := by
  have hall (l : ℕ) (hl : l ≤ tr.length) : ∀ a ≤ l,(tr.state a).2 i ≤ (tr.state l).2 i := by
    induction l with
    | zero =>
      intro a ha
      have he : a=0 := by omega
      subst a
      rfl
    | succ l ih =>
      intro a ha
      by_cases he : a=l+1
      · subst a; rfl
      · have hp := ih (by omega) a (by omega)
        have hs := tr.counters l (by omega) i
        omega
  have h := hall tr.length le_rfl k hk
  rwa [tr.finish] at h

theorem SegmentTrace.counter_start_le {M collect X Y} (tr : SegmentTrace (M:=M) collect X Y)
    (i : Fin 5) : X.2 i ≤ Y.2 i := by
  have h := tr.counter_mono i 0 (Nat.zero_le _)
  rwa [tr.start] at h

def CycleTrace.visitedCost {M N V p Y} (tr : CycleTrace M N V p Y) (i : Fin 5) : Set ℕ :=
  {c | c=0 ∨ (∃ k ≤ tr.recovery.length,c=(tr.recovery.state k).2 i) ∨
    (∃ k ≤ tr.collection.length,c=(tr.collection.state k).2 i)}

theorem CycleTrace.prefix_cost_le {M N V p Y} (tr : CycleTrace M N V p Y) (i : Fin 5)
    (c : ℕ) (hc : c ∈ tr.visitedCost i) : c ≤ Y.2 i := by
  rcases hc with rfl | ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩
  · omega
  · exact (tr.recovery.counter_mono i k hk).trans (tr.collection.counter_start_le i)
  · exact tr.collection.counter_mono i k hk

def HistoryTrace.cost {M N V policy h} (_tr : HistoryTrace M N V policy h) (i : Fin 5) : ℝ := returnedTotal h i

/-- Per-cycle counters include its bolus; history costs accumulate those counters without resetting inventory. -/
def HistoryTrace.visitedCost {M N V policy h} : HistoryTrace M N V policy h → Fin 5 → Set ℝ
  | .nil,_ => {0}
  | .cons previous _ cycle,i => previous.visitedCost i ∪
      {c | ∃ a ∈ cycle.visitedCost i,c=previous.cost i+(a:ℝ)}

theorem HistoryTrace.prefix_cost_le {M N V policy h} (tr : HistoryTrace M N V policy h)
    (i : Fin 5) (c : ℝ) (hc : c ∈ tr.visitedCost i) : c ≤ returnedTotal h i := by
  induction tr with
  | nil =>
    have he : c=0 := hc
    subst c
    simp [returnedTotal]
  | @cons h previous Y cycle ih =>
    change c ≤ (Y.2 i:ℝ)+returnedTotal h i
    rcases hc with hc | ⟨a,ha,rfl⟩
    · have hp := ih hc
      have hn := Nat.cast_nonneg (α:=ℝ) (Y.2 i)
      linarith
    · have hp : (a:ℝ) ≤ Y.2 i := by exact_mod_cast cycle.prefix_cost_le i a ha
      dsimp only [HistoryTrace.cost]
      linarith

/-- One spare molecule gives strict positive inventory on every successful prefix, including boluses. -/
theorem HistoryTrace.food_no_stockout {M N V policy h} (tr : HistoryTrace M N V policy h)
    (n : ℕ) (hh : h ∈ returnedFinal V M n) (preU preW : ℕ) (usedU usedW : ℝ)
    (hu : usedU ∈ tr.visitedCost 2) (hw : usedW ∈ tr.visitedCost 3) :
    (preU:ℝ)+usedU < (preU+5*n*V+1:ℕ) ∧ (preW:ℝ)+usedW < (preW+5*n*V+1:ℕ) := by
  obtain ⟨_,_,hU,hW,_⟩ := returned_joint_totals V M n h hh
  have hpu := tr.prefix_cost_le 2 usedU hu
  have hpw := tr.prefix_cost_le 3 usedW hw
  push_cast
  constructor <;> nlinarith

end
end FiniteReservoir
