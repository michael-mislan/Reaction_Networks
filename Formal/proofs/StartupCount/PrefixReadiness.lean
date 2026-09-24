import proofs.StartupCount.TerminalEvent
import proofs.StartupCount.HistoryHolding
import proofs.RandomViability.CensoredStateProducts

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {α β : Type*}

def historyElapsed (k : ℕ) (h : Finset.Iic k → JumpState α β) (j : Finset.Iic k) : ℝ :=
  prefixElapsed j (Preorder.frestrictLe₂ (π := fun _ : ℕ => JumpState α β)
    (Finset.mem_Iic.mp j.property) h)

def readyPrefix (guard : α → Prop) (k : ℕ) (h : Finset.Iic k → JumpState α β) (t : ℝ) : Prop :=
  ∀ j : Finset.Iic k,guard (h j).1 ∧ historyElapsed k h j ≤ t

theorem prefixElapsed_eq_jumpElapsed (k : ℕ) (z : ℕ → JumpState α β) :
    prefixElapsed k (Preorder.frestrictLe k z) = jumpElapsed z k := by
  unfold prefixElapsed jumpElapsed
  exact Fin.sum_univ_eq_sum_range (fun i => (z (i+1)).2.2) k

theorem historyElapsed_restrict (k : ℕ) (z : ℕ → JumpState α β) (j : Finset.Iic k) :
    historyElapsed k (Preorder.frestrictLe k z) j = jumpElapsed z j :=
  prefixElapsed_eq_jumpElapsed j z

theorem readyPrefix_restrict (guard : α → Prop) (k : ℕ) (z : ℕ → JumpState α β) (t : ℝ) :
    readyPrefix guard k (Preorder.frestrictLe k z) t ↔
      (∀ j ≤ k,guard (z j).1) ∧ (∀ j ≤ k,jumpElapsed z j ≤ t) := by
  constructor
  · intro hh
    constructor
    · intro j hj
      exact (hh ⟨j,Finset.mem_Iic.mpr hj⟩).1
    · intro j hj
      exact (historyElapsed_restrict k z ⟨j,Finset.mem_Iic.mpr hj⟩) ▸
        (hh ⟨j,Finset.mem_Iic.mpr hj⟩).2
  · rintro ⟨hg,ht⟩ j
    exact ⟨hg j (Finset.mem_Iic.mp j.property),by
      rw [historyElapsed_restrict]
      exact ht j (Finset.mem_Iic.mp j.property)⟩

theorem readyPrefix_last (guard : α → Prop) (k : ℕ) (h : Finset.Iic k → JumpState α β)
    (t : ℝ) (hh : readyPrefix guard k h t) :
    guard (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 ∧ prefixElapsed k h ≤ t :=
  hh ⟨k,Finset.mem_Iic.mpr le_rfl⟩

def guardedLowAt (guard : α → Prop) (count : α → ℕ) (h k : ℕ) (t : ℝ) :
    Set (ℕ → JumpState α β) :=
  {z | readyPrefix guard k (Preorder.frestrictLe k z) t ∧ count (z k).1 ≤ h ∧
    t < jumpElapsed z (k+1)}

theorem guardedLowAt_union (guard : α → Prop) (count : α → ℕ) (h : ℕ) (t : ℝ) :
    (⋃ k,guardedLowAt (β := β) guard count h k t) = guardedLowEvent guard count h t := by
  ext z
  constructor
  · intro hz
    obtain ⟨k,hk⟩ := mem_iUnion.mp hz
    obtain ⟨hg,hpre⟩ := (readyPrefix_restrict guard k z t).mp hk.1
    exact ⟨k,hg,hpre,hk.2.2,hk.2.1⟩
  · rintro ⟨k,hg,hpre,hpost,hcount⟩
    exact mem_iUnion.mpr ⟨k,(readyPrefix_restrict guard k z t).mpr ⟨hg,hpre⟩,hcount,hpost⟩

theorem guardedLowAt_disjoint (guard : α → Prop) (count : α → ℕ) (h : ℕ) (t : ℝ) :
    Pairwise (fun i j => Disjoint (guardedLowAt (β := β) guard count h i t)
      (guardedLowAt guard count h j t)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  have hpi := ((readyPrefix_restrict guard i z t).mp hi.1).2
  have hpj := ((readyPrefix_restrict guard j z t).mp hj.1).2
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hh := hpj (i+1) (by omega)
    exact not_lt_of_ge hh hi.2.2
  · have hh := hpi (j+1) (by omega)
    exact not_lt_of_ge hh hj.2.2

variable [MeasurableSpace α] [MeasurableSpace β] [Countable α] [MeasurableSingletonClass α]

omit [Countable α] [MeasurableSingletonClass α] in
theorem historyElapsed_measurable (k : ℕ) (j : Finset.Iic k) :
    Measurable (fun h : Finset.Iic k → JumpState α β => historyElapsed k h j) :=
  (prefixElapsed_measurable j).comp
    (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => JumpState α β)
      (Finset.mem_Iic.mp j.property))

theorem readyPrefix_measurableSet (guard : α → Prop) (k : ℕ) :
    MeasurableSet {p : (Finset.Iic k → JumpState α β) × ℝ | readyPrefix guard k p.1 p.2} := by
  have hall : MeasurableSet (⋂ j : Finset.Iic k,
      {p : (Finset.Iic k → JumpState α β) × ℝ | guard (p.1 j).1 ∧ historyElapsed k p.1 j ≤ p.2}) := by
    apply MeasurableSet.iInter
    intro j
    exact ((Set.to_countable {x : α | guard x}).measurableSet.preimage
      (((measurable_pi_apply j).comp measurable_fst).fst)).inter
      (measurableSet_le ((historyElapsed_measurable k j).comp measurable_fst) measurable_snd)
  convert hall using 1
  ext p
  simp only [Set.mem_iInter,Set.mem_setOf_eq]
  rfl

theorem guardedLowAt_measurable (guard : α → Prop) (count : α → ℕ) (h k : ℕ) (t : ℝ) :
    MeasurableSet (guardedLowAt (β := β) guard count h k t) := by
  apply MeasurableSet.inter
  · have hm : Measurable (fun z : ℕ → JumpState α β => (Preorder.frestrictLe k z,t)) :=
      (Preorder.measurable_frestrictLe k).prodMk measurable_const
    exact (readyPrefix_measurableSet guard k).preimage hm
  · exact ((Set.to_countable {x : α | count x ≤ h}).measurableSet.preimage
      (measurable_pi_apply k).fst).inter
      (measurableSet_lt measurable_const (jumpElapsed_measurable (k+1)))

theorem guardedLowAt_measure_sum (μ : Measure (ℕ → JumpState α β))
    (guard : α → Prop) (count : α → ℕ) (h : ℕ) (t : ℝ) :
    (∑' k,μ (guardedLowAt guard count h k t)) = μ (guardedLowEvent guard count h t) := by
  rw [← measure_iUnion (guardedLowAt_disjoint guard count h t)
    (fun k => guardedLowAt_measurable guard count h k t),guardedLowAt_union]

end
end StartupCount
