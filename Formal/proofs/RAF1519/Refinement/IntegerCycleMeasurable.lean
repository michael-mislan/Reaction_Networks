import proofs.RAF1519.Refinement.IntegerCycle

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators

theorem naturalMarkPrefix_measurable {n : ℕ} (i : Fin n) (m : PhysicalMark) (K : ℕ) :
    Measurable (fun z : ℕ → JumpState (MolecularState n) (CountChannel n) => naturalMarkPrefix i m z K) := by
  unfold naturalMarkPrefix
  apply Finset.measurable_sum
  intro j _
  have he : Measurable (naturalMark i m) :=
    measurable_fun_sum measurable_const (measurable_of_countable _)
  exact he.comp (measurable_pi_apply (j+1)).snd.fst

theorem naturalMarkAt_measurable {n : ℕ} (i : Fin n) (m : PhysicalMark) (t : ℝ) :
    Measurable (fun z : ℕ → JumpState (MolecularState n) (CountChannel n) =>
      naturalMarkPrefix i m z (countPathIndex z t)) := by
  have he : Measurable (fun p : (ℕ → JumpState (MolecularState n) (CountChannel n)) × ℕ =>
      naturalMarkPrefix i m p.1 p.2) :=
    measurable_from_prod_countable_left (fun K => naturalMarkPrefix_measurable i m K)
  exact he.comp (measurable_id.prodMk (countPathIndex_measurable t))

theorem naturalMarkedWindow_measurable {n : ℕ} (i : Fin n) (m : PhysicalMark) (a b : ℝ) :
    Measurable (fun z : ℕ → JumpState (MolecularState n) (CountChannel n) => naturalMarkedWindow i m z a b) :=
  (measurable_of_countable (fun x : ℕ × ℕ => x.1-x.2)).comp
    ((naturalMarkAt_measurable i m b).prodMk (naturalMarkAt_measurable i m a))

theorem integerCycleSuccess_measurable {n : ℕ} (V : ℕ) (p : Fin n → Intervention) :
    MeasurableSet {z : ℕ → JumpState (MolecularState n) (CountChannel n) | integerCycleSuccess V p z} := by
  have hr : ∀ i : Fin n, MeasurableSet {z : ℕ → JumpState (MolecularState n) (CountChannel n) |
      Ready (1/100) (fun s => countPath V z 4 (i,s))} := by
    intro i
    exact (Set.to_countable {N : MolecularState n |
      Ready (1/100) (concentration V (fun s => N (i,s)))}).measurableSet.preimage
        (molecularStateAt_measurable 4)
  unfold integerCycleSuccess
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (hr i).inter ((measurableSet_le measurable_const (naturalMarkedWindow_measurable i .inventory 3 4)).inter
    ((measurableSet_le measurable_const (naturalMarkedWindow_measurable i .freeX 3 4)).inter
    ((measurableSet_le ((naturalMarkedWindow_measurable i .foodU 0 4).add_const _) measurable_const).inter
    ((measurableSet_le ((naturalMarkedWindow_measurable i .foodW 0 4).add_const _) measurable_const).inter
      (measurableSet_le (naturalMarkedWindow_measurable i .service 0 4) measurable_const)))))

end
end RAF1519.Refinement
