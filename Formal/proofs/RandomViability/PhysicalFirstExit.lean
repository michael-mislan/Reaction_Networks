import proofs.RandomViability.NonfoodIntervalControl

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

/-- Remember every past mass-corridor exit, including an exit followed by reentry. -/
def massExitStop {n : ℕ} (V : NNReal) (k : ℕ)
    (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∃ j : Finset.Iic k, 11*(V : ℝ) < countMass (h j).1

theorem mass_exit_restrict_iff {n : ℕ} (V : NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) :
    massExitStop V k (Preorder.frestrictLe k z) ↔ ∃ j ≤ k,11*(V : ℝ) < countMass (z j).1 := by
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨j,Finset.mem_Iic.mp j.property,hj⟩
  · rintro ⟨j,hjk,hj⟩
    exact ⟨⟨j,Finset.mem_Iic.mpr hjk⟩,hj⟩

theorem mass_exit_persistent {n : ℕ} (V : NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) {j k : ℕ} (hjk : j ≤ k)
    (hj : massExitStop V j (Preorder.frestrictLe j z)) :
    massExitStop V k (Preorder.frestrictLe k z) := by
  rw [mass_exit_restrict_iff] at hj ⊢
  obtain ⟨i,hij,hi⟩ := hj
  exact ⟨i,hij.trans hjk,hi⟩

theorem mass_exit_absent_iff {n : ℕ} (V : NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) :
    ¬massExitStop V k (Preorder.frestrictLe k z) ↔ ∀ j ≤ k,(countMass (z j).1 : ℝ) ≤ 11*V := by
  rw [mass_exit_restrict_iff]
  push Not
  rfl

theorem nonfood_compensation_after_mass_exit {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (T : ℝ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    {j k : ℕ} (hjk : j ≤ k) (hj : massExitStop V j (Preorder.frestrictLe j z)) :
    censoredNonfoodCompensation c V basal cat T (massExitStop V)
      k (Preorder.frestrictLe k z) (z (k+1)) = 0 := by
  have hs : censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z) :=
    Or.inl (mass_exit_persistent V z hjk hj)
  simp only [censoredNonfoodCompensation,if_pos hs]

/-- The prefix containing the exiting jump is retained, then frozen permanently. -/
theorem nonfood_prefix_frozen_after_mass_exit {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (T : ℝ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    {j k : ℕ} (hjk : j ≤ k) (hj : massExitStop V j (Preorder.frestrictLe j z)) :
    censoredNonfoodPrefix c V basal cat T (massExitStop V) z k =
      censoredNonfoodPrefix c V basal cat T (massExitStop V) z j := by
  induction k,hjk using Nat.le_induction with
  | base => rfl
  | succ k hjk ih =>
    rw [censoredNonfoodPrefix_succ,nonfood_compensation_after_mass_exit c V basal cat T z hjk hj,
      add_zero,ih]

theorem mass_exit_active_before_first_exit {n : ℕ} (V : NNReal) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) {J k : ℕ}
    (hk : k < J) (hgood : ∀ i < J,(countMass (z i).1 : ℝ) ≤ 11*V)
    (ht : prefixElapsed k (Preorder.frestrictLe k z) < T) :
    ¬censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z) := by
  have hs := (mass_exit_absent_iff V z k).mpr (fun i hik => hgood i (lt_of_le_of_lt hik hk))
  exact fun h => h.elim hs (fun h => h.elim (fun hm => hm (hgood k hk)) (not_le.mpr ht))

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

omit [MeasurableSingletonClass (PhysicalCountChannel n)] in
theorem massExitStop_measurable (V : NNReal) (k : ℕ) :
    MeasurableSet {h | @massExitStop n V k h} := by
  have he : {h | @massExitStop n V k h} =
      ⋃ j : Finset.Iic k,{h | 11*(V : ℝ) < (countMass (h j).1 : ℝ)} := by
    ext h
    simp only [massExitStop,Set.mem_setOf_eq,Set.mem_iUnion]
  rw [he]
  apply MeasurableSet.iUnion
  intro j
  exact measurableSet_lt measurable_const
    ((measurable_of_countable (fun N : Molecule n → ℕ => (countMass N : ℝ))).comp
      (measurable_pi_apply j).fst)

/-- The actual-law exponential bound with a measurable, persistent mass exit. -/
theorem physical_first_exit_nonfood_tail (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      (⋃ K,{z | censoredNonfoodFluctuationBy c V basal cat T (massExitStop V) δ K z}) ≤
      ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) :=
  physical_censored_nonfood_volume_rate hn c V hV basal cat N hbasal hcat δ T hδ hT
    (massExitStop V) (massExitStop_measurable V)

end
end RandomViability
