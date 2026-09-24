import proofs.RandomViability.BindingOperatingEntry
import proofs.RandomViability.BindingOutputProbability

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

def operatingSuccess (X : OutputState) : Prop :=
  resourceGood (boxCounts (trackedCounts X.1)) 100000000 ∧ trackedPhase X.1=1 ∧ X.2.val=10000000

def operatingEvents : Fin 5 → Set OutputState :=
  ![{X | operatingSuccess X},{X | missedEntry X},{X | returnFailure X},
    {X | resourceFailure X},{X | outputActive X}]

theorem operating_events_cover (X : OutputState) :
    1 ≤ ∑ i,FiniteKernel.eventIndicator (operatingEvents i) X := by
  have hex : ∃ i : Fin 5,X ∈ operatingEvents i := by
    by_cases hg : resourceGood (boxCounts (trackedCounts X.1)) 100000000
    · by_cases hp0 : trackedPhase X.1=0
      · exact ⟨1,hp0,hg⟩
      · by_cases hp1 : trackedPhase X.1=1
        · by_cases hc : X.2.val=10000000
          · exact ⟨0,hg,hp1,hc⟩
          · have hp2 : trackedPhase X.1≠2 := by omega
            have hct : X.2.val<10000000 := by have hh := X.2.isLt; omega
            exact ⟨4,⟨hp2,hg⟩,hp1,hct⟩
        · have hp2 : trackedPhase X.1=2 := by omega
          exact ⟨2,hp2⟩
    · exact ⟨3,hg⟩
  obtain ⟨i,hi⟩ := hex
  have hh := Finset.single_le_sum (fun j _=>(FiniteKernel.eventIndicator_bounds (operatingEvents j) X).1)
    (Finset.mem_univ i)
  simpa only [FiniteKernel.eventIndicator,if_pos hi] using hh

theorem twoPeriod_finset_sum {α ι : Type*} [Fintype α] (P Q : FiniteKernel α) (t : ℝ≥0)
    (s : Finset ι) (F : ι → α → ℝ) (hF : ∀ i x,0≤F i x) (x : α) :
    twoPeriod P Q t (fun y=>∑ i ∈ s,F i y) x = ∑ i ∈ s,twoPeriod P Q t (F i) x := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,twoPeriod_const]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [twoPeriod_add P Q t (F i) (fun y=>∑ j ∈ s,F j y) (hF i)
      (fun y=>Finset.sum_nonneg (fun j _=>hF j y)),ih]

theorem operating_insufficient_output (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) :
    operatingExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator {X | outputActive X}) ≤ 1/10000 := by
  let P := operatingOutputKernel false k r hk hk1 hr hr1
  let Q := operatingOutputKernel true k r hk hk1 hr hr1
  have h := P.poissonized_mono 150000000000000
    (fun X=>Q.poissonized 150000000000000 (FiniteKernel.eventIndicator {X | outputActive X}) X)
    (fun _=>(1/10000:ℝ))
    (fun X=>(Q.poissonized_event_bounds _ _ X).1) (by intro X; norm_num)
    (fun X=>(output_probability k r hk hk1 hr hr1 X).le) outputInitial
  rw [P.poissonized_const] at h
  exact h

/-- Evaluated finite-copy reliability for the literal reversible binding mechanism.
The two windows share the entire count/phase/counter distribution. -/
theorem operating_success_lower_bound (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) :
    (9/10:ℝ) ≤ operatingExpectation k r hk hk1 hr hr1
      (FiniteKernel.eventIndicator {X | operatingSuccess X}) := by
  let P := operatingOutputKernel false k r hk hk1 hr hr1
  let Q := operatingOutputKernel true k r hk hk1 hr hr1
  have h := twoPeriod_mono P Q 150000000000000 (fun _=>(1:ℝ))
    (fun X=>∑ i,FiniteKernel.eventIndicator (operatingEvents i) X)
    (by intro X; norm_num)
    (fun X=>Finset.sum_nonneg (fun i _=>(FiniteKernel.eventIndicator_bounds (operatingEvents i) X).1))
    operating_events_cover outputInitial
  rw [twoPeriod_const,twoPeriod_finset_sum P Q 150000000000000 Finset.univ
    (fun i=>FiniteKernel.eventIndicator (operatingEvents i))
    (fun i X=>(FiniteKernel.eventIndicator_bounds (operatingEvents i) X).1)] at h
  change 1 ≤ ∑ i,operatingExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator (operatingEvents i)) at h
  simp only [operatingEvents,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero] at h
  have hn := operating_missed_entry k r hk hk1 hr hr1
  have hr' := operating_return_failure k r hk hk1 hr hr1
  have hf := operating_resource_failure k r hk hk1 hr hr1
  have ho := operating_insufficient_output k r hk hk1 hr hr1
  linarith

end
end RandomViability.Binding
