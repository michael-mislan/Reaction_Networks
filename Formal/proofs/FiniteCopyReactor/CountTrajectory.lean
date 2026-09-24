import proofs.FiniteCopyReactor.Source
import proofs.RandomViability.JumpSupport
import proofs.RandomViability.JumpInitial

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped BigOperators

instance reactorChannelMeasurable : MeasurableSpace CompetitionChannel := ⊤
instance reactorChannelSingleton : MeasurableSingletonClass CompetitionChannel := ⟨fun _ => trivial⟩

def reactorRate (V r d : ℝ) (N : Counts) (j : CompetitionChannel) : ℝ :=
  competitionRate N V (1/500000000) (1/10) r d j

def reactorNext (N : Counts) (j : CompetitionChannel) : Counts :=
  if ∀ i, reactants (competitionBase j) i ≤ N i then competitionNext N j else N

theorem reactor_next_source (N : Counts) (V r d : ℝ) (j : CompetitionChannel)
    (h : reactorRate V r d N j ≠ 0) :
    reactorNext N j = CommonPhysicalRealization.physicalNext N j := by
  rw [reactorNext, if_pos (competition_rate_support N V _ _ r d j h)]
  rfl

theorem reactor_rate_nonneg (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : Counts) (j : CompetitionChannel) : 0 ≤ reactorRate V r d N j :=
  competitionRate_nonneg N V _ _ r d hV (by norm_num) (by norm_num) hr hd j

theorem reactor_total_pos (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : Counts) : 0 < ∑ j, reactorRate V r d N j := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => reactor_rate_nonneg V r d hV hr hd N j)
    (Finset.mem_univ (Sum.inl (10 : Fin 18) : CompetitionChannel))
  have he : reactorRate V r d N (.inl 10)=V := rfl
  rw [he] at h
  exact hV.trans_le h

def reactorMass (N : Counts) : ℕ := N 0+N 1+2*N 2+3*N 3+4*N 4+4*N 5

def reactorFood : CompetitionChannel → ℕ
  | .inl j => if j=10 ∨ j=11 then 1 else 0
  | .inr _ => 0

theorem reactor_next_mass (N : Counts) (j : CompetitionChannel) :
    reactorMass (reactorNext N j) ≤ reactorMass N+reactorFood j := by
  unfold reactorNext
  split_ifs with h
  · cases j with
    | inl j =>
      fin_cases j
      · change (N 0-1+0)+(N 1-1+0)+2*(N 2-0+1)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h0 : 1 ≤ N 0 := h 0
        have h1 : 1 ≤ N 1 := h 1
        unfold reactorMass
        omega
      · change (N 0-0+1)+(N 1-0+1)+2*(N 2-1+0)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h2 : 1 ≤ N 2 := h 2
        unfold reactorMass
        omega
      · change (N 0-1+0)+(N 1-0+0)+2*(N 2-1+0)+3*(N 3-0+1)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h0 : 1 ≤ N 0 := h 0
        have h2 : 1 ≤ N 2 := h 2
        unfold reactorMass
        omega
      · change (N 0-0+1)+(N 1-0+0)+2*(N 2-0+1)+3*(N 3-1+0)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h3 : 1 ≤ N 3 := h 3
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-1+0)+2*(N 2-0+0)+3*(N 3-1+0)+4*(N 4-0+1)+4*(N 5-0+0) ≤ reactorMass N+0
        have h1 : 1 ≤ N 1 := h 1
        have h3 : 1 ≤ N 3 := h 3
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-0+1)+2*(N 2-0+0)+3*(N 3-0+1)+4*(N 4-1+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h4 : 1 ≤ N 4 := h 4
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-0+0)+2*(N 2-0+0)+3*(N 3-0+0)+4*(N 4-1+0)+4*(N 5-0+1) ≤ reactorMass N+0
        have h4 : 1 ≤ N 4 := h 4
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-0+0)+2*(N 2-0+0)+3*(N 3-0+0)+4*(N 4-0+1)+4*(N 5-1+0) ≤ reactorMass N+0
        have h5 : 1 ≤ N 5 := h 5
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-0+0)+2*(N 2-0+2)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-1+0) ≤ reactorMass N+0
        have h5 : 1 ≤ N 5 := h 5
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-0+0)+2*(N 2-2+0)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-0+1) ≤ reactorMass N+0
        have h2 : 2 ≤ N 2 := h 2
        unfold reactorMass
        omega
      · change (N 0-0+1)+(N 1-0+0)+2*(N 2-0+0)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+1
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-0+1)+2*(N 2-0+0)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+1
        unfold reactorMass
        omega
      · change (N 0-1+0)+(N 1-0+0)+2*(N 2-0+0)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h0 : 1 ≤ N 0 := h 0
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-1+0)+2*(N 2-0+0)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h1 : 1 ≤ N 1 := h 1
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-0+0)+2*(N 2-1+0)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h2 : 1 ≤ N 2 := h 2
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-0+0)+2*(N 2-0+0)+3*(N 3-1+0)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h3 : 1 ≤ N 3 := h 3
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-0+0)+2*(N 2-0+0)+3*(N 3-0+0)+4*(N 4-1+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h4 : 1 ≤ N 4 := h 4
        unfold reactorMass
        omega
      · change (N 0-0+0)+(N 1-0+0)+2*(N 2-0+0)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-1+0) ≤ reactorMass N+0
        have h5 : 1 ≤ N 5 := h 5
        unfold reactorMass
        omega
    | inr j =>
      fin_cases j
      · change (N 0-0+1)+(N 1-0+1)+2*(N 2-1+0)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h2 : 1 ≤ N 2 := h 2
        unfold reactorMass
        omega
      · change (N 0-1+0)+(N 1-1+0)+2*(N 2-0+1)+3*(N 3-0+0)+4*(N 4-0+0)+4*(N 5-0+0) ≤ reactorMass N+0
        have h0 : 1 ≤ N 0 := h 0
        have h1 : 1 ≤ N 1 := h 1
        unfold reactorMass
        omega
  · exact Nat.le_add_right _ _

theorem count_le_reactorMass (N : Counts) (i : Fin 6) : N i ≤ reactorMass N := by
  fin_cases i <;> dsimp [reactorMass] <;> omega

def reactorTrajectory (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (N : Counts) :=
  jumpTrajectoryLaw N reactorNext (reactorRate V r d)
    (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd)

instance reactorTrajectory_probability (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (N : Counts) :
    IsProbabilityMeasure (reactorTrajectory V r d hV hr hd N) := by
  unfold reactorTrajectory
  infer_instance

def reactorTrajectoryFood (j : Unit ⊕ CompetitionChannel) : ℕ := j.elim (fun _ => 0) reactorFood

theorem reactor_mass_envelope (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (N : Counts) :
    ∀ᵐ z ∂reactorTrajectory V r d hV hr hd N, ∀ k,
      reactorMass (z k).1 ≤ reactorMass N+∑ i ∈ Finset.range k,reactorTrajectoryFood (z (i+1)).2.1 := by
  have hs := jumpTrajectory_consistent N reactorNext (reactorRate V r d)
    (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd)
  have hi := jumpTrajectory_initial_population N reactorNext (reactorRate V r d)
    (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd)
  filter_upwards [hs,hi] with z hz hinit
  intro k
  induction k with
  | zero => simp [hinit]
  | succ k ih =>
    obtain ⟨j,hj,hn⟩ := hz k
    have hstep := reactor_next_mass (z k).1 j
    rw [Finset.sum_range_succ,hn,hj]
    change reactorMass (reactorNext (z k).1 j) ≤
      reactorMass N+((∑ i ∈ Finset.range k,reactorTrajectoryFood (z (i+1)).2.1)+reactorFood j)
    omega

theorem reactor_locally_bounded (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (B : ℕ) :
    ∃ q : ℝ, 1 ≤ q ∧ ∀ N, reactorMass N ≤ B → ∑ j,reactorRate V r d N j ≤ q := by
  let R := fun X : Fin 6 → Fin (B+1) => ∑ j,reactorRate V r d (fun i => (X i:ℕ)) j
  have hR (X) : 0 ≤ R X := Finset.sum_nonneg (fun j _ => reactor_rate_nonneg V r d hV hr hd _ j)
  refine ⟨1+∑ X,R X, by have h := Finset.sum_nonneg (fun X (_ : X ∈ Finset.univ) => hR X); linarith, ?_⟩
  intro N hN
  let X : Fin 6 → Fin (B+1) := fun i => ⟨N i, by have h := count_le_reactorMass N i; omega⟩
  have h := Finset.single_le_sum (fun Y (_ : Y ∈ Finset.univ) => hR Y) (Finset.mem_univ X)
  change (∑ j,reactorRate V r d N j) ≤ ∑ Y,R Y at h
  linarith

end
end FiniteCopyReactor
