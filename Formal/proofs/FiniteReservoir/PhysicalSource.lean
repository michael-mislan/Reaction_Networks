import proofs.FiniteReservoir.FiniteModel
import proofs.FiniteCopyReactor.CountTrajectory

namespace FiniteReservoir
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped BigOperators

/-- Unbounded internal counts and the conserved finite reservoir inventory. -/
abbrev CountState (M : ℕ) := Counts × FuelState M

def countState {M : ℕ} (X : CountState M) : State := (X.1,bathOf X.2)

def reactorRate (M : ℕ) (p : Parameters M) (V : ℝ) (X : CountState M)
    (j : CompetitionChannel) : ℝ := rate (countState X) V p.release p.cleavage p.capacity j

def reactorNext {M : ℕ} (X : CountState M) (j : CompetitionChannel) : CountState M :=
  (FiniteCopyReactor.reactorNext X.1 j,fuelNext X.2 j)

def reactorMass {M : ℕ} (X : CountState M) : ℕ := FiniteCopyReactor.reactorMass X.1

theorem reactor_rate_nonneg (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V)
    (X : CountState M) (j : CompetitionChannel) : 0 ≤ reactorRate M p V X j :=
  bath_rate_nonneg _ _ _ _ _ hV (by linarith [p.release_lower]) p.cleavage_nonneg p.capacity_pos j

theorem reactor_total_pos (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V)
    (X : CountState M) : 0 < ∑ j,reactorRate M p V X j := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => reactor_rate_nonneg M p V hV X j)
    (Finset.mem_univ (Sum.inl (10 : Fin 18) : CompetitionChannel))
  have he : reactorRate M p V X (.inl 10)=V := rfl
  rw [he] at h
  exact hV.trans_le h

theorem reactor_next_mass (M : ℕ) (X : CountState M) (j : CompetitionChannel) :
    reactorMass (reactorNext X j) ≤ reactorMass X+FiniteCopyReactor.reactorFood j :=
  FiniteCopyReactor.reactor_next_mass X.1 j

theorem reactor_next_source (M : ℕ) (p : Parameters M) (V : ℝ) (X : CountState M)
    (j : CompetitionChannel) (hj : reactorRate M p V X j ≠ 0) :
    countState (reactorNext X j)=next (countState X) j := by
  apply Prod.ext
  · change FiniteCopyReactor.reactorNext X.1 j=CommonPhysicalRealization.physicalNext X.1 j
    unfold FiniteCopyReactor.reactorNext
    have hs : ∀ i, reactants (competitionBase j) i ≤ X.1 i :=
      bath_internal_support (countState X) V p.release p.cleavage p.capacity j hj
    rw [if_pos hs]
    rfl
  · cases j with
    | inl j => rfl
    | inr j =>
      fin_cases j
      · have hf : 0 < X.2.val := by
          by_contra h
          have hz : X.2.val=0 := by omega
          apply hj
          simp [reactorRate,rate,countState,bathOf,CommonPhysicalRealization.physicalRate,hz]
        have hbound := X.2.isLt
        norm_num [countState,reactorNext,bathOf,fuelNext,next,Bath.forward]
        omega
      · have hf : X.2.val < M := by
          by_contra h
          have hz : M-X.2.val=0 := by omega
          apply hj
          norm_num [reactorRate,rate,countState,bathOf,CommonPhysicalRealization.physicalRate,hz]
        norm_num [countState,reactorNext,bathOf,fuelNext,next,Bath.reverse]
        omega

theorem reactor_locally_bounded (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) (B : ℕ) :
    ∃ q : ℝ, 1 ≤ q ∧ ∀ X : CountState M, reactorMass X ≤ B → ∑ j,reactorRate M p V X j ≤ q := by
  let R := fun X : (Fin 6 → Fin (B+1)) × FuelState M =>
    ∑ j,reactorRate M p V ((fun i => (X.1 i:ℕ)),X.2) j
  have hR (X) : 0 ≤ R X := Finset.sum_nonneg (fun j _ => reactor_rate_nonneg M p V hV _ j)
  refine ⟨1+∑ X,R X, by have h := Finset.sum_nonneg (fun X (_ : X ∈ Finset.univ) => hR X); linarith, ?_⟩
  intro N hN
  let X : (Fin 6 → Fin (B+1)) × FuelState M :=
    ((fun i => ⟨N.1 i, by have h := FiniteCopyReactor.count_le_reactorMass N.1 i; change FiniteCopyReactor.reactorMass N.1 ≤ B at hN; omega⟩),N.2)
  have h := Finset.single_le_sum (fun Y (_ : Y ∈ Finset.univ) => hR Y) (Finset.mem_univ X)
  change (∑ j,reactorRate M p V N j) ≤ ∑ Y,R Y at h
  linarith

end
end FiniteReservoir
