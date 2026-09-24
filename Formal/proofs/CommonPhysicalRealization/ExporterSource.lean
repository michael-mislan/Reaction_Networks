import proofs.RandomViability.BindingCompetitionSource

namespace CommonPhysicalRealization
noncomputable section
open RandomViability.Binding
open scoped BigOperators

/-- U,W,X,C1,C2,Z,F,P; three formal neutral elemental units. -/
def composition : Fin 8 → Fin 3 → ℕ :=
  ![![1,0,0], ![0,1,0], ![1,1,0], ![2,1,0],
    ![2,2,0], ![2,2,0], ![0,0,1], ![0,0,1]]

def pairLeft : Fin 6 → Fin 8 → ℕ :=
  ![![1,1,0,0,0,0,0,0], ![1,0,1,0,0,0,0,0],
    ![0,1,0,1,0,0,0,0], ![0,0,0,0,1,0,0,0],
    ![0,0,0,0,0,1,0,0], ![0,0,1,0,0,0,1,0]]

def pairRight : Fin 6 → Fin 8 → ℕ :=
  ![![0,0,1,0,0,0,0,0], ![0,0,0,1,0,0,0,0],
    ![0,0,0,0,1,0,0,0], ![0,0,0,0,0,1,0,0],
    ![0,0,2,0,0,0,0,0], ![1,1,0,0,0,0,0,1]]

def pairForward : Fin 6 → CompetitionChannel :=
  ![.inl 0, .inl 2, .inl 4, .inl 6, .inl 8, .inr 0]
def pairReverse : Fin 6 → CompetitionChannel :=
  ![.inl 1, .inl 3, .inl 5, .inl 7, .inl 9, .inr 1]

theorem material_balance (j : Fin 6) (e : Fin 3) :
    (∑ i, pairLeft j i * composition i e) =
      ∑ i, pairRight j i * composition i e := by
  fin_cases j <;> fin_cases e <;>
    norm_num [pairLeft, pairRight, composition, Fin.sum_univ_succ]

theorem internal_complexes (j : Fin 6) (i : Fin 6) :
    pairLeft j (i.castLE (by decide)) = reactants (competitionBase (pairForward j)) i ∧
    pairRight j (i.castLE (by decide)) = products (competitionBase (pairForward j)) i ∧
    pairRight j (i.castLE (by decide)) = reactants (competitionBase (pairReverse j)) i ∧
    pairLeft j (i.castLE (by decide)) = products (competitionBase (pairReverse j)) i := by
  revert j i
  decide

/-- Literal chemostatted mass-action rates; aF and aP are activities, not counts.
The bimolecular identical-X propensity uses the donor's falling factorial. -/
def physicalRate (N : Counts) (V r d aF aP : ℝ) : CompetitionChannel → ℝ
  | .inl j =>
    ![(1/500000000)*(N 0)*(N 1)/V, (1/5000000000)*(N 2),
      20*(N 2)*(N 0)/V,20*(N 3),20*(N 3)*(N 1)/V,20*(N 4),
      20*(N 4),2*(N 5),r*(N 5),r*(N 2*(N 2-1):ℕ)/V,
      V,V,N 0,N 1,N 2,N 3,N 4,N 5] j
  | .inr j => if j=0 then d*aF*(N 2)
      else d*(1/8000000000)*aP*(N 0)*(N 1)/V

theorem rate_projection (N : Counts) (V r d : ℝ) (j : CompetitionChannel) :
    physicalRate N V r d 1 1 j = competitionRate N V (1/500000000) (1/10) r d j := by
  cases j with
  | inl j => fin_cases j <;> norm_num [physicalRate,competitionRate,countRate]
  | inr j =>
    fin_cases j
    · norm_num [physicalRate,competitionRate,drivenRate,drivenBase,countRate]
    · norm_num [physicalRate,competitionRate,drivenRate,drivenBase,countRate]
      ring

/-- Event identities and marks are retained, including the distinct driven labels. -/
def physicalNext (N : Counts) (j : CompetitionChannel) : Counts :=
  fun i => N i - reactants (competitionBase j) i + products (competitionBase j) i
def physicalExport : CompetitionChannel → ℝ
  | .inl j => ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,8] j
  | .inr _ => 0
def physicalService (q : Fin 2) : CompetitionChannel → ℕ
  | .inl _ => 0
  | .inr j => if j=q then 1 else 0

theorem marked_projection (N : Counts) (V r d : ℝ) (j : CompetitionChannel) :
    physicalRate N V r d 1 1 j = competitionRate N V (1/500000000) (1/10) r d j ∧
    physicalNext N j = competitionNext N j ∧
    physicalExport j = competitionExport j ∧
    (∀ q, physicalService q j = reservoirMark q j) := by
  refine ⟨rate_projection N V r d j, rfl, ?_, fun _ => rfl⟩
  cases j <;> rfl

theorem passive_cycle (i : Fin 8) :
    ((pairRight 1 i : ℤ)-pairLeft 1 i) + ((pairRight 2 i : ℤ)-pairLeft 2 i) +
      ((pairRight 3 i : ℤ)-pairLeft 3 i) + ((pairRight 4 i : ℤ)-pairLeft 4 i) =
      (pairRight 0 i : ℤ)-pairLeft 0 i := by
  revert i
  decide

theorem driven_cycle (i : Fin 8) :
    ((pairRight 0 i : ℤ)-pairLeft 0 i) + ((pairRight 5 i : ℤ)-pairLeft 5 i) =
      (![0,0,0,0,0,0,-1,1] : Fin 8 → ℤ) i := by
  revert i
  decide

end
end CommonPhysicalRealization
