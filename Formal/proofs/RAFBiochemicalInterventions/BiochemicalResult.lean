import proofs.RAFBiochemicalInterventions.ParentIntervention
import proofs.RAFBiochemicalInterventions.SmallSource

namespace RAFBiochemicalLiteral

/-- Exact completion query for the two known singleton supports is negative. -/
theorem small_completion_closed : ¬ ∃ S : List Row,
    Subrows S SmallSource.rows ∧ RAF S SmallSource.food ∧
    SmallSource.r0 ∉ S ∧ SmallSource.r7 ∉ S := by
  rintro ⟨S,hsub,hraf,h0,h7⟩
  obtain ⟨r,hr,hseed⟩ := raf_contains_seed hraf
  rcases SmallSource.only_seeds r (hsub r hr) hseed with he | he
  · exact h0 (he ▸ hr)
  · exact h7 (he ▸ hr)

/-- Concrete source-defined case-study result. Capability is existential RAF
support with positive catalyst formulas evaluated in food-generated closure.
Minimality is inclusion minimality among grouped source-action deletions. -/
theorem biochemical_result :
    MinimalCut ParentSource.rows ParentSource.food ParentSource.target ParentSource.cut ∧
    Capable (remaining ParentSource.rows ParentSource.cut) ParentSource.food 68 ∧
    (∀ S : List Row, Subrows S SmallSource.rows →
      (Irreducible S SmallSource.food ↔
        SameRows S [SmallSource.r0] ∨ SameRows S [SmallSource.r7])) ∧
    ClosedRAF SmallSource.rows SmallSource.lower SmallSource.food ∧
    ClosedRAF SmallSource.rows SmallSource.rows SmallSource.food ∧
    (Subrows SmallSource.lower SmallSource.rows ∧ ¬ Subrows SmallSource.rows SmallSource.lower) := by
  exact ⟨ParentIntervention.valine_cut_minimal, ParentIntervention.methionine_preserved,
    SmallSource.irreducible_catalogue, SmallSource.lower_closed, SmallSource.whole_closed,
    SmallSource.lower_proper⟩

end RAFBiochemicalLiteral
