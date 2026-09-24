import proofs.ThermoCoreCompatibility.Hypergraph.PrivateTriangleBounds

namespace ThermoCoreCompatibility.Hypergraph.MonomialTriple

/-- The three branch inequalities needed for the monomial contradiction. -/
theorem split_obstruction {a b : ℝ} (ha : 0 ≤ a)
    (h₀ : 5*b < 71/25+a) (h₁ : 39/20 < b+2*a^4)
    (h₂ : 2*a+3*a^3 < 5*b) : False := by
  by_cases h : a ≤ 7/8
  · have hp := pow_le_pow_left₀ ha h 4
    norm_num at hp
    linarith
  · have hge : (7/8 : ℝ) ≤ a := le_of_lt (lt_of_not_ge h)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7/8) hge 3
    norm_num at hp
    linarith

/-- Three literal branches, gains 3,4,3, share exactly a,b and current a-b.
All private activities belong to the fixed declared boxes. -/
theorem no_common_state {a b c₀ c₁ c₂ : ℝ} (ha : 0 ≤ a)
    (hu₀ : c₀ ≤ 71/100) (hl₁ : 65/100 ≤ c₁)
    (h₀ : TriangleProduction 3 4 2 (a^3) b c₀ (a-b))
    (h₁ : TriangleProduction 4 (1/2) 1 (a^4) b c₁ (a-b))
    (h₂ : TriangleProduction 3 1 1 (a^3) b c₂ (a-b)) : False := by
  rcases h₀ with ⟨_,h₀,_⟩
  rcases h₁ with ⟨_,_,h₁⟩
  rcases h₂ with ⟨h₂a,_,h₂c⟩
  apply split_obstruction (b := b) ha <;> nlinarith

/-- The complete family passes independent-complex productivity, with one
shared value t3 for A^3 in branches 0 and 2, and one value t4 for A^4. -/
theorem independent_complex_witness :
    TriangleProduction 3 4 2 (157/250) (37/50) (701/1000) (9/10-37/50) ∧
    TriangleProduction 4 (1/2) 1 (61/100) (37/50) (651/1000) (9/10-37/50) ∧
    TriangleProduction 3 1 1 (157/250) (37/50) (341/500) (9/10-37/50) := by
  norm_num [TriangleProduction]

theorem pair₀₁ :
    TriangleProduction 3 4 2 ((141/160)^3) (93/125) (71/100) (141/160-93/125) ∧
    TriangleProduction 4 (1/2) 1 ((141/160)^4) (93/125) (13/20) (141/160-93/125) := by
  norm_num [TriangleProduction]

theorem pair₀₂ :
    TriangleProduction 3 4 2 ((169/200)^3) (88/125) (67/100) (169/200-88/125) ∧
    TriangleProduction 3 1 1 ((169/200)^3) (88/125) (653/1000) (169/200-88/125) := by
  norm_num [TriangleProduction]

theorem pair₁₂ :
    TriangleProduction 4 (1/2) 1 ((22/25)^4) (157/200) (13/20) (22/25-157/200) ∧
    TriangleProduction 3 1 1 ((22/25)^3) (157/200) (18/25) (22/25-157/200) := by
  norm_num [TriangleProduction]

end ThermoCoreCompatibility.Hypergraph.MonomialTriple
