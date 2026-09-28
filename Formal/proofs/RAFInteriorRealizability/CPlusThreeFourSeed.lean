import proofs.RAFInteriorRealizability.CPlusThreeRestriction

/-!
The four-vertex graph obstruction needed to bound the seed set in the sharp
three-element threshold argument.
-/

namespace RAFInteriorRealizability

/-- Four vertices cannot have every triple predecessor-supported while every
singleton and pair is unsupported. The proof reduces to a small propositional
contradiction among the sixteen possible directed incidences. -/
theorem four_seed_graph_obstruction (P : Fin 4 → Finset (Fin 4))
    (hsmall : ∀ S : Finset (Fin 4), S.Nonempty → S.card < 3 → ¬ PredSupported P S)
    (htriple : ∀ S : Finset (Fin 4), S.card = 3 → PredSupported P S) : False := by
  have h0 := hsmall ({0} : Finset (Fin 4)) (by decide) (by decide)
  have h1 := hsmall ({1} : Finset (Fin 4)) (by decide) (by decide)
  have h2 := hsmall ({2} : Finset (Fin 4)) (by decide) (by decide)
  have h3 := hsmall ({3} : Finset (Fin 4)) (by decide) (by decide)
  have h01 := hsmall ({0, 1} : Finset (Fin 4)) (by decide) (by decide)
  have h02 := hsmall ({0, 2} : Finset (Fin 4)) (by decide) (by decide)
  have h03 := hsmall ({0, 3} : Finset (Fin 4)) (by decide) (by decide)
  have h12 := hsmall ({1, 2} : Finset (Fin 4)) (by decide) (by decide)
  have h13 := hsmall ({1, 3} : Finset (Fin 4)) (by decide) (by decide)
  have h23 := hsmall ({2, 3} : Finset (Fin 4)) (by decide) (by decide)
  have h012 := htriple ({0, 1, 2} : Finset (Fin 4)) (by decide)
  have h013 := htriple ({0, 1, 3} : Finset (Fin 4)) (by decide)
  have h023 := htriple ({0, 2, 3} : Finset (Fin 4)) (by decide)
  have h123 := htriple ({1, 2, 3} : Finset (Fin 4)) (by decide)
  simp [PredSupported] at h0 h1 h2 h3 h01 h02 h03 h12 h13 h23 h012 h013 h023 h123
  simp [h0, h1, h2, h3] at h01 h02 h03 h12 h13 h23 h012 h013 h023 h123
  have htwo :
      ((1 : Fin 4) ∈ P 0 ∧ (2 : Fin 4) ∈ P 0) ∨
      ((1 : Fin 4) ∈ P 0 ∧ (3 : Fin 4) ∈ P 0) ∨
      ((2 : Fin 4) ∈ P 0 ∧ (3 : Fin 4) ∈ P 0) := by
    rcases h012.1 with ha | hb
    · rcases h023.1 with hc | hd
      · exact Or.inl ⟨ha, hc⟩
      · exact Or.inr (Or.inl ⟨ha, hd⟩)
    · rcases h013.1 with hc | hd
      · exact Or.inl ⟨hc, hb⟩
      · exact Or.inr (Or.inr ⟨hb, hd⟩)
  rcases htwo with h12' | h13' | h23'
  · have hn01 := h01 h12'.1
    have hn02 := h02 h12'.2
    have h31 : (3 : Fin 4) ∈ P 1 := h013.2.1.resolve_left hn01
    have h32 : (3 : Fin 4) ∈ P 2 := h023.2.1.resolve_left hn02
    have hn13 := h13 h31
    have hn23 := h23 h32
    exact h123.2.2.elim hn13 hn23
  · have hn01 := h01 h13'.1
    have hn03 := h03 h13'.2
    have h21 : (2 : Fin 4) ∈ P 1 := h012.2.1.resolve_left hn01
    have h23' : (2 : Fin 4) ∈ P 3 := h023.2.2.resolve_left hn03
    have hn12 := h12 h21
    have hn32 : (3 : Fin 4) ∉ P 2 := by
      intro h32
      exact (h23 h32) h23'
    exact h123.2.1.elim hn12 hn32
  · have hn02 := h02 h23'.1
    have hn03 := h03 h23'.2
    have h12' : (1 : Fin 4) ∈ P 2 := h012.2.2.resolve_left hn02
    have h13' : (1 : Fin 4) ∈ P 3 := h013.2.2.resolve_left hn03
    have hn21 : (2 : Fin 4) ∉ P 1 := by
      intro h21
      exact (h12 h21) h12'
    have hn31 : (3 : Fin 4) ∉ P 1 := by
      intro h31
      exact (h13 h31) h13'
    exact h123.1.elim hn21 hn31

end RAFInteriorRealizability
