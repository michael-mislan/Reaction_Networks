import proofs.CoreCriticalSiphon.Siphon

namespace CoreCriticalSiphon

variable (Q : SourceCRN)

/-- The closed coordinate face on which every species in `Σ` is absent. -/
def BoundaryFace (sigma : Finset Q.Species) : Set (Q.Species → ℝ) :=
  {x | ∀ i ∈ sigma, x i = 0}

/-- Universal reactionwise tangency of a coordinate face. Quantification over
each literal reaction rules out accidental cancellation and is equivalent to
invariance for every independently positive rate assignment. -/
def UniversallyFaceInvariant (sigma : Finset Q.Species) : Prop :=
  ∀ (r : Q.Reaction) (k : ℝ), 0 < k → ∀ x ∈ BoundaryFace Q sigma,
    ∀ i ∈ sigma, Q.reactionField r k x i = 0

private theorem monomial_eq_zero_of_consumes
    {sigma : Finset Q.Species} {r : Q.Reaction} {x : Q.Species → ℝ}
    (hx : x ∈ BoundaryFace Q sigma) (hc : Consumes Q sigma r) :
    Q.monomial r x = 0 := by
  obtain ⟨j, hjSigma, hjpos⟩ := hc
  rw [SourceCRN.monomial, Finset.prod_eq_zero (Finset.mem_univ j)]
  rw [hx j hjSigma]
  exact zero_pow (Nat.ne_of_gt hjpos)

theorem siphon_implies_universallyFaceInvariant
    {sigma : Finset Q.Species} (hsigma : IsSiphon Q sigma) :
    UniversallyFaceInvariant Q sigma := by
  intro r k hk x hx i hi
  by_cases hp : 0 < Q.product r i
  · have hc : Consumes Q sigma r := hsigma r ⟨i, hi, hp⟩
    simp [SourceCRN.reactionField, monomial_eq_zero_of_consumes Q hx hc]
  · have hprod : Q.product r i = 0 := Nat.eq_zero_of_not_pos hp
    by_cases hr : Q.reactant r i = 0
    · simp [SourceCRN.reactionField, hprod, hr]
    · have hc : Consumes Q sigma r := ⟨i, hi, Nat.pos_of_ne_zero hr⟩
      simp [SourceCRN.reactionField, monomial_eq_zero_of_consumes Q hx hc]

theorem universallyFaceInvariant_implies_siphon
    {sigma : Finset Q.Species} (hface : UniversallyFaceInvariant Q sigma) :
    IsSiphon Q sigma := by
  intro r hp
  by_contra hnot
  obtain ⟨i, hiSigma, hiprod⟩ := hp
  let x : Q.Species → ℝ := fun j => if j ∈ sigma then 0 else 1
  have hx : x ∈ BoundaryFace Q sigma := by
    intro j hj
    simp [x, hj]
  have hm : Q.monomial r x = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    by_cases hjSigma : j ∈ sigma
    · have hreact : Q.reactant r j = 0 := by
        by_contra hjr
        exact hnot ⟨j, hjSigma, Nat.pos_of_ne_zero hjr⟩
      simp [x, hjSigma, hreact]
    · simp [x, hjSigma]
  have hzero := hface r 1 (by norm_num) x hx i hiSigma
  simp [SourceCRN.reactionField, hm] at hzero
  have hir : Q.reactant r i = 0 := by
    by_contra hir
    exact hnot ⟨i, hiSigma, Nat.pos_of_ne_zero hir⟩
  simp [hir] at hzero
  exact (Nat.ne_of_gt hiprod) (Nat.cast_eq_zero.mp hzero)

/-- Exact source theorem: siphonhood is precisely universal coordinate-face
invariance under literal mass-action reactions. -/
theorem siphon_iff_boundaryFace_forwardInvariant (sigma : Finset Q.Species) :
    IsSiphon Q sigma ↔ UniversallyFaceInvariant Q sigma :=
  ⟨siphon_implies_universallyFaceInvariant Q,
    universallyFaceInvariant_implies_siphon Q⟩

end CoreCriticalSiphon
