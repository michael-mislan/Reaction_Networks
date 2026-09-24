import proofs.ThermoCoreCompatibility.Hypergraph.FanElimination
import proofs.ThermoCoreCompatibility.Hypergraph.FiniteBounds

namespace ThermoCoreCompatibility.Hypergraph

noncomputable section

def FanData.lowerBound {ι : Type*} (D : FanData ι) (a : ℝ) (i : ι) : Fin 3 → ℝ :=
  let m : ℝ := D.gain i
  let x := D.firstFactor i
  let y := D.secondFactor i
  let z := D.sharedFactor
  let t := a ^ D.gain i
  ![((x+y)*z*a+m*x*y*t)/(m*x*y+(x+y)*z),
    ((x+y)*D.lower i-y*t)/x,
    (z*a+m*y*(t-D.upper i))/z]

def FanData.upperBound {ι : Type*} (D : FanData ι) (a : ℝ) (i : ι) : Fin 2 → ℝ :=
  let x := D.firstFactor i
  let y := D.secondFactor i
  let z := D.sharedFactor
  let t := a ^ D.gain i
  ![((x+y)*z*a+x*y*t)/(x*y+(x+y)*z),
    (x*D.upper i+z*a)/(x+z)]

theorem FanData.privateConditions_iff_bounds {ι : Type*} (D : FanData ι)
    (a b : ℝ) (i : ι) :
    D.PrivateConditions a b i ↔
      (∀ r, D.lowerBound a i r < b) ∧ (∀ r, b < D.upperBound a i r) := by
  have hm : 0 < (D.gain i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (D.gain_ge_two i))
  have hx := D.firstFactor_pos i
  have hy := D.secondFactor_pos i
  have hz := D.sharedFactor_pos
  have he := (privateTriangle_box_iff (A := a ^ D.gain i) (B := b)
    (j := D.sharedFactor * (a - b)) hm hx hy (D.box_nonempty i)).symm.trans
    (privateTriangle_box_iff_polynomial hm hx hy (D.box_nonempty i))
  change D.PrivateConditions a b i ↔ _
  unfold FanData.PrivateConditions
  rw [he]
  simp only [FanData.lowerBound, FanData.upperBound, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.forall_fin_zero,
    and_true]
  have hden₁ : 0 < (D.gain i : ℝ) * D.firstFactor i * D.secondFactor i +
      (D.firstFactor i + D.secondFactor i) * D.sharedFactor := by positivity
  have hden₂ : 0 < D.firstFactor i * D.secondFactor i +
      (D.firstFactor i + D.secondFactor i) * D.sharedFactor := by positivity
  have hden₃ : 0 < D.firstFactor i + D.sharedFactor := by positivity
  rw [div_lt_iff₀ hden₁, div_lt_iff₀ hx, div_lt_iff₀ hz,
    lt_div_iff₀ hden₂, lt_div_iff₀ hden₃]
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄,h₅⟩
    exact ⟨⟨by nlinarith, by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  · rintro ⟨⟨h₁,h₂,h₃⟩,h₄,h₅⟩
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Only a remains a physical unknown. All bounds are explicit univariate
polynomials with positive constant denominators and degree at most the gains. -/
def FanData.UnivariateConditions {ι : Type*} (D : FanData ι) (a lb ub : ℝ) : Prop :=
  (∀ i r k s, D.lowerBound a i r < D.upperBound a k s) ∧
    (∀ k s, lb < D.upperBound a k s) ∧ (∀ i r, D.lowerBound a i r < ub)

theorem FanData.commonB_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (D : FanData ι) (a lb ub : ℝ) (hbox : lb ≤ ub) :
    (∃ b, lb ≤ b ∧ b ≤ ub ∧ D.LiteralWitness Set.univ a b) ↔
      D.UnivariateConditions a lb ub := by
  have he := finite_bounds_box_iff
    (Finset.univ : Finset (ι × Fin 3)) (Finset.univ : Finset (ι × Fin 2))
    Finset.univ_nonempty Finset.univ_nonempty
    (fun p => D.lowerBound a p.1 p.2) (fun p => D.upperBound a p.1 p.2) hbox
  simp only [Finset.mem_univ, forall_const, Prod.forall] at he
  constructor
  · rintro ⟨b, hl, hu, hw⟩
    have hp := (D.literalWitness_iff Set.univ a b).1 hw
    have hb (i : ι) := (D.privateConditions_iff_bounds a b i).1 (hp i (Set.mem_univ i))
    exact he.1 ⟨b, hl, hu, fun i => (hb i).1, fun i => (hb i).2⟩
  · intro h
    obtain ⟨b, hl, hu, hL, hU⟩ := he.2 h
    refine ⟨b, hl, hu, (D.literalWitness_iff Set.univ a b).2 ?_⟩
    intro i _
    exact (D.privateConditions_iff_bounds a b i).2 ⟨hL i, hU i⟩

/-- Complete literal-equation fan elimination, with a physical reconstruction
of every private activity in the same box and the same shared current. -/
theorem FanData.boundedFan_univariate_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (D : FanData ι) (la ua lb ub : ℝ) (hbox : lb ≤ ub) :
    (∃ a b, la ≤ a ∧ a ≤ ua ∧ lb ≤ b ∧ b ≤ ub ∧ D.LiteralWitness Set.univ a b) ↔
      ∃ a, la ≤ a ∧ a ≤ ua ∧ D.UnivariateConditions a lb ub := by
  constructor
  · rintro ⟨a, b, ha, hau, hb, hbu, hw⟩
    exact ⟨a, ha, hau, (D.commonB_iff a lb ub hbox).1 ⟨b, hb, hbu, hw⟩⟩
  · rintro ⟨a, ha, hau, h⟩
    obtain ⟨b, hb, hbu, hw⟩ := (D.commonB_iff a lb ub hbox).2 h
    exact ⟨a, b, ha, hau, hb, hbu, hw⟩

end

end ThermoCoreCompatibility.Hypergraph
