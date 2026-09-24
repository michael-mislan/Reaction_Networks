import proofs.ThermoCoreCompatibility.Hypergraph.PrivateTriangleBounds

namespace ThermoCoreCompatibility.Hypergraph

/-- Data for a literal fan, with fixed kinetics and a fixed private box.
The terminal complex activity of branch i is a^(gain i). -/
structure FanData (ι : Type*) where
  gain : ι → ℕ
  gain_ge_two : ∀ i, 2 ≤ gain i
  sharedFactor : ℝ
  sharedFactor_pos : 0 < sharedFactor
  firstFactor : ι → ℝ
  firstFactor_pos : ∀ i, 0 < firstFactor i
  secondFactor : ι → ℝ
  secondFactor_pos : ∀ i, 0 < secondFactor i
  lower : ι → ℝ
  upper : ι → ℝ
  lower_pos : ∀ i, 0 < lower i
  box_nonempty : ∀ i, lower i ≤ upper i

def FanData.PrivateConditions {ι : Type*} (D : FanData ι) (a b : ℝ) (i : ι) : Prop :=
  let j := D.sharedFactor * (a - b)
  let t := a ^ D.gain i
  let top := (D.firstFactor i * b + D.secondFactor i * t) /
    (D.firstFactor i + D.secondFactor i)
  b - j / D.firstFactor i < top ∧
    t + j / ((D.gain i : ℝ) * D.secondFactor i) < top ∧
    D.lower i < top ∧ b - j / D.firstFactor i < D.upper i ∧
    t + j / ((D.gain i : ℝ) * D.secondFactor i) < D.upper i

/-- Omitted branches keep their nonempty boxes but impose no production conditions.
All retained branches use the same species a,b and one shared current. -/
def FanData.LiteralWitness {ι : Type*} (D : FanData ι) (F : Set ι) (a b : ℝ) : Prop :=
  ∃ c : ι → ℝ, (∀ i, D.lower i ≤ c i ∧ c i ≤ D.upper i) ∧
    ∀ i ∈ F, TriangleProduction (D.gain i) (D.firstFactor i) (D.secondFactor i)
      (a ^ D.gain i) b (c i) (D.sharedFactor * (a - b))

theorem FanData.literalWitness_iff {ι : Type*} (D : FanData ι) (F : Set ι) (a b : ℝ) :
    D.LiteralWitness F a b ↔ ∀ i ∈ F, D.PrivateConditions a b i := by
  classical
  have hm (i : ι) : 0 < (D.gain i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (D.gain_ge_two i))
  constructor
  · rintro ⟨c, hc, hp⟩ i hi
    exact (privateTriangle_box_iff (hm i) (D.firstFactor_pos i)
      (D.secondFactor_pos i) (D.box_nonempty i)).1
        ⟨c i, (hc i).1, (hc i).2, hp i hi⟩
  · intro h
    have hex (i : ι) : ∃ c : ℝ, D.lower i ≤ c ∧ c ≤ D.upper i ∧
        (i ∈ F → TriangleProduction (D.gain i) (D.firstFactor i) (D.secondFactor i)
          (a ^ D.gain i) b c (D.sharedFactor * (a - b))) := by
      by_cases hi : i ∈ F
      · obtain ⟨c, hl, hu, hp⟩ :=
          (privateTriangle_box_iff (hm i) (D.firstFactor_pos i)
            (D.secondFactor_pos i) (D.box_nonempty i)).2 (h i hi)
        exact ⟨c, hl, hu, fun _ => hp⟩
      · exact ⟨D.lower i, le_rfl, D.box_nonempty i, fun hmem => (hi hmem).elim⟩
    choose c hc using hex
    exact ⟨c, fun i => ⟨(hc i).1, (hc i).2.1⟩, fun i hi => (hc i).2.2 hi⟩

/-- The private elimination is exact inside the same closed global box. -/
theorem FanData.boundedFan_iff {ι : Type*} (D : FanData ι) (F : Set ι)
    (la ua lb ub : ℝ) :
    (∃ a b, la ≤ a ∧ a ≤ ua ∧ lb ≤ b ∧ b ≤ ub ∧ D.LiteralWitness F a b) ↔
      ∃ a b, la ≤ a ∧ a ≤ ua ∧ lb ≤ b ∧ b ≤ ub ∧
        ∀ i ∈ F, D.PrivateConditions a b i := by
  simp_rw [D.literalWitness_iff]

end ThermoCoreCompatibility.Hypergraph
