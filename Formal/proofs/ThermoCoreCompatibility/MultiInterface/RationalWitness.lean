import proofs.ThermoCoreCompatibility.MultiInterface.WeightedSource

namespace ThermoCoreCompatibility.MultiInterface

def rationalEdgeCheck (a b x y : ℚ) : Bool :=
  decide (0 < 2*(b*(y-x^2))-a*(x-y) ∧ 0 < a*(x-y)-b*(y-x^2))

def rationalFactors (a b : ℚ) (ha : 0 < a) (hb : 0 < b) : Factors where
  a := a
  b := b
  a_pos := by exact_mod_cast ha
  b_pos := by exact_mod_cast hb

theorem rationalEdgeCheck_sound (a b x y : ℚ) (ha : 0 < a) (hb : 0 < b)
    (h : rationalEdgeCheck a b x y = true) :
    (rationalFactors a b ha hb).Productive (x : ℝ) (y : ℝ) := by
  have hq : 0 < 2*(b*(y-x^2))-a*(x-y) ∧ 0 < a*(x-y)-b*(y-x^2) := of_decide_eq_true h
  change (0 : ℝ) < 2*((b : ℝ)*((y : ℝ)-(x : ℝ)^2))-(a : ℝ)*((x : ℝ)-(y : ℝ)) ∧
    0 < (a : ℝ)*((x : ℝ)-(y : ℝ))-(b : ℝ)*((y : ℝ)-(x : ℝ)^2)
  exact_mod_cast hq

def rationalFamilyCheck {V E : Type*} [Fintype V] [Fintype E]
    (G : Hypergraph.PairAssembly V E) (a b : E → ℚ) (z lo hi : V → ℚ) : Bool :=
  decide ((∀ v, lo v ≤ z v ∧ z v ≤ hi v) ∧
    ∀ e, rationalEdgeCheck (a e) (b e) (z (G.src e)) (z (G.dst e)) = true)

theorem rationalFamilyCheck_eq_true {V E : Type*} [Fintype V] [Fintype E]
    (G : Hypergraph.PairAssembly V E) (a b : E → ℚ) (z lo hi : V → ℚ)
    (hbox : ∀ v, lo v ≤ z v ∧ z v ≤ hi v)
    (hedge : ∀ e, rationalEdgeCheck (a e) (b e) (z (G.src e)) (z (G.dst e)) = true) :
    rationalFamilyCheck G a b z lo hi = true := by
  unfold rationalFamilyCheck
  exact decide_eq_true ⟨hbox,hedge⟩

theorem rationalFamilyCheck_sound {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : Hypergraph.PairAssembly V E) (a b : E → ℚ) (z lo hi : V → ℚ)
    (ha : ∀ e, 0 < a e) (hb : ∀ e, 0 < b e)
    (h : rationalFamilyCheck G a b z lo hi = true) :
    (∀ v, (lo v : ℝ) ≤ (z v : ℝ) ∧ (z v : ℝ) ≤ (hi v : ℝ)) ∧
    ∀ e, (WeightedSource.motif G (fun e => rationalFactors (a e) (b e) (ha e) (hb e)) e).IsPAC ∧
      (WeightedSource.motif G (fun e => rationalFactors (a e) (b e) (ha e) (hb e)) e).Productive
        ((WeightedSource.network G (fun e => rationalFactors (a e) (b e) (ha e) (hb e))).current
          (fun v => (z v : ℝ))) := by
  have hc : (∀ v, lo v ≤ z v ∧ z v ≤ hi v) ∧
      ∀ e, rationalEdgeCheck (a e) (b e) (z (G.src e)) (z (G.dst e)) = true :=
    of_decide_eq_true h
  constructor
  · intro v
    exact_mod_cast hc.1 v
  · intro e
    refine ⟨WeightedSource.isPAC _ _ e,?_⟩
    apply (WeightedSource.current_productive_iff _ _ e _).2
    exact rationalEdgeCheck_sound _ _ _ _ (ha e) (hb e) (hc.2 e)

end ThermoCoreCompatibility.MultiInterface
