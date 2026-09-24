import proofs.RAFQueryCompilation.FreshEvaluation
import proofs.RAFQueryCompilation.CappedBounds

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

omit [DecidableEq R] in
theorem freshClosureFuel_bound (Q : CRS M R) (A : Finset R) (fuel : ℕ) (pool : Finset M)
    (e i o : ℕ) (he : A.card ≤ e)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i) (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o) :
    (freshClosureFuel Q A fuel pool).2 ≤ fuel*terminalCap e i o (Fintype.card M) := by
  induction fuel generalizing pool with
  | zero => simp [freshClosureFuel]
  | succ fuel ih =>
    have hs := closureTerminalCharge_le Q A pool e i o (Fintype.card M) he
      (Finset.card_le_univ _) hi ho
    change closureTerminalCharge Q A pool ≤ terminalCap e i o (Fintype.card M) at hs
    have ht := ih (closureStep Q A pool)
    simp only [freshClosureFuel,Nat.add_mul,Nat.one_mul]
    split <;> dsimp only
    all_goals omega

def freshRoundCap (e i o c p : ℕ) : ℕ :=
  p+p*terminalCap e i o p+supportCap e i c p

theorem freshPruningFuel_bound (Q : CRS M R) (cats : R → Finset M) (fuel : ℕ)
    (A : Finset R) (e i o c : ℕ) (he : A.card ≤ e)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i) (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o)
    (hc : ∀ r ∈ A, (cats r).card ≤ c) :
    (freshPruningFuel Q cats fuel A).2 ≤ fuel*freshRoundCap e i o c (Fintype.card M) := by
  induction fuel generalizing A with
  | zero => simp [freshPruningFuel]
  | succ fuel ih =>
    let pool := (freshClosureFuel Q A (Fintype.card M) Q.food).1
    have hcl := freshClosureFuel_bound Q A (Fintype.card M) Q.food e i o he hi ho
    have hs := supportCharge_le Q cats A pool e i c (Fintype.card M) he
      (Finset.card_le_univ _) hi hc
    change supportCharge Q cats A pool ≤ supportCap e i c (Fintype.card M) at hs
    have hf := Finset.card_le_univ Q.food
    have hsub : pruneWithPool Q (fun x r => x ∈ cats r) A pool ⊆ A := Finset.filter_subset _ _
    have ht := ih _ ((Finset.card_le_card hsub).trans he)
      (fun r hr => hi r (hsub hr)) (fun r hr => ho r (hsub hr)) (fun r hr => hc r (hsub hr))
    have hfee : Q.food.card+(freshClosureFuel Q A (Fintype.card M) Q.food).2+
        supportCharge Q cats A pool ≤ freshRoundCap e i o c (Fintype.card M) :=
      Nat.add_le_add (Nat.add_le_add hf hcl) hs
    dsimp only [pool] at hfee ht
    simp only [freshPruningFuel,Nat.add_mul,Nat.one_mul]
    split <;> dsimp only
    all_goals omega

theorem freshEvaluate_bound (Q : CRS M R) (cats : R → Finset M) (A : Finset R)
    (e i o c : ℕ) (he : A.card ≤ e)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i) (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o)
    (hc : ∀ r ∈ A, (cats r).card ≤ c) :
    (freshEvaluate Q cats A).2 ≤ e+e*freshRoundCap e i o c (Fintype.card M) := by
  have h := freshPruningFuel_bound Q cats A.card A e i o c he hi ho hc
  have hm := Nat.mul_le_mul_right (freshRoundCap e i o c (Fintype.card M)) he
  dsimp only [freshEvaluate]
  omega

end RAFQueryCompilation
