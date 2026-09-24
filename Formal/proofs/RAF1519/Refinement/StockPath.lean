import proofs.RAF1519.Refinement.CountFreeFloor
import proofs.RAF1519.Refinement.Stock

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators

def stockWeight : State := ![0,0,1,9/8,7/5,9/5,0]

theorem stock_weighted (c : State) : stock c = weightedCoordinate stockWeight c := by
  simp [stock,weightedCoordinate,stockWeight,free,ProductiveRecovery.Y,Fin.sum_univ_succ]
  ring

theorem stockWeight_bounds : (∀ s, 0 ≤ stockWeight s) ∧ (∑ s, stockWeight s) ≤ 11/2 := by
  constructor
  · intro s; fin_cases s <;> norm_num [stockWeight]
  · norm_num [stockWeight,Fin.sum_univ_succ]

def countStock {n : ℕ} (V : ℝ) (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (t : ℝ) (i : Fin n) : ℝ := stock (fun s => countPath V z t (i,s))

def stockPrimitive {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (K : ℕ) (t : ℝ) (i : Fin n) : ℝ :=
  weightedCoordinate stockWeight (fun s => countDriftPrimitive r d k V z K (i,s) t)

theorem stockPrimitive_continuous {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (K : ℕ) (i : Fin n) :
    Continuous (fun t => stockPrimitive r d k V z K t i) := by
  unfold stockPrimitive weightedCoordinate
  apply continuous_finsetSum
  intro s _
  exact continuous_const.mul (countDriftPrimitive_continuous r d k V z K (i,s))

theorem stockPrimitive_zero {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K : ℕ) (i : Fin n) :
    stockPrimitive r d k V z K 0 i = stock (concentration V (fun s => (z 0).1 (i,s))) := by
  unfold stockPrimitive
  simp only [countDriftPrimitive_zero r d k V z hh K,stock_weighted]
  rfl

theorem weighted_molecular_stock_drift {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : V ≠ 0) (hsym : ∀ i j, k i j=k j i)
    (N : MolecularState n) (i : Fin n) :
    weightedCoordinate stockWeight (fun s => ∑ a, molecularRate r d k V N a*molecularIncrement r d k V (i,s) N a) =
      stock (countDrift (r i) (d i) (1/100) (1/100) V (concentration V (fun s => N (i,s))))+
      graphDiffusion k (fun j => stock (concentration V (fun s => N (j,s)))) i := by
  have he : (fun s => ∑ a, molecularRate r d k V N a*molecularIncrement r d k V (i,s) N a) =
      fun s => countDrift (r i) (d i) (1/100) (1/100) V (concentration V (fun s => N (i,s))) s+
        graphDiffusion k (fun j => concentration V (fun s => N (j,s)) s) i := by
    funext s
    exact molecular_drift_binding r d k V hV hsym N (i,s)
  rw [he,weightedCoordinate_add,weightedCoordinate_diffusion]
  simp only [stock_weighted]

theorem stockPrimitive_right_derivative {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : V ≠ 0) (hsym : ∀ i j, k i j=k j i)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K : ℕ) (i : Fin n) (t : ℝ) (ht : 0 ≤ t)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z)) :
    HasDerivWithinAt (fun u => stockPrimitive r d k V z K u i)
      (stock (countDrift (r i) (d i) (1/100) (1/100) V (fun s => countPath V z t (i,s)))+
        graphDiffusion k (countStock V z t) i) (Set.Ici t) t := by
  have hd := weightedCoordinate_right_derivative stockWeight
    (fun u s => countDriftPrimitive r d k V z K (i,s) u) _ t
    (fun s => countPrimitive_path_derivative r d k V z hh K (i,s) t ht hK)
  rw [weighted_molecular_stock_drift r d k V hV hsym] at hd
  exact hd

theorem stock_noise_from_coordinates (x y : State) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ s, |x s-y s| ≤ ε) : |stock x-weightedCoordinate stockWeight y| ≤ (11/2)*ε := by
  rw [stock_weighted]
  exact (weightedCoordinate_noise _ _ _ ε stockWeight_bounds.1 h).trans
    (mul_le_mul_of_nonneg_right stockWeight_bounds.2 hε)

end
end RAF1519.Refinement
