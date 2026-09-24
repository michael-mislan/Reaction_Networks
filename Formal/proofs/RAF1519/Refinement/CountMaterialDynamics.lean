import proofs.RAF1519.Refinement.MaterialLinear
import proofs.RAF1519.Refinement.CountPath

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 30000

def materialWeight : Bool → State
  | false => weightA
  | true => weightB

theorem materialWeight_bounds (b : Bool) :
    (∀ s, 0 ≤ materialWeight b s) ∧ (∑ s, materialWeight b s) ≤ 9 := by
  cases b
  · exact ⟨material_weight_bounds.1,material_weight_bounds.2.2.1.le⟩
  · exact ⟨material_weight_bounds.2.1,by rw [materialWeight,material_weight_bounds.2.2.2]; norm_num⟩

theorem weighted_source_material (b : Bool) (r d V : ℝ) (c : State) :
    weightedCoordinate (materialWeight b) (countDrift r d (1/100) (1/100) V c) =
      1-weightedCoordinate (materialWeight b) c := by
  cases b
  · simpa only [materialA_weighted] using count_material_A r d (1/100) (1/100) V c
  · simpa only [materialB_weighted] using count_material_B r d (1/100) (1/100) V c

theorem weighted_molecular_material_drift {n : ℕ} (b : Bool) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : V ≠ 0) (hsym : ∀ i j, k i j=k j i)
    (N : MolecularState n) (i : Fin n) :
    weightedCoordinate (materialWeight b) (fun s =>
      ∑ a, molecularRate r d k V N a*molecularIncrement r d k V (i,s) N a) =
      1-weightedCoordinate (materialWeight b) (concentration V (fun s => N (i,s)))+
      graphDiffusion k (fun j => weightedCoordinate (materialWeight b)
        (concentration V (fun s => N (j,s)))) i := by
  have he : (fun s => ∑ a, molecularRate r d k V N a*molecularIncrement r d k V (i,s) N a) =
      fun s => countDrift (r i) (d i) (1/100) (1/100) V (concentration V (fun s => N (i,s))) s+
        graphDiffusion k (fun j => concentration V (fun s => N (j,s)) s) i := by
    funext s
    exact molecular_drift_binding r d k V hV hsym N (i,s)
  rw [he,weightedCoordinate_add,weighted_source_material,weightedCoordinate_diffusion]

def countMaterial {n : ℕ} (b : Bool) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (t : ℝ) (i : Fin n) : ℝ :=
  weightedCoordinate (materialWeight b) (fun s => countPath V z t (i,s))

def materialPrimitive {n : ℕ} (b : Bool) (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (K : ℕ) (t : ℝ) (i : Fin n) : ℝ :=
  weightedCoordinate (materialWeight b) (fun s => countDriftPrimitive r d k V z K (i,s) t)

theorem materialPrimitive_continuous {n : ℕ} (b : Bool) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (K : ℕ) (i : Fin n) :
    Continuous (fun t => materialPrimitive b r d k V z K t i) := by
  unfold materialPrimitive weightedCoordinate
  apply continuous_finsetSum
  intro s _
  exact continuous_const.mul (countDriftPrimitive_continuous r d k V z K (i,s))

theorem materialPrimitive_right_derivative {n : ℕ} (b : Bool) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : V ≠ 0) (hsym : ∀ i j, k i j=k j i)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K : ℕ) (i : Fin n) (t : ℝ) (ht : 0 ≤ t)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z)) :
    HasDerivWithinAt (fun u => materialPrimitive b r d k V z K u i)
      (1-countMaterial b V z t i+graphDiffusion k (countMaterial b V z t) i) (Set.Ici t) t := by
  have hd := weightedCoordinate_right_derivative (materialWeight b)
    (fun u s => countDriftPrimitive r d k V z K (i,s) u) _ t
    (fun s => countPrimitive_path_derivative r d k V z hh K (i,s) t ht hK)
  rw [weighted_molecular_material_drift b r d k V hV hsym] at hd
  exact hd

theorem material_noise_from_coordinates (b : Bool) (x y : State) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ s, |x s-y s| ≤ ε) :
    |weightedCoordinate (materialWeight b) x-weightedCoordinate (materialWeight b) y| ≤ 9*ε := by
  exact (weightedCoordinate_noise _ _ _ ε (materialWeight_bounds b).1 h).trans
    (mul_le_mul_of_nonneg_right (materialWeight_bounds b).2 hε)

end
end RAF1519.Refinement
