import proofs.RAF1519.Refinement.CountLaw

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators

def massWeight (i : Fin 7) : ℝ := weightA i+weightB i

theorem mass_weight_positive (i : Fin 7) : 1 ≤ massWeight i := by
  fin_cases i <;> norm_num [massWeight,weightA,weightB]

def localMassChange : LocalChannel → ℝ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr i) => -massWeight i

theorem local_mass_change (r d : ℝ) (j : LocalChannel) :
    (∑ i, massWeight i*((localReaction r d j).produce i-(localReaction r d j).consume i : ℝ)) =
      localMassChange j := by
  rcases j with ⟨j,b⟩ | (i | i)
  · cases b <;> fin_cases j <;>
      norm_num [localReaction,localMassChange,chemicalInput,chemicalOutput,massWeight,
        weightA,weightB,Fin.sum_univ_succ]
  · fin_cases i <;> norm_num [localReaction,localMassChange,massWeight,weightA,weightB,
      Fin.sum_univ_succ,Pi.single_apply,Fin.castLE]
  · simp [localReaction,localMassChange,Pi.single_apply]

def molecularMass {n : ℕ} (N : MolecularState n) : ℝ :=
  1+Reaction.material (fun p => massWeight p.2) N

theorem molecular_mass_positive {n : ℕ} (N : MolecularState n) : 0 < molecularMass N := by
  unfold molecularMass Reaction.material
  have h := Finset.sum_nonneg (s := Finset.univ) (fun p _ =>
    mul_nonneg (le_trans (by norm_num) (mass_weight_positive p.2)) (Nat.cast_nonneg (N p)))
  linarith

def graphMassChange {n : ℕ} : CountChannel n → ℝ
  | .inl (_,j) => localMassChange j
  | .inr _ => 0

theorem graph_mass_change {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (a : CountChannel n) :
    (∑ p, massWeight p.2*((graphReaction r d k a).produce p-
      (graphReaction r d k a).consume p : ℝ)) = graphMassChange a := by
  rcases a with ⟨i,j⟩ | ⟨i,j,s⟩
  · simp only [graphReaction,atNode,graphMassChange,Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i]
    · simpa only [if_pos rfl] using local_mass_change (r i) (d i) j
    · intro b _ hbi
      simp [hbi]
    · simp
  · simp [graphReaction,graphMassChange,Pi.single_apply,mul_sub,Finset.sum_sub_distrib,mul_ite]

theorem molecular_mass_increment {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (N : MolecularState n) (a : CountChannel n) :
    molecularRate r d k V N a*(molecularMass (molecularNext r d k N a)-molecularMass N) =
      molecularRate r d k V N a*graphMassChange a := by
  unfold molecularMass molecularNext molecularRate
  rw [add_sub_add_left_eq_sub,Reaction.material_increment,graph_mass_change]

def foodBound {n : ℕ} (V : ℝ) : CountChannel n → ℝ
  | .inl (_,.inr (.inl _)) => V
  | _ => 0

theorem molecular_generator_bound {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 ≤ V) (N : MolecularState n) :
    (∑ a, molecularRate r d k V N a*(molecularMass (molecularNext r d k N a)-molecularMass N)) ≤
      2*n*V := by
  have hterm (a : CountChannel n) :
      molecularRate r d k V N a*(molecularMass (molecularNext r d k N a)-molecularMass N) ≤ foodBound V a := by
    rw [molecular_mass_increment]
    rcases a with ⟨i,j⟩ | ⟨i,j,s⟩
    · rcases j with ⟨j,b⟩ | (j | j)
      · simp [graphMassChange,localMassChange,foodBound]
      · simp [graphMassChange,localMassChange,foodBound,food_rate]
      · change molecularRate r d k V N _*(-massWeight j) ≤ 0
        exact mul_nonpos_of_nonneg_of_nonpos
          (molecular_rate_nonnegative r d k V hr hd hk hV N _)
          (neg_nonpos.mpr (le_trans (by norm_num) (mass_weight_positive j)))
    · simp [graphMassChange,foodBound]
  calc
    _ ≤ ∑ a, foodBound V a := Finset.sum_le_sum (fun a _ => hterm a)
    _ = 2*n*V := by
      simp [Fintype.sum_sum_type,Fintype.sum_prod_type,foodBound]
      ring

end
end RAF1519.Refinement
