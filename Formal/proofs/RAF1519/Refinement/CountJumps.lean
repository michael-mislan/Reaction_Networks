import proofs.RAF1519.Refinement.CountLaw

namespace RAF1519.Refinement
noncomputable section
open Classical

theorem local_stoichiometry_bounded (r d : ℝ) (a : LocalChannel) (s : Fin 7) :
    (localReaction r d a).consume s ≤ 2 ∧ (localReaction r d a).produce s ≤ 2 := by
  rcases a with ⟨j,b⟩ | (i | i)
  · cases b <;> fin_cases j <;> fin_cases s <;>
      norm_num [localReaction,chemicalInput,chemicalOutput]
  · by_cases h : s=Fin.castLE (by omega : 2 ≤ 7) i <;>
      simp [localReaction,h]
  · by_cases h : s=i <;> simp [localReaction,h]

theorem graph_stoichiometry_bounded {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (a : CountChannel n) (p : Fin n × Fin 7) :
    (graphReaction r d k a).consume p ≤ 2 ∧ (graphReaction r d k a).produce p ≤ 2 := by
  rcases a with ⟨i,j⟩ | ⟨i,j,s⟩
  · by_cases h : p.1=i
    · simpa only [graphReaction,atNode,if_pos h] using local_stoichiometry_bounded (r i) (d i) j p.2
    · simp [graphReaction,atNode,h]
  · simp only [graphReaction,Pi.single_apply]
    constructor <;> split_ifs <;> norm_num

theorem molecular_jump_bound {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (N : MolecularState n) (a : CountChannel n) (p : Fin n × Fin 7) :
    |(molecularNext r d k N a p:ℝ)-(N p:ℝ)| ≤ 2 := by
  let R := graphReaction r d k a
  have hc : (R.consume p:ℝ) ≤ 2 := by exact_mod_cast (graph_stoichiometry_bounded r d k a p).1
  have hp : (R.produce p:ℝ) ≤ 2 := by exact_mod_cast (graph_stoichiometry_bounded r d k a p).2
  by_cases h : R.enabled N
  · change |(R.next N p:ℝ)-(N p:ℝ)| ≤ 2
    rw [R.next_of_enabled N h p]
    have hc0 : (0:ℝ) ≤ R.consume p := Nat.cast_nonneg _
    have hp0 : (0:ℝ) ≤ R.produce p := Nat.cast_nonneg _
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · change |(R.next N p:ℝ)-(N p:ℝ)| ≤ 2
    simp [Reaction.next,h]

def molecularIncrement {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℝ)
    (p : Fin n × Fin 7) (N : MolecularState n) (a : CountChannel n) : ℝ :=
  ((molecularNext r d k N a p:ℝ)-(N p:ℝ))/V

theorem molecular_increment_bound {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : 0 < V)
    (p : Fin n × Fin 7) (N : MolecularState n) (a : CountChannel n) :
    |molecularIncrement r d k V p N a| ≤ 2/V := by
  rw [molecularIncrement,abs_div,abs_of_pos hV]
  exact div_le_div_of_nonneg_right (molecular_jump_bound r d k N a p) hV.le

theorem reaction_next_unchanged {ι : Type*} (R : Reaction ι) (N : ι → ℕ) (i : ι)
    (hc : R.consume i = 0) (hp : R.produce i = 0) : R.next N i = N i := by
  by_cases h : R.enabled N <;> simp [Reaction.next,h,hc,hp]

theorem local_increment_off_node {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (N : MolecularState n)
    (p : Fin n × Fin 7) (i : Fin n) (a : LocalChannel) (hi : p.1 ≠ i) :
    molecularIncrement r d k V p N (.inl (i,a)) = 0 := by
  have h : molecularNext r d k N (.inl (i,a)) p = N p := by
    apply reaction_next_unchanged <;> simp [graphReaction,atNode,hi]
  simp [molecularIncrement,h]

theorem exchange_increment_off_nodes {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (N : MolecularState n)
    (p : Fin n × Fin 7) (i j : Fin n) (s : Fin 7) (hi : p ≠ (i,s)) (hj : p ≠ (j,s)) :
    molecularIncrement r d k V p N (.inr (i,j,s)) = 0 := by
  have h : molecularNext r d k N (.inr (i,j,s)) p = N p := by
    apply reaction_next_unchanged <;> simp [graphReaction,hi,hj]
  simp [molecularIncrement,h]

end
end RAF1519.Refinement
