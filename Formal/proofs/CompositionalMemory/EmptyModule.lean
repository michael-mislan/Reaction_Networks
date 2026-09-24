import proofs.CompositionalMemory.SourceBirthGeometry

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

theorem source_birth_module_nonzero {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool) (n : WordBirthCount N (sourceWordCenter σ) σ) (i : Fin k) :
    n.val i ≠ (fun _ => 0) := by
  intro hz
  have h := source_word_readout N hN σ n i
  cases hs : σ i <;> simp [hs,hz,compositionalReadout] at h

theorem daughter_empty_weight (n : Counts) :
    daughterWeight n (fun _ => 0) = (1/2 : ℝ)^(∑ a, n a) := by
  unfold daughterWeight fairBinomialWeight
  simp only [Nat.choose_zero_right,Nat.cast_one,← one_div_pow]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem daughter_nonempty_mass (n : Counts) :
    (∑ d ∈ daughterDraws n, daughterWeight n d*(if d ≠ (fun _ => 0) then 1 else 0)) =
      1-(1/2 : ℝ)^(∑ a, n a) := by
  classical
  have hz : (fun _ => 0) ∈ daughterDraws n := by
    apply Fintype.mem_piFinset.mpr
    intro a
    simp
  have he : (∑ d ∈ daughterDraws n, daughterWeight n d*(if d = (fun _ => 0) then 1 else 0)) =
      daughterWeight n (fun _ => 0) := by simp [hz]
  have hsum : (∑ d ∈ daughterDraws n, daughterWeight n d*(if d ≠ (fun _ => 0) then 1 else 0)) +
      (∑ d ∈ daughterDraws n, daughterWeight n d*(if d = (fun _ => 0) then 1 else 0)) = 1 := by
    calc
      _ = ∑ d ∈ daughterDraws n, daughterWeight n d := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : d = (fun _ => 0) <;> simp [hd]
      _ = 1 := daughterWeight_sum n
  rw [he,daughter_empty_weight] at hsum
  linarith only [hsum]

theorem word_draw_regroup {k : ℕ} (n : Fin k → Counts) (g : (Fin k → Counts) → ℝ) :
    (∑ d ∈ wordDraws n, wordDrawWeight n d*g (drawModule d)) =
      ∑ d ∈ Fintype.piFinset (fun i => daughterDraws (n i)),
        (∏ i, daughterWeight (n i) (d i))*g d := by
  classical
  apply Finset.sum_bij (fun d _ => drawModule d)
  · intro d hd
    exact Fintype.mem_piFinset.mpr (draw_module_valid n d hd)
  · intro a _ b _ hab
    funext p
    exact congrFun (congrFun hab p.1) p.2
  · intro b hb
    refine ⟨(fun p => b p.1 p.2),?_,rfl⟩
    apply Fintype.mem_piFinset.mpr
    intro p
    exact Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hb p.1) p.2
  · intro d _
    congr 1
    simp only [wordDrawWeight,daughterWeight,drawModule,Fintype.prod_prod_type]

end CompositionalMemory
