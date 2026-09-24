import proofs.G6PDReserve.CapacityDynamics

namespace G6PDReserve.Population
noncomputable section
open Set
open scoped BigOperators

structure Pop (ι : Type*) [Fintype ι] where
  w : ι → ℝ
  V : ι → ℝ
  nonneg : ∀ i, 0 ≤ w i
  mass : ∑ i, w i = 1
  support : ∀ i, Admitted (V i)
  mean : ∑ i, w i * V i = 1

def flag (V : ℝ) : ℝ := if 1 ≤ V then 1 else 0
def fraction {ι : Type*} [Fintype ι] (P : Pop ι) : ℝ := ∑ i, P.w i * flag (P.V i)
def actualFraction {ι : Type*} [Fintype ι] (P : Pop ι) (g : ι → ℝ → ℝ) : ℝ := by
  classical
  exact ∑ i, P.w i * (if Hits (g i) then 1 else 0)

theorem actual_eq {ι : Type*} [Fintype ι] (P : Pop ι) (g : ι → ℝ → ℝ)
    (hg : ∀ i, Solution (P.V i) (g i)) : actualFraction P g = fraction P := by
  classical
  unfold actualFraction fraction flag
  congr 1
  funext i
  rw [hits_iff (P.support i) (hg i)]

theorem fraction_bounds {ι : Type*} [Fintype ι] (P : Pop ι) :
    20/41 ≤ fraction P ∧ fraction P ≤ 1 := by
  have hpoint (i : ι) : P.V i ≤ 9/14 + (41/56)*flag (P.V i) := by
    rcases P.support i with h | h
    · have hn : ¬ 1 ≤ P.V i := by linarith [h.2]
      simp only [flag, if_neg hn]; linarith [h.2]
    · simp only [flag, if_pos h.1]; linarith [h.2]
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hpoint i) (P.nonneg i))
  have he : (∑ i, P.w i * (9/14+(41/56)*flag (P.V i))) =
      (9/14)*(∑ i, P.w i)+(41/56)*fraction P := by
    simp only [fraction, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [P.mean, he, P.mass] at hb
  have hu : fraction P ≤ ∑ i, P.w i := by
    apply Finset.sum_le_sum
    intro i _
    have hi : flag (P.V i) ≤ 1 := by unfold flag; split <;> norm_num
    simpa using mul_le_mul_of_nonneg_left hi (P.nonneg i)
  rw [P.mass] at hu
  exact ⟨by linarith,hu⟩

theorem bulk_surface {ι : Type*} [Fintype ι] (P : Pop ι)
    (N S H A B : ℝ) :
    (∑ i, P.w i * shimoRate (P.V i) 3 7 56 125 520 N S H A B) =
      shimoRate 1 3 7 56 125 520 N S H A B := by
  have he (V : ℝ) : shimoRate V 3 7 56 125 520 N S H A B =
      V * shimoRate 1 3 7 56 125 520 N S H A B := by unfold shimoRate; ring
  calc
    _ = ∑ i, (P.w i * P.V i) * shimoRate 1 3 7 56 125 520 N S H A B := by
      apply Finset.sum_congr rfl
      intro i _
      rw [he (P.V i)]
      ring
    _ = _ := by rw [← Finset.sum_mul, P.mean, one_mul]

def witnessV : Fin 3 → ℝ := ![9/14,11/8,1]
def witnessW (p : ℝ) : Fin 3 → ℝ := ![1-p,(20/21)*(1-p),(41*p-20)/21]

theorem witness_support (i : Fin 3) : Admitted (witnessV i) := by
  fin_cases i <;> norm_num [witnessV, Admitted]

def witness (p : ℝ) (hl : 20/41 ≤ p) (hu : p ≤ 1) : Pop (Fin 3) where
  w := witnessW p
  V := witnessV
  nonneg := by
    intro i; fin_cases i <;> simp [witnessW] <;> linarith
  mass := by simp [witnessW, Fin.sum_univ_succ]; ring
  support := witness_support
  mean := by simp [witnessV, witnessW, Fin.sum_univ_succ]; ring

theorem witness_fraction (p : ℝ) (hl : 20/41 ≤ p) (hu : p ≤ 1) :
    fraction (witness p hl hu) = p := by
  norm_num [fraction, witness, witnessW, witnessV, flag, Fin.sum_univ_succ]
  ring

theorem all_solutions {ι : Type*} [Fintype ι] (P : Pop ι) :
    ∃ g : ι → ℝ → ℝ, ∀ i, Solution (P.V i) (g i) := by
  have h (i : ι) := solution_exists (P.V i) (admitted_lower (P.support i))
  choose g hg using h
  exact ⟨g,hg⟩

end
end G6PDReserve.Population
