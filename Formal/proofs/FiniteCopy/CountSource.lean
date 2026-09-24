import proofs.FiniteCopy.Source

namespace FiniteCopy

def intJump : Fin 13 → Fin 4 → ℤ :=
  ![![-1,1,1,0], ![1,-1,-1,0], ![0,0,-1,1], ![0,0,1,-1],
    ![0,0,2,-1], ![0,0,-2,1], ![1,0,0,0], ![-1,0,0,0],
    ![0,1,0,0], ![0,-1,0,0], ![2,-1,0,0], ![-2,1,0,0], ![0,0,0,-1]]

def reactants (n : Counts) : Fin 13 → Prop :=
  ![1 ≤ n 0, 1 ≤ n 1 ∧ 1 ≤ n 2, 1 ≤ n 2, 1 ≤ n 3, 1 ≤ n 3,
    2 ≤ n 2, True, 1 ≤ n 0, True, 1 ≤ n 1, 1 ≤ n 1, 2 ≤ n 0, 1 ≤ n 3]

def nextCounts (n : Counts) (r : Fin 13) : Counts :=
  fun i => Int.toNat ((n i : ℤ)+intJump r i)

theorem intJump_cast (r : Fin 13) (i : Fin 4) : (intJump r i : ℝ) = jump r i := by
  fin_cases r <;> fin_cases i <;> norm_num [intJump, jump]

theorem enabled_jump_nonneg (n : Counts) (r : Fin 13) (h : reactants n r) (i : Fin 4) :
    0 ≤ (n i : ℤ)+intJump r i := by
  fin_cases r <;> fin_cases i <;> norm_num [reactants, intJump] at h ⊢
  all_goals first | omega | exact_mod_cast h | exact_mod_cast h.1 | exact_mod_cast h.2

theorem nextCounts_cast (n : Counts) (r : Fin 13) (h : reactants n r) (i : Fin 4) :
    (nextCounts n r i : ℝ) = (n i : ℝ)+jump r i := by
  have he := Int.toNat_of_nonneg (enabled_jump_nonneg n r h i)
  have he' : (nextCounts n r i : ℤ) = (n i : ℤ)+intJump r i := he
  have heR : (nextCounts n r i : ℝ) = (n i : ℝ)+(intJump r i : ℝ) := by exact_mod_cast he'
  simpa only [intJump_cast] using heR

theorem disabled_density_zero (e : ℝ) (N : ℕ) (n : Counts) (r : Fin 13)
    (h : ¬reactants n r) : densityRates e (1/(N : ℝ)) (concentration N n) r = 0 := by
  fin_cases r <;> norm_num [reactants] at h
  · have hn : n 0=0 := by omega
    simp [densityRates, concentration, hn]
  · have hn : n 1=0 ∨ n 2=0 := by omega
    rcases hn with hn | hn <;> simp [densityRates, concentration, hn]
  · have hn : n 2=0 := by omega
    simp [densityRates, concentration, hn]
  · have hn : n 3=0 := by omega
    simp [densityRates, concentration, hn]
  · have hn : n 3=0 := by omega
    simp [densityRates, concentration, hn]
  · have hn : n 2=0 ∨ n 2=1 := by omega
    rcases hn with hn | hn <;> simp [densityRates, concentration, hn]
  · have hn : n 0=0 := by omega
    simp [densityRates, concentration, hn]
  · have hn : n 1=0 := by omega
    simp [densityRates, concentration, hn]
  · have hn : n 1=0 := by omega
    simp [densityRates, concentration, hn]
  · have hn : n 0=0 ∨ n 0=1 := by omega
    rcases hn with hn | hn <;> simp [densityRates, concentration, hn]
  · have hn : n 3=0 := by omega
    simp [densityRates, concentration, hn]

theorem concentration_next (N : ℕ) (n : Counts) (r : Fin 13) (h : reactants n r) :
    concentration N (nextCounts n r) =
      fun i => concentration N n i+jump r i/(N : ℝ) := by
  funext i
  dsimp [concentration]
  rw [nextCounts_cast n r h]
  ring

end FiniteCopy
