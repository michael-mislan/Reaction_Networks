import proofs.SerialTransferSelection.ChemicalEnvelope
import proofs.SerialTransferSelection.ShareParameters
import proofs.SerialTransferSelection.MinorityBoundary

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem history_geometric_closed (r : ℝ) (hr : r ≠ 1) (k j : ℕ) :
    historyBudget (fun i => r^i) k j = r^j*(r^k-1)/(r-1) := by
  induction k generalizing j with
  | zero => simp [historyBudget]
  | succ k ih =>
    rw [historyBudget,ih]
    simp only [pow_succ]
    field_simp
    ring

theorem share_transfer_closed (M K : ℕ) :
    80000/(M : ℝ)*historyBudget (fun j => (204/49 : ℝ)^j) K 0 =
      80000/(M : ℝ)*((204/49 : ℝ)^K-1)/(204/49-1) := by
  rw [history_geometric_closed _ (by norm_num)]
  simp only [pow_zero,one_mul]
  ring

theorem transfer_population_iff (M K : ℕ) (hM : 0 < M) (δ : ℝ) (hδ : 0 < δ) :
    80000/(M : ℝ)*historyBudget (fun j => (204/49 : ℝ)^j) K 0 ≤ δ ↔
    80000/(δ*(204/49-1))*((204/49 : ℝ)^K-1) ≤ (M : ℝ) := by
  rw [share_transfer_closed]
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hd : (0 : ℝ) < δ*(204/49-1) := by positivity
  have hden : (0 : ℝ) < (M : ℝ)*(204/49-1) := by positivity
  have heq : 80000/(M : ℝ)*((204/49 : ℝ)^K-1)/(204/49-1) =
      80000*((204/49 : ℝ)^K-1)/((M : ℝ)*(204/49-1)) := by ring
  rw [heq,div_mul_eq_mul_div,div_le_iff₀ hden,div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem transfer_inverse_horizon (M K : ℕ) (hM : 0 < M) (δ : ℝ) (hδ : 0 < δ) :
    80000/(M : ℝ)*historyBudget (fun j => (204/49 : ℝ)^j) K 0 ≤ δ ↔
    (K : ℝ) ≤ Real.log (1+δ*(204/49-1)*(M : ℝ)/80000)/Real.log (204/49) := by
  rw [transfer_population_iff M K hM δ hδ]
  have hr : (0 : ℝ) < Real.log (204/49) := Real.log_pos (by norm_num)
  have hp : (0 : ℝ) < (204/49 : ℝ)^K := by positivity
  have hb : (0 : ℝ) < 1+δ*(204/49-1)*(M : ℝ)/80000 := by positivity
  rw [le_div_iff₀ hr,← Real.log_pow,Real.log_le_log_iff hp hb]
  have hd : 0 < δ*(204/49-1) := by positivity
  constructor <;> intro h
  · have hh := (div_le_iff₀ hd).mp (show 80000*((204/49 : ℝ)^K-1)/(δ*(204/49-1)) ≤ (M : ℝ) by convert h using 1; ring)
    nlinarith
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith

theorem absorbed_chemical_envelope (N M : ℕ) (hM : 1 ≤ M) (t : ℝ) (ht : 0 ≤ t) :
    chemicalCycleError N M t ≤
      (142+4*t/21)*(M : ℝ)*Real.exp (-((N : ℝ)*localAlpha*innerEnergy)/4) := by
  let u := (N : ℝ)*localAlpha*innerEnergy
  have hu : 0 ≤ u := by dsimp [u,localAlpha,innerEnergy,outerEnergy]; positivity
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have he := Real.add_one_le_exp (u/4)
  have hep : 0 < Real.exp (-u/4) := Real.exp_pos _
  have hid : Real.exp (u/4)*Real.exp (-u/4)=1 := by
    rw [← Real.exp_add,show u/4 + -u/4=0 by ring,Real.exp_zero]
  have huv : u*Real.exp (-u/4) ≤ 4 := by nlinarith
  have he1 : Real.exp (-u/4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsplit : Real.exp (-u/2)=Real.exp (-u/4)*Real.exp (-u/4) := by rw [← Real.exp_add]; congr 1; ring
  have hc := chemicalCycleError_envelope N M t ht
  change chemicalCycleError N M t ≤ ((M : ℝ)*(76+16*u+t*u/21)+2)*Real.exp (-u/2) at hc
  apply hc.trans
  rw [hsplit]
  have hsmall : ((M : ℝ)*(76+16*u+t*u/21)+2)*Real.exp (-u/4) ≤ (142+4*t/21)*(M : ℝ) := by
    have ha := mul_le_mul_of_nonneg_left he1 (show 0 ≤ 76*(M : ℝ)+2 by positivity)
    have hb := mul_le_mul_of_nonneg_left huv (show 0 ≤ (16+t/21)*(M : ℝ) by positivity)
    nlinarith
  convert mul_le_mul_of_nonneg_right hsmall hep.le using 1; dsimp [u]; ring

theorem chemical_sizing (N M K : ℕ) (hM : 1 ≤ M) (hK : 0 < K)
    (t δ : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ)
    (hsize : 4*Real.log ((142+4*t/21)*(M : ℝ)*(K : ℝ)/δ) ≤
      (N : ℝ)*localAlpha*innerEnergy) :
    (K : ℝ)*chemicalCycleError N M t ≤ δ := by
  have hc := absorbed_chemical_envelope N M hM t ht
  have hp : 0 < (142+4*t/21)*(M : ℝ)*(K : ℝ)/δ := by positivity
  have he := Real.exp_le_exp.mpr (show -((N : ℝ)*localAlpha*innerEnergy)/4 ≤
      -Real.log ((142+4*t/21)*(M : ℝ)*(K : ℝ)/δ) by linarith)
  rw [Real.exp_neg,Real.exp_log hp] at he
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ (142+4*t/21)*(M : ℝ)*(K : ℝ) by positivity)
  have hz : (142+4*t/21)*(M : ℝ)*(K : ℝ)*((142+4*t/21)*(M : ℝ)*(K : ℝ)/δ)⁻¹=δ := by field_simp
  rw [hz] at hh
  have hk := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg K)
  nlinarith

theorem necessary_inverse_horizon (H L M K : ℕ) (g : ℝ) (hg : 0 < g)
    (hH : 0 < H) (hL : 0 < L) (hs : H+L=M)
    (hgain : (K : ℝ)*g-Real.log 2 < Real.log (H : ℝ)-Real.log (L : ℝ)) :
    (K : ℝ) < Real.log (2*((M : ℝ)-1))/g :=
  (lt_div_iff₀ hg).mpr (finite_population_horizon H L M K g hH hL hs hgain)

end SerialTransferSelection
