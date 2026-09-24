import proofs.CompositionalMemory.MembraneMoments
import proofs.CompositionalMemory.ExchangeMoments
import Mathlib.Data.Fintype.BigOperators

namespace CompositionalMemory

abbrev IncidentChannel (k : ℕ) := Fin k ⊕ (Fin k ⊕ Fin k)

/-- Membrane, outgoing exchange, incoming exchange; both exchange clocks remain. -/
noncomputable def incidentRate {k : ℕ} (γ m : ℝ) (z w : Fin k → ℝ) (i : Fin k) :
    IncidentChannel k → ℝ :=
  Sum.elim (fun j => γ*(m/k)*z j)
    (Sum.elim (fun j => (m/k)*w j*z i) (fun j => (m/k)*w j*z j))

noncomputable def incidentSize {k : ℕ} (m : ℝ) (i : Fin k) : IncidentChannel k → ℝ :=
  Sum.elim (fun j => (70+if j=i then (k : ℝ) else 0)/(m+1))
    (Sum.elim (fun _ => 1/(m/k)) (fun _ => 1/(m/k)))

theorem incident_rate_nonnegative {k : ℕ} (γ m : ℝ) (z w : Fin k → ℝ) (i : Fin k)
    (hγ : 0 ≤ γ) (hm : 0 ≤ m) (hz : ∀ j, 0 ≤ z j) (hw : ∀ j, 0 ≤ w j)
    (c : IncidentChannel k) : 0 ≤ incidentRate γ m z w i c := by
  rcases c with j | j | j
  all_goals simp only [incidentRate,Sum.elim_inl,Sum.elim_inr]
  · exact mul_nonneg (mul_nonneg hγ (div_nonneg hm (Nat.cast_nonneg k))) (hz j)
  · exact mul_nonneg (mul_nonneg (div_nonneg hm (Nat.cast_nonneg k)) (hw j)) (hz i)
  · exact mul_nonneg (mul_nonneg (div_nonneg hm (Nat.cast_nonneg k)) (hw j)) (hz j)

theorem incident_first_moment {k : ℕ} (hk : 1 ≤ k) (γ m κ : ℝ)
    (z w : Fin k → ℝ) (i : Fin k)
    (hγ : 0 ≤ γ) (hm : 0 < m) (hz : ∀ j, z j ≤ 4)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j ≤ κ) :
    ∑ c, incidentRate γ m z w i c*incidentSize m i c ≤ 284*γ+8*κ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hmem := membrane_first_moment hk i z γ m 70 4 hγ hm (by norm_num) (by norm_num) hz
  have hex := exchange_first_moment w z (z i) 4 κ (m/k) hw hz (hz i) (by norm_num) hs
    (div_pos hm hkpos)
  simp only [Fintype.sum_sum_type,incidentRate,incidentSize,Sum.elim_inl,Sum.elim_inr]
  nlinarith only [hmem,hex]

theorem incident_second_moment {k : ℕ} (hk : 1 ≤ k) (γ m κ N : ℝ)
    (z w : Fin k → ℝ) (i : Fin k)
    (hγ : 0 ≤ γ) (hκ : 0 ≤ κ) (hN : 0 < N) (hm : (k : ℝ)*N ≤ m)
    (hz : ∀ j, z j ≤ 4) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j ≤ κ) :
    ∑ c, incidentRate γ m z w i c*(incidentSize m i c)^2 ≤ (20164*γ+8*κ)/N := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hv : N ≤ m/k := (le_div_iff₀ hkpos).mpr (by nlinarith only [hm])
  have hmem := membrane_moment_uniform hk i z γ m N 70 4 hγ hN hm (by norm_num) (by norm_num) hz
  have hex := exchange_second_moment w z (z i) 4 κ N (m/k) hw hz (hz i) (by norm_num) hκ hs hN hv
  simp only [add_mul,Finset.sum_add_distrib] at hex
  simp only [Fintype.sum_sum_type,incidentRate,incidentSize,Sum.elim_inl,Sum.elim_inr]
  simp only [div_eq_mul_inv] at hmem hex ⊢
  nlinarith only [hmem,hex]

theorem incident_size_bounds {k : ℕ} (hk : 1 ≤ k) (m N : ℝ) (i : Fin k)
    (hN : 0 < N) (hm : (k : ℝ)*N ≤ m) (c : IncidentChannel k) :
    0 ≤ incidentSize m i c ∧ incidentSize m i c ≤ 71/N := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hmpos : 0 < m := lt_of_lt_of_le (mul_pos hkpos hN) hm
  have hv : N ≤ m/k := (le_div_iff₀ hkpos).mpr (by nlinarith only [hm])
  have he : 1/(m/k) ≤ 71/N := by
    calc
      _ ≤ 1/N := div_le_div_of_nonneg_left (by norm_num) hN hv
      _ ≤ 71/N := div_le_div_of_nonneg_right (by norm_num) hN.le
  rcases c with j | j | j
  · simp only [incidentSize,Sum.elim_inl]
    constructor
    · positivity
    · simpa only [show (70 : ℝ)+1=71 by norm_num] using
        membrane_jump_size hk i j m N 70 hN hm (by norm_num)
  all_goals simp only [incidentSize,Sum.elim_inl,Sum.elim_inr]
  all_goals exact ⟨by positivity,he⟩

end CompositionalMemory
