import proofs.SpecimenReliability.GateTradeoff

namespace SpecimenReliability
noncomputable section
open scoped BigOperators

theorem gate_interior_formula (m : ℕ) (H : ℝ) (hH : H < 1)
    (hb : (m+1:ℝ)*H < 1) :
    gateBound m H = (m:ℝ)^m / ((m+1:ℝ)^(m+1)*(1-H)^m) := by
  have hc : 1-H ≠ 0 := by linarith
  have hm : (m+1:ℝ) ≠ 0 := by positivity
  have hi : 1-((m:ℝ)/((m+1:ℝ)*(1-H)))*(1-H) = 1/(m+1:ℝ) := by
    field_simp
    ring
  unfold gateBound gateOpt
  rw [if_neg (not_le.mpr hb)]
  unfold gateCurve
  rw [hi]
  simp only [div_pow,mul_pow,pow_succ]
  field_simp

def singleReference (p : ℝ) : Fin 2 → ℝ := ![1-p,p]

def singleCalibratedRisk {S : Type*} [Fintype S] (μ x : S → ℝ)
    (s : ℝ) (n m : ℕ) : ℝ :=
  ∑ h : Fin m → Fin 2,
    (∏ i, if h i = 1 then singleReference (mean μ x) (h i) else 0) *
      sourceRisk μ x (fun _ => 0) s 0 n

theorem single_reference_law {S : Type*} [Fintype S] (μ x : S → ℝ)
    (hs : ∑ s, μ s = 1) (j : Fin 2) :
    (∑ s, μ s*singleReference (x s) j) = singleReference (mean μ x) j := by
  fin_cases j <;> simp [singleReference,mean,mul_sub,Finset.sum_sub_distrib,hs]

theorem single_identity {S : Type*} [Fintype S] (μ x : S → ℝ)
    (s : ℝ) (n m : ℕ) :
    singleCalibratedRisk μ x s n m = (mean μ x)^m * sourceRisk μ x (fun _ => 0) s 0 n := by
  unfold singleCalibratedRisk
  rw [← Finset.sum_mul,
    ← Fintype.sum_pow (fun j => if j=1 then singleReference (mean μ x) j else 0) m]
  simp [singleReference]

theorem mean_interval {S : Type*} [Fintype S] (μ x : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hs : ∑ s, μ s = 1)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) : 0 ≤ mean μ x ∧ mean μ x ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (hx s).1)
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
      mul_le_mul_of_nonneg_left (hx s).2 (hμ s))
    simpa only [mul_one, hs,mean] using h

theorem single_general {S : Type*} [Fintype S] (μ x : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hs : ∑ s, μ s = 1)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (k n m : ℕ) (hkn : k ≤ n) (hm : 1 ≤ m) :
    singleCalibratedRisk μ x s n m ≤ gateBound m ((1-s)^k) := by
  have hzero : ∀ i : S, 0 ≤ (0:ℝ) ∧ (0:ℝ) ≤ 1 := by intro i; norm_num
  have hr := (risk_count_mono μ x (fun _ => 0) hμ hx hzero s 0 hs0 (by norm_num)
    (by linarith) k n hkn).trans
    (sharp_upper μ x (fun _ => 0) hμ hs hx hzero s 0 k hs0 (by norm_num) (by linarith))
  have he : envelope (mean μ x) (mean μ (fun _ => 0))
      (mean μ (fun i => x i*0)) s 0 k = 1-(mean μ x)*(1-(1-s)^k) := by
    simp [mean,envelope]
    ring
  rw [he] at hr
  have hp := mean_interval μ x hμ hs hx
  have hH : 0 ≤ (1-s)^k ∧ (1-s)^k ≤ 1 :=
    ⟨pow_nonneg (by linarith) k, pow_le_one₀ (by linarith) (by linarith)⟩
  rw [single_identity]
  exact (mul_le_mul_of_nonneg_left hr (pow_nonneg hp.1 m)).trans
    (gate_maximum m hm _ _ hH hp)

theorem single_attainment (z s : ℝ) (k m : ℕ) :
    singleCalibratedRisk (corners z 0 0) cornerX s k m = gateCurve m ((1-s)^k) z := by
  rw [single_identity]
  have hp := (corners_moments z 0 0).1
  change mean (corners z 0 0) cornerX = z at hp
  rw [hp,source_law]
  simp [corners,cornerX,Fin.sum_univ_succ,gateCurve]
  ring
  simp

theorem single_witness_valid (z : ℝ) (hz : 0 ≤ z ∧ z ≤ 1) :
    (∀ i, 0 ≤ corners z 0 0 i) ∧ ∑ i, corners z 0 0 i = 1 := by
  exact ⟨corners_nonneg _ _ _ (by norm_num) (by norm_num) hz.1 (by linarith),
    corners_normalized _ _ _⟩

theorem worked_bounds :
    gateBound 3 ((1-(9/20:ℝ))^2) = 121/400 ∧
    gateBound 3 ((1-(19/20:ℝ))^2) = 250000/2352637 ∧
    gateBound 9 ((1-(9/20:ℝ))^6) ≤ 1/20 ∧
    1/20 < gateBound 8 ((1-(9/20:ℝ))^6) := by
  norm_num [gateBound,gateOpt,gateCurve]

end
end SpecimenReliability

