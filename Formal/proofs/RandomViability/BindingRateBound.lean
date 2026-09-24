import proofs.RandomViability.BindingCountChannels

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

theorem bounded_pair_rate (a b V : ℝ) (hV : 0 < V)
    (hb : 0 ≤ b) (haV : a ≤ (5/2)*V) (hbV : b ≤ (5/2)*V) :
    a*b/V ≤ (25/4)*V := by
  apply (div_le_iff₀ hV).2
  have h := mul_le_mul haV hbV hb (by positivity : 0 ≤ (5/2)*V)
  nlinarith

theorem bounded_bimolecular_rate (a b V c : ℝ) (hV : 0 < V)
    (hb : 0 ≤ b) (haV : a ≤ (5/2)*V) (hbV : b ≤ (5/2)*V)
    (hc : 0 ≤ c) (hc22 : c ≤ 22) : c*a*b/V ≤ 150*V := by
  have h := mul_le_mul_of_nonneg_left (bounded_pair_rate a b V hV hb haV hbV) hc
  have hh := mul_le_mul_of_nonneg_right hc22 (show 0 ≤ (25/4)*V by positivity)
  have he : c*a*b/V = c*(a*b/V) := by ring
  rw [he]
  nlinarith

theorem channel_rate_bound (N : Counts) (V eps k r : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 0 ≤ r) (hr22 : r ≤ 22)
    (hN : ∀ i, (N i:ℝ) ≤ (5/2)*V) (j : Fin 18) :
    countRate N V eps k r j ≤ 150*V := by
  have hp (i l : Fin 6) (c : ℝ) (hc : 0 ≤ c) (hc22 : c ≤ 22) :
      c*(N i)*(N l)/V ≤ 150*V :=
    bounded_bimolecular_rate (N i) (N l) V c hV (by positivity)
      (hN i) (hN l) hc hc22
  have hu (i : Fin 6) (c : ℝ) (hc : 0 ≤ c) (hc22 : c ≤ 22) :
      c*(N i) ≤ 150*V := by
    have h := mul_le_mul_of_nonneg_left (hN i) hc
    have hh := mul_le_mul_of_nonneg_right hc22 (show 0 ≤ (5/2)*V by positivity)
    nlinarith
  have hek : 0 ≤ eps*k := mul_nonneg heps hk
  have hek1 : eps*k ≤ 22 := by
    have h := mul_le_mul heps1 hk1 hk (by norm_num : (0:ℝ) ≤ 1)
    nlinarith
  have h20k : 0 ≤ 20*k := by positivity
  have h20k22 : 20*k ≤ 22 := by linarith
  have hf : r*(N 2*(N 2-1):ℕ)/V ≤ 150*V := by
    have h := mul_le_mul_of_nonneg_left (factorial_le_square (N 2)) hr
    have hh := div_le_div_of_nonneg_right h hV.le
    calc
      _ ≤ r*(N 2:ℝ)^2/V := hh
      _ = r*(N 2)*(N 2)/V := by ring
      _ ≤ _ := hp 2 2 r hr hr22
  fin_cases j <;> norm_num [countRate]
  all_goals first
    | exact hp 0 1 eps heps (by linarith)
    | exact hu 2 (eps*k) hek hek1
    | exact hp 2 0 20 (by norm_num) (by norm_num)
    | exact hu 3 20 (by norm_num) (by norm_num)
    | exact hp 3 1 20 (by norm_num) (by norm_num)
    | exact hu 4 20 (by norm_num) (by norm_num)
    | exact hu 5 (20*k) h20k h20k22
    | exact hu 5 r hr hr22
    | simpa only [Nat.cast_mul] using hf
    | linarith [hN 0,hN 1,hN 2,hN 3,hN 4,hN 5]

theorem total_rate_bound (N : Counts) (V eps k r : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 0 ≤ r) (hr22 : r ≤ 22)
    (hN : ∀ i, (N i:ℝ) ≤ (5/2)*V) :
    (∑ j,countRate N V eps k r j) ≤ 3000*V := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 18))) =>
    channel_rate_bound N V eps k r hV heps heps1 hk hk1 hr hr22 hN j)
  norm_num at h
  linarith

end
end RandomViability.Binding
