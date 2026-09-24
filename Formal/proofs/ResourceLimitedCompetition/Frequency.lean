import proofs.ResourceLimitedCompetition.Main
namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

theorem odds_implies_frequency (r h l H L : ℝ) (hr : 0 < r)
    (hh : 0 < h) (hl : 0 < l) (hH : 0 < H) (hL : 0 < L)
    (ho : r*h/l ≤ H/L) : r*h/(l+r*h) ≤ H/(H+L) := by
  have hp := (div_le_div_iff₀ hl hL).mp ho
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hp]

theorem frequency_logistic_identity (r h l : ℝ) (hr : 0 < r) (hh : 0 < h) (hl : 0 < l) :
    r*h/(l+r*h) = r*(h/(h+l))/(1-h/(h+l)+r*(h/(h+l))) := by
  have hd : l+r*h ≠ 0 := ne_of_gt (by positivity)
  have hs : h+l ≠ 0 := ne_of_gt (by positivity)
  field_simp [hd,hs]
  ring

theorem frequency_gain_identity (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp1 : p < 1) :
    r*p/(1-p+r*p)-p=p*(1-p)*(r-1)/(1+p*(r-1)) := by
  have hd : 0 < 1-p+r*p := by positivity
  have he : 1+p*(r-1)=1-p+r*p := by ring
  rw [he]
  field_simp
  ring

theorem two_founder_integer_frequency (H L : ℕ) (hH : L < H) (hbudget : H+L ≤ 8) :
    (4/7 : ℝ) ≤ (H : ℝ)/(H+L : ℕ) := by
  have hL : L ≤ 3 := by omega
  have hlin : 4*(H+L) ≤ 7*H := by omega
  have hsum : 0 < (H+L : ℕ) := by omega
  apply (le_div_iff₀ (by exact_mod_cast hsum)).mpr
  have hR : (4 : ℝ)*((H+L : ℕ) : ℝ) ≤ 7*(H : ℝ) := by exact_mod_cast hlin
  linarith only [hR]

theorem success_two_founder_frequency (N : ℕ) (hN : 0 < N) (zL zH : ℝ)
    (x : StoppedPopulation (activeDomain N (1+1) zL zH))
    (hx : x ∈ competitionSuccessSet N 1 1 zL zH) :
    ∃ e, x=.inr e ∧ (4/7 : ℝ) ≤
      (ancestralCount true (eventOutcome N e).live : ℝ)/
        (ancestralCount true (eventOutcome N e).live+ancestralCount false (eventOutcome N e).live : ℕ) := by
  obtain ⟨e,rfl,hn,_,_,hH,hL,ho⟩ := hx
  refine ⟨e,rfl,?_⟩
  have hs := activeDomain_safe N (1+1) zL zH e.1.val e.1.property
  have hv := event_valid_volumes N hN _ e.1 e.2 hs.2.2.2.2.1
  have hB := (ancestral_count_bounds N true (eventOutcome N e).live
    (fun c hc => ⟨(hv c hc).1,(hv c hc).2.le⟩)).1
  have hC := (ancestral_count_bounds N false (eventOutcome N e).live
    (fun c hc => ⟨(hv c hc).1,(hv c hc).2.le⟩)).1
  have hW := nutrient_endpoint_membrane N (1+1) zL zH e.1 e.2 hn
  rw [← ancestral_membrane_total] at hW
  have hb : ancestralCount true (eventOutcome N e).live+ancestralCount false (eventOutcome N e).live ≤ 8 := by
    have ht : N*(ancestralCount true (eventOutcome N e).live+ancestralCount false (eventOutcome N e).live) ≤ N*8 := by
      rw [Nat.mul_add]
      nlinarith only [hB,hC,hW]
    exact le_of_mul_le_mul_left ht hN
  have he : (1 : ℝ) < Real.exp (1/10) := Real.one_lt_exp_iff.mpr (by norm_num)
  norm_num only [Nat.cast_one,mul_one,div_one] at ho
  have ht : (ancestralCount false (eventOutcome N e).live : ℝ) <
      (ancestralCount true (eventOutcome N e).live : ℝ) := by
    have h := (lt_div_iff₀ (by exact_mod_cast hL)).mp (he.trans_le ho)
    simpa only [one_mul] using h
  exact two_founder_integer_frequency _ _ (by exact_mod_cast ht) hb

end ResourceLimitedCompetition
