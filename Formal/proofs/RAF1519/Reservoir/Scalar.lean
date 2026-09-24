import Mathlib

namespace RAF1519.Reservoir
noncomputable section
open Set

def uptake (s : ℝ) := s*(1/2+s)
def reservoir (s : ℝ) := 1-20*uptake s
def resource (s : ℝ) := (1/2+s)/reservoir s
def substrate (s : ℝ) := 60/(resource s+2)
def catalyst (s : ℝ) := (16*resource s+2*(resource s)^2)/(20001/10000)
def precursor (s : ℝ) := substrate s*resource s+16*resource s+
  4*(resource s)^2-3*catalyst s+uptake s
def residual (s : ℝ) := precursor s+substrate s+
  (1/100000)*((precursor s)^2-substrate s)-33
def state (s : ℝ) : Fin 6 → ℝ :=
  ![precursor s,substrate s,resource s,catalyst s,reservoir s,s]
def field (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![6-2*x 0+x 1*x 2+2*(1/100000)*(x 1-(x 0)^2),
    27+x 0-(x 2+1)*x 1-(1/100000)*(x 1-(x 0)^2),
    x 0-x 1*x 2-16*x 2+3*x 3-4*(x 2)^2-x 4*x 2*x 5,
    16*x 2+2*(x 2)^2-(20001/10000)*x 3,
    (1/20)*(1-x 4)-x 4*x 2*x 5,
    x 5*(x 4*x 2-1/2-x 5)]

theorem reservoir_positive (s : ℝ) (hs : s ∈ Icc (0:ℝ) (3/40)) :
    0 < reservoir s := by
  dsimp [reservoir,uptake]
  nlinarith [hs.1,hs.2,mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]

theorem resource_bounds (s : ℝ) (hs : s ∈ Icc (0:ℝ) (3/40)) :
    0 < resource s ∧ resource s ≤ 5 := by
  have hr := reservoir_positive s hs
  constructor
  · exact div_pos (by linarith [hs.1]) hr
  · apply (div_le_iff₀ hr).2
    dsimp [reservoir,uptake]
    nlinarith [hs.1,hs.2,mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]

theorem substrate_bound (s : ℝ) (hs : s ∈ Icc (0:ℝ) (3/40)) :
    8 < substrate s := by
  have hz := resource_bounds s hs
  apply (lt_div_iff₀ (by linarith : 0 < resource s+2)).2
  linarith

theorem residual_continuous : ContinuousOn residual (Icc (0:ℝ) (3/40)) := by
  intro s hs
  have hr : reservoir s ≠ 0 := ne_of_gt (reservoir_positive s hs)
  have hz : resource s+2 ≠ 0 := by have := (resource_bounds s hs).1; linarith
  have hR : ContinuousAt reservoir s := by unfold reservoir uptake; fun_prop
  have hZ : ContinuousAt resource s := by
    unfold resource
    exact (continuousAt_const.add continuousAt_id).div hR hr
  have hB : ContinuousAt substrate s := by
    unfold substrate
    exact continuousAt_const.div (hZ.add continuousAt_const) hz
  have hH : ContinuousAt catalyst s := by unfold catalyst; fun_prop
  have hA : ContinuousAt precursor s := by unfold precursor uptake; fun_prop
  exact (by unfold residual; fun_prop : ContinuousAt residual s).continuousWithinAt

theorem state_positive (s : ℝ) (hs : s ∈ Icc (0:ℝ) (3/40)) (hs' : 0 < s) :
    ∀ i, 0 < state s i := by
  have hz := (resource_bounds s hs).1
  have hb := substrate_bound s hs
  have hh : 0 < catalyst s := by unfold catalyst; positivity
  have hH : catalyst s ≤ 8*resource s+(resource s)^2 := by
    unfold catalyst
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 20001/10000)).2
    nlinarith [sq_nonneg (resource s)]
  have hJ : 0 ≤ uptake s := by unfold uptake; positivity
  have hA : 0 < precursor s := by
    unfold precursor
    nlinarith [mul_pos (sub_pos.mpr hb) hz, sq_nonneg (resource s)]
  intro i
  fin_cases i
  · exact hA
  · exact lt_trans (by norm_num) hb
  · exact hz
  · exact hh
  · exact reservoir_positive s hs
  · exact hs'

theorem stationary (s : ℝ) (hs : s ∈ Icc (0:ℝ) (3/40)) (hf : residual s = 0) :
    field (state s) = 0 := by
  have hr : reservoir s ≠ 0 := ne_of_gt (reservoir_positive s hs)
  have hR : reservoir s*resource s = 1/2+s := by
    unfold resource
    field_simp
  have hB : substrate s*(resource s+2) = 60 := by
    have hz : resource s+2 ≠ 0 := by have := (resource_bounds s hs).1; linarith
    unfold substrate
    field_simp
  have hH : (20001/10000:ℝ)*catalyst s = 16*resource s+2*(resource s)^2 := by
    unfold catalyst
    ring
  have hA : precursor s = substrate s*resource s+16*resource s+
      4*(resource s)^2-3*catalyst s+uptake s := rfl
  have hJ : uptake s = s*(1/2+s) := rfl
  have hreservoir : reservoir s = 1-20*uptake s := rfl
  have hRS := congrArg (fun a : ℝ => a*s) hR
  unfold residual at hf
  funext i
  fin_cases i
  · change 6-2*precursor s+substrate s*resource s+
      2*(1/100000)*(substrate s-(precursor s)^2) = 0
    nlinarith
  · change 27+precursor s-(resource s+1)*substrate s-
      (1/100000)*(substrate s-(precursor s)^2) = 0
    nlinarith
  · change precursor s-substrate s*resource s-16*resource s+3*catalyst s-
      4*(resource s)^2-reservoir s*resource s*s = 0
    nlinarith [hRS]
  · change 16*resource s+2*(resource s)^2-(20001/10000)*catalyst s = 0
    linarith
  · change (1/20)*(1-reservoir s)-reservoir s*resource s*s = 0
    nlinarith [hRS]
  · change s*(reservoir s*resource s-1/2-s) = 0
    rw [hR]
    ring

theorem low_signs : residual (4067409/100000000) < 0 ∧
    0 < residual (1016853/25000000) := by
  norm_num [residual,precursor,substrate,resource,reservoir,catalyst,uptake]

theorem high_signs : residual (701493/10000000) < 0 ∧
    0 < residual (7014933/100000000) := by
  norm_num [residual,precursor,substrate,resource,reservoir,catalyst,uptake]

theorem two_positive_stationary_states :
    ∃ a b : ℝ, a ∈ Icc (4067409/100000000:ℝ) (1016853/25000000) ∧
      b ∈ Icc (701493/10000000:ℝ) (7014933/100000000) ∧
      a < b ∧ (∀ i, 0 < state a i) ∧ (∀ i, 0 < state b i) ∧
      field (state a) = 0 ∧ field (state b) = 0 := by
  have hl : Icc (4067409/100000000:ℝ) (1016853/25000000) ⊆ Icc 0 (3/40) := by
    intro s hs; constructor <;> linarith [hs.1,hs.2]
  have hh : Icc (701493/10000000:ℝ) (7014933/100000000) ⊆ Icc 0 (3/40) := by
    intro s hs; constructor <;> linarith [hs.1,hs.2]
  obtain ⟨a,ha,hfa⟩ := intermediate_value_Icc
    (by norm_num : (4067409/100000000:ℝ) ≤ 1016853/25000000)
    (residual_continuous.mono hl) ⟨low_signs.1.le,low_signs.2.le⟩
  obtain ⟨b,hb,hfb⟩ := intermediate_value_Icc
    (by norm_num : (701493/10000000:ℝ) ≤ 7014933/100000000)
    (residual_continuous.mono hh) ⟨high_signs.1.le,high_signs.2.le⟩
  exact ⟨a,b,ha,hb,by linarith [ha.2,hb.1],
    state_positive a (hl ha) (by linarith [ha.1]),
    state_positive b (hh hb) (by linarith [hb.1]),
    stationary a (hl ha) hfa,stationary b (hh hb) hfb⟩

end
end RAF1519.Reservoir
