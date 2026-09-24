import proofs.FiniteReservoir.Sizing

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery FiniteCopyReactor MeasureTheory ProbabilityTheory RandomViability.Binding
open scoped ENNReal

def designVolume (m : ℕ) (δ QI QX : ℝ) : ℕ :=
  max (logarithmicVolume m δ) (max ⌈56*QI/(m:ℝ)⌉₊ ⌈1080*QX/(m:ℝ)⌉₊)

theorem confidence_budget (V m : ℕ) (hm : 0 < m) (δ : ℝ) (hd : 0 < δ)
    (hscale : 200000000000 ≤ V) (hlog : 10000000000*Real.log (101*(m:ℝ)/δ) ≤ V) :
    (m:ℝ)*oneCycleError V ≤ δ := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have he : 101*(m:ℝ)/δ ≤ Real.exp ((V:ℝ)/10000000000) := by
    rw [← Real.exp_log (by positivity : 0 < 101*(m:ℝ)/δ)]
    exact Real.exp_le_exp.mpr (by linarith)
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_pos (-((V:ℝ)/10000000000))).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at he'
  have hh := mul_le_mul_of_nonneg_right he' hd.le
  have hid : (101*(m:ℝ)/δ*Real.exp (-((V:ℝ)/10000000000)))*δ=
      101*(m:ℝ)*Real.exp (-((V:ℝ)/10000000000)) := by field_simp
  rw [hid] at hh
  have hb := mul_le_mul_of_nonneg_left (one_cycle_single_exponential V (by exact_mod_cast hscale)) hm'.le
  norm_num only [neg_div] at hb
  nlinarith only [hb,hh]

theorem design_volume_scale (m : ℕ) (δ QI QX : ℝ) : 200000000000 ≤ designVolume m δ QI QX :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem design_volume_budget (m : ℕ) (hm : 0 < m) (δ QI QX : ℝ) (hd : 0 < δ) :
    (m:ℝ)*oneCycleError (designVolume m δ QI QX) ≤ δ := by
  apply confidence_budget _ m hm δ hd (design_volume_scale m δ QI QX)
  have hc : ⌈10000000000*Real.log (101*(m:ℝ)/δ)⌉₊ ≤ designVolume m δ QI QX :=
    (le_max_right _ _).trans (le_max_left _ _)
  exact (Nat.le_ceil _).trans (by exact_mod_cast hc)

theorem design_volume_outputs (m : ℕ) (hm : 0 < m) (δ QI QX : ℝ) :
    QI ≤ (m:ℝ)*(Nat.ceil ((designVolume m δ QI QX:ℝ)/56):ℝ) ∧
    QX ≤ (m:ℝ)*(Nat.ceil ((designVolume m δ QI QX:ℝ)/1080):ℝ) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hI : ⌈56*QI/(m:ℝ)⌉₊ ≤ designVolume m δ QI QX :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hX : ⌈1080*QX/(m:ℝ)⌉₊ ≤ designVolume m δ QI QX :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hIr : (⌈56*QI/(m:ℝ)⌉₊:ℝ) ≤ designVolume m δ QI QX := by exact_mod_cast hI
  have hXr : (⌈1080*QX/(m:ℝ)⌉₊:ℝ) ≤ designVolume m δ QI QX := by exact_mod_cast hX
  have hi := (div_le_iff₀ hm').mp ((Nat.le_ceil (56*QI/(m:ℝ))).trans hIr)
  have hx := (div_le_iff₀ hm').mp ((Nat.le_ceil (1080*QX/(m:ℝ))).trans hXr)
  have hi' := mul_le_mul_of_nonneg_left (Nat.le_ceil ((designVolume m δ QI QX:ℝ)/56)) hm'.le
  have hx' := mul_le_mul_of_nonneg_left (Nat.le_ceil ((designVolume m δ QI QX:ℝ)/1080)) hm'.le
  constructor <;> nlinarith

def DesignedSuccess (R : ℕ) (N : CountState R) (V m : ℕ) (policy : ReturnedHistory R → Intervention)
    (rho QI QX : ℝ) : Set (ReturnedHistory R) :=
  {h | h ∈ OperationalSuccess R N V m policy ∧ QI ≤ returnedTotal h 1 ∧ QX ≤ returnedTotal h 0 ∧
    ∀ tr : HistoryTrace R N V policy h,∀ b ∈ tr.visitedBath,
      1-rho ≤ (b.val:ℝ)/R ∧ (b.val:ℝ)/R ≤ 1 ∧ ((bathOf b).waste:ℝ)/R ≤ rho}

/-- Simultaneous inverse design: confidence, integer outputs and every-prefix fuel tolerance. -/
theorem pure_inverse_design (m : ℕ) (hm : 0 < m) (δ rho QI QX : ℝ) (hd : 0 < δ) (hr : 0 < rho)
    (policy : ReturnedHistory (reservoirSize (designVolume m δ QI QX) m rho) → Intervention) :
    let V := designVolume m δ QI QX
    let R := reservoirSize V m rho
    let N : CountState R := (![0,0,V,0,0,0],pureFuel R)
    let params := pureParameters R (reservoir_size_positive V m rho) 20 (1/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ENNReal.ofReal (1-δ) ≤
      fullHistoryKernel (returnedHistoryStep R N V params
        (by exact_mod_cast (show 0 < V by have := design_volume_scale m δ QI QX; dsimp [V]; omega)) policy) m []
        (DesignedSuccess R N V m policy rho QI QX) := by
  dsimp only
  let V := designVolume m δ QI QX
  let R := reservoirSize V m rho
  let N : CountState R := (![0,0,V,0,0,0],pureFuel R)
  have hR : 0 < R := reservoir_size_positive V m rho
  have hN : Restart V N.1 := all_free_restart V
  have hs := design_volume_scale m δ QI QX
  have hb := design_volume_budget m hm δ QI QX hd
  apply (finite_bath_budget R N V _ _ policy hs hN m δ hb).trans
  apply measure_mono
  intro h hh
  obtain ⟨hI,hX⟩ := design_volume_outputs m hm δ QI QX
  refine ⟨hh,hI.trans hh.2.2.1,hX.trans hh.2.2.2.1,?_⟩
  intro tr b hvisit
  exact pure_prefix_tolerance tr hR rfl m hh.1 rho (reservoir_size_budget V m rho hr) b hvisit

end
end FiniteReservoir
