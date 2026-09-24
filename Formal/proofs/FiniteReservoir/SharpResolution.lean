import proofs.FiniteReservoir.SharpMission

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

def designVolumeSharp (m : ℕ) (δ QI QX : ℝ) : ℕ :=
  max (sharpVolume m δ) (max ⌈56*QI/(m:ℝ)⌉₊ ⌈1080*QX/(m:ℝ)⌉₊)

theorem designVolumeSharp_scale (m : ℕ) (δ QI QX : ℝ) :
    50000000000 ≤ designVolumeSharp m δ QI QX :=
  (sharp_volume_scale m δ).trans (le_max_left _ _)

theorem designVolumeSharp_budget (m : ℕ) (hm : 0 < m) (δ QI QX : ℝ) (hd : 0 < δ) :
    (m:ℝ)*sharpBothError (designVolumeSharp m δ QI QX) ≤ δ := by
  apply sharp_confidence_budget _ m hm δ hd
    (le_trans (by norm_num) (designVolumeSharp_scale m δ QI QX))
  have hc : ⌈Real.log (101*(m:ℝ)/δ)/phaseRate⌉₊ ≤ designVolumeSharp m δ QI QX :=
    (le_max_right _ _).trans (le_max_left _ _)
  exact (Nat.le_ceil _).trans (by exact_mod_cast hc)

theorem designVolumeSharp_outputs (m : ℕ) (hm : 0 < m) (δ QI QX : ℝ) :
    QI ≤ (m:ℝ)*(Nat.ceil ((designVolumeSharp m δ QI QX:ℝ)/56):ℝ) ∧
    QX ≤ (m:ℝ)*(Nat.ceil ((designVolumeSharp m δ QI QX:ℝ)/1080):ℝ) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hI : ⌈56*QI/(m:ℝ)⌉₊ ≤ designVolumeSharp m δ QI QX :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hX : ⌈1080*QX/(m:ℝ)⌉₊ ≤ designVolumeSharp m δ QI QX :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hIr : (⌈56*QI/(m:ℝ)⌉₊:ℝ) ≤ designVolumeSharp m δ QI QX := by exact_mod_cast hI
  have hXr : (⌈1080*QX/(m:ℝ)⌉₊:ℝ) ≤ designVolumeSharp m δ QI QX := by exact_mod_cast hX
  have hi := (div_le_iff₀ hm').mp ((Nat.le_ceil (56*QI/(m:ℝ))).trans hIr)
  have hx := (div_le_iff₀ hm').mp ((Nat.le_ceil (1080*QX/(m:ℝ))).trans hXr)
  have hi' := mul_le_mul_of_nonneg_left (Nat.le_ceil ((designVolumeSharp m δ QI QX:ℝ)/56)) hm'.le
  have hx' := mul_le_mul_of_nonneg_left (Nat.le_ceil ((designVolumeSharp m δ QI QX:ℝ)/1080)) hm'.le
  constructor <;> nlinarith

def SharpDesignTarget (R : ℕ) (N : CountState R) (V m : ℕ)
    (policy : ReturnedHistory R → Intervention) (rho QI QX : ℝ) : Set (ReturnedHistory R) :=
  {h | h ∈ SharpDesignedSuccess R N V m policy rho ∧
    QI ≤ returnedTotal h 1 ∧ QX ≤ returnedTotal h 0}

/-- Inverse design at the unrounded phase rate and the halved service allowance:
confidence, both integer output demands and every-prefix fuel tolerance. -/
theorem sharp_inverse_design (m : ℕ) (hm : 0 < m) (δ rho QI QX : ℝ) (hd : 0 < δ) (hr : 0 < rho)
    (policy : ReturnedHistory
      (reservoirSizeSharp (designVolumeSharp m δ QI QX) m rho) → Intervention) :
    let V := designVolumeSharp m δ QI QX
    let R := reservoirSizeSharp V m rho
    let N : CountState R := (![0,0,V,0,0,0],pureFuel R)
    let params := pureParameters R (reservoirSizeSharp_positive V m rho) 20 (1/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ENNReal.ofReal (1-δ) ≤
      fullHistoryKernel (returnedHistoryStep R N V params
        (by exact_mod_cast (show 0 < V by
          have := designVolumeSharp_scale m δ QI QX; dsimp [V]; omega)) policy) m []
        (SharpDesignTarget R N V m policy rho QI QX) := by
  dsimp only
  let V := designVolumeSharp m δ QI QX
  let R := reservoirSizeSharp V m rho
  have hR : 0 < R := reservoirSizeSharp_positive V m rho
  let N : CountState R := (![0,0,V,0,0,0],pureFuel R)
  let params : Parameters R := pureParameters R hR 20 (1/50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs := designVolumeSharp_scale m δ QI QX
  have hb := designVolumeSharp_budget m hm δ QI QX hd
  have hVpos : 0 < (V:ℝ) := by
    have : 50000000000 ≤ V := hs
    have : (0:ℕ) < V := by omega
    exact_mod_cast this
  have hN : Restart V N.1 := all_free_restart V
  apply (sharp_mission_bound R N V params hVpos policy hs hR rfl rfl rfl hN m rho
    (reservoirSizeSharp_budget V m rho hr) δ hb).trans
  apply measure_mono
  intro h hh
  obtain ⟨hI,hX⟩ := designVolumeSharp_outputs m hm δ QI QX
  exact ⟨hh,hI.trans hh.1.2.2.1,hX.trans hh.1.2.2.2.1⟩

/-- Same copy scale as the original certified example, half the fuel inventory,
and a far smaller failure bound. -/
theorem sharp_hundred_halved_bath
    (policy : ReturnedHistory 20000000000000 → Intervention) :
    let V : ℕ := 200000000000
    let R : ℕ := 20000000000000
    let N : CountState R := (![0,0,V,0,0,0],pureFuel R)
    let params := pureParameters R (by norm_num) 20 (1/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ENNReal.ofReal (1-1/10000000000000:ℝ) ≤
      fullHistoryKernel (returnedHistoryStep R N V params (by norm_num) policy) 100 []
        (SharpDesignedSuccess R N V 100 policy (1/10)) := by
  dsimp only
  have hN : Restart 200000000000 ![0,0,200000000000,0,0,0] := all_free_restart _
  have hfl : ⌊((200000000000:ℕ):ℝ)/10⌋₊ = 20000000000 := by
    rw [show ((200000000000:ℕ):ℝ)/10 = ((20000000000:ℕ):ℝ) by push_cast; norm_num]
    exact Nat.floor_natCast _
  have hg : grossAllowanceSharp 200000000000 100 ≤ (1/10)*(20000000000000:ℝ) := by
    unfold grossAllowanceSharp
    rw [hfl]
    norm_num
  have hbudget : (100:ℝ)*sharpBothError 200000000000 ≤ 1/10000000000000 := by
    have hs := sharp_single_exponential 200000000000 (by norm_num)
    have hx : (42:ℝ) ≤ phaseRate*200000000000 := by unfold phaseRate; norm_num
    have hn : Real.exp (-phaseRate*200000000000) ≤ Real.exp (-42) :=
      Real.exp_le_exp.mpr (by linarith)
    have h20 := FiniteCopyReactor.exp_twenty_certificate
    have h42 : (235031040000000000:ℝ) ≤ Real.exp 42 := by
      have hsum : Real.exp 42 = Real.exp 20*Real.exp 20*Real.exp 2 := by
        rw [← Real.exp_add,← Real.exp_add]
        norm_num
      have h2 : (1:ℝ) ≤ Real.exp 2 := Real.one_le_exp_iff.mpr (by norm_num)
      rw [hsum]
      nlinarith [Real.exp_pos 20,Real.exp_pos 2]
    have hinv : Real.exp (-(42:ℝ)) ≤ 1/235031040000000000 := by
      rw [Real.exp_neg,inv_le_comm₀ (Real.exp_pos 42) (by norm_num)]
      linarith
    have hne : Real.exp (-phaseRate*200000000000) = Real.exp (-(phaseRate*200000000000)) := by
      congr 1
      ring
    linarith
  convert sharp_mission_bound 20000000000000 (![0,0,200000000000,0,0,0],pureFuel 20000000000000)
    200000000000
    (pureParameters 20000000000000 (by norm_num) 20 (1/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) policy (by norm_num) (by norm_num) rfl rfl rfl hN 100 (1/10) hg
    (1/10000000000000) hbudget using 1

/-- Consolidated root of the refinement: general theorem, design rule and two instances. -/
theorem sharp_finite_reservoir_operation (m : ℕ) (hm : 0 < m) (δ rho QI QX : ℝ)
    (hd : 0 < δ) (hr : 0 < rho)
    (policy : ReturnedHistory
      (reservoirSizeSharp (designVolumeSharp m δ QI QX) m rho) → Intervention) :
    let V := designVolumeSharp m δ QI QX
    let R := reservoirSizeSharp V m rho
    let N : CountState R := (![0,0,V,0,0,0],pureFuel R)
    let params := pureParameters R (reservoirSizeSharp_positive V m rho) 20 (1/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ENNReal.ofReal (1-δ) ≤
      fullHistoryKernel (returnedHistoryStep R N V params
        (by exact_mod_cast (show 0 < V by
          have := designVolumeSharp_scale m δ QI QX; dsimp [V]; omega)) policy) m []
        (SharpDesignTarget R N V m policy rho QI QX) :=
  sharp_inverse_design m hm δ rho QI QX hd hr policy

end
end FiniteReservoir
