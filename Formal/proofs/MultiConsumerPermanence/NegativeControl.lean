import proofs.MultiConsumerPermanence.RateLiteralSource
import proofs.MultiConsumerPermanence.LoadedPotential

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Filter Topology
open scoped BigOperators

/-- A separate negative-control source: no quadratic consumer loss and unequal
linear losses. This source lies outside the positive theorem's rate cube. -/
noncomputable def unregulatedRates (e : ℝ) : Rates 2 :=
  ⟨residentRates e,(fun _ => 1),![(1/2:ℝ),3/4],(fun _ => 0)⟩

structure IsUnregulatedTrajectory (e : ℝ) (Y : ℝ → State)
    (x : ℝ → Fin 2 → ℝ) : Prop extends
    IsLoadedResidentTrajectory e Y (fun t => total (x t)) where
  consumer_positive : ∀ t, 0 ≤ t → ∀ i, 0 < x t i
  dx : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => x s i)
    (x t i*((Y t).z-(![(1/2:ℝ),3/4] i))) t

theorem unregulated_source_deriv (e : ℝ) (Y : ℝ → State) (x : ℝ → Fin 2 → ℝ)
    (h : IsUnregulatedTrajectory e Y x) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => (Sum.elim ![(Y s).A,(Y s).B,(Y s).z,(Y s).H] (x s) : Vector 2))
      (perturbedLiteralField (unregulatedRates e)
        (Sum.elim ![(Y t).A,(Y t).B,(Y t).z,(Y t).H] (x t))) t := by
  rw [perturbed_literal_field_eq]
  apply hasDerivAt_pi.2
  intro i
  cases i with
  | inl i =>
    fin_cases i
    · convert h.dA t ht using 1
      simp [perturbedField,rateField,rateDonorVector,baseRates,unregulatedRates,residentRates,rateA,fA,flagshipRates]
      ring
    · convert h.dB t ht using 1
      simp [perturbedField,rateField,rateDonorVector,baseRates,unregulatedRates,residentRates,rateB,fB,flagshipRates]
      ring
    · convert h.dz t ht using 1
      simp [perturbedField,rateField,rateDonorVector,baseRates,unregulatedRates,residentRates,rateZ,fZ,flagshipRates,copyingLoad,total]
      ring
    · convert h.dH t ht using 1
      dsimp [perturbedField,rateField,rateDonorVector,baseRates,unregulatedRates,residentRates,rateH,fH,flagshipRates]
      ring
  | inr i =>
    simpa [perturbedField,unregulatedRates] using h.dx t ht i

theorem unregulated_total_deriv (e : ℝ) (Y : ℝ → State) (x : ℝ → Fin 2 → ℝ)
    (h : IsUnregulatedTrajectory e Y x) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => total (x s))
      ((Y t).z*total (x t)-(1/2)*x t 0-(3/4)*x t 1) t := by
  convert (h.dx t ht 0).add (h.dx t ht 1) using 1 <;>
    simp [total,Fin.sum_univ_two,Pi.add_apply,funext_iff]
  ring

theorem unregulated_total_upper (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin 2 → ℝ) (h : IsUnregulatedTrajectory e Y x) :
    ∀ᶠ t in atTop, total (x t) < 400 := by
  have habs := loaded_eventually_resident_absorbing e he he' Y _ h.toIsLoadedResidentTrajectory
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.1 (habs.and (eventually_ge_atTop (0:ℝ)))
  let W := fun t => (Y t).z+(7/4:ℝ)*(Y t).H+total (x t)
  let v := fun t => fZ (flagshipRates e) (Y t).A (Y t).B (Y t).z (Y t).H+
    (7/4:ℝ)*fH (flagshipRates e) (Y t).z (Y t).H-(1/2)*x t 0-(3/4)*x t 1
  have hW : ∀ᶠ t in atTop, W t < 400 := by
    apply eventual_upper_of_linear_drift W v T 110 (2/7) 400 (by norm_num) (by norm_num)
    · intro t ht
      have h0 := (hT t ht).2
      convert ((h.dz t h0).add ((h.dH t h0).const_mul (7/4:ℝ))).add
        (unregulated_total_deriv e Y x h t h0) using 1
      dsimp [v]
      ring
    · intro t ht
      have h0 := (hT t ht).2
      have hp := h.positive t h0
      have hb := (hT t ht).1.1
      have hh := weighted_upper_comparison_general (Y t).A (Y t).B (Y t).z (Y t).H e 34
        (by linarith [hp.2.1]) hp.2.1.le hp.2.2.1.le hp.2.2.2.le
      have hx0 := (h.consumer_positive t h0 0).le
      have hx1 := (h.consumer_positive t h0 1).le
      dsimp [W,v]
      simp only [total,Fin.sum_univ_two]
      nlinarith only [hh,hx0,hx1]
  filter_upwards [hW,eventually_ge_atTop (0:ℝ)] with t ht h0
  have hp := h.positive t h0
  dsimp [W] at ht
  linarith only [ht,hp.2.2.1,hp.2.2.2]

theorem no_individual_limitation_extinction_control (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin 2 → ℝ) (h : IsUnregulatedTrajectory e Y x) :
    Tendsto (fun t => x t 1) atTop (𝓝 0) := by
  have hu := unregulated_total_upper e he he' Y x h
  have hq : ∀ t, 0 ≤ t → HasDerivAt (fun s => x s 1/x s 0) (-(1/4)*(x t 1/x t 0)) t := by
    intro t ht
    have hx0 := ne_of_gt (h.consumer_positive t ht 0)
    convert (h.dx t ht 1).div (h.dx t ht 0) hx0 using 1
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    field_simp
    ring
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact ha.trans (h.consumer_positive t ht 1)
  · intro eps heps
    have hsmall : ∀ᶠ t in atTop, x t 1/x t 0 < eps/400 := by
      apply eventual_upper_of_linear_drift (fun t => x t 1/x t 0)
        (fun t => -(1/4)*(x t 1/x t 0)) 0 0 (1/4) (eps/400)
        (by norm_num) (by simpa using div_pos heps (by norm_num : (0:ℝ)<400)) hq
      intro t _
      linarith
    filter_upwards [hsmall,hu,eventually_ge_atTop (0:ℝ)] with t hsmall hu h0
    have hx0 := h.consumer_positive t h0 0
    have hx0u : x t 0 < 400 := (show x t 0 ≤ total (x t) from
      Finset.single_le_sum (fun i _ => (h.consumer_positive t h0 i).le) (Finset.mem_univ 0)).trans_lt hu
    have hh := (div_lt_iff₀ hx0).1 hsmall
    have hh' := mul_lt_mul_of_pos_left hx0u (div_pos heps (by norm_num : (0:ℝ)<400))
    nlinarith only [hh,hh']

end MultiConsumerPermanence
