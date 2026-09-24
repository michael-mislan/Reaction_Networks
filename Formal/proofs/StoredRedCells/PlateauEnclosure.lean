import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

/-! Order-theoretic scope of the service-constrained turnover problem.

`P` is an abstract feasible set and `Mv`, `Qv` are two real observables
("service" and "turnover").  At a required service level `m` the restricted
problem maximises `Qv` over `{ξ | ξ ∈ P ∧ m ≤ Mv ξ}`.  Every statement below
speaks about an *attained* optimum, written `IsGreatest (Qv '' ...) v`, so no
supremum junk value and no boundedness hypothesis is involved; nothing here
asserts that such a `v` exists.  No chemistry, no kinetics, no storage model is
used: these are statements about sets and two real-valued functions. -/
namespace StoredRedCells.PlateauEnclosure
noncomputable section

/-- One witness that clears the required service level makes the restricted
problem feasible at every lower level. -/
theorem feasible_nonempty {α : Type*} {P : Set α} {Mv : α → ℝ} {m mh : ℝ}
    {ξh : α} (hmem : ξh ∈ P) (hM : mh ≤ Mv ξh) (hmle : m ≤ mh) :
    {ξ | ξ ∈ P ∧ m ≤ Mv ξ}.Nonempty :=
  ⟨ξh, hmem, hmle.trans hM⟩

/-- Two-sided enclosure of an attained restricted optimum: a global upper
certificate `hU` caps it and a single feasible witness floors it, uniformly in
every service level `m` between `0` and the witness level `mh`.  The hypothesis
`hmh0 : 0 ≤ mh` is retained as part of the declared scope, but the enclosure
does not depend on it: the upper bound needs only `0 ≤ m`.  It is discharged
below into the unused side fact `0 ≤ Mv ξh`. -/
theorem uniform_enclosure {α : Type*} {P : Set α} {Mv Qv : α → ℝ}
    {L U m mh v : ℝ} {ξh : α}
    (hU : ∀ ξ ∈ P, 0 ≤ Mv ξ → Qv ξ ≤ U)
    (hmem : ξh ∈ P) (hM : mh ≤ Mv ξh) (hL : L ≤ Qv ξh) (hmh0 : 0 ≤ mh)
    (hm0 : 0 ≤ m) (hmle : m ≤ mh)
    (hv : IsGreatest (Qv '' {ξ | ξ ∈ P ∧ m ≤ Mv ξ}) v) :
    L ≤ v ∧ v ≤ U := by
  have hwitness : ξh ∈ {ξ | ξ ∈ P ∧ m ≤ Mv ξ} :=
    ⟨hmem, hmle.trans hM⟩
  have hmh : (0 : ℝ) ≤ Mv ξh := hmh0.trans hM
  refine ⟨hL.trans (hv.2 ⟨ξh, hwitness, rfl⟩), ?_⟩
  obtain ⟨ξ, ⟨hξP, hξM⟩, hξQ⟩ := hv.1
  exact hξQ ▸ hU ξ hξP (hm0.trans hξM)

/-- Raising the required service level can only lower an attained optimum. -/
theorem value_antitone {α : Type*} {P : Set α} {Mv Qv : α → ℝ}
    {m₁ m₂ v₁ v₂ : ℝ} (hm : m₁ ≤ m₂)
    (hv₁ : IsGreatest (Qv '' {ξ | ξ ∈ P ∧ m₁ ≤ Mv ξ}) v₁)
    (hv₂ : IsGreatest (Qv '' {ξ | ξ ∈ P ∧ m₂ ≤ Mv ξ}) v₂) :
    v₂ ≤ v₁ := by
  obtain ⟨ξ, ⟨hξP, hξM⟩, hξQ⟩ := hv₂.1
  exact hξQ ▸ hv₁.2 ⟨ξ, ⟨hξP, hm.trans hξM⟩, rfl⟩

/-- Concavity of the attained optimum in the required service level, for a
convex feasible set and linear observables. -/
theorem value_concave {α : Type*} [AddCommGroup α] [Module ℝ α]
    {P : Set α} {Mv Qv : α → ℝ} {m₁ m₂ v₁ v₂ a b v : ℝ}
    (hP : Convex ℝ P) (hM : IsLinearMap ℝ Mv) (hQ : IsLinearMap ℝ Qv)
    (hv₁ : IsGreatest (Qv '' {ξ | ξ ∈ P ∧ m₁ ≤ Mv ξ}) v₁)
    (hv₂ : IsGreatest (Qv '' {ξ | ξ ∈ P ∧ m₂ ≤ Mv ξ}) v₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hv : IsGreatest (Qv '' {ξ | ξ ∈ P ∧ a * m₁ + b * m₂ ≤ Mv ξ}) v) :
    a * v₁ + b * v₂ ≤ v := by
  obtain ⟨ξ₁, ⟨hξ₁P, hξ₁M⟩, hξ₁Q⟩ := hv₁.1
  obtain ⟨ξ₂, ⟨hξ₂P, hξ₂M⟩, hξ₂Q⟩ := hv₂.1
  have hmemP : a • ξ₁ + b • ξ₂ ∈ P := hP hξ₁P hξ₂P ha hb hab
  have hMv : Mv (a • ξ₁ + b • ξ₂) = a * Mv ξ₁ + b * Mv ξ₂ := by
    rw [hM.map_add, hM.map_smul, hM.map_smul, smul_eq_mul, smul_eq_mul]
  have hQv : Qv (a • ξ₁ + b • ξ₂) = a * Qv ξ₁ + b * Qv ξ₂ := by
    rw [hQ.map_add, hQ.map_smul, hQ.map_smul, smul_eq_mul, smul_eq_mul]
  have h₁ : a * m₁ ≤ a * Mv ξ₁ := mul_le_mul_of_nonneg_left hξ₁M ha
  have h₂ : b * m₂ ≤ b * Mv ξ₂ := mul_le_mul_of_nonneg_left hξ₂M hb
  have hfeas : a * m₁ + b * m₂ ≤ Mv (a • ξ₁ + b • ξ₂) := by
    rw [hMv]; linarith
  have hle : Qv (a • ξ₁ + b • ξ₂) ≤ v :=
    hv.2 ⟨a • ξ₁ + b • ξ₂, ⟨hmemP, hfeas⟩, rfl⟩
  rw [hQv, hξ₁Q, hξ₂Q] at hle
  exact hle

/-- Above a global service ceiling the restricted problem has no feasible
point at all, so no optimum can be attained there. -/
theorem infeasible_above_ceiling {α : Type*} {P : Set α} {Mv : α → ℝ}
    {Umax m : ℝ} (hceil : ∀ ξ ∈ P, Mv ξ ≤ Umax) (hm : Umax < m) :
    {ξ | ξ ∈ P ∧ m ≤ Mv ξ} = ∅ := by
  ext ξ
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hξP hξM
  exact absurd (hξM.trans (hceil ξ hξP)) (not_le.mpr hm)

/-- Transient integral bound for a scalar balance `g' = u - v` whose outflow is
capped by `a * g` and whose inflow is capped by `b * (C - g)`.  The bound is
obtained from the adjoint weight `lam s = (a/(a+b))*(1 - exp (-(a+b)*(T-s)))`,
which satisfies `lam T = 0` and `lam' = (a+b)*lam - a`.  The derivative
hypothesis is global in `t`; the four sign and cap hypotheses are only assumed
on `[0, T]`.  The nonnegativity hypotheses `hv0` and `hu0` are retained as part
of the declared model scope, but the bound does not depend on them: only the
two caps `hva` and `hub` enter the pointwise estimate.  They are discharged
below into the unused side fact `hsigns`. -/
theorem carrier_transient_bound (a b C T : ℝ) (g u v : ℝ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hT : 0 ≤ T)
    (huc : Continuous u) (hvc : Continuous v)
    (hg : ∀ t, HasDerivAt g (u t - v t) t)
    (hv0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ v t)
    (hva : ∀ t ∈ Set.Icc 0 T, v t ≤ a * g t)
    (hu0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ u t)
    (hub : ∀ t ∈ Set.Icc 0 T, u t ≤ b * (C - g t)) :
    (∫ t in (0:ℝ)..T, v t) ≤
      (a*b/(a+b))*C*T +
        (a/(a+b))*(g 0 - b*C/(a+b))*(1 - Real.exp (-(a+b)*T)) := by
  have hk : (0:ℝ) < a + b := by linarith
  have hkne : (a + b) ≠ 0 := ne_of_gt hk
  have hsigns : ∀ t ∈ Set.Icc (0:ℝ) T, 0 ≤ v t ∧ 0 ≤ u t :=
    fun t ht => ⟨hv0 t ht, hu0 t ht⟩
  have hgc : Continuous g :=
    (show Differentiable ℝ g from fun t => (hg t).differentiableAt).continuous
  have hline : ∀ s : ℝ, HasDerivAt (fun x : ℝ => -(a+b)*(T-x)) (a+b) s := by
    intro s
    simpa using ((hasDerivAt_id s).const_sub T).const_mul (-(a+b))
  let lam : ℝ → ℝ := fun s => (a/(a+b)) * (1 - Real.exp (-(a+b)*(T-s)))
  have hlam_deriv : ∀ s, HasDerivAt lam ((a+b) * lam s - a) s := by
    intro s
    have h3 := (((hline s).exp).const_sub 1).const_mul (a/(a+b))
    convert h3 using 1
    dsimp [lam]
    field_simp
    ring
  have hlamc : Continuous lam :=
    (show Differentiable ℝ lam from fun s => (hlam_deriv s).differentiableAt).continuous
  have hlam_nonneg : ∀ s ∈ Set.Icc (0:ℝ) T, 0 ≤ lam s := by
    intro s hs
    have h1 : Real.exp (-(a+b)*(T-s)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hs.2])
    have h2 : (0:ℝ) ≤ a/(a+b) := le_of_lt (div_pos ha hk)
    dsimp [lam]
    nlinarith
  have hlam_le_one : ∀ s, lam s ≤ 1 := by
    intro s
    have hE : 0 < Real.exp (-(a+b)*(T-s)) := Real.exp_pos _
    have hfrac : a/(a+b) < 1 := by rw [div_lt_one hk]; linarith
    have hpos : 0 < a/(a+b) := div_pos ha hk
    dsimp [lam]
    nlinarith [mul_pos hpos hE]
  have hF : ∀ s, HasDerivAt (fun x => lam x * g x)
      (((a+b) * lam s - a) * g s + lam s * (u s - v s)) s :=
    fun s => (hlam_deriv s).mul (hg s)
  have hcontF : Continuous
      (fun s => ((a+b) * lam s - a) * g s + lam s * (u s - v s)) :=
    (((continuous_const.mul hlamc).sub continuous_const).mul hgc).add
      (hlamc.mul (huc.sub hvc))
  have hcontL : Continuous (fun s => lam s * b * C) :=
    (hlamc.mul continuous_const).mul continuous_const
  have hpoint : ∀ s ∈ Set.Icc (0:ℝ) T,
      v s + (((a+b) * lam s - a) * g s + lam s * (u s - v s)) ≤ lam s * b * C := by
    intro s hs
    have h1 : 0 ≤ lam s := hlam_nonneg s hs
    have h2 : lam s ≤ 1 := hlam_le_one s
    have h3 : v s ≤ a * g s := hva s hs
    have h4 : u s ≤ b * (C - g s) := hub s hs
    nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ 1 - lam s),
               mul_le_mul_of_nonneg_left h4 h1]
  have hmono : (∫ s in (0:ℝ)..T,
        (v s + (((a+b) * lam s - a) * g s + lam s * (u s - v s))))
      ≤ ∫ s in (0:ℝ)..T, lam s * b * C :=
    intervalIntegral.integral_mono_on hT
      ((hvc.add hcontF).intervalIntegrable _ _)
      (hcontL.intervalIntegrable _ _) hpoint
  have hsplit : (∫ s in (0:ℝ)..T,
        (v s + (((a+b) * lam s - a) * g s + lam s * (u s - v s))))
      = (∫ s in (0:ℝ)..T, v s)
        + ∫ s in (0:ℝ)..T, (((a+b) * lam s - a) * g s + lam s * (u s - v s)) :=
    intervalIntegral.integral_add (hvc.intervalIntegrable _ _)
      (hcontF.intervalIntegrable _ _)
  have hftc : (∫ s in (0:ℝ)..T,
        (((a+b) * lam s - a) * g s + lam s * (u s - v s)))
      = lam T * g T - lam 0 * g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s)
      (hcontF.intervalIntegrable _ _)
  have hlamT : lam T = 0 := by dsimp [lam]; simp
  have hlam0 : lam 0 = (a/(a+b)) * (1 - Real.exp (-(a+b)*T)) := by
    dsimp [lam]; rw [sub_zero]
  have hH : ∀ s, HasDerivAt
      (fun x : ℝ => (a*b*C/(a+b)) * (x - (1/(a+b)) * Real.exp (-(a+b)*(T-x))))
      (lam s * b * C) s := by
    intro s
    have h3 : HasDerivAt
        (fun x : ℝ => x - (1/(a+b)) * Real.exp (-(a+b)*(T-x)))
        (1 - (1/(a+b)) * (Real.exp (-(a+b)*(T-s)) * (a+b))) s :=
      (hasDerivAt_id s).sub (((hline s).exp).const_mul (1/(a+b)))
    have h4 := h3.const_mul (a*b*C/(a+b))
    convert h4 using 1
    dsimp [lam]
    field_simp
  have hintegral : (∫ s in (0:ℝ)..T, lam s * b * C)
      = (a*b*C/(a+b))*T
        - (a*b*C/((a+b)*(a+b))) * (1 - Real.exp (-(a+b)*T)) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hH s)
      (hcontL.intervalIntegrable _ _)]
    simp only [sub_self, sub_zero, mul_zero, Real.exp_zero, mul_one]
    field_simp
    ring
  have hclose : (a*b*C/(a+b))*T
      - (a*b*C/((a+b)*(a+b))) * (1 - Real.exp (-(a+b)*T))
      + lam 0 * g 0
      = (a*b/(a+b))*C*T
        + (a/(a+b))*(g 0 - b*C/(a+b))*(1 - Real.exp (-(a+b)*T)) := by
    rw [hlam0]
    field_simp
    ring
  rw [hsplit, hftc, hlamT, hintegral] at hmono
  linarith [hmono, hclose]

end
end StoredRedCells.PlateauEnclosure
