import proofs.ProductiveMemory.ExtractionSupport
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false

def productiveOutputValue (W0 : ℕ) (s : ProductiveState) : ℝ :=
  Real.exp (2*(4*(W0:ℝ)-(s.population.resource:ℝ))-(s.collected:ℝ))

def productiveOutputObservable (N W0 : ℕ) {D : Finset ProductiveState} (x : ProductiveStopped D) : ℝ :=
  productiveOutputValue W0 (productivePhysical N x)

theorem productive_output_value_nonneg (W0 : ℕ) (s : ProductiveState) : 0 ≤ productiveOutputValue W0 s :=
  (Real.exp_pos _).le

theorem productive_output_resident (N W0 : ℕ) (s : ProductiveState)
    (i : Fin s.population.live.length) (r : Fin 13) :
    productiveOutputValue W0 (productiveOutcome N s (.inl ⟨i,.inl r⟩)) = productiveOutputValue W0 s := rfl

theorem productive_output_growth (N W0 : ℕ) (s : ProductiveState) (hQ : 0 < s.population.resource)
    (i : Fin s.population.live.length)
    (d : {d : Counts // d ∈ daughterDraws (nextCompartment (selectedCell s.population i).compartment (.inr ())).1}) :
    productiveOutputValue W0 (productiveOutcome N s (.inl ⟨i,.inr d⟩)) =
      productiveOutputValue W0 s*Real.exp 2 := by
  unfold productiveOutputValue productiveOutcome growthAt
  dsimp only
  split_ifs <;> dsimp only <;> rw [← Real.exp_add,Nat.cast_sub (by omega : 1 ≤ s.population.resource),Nat.cast_one] <;> congr 1 <;> ring

theorem productive_output_extraction (N W0 : ℕ) (s : ProductiveState) (i : Fin s.population.live.length) :
    productiveOutputValue W0 (productiveOutcome N s (.inr i)) = productiveOutputValue W0 s*Real.exp (-1) := by
  unfold productiveOutputValue productiveOutcome extractionAt
  dsimp only
  rw [← Real.exp_add,Nat.cast_add,Nat.cast_one]
  congr 1
  ring

theorem productive_output_scalar (rho beta : ℝ) (hb : 0 ≤ beta) (hr : 16*beta ≤ rho) :
    beta*(Real.exp 2-1)+rho*(Real.exp (-1)-1) ≤ 0 := by
  have he2 : Real.exp 2 ≤ 9 := by
    have he := Real.exp_one_lt_three
    have hp := Real.exp_pos 1
    have hid : Real.exp 2 = Real.exp 1*Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [hid]
    nlinarith only [he,hp]
  have hem : Real.exp (-1) ≤ 1/2 := by
    have hid : Real.exp (-1)*Real.exp 1=1 := by rw [← Real.exp_add]; norm_num
    have hm := mul_le_mul_of_nonneg_left Real.exp_one_gt_two.le (Real.exp_pos (-1)).le
    linarith only [hid,hm]
  have hrho : 0 ≤ rho := by linarith only [hb,hr]
  have h1 := mul_le_mul_of_nonneg_left he2 hb
  have h2 := mul_le_mul_of_nonneg_left hem hrho
  nlinarith only [h1,h2,hr]

theorem productive_output_generator_binding (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (Ω N W0 J : ℕ) (zL zH : ℝ) (D : Finset ProductiveState) (s : ProductiveActive D)
    (hQ : 0 < s.val.population.resource) :
    (productiveStoppedModel rho γ hr hg Ω N W0 J zL zH D).generator (productiveOutputObservable N W0) (.inl s) =
      ∑ i : Fin s.val.population.live.length,
        ((selectedCell s.val.population i).compartment.1 2:ℝ)*productiveOutputValue W0 s.val*
          (resourceCoefficient γ s.val.population.resource Ω*(Real.exp 2-1)+rho*(Real.exp (-1)-1)) := by
  classical
  have hnext (e : ProductiveEvent s.val) :
      productivePhysical N (productiveStoppedNext N W0 J rho zL zH D (.inl s) ⟨s,e⟩) =
        productiveOutcome N s.val e := productive_physical_chosen N W0 J rho zL zH D ⟨s,e⟩
  rw [productive_active_generator,Fintype.sum_sum_type]
  simp only [productiveOutputObservable]
  simp only [hnext]
  simp only [productivePhysical,productive_output_extraction]
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sum_type]
  simp only [productive_output_resident,productive_output_growth N W0 s.val hQ,
    sub_self,mul_zero,Finset.sum_const_zero,zero_add,productiveRate]
  have hdraw (i : Fin s.val.population.live.length) := daughter_constant_sum
    (nextCompartment (selectedCell s.val.population i).compartment (.inr ())).1
    (propensity (resourceCoefficient γ s.val.population.resource Ω) (selectedCell s.val.population i).compartment (.inr ()))
    (productiveOutputValue W0 s.val*Real.exp 2-productiveOutputValue W0 s.val)
  simp_rw [hdraw]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [propensity]
  ring


theorem productive_output_generator (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (hcompare : 16*γ ≤ rho) (N M W0 J : ℕ) (zL zH : ℝ)
    (x : ProductiveStopped (productiveActiveDomain N M W0 J rho zL zH)) :
    (productiveStoppedModel rho γ hr hg (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).generator (productiveOutputObservable N W0) x ≤ 0 := by
  classical
  cases x with
  | inr e => exact (productive_terminal_generator rho γ hr hg (4*W0) N W0 J zL zH _ _ e).le
  | inl s =>
    have hs := productive_active_safe N M W0 J rho zL zH s.val s.property
    obtain ⟨hb,hbmax⟩ := resource_coefficient_bounds γ s.val.population.resource (4*W0) hg hs.2.1
    rw [productive_output_generator_binding rho γ hr hg (4*W0) N W0 J zL zH _ s (Nat.zero_lt_of_lt hs.1)]
    apply Finset.sum_nonpos
    intro i _
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Nat.cast_nonneg _) (productive_output_value_nonneg W0 s.val))
      (productive_output_scalar rho _ hb (by linarith only [hbmax,hcompare]))

end
end ProductiveMemory
