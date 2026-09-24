import proofs.CompositionalMemory.WordClock
import proofs.CompositionalMemory.ActiveObservable

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set HeritableCompositions

noncomputable def modularActiveLiving {k : ℕ} (N : ℕ) (D : Finset (ModularCountState k)) :
    Set (StoppedModularState D) :=
  {x | match x with | none => False | some s => s.val.2 < 2*(k*N)}

theorem word_retained_late_division {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (z₀ z₁ γ : ℝ) (σ : Fin k → Bool) (hγ : 0 < γ)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (b : ℝ) (hb : b ≤ 1/32000000) (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (retainedModularModel γ w hγ.le hw N
      (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b)).total x ≤ q)
    (hdecay : 19*(γ/2)*((k*N : ℕ) : ℝ)/400 ≤ q)
    (s : {s : ModularCountState k // s ∈ productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b})
    (hactive : s.val.2 < 2*(k*N)) :
    ((retainedModularModel γ w hγ.le hw N (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b)).uniformize q hq hclock).poissonized
      (q*modularDeadline γ hγ) (FiniteKernel.eventIndicator (modularActiveLiving N
        (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b))) (some s) ≤
      Real.exp (-9*((k*N : ℕ) : ℝ)/4000) := by
  let D := productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b
  let F : ModularCountState k → ℝ := modularMembraneObservable (k*N) (-1/20)
  let decay := 19*(γ/2)*((k*N : ℕ) : ℝ)/400
  have hf (u : ModularCountState k) : 0 ≤ F u := (Real.exp_pos _).le
  have hg (u) (hu : u ∈ D) (_ : u.2 < 2*(k*N)) :
      modularGenerator γ w F u ≤ -decay*F u+decay*0 := by
    have hrate := (word_membrane_rate_bounds hk N hN z₀ z₁ γ σ hγ.le h₀ h₁ b hb u hu).1
    simpa only [mul_zero,add_zero] using modular_late_generator γ (γ/2) hγ.le w (k*N) u hrate
  have hA : ∀ x ∈ modularActiveLiving N D, Real.exp (-((k*N : ℕ) : ℝ)/20) ≤
      modularActiveObservable N D F x := by
    intro x hx
    cases x with
    | none => exact False.elim hx
    | some u =>
      change u.val.2 < 2*(k*N) at hx
      simp only [modularActiveObservable,if_pos hx]
      apply Real.exp_le_exp.mpr
      have hm : (u.val.2 : ℝ) ≤ 2*((k*N : ℕ) : ℝ) := by exact_mod_cast hx.le
      change -((k*N : ℕ) : ℝ)/20 ≤ (-1/20)*((u.val.2 : ℝ)-((k*N : ℕ) : ℝ))
      linarith only [hm]
  have h := modular_retained_affine_event γ w hw hγ.le N D F hf decay 0
    (by dsimp [decay]; positivity) (by norm_num) hg q (modularDeadline γ hγ) hq hclock hdecay
    (modularActiveLiving N D) (Real.exp (-((k*N : ℕ) : ℝ)/20)) hA s hactive
  have hc := word_center_bounds z₀ z₁ σ h₀ h₁
  have hmem := ((mem_productDomain hk N hN _ hc.1 _ (word_energy_lower σ) b hb s.val).mp s.property).1
  have hs : F s.val ≤ 1 := by
    have hm : ((k*N : ℕ) : ℝ) ≤ (s.val.2 : ℝ) := by exact_mod_cast hmem
    change Real.exp ((-1/20)*((s.val.2 : ℝ)-((k*N : ℕ) : ℝ))) ≤ 1
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith only [hm])
      _ = 1 := Real.exp_zero
  have hh := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-decay*(modularDeadline γ hγ : ℝ))).le
  simp only [add_zero] at h
  have h' := h.trans (by simpa only [mul_one] using hh)
  have ht : (γ/2)*(modularDeadline γ hγ : ℝ)=11/10 := by
    change (γ/2)*(11/(5*γ))=11/10
    field_simp
    ring
  have he : -decay*(modularDeadline γ hγ : ℝ)-(-((k*N : ℕ) : ℝ)/20) =
      -9*((k*N : ℕ) : ℝ)/4000 := by
    dsimp [decay]
    calc
      _ = -(19*((k*N : ℕ) : ℝ)/400)*((γ/2)*(modularDeadline γ hγ : ℝ))+((k*N : ℕ) : ℝ)/20 := by ring
      _ = _ := by rw [ht]; ring
  simpa only [he] using exponential_probability_cancel _ _ _ h'

end CompositionalMemory
