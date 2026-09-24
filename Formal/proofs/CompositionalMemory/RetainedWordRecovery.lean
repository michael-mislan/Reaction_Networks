import proofs.CompositionalMemory.WordEnvelope
import proofs.CompositionalMemory.ProductExit
import proofs.CompositionalMemory.ActiveObservable
import proofs.CompositionalMemory.RecoveryTime

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set HeritableCompositions

noncomputable def wordRetainedUnrecovered {k : ℕ} (N : ℕ) (center : Fin k → Point)
    (σ : Fin k → Bool) (D : Finset (ModularCountState k)) : Set (StoppedModularState D) :=
  {x | match x with | none => False | some c => c.val.2 < 2*(k*N) ∧
    ∃ i, innerEnergy < wordEnergy σ i (fun a => modularConcentration c.val i a-center i a)}

theorem word_retained_recovery {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N) (hNlarge : 140000000000000000000 ≤ N)
    (z₀ z₁ γ κ : ℝ) (σ : Fin k → Bool)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hst₀ : Stationary sourceRates (lift sourceRates z₀))
    (hst₁ : Stationary sourceRates (lift sourceRates z₁))
    (w : Fin k → Fin k → ℝ) (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (b : ℝ) (hb : b ≤ 1/32000000) (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (retainedModularModel γ w hγ hw N
      (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b)).total x ≤ q)
    (hdecay : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (s : {s : ModularCountState k // s ∈ productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b})
    (hactive : s.val.2 < 2*(k*N))
    (hbirth : ∀ i, wordEnergy σ i (fun a => modularConcentration s.val i a-wordCenter z₀ z₁ σ i a) ≤ 4*innerEnergy) :
    ((retainedModularModel γ w hγ hw N (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b)).uniformize q hq hclock).poissonized
      (q*2688) (FiniteKernel.eventIndicator (wordRetainedUnrecovered N (wordCenter z₀ z₁ σ) σ
        (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b))) (some s) ≤
      3*(k : ℝ)*Real.exp (-(N : ℝ)*localAlpha*innerEnergy/2) := by
  classical
  let D := productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b
  let F : Fin k → ModularCountState k → ℝ := fun i u => Real.exp ((N : ℝ)*localAlpha*
    wordEnergy σ i (fun a => modularConcentration u i a-wordCenter z₀ z₁ σ i a))
  let decay := (N : ℝ)*localAlpha*innerEnergy/672
  let C := 2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)
  have hF (i u) : 0 ≤ F i u := (Real.exp_pos _).le
  have hd : 0 ≤ decay := by dsimp [decay,localAlpha,innerEnergy,outerEnergy]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum (u) : 0 ≤ ∑ i, F i u := Finset.sum_nonneg (fun i _ => hF i u)
  have hg (u) (hu : u ∈ D) (_ : u.2 < 2*(k*N)) :
      modularGenerator γ w (fun v => ∑ i, F i v) u ≤ -decay*(∑ i, F i u)+decay*((k : ℝ)*C) := by
    rw [modular_generator_sum]
    have hi (i) : modularGenerator γ w (F i) u ≤ -decay*F i u+decay*C := by
      have h := word_generator_affine hk N hN hNlarge z₀ z₁ γ κ σ h₀ h₁ hst₀ hst₁
        w hdiag hsym hw hrow hγ hγmax hκ hκmax b hb u hu i
      simpa only [F,decay,C,mul_comm (N : ℝ) localAlpha] using h
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    rw [Finset.sum_add_distrib,← Finset.mul_sum] at hh
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    nlinarith only [hh]
  have hA : ∀ x ∈ wordRetainedUnrecovered N (wordCenter z₀ z₁ σ) σ D,
      Real.exp ((N : ℝ)*localAlpha*innerEnergy) ≤ modularActiveObservable N D (fun u => ∑ i, F i u) x := by
    intro x hx
    cases x with
    | none => exact False.elim hx
    | some u =>
      obtain ⟨ha,i,hi⟩ := hx
      simp only [modularActiveObservable,if_pos ha]
      have he : Real.exp ((N : ℝ)*localAlpha*innerEnergy) ≤ F i u.val :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi.le (by unfold localAlpha; positivity))
      exact he.trans (Finset.single_le_sum (fun j _ => hF j u.val) (Finset.mem_univ i))
  have h := modular_retained_affine_event γ w hw hγ N D (fun u => ∑ i, F i u) hsum
    decay ((k : ℝ)*C) hd (mul_nonneg (Nat.cast_nonneg _) hC) hg q 2688 hq hclock hdecay
    (wordRetainedUnrecovered N (wordCenter z₀ z₁ σ) σ D)
    (Real.exp ((N : ℝ)*localAlpha*innerEnergy)) hA s hactive
  have hs : ∑ i, F i s.val ≤ (k : ℝ)*Real.exp (localAlpha*(N : ℝ)*(4*innerEnergy)) := by
    calc
      _ ≤ ∑ _i : Fin k, Real.exp (localAlpha*(N : ℝ)*(4*innerEnergy)) := Finset.sum_le_sum (fun i _ => by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (hbirth i) (by unfold localAlpha; positivity : 0 ≤ (N : ℝ)*localAlpha)
        nlinarith only [hh])
      _ = _ := by simp
  have hs' := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-decay*(2688 : NNReal))).le
  apply recovery_at_2688 k N _ (Nat.cast_nonneg N)
  dsimp only [decay,C] at h hs'
  norm_num only [NNReal.coe_ofNat] at h hs'
  simp only [mul_comm (N : ℝ) localAlpha] at h hs' ⊢
  nlinarith only [h,hs']

end CompositionalMemory
