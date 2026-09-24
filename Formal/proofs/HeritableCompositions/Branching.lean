import proofs.HeritableCompositions.Main

namespace HeritableCompositions
open FiniteCopy

noncomputable def goodIntegral {α : Type*} [Fintype α] (μ : FiniteLaw (Option α)) (f : α → ℝ) : ℝ :=
  ∑ x, μ.mass (some x)*f x

theorem goodIntegral_const {α : Type*} [Fintype α] (μ : FiniteLaw (Option α)) (a : ℝ) :
    goodIntegral μ (fun _ => a) = (1-μ.mass none)*a := by
  have ht := μ.total
  rw [Fintype.sum_option] at ht
  unfold goodIntegral
  rw [← Finset.sum_mul]
  congr 1
  linarith only [ht]

theorem goodIntegral_mono {α : Type*} [Fintype α] (μ : FiniteLaw (Option α))
    (f g : α → ℝ) (h : ∀ x, f x ≤ g x) : goodIntegral μ f ≤ goodIntegral μ g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg (some x)))

theorem goodIntegral_nonneg {α : Type*} [Fintype α] (μ : FiniteLaw (Option α))
    (f : α → ℝ) (h : ∀ x, 0 ≤ f x) : 0 ≤ goodIntegral μ f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (μ.nonneg (some x)) (h x))

variable {α : Type*} [Fintype α]

noncomputable def familyFidelity (K : α → FiniteLaw (Option (α × α))) : ℕ → α → ℝ
  | 0, _ => 1
  | G+1, x => goodIntegral (K x) (fun p => familyFidelity K G p.1*familyFidelity K G p.2)

noncomputable def retainedMean (K : α → FiniteLaw (Option (α × α))) : ℕ → α → ℝ
  | 0, _ => 1
  | G+1, x => goodIntegral (K x) (fun p => retainedMean K G p.1+retainedMean K G p.2)

noncomputable def extinctionBy (K : α → FiniteLaw (Option (α × α))) : ℕ → α → ℝ
  | 0, _ => 0
  | G+1, x => (K x).mass none+goodIntegral (K x) (fun p => extinctionBy K G p.1*extinctionBy K G p.2)

theorem familyFidelity_nonneg (K : α → FiniteLaw (Option (α × α))) (G : ℕ) (x : α) :
    0 ≤ familyFidelity K G x := by
  induction G generalizing x with
  | zero => norm_num [familyFidelity]
  | succ G ih => exact goodIntegral_nonneg _ _ (fun p => mul_nonneg (ih p.1) (ih p.2))

theorem family_divisions_succ (G : ℕ) : 2^(G+1)-1 = 1+2*(2^G-1) := by
  have hp : 1 ≤ 2^G := Nat.one_le_pow G 2 (by norm_num)
  rw [pow_succ]
  omega

theorem family_fidelity_bound (K : α → FiniteLaw (Option (α × α))) (ε : ℝ)
    (_hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hK : ∀ x, (K x).mass none ≤ ε) (G : ℕ) (x : α) :
    (1-ε)^(2^G-1) ≤ familyFidelity K G x := by
  have hp : 0 ≤ 1-ε := sub_nonneg.mpr hε1
  induction G generalizing x with
  | zero => simp [familyFidelity]
  | succ G ih =>
    have h := goodIntegral_mono (K x) (fun _ => (1-ε)^(2^G-1)*(1-ε)^(2^G-1))
      (fun p => familyFidelity K G p.1*familyFidelity K G p.2)
      (fun p => mul_le_mul (ih p.1) (ih p.2) (pow_nonneg hp _) (familyFidelity_nonneg K G p.1))
    rw [goodIntegral_const] at h
    have hq := mul_le_mul_of_nonneg_right (sub_le_sub_left (hK x) 1)
      (mul_nonneg (pow_nonneg hp (2^G-1)) (pow_nonneg hp (2^G-1)))
    change _ ≤ goodIntegral (K x) _
    calc
      _ = (1-ε)*((1-ε)^(2^G-1)*(1-ε)^(2^G-1)) := by
        rw [family_divisions_succ,pow_add,pow_one,Nat.mul_comm 2 (2^G-1),pow_mul,pow_two]
      _ ≤ _ := hq.trans h

theorem bernoulli_failure (ε : ℝ) (_hε : 0 ≤ ε) (hε1 : ε ≤ 1) (n : ℕ) :
    1-(n : ℝ)*ε ≤ (1-ε)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hε1)
    have he : 0 ≤ (n : ℝ)*ε^2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg ε)
    rw [pow_succ]
    push_cast
    nlinarith only [h,he]

theorem whole_family_union_bound (K : α → FiniteLaw (Option (α × α))) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hK : ∀ x, (K x).mass none ≤ ε) (G : ℕ) (x : α) :
    1-((2^G-1 : ℕ) : ℝ)*ε ≤ familyFidelity K G x :=
  (bernoulli_failure ε hε hε1 _).trans (family_fidelity_bound K ε hε hε1 hK G x)

theorem retained_mean_bound (K : α → FiniteLaw (Option (α × α))) (ε : ℝ)
    (hε1 : ε ≤ 1) (hK : ∀ x, (K x).mass none ≤ ε) (G : ℕ) (x : α) :
    (2*(1-ε))^G ≤ retainedMean K G x := by
  induction G generalizing x with
  | zero => simp [retainedMean]
  | succ G ih =>
    have h := goodIntegral_mono (K x) (fun _ => (2*(1-ε))^G+(2*(1-ε))^G)
      (fun p => retainedMean K G p.1+retainedMean K G p.2) (fun p => add_le_add (ih p.1) (ih p.2))
    rw [goodIntegral_const] at h
    have hq := mul_le_mul_of_nonneg_right (sub_le_sub_left (hK x) 1)
      (by positivity : 0 ≤ (2*(1-ε))^G+(2*(1-ε))^G)
    change _ ≤ goodIntegral (K x) _
    rw [pow_succ]
    nlinarith only [h,hq]

theorem extinction_uniform_bound (K : α → FiniteLaw (Option (α × α))) (ε r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hK : ∀ x, (K x).mass none ≤ ε)
    (hfixed : ε+(1-ε)*r^2=r) (G : ℕ) (x : α) :
    0 ≤ extinctionBy K G x ∧ extinctionBy K G x ≤ r := by
  induction G generalizing x with
  | zero => simpa [extinctionBy] using hr
  | succ G ih =>
    have hl := goodIntegral_nonneg (K x) (fun p => extinctionBy K G p.1*extinctionBy K G p.2)
      (fun p => mul_nonneg (ih p.1).1 (ih p.2).1)
    have hu := goodIntegral_mono (K x) (fun p => extinctionBy K G p.1*extinctionBy K G p.2)
      (fun _ => r*r) (fun p => mul_le_mul (ih p.1).2 (ih p.2).2 (ih p.2).1 hr)
    rw [goodIntegral_const] at hu
    have hrr : 0 ≤ 1-r*r := by nlinarith only [hr,hr1]
    have he := mul_le_mul_of_nonneg_right (hK x) hrr
    change 0 ≤ (K x).mass none+_ ∧ (K x).mass none+_ ≤ r
    constructor
    · exact add_nonneg ((K x).nonneg none) hl
    · nlinarith only [hu,he,hfixed]

theorem binary_extinction_fixed_point (ε : ℝ) (hε : 0 ≤ ε) (hhalf : ε < 1/2) :
    0 ≤ ε/(1-ε) ∧ ε/(1-ε) < 1 ∧
    ε+(1-ε)*(ε/(1-ε))^2=ε/(1-ε) := by
  have hp : 0 < 1-ε := by linarith only [hhalf]
  refine ⟨div_nonneg hε hp.le,(div_lt_one hp).mpr (by linarith only [hhalf]),?_⟩
  field_simp
  ring

theorem source_family_bound {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hmax : γ ≤ 1/100000000000) (N : ℕ) (hN : copyThreshold γ ≤ N)
    (G : ℕ) (x : BirthCount C N) :
    1-((2^G-1 : ℕ) : ℝ)*(generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent)) ≤
      familyFidelity (certifiedGeneration C hγ hmax N (copyThreshold_positive γ N hN)) G x := by
  apply whole_family_union_bound _ _ (mul_nonneg (generationPrefactor_pos γ hγ).le (Real.exp_pos _).le)
    ((copyThreshold_nonvacuous γ hγ N hN).trans (by norm_num : (1/2 : ℝ) ≤ 1))
  exact certified_generation_failure C hγ hmax N (copyThreshold_positive γ N hN) (copyThreshold_large γ N hN)

end HeritableCompositions
