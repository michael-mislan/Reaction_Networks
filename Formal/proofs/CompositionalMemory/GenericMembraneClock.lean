import proofs.CompositionalMemory.GenericGlobalGenerator
import proofs.HeritableCompositions.MembraneClock

namespace CompositionalMemory

noncomputable def generalMembraneObservable {k d : ℕ} (M : ℕ) (θ : ℝ)
    (s : GeneralCountState k d) : ℝ := Real.exp (θ*((s.2:ℝ)-(M:ℝ)))

theorem general_exchange_membrane_unchanged {k d : ℕ} (z : Fin d)
    (s : GeneralCountState k d) (i j : Fin k) : (generalExchangeNext z s i j).2=s.2 := by
  unfold generalExchangeNext
  split_ifs <;> rfl

theorem general_membrane_clock_generator {k d : ℕ} {ι : Type*} [Fintype ι]
    (consume produce : Fin k → ι → Fin d → ℕ) (coeff : Fin k → ι → ℝ)
    (z : Fin d) (γ θ : ℝ) (w : Fin k → Fin k → ℝ) (M : ℕ)
    (s : GeneralCountState k d) :
    reactionGenerator (generalGlobalNext consume produce z) (generalGlobalRate consume coeff z γ w)
      (generalMembraneObservable M θ) s =
      (∑ i, γ*(s.1 i z:ℝ))*generalMembraneObservable M θ s*(Real.exp θ-1) := by
  classical
  have he : Real.exp (θ*((s.2:ℝ)+1-(M:ℝ)))=
      Real.exp (θ*((s.2:ℝ)-(M:ℝ)))*Real.exp θ := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmem (i) : γ*(s.1 i z:ℝ)*
      (generalMembraneObservable M θ (generalMembraneNext z s i)-generalMembraneObservable M θ s)=
      γ*(s.1 i z:ℝ)*generalMembraneObservable M θ s*(Real.exp θ-1) := by
    by_cases hi : s.1 i z=0
    · simp [hi]
    · simp only [generalMembraneNext,hi,ite_false,generalMembraneObservable,Nat.cast_add,Nat.cast_one,he]
      ring
  simp only [reactionGenerator,generalGlobalNext,generalGlobalRate,Fintype.sum_sum_type,
    Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr]
  have hres (j : Fin k) (r : ι) : generalMembraneObservable M θ
      (generalResidentNext s j (consume j r) (produce j r))=generalMembraneObservable M θ s := rfl
  have hex (i j) : generalMembraneObservable M θ (generalExchangeNext z s i j)=generalMembraneObservable M θ s := by
    simp only [generalMembraneObservable,general_exchange_membrane_unchanged]
  simp only [hres,hex,sub_self,mul_zero,Finset.sum_const_zero,zero_add,hmem,Finset.sum_mul]

theorem general_early_clock_generator {k d : ℕ} {ι : Type*} [Fintype ι]
    (consume produce : Fin k → ι → Fin d → ℕ) (coeff : Fin k → ι → ℝ)
    (z : Fin d) (γ b : ℝ) (hγ : 0 ≤ γ) (w : Fin k → Fin k → ℝ) (M : ℕ)
    (s : GeneralCountState k d) (hrate : ∑ i, γ*(s.1 i z:ℝ) ≤ 2*b*(M:ℝ)) :
    reactionGenerator (generalGlobalNext consume produce z) (generalGlobalRate consume coeff z γ w)
      (generalMembraneObservable M (1/5)) s ≤ (12*b*(M:ℝ)/25)*generalMembraneObservable M (1/5) s := by
  rw [general_membrane_clock_generator]
  have hW : 0 ≤ generalMembraneObservable M (1/5) s := (Real.exp_pos _).le
  have hr0 : 0 ≤ ∑ i, γ*(s.1 i z:ℝ) := Finset.sum_nonneg (fun _ _ => mul_nonneg hγ (Nat.cast_nonneg _))
  have hfirst := mul_le_mul_of_nonneg_left HeritableCompositions.early_clock_increment (mul_nonneg hr0 hW)
  have hsecond := mul_le_mul_of_nonneg_right hrate
    (by positivity : 0 ≤ generalMembraneObservable M (1/5) s*(6/25))
  nlinarith only [hfirst,hsecond]

theorem general_late_clock_generator {k d : ℕ} {ι : Type*} [Fintype ι]
    (consume produce : Fin k → ι → Fin d → ℕ) (coeff : Fin k → ι → ℝ)
    (z : Fin d) (γ a : ℝ) (hγ : 0 ≤ γ) (w : Fin k → Fin k → ℝ) (M : ℕ)
    (s : GeneralCountState k d) (hrate : a*(M:ℝ) ≤ ∑ i, γ*(s.1 i z:ℝ)) :
    reactionGenerator (generalGlobalNext consume produce z) (generalGlobalRate consume coeff z γ w)
      (generalMembraneObservable M (-1/20)) s ≤
      -(19*a*(M:ℝ)/400)*generalMembraneObservable M (-1/20) s := by
  rw [general_membrane_clock_generator]
  have hW : 0 ≤ generalMembraneObservable M (-1/20) s := (Real.exp_pos _).le
  have hr0 : 0 ≤ ∑ i, γ*(s.1 i z:ℝ) := Finset.sum_nonneg (fun _ _ => mul_nonneg hγ (Nat.cast_nonneg _))
  have hfirst := mul_le_mul_of_nonneg_left HeritableCompositions.late_clock_increment (mul_nonneg hr0 hW)
  have hsecond := mul_le_mul_of_nonneg_right hrate
    (by positivity : 0 ≤ generalMembraneObservable M (-1/20) s*(19/400))
  nlinarith only [hfirst,hsecond]

end CompositionalMemory
