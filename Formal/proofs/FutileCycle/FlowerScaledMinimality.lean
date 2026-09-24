import proofs.FutileCycle.FlowerSpectrum
import proofs.FutileCycle.PrincipalExtension

namespace FutileCycle
open Matrix

theorem resolvent_re (z : ℂ) (d : ℝ) (hz : 0 < z.re) (hd : 0 < d) :
    1 < (1+z/(d:ℂ)).re := by
  simp only [Complex.add_re, Complex.one_re, Complex.div_ofReal_re]
  linarith [div_pos hz hd]

theorem resolvent_mul (z w : ℂ) (d : ℝ) (hd : 0 < d) :
    (1+z/(d:ℂ))*((d:ℂ)*w) = (d:ℂ)*w+z*w := by
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  field_simp

theorem flower_scaled_no_rhp (k : ℕ) (p : FlowerIndex k → Prop) [DecidablePred p]
    (hp : ∃ i, ¬p i) (d : FlowerIndex k → ℝ) (hd : ∀ i, 0 < d i)
    (z : ℂ) (hz : 0 < z.re) (w : FlowerIndex k → ℂ)
    (he : padded (fun i j => flowerComplex k i j * (d j:ℂ)) p *ᵥ w = z • w) :
    w = 0 := by
  classical
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hwzero (i) (hi : ¬p i) : w i=0 := by
    have hh := congrFun he i
    simp [padded, Matrix.mulVec, dotProduct, hi] at hh
    exact hh.resolve_left hz0
  let u : FlowerIndex k → ℂ := fun i => (d i:ℂ)*w i
  have hrows (i) (hi : p i) : (flowerComplex k *ᵥ u) i = z*w i := by
    have hh := congrFun he i
    have heq : (padded (fun i j => flowerComplex k i j * (d j:ℂ)) p *ᵥ w) i =
        (flowerComplex k *ᵥ u) i := by
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : p j
      · simp [padded, hi, hj, u, mul_assoc]
      · simp [padded, hi, hj, u, hwzero j hj]
    rw [heq] at hh
    exact hh
  have hproper : (∃ i : Fin (k+1), ¬p (.inl i)) ∨ ¬p (.inr ()) := by
    obtain ⟨i,hi⟩ := hp
    cases i with
    | inl i => exact Or.inl ⟨i,hi⟩
    | inr i => cases i; exact Or.inr hi
  obtain ⟨hu,hv⟩ := flower_restriction_zero k (fun i => u (.inl i)) (u (.inr ()))
    (fun i => p (.inl i)) (p (.inr ()))
    (fun i => 1+z/(d (.inl i):ℂ)) (1+z/(d (.inr ()):ℂ))
    (fun i => resolvent_re z _ hz (hd _)) (resolvent_re z _ hz (hd _))
    (fun i hi => by simp [u,hwzero _ hi])
    (fun hi => by simp [u,hwzero _ hi])
    (by
      intro i hi
      have hh := hrows (.inl i.succ) hi
      rw [flower_step] at hh
      change (1+z/(d (.inl i.succ):ℂ))*((d (.inl i.succ):ℂ)*w (.inl i.succ)) = _
      rw [resolvent_mul z _ _ (hd _)]
      change u (.inl i.succ) + z*w (.inl i.succ) = _
      linear_combination -hh)
    (by
      intro hi
      have hh := hrows (.inr ()) hi
      rw [flower_leaf] at hh
      change (1+z/(d (.inr ()):ℂ))*((d (.inr ()):ℂ)*w (.inr ())) = _
      rw [resolvent_mul z _ _ (hd _)]
      change u (.inr ()) + z*w (.inr ()) = _
      linear_combination -hh)
    (by
      intro hi
      have hh := hrows (.inl 0) hi
      rw [flower_hub] at hh
      change (1+z/(d (.inl 0):ℂ))*((d (.inl 0):ℂ)*w (.inl 0)) = _
      rw [resolvent_mul z _ _ (hd _)]
      change u (.inl 0) + z*w (.inl 0) = _
      linear_combination -hh)
    hproper
  funext i
  have hui : u i=0 := by cases i with
    | inl i => exact hu i
    | inr i => cases i; exact hv
  have hd' : (d i:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hd i)
  exact (mul_eq_zero.mp hui).resolve_left hd'

end FutileCycle
