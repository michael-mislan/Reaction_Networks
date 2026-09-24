import proofs.OscillatoryCores.LocalizedFlow
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Order.Floor.Ring

namespace OscillatoryCores

open Set

theorem constant_on_unit_of_hasDerivAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f 0 s) :
    ∀ s ∈ Icc (0 : ℝ) 1, f s=f 0 := by
  intro s hs
  have hb := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hf s hs).hasDerivWithinAt) (fun s _ => by simp : ∀ s ∈ Icc (0 : ℝ) 1, ‖(0 : E)‖ ≤ (0 : ℝ))
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) hs
  have hh : ‖f s-f 0‖ ≤ 0 := by simpa using hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

noncomputable def staticCoordinates (x : ShootingState) : ℝ × ℝ × ℝ := (x.1,x.2.1,x.2.2.1)

theorem unit_static_coordinates
    (g : ShootingState → ShootingState) (Φ : ℝ → ShootingState → ShootingState)
    (hΦ0 : ∀ x, Φ 0 x=x)
    (hΦ : ∀ x t, HasDerivAt (fun s => Φ s x) (g (Φ t x)) t)
    (c : ShootingState) (R : ℝ) (hge : ∀ x ∈ Metric.closedBall c R, g x=augmentedField x)
    (x : ShootingState) (hb : ∀ s ∈ Icc (0 : ℝ) 1, Φ s x ∈ Metric.closedBall c R) :
    ∀ s ∈ Icc (0 : ℝ) 1, staticCoordinates (Φ s x)=staticCoordinates x := by
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => staticCoordinates (Φ s x)) 0 s := by
    intro s hs
    have hh := (hΦ x s).fst.prodMk ((hΦ x s).snd.fst.prodMk (hΦ x s).snd.snd.fst)
    simpa only [staticCoordinates,hge _ (hb s hs),augmentedField] using hh
  simpa only [hΦ0] using constant_on_unit_of_hasDerivAt_zero _ hd

theorem full_return_of_displacement_return
    (g : ShootingState → ShootingState) (Φ : ℝ → ShootingState → ShootingState)
    (hΦ0 : ∀ x, Φ 0 x=x)
    (hΦ : ∀ x t, HasDerivAt (fun s => Φ s x) (g (Φ t x)) t)
    (c : ShootingState) (R : ℝ) (hge : ∀ x ∈ Metric.closedBall c R, g x=augmentedField x)
    (x : ShootingState) (hb : ∀ s ∈ Icc (0 : ℝ) 1, Φ s x ∈ Metric.closedBall c R)
    (hr : (Φ 1 x).2.2.2=x.2.2.2) : Φ 1 x=x := by
  have hs := unit_static_coordinates g Φ hΦ0 hΦ c R hge x hb 1 ⟨by norm_num,le_rfl⟩
  apply Prod.ext
  · exact congrArg (fun p : ℝ × ℝ × ℝ => p.1) hs
  · apply Prod.ext
    · exact congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hs
    · exact Prod.ext (congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hs) hr

theorem flow_periodic_of_return
    (Φ : ℝ → ShootingState → ShootingState)
    (hadd : ∀ s t x, Φ s (Φ t x)=Φ (t+s) x)
    (x : ShootingState) (hx : Φ 1 x=x) : Function.Periodic (fun s => Φ s x) 1 := by
  intro s
  change Φ (s+1) x=Φ s x
  rw [add_comm s 1,← hadd,hx]

theorem periodic_unit_property {E : Type*} (y : ℝ → E)
    (hp : Function.Periodic y 1) (P : E → Prop)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, P (y s)) : ∀ s, P (y s) := by
  intro s
  have he : y (Int.fract s)=y s := by
    simpa only [Int.fract,mul_one] using hp.sub_int_mul_eq ⌊s⌋ (x := s)
  rw [← he]
  exact hP (Int.fract s) ⟨Int.fract_nonneg s,(Int.fract_lt_one s).le⟩

end OscillatoryCores
