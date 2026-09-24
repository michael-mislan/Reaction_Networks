import proofs.DynamicSharedResource.FastRecoveryChecks
import proofs.DynamicSharedResource.Resolution

namespace DynamicSharedResource.Certificate
noncomputable section
open Set

def movingRadius (t : ℝ) : State := (1-250*t) • recoveryR+(250*t) • serviceR

theorem movingRadius_zero : movingRadius 0=recoveryR := by simp [movingRadius]
theorem movingRadius_end : movingRadius (1/250)=serviceR := by norm_num [movingRadius]

theorem movingRadius_deriv (t : ℝ) : HasDerivAt movingRadius rectVelocity t := by
  have he : rectVelocity=(250:ℝ) • (serviceR-recoveryR) := by
    funext i
    exact rect_velocity i
  have h := (((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul 250)).smul_const recoveryR).add
    (((hasDerivAt_id t).const_mul 250).smul_const serviceR)
  convert h using 1
  rw [he]
  module

theorem movingRadius_bounds (t : ℝ) (ht : t ∈ Icc 0 (1/250:ℝ)) (i : Fin 8) :
    serviceR i ≤ movingRadius t i ∧ movingRadius t i ≤ recoveryR i := by
  have h := rect_radii i
  simp only [movingRadius,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  constructor <;> nlinarith [ht.1,ht.2]

theorem movingRadius_budget (t : ℝ) (ht : t ∈ Icc 0 (1/250:ℝ)) (i : Fin 8) :
    faceBudget (movingRadius t) i < rectVelocity i := by
  rw [movingRadius,faceBudget_affine]
  have hR := recovery_face_check i
  have hS := service_face_check i
  have ht0 : 0 ≤ 250*t := by linarith [ht.1]
  have ht1 : 0 ≤ 1-250*t := by linarith [ht.2]
  have h₁ := mul_le_mul_of_nonneg_left hR.le ht1
  have h₂ := mul_le_mul_of_nonneg_left hS.le ht0
  rcases eq_or_lt_of_le ht0 with he | he
  · have hz : t=0 := by linarith
    subst t
    simpa using hR
  · have hs := mul_lt_mul_of_pos_left hS he
    nlinarith

theorem fast_modal_trajectory (a : ℝ → State)
    (hd : ∀ t, 0 ≤ t → HasDerivAt a (modalField (a t)) t)
    (h0 : InRect recoveryR (a 0)) :
    (∀ t, 0 ≤ t → InRect recoveryR (a t)) ∧
    (∀ t, 1/250 ≤ t → InRect serviceR (a t)) := by
  have outer : ∀ t, 0 ≤ t → InRect recoveryR (a t) := by
    intro t ht
    apply moving_rect a (fun s => modalField (a s)) 0 t (fun _ => recoveryR) (fun _ => 0)
      (fun s hs => hd s hs.1) (fun s _ => hasDerivAt_const s recoveryR) ?_ h0 t ⟨ht,le_rfl⟩
    intro s hs ha i
    have hf := rectangular_source_faces recoveryR (a s) (fun j => (rect_radii j).2.2) ha i
    have hb := (recovery_face_check i).trans_le (rect_velocity_nonpos i)
    constructor
    · intro hi
      exact (hf.1 hi).trans_lt hb
    · intro hi
      have hh := hf.2 hi
      change -(0:ℝ) < modalField (a s) i
      linarith
  have capture : InRect serviceR (a (1/250)) := by
    have hh := moving_rect a (fun s => modalField (a s)) 0 (1/250)
      movingRadius (fun _ => rectVelocity) (fun s hs => hd s hs.1)
      (fun s _ => movingRadius_deriv s) ?_ (by simpa only [movingRadius_zero] using h0)
      (1/250) (by constructor <;> norm_num)
    · simpa only [movingRadius_end] using hh
    · intro s hs ha i
      have hs' : s ∈ Icc 0 (1/250:ℝ) := ⟨hs.1,hs.2.le⟩
      have hf := rectangular_source_faces (movingRadius s) (a s)
        (fun j => ((movingRadius_bounds s hs' j).2).trans (rect_radii j).2.2) ha i
      have hb := movingRadius_budget s hs' i
      constructor
      · intro hi
        exact (hf.1 hi).trans_lt hb
      · intro hi
        have hh := hf.2 hi
        linarith
  refine ⟨outer,?_⟩
  intro t ht
  apply moving_rect a (fun s => modalField (a s)) (1/250) t
    (fun _ => serviceR) (fun _ => 0)
    (fun s hs => hd s (by linarith [hs.1])) (fun s _ => hasDerivAt_const s serviceR)
    ?_ capture t ⟨ht,le_rfl⟩
  intro s hs ha i
  have hf := rectangular_source_faces serviceR (a s)
    (fun j => (rect_radii j).2.1.trans (rect_radii j).2.2) ha i
  have hb := (service_face_check i).trans_le (rect_velocity_nonpos i)
  constructor
  · intro hi
    exact (hf.1 hi).trans_lt hb
  · intro hi
    have hh := hf.2 hi
    change -(0:ℝ) < modalField (a s) i
    linarith

theorem fast_source_solution (u₀ : State) (h₀ : InRect recoveryR (coordinates u₀)) :
    ∃ u : ℝ → State, u 0=u₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t ∧
        Physical (u t) ∧ InRect recoveryR (coordinates (u t))) ∧
      ∀ t, 1/250 ≤ t → InRect serviceR (coordinates (u t)) := by
  obtain ⟨a,ha0,ha,_⟩ := exists_captured_solution modalField modal_smooth nominal_face_decay
    (coordinates u₀) (fun i => (h₀ i).trans (rect_radii i).2.2)
  have hr := fast_modal_trajectory a (fun t ht => (ha t ht).1) (by simpa only [ha0] using h₀)
  let u := fun t => reconstruct (a t)
  refine ⟨u,by simp only [u,ha0,reconstruct_coordinates],?_,?_⟩
  · intro t ht
    have hd := mulVec_hasDerivAt basis a (modalField (a t)) t (ha t ht).1
    have he : basis.mulVec (modalField (a t))=nominal (u t) := by
      simp only [modalField,Matrix.mulVec_mulVec,basis_inverse,Matrix.one_mulVec,u]
    rw [he] at hd
    refine ⟨hd.const_add center,outer_physical (a t) (ha t ht).2,?_⟩
    simpa only [u,coordinates_reconstruct] using hr.1 t ht
  · intro t ht
    simpa only [u,coordinates_reconstruct] using hr.2 t ht

end
end DynamicSharedResource.Certificate
