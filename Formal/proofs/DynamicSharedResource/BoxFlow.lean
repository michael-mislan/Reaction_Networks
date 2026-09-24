import proofs.DynamicSharedResource.Model
import proofs.C4Assemblies.Comparison
import proofs.CoreCouplingCAC.GlobalExistence

namespace DynamicSharedResource
noncomputable section
open Set

def InCube (q : ℝ) (a : State) : Prop := ∀ i, |a i| ≤ q

def FaceDecay (f : State → State) : Prop :=
  ∀ q, (1/2:ℝ) ≤ q → q ≤ 1 → ∀ a, InCube q a → ∀ i,
    (a i = q → f a i < -q/2000) ∧ (a i = -q → q/2000 < f a i)

/-- Simultaneous moving faces. Only the literal local face inequality is used. -/
theorem moving_cube (f : State → State) (hf : FaceDecay f)
    (u du : ℝ → State) (a b : ℝ) (q dq : ℝ → ℝ)
    (hd : ∀ t ∈ Icc a b, HasDerivAt u (du t) t)
    (hfield : ∀ t ∈ Ico a b, InCube (q t) (u t) → du t = f (u t))
    (hq : ∀ t ∈ Icc a b, (1/2:ℝ) ≤ q t ∧ q t ≤ 1)
    (hqd : ∀ t ∈ Icc a b, HasDerivAt q (dq t) t)
    (hspeed : ∀ t ∈ Ico a b, -(q t)/2000 ≤ dq t)
    (h0 : InCube (q a) (u a)) :
    ∀ t ∈ Icc a b, InCube (q t) (u t) := by
  let Y : ℝ → Fin 8 × Bool → ℝ := fun t i => if i.2 then q t-u t i.1 else q t+u t i.1
  let V : ℝ → Fin 8 × Bool → ℝ := fun t i => if i.2 then dq t-du t i.1 else dq t+du t i.1
  have hY : ∀ t ∈ Icc a b, ∀ i, HasDerivAt (fun s => Y s i) (V t i) t := by
    intro t ht ⟨i,k⟩
    cases k
    · exact (hqd t ht).add (hasDerivAt_pi.1 (hd t ht) i)
    · exact (hqd t ht).sub (hasDerivAt_pi.1 (hd t ht) i)
  have hY0 : ∀ i, 0 ≤ Y a i := by
    intro ⟨i,k⟩
    have hi := abs_le.mp (h0 i)
    cases k <;> simp only [Y,Bool.false_eq_true,↓reduceIte] <;> linarith
  have hb : ∀ t ∈ Ico a b, (∀ i, 0 ≤ Y t i) → ∀ i, Y t i=0 → 0<V t i := by
    intro t ht hall ⟨i,k⟩ hz
    have hu : InCube (q t) (u t) := by
      intro j
      have h₁ := hall (j,true)
      have h₂ := hall (j,false)
      simp only [Y,Bool.false_eq_true,↓reduceIte] at h₁ h₂
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have he := hfield t ht hu
    have hqt := hq t ⟨ht.1,ht.2.le⟩
    have hface := hf (q t) hqt.1 hqt.2 (u t) hu i
    have hsp := hspeed t ht
    cases k
    · simp only [Y,Bool.false_eq_true,↓reduceIte] at hz
      have hh := hface.2 (by linarith)
      simp only [V,Bool.false_eq_true,↓reduceIte,he]
      linarith
    · simp only [Y,↓reduceIte] at hz
      have hh := hface.1 (by linarith)
      simp only [V,↓reduceIte,he]
      linarith
  have h := C4Assemblies.finite_strict_lower_barrier Y V a b hY hY0 hb
  intro t ht i
  have h₁ := h t ht (i,true)
  have h₂ := h t ht (i,false)
  simp only [Y,Bool.false_eq_true,↓reduceIte] at h₁ h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem cube_capture (f ext : State → State) (hf : FaceDecay f)
    (hext : ∀ a, InCube 1 a → ext a=f a)
    (u : ℝ → State) (hd : ∀ t, HasDerivAt u (ext (u t)) t)
    (h0 : InCube 1 (u 0)) :
    (∀ t, 0 ≤ t → InCube 1 (u t)) ∧
    (∀ t, 2000 ≤ t → InCube (1/2) (u t)) ∧
    (∀ t, 0 ≤ t → HasDerivAt u (f (u t)) t) := by
  have outer : ∀ t, 0 ≤ t → InCube 1 (u t) := by
    intro t ht
    apply moving_cube f hf u (fun s => ext (u s)) 0 t (fun _ => 1) (fun _ => 0)
      (fun s _ => hd s) (fun s _ hs => hext (u s) hs)
      (by intro s hs; norm_num) (fun s _ => hasDerivAt_const s 1)
      (by intro s hs; norm_num) h0 t ⟨ht,le_rfl⟩
  have capture : InCube (1/2) (u 2000) := by
    have h := moving_cube f hf u (fun s => ext (u s)) 0 2000
      (fun t => 1-t/4000) (fun _ => -(1/4000))
      (fun s _ => hd s)
      (fun s hs _ => hext (u s) (outer s hs.1))
      (by intro s hs; constructor <;> linarith [hs.1,hs.2])
      (fun s _ => by simpa only [zero_sub] using
        (hasDerivAt_const s 1).sub ((hasDerivAt_id s).div_const 4000))
      (by intro s hs; linarith [hs.2]) (by simpa using h0) 2000
      (by constructor <;> norm_num)
    norm_num at h
    exact h
  have inner : ∀ t, 2000 ≤ t → InCube (1/2) (u t) := by
    intro t ht
    exact moving_cube f hf u (fun s => ext (u s)) 2000 t (fun _ => 1/2) (fun _ => 0)
      (fun s _ => hd s) (fun s hs _ => hext (u s) (outer s (by linarith [hs.1])))
      (by intro s hs; norm_num) (fun s _ => hasDerivAt_const s (1/2))
      (by intro s hs; norm_num) capture t ⟨ht,le_rfl⟩
  exact ⟨outer,inner,fun t ht => by rw [← hext (u t) (outer t ht)]; exact hd t⟩

end
end DynamicSharedResource
