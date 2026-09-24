import proofs.DynamicSharedResource.SourceCertificate

namespace DynamicSharedResource
noncomputable section
open Set
open scoped BigOperators

def InRect (q a : State) : Prop := ∀ i, |a i| ≤ q i

theorem moving_rect (u du : ℝ → State) (a b : ℝ) (q dq : ℝ → State)
    (hd : ∀ t ∈ Icc a b, HasDerivAt u (du t) t)
    (hqd : ∀ t ∈ Icc a b, HasDerivAt q (dq t) t)
    (hface : ∀ t ∈ Ico a b, InRect (q t) (u t) → ∀ i,
      (u t i=q t i → du t i<dq t i) ∧
      (u t i= -q t i → -dq t i<du t i))
    (h0 : InRect (q a) (u a)) :
    ∀ t ∈ Icc a b, InRect (q t) (u t) := by
  let Y : ℝ → Fin 8 × Bool → ℝ := fun t i =>
    if i.2 then q t i.1-u t i.1 else q t i.1+u t i.1
  let V : ℝ → Fin 8 × Bool → ℝ := fun t i =>
    if i.2 then dq t i.1-du t i.1 else dq t i.1+du t i.1
  have hY : ∀ t ∈ Icc a b, ∀ i, HasDerivAt (fun s => Y s i) (V t i) t := by
    intro t ht ⟨i,k⟩
    cases k
    · exact (hasDerivAt_pi.mp (hqd t ht) i).add (hasDerivAt_pi.mp (hd t ht) i)
    · exact (hasDerivAt_pi.mp (hqd t ht) i).sub (hasDerivAt_pi.mp (hd t ht) i)
  have hY0 : ∀ i, 0 ≤ Y a i := by
    intro ⟨i,k⟩
    have hi := abs_le.mp (h0 i)
    cases k <;> simp only [Y,Bool.false_eq_true,↓reduceIte] <;> linarith
  have hb : ∀ t ∈ Ico a b, (∀ i, 0 ≤ Y t i) → ∀ i, Y t i=0 → 0<V t i := by
    intro t ht hall ⟨i,k⟩ hz
    have hu : InRect (q t) (u t) := by
      intro j
      have h₁ := hall (j,true)
      have h₂ := hall (j,false)
      simp only [Y,Bool.false_eq_true,↓reduceIte] at h₁ h₂
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hf := hface t ht hu i
    cases k
    · simp only [Y,Bool.false_eq_true,↓reduceIte] at hz
      have hh := hf.2 (by linarith)
      simp only [V,Bool.false_eq_true,↓reduceIte]
      linarith
    · simp only [Y,↓reduceIte] at hz
      have hh := hf.1 (by linarith)
      simp only [V,↓reduceIte]
      linarith
  have h := C4Assemblies.finite_strict_lower_barrier Y V a b hY hY0 hb
  intro t ht i
  have h₁ := h t ht (i,true)
  have h₂ := h t ht (i,false)
  simp only [Y,Bool.false_eq_true,↓reduceIte] at h₁ h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end
end DynamicSharedResource
