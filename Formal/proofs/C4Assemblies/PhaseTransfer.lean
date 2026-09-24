import proofs.C4Assemblies.Bounds
import proofs.C4Assemblies.Source
import proofs.ProductiveRecovery.PhaseComparison

namespace C4Assemblies
noncomputable section
open Set ProductiveRecovery
variable {ι : Type*} [Fintype ι]

def phaseWeight (a : ℝ) (c : State) : ℝ :=
  c 2+20*a*c 3+580*a^2*c 4+38*a*c 5

theorem phaseWeight_assembly (a : ℝ) (k : ι → ι → ℝ) (r d : ι → ℝ)
    (c : Assembly ι) (i : ι) :
    phaseWeight a (assemblyField k r d c i) =
      phaseWeight a (field (r i) (d i) (c i)) +
        diffusion k (fun j => phaseWeight a (c j)) i := by
  simp only [phaseWeight,assemblyField,diffusion_add,diffusion_mul]
  ring

theorem backward_phase_local (a r d : ℝ) (ha : 0 ≤ a) (c : State) (hc : Nonneg c)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : A c ≤ 11/10) (hB : B c ≤ 11/10) :
    0 ≤ 70*phaseWeight a c+phaseWeight a (field r d c)-20*c 3-1160*a*c 4-38*c 5 := by
  obtain ⟨hx,hc1,hc2,hz⟩ := phase_comparison r d c hc hr hr' hd hd' hA hB
  have h1 := mul_le_mul_of_nonneg_left hc1 (show 0 ≤ 20*a by positivity)
  have h2 := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ 580*a^2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left hz (show 0 ≤ 38*a by positivity)
  dsimp [phaseWeight]
  nlinarith

theorem backward_phase_deriv (X : ℝ → State) (V : State) (h t : ℝ)
    (hX : HasDerivAt X V t) :
    HasDerivAt (fun s => Real.exp (70*s)*phaseWeight (h-s) (X s))
      (Real.exp (70*t)*(70*phaseWeight (h-t) (X t)+phaseWeight (h-t) V-
        20*X t 3-1160*(h-t)*X t 4-38*X t 5)) t := by
  have hd := hasDerivAt_pi.1 hX
  have ha := (hasDerivAt_id t).const_sub h
  have hp := (((hd 2).add ((ha.const_mul 20).mul (hd 3))).add
    (((ha.pow 2).const_mul 580).mul (hd 4))).add ((ha.const_mul 38).mul (hd 5))
  convert (((hasDerivAt_id t).const_mul 70).exp).mul hp using 1
  dsimp [phaseWeight]
  ring

/-- The minimum of a backward phase observable replaces a spatial semigroup construction. -/
theorem phase_minimum_propagation (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j)
    (r d : ι → ℝ) (hr : ∀ i, 19 ≤ r i) (hr' : ∀ i, r i ≤ 21)
    (hd : ∀ i, 0 ≤ d i) (hd' : ∀ i, d i ≤ 1/25)
    (X : ℝ → Assembly ι) (h L : ℝ) (hh : 0 ≤ h)
    (hX : ∀ t ∈ Icc 0 h, HasDerivAt X (assemblyField k r d (X t)) t)
    (hn : ∀ t ∈ Icc 0 h, ∀ i, Nonneg (X t i))
    (hA : ∀ t ∈ Icc 0 h, ∀ i, A (X t i) ≤ 11/10)
    (hB : ∀ t ∈ Icc 0 h, ∀ i, B (X t i) ≤ 11/10)
    (h0 : ∀ i, L ≤ phaseWeight h (X 0 i)) :
    ∀ i, L ≤ Real.exp (70*h)*X h i 2 := by
  let W : ℝ → ι → ℝ := fun t i => Real.exp (70*t)*phaseWeight (h-t) (X t i)
  let V : ℝ → ι → ℝ := fun t i => Real.exp (70*t)*
    (70*phaseWeight (h-t) (X t i)+phaseWeight (h-t) (assemblyField k r d (X t) i)-
      20*X t i 3-1160*(h-t)*X t i 4-38*X t i 5)
  have hder : ∀ t ∈ Icc 0 h, ∀ i, HasDerivAt (fun s => W s i) (V t i) t := by
    intro t ht i
    exact backward_phase_deriv (fun s => X s i) _ h t (hasDerivAt_pi.1 (hX t ht) i)
  have hinit : ∀ i, L ≤ W 0 i := by simpa [W] using h0
  have hv : ∀ t ∈ Ico 0 h, ∀ i, diffusion k (W t) i ≤ V t i := by
    intro t ht i
    have hh' := backward_phase_local (h-t) (r i) (d i) (by linarith [ht.2])
      (X t i) (hn t (Ico_subset_Icc_self ht) i) (hr i) (hr' i) (hd i) (hd' i)
      (hA t (Ico_subset_Icc_self ht) i) (hB t (Ico_subset_Icc_self ht) i)
    dsimp [W,V]
    rw [diffusion_mul, phaseWeight_assembly]
    have hp := mul_nonneg (Real.exp_pos (70*t)).le hh'
    nlinarith
  have hm := diffusion_lower_bound k hk W V L h hh hder hinit hv
  simpa [W,phaseWeight] using hm

end
end C4Assemblies
