import proofs.C4Assemblies.PhaseTransfer
import proofs.C4Assemblies.FinePhaseBounds
namespace C4Assemblies
noncomputable section
open Set ProductiveRecovery
variable {ι : Type*} [Fintype ι]

/-- Degree-four backward phase weight `p(a) = Σ_{k≤4} a^k e_X K''^k / k!` for the
distinct-loss comparison matrix `K'' = [[0,20,0,38],[0,5,20,0],[0,0,7,2],[0,0,20,24]]`. -/
def finePhaseWeight (a : ℝ) (c : State) : ℝ :=
  c 2 + (20*a+50*a^2+(250/3)*a^3+(625/6)*a^4)*c 3
      + (580*a^2+(14180/3)*a^3+(86585/3)*a^4)*c 4
      + (38*a+456*a^2+(12104/3)*a^3+(79714/3)*a^4)*c 5

theorem finePhaseWeight_assembly (a : ℝ) (k : ι → ι → ℝ) (r d : ι → ℝ)
    (c : Assembly ι) (i : ι) :
    finePhaseWeight a (assemblyField k r d c i) =
      finePhaseWeight a (field (r i) (d i) (c i)) +
        diffusion k (fun j => finePhaseWeight a (c j)) i := by
  simp only [finePhaseWeight,assemblyField,diffusion_add,diffusion_mul]
  ring

theorem fine_backward_phase_local (a r d : ℝ) (ha : 0 ≤ a) (c : State) (hc : Nonneg c)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : A c ≤ 11/10) (hB : B c ≤ 11/10) :
    0 ≤ 48*finePhaseWeight a c+finePhaseWeight a (field r d c)-
      ((20+100*a+250*a^2+(1250/3)*a^3)*c 3+
        (1160*a+14180*a^2+(346340/3)*a^3)*c 4+
        (38+912*a+12104*a^2+(318856/3)*a^3)*c 5) := by
  obtain ⟨h2,h3,h4,h5⟩ := fine_phase_comparison r d c hc hr hr' hd hd' hA hB
  have hw3 : 0 ≤ 20*a+50*a^2+(250/3)*a^3+(625/6)*a^4 := by positivity
  have hw4 : 0 ≤ 580*a^2+(14180/3)*a^3+(86585/3)*a^4 := by positivity
  have hw5 : 0 ≤ 38*a+456*a^2+(12104/3)*a^3+(79714/3)*a^4 := by positivity
  have key : 48*finePhaseWeight a c+finePhaseWeight a (field r d c)-
      ((20+100*a+250*a^2+(1250/3)*a^3)*c 3+
        (1160*a+14180*a^2+(346340/3)*a^3)*c 4+
        (38+912*a+12104*a^2+(318856/3)*a^3)*c 5) =
      (field r d c 2-(-48*c 2+20*c 3+38*c 5))+
      (20*a+50*a^2+(250/3)*a^3+(625/6)*a^4)*(field r d c 3-(-43*c 3+20*c 4))+
      (580*a^2+(14180/3)*a^3+(86585/3)*a^4)*(field r d c 4-(-41*c 4+2*c 5))+
      (38*a+456*a^2+(12104/3)*a^3+(79714/3)*a^4)*(field r d c 5-(-24*c 5+20*c 4))+
      ((3125/6)*a^4)*c 3+((2206625/3)*a^4)*c 4+((2086306/3)*a^4)*c 5 := by
    dsimp [finePhaseWeight]
    ring
  rw [key]
  have p2 := sub_nonneg.mpr h2
  have p3 := mul_nonneg hw3 (sub_nonneg.mpr h3)
  have p4 := mul_nonneg hw4 (sub_nonneg.mpr h4)
  have p5 := mul_nonneg hw5 (sub_nonneg.mpr h5)
  have q3 := mul_nonneg (show 0 ≤ (3125/6)*a^4 by positivity) (hc 3)
  have q4 := mul_nonneg (show 0 ≤ (2206625/3)*a^4 by positivity) (hc 4)
  have q5 := mul_nonneg (show 0 ≤ (2086306/3)*a^4 by positivity) (hc 5)
  linarith

theorem fine_backward_phase_deriv (X : ℝ → State) (V : State) (h t : ℝ)
    (hX : HasDerivAt X V t) :
    HasDerivAt (fun s => Real.exp (48*s)*finePhaseWeight (h-s) (X s))
      (Real.exp (48*t)*(48*finePhaseWeight (h-t) (X t)+finePhaseWeight (h-t) V-
        ((20+100*(h-t)+250*(h-t)^2+(1250/3)*(h-t)^3)*X t 3+
          (1160*(h-t)+14180*(h-t)^2+(346340/3)*(h-t)^3)*X t 4+
          (38+912*(h-t)+12104*(h-t)^2+(318856/3)*(h-t)^3)*X t 5))) t := by
  have hd := hasDerivAt_pi.1 hX
  have ha := (hasDerivAt_id t).const_sub h
  have hw3 := (((ha.const_mul 20).add ((ha.pow 2).const_mul 50)).add
    ((ha.pow 3).const_mul (250/3))).add ((ha.pow 4).const_mul (625/6))
  have hw4 := (((ha.pow 2).const_mul 580).add ((ha.pow 3).const_mul (14180/3))).add
    ((ha.pow 4).const_mul (86585/3))
  have hw5 := (((ha.const_mul 38).add ((ha.pow 2).const_mul 456)).add
    ((ha.pow 3).const_mul (12104/3))).add ((ha.pow 4).const_mul (79714/3))
  have hp := (((hd 2).add (hw3.mul (hd 3))).add (hw4.mul (hd 4))).add (hw5.mul (hd 5))
  convert (((hasDerivAt_id t).const_mul 48).exp).mul hp using 1
  dsimp [finePhaseWeight]
  ring

/-- The minimum of the degree-four backward phase observable propagates along the
assembly flow with the common exponential loss `48`. -/
theorem fine_phase_minimum_propagation (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j)
    (r d : ι → ℝ) (hr : ∀ i, 19 ≤ r i) (hr' : ∀ i, r i ≤ 21)
    (hd : ∀ i, 0 ≤ d i) (hd' : ∀ i, d i ≤ 1/25)
    (X : ℝ → Assembly ι) (h L : ℝ) (hh : 0 ≤ h)
    (hX : ∀ t ∈ Icc 0 h, HasDerivAt X (assemblyField k r d (X t)) t)
    (hn : ∀ t ∈ Icc 0 h, ∀ i, Nonneg (X t i))
    (hA : ∀ t ∈ Icc 0 h, ∀ i, A (X t i) ≤ 11/10)
    (hB : ∀ t ∈ Icc 0 h, ∀ i, B (X t i) ≤ 11/10)
    (h0 : ∀ i, L ≤ finePhaseWeight h (X 0 i)) :
    ∀ i, L ≤ Real.exp (48*h)*X h i 2 := by
  let W : ℝ → ι → ℝ := fun t i => Real.exp (48*t)*finePhaseWeight (h-t) (X t i)
  let V : ℝ → ι → ℝ := fun t i => Real.exp (48*t)*
    (48*finePhaseWeight (h-t) (X t i)+finePhaseWeight (h-t) (assemblyField k r d (X t) i)-
      ((20+100*(h-t)+250*(h-t)^2+(1250/3)*(h-t)^3)*X t i 3+
        (1160*(h-t)+14180*(h-t)^2+(346340/3)*(h-t)^3)*X t i 4+
        (38+912*(h-t)+12104*(h-t)^2+(318856/3)*(h-t)^3)*X t i 5))
  have hder : ∀ t ∈ Icc 0 h, ∀ i, HasDerivAt (fun s => W s i) (V t i) t := by
    intro t ht i
    exact fine_backward_phase_deriv (fun s => X s i) _ h t (hasDerivAt_pi.1 (hX t ht) i)
  have hinit : ∀ i, L ≤ W 0 i := by simpa [W] using h0
  have hv : ∀ t ∈ Ico 0 h, ∀ i, diffusion k (W t) i ≤ V t i := by
    intro t ht i
    have hh' := fine_backward_phase_local (h-t) (r i) (d i) (by linarith [ht.2])
      (X t i) (hn t (Ico_subset_Icc_self ht) i) (hr i) (hr' i) (hd i) (hd' i)
      (hA t (Ico_subset_Icc_self ht) i) (hB t (Ico_subset_Icc_self ht) i)
    dsimp [W,V]
    rw [diffusion_mul, finePhaseWeight_assembly]
    have hp := mul_nonneg (Real.exp_pos (48*t)).le hh'
    nlinarith
  have hm := diffusion_lower_bound k hk W V L h hh hder hinit hv
  simpa [W,finePhaseWeight] using hm

end
end C4Assemblies
