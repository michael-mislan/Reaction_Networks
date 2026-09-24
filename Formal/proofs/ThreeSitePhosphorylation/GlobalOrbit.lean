import proofs.ThreeSitePhosphorylation.PeriodicExtension
import proofs.ThreeSitePhosphorylation.Source

namespace ThreeSitePhosphorylation
noncomputable section

theorem globalize_closed_source (r T : ℝ) (hT : 0<T) (f : ℝ → State) (P : State → Prop)
    (he : f 0=f 1)
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt f (T • field (witnessRates r) (f t)) t)
    (hP : ∀ t ∈ Set.Icc (0:ℝ) 1, P (f t)) (hn : field (witnessRates r) (f 0) ≠ 0) :
    ∃ φ : ℝ → State, Function.Periodic φ T ∧
      (∀ s, HasDerivAt φ (field (witnessRates r) (φ s)) s) ∧
      (∀ s, P (φ s)) ∧ ∃ s, φ s ≠ φ 0 := by
  let g := periodicCurve 1 (by norm_num) f
  let φ : ℝ → State := fun s => g (s/T)
  have hgper : Function.Periodic g 1 := periodicCurve_periodic 1 (by norm_num) f
  have hg : ∀ s, HasDerivAt g (T • field (witnessRates r) (g s)) s :=
    periodicCurve_source 1 (by norm_num) (fun y => T • field (witnessRates r) y) f he hf
  have hφ : ∀ s, HasDerivAt φ (field (witnessRates r) (φ s)) s := by
    intro s
    have hh := (hg (s/T)).scomp s ((hasDerivAt_id s).div_const T)
    simpa only [id_eq,one_div,smul_smul,inv_mul_cancel₀ (ne_of_gt hT),one_smul] using hh
  have hφ0 : φ 0=f 0 := by
    change g (0/T)=f 0
    rw [zero_div]
    exact periodicCurve_eq 1 (by norm_num) f 0 (by norm_num)
  refine ⟨φ,?_,hφ,?_,?_⟩
  · intro s
    change g ((s+T)/T)=g (s/T)
    rw [add_div,div_self (ne_of_gt hT)]
    exact hgper (s/T)
  · intro s
    apply hP
    have ht := toIcoMod_mem_Ico' (show (0:ℝ)<1 by norm_num) (s/T)
    exact ⟨ht.1,ht.2.le⟩
  · by_contra h
    push Not at h
    have hc : HasDerivAt φ 0 0 := by
      have heq : φ=(fun _ => φ 0) := funext h
      rw [heq]
      exact hasDerivAt_const _ _
    have hz := (hφ 0).unique hc
    rw [hφ0] at hz
    exact hn hz

end
end ThreeSitePhosphorylation
