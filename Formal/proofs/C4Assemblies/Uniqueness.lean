import proofs.C4Assemblies.Recovery
import proofs.ProductiveRecovery.SourceUniqueness

namespace C4Assemblies
noncomputable section
open Set ProductiveRecovery
variable {ι : Type*} [Fintype ι]

theorem assembly_actual_unique (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyAdmitted c) (X Z : ℝ → Assembly ι)
    (hX0 : X 0 = assemblyPulse p c) (hZ0 : Z 0 = assemblyPulse p c)
    (hnX : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hnZ : ∀ t, 0 ≤ t → ∀ i, Nonneg (Z t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (assemblyField P.k P.r P.d (Z t)) t) :
    ∀ t, 0 ≤ t → X t = Z t := by
  have hxcor := (assembly_material_bounds P p c hc X hX0 hX).1
  have hzcor := (assembly_material_bounds P p c hc Z hZ0 hZ).1
  have hxb : ∀ t, 0 ≤ t → ‖X t‖ ≤ 2 := by
    intro t ht
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)).2
    intro i
    exact corridor_norm _ (hnX t ht i) (hxcor t ht i).1.2 (hxcor t ht i).2.2
  have hzb : ∀ t, 0 ≤ t → ‖Z t‖ ≤ 2 := by
    intro t ht
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)).2
    intro i
    exact corridor_norm _ (hnZ t ht i) (hzcor t ht i).1.2 (hzcor t ht i).2.2
  obtain ⟨K,hK⟩ := (assemblyField_contDiff P.k P.r P.d).contDiffOn.exists_lipschitzOnWith
    (s := Metric.closedBall (0:Assembly ι) 2) (by norm_num)
    (convex_closedBall (0:Assembly ι) 2) (isCompact_closedBall (0:Assembly ι) 2)
  intro t ht
  have h := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => assemblyField P.k P.r P.d) (s := fun _ => Metric.closedBall (0:Assembly ι) 2)
    (a := 0) (b := t) (K := K) (f := X) (g := Z)
    (fun _ _ => hK)
    (fun s hs => (hX s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hX s hs.1).hasDerivWithinAt)
    (fun s hs => by simpa [Metric.mem_closedBall,dist_zero_right] using hxb s hs.1)
    (fun s hs => (hZ s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hZ s hs.1).hasDerivWithinAt)
    (fun s hs => by simpa [Metric.mem_closedBall,dist_zero_right] using hzb s hs.1)
    (hX0.trans hZ0.symm)
  exact h ⟨ht,le_rfl⟩

end
end C4Assemblies
