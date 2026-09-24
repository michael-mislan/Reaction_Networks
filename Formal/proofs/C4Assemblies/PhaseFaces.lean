import proofs.C4Assemblies.Source
import proofs.ProductiveRecovery.PhaseComparison

namespace C4Assemblies
noncomputable section
open ProductiveRecovery
variable {ι : Type*} [Fintype ι]

theorem assembly_phase_comparison (k : ι → ι → ℝ) (r d : ι → ℝ)
    (c : Assembly ι) (i : ι) (hc : Nonneg (c i))
    (hr : 19 ≤ r i) (hr' : r i ≤ 21) (hd : 0 ≤ d i) (hd' : d i ≤ 1/25)
    (hA : A (c i) ≤ 11/10) (hB : B (c i) ≤ 11/10) :
    -70*c i 2+20*c i 3+38*c i 5+diffusion k (fun j => c j 2) i ≤ assemblyField k r d c i 2 ∧
    -70*c i 3+20*c i 4+diffusion k (fun j => c j 3) i ≤ assemblyField k r d c i 3 ∧
    -70*c i 4+diffusion k (fun j => c j 4) i ≤ assemblyField k r d c i 4 ∧
    -70*c i 5+20*c i 4+diffusion k (fun j => c j 5) i ≤ assemblyField k r d c i 5 := by
  obtain ⟨h2,h3,h4,h5⟩ := phase_comparison (r i) (d i) (c i) hc hr hr' hd hd' hA hB
  dsimp [assemblyField]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end C4Assemblies
