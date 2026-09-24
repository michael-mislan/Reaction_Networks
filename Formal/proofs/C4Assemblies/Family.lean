import proofs.C4Assemblies.Source
import proofs.ProductiveRecovery.StrongReturn

namespace C4Assemblies
noncomputable section
open ProductiveRecovery

structure Parameters (ι : Type*) where
  k : ι → ι → ℝ
  r : ι → ℝ
  d : ι → ℝ
  exchange_nonneg : ∀ i j, 0 ≤ k i j
  exchange_symmetric : ∀ i j, k i j = k j i
  exchange_diagonal : ∀ i, k i i = 0
  r_lower : ∀ i, 19 ≤ r i
  r_upper : ∀ i, r i ≤ 21
  d_lower : ∀ i, 1/50 ≤ d i
  d_upper : ∀ i, d i ≤ 1/25

variable {ι : Type*} [Fintype ι]
def AssemblyAdmitted (c : Assembly ι) : Prop := ∀ i, Admitted (c i)
def AssemblyReady (c : Assembly ι) : Prop := ∀ i, StrongReturned (c i)
def assemblyPulse (p : ι → Intervention) (c : Assembly ι) : Assembly ι := fun i => pulse (p i) (c i)

end
end C4Assemblies
