import proofs.C4Assemblies.Transport
import proofs.ProductiveRecovery.StrongGrowth

namespace C4Assemblies
noncomputable section
open scoped BigOperators
open ProductiveRecovery

variable {ι : Type*} [Fintype ι]
abbrev Assembly (ι : Type*) := ι → State

def assemblyField (k : ι → ι → ℝ) (r d : ι → ℝ) (c : Assembly ι) : Assembly ι :=
  fun i s => field (r i) (d i) (c i) s + diffusion k (fun j => c j s) i

theorem assembly_A (k : ι → ι → ℝ) (r d : ι → ℝ) (c : Assembly ι) (i : ι) :
    A (assemblyField k r d c i) = 1 - A (c i) + diffusion k (fun j => A (c j)) i := by
  have h := material_A (r i) (d i) (c i)
  simp only [A, assemblyField, diffusion_add, diffusion_mul] at *
  linarith

theorem assembly_B (k : ι → ι → ℝ) (r d : ι → ℝ) (c : Assembly ι) (i : ι) :
    B (assemblyField k r d c i) = 1 - B (c i) + diffusion k (fun j => B (c j)) i := by
  have h := material_B (r i) (d i) (c i)
  simp only [B, assemblyField, diffusion_add, diffusion_mul] at *
  linarith

theorem assembly_Y (k : ι → ι → ℝ) (r d : ι → ℝ) (c : Assembly ι) (i : ι) :
    Y (assemblyField k r d c i) = Y (field (r i) (d i) (c i)) +
      diffusion k (fun j => Y (c j)) i := by
  simp only [Y, assemblyField, diffusion_add, diffusion_mul]
  ring

theorem assembly_guarded_growth_at_min (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (r d : ι → ℝ) (c : Assembly ι) (i : ι)
    (hc : Nonneg (c i)) (hr : 19 ≤ r i) (hr' : r i ≤ 21)
    (hd : 0 ≤ d i) (hd' : d i ≤ 1/25)
    (hA : 9/10 ≤ A (c i)) (hB : 9/10 ≤ B (c i))
    (hY : Y (c i) ≤ 1/20) (hm : ∀ j, Y (c i) ≤ Y (c j)) :
    (2/3)*Y (c i) ≤ Y (assemblyField k r d c i) := by
  rw [assembly_Y]
  have hg := strong_guarded_growth (r i) (d i) (c i) hc hr hr' hd hd' hA hB hY
  have ht := diffusion_at_min k hk (fun j => Y (c j)) i hm
  linarith

end
end C4Assemblies
