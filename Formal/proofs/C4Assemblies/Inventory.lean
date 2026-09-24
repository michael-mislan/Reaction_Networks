import proofs.C4Assemblies.GlobalFlow
import proofs.ProductiveRecovery.NetSynthesis

namespace C4Assemblies
noncomputable section
open ProductiveRecovery MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def totalInventory (c : Assembly ι) : ℝ := ∑ i, inventory (c i)
def netRate (r d : ι → ℝ) (c : Assembly ι) : ℝ :=
  ∑ i, (flux (r i) (d i) (c i) 0+flux (r i) (d i) (c i) 3-flux (r i) (d i) (c i) 5)
def assemblyNet (r d : ι → ℝ) (T : ℝ) (X : ℝ → Assembly ι) : ℝ :=
  ∫ t in (0:ℝ)..T, netRate r d (X t)

theorem assembly_inventory_drift (k : ι → ι → ℝ) (r d : ι → ℝ)
    (c : Assembly ι) (i : ι) :
    inventory (assemblyField k r d c i) =
      flux (r i) (d i) (c i) 0+flux (r i) (d i) (c i) 3-flux (r i) (d i) (c i) 5-
      inventory (c i)+diffusion k (fun j => inventory (c j)) i := by
  have h := inventory_drift (r i) (d i) (c i)
  simp only [inventory,assemblyField,diffusion_add,diffusion_mul] at *
  linarith

theorem total_inventory_drift (k : ι → ι → ℝ) (hs : ∀ i j, k i j = k j i)
    (r d : ι → ℝ) (c : Assembly ι) :
    totalInventory (assemblyField k r d c) = netRate r d c-totalInventory c := by
  simp only [totalInventory,assembly_inventory_drift,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,diffusion_sum_zero k hs,add_zero,netRate]

theorem deriv_totalInventory (X : ℝ → Assembly ι) (v : Assembly ι) (t : ℝ)
    (h : HasDerivAt X v t) :
    HasDerivAt (fun s => totalInventory (X s)) (totalInventory v) t := by
  exact HasDerivAt.fun_sum fun i _ => deriv_inventory (fun s => X s i) (v i) t (hasDerivAt_pi.1 h i)

theorem assembly_inventory_balance (k : ι → ι → ℝ) (hs : ∀ i j, k i j = k j i)
    (r d : ι → ℝ) (X : ℝ → Assembly ι) (T : ℝ) (hT : 0 ≤ T)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField k r d (X t)) t) :
    totalInventory (X T)+(∫ t in (0:ℝ)..T, totalInventory (X t)) =
      totalInventory (X 0)+assemblyNet r d T X := by
  have hc : ContinuousOn X (Icc 0 T) := fun t ht => (hX t ht.1).continuousAt.continuousWithinAt
  have hi : Continuous (@totalInventory ι _) := by unfold totalInventory inventory; fun_prop
  have hf : Continuous (netRate r d) := by unfold netRate flux; fun_prop
  have hii : IntervalIntegrable (fun t => totalInventory (X t)) volume 0 T :=
    (hi.comp_continuousOn hc).intervalIntegrable_of_Icc hT
  have hfi : IntervalIntegrable (fun t => netRate r d (X t)) volume 0 T :=
    (hf.comp_continuousOn hc).intervalIntegrable_of_Icc hT
  have hd : ∀ t ∈ uIcc (0:ℝ) T, HasDerivAt (fun s => totalInventory (X s))
      (netRate r d (X t)-totalInventory (X t)) t := by
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) T := by simpa [uIcc_of_le hT] using ht
    simpa only [total_inventory_drift k hs] using deriv_totalInventory X _ t (hX t ht'.1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hfi.sub hii)
  rw [intervalIntegral.integral_sub hfi hii] at h
  dsimp [assemblyNet]
  linarith

end
end C4Assemblies
