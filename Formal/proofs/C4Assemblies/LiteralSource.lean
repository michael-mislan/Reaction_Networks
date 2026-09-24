import proofs.C4Assemblies.Source
import proofs.ProductiveRecovery.SourceCorrespondence

namespace C4Assemblies
noncomputable section
open scoped BigOperators
open ProductiveRecovery
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Distinct directed labels retain source, destination, and transported species. -/
abbrev TransferLabel (ι : Type*) := ι × ι × Fin 6
def transferRate (k : ι → ι → ℝ) (c : Assembly ι) (e : TransferLabel ι) : ℝ :=
  k e.1 e.2.1 * c e.1 e.2.2
def transferIncrement (e : TransferLabel ι) (i : ι) (s : Fin 6) : ℝ :=
  (if e.2.1 = i ∧ e.2.2 = s then 1 else 0) -
  (if e.1 = i ∧ e.2.2 = s then 1 else 0)

omit [Fintype ι] in
theorem transfer_species_sum (k : ι → ι → ℝ) (c : Assembly ι) (a b i : ι) (s : Fin 6) :
    (∑ l : Fin 6, transferRate k c (a,b,l)*transferIncrement (a,b,l) i s) =
      (if b=i then k a b*c a s else 0) - (if a=i then k a b*c a s else 0) := by
  simp only [transferRate,transferIncrement,mul_sub,Finset.sum_sub_distrib]
  by_cases hb : b=i <;> by_cases ha : a=i <;> simp [hb,ha]

theorem literal_transfer_drift (k : ι → ι → ℝ) (hs : ∀ i j, k i j = k j i)
    (c : Assembly ι) (i : ι) (s : Fin 6) :
    (∑ e : TransferLabel ι, transferRate k c e*transferIncrement e i s) =
      diffusion k (fun j => c j s) i := by
  simp only [Fintype.sum_prod_type,transfer_species_sum,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [diffusion]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  · simp

/-- Source-level ODE equality: C0 chemistry, feed/washout, and directed transfer. -/
theorem literal_assembly_field (k : ι → ι → ℝ) (hs : ∀ i j, k i j = k j i)
    (r d : ι → ℝ) (c : Assembly ι) (i : ι) (s : Fin 6) :
    assemblyField k r d c i s = (if s=0 ∨ s=1 then 1 else 0)-c i s +
      (∑ j : Fin 6, flux (r i) (d i) (c i) j *
        ((CommonPhysicalRealization.pairRight j (s.castLE (by decide)) : ℝ)-
          CommonPhysicalRealization.pairLeft j (s.castLE (by decide)))) +
      ∑ e : TransferLabel ι, transferRate k c e*transferIncrement e i s := by
  rw [literal_transfer_drift k hs]
  exact congrArg (fun v => v+diffusion k (fun j => c j s) i)
    (field_stoichiometry (r i) (d i) (c i) s)

/-- Pure relocation has zero increment of every location-independent molecular property. -/
theorem transfer_property_balance (w : Fin 6 → ℝ) (e : TransferLabel ι) :
    (∑ i, ∑ s : Fin 6, w s*transferIncrement e i s) = 0 := by
  rcases e with ⟨a,b,l⟩
  simp only [transferIncrement,mul_sub,Finset.sum_sub_distrib]
  simp [mul_ite,ite_and,Finset.sum_ite_irrel]

def transferExportMark (_ : TransferLabel ι) : ℝ := 0
def transferFoodMark (_ : TransferLabel ι) : ℝ := 0
def transferHandlingMark (_ : TransferLabel ι) : ℝ := 1

end
end C4Assemblies
