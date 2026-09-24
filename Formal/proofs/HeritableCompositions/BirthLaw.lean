import proofs.HeritableCompositions.FiniteLaw
import proofs.HeritableCompositions.GrowthCertificate

namespace HeritableCompositions
open FiniteCopy

noncomputable def birthDomain {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ) : Finset Counts := by
  classical
  exact (countBox N).filter (fun n => C.energy (fun i => concentration N n i-C.center i) ≤ 4*innerEnergy)

abbrev BirthCount {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ) := {n : Counts // n ∈ birthDomain C N}
abbrev BirthOutcome {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ) := Option (BirthCount C N × BirthCount C N)

theorem mem_birthDomain {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ) (hN : 1 ≤ N) (n : Counts) :
    n ∈ birthDomain C N ↔ C.energy (fun i => concentration N n i-C.center i) ≤ 4*innerEnergy := by
  classical
  rw [birthDomain,Finset.mem_filter]
  constructor
  · exact And.right
  · intro he
    have hb : C.energy (fun i => concentration N n i-C.center i) < 1/32000000 := by
      norm_num [innerEnergy,outerEnergy] at he ⊢
      linarith only [he]
    exact ⟨small_energy_in_countBox N hN n C.center C.center_upper C.energy C.energy_lower hb,he⟩

noncomputable def daughterLaw (n : Counts) : FiniteLaw {d : Counts // d ∈ daughterDraws n} := {
  mass := fun d => daughterWeight n d.val
  nonneg := fun d => daughterWeight_nonneg n d.val
  total := by
    rw [Finset.sum_coe_sort]
    exact daughterWeight_sum n }

noncomputable def partitionLaw {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ) (hN : 1 ≤ N)
    (n : Counts) : FiniteLaw (BirthOutcome C N) := by
  classical
  exact (daughterLaw n).bind (fun d =>
    if h : C.energy (fun i => concentration N d.val i-C.center i) < 4*innerEnergy ∧
        C.energy (fun i => concentration N (fun j => n j-d.val j) i-C.center i) < 4*innerEnergy then
      FiniteLaw.pure (some
        (⟨d.val,(mem_birthDomain C N hN d.val).mpr h.1.le⟩,
         ⟨fun j => n j-d.val j,(mem_birthDomain C N hN _).mpr h.2.le⟩))
    else FiniteLaw.pure none)

theorem partitionLaw_failure {γ : ℝ} (C : GrowthCertificate γ) (N : ℕ) (hN : 1 ≤ N)
    (n : Counts) (hparent : C.energy (fun i => concentration (2*N) n i-C.center i) ≤ 2*innerEnergy) :
    (partitionLaw C N hN n).mass none ≤ 8*Real.exp (-(N : ℝ)*(1/1000000)^2/35) := by
  classical
  have hraw := partition_failure_bound C.energy C.return_bound n N (by omega) C.center
    (parent_count_bound C.energy C.energy_lower n N (by omega) C.center C.center_upper hparent) hparent
  have heq : (partitionLaw C N hN n).mass none =
      ∑ d ∈ daughterDraws n, daughterWeight n d*
      (if ¬(C.energy (fun i => concentration N d i-C.center i) < 4*innerEnergy ∧
        C.energy (fun i => concentration N (fun j => n j-d j) i-C.center i) < 4*innerEnergy) then 1 else 0) := by
    unfold partitionLaw FiniteLaw.bind
    change (∑ d : {d : Counts // d ∈ daughterDraws n}, daughterWeight n d.val*_) = _
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs with h
    · simp [FiniteLaw.pure,h]
    · simp [FiniteLaw.pure,h]
  rw [heq]
  exact hraw

end HeritableCompositions
