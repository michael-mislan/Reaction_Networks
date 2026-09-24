import proofs.HeritableCompositions.GenerationTheorem
import proofs.HeritableCompositions.ExponentialBudget

namespace HeritableCompositions
open FiniteCopy

theorem expect_failure {α : Type*} [Fintype α] (μ : FiniteLaw (Option α)) :
    μ.expect (FiniteKernel.eventIndicator {none}) = μ.mass none := by
  classical
  simp [FiniteLaw.expect,FiniteKernel.eventIndicator]

theorem option_map_failure {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw (Option α)) (g : α → β) :
    (μ.bind (fun x => FiniteLaw.pure (x.map g))).mass none = μ.mass none := by
  classical
  simp [FiniteLaw.bind,FiniteLaw.pure]

noncomputable def lineageNext {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N) :
    Option (BirthCount C N) → FiniteLaw (Option (BirthCount C N))
  | none => FiniteLaw.pure none
  | some n => (certifiedGeneration C hγ hγmax N hN n).bind (fun x => FiniteLaw.pure (x.map Prod.fst))

noncomputable def lineageKernel {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N) : FiniteKernel (Option (BirthCount C N)) := {
  prob := fun x y => (lineageNext C hγ hγmax N hN x).mass y
  nonneg := fun x y => (lineageNext C hγ hγmax N hN x).nonneg y
  row_sum := fun x => (lineageNext C hγ hγmax N hN x).total }

theorem lineage_failure_step {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (x : Option (BirthCount C N)) :
    (lineageKernel C hγ hγmax N hN).step (FiniteKernel.eventIndicator {none}) x ≤
      FiniteKernel.eventIndicator {none} x+generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent) := by
  classical
  change (lineageNext C hγ hγmax N hN x).expect (FiniteKernel.eventIndicator {none}) ≤ _
  rw [expect_failure]
  cases x with
  | none =>
    have he : 0 ≤ generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent) :=
      mul_nonneg (generationPrefactor_pos γ hγ).le (Real.exp_pos _).le
    simpa [lineageNext,FiniteLaw.pure,FiniteKernel.eventIndicator] using
      (le_add_of_nonneg_right he : (1 : ℝ) ≤ 1+generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent))
  | some n =>
    simp only [lineageNext,option_map_failure]
    simpa [FiniteKernel.eventIndicator] using certified_generation_failure C hγ hγmax N hN hlarge n

noncomputable def lineageSuccess {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N) (G : ℕ) (n : BirthCount C N) : ℝ :=
  1-(lineageKernel C hγ hγmax N hN).steps G (FiniteKernel.eventIndicator {none}) (some n)

theorem lineage_heredity_bound {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (G : ℕ) (n : BirthCount C N) :
    1-(G : ℝ)*(generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent)) ≤
      lineageSuccess C hγ hγmax N hN G n := by
  have h := (lineageKernel C hγ hγmax N hN).steps_drift_bound (FiniteKernel.eventIndicator {none})
    (generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent))
    (lineage_failure_step C hγ hγmax N hN hlarge) G (some n)
  simp only [FiniteKernel.eventIndicator,Set.mem_singleton_iff,Option.some_ne_none,if_false,zero_add] at h
  unfold lineageSuccess
  linarith only [h]

theorem lineage_copy_tradeoff {γ : ℝ} (C : GrowthCertificate γ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (N G : ℕ) (hN : copyThreshold γ ≤ N) (hG : 1 ≤ G)
    (η : ℝ) (hη : 0 < η)
    (hbudget : Real.log (generationPrefactor γ*(G : ℝ)/η)/heredityExponent ≤ N)
    (n : BirthCount C N) :
    1-η ≤ lineageSuccess C hγ hγmax N (copyThreshold_positive γ N hN) G n := by
  have h := lineage_heredity_bound C hγ hγmax N (copyThreshold_positive γ N hN)
    (copyThreshold_large γ N hN) G n
  have hb := generation_tradeoff γ hγ N G hG η hη hbudget
  linarith only [h,hb]

end HeritableCompositions
