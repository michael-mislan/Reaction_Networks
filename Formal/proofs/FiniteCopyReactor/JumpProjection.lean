import proofs.RandomViability.JumpRestartLaw
import proofs.RandomViability.JumpInitial

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability

theorem map_compProd_both {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μ : Measure A) [SFinite μ]
    (κ : Kernel A C) [IsSFiniteKernel κ] (η : Kernel B D) [IsSFiniteKernel η]
    (f : A → B) (g : C → D) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ a,(κ a).map g=η (f a)) :
    (μ ⊗ₘ κ).map (Prod.map f g)=μ.map f ⊗ₘ η := by
  have hm := hf.prodMap hg
  ext s hs
  rw [Measure.map_apply hm hs,Measure.compProd_apply (hm hs),Measure.compProd_apply hs,
    lintegral_map' (Kernel.measurable_kernel_prodMk_left hs).aemeasurable hf.aemeasurable]
  apply lintegral_congr
  intro a
  rw [← he a,Measure.map_apply hg (hs.preimage measurable_prodMk_left)]
  rfl

def projectJumpState {α γ β : Type*} (φ : α → γ) (y : JumpState α β) : JumpState γ β := (φ y.1,y.2)

def projectJumpPath {α γ β : Type*} (φ : α → γ) (z : ℕ → JumpState α β) : ℕ → JumpState γ β :=
  fun k => projectJumpState φ (z k)

def projectJumpPrefix {α γ β : Type*} (φ : α → γ) (k : ℕ) (h : Finset.Iic k → JumpState α β) :
    Finset.Iic k → JumpState γ β := fun i => projectJumpState φ (h i)

section Measurability
variable {α γ β : Type*} [MeasurableSpace α] [MeasurableSpace γ] [MeasurableSpace β]

theorem project_jump_state_measurable (φ : α → γ) (hφ : Measurable φ) :
    Measurable (projectJumpState (β := β) φ) := (hφ.comp measurable_fst).prodMk measurable_snd

theorem project_jump_path_measurable (φ : α → γ) (hφ : Measurable φ) :
    Measurable (projectJumpPath (β := β) φ) := by
  apply measurable_pi_lambda
  intro k
  exact (project_jump_state_measurable φ hφ).comp (measurable_pi_apply k)

theorem project_jump_prefix_measurable (φ : α → γ) (hφ : Measurable φ) (k : ℕ) :
    Measurable (projectJumpPrefix (β := β) φ k) := by
  apply measurable_pi_lambda
  intro i
  exact (project_jump_state_measurable φ hφ).comp (measurable_pi_apply i)

theorem project_prefix_map (φ : α → γ) (hφ : Measurable φ) (μ : Measure (ℕ → JumpState α β)) (k : ℕ) :
    (μ.map (projectJumpPath φ)).map (Preorder.frestrictLe k)=
      (μ.map (Preorder.frestrictLe k)).map (projectJumpPrefix φ k) := by
  rw [Measure.map_map (Preorder.measurable_frestrictLe k) (project_jump_path_measurable φ hφ),
    Measure.map_map (project_jump_prefix_measurable φ hφ k) (Preorder.measurable_frestrictLe k)]
  rfl
end Measurability

variable {α γ β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace γ] [Countable γ] [MeasurableSingletonClass γ]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem project_jump_kernel (φ : α → γ) (hφ : Measurable φ)
    (next : α → β → α) (next' : γ → β → γ)
    (hn : ∀ x b,φ (next x b)=next' (φ x) b)
    (rate : γ → β → ℝ) (hr : ∀ y b,0 ≤ rate y b) (ht : ∀ y,0 < ∑ b,rate y b) (x : α) :
    (jumpStateKernel next (fun x => rate (φ x)) (fun x => hr (φ x)) (fun x => ht (φ x)) x).map
      (projectJumpState φ)=jumpStateKernel next' rate hr ht (φ x) := by
  change ((jumpClockMeasure (rate (φ x)) (hr (φ x)) (ht (φ x))).map (jumpStateUpdate next x)).map
    (projectJumpState φ)=(jumpClockMeasure (rate (φ x)) (hr (φ x)) (ht (φ x))).map (jumpStateUpdate next' (φ x))
  rw [Measure.map_map (project_jump_state_measurable φ hφ) (jumpStateUpdate_measurable next x)]
  apply congrArg (fun g => (jumpClockMeasure (rate (φ x)) (hr (φ x)) (ht (φ x))).map g)
  funext y
  apply Prod.ext
  · exact hn x y.1
  · rfl

/-- Erasing auxiliary state preserves the complete physical label and waiting-time law. -/
theorem project_jump_trajectory (φ : α → γ) (hφ : Measurable φ)
    (next : α → β → α) (next' : γ → β → γ)
    (hn : ∀ x b,φ (next x b)=next' (φ x) b)
    (rate : γ → β → ℝ) (hr : ∀ y b,0 ≤ rate y b) (ht : ∀ y,0 < ∑ b,rate y b) (x : α) :
    (jumpTrajectoryLaw x next (fun x => rate (φ x)) (fun x => hr (φ x)) (fun x => ht (φ x))).map
      (projectJumpPath φ)=jumpTrajectoryLaw (φ x) next' rate hr ht := by
  let r := fun x => rate (φ x)
  let hr' := fun x => hr (φ x)
  let ht' := fun x => ht (φ x)
  let μ := jumpTrajectoryLaw x next r hr' ht'
  have hmPath := project_jump_path_measurable (β := β) φ hφ
  have hmState := project_jump_state_measurable (β := β) φ hφ
  apply trajectory_law_unique (μ.map (projectJumpPath φ)) (jumpTrajectoryLaw (φ x) next' rate hr ht)
    (jumpHistoryKernel next' rate hr ht)
  · rw [project_prefix_map φ hφ μ 0,jumpTrajectory_initial_prefix,
      Measure.map_dirac' (project_jump_prefix_measurable φ hφ 0),jumpTrajectory_initial_prefix]
    rfl
  · intro k
    have hc : μ.map (Preorder.frestrictLe k) ⊗ₘ jumpHistoryKernel next r hr' ht' k=
        μ.map (fun z => (Preorder.frestrictLe k z,z (k+1))) :=
      @Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (fun _ => JumpState α β) _ (jumpHistoryKernel next r hr' ht') _
        (Measure.dirac (x,(Sum.inl (), (0:ℝ)))) _ k
    rw [project_prefix_map φ hφ μ k]
    rw [← map_compProd_both (μ.map (Preorder.frestrictLe k)) (jumpHistoryKernel next r hr' ht' k)
      (jumpHistoryKernel next' rate hr ht k) (projectJumpPrefix φ k) (projectJumpState φ)
      (project_jump_prefix_measurable φ hφ k) hmState
      (fun h => project_jump_kernel φ hφ next next' hn rate hr ht (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)]
    rw [hc,Measure.map_map ((project_jump_prefix_measurable φ hφ k).prodMap hmState) (by fun_prop),
      Measure.map_map (by fun_prop) hmPath]
    rfl
  · intro k
    exact @Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (fun _ => JumpState γ β) _ (jumpHistoryKernel next' rate hr ht) _
      (Measure.dirac (φ x,(Sum.inl (), (0:ℝ)))) _ k

end
end FiniteCopyReactor
