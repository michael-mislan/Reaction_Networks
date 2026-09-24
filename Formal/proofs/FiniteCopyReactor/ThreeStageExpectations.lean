import proofs.FiniteCopyReactor.MarkedExpectations

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical

theorem three_stage_bounds {α β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
    (P : MarkedKernel α β) (Q : MarkedKernel α γ) (R : MarkedKernel α δ)
    (t u v : NNReal) (f : α → ℝ → ℝ) (C : ℝ) (hf : ∀ x z, 0 ≤ f x z ∧ f x z ≤ C)
    (x : α) (z : ℝ) : 0 ≤ threeStage P Q R t u v f x z ∧ threeStage P Q R t u v f x z ≤ C :=
  marked_poisson_bounds P _ C
    (fun y a => marked_poisson_bounds Q _ C (fun w b => marked_poisson_bounds R f C hf v w b) u y a) t x z

theorem three_stage_mono {α β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
    (P : MarkedKernel α β) (Q : MarkedKernel α γ) (R : MarkedKernel α δ)
    (t u v : NNReal) (f g : α → ℝ → ℝ) (C D : ℝ)
    (hf : ∀ x z, 0 ≤ f x z ∧ f x z ≤ C) (hg : ∀ x z, 0 ≤ g x z ∧ g x z ≤ D)
    (h : ∀ x z, f x z ≤ g x z) (x : α) (z : ℝ) :
    threeStage P Q R t u v f x z ≤ threeStage P Q R t u v g x z := by
  have hfR (y a) := marked_poisson_bounds R f C hf v y a
  have hgR (y a) := marked_poisson_bounds R g D hg v y a
  have hR (y a) := marked_poisson_mono R f g C D hf hg h v y a
  have hfQ (y a) := marked_poisson_bounds Q _ C hfR u y a
  have hgQ (y a) := marked_poisson_bounds Q _ D hgR u y a
  have hQ (y a) := marked_poisson_mono Q _ _ C D hfR hgR hR u y a
  exact marked_poisson_mono P _ _ C D hfQ hgQ hQ t x z

theorem three_stage_add {α β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
    (P : MarkedKernel α β) (Q : MarkedKernel α γ) (R : MarkedKernel α δ)
    (t u v : NNReal) (f g : α → ℝ → ℝ) (C D : ℝ)
    (hf : ∀ x z, 0 ≤ f x z ∧ f x z ≤ C) (hg : ∀ x z, 0 ≤ g x z ∧ g x z ≤ D)
    (x : α) (z : ℝ) :
    threeStage P Q R t u v (fun y w => f y w+g y w) x z=
      threeStage P Q R t u v f x z+threeStage P Q R t u v g x z := by
  have hfR (y a) := marked_poisson_bounds R f C hf v y a
  have hgR (y a) := marked_poisson_bounds R g D hg v y a
  have hfQ (y a) := marked_poisson_bounds Q _ C hfR u y a
  have hgQ (y a) := marked_poisson_bounds Q _ D hgR u y a
  unfold threeStage
  simp_rw [marked_poisson_add R f g C D hf hg v]
  simp_rw [marked_poisson_add Q _ _ C D hfR hgR u]
  exact marked_poisson_add P _ _ C D hfQ hgQ t x z

theorem three_stage_event_union {α β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
    (P : MarkedKernel α β) (Q : MarkedKernel α γ) (R : MarkedKernel α δ)
    (t u v : NNReal) (A B : Set (α × ℝ)) (x : α) (z : ℝ) :
    threeStage P Q R t u v (MarkedKernel.eventIndicator (A ∪ B)) x z ≤
      threeStage P Q R t u v (MarkedKernel.eventIndicator A) x z+
      threeStage P Q R t u v (MarkedKernel.eventIndicator B) x z := by
  have ha (y a) : 0 ≤ MarkedKernel.eventIndicator A y a ∧ MarkedKernel.eventIndicator A y a ≤ 1 := P.event_bounds A 0 y a
  have hb (y a) : 0 ≤ MarkedKernel.eventIndicator B y a ∧ MarkedKernel.eventIndicator B y a ≤ 1 := P.event_bounds B 0 y a
  have hab (y a) : 0 ≤ MarkedKernel.eventIndicator A y a+MarkedKernel.eventIndicator B y a ∧
      MarkedKernel.eventIndicator A y a+MarkedKernel.eventIndicator B y a ≤ 2 :=
    ⟨add_nonneg (ha y a).1 (hb y a).1, by linarith [(ha y a).2,(hb y a).2]⟩
  have h (y a) : MarkedKernel.eventIndicator (A ∪ B) y a ≤
      MarkedKernel.eventIndicator A y a+MarkedKernel.eventIndicator B y a := by
    simp only [MarkedKernel.eventIndicator,Set.mem_union]
    split_ifs <;> simp_all
  have hm := three_stage_mono P Q R t u v _ _ 1 2 (fun y a => P.event_bounds _ 0 y a) hab h x z
  rw [three_stage_add P Q R t u v _ _ 1 1 ha hb] at hm
  exact hm

end
end FiniteCopyReactor
