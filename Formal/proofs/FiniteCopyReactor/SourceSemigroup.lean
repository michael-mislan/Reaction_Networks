import proofs.FiniteCopyReactor.KilledSemigroup
import proofs.FiniteCopyReactor.KilledContinuity

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Local rate bounds suffice for deterministic-time composition of the minimal chronological law. -/
theorem chronological_endpoint_semigroup (height : α → ℕ) (next : α → β → α)
    (rate : α → β → ℝ) (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (hb : ∀ n : ℕ,∃ q : NNReal,0 < (q:ℝ) ∧ ∀ x,height x ≤ n → (∑ b,rate x b) ≤ q)
    (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (x : α) (t u : NNReal) :
    chronologicalEndpoint next rate hr ht f x (t+u)=
      chronologicalEndpoint next rate hr ht (fun y => chronologicalEndpoint next rate hr ht f y u) x t := by
  let K := fun n g y s => killedChronologicalEndpoint {z | height z ≤ n} next rate hr ht g y s
  let E := chronologicalEndpoint next rate hr ht
  have hex (g : α → ℝ≥0∞) (y : α) (s : ℝ) : (⨆ n : ℕ,K n g y s)=E g y s :=
    killed_chronological_exhaustion height next rate hr ht g y s
  have hsem (n : ℕ) : K n f x (t+u)=K n (fun y => K n f y u) x t := by
    obtain ⟨q,hq,hbound⟩ := hb n
    exact killed_chronological_semigroup _ next rate hr ht q hq hbound f hf x t u
  have hreg (n m : ℕ) (hnm : n ≤ m) (g : α → ℝ≥0∞) (y : α) (s : ℝ) :
      K n g y s ≤ K m g y s :=
    killed_chronological_mono_region _ _ (fun _ hz => hz.trans hnm) next rate hr ht g y s
  have hpay (n : ℕ) (g h : α → ℝ≥0∞) (hgh : ∀ y,g y ≤ h y) :
      K n g x t ≤ K n h x t := killed_chronological_mono_payoff _ next rate hr ht g h hgh x t
  have hle (n : ℕ) (g : α → ℝ≥0∞) (y : α) (s : ℝ) : K n g y s ≤ E g y s :=
    killed_chronological_le _ next rate hr ht g y s
  change E f x (t+u)=E (fun y => E f y u) x t
  apply le_antisymm
  · rw [← hex f x (t+u)]
    apply iSup_le
    intro n
    rw [hsem n]
    exact (hpay n _ _ (fun y => hle n f y u)).trans (hle n _ x t)
  · rw [← hex (fun y => E f y u) x t]
    apply iSup_le
    intro n
    have hi : (fun y => E f y u)=(fun y => ⨆ m : ℕ,K m f y u) := by
      funext y
      exact (hex f y u).symm
    rw [hi]
    have hc : K n (fun y => ⨆ m : ℕ,K m f y u) x t=⨆ m : ℕ,K n (fun y => K m f y u) x t :=
      killed_chronological_iSup _ next rate hr ht (fun m y => K m f y u)
        (fun a b hab y => hreg a b hab f y u) x t
    rw [hc]
    apply iSup_le
    intro m
    let k := max n m
    have h1 := hreg n k (le_max_left n m) (fun y => K m f y u) x t
    have h2 := hpay k _ _ (fun y => hreg m k (le_max_right n m) f y u)
    exact (h1.trans h2).trans ((hsem k).symm.le.trans (hle k f x (t+u)))

end
end FiniteCopyReactor
