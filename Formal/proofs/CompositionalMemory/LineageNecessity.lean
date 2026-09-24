import proofs.CompositionalMemory.GenerationNecessity
import proofs.CompositionalMemory.WordLineage

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

def lineageAlive {α : Type*} : Option α → ℝ
  | none => 0
  | some _ => 1

theorem expect_lineageAlive {α : Type*} [Fintype α] (μ : FiniteLaw (Option α)) :
    μ.expect lineageAlive = 1-μ.mass none := by
  have ht := μ.total
  rw [Fintype.sum_option] at ht
  simp only [FiniteLaw.expect,Fintype.sum_option,lineageAlive,mul_zero,mul_one,zero_add]
  linarith only [ht]

theorem word_lineage_upper {α : Type*} [Fintype α]
    (K : α → FiniteLaw (Option (α × α))) (r : ℝ) (hr : 0 ≤ r)
    (hK : ∀ n, 1-r ≤ (K n).mass none) (G : ℕ) (n : α) :
    wordLineageSuccess K G n ≤ r^G := by
  classical
  have hstep (x : Option α) : (wordLineageKernel K).step lineageAlive x ≤ r*lineageAlive x := by
    change (wordLineageNext K x).expect lineageAlive ≤ _
    rw [expect_lineageAlive]
    cases x with
    | none => simp [wordLineageNext,FiniteLaw.pure,lineageAlive]
    | some x =>
      simp only [wordLineageNext,option_map_failure,lineageAlive,mul_one]
      linarith only [hK x]
  have h := (wordLineageKernel K).steps_decay_bound lineageAlive r hr hstep G (some n)
  have he : (fun x : Option α => lineageAlive x+FiniteKernel.eventIndicator {none} x) = (fun _ => 1) := by
    funext x
    cases x <;> simp [lineageAlive,FiniteKernel.eventIndicator]
  have hs := steps_additive (wordLineageKernel K) G lineageAlive (FiniteKernel.eventIndicator {none}) (some n)
  rw [he,FiniteKernel.steps_const] at hs
  simp only [lineageAlive,mul_one] at h
  unfold wordLineageSuccess
  linarith only [h,hs]

end CompositionalMemory
