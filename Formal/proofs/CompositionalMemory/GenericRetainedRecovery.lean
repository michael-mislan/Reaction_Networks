import proofs.CompositionalMemory.GenericRetainedReactions
import proofs.CompositionalMemory.SumObservables

namespace CompositionalMemory
open FiniteCopy

/-- Recovery reward is zero after an unsafe exit or a frozen division.
The retained law itself is unchanged. -/
noncomputable def retainedActiveObservable {S : Type*} (active : S → Prop)
    (D : Finset S) (W : S → ℝ) : Option {s : S // s ∈ D} → ℝ := by
  classical
  exact retainedReactionObservable D (fun s => if active s then W s else 0) 0

theorem retained_active_generator_le {S R : Type*} [Fintype R]
    (next : S → R → S) (rate : S → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (active : S → Prop) (D : Finset S) (W : S → ℝ) (hW : ∀ s, 0 ≤ W s)
    (s : {s : S // s ∈ D}) (hs : active s.val) :
    (retainedReactionModel next rate hrate active D).generator
      (retainedActiveObservable active D W) (some s) ≤ reactionGenerator next rate W s.val := by
  classical
  let cut := fun s => if active s then W s else 0
  have hcut (x) : 0 ≤ cut x := by dsimp [cut]; split_ifs; exact hW x; rfl
  have hret := retained_reaction_generator_le next rate hrate active D cut 0
    (fun _ _ _ _ _ => hcut _) s hs
  have hactual : reactionGenerator next rate cut s.val ≤ reactionGenerator next rate W s.val := by
    unfold reactionGenerator
    apply Finset.sum_le_sum
    intro r _
    have hh : cut (next s.val r) ≤ W (next s.val r) := by
      dsimp [cut]
      split_ifs
      · exact le_rfl
      · exact hW _
    simpa only [cut,if_pos hs] using
      mul_le_mul_of_nonneg_left (sub_le_sub_right hh (W s.val)) (hrate s.val r)
  exact hret.trans hactual

/-- Joint recovery under one literal retained law. A positive event threshold
excludes both unsafe and frozen states because their recovery reward is zero. -/
theorem retained_product_recovery {S R : Type*} [Fintype R] [DecidableEq S] {k : ℕ}
    (next : S → R → S) (rate : S → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (active : S → Prop) (D : Finset S) (W : Fin k → S → ℝ)
    (a decay C w0 : ℝ) (hW : ∀ i s, 0 ≤ W i s)
    (hdecay0 : 0 ≤ decay) (hC : 0 ≤ C) (hw0 : 0 ≤ w0)
    (hgen : ∀ s ∈ D, active s → ∀ i,
      reactionGenerator next rate (W i) s ≤ -decay*W i s+decay*C)
    (q t : NNReal) (hq : 0 < (q:ℝ)) (hdecay : decay ≤ q)
    (hclock : ∀ s, (retainedReactionModel next rate hrate active D).total s ≤ q)
    (s : {s : S // s ∈ D}) (hstart : ∀ i, W i s.val ≤ w0) :
    a*((retainedReactionModel next rate hrate active D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {x | ∃ i, a ≤ retainedActiveObservable active D (W i) x}) (some s) ≤
      (k:ℝ)*(Real.exp (-decay*(t:ℝ))*w0+C) := by
  classical
  apply product_recovery_bound (retainedReactionModel next rate hrate active D)
    (fun i => retainedActiveObservable active D (W i)) q t hq hclock a decay C w0 _
    hdecay hC _ (some s) _
  · intro i x
    cases x with
    | none => exact le_rfl
    | some x =>
      change 0 ≤ if active x.val then W i x.val else 0
      split_ifs
      · exact hW i x.val
      · exact le_rfl
  · intro i x
    cases x with
    | none =>
      simpa [retainedReactionModel,retainedActiveObservable,retainedReactionObservable,
        FiniteJumpModel.generator] using mul_nonneg hdecay0 hC
    | some x =>
      by_cases hx : active x.val
      · have hh := (retained_active_generator_le next rate hrate active D (W i) (hW i) x hx).trans
          (hgen x.val x.property hx i)
        simpa only [retainedActiveObservable,retainedReactionObservable,if_pos hx] using hh
      · simpa [retainedReactionModel,retainedActiveObservable,retainedReactionObservable,
          FiniteJumpModel.generator,hx] using mul_nonneg hdecay0 hC
  · intro i
    change (if active s.val then W i s.val else 0) ≤ w0
    split_ifs
    · exact hstart i
    · exact hw0

end CompositionalMemory
