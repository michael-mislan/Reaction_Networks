import proofs.CompositionalMemory.FiniteJumpIdentification
import proofs.CompositionalMemory.FiniteRestriction

namespace CompositionalMemory
open Classical RandomViability FiniteCopy MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000
attribute [local irreducible] physicalSafeDeadline
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Exact finite restriction of the actual countable-source safe-history event.
No rate bound outside the safe domain is required. -/
theorem jump_finite_restriction (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (D : Finset α) [DecidableEq (RestrictedState D)] (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (q : ℝ) (hq : 0 < q)
    (hbound : ∀ s,(finiteRestrictionModel next rate hr D).total s ≤ q)
    (x : {x : α // x ∈ D}) (T : ℝ) :
    physicalSafeDeadline next rate hr ht (D : Set α) f x.val T =
      causalSafeClock ((finiteRestrictionModel next rate hr D).uniformize q hq hbound)
        Set.univ (restrictionValue D f) q T (some x) := by
  letI : MeasurableSpace (RestrictedState D) := ⊤
  letI : MeasurableSingletonClass (RestrictedState D) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let M := finiteRestrictionModel next rate hr D
  let P := M.uniformize q hq hbound
  let fR := restrictionValue D f
  let F : RestrictedState D × ℝ → ℝ≥0∞ := fun p =>
    restrictionValue D (fun z => physicalSafeDeadline next rate hr ht (D : Set α) f z p.2) p.1
  let G : RestrictedState D × ℝ → ℝ≥0∞ := fun p => causalSafeClock P Set.univ fR q p.2 p.1
  have hFm : Measurable F := by
    apply measurable_from_prod_countable_right
    intro s
    cases s with
    | none => exact measurable_const
    | some s =>
      exact (physicalSafeDeadline_measurable next rate hr ht (D : Set α) f).comp
        (measurable_const.prodMk measurable_id)
  have hFb (p : RestrictedState D × ℝ) : F p ≤ 1 := by
    rcases p with ⟨s,t⟩
    cases s with
    | none => exact zero_le
    | some s =>
      exact physicalSafeDeadline_le_one next rate hr ht (D : Set α) f hf s.val t
  have hfn (p : RestrictedState D × ℝ) (hp : p.2 < 0) : F p=0 := by
    rcases p with ⟨s,t⟩
    cases s with
    | none => rfl
    | some s =>
      exact physicalSafeDeadline_outside next rate hr ht (D : Set α) f s.val t
        (fun h => (not_le.mpr hp) h.2)
  have hfr (s : RestrictedState D) : fR s ≤ 1 := by
    cases s with
    | none => exact zero_le
    | some s =>
      exact hf s.val
  have hFe (s : RestrictedState D) (t : ℝ) : F (s,t)=causalExp q t*fR s+
      renewalConv (causalExp q) (fun u => ENNReal.ofReal q*∑ z,ENNReal.ofReal (P.prob s z)*F (z,u)) t := by
    cases s with
    | none =>
      have hz (u : ℝ) : ENNReal.ofReal q*(∑ z,ENNReal.ofReal (P.prob none z)*F (z,u))=0 := by
        dsimp only [P]
        rw [uniformize_ennreal_step M q hq hbound]
        simp [M,finiteRestrictionModel,FiniteJumpModel.total,F,restrictionValue]
      change 0=causalExp q t*0+_
      simp_rw [hz]
      simp [renewalConv]
    | some s =>
      have hqS : (∑ b,rate s.val b) ≤ q := hbound (some s)
      have hh := physicalSafeDeadline_common_clock next rate hr ht (D : Set α) f s.val s.property q hqS t
      change physicalSafeDeadline next rate hr ht (D : Set α) f s.val t=causalExp q t*f s.val+_
      rw [hh]
      congr 1
      apply congrArg (fun H => renewalConv (causalExp q) H t)
      funext u
      have hn (b : β) : F (M.next (some s) b,u)=
          physicalSafeDeadline next rate hr ht (D : Set α) f (next s.val b) u := by
        apply restriction_next_value next rate hr D
        intro z hz
        exact physicalSafeDeadline_outside next rate hr ht (D : Set α) f z u (fun h => hz h.1)
      dsimp only [P]
      rw [uniformize_ennreal_step M q hq hbound]
      simp_rw [hn]
      have htot : M.total (some s)=∑ b,rate s.val b := rfl
      rw [htot]
      exact add_comm _ _
  have hEq : F=G := finite_common_clock_unique P q hq Set.univ fR F G hFm
    (causalSafeClock_measurable P Set.univ fR q) hFb
    (fun p => causalSafeClock_le_one P Set.univ fR hfr ⟨q,hq.le⟩ p.2 p.1) hfn
    (fun p hp => causalSafeClock_negative P Set.univ fR q p.2 hp p.1)
    (fun p hp => False.elim (hp (Set.mem_univ p.1)))
    (fun p hp => False.elim (hp (Set.mem_univ p.1)))
    (fun s _ t => hFe s t)
    (fun s hs t => causalSafeClock_causal_all P Set.univ fR q hq.le t s hs)
  exact congrFun hEq (some x,T)

end
end CompositionalMemory
