import proofs.CompositionalMemory.FiniteJumpIdentification

namespace CompositionalMemory
open Classical RandomViability FiniteCopy MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000
attribute [local irreducible] physicalSafeDeadline

variable {α σ β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype σ] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def encodedFiniteModel (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (embed : σ → α) (clip : α → Option σ) :
    FiniteJumpModel (Option σ) β where
  next s b := match s with | none => none | some s => clip (next (embed s) b)
  rate s b := match s with | none => 0 | some s => rate (embed s) b
  nonneg s b := by cases s with | none => exact le_rfl | some s => exact hr _ b

def encodedValue (embed : σ → α) (f : α → ℝ≥0∞) : Option σ → ℝ≥0∞
  | none => 0
  | some s => f (embed s)

/-- A finite encoding preserves the actual countable-source safe-history law.
Only rates at encoded states need a common bound. -/
theorem encoded_source_identification (next : α → β → α) (rate : α → β → ℝ)
    [DecidableEq (Option σ)]
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (embed : σ → α) (clip : α → Option σ)
    (hleft : ∀ s, clip (embed s)=some s)
    (hright : ∀ x s, clip x=some s → embed s=x)
    (f : α → ℝ≥0∞) (hf : ∀ x, f x ≤ 1)
    (q : ℝ) (hq : 0 < q)
    (hbound : ∀ s, (encodedFiniteModel next rate hr embed clip).total s ≤ q)
    (s : σ) (T : ℝ) :
    physicalSafeDeadline next rate hr ht {x | clip x≠none} f (embed s) T =
      causalSafeClock ((encodedFiniteModel next rate hr embed clip).uniformize q hq hbound)
        Set.univ (encodedValue embed f) q T (some s) := by
  letI : MeasurableSpace (Option σ) := ⊤
  letI : MeasurableSingletonClass (Option σ) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let D : Set α := {x | clip x≠none}
  let M := encodedFiniteModel next rate hr embed clip
  let P := M.uniformize q hq hbound
  let fR := encodedValue embed f
  let F : Option σ × ℝ → ℝ≥0∞ := fun p =>
    encodedValue embed (fun z => physicalSafeDeadline next rate hr ht D f z p.2) p.1
  let G : Option σ × ℝ → ℝ≥0∞ := fun p => causalSafeClock P Set.univ fR q p.2 p.1
  have hFm : Measurable F := by
    apply measurable_from_prod_countable_right
    intro z
    cases z with
    | none => exact measurable_const
    | some z =>
      exact (physicalSafeDeadline_measurable next rate hr ht D f).comp
        (measurable_const.prodMk measurable_id)
  have hFb (p : Option σ × ℝ) : F p ≤ 1 := by
    rcases p with ⟨z,t⟩
    cases z with
    | none => exact zero_le
    | some z => exact physicalSafeDeadline_le_one next rate hr ht D f hf (embed z) t
  have hfn (p : Option σ × ℝ) (hp : p.2 < 0) : F p=0 := by
    rcases p with ⟨z,t⟩
    cases z with
    | none => rfl
    | some z =>
      exact physicalSafeDeadline_outside next rate hr ht D f (embed z) t
        (fun h => (not_le.mpr hp) h.2)
  have hfr (z : Option σ) : fR z ≤ 1 := by
    cases z with | none => exact zero_le | some z => exact hf (embed z)
  have hclip (x : α) (t : ℝ) : F (clip x,t)=physicalSafeDeadline next rate hr ht D f x t := by
    cases hh : clip x with
    | none =>
      have ho := physicalSafeDeadline_outside next rate hr ht D f x t (fun h => h.1 hh)
      simpa [F,encodedValue] using ho.symm
    | some z =>
      simp only [F,encodedValue,hright x z hh]
  have hFe (z : Option σ) (t : ℝ) : F (z,t)=causalExp q t*fR z+
      renewalConv (causalExp q) (fun u => ENNReal.ofReal q*∑ w,ENNReal.ofReal (P.prob z w)*F (w,u)) t := by
    cases z with
    | none =>
      have hz (u : ℝ) : ENNReal.ofReal q*(∑ w,ENNReal.ofReal (P.prob none w)*F (w,u))=0 := by
        dsimp only [P]
        rw [uniformize_ennreal_step M q hq hbound]
        simp [M,encodedFiniteModel,FiniteJumpModel.total,F,encodedValue]
      change 0=causalExp q t*0+_
      simp_rw [hz]
      simp [renewalConv]
    | some z =>
      have hz : embed z ∈ D := by simp [D,hleft]
      have hh := physicalSafeDeadline_common_clock next rate hr ht D f (embed z) hz q
        (hbound (some z)) t
      change physicalSafeDeadline next rate hr ht D f (embed z) t=causalExp q t*f (embed z)+_
      rw [hh]
      congr 1
      apply congrArg (fun H => renewalConv (causalExp q) H t)
      funext u
      dsimp only [P]
      rw [uniformize_ennreal_step M q hq hbound]
      have hn (b : β) : F (M.next (some z) b,u)=
          physicalSafeDeadline next rate hr ht D f (next (embed z) b) u := hclip _ u
      simp_rw [hn]
      exact add_comm _ _
  have hEq : F=G := finite_common_clock_unique P q hq Set.univ fR F G hFm
    (causalSafeClock_measurable P Set.univ fR q) hFb
    (fun p => causalSafeClock_le_one P Set.univ fR hfr ⟨q,hq.le⟩ p.2 p.1) hfn
    (fun p hp => causalSafeClock_negative P Set.univ fR q p.2 hp p.1)
    (fun p hp => False.elim (hp (Set.mem_univ p.1)))
    (fun p hp => False.elim (hp (Set.mem_univ p.1)))
    (fun z _ t => hFe z t)
    (fun z hz t => causalSafeClock_causal_all P Set.univ fR q hq.le t z hz)
  exact congrFun hEq (some s,T)

end
end CompositionalMemory
