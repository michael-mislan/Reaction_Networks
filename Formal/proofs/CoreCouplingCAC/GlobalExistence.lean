import Mathlib

namespace CoreCouplingCAC

/-- A bounded globally Lipschitz autonomous vector field on a Banach space
has a global classical solution. Picard supplies arbitrary finite intervals;
ODE uniqueness glues them. This will be applied to a smooth cutoff that
equals the literal source throughout the invariant neighborhoods. -/
theorem bounded_lipschitz_global_solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (K L : NNReal) (hK : LipschitzWith K f)
    (hL : ∀ x, ‖f x‖ ≤ L) (x₀ : E) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ ∀ t, HasDerivAt x (f (x t)) t := by
  classical
  have hlocal : ∀ a : ℝ, ∃ x : ℝ → E, x 0 = x₀ ∧
      ∀ t ∈ Set.Ioo (-(|a|+1)) (|a|+1), HasDerivAt x (f (x t)) t := by
    intro a
    have hp : 0 < |a|+1 := by positivity
    let t₀ : Set.Icc (-(|a|+1)) (|a|+1) := ⟨0,by constructor <;> linarith⟩
    have hpic : IsPicardLindelof (fun _ => f) t₀ x₀
        (L*⟨|a|+1,hp.le⟩) 0 L K := by
      constructor
      · intro t ht
        exact hK.lipschitzOnWith
      · intro x hx
        exact continuousOn_const
      · intro t ht x hx
        exact hL x
      · simp [t₀]
        exact le_rfl
    obtain ⟨x,hx,hxd⟩ := hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨x,hx,?_⟩
    intro t ht
    exact (hxd t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  choose γ hγ hγd using hlocal
  have agree : ∀ a b t : ℝ,
      t ∈ Set.Ioo (-(|a|+1)) (|a|+1) →
      t ∈ Set.Ioo (-(|b|+1)) (|b|+1) → γ a t = γ b t := by
    intro a b t hta htb
    let r := min (|a|+1) (|b|+1)
    have hr : 0 < r := lt_min (by positivity) (by positivity)
    have hs₁ : Set.Ioo (-r) r ⊆ Set.Ioo (-(|a|+1)) (|a|+1) := by
      intro s hs
      have hh : r ≤ |a|+1 := min_le_left _ _
      exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have hs₂ : Set.Ioo (-r) r ⊆ Set.Ioo (-(|b|+1)) (|b|+1) := by
      intro s hs
      have hh : r ≤ |b|+1 := min_le_right _ _
      exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have hh : Set.EqOn (γ a) (γ b) (Set.Ioo (-r) r) :=
      ODE_solution_unique_of_mem_Ioo (v := fun _ => f) (s := fun _ => Set.univ)
        (fun _ _ => hK.lipschitzOnWith) (by constructor <;> linarith)
        (fun s hs => ⟨hγd a s (hs₁ hs),Set.mem_univ _⟩)
        (fun s hs => ⟨hγd b s (hs₂ hs),Set.mem_univ _⟩)
        ((hγ a).trans (hγ b).symm)
    apply hh
    change -min (|a|+1) (|b|+1) < t ∧ t < min (|a|+1) (|b|+1)
    constructor
    · have hh : -t < min (|a|+1) (|b|+1) :=
        lt_min (by linarith [hta.1]) (by linarith [htb.1])
      linarith
    · exact lt_min hta.2 htb.2
  let x : ℝ → E := fun t => γ (|t|+1) t
  refine ⟨x,hγ (|0|+1),?_⟩
  intro t
  have ht : t ∈ Set.Ioo (-(|(|t|+1)|+1)) (|(|t|+1)|+1) := by
    rw [abs_of_pos (by positivity : 0 < |t|+1)]
    constructor <;> linarith [neg_abs_le t,le_abs_self t]
  have heq : x =ᶠ[nhds t] γ (|t|+1) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    apply agree (|s|+1) (|t|+1) s _ hs
    rw [abs_of_pos (by positivity : 0 < |s|+1)]
    constructor <;> linarith [neg_abs_le s,le_abs_self s]
  have hd := hγd (|t|+1) t ht
  rw [← heq.eq_of_nhds] at hd
  exact heq.hasDerivAt_iff.mpr hd

end CoreCouplingCAC
