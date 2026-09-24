import proofs.ThermoCoreCompatibility.BeyondJunction.OrderClosure
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ThermoCoreCompatibility.GeneralCompatibility

open MultiInterface
open scoped BigOperators

def BoxedMargin {V E : Type*} (src dst : E → V) (w : E → Factors)
    (lo hi : V → ℝ) (τ : ℝ) (z : V → ℝ) : Prop :=
  (∀ v, lo v ≤ z v ∧ z v ≤ hi v) ∧
    ∀ e, (w e).lower (z (src e)) + τ ≤ z (dst e) ∧
      z (dst e) + τ ≤ (w e).upper (z (src e))

theorem compact_min_closed_has_least {V : Type*} [Fintype V]
    {S : Set (V → ℝ)} (hc : IsCompact S) (hne : S.Nonempty)
    (hmin : ∀ x ∈ S, ∀ y ∈ S, (fun v => min (x v) (y v)) ∈ S) :
    ∃ x, IsLeast S x := by
  classical
  have hcont : Continuous (fun x : V → ℝ => ∑ v, x v) :=
    continuous_finsetSum _ (fun v _ => continuous_apply v)
  obtain ⟨x, hx, hopt⟩ := hc.exists_isMinOn hne hcont.continuousOn
  refine ⟨x, hx, ?_⟩
  intro y hy v
  by_contra hn
  have hv : y v < x v := lt_of_not_ge hn
  have hs : (∑ i, min (x i) (y i)) < ∑ i, x i :=
    Finset.sum_lt_sum (fun i _ => min_le_left _ _)
      ⟨v, Finset.mem_univ v, lt_of_le_of_lt (min_le_right _ _) hv⟩
  have ho := hopt (hmin x hx y hy)
  exact (not_lt_of_ge ho) hs

theorem margin_min {V E : Type*} (src dst : E → V) (w : E → Factors)
    (lo hi : V → ℝ) (τ : ℝ) (hlo : ∀ v, 0 ≤ lo v)
    {x y : V → ℝ} (hx : BoxedMargin src dst w lo hi τ x)
    (hy : BoxedMargin src dst w lo hi τ y) :
    BoxedMargin src dst w lo hi τ (fun v => min (x v) (y v)) := by
  constructor
  · intro v
    exact ⟨le_min (hx.1 v).1 (hy.1 v).1,
      le_trans (min_le_left _ _) (hx.1 v).2⟩
  · intro e
    dsimp only
    have hx0 : 0 ≤ x (src e) := le_trans (hlo _) (hx.1 _).1
    have hy0 : 0 ≤ y (src e) := le_trans (hlo _) (hy.1 _).1
    have hm0 : 0 ≤ min (x (src e)) (y (src e)) := le_min hx0 hy0
    constructor
    · apply le_min
      · have hh := (w e).lower_strictMono.monotoneOn hm0 hx0 (min_le_left _ _)
        have he := (hx.2 e).1
        linarith
      · have hh := (w e).lower_strictMono.monotoneOn hm0 hy0 (min_le_right _ _)
        have he := (hy.2 e).1
        linarith
    · rcases le_total (x (src e)) (y (src e)) with hh | hh
      · rw [min_eq_left hh]
        have hm := min_le_left (x (dst e)) (y (dst e))
        have he := (hx.2 e).2
        linarith
      · rw [min_eq_right hh]
        have hm := min_le_right (x (dst e)) (y (dst e))
        have he := (hy.2 e).2
        linarith

theorem margin_isClosed {V E : Type*} (src dst : E → V) (w : E → Factors)
    (lo hi : V → ℝ) (τ : ℝ) :
    IsClosed {z | BoxedMargin src dst w lo hi τ z} := by
  simp only [BoxedMargin, Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro v
    exact (isClosed_le continuous_const (continuous_apply v)).inter
      (isClosed_le (continuous_apply v) continuous_const)
  · apply isClosed_iInter
    intro e
    exact (isClosed_le (((w e).continuous_lower.comp (continuous_apply (src e))).add
      continuous_const) (continuous_apply (dst e))).inter
      (isClosed_le ((continuous_apply (dst e)).add continuous_const)
        ((w e).continuous_upper.comp (continuous_apply (src e))))

theorem margin_has_least {V E : Type*} [Fintype V]
    (src dst : E → V) (w : E → Factors) (lo hi : V → ℝ) (τ : ℝ)
    (hlo : ∀ v, 0 ≤ lo v) (hne : ∃ z, BoxedMargin src dst w lo hi τ z) :
    ∃ z, IsLeast {x | BoxedMargin src dst w lo hi τ x} z := by
  have hc : IsCompact {z | BoxedMargin src dst w lo hi τ z} :=
    isCompact_Icc.of_isClosed_subset (margin_isClosed src dst w lo hi τ)
      (fun z hz => ⟨fun v => (hz.1 v).1, fun v => (hz.1 v).2⟩)
  exact compact_min_closed_has_least hc hne
    (fun _ hx _ hy => margin_min src dst w lo hi τ hlo hx hy)

end ThermoCoreCompatibility.GeneralCompatibility
