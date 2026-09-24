import proofs.SmallCusp.Obstruction.FiniteGeneratorHull
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Circuit coverage of normalized equilibrium fluxes

The normalized equilibrium slice has three independent affine constraints:
two equilibrium equations and normalization.  Its extreme points therefore
use at most three reaction coordinates.  This file develops that statement
from the generator mechanism, independently of any network enumeration.
-/

open scoped BigOperators

namespace SmallCusp

open Set

noncomputable def supportExtension {n : ℕ} (x : Fin n → ℝ) :
    ({i : Fin n // x i ≠ 0} → ℝ) →ₗ[ℝ]
      (Fin n → ℝ) where
  toFun c i := if hi : x i ≠ 0 then c ⟨i, hi⟩ else 0
  map_add' c d := by
    funext i
    by_cases hi : x i = 0 <;> simp [hi]
  map_smul' a c := by
    funext i
    by_cases hi : x i = 0 <;> simp [hi]

theorem supportExtension_injective {n : ℕ} (x : Fin n → ℝ) :
    Function.Injective (supportExtension x) := by
  intro c d hcd
  funext i
  have hxi : x i.1 ≠ 0 := i.2
  have hi := congrFun hcd i.1
  simpa [supportExtension, hxi] using hi

/-- More than three active reaction coordinates leave a nonzero direction
inside the kernel of any three linear constraints. -/
theorem exists_nonzero_supported_kernel_of_three_lt_support {n : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (x : Fin n → ℝ)
    (hcard : 3 < Fintype.card {i : Fin n // x i ≠ 0}) :
    ∃ d : Fin n → ℝ, d ≠ 0 ∧ A d = 0 ∧ ∀ i, x i = 0 → d i = 0 := by
  let I := {i : Fin n // x i ≠ 0}
  let L : (I → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := A.comp (supportExtension x)
  have hdim : Module.finrank ℝ (Fin 3 → ℝ) < Module.finrank ℝ (I → ℝ) := by
    simpa [I, Module.finrank_fin_fun, Module.finrank_pi] using hcard
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hcL, hc0⟩ := (Submodule.ne_bot_iff (LinearMap.ker L)).mp hker
  refine ⟨supportExtension x c, ?_, ?_, ?_⟩
  · exact fun hc ↦ hc0 (supportExtension_injective x (by simpa using hc))
  · exact hcL
  · intro i hxi
    simp [supportExtension, hxi]

/-- An extreme point cannot admit a nonzero two-sided feasible direction. -/
theorem not_extreme_of_nonzero_feasible_direction {n : ℕ}
    (s : Set (Fin n → ℝ)) (x d : Fin n → ℝ)
    (hd : d ≠ 0) (hminus : x - d ∈ s) (hplus : x + d ∈ s) :
    x ∉ s.extremePoints ℝ := by
  intro hx
  letI : Invertible (2 : ℝ) := by
    use (2 : ℝ)⁻¹ <;> norm_num
  have hxm : x - d = x := hx.2 hminus hplus (mem_openSegment_sub_add x d)
  apply hd
  simpa only [sub_eq_self] using hxm

/-- A nonnegative vector on a finite index set has a uniform positive lower
bound on its nonzero coordinates. -/
theorem exists_pos_lower_bound_on_support {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, x i ≠ 0 → δ ≤ x i := by
  induction n with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      obtain ⟨δ, hδ, hδle⟩ := ih (fun i ↦ x i.succ) (fun i ↦ hx i.succ)
      by_cases h0 : x 0 = 0
      · refine ⟨δ, hδ, ?_⟩
        intro i
        refine Fin.cases ?_ (fun j hj ↦ hδle j ?_) i
        · exact fun hi ↦ (hi h0).elim
        · simpa using hj
      · have hx0 : 0 < x 0 := lt_of_le_of_ne (hx 0) (Ne.symm h0)
        refine ⟨min δ (x 0), lt_min hδ hx0, ?_⟩
        intro i
        refine Fin.cases ?_ (fun j hj ↦ (min_le_left δ (x 0)).trans (hδle j ?_)) i
        · exact fun _ ↦ min_le_right δ (x 0)
        · simpa using hj

def nonnegativeLinearFiber {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (b : Fin k → ℝ) :
    Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ A x = b}

theorem convex_nonnegativeLinearFiber {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (b : Fin k → ℝ) :
    Convex ℝ (nonnegativeLinearFiber A b) := by
  intro x hx y hy a c ha hc hac
  constructor
  · intro i
    dsimp
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hc (hy.1 i))
  · rw [map_add, map_smul, map_smul, hx.2, hy.2, ← add_smul, hac, one_smul]

theorem exists_nonzero_feasible_direction_of_supported_kernel {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (b : Fin k → ℝ)
    {x d : Fin n → ℝ} (hx : x ∈ nonnegativeLinearFiber A b)
    (hd0 : d ≠ 0) (hAd : A d = 0) (
      hsupp : ∀ i, x i = 0 → d i = 0) :
    ∃ e : Fin n → ℝ, e ≠ 0 ∧
      x - e ∈ nonnegativeLinearFiber A b ∧
      x + e ∈ nonnegativeLinearFiber A b := by
  obtain ⟨δ, hδ0, hδle⟩ := exists_pos_lower_bound_on_support x hx.1
  let ε : ℝ := δ / (2 * (‖d‖ + 1))
  have hden : 0 < 2 * (‖d‖ + 1) := by positivity
  have hε0 : 0 < ε := div_pos hδ0 hden
  have hsmall : ∀ i, x i ≠ 0 → |ε * d i| < x i := by
    intro i hxi
    have hdi : |d i| ≤ ‖d‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm d i
    have hnorm : ‖d‖ < ‖d‖ + 1 := by linarith
    have heq : ε * (‖d‖ + 1) = δ / 2 := by
      dsimp [ε]
      field_simp
    have habs : |ε * d i| = ε * |d i| := by
      rw [abs_mul, abs_of_pos hε0]
    rw [habs]
    have : ε * |d i| < δ := by nlinarith
    exact this.trans_le (hδle i hxi)
  let e : Fin n → ℝ := ε • d
  have he0 : e ≠ 0 := smul_ne_zero hε0.ne' hd0
  have hAe : A e = 0 := by simp [e, hAd]
  refine ⟨e, he0, ?_, ?_⟩
  · constructor
    · intro i
      by_cases hxi : x i = 0
      · have hdi := hsupp i hxi
        simp [e, hxi, hdi]
      · have hs := hsmall i hxi
        dsimp [e]
        exact sub_nonneg.mpr (le_of_lt (lt_of_le_of_lt (le_abs_self _) hs))
    · rw [map_sub, hAe, sub_zero]
      exact hx.2
  · constructor
    · intro i
      by_cases hxi : x i = 0
      · have hdi := hsupp i hxi
        simp [e, hxi, hdi]
      · have hs := hsmall i hxi
        dsimp [e]
        exact le_of_lt (by linarith [neg_abs_le (ε * d i)])
    · rw [map_add, hAe, add_zero]
      exact hx.2

/-- At an extreme feasible flux, the active columns admit no nontrivial
linear relation.  This is the exact support-minimal circuit interface used by
the finite rational checker. -/
theorem extreme_supportRestriction_injective {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (b : Fin k → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ (nonnegativeLinearFiber A b).extremePoints ℝ) :
    Function.Injective (A.comp (supportExtension x)) := by
  intro c d hcd
  let q := c - d
  have hLq : (A.comp (supportExtension x)) q = 0 := by
    dsimp [q]
    simpa only [map_sub] using sub_eq_zero.mpr hcd
  by_contra hne
  have hq0 : q ≠ 0 := by
    intro hq
    apply hne
    exact sub_eq_zero.mp hq
  let direction : Fin n → ℝ := supportExtension x q
  have hdirection0 : direction ≠ 0 := by
    exact fun hd ↦ hq0 (supportExtension_injective x (by simpa [direction] using hd))
  have hAdirection : A direction = 0 := hLq
  have hsupp : ∀ i, x i = 0 → direction i = 0 := by
    intro i hxi
    simp [direction, supportExtension, hxi]
  obtain ⟨e, he0, hminus, hplus⟩ :=
    exists_nonzero_feasible_direction_of_supported_kernel A b hx.1
      hdirection0 hAdirection hsupp
  exact not_extreme_of_nonzero_feasible_direction
    (nonnegativeLinearFiber A b) x e he0 hminus hplus hx

/-- A support-minimal feasible point is the unique feasible point with its
zero pattern.  Thus a closed-form circuit candidate only has to match the
active support; its coefficients are then forced by the generator mechanism. -/
theorem eq_of_same_zero_and_injective_supportRestriction {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (b : Fin k → ℝ)
    {x y : Fin n → ℝ}
    (hx : x ∈ nonnegativeLinearFiber A b)
    (hy : y ∈ nonnegativeLinearFiber A b)
    (hzero : ∀ i, x i = 0 ↔ y i = 0)
    (hinj : Function.Injective (A.comp (supportExtension x))) :
    x = y := by
  let c : {i : Fin n // x i ≠ 0} → ℝ := fun i ↦ x i - y i
  have hext : supportExtension x c = x - y := by
    funext i
    by_cases hxi : x i = 0
    · have hyi : y i = 0 := (hzero i).mp hxi
      simp [supportExtension, hxi, hyi]
    · simp [supportExtension, hxi, c]
  have hAc : (A.comp (supportExtension x)) c = 0 := by
    rw [LinearMap.comp_apply, hext, map_sub, hx.2, hy.2, sub_self]
  have hc : c = 0 := hinj (by simpa using hAc)
  funext i
  by_cases hxi : x i = 0
  · have hyi : y i = 0 := (hzero i).mp hxi
    exact hxi.trans hyi.symm
  · have hi := congrFun hc ⟨i, hxi⟩
    simpa [c] using sub_eq_zero.mp hi

theorem support_card_le_of_injective_supportRestriction {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) {x : Fin n → ℝ}
    (hinj : Function.Injective (A.comp (supportExtension x))) :
    Fintype.card {i : Fin n // x i ≠ 0} ≤ k := by
  have hdim := (A.comp (supportExtension x)).finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fin_fun, Module.finrank_pi] using hdim

/-- With only three linear equalities, an extreme nonnegative feasible point
has support of cardinality at most three. -/
theorem extreme_support_card_le_three {n : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (b : Fin 3 → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ (nonnegativeLinearFiber A b).extremePoints ℝ) :
    Fintype.card {i : Fin n // x i ≠ 0} ≤ 3 := by
  by_contra hcard
  have hcard' : 3 < Fintype.card {i : Fin n // x i ≠ 0} := by omega
  obtain ⟨d, hd0, hAd, hsupp⟩ :=
    exists_nonzero_supported_kernel_of_three_lt_support A x hcard'
  obtain ⟨δ, hδ0, hδle⟩ := exists_pos_lower_bound_on_support x hx.1.1
  let ε : ℝ := δ / (2 * (‖d‖ + 1))
  have hden : 0 < 2 * (‖d‖ + 1) := by positivity
  have hε0 : 0 < ε := div_pos hδ0 hden
  have hsmall : ∀ i, x i ≠ 0 → |ε * d i| < x i := by
    intro i hxi
    have hdi : |d i| ≤ ‖d‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm d i
    have hnorm : ‖d‖ < ‖d‖ + 1 := by linarith
    have heq : ε * (‖d‖ + 1) = δ / 2 := by
      dsimp [ε]
      field_simp
    have habs : |ε * d i| = ε * |d i| := by
      rw [abs_mul, abs_of_pos hε0]
    rw [habs]
    have : ε * |d i| < δ := by nlinarith
    exact this.trans_le (hδle i hxi)
  let e : Fin n → ℝ := ε • d
  have he0 : e ≠ 0 := by
    exact smul_ne_zero hε0.ne' hd0
  have hAe : A e = 0 := by simp [e, hAd]
  have hminus : x - e ∈ nonnegativeLinearFiber A b := by
    constructor
    · intro i
      by_cases hxi : x i = 0
      · have hdi := hsupp i hxi
        simp [e, hxi, hdi]
      · have hs := hsmall i hxi
        dsimp [e]
        exact sub_nonneg.mpr (le_of_lt (lt_of_le_of_lt (le_abs_self _) hs))
    · rw [map_sub, hAe, sub_zero]
      exact hx.1.2
  have hplus : x + e ∈ nonnegativeLinearFiber A b := by
    constructor
    · intro i
      by_cases hxi : x i = 0
      · have hdi := hsupp i hxi
        simp [e, hxi, hdi]
      · have hs := hsmall i hxi
        dsimp [e]
        exact le_of_lt (by linarith [neg_abs_le (ε * d i)])
    · rw [map_add, hAe, add_zero]
      exact hx.1.2
  exact not_extreme_of_nonzero_feasible_direction
    (nonnegativeLinearFiber A b) x e he0 hminus hplus hx

/-- Finite circuit docking interface.  A checker need only establish that its
finite list contains every feasible point of support at most three.  Compact
convex geometry and the support theorem then cover the entire continuum. -/
theorem finite_smallSupport_generators_cover_threeFiber {n : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (b : Fin 3 → ℝ)
    (generators : Set (Fin n → ℝ))
    (hcompact : IsCompact (nonnegativeLinearFiber A b))
    (hfinite : generators.Finite)
    (hsubset : generators ⊆ nonnegativeLinearFiber A b)
    (hsmall : ∀ x ∈ nonnegativeLinearFiber A b,
      Fintype.card {i : Fin n // x i ≠ 0} ≤ 3 → x ∈ generators) :
    nonnegativeLinearFiber A b = convexHull ℝ generators := by
  apply compactConvex_eq_convexHull_finite_of_extremePoints_subset
    (nonnegativeLinearFiber A b) generators hcompact
    (convex_nonnegativeLinearFiber A b) hfinite hsubset
  intro x hx
  exact hsmall x hx.1 (extreme_support_card_le_three A b hx)

/-- Sharper finite docking interface: the generator list only needs to cover
feasible points whose active-column restriction is injective.  These are the
support-minimal circuits; dependent faces need no pointwise enumeration. -/
theorem finite_supportMinimal_generators_cover {n k : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (b : Fin k → ℝ)
    (generators : Set (Fin n → ℝ))
    (hcompact : IsCompact (nonnegativeLinearFiber A b))
    (hfinite : generators.Finite)
    (hsubset : generators ⊆ nonnegativeLinearFiber A b)
    (hminimal : ∀ x ∈ nonnegativeLinearFiber A b,
      Function.Injective (A.comp (supportExtension x)) → x ∈ generators) :
    nonnegativeLinearFiber A b = convexHull ℝ generators := by
  apply compactConvex_eq_convexHull_finite_of_extremePoints_subset
    (nonnegativeLinearFiber A b) generators hcompact
    (convex_nonnegativeLinearFiber A b) hfinite hsubset
  intro x hx
  exact hminimal x hx.1 (extreme_supportRestriction_injective A b hx)

def equilibriumNormalizationMap {n : ℕ} (stoich : Fin 2 → Fin n → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![
    ∑ r, stoich 0 r * x r,
    ∑ r, stoich 1 r * x r,
    ∑ r, x r]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [Finset.mul_sum, mul_left_comm]

def normalizedEquilibriumTarget : Fin 3 → ℝ := ![0, 0, 1]

theorem equilibriumNormalizationMap_last {n : ℕ}
    (stoich : Fin 2 → Fin n → ℝ) (x : Fin n → ℝ) :
    equilibriumNormalizationMap stoich x 2 = ∑ r, x r := by
  rfl

/-- Nonzero stoichiometric columns exclude singleton normalized equilibria.
Together with active-column injectivity, every support-minimal normalized
planar equilibrium is therefore exactly a pair or a triple. -/
theorem normalized_support_card_eq_two_or_three {n : ℕ}
    (stoich : Fin 2 → Fin n → ℝ)
    (hcol : ∀ r, (fun i ↦ stoich i r) ≠ 0)
    {x : Fin n → ℝ}
    (hx : x ∈ nonnegativeLinearFiber
      (equilibriumNormalizationMap stoich) normalizedEquilibriumTarget)
    (hinj : Function.Injective
      ((equilibriumNormalizationMap stoich).comp (supportExtension x))) :
    Fintype.card {i : Fin n // x i ≠ 0} = 2 ∨
      Fintype.card {i : Fin n // x i ≠ 0} = 3 := by
  have hle : Fintype.card {i : Fin n // x i ≠ 0} ≤ 3 :=
    support_card_le_of_injective_supportRestriction
      (equilibriumNormalizationMap stoich) hinj
  have hsum : ∑ r, x r = 1 := by
    have hlast := congrFun hx.2 (2 : Fin 3)
    simpa [equilibriumNormalizationMap, normalizedEquilibriumTarget] using hlast
  have hpos : 0 < Fintype.card {i : Fin n // x i ≠ 0} := by
    rw [Fintype.card_pos_iff]
    by_contra hempty
    have hz : ∀ r, x r = 0 := by
      intro r
      by_contra hr
      exact hempty ⟨⟨r, hr⟩⟩
    have : ∑ r, x r = 0 := by simp [hz]
    linarith
  have hne_one : Fintype.card {i : Fin n // x i ≠ 0} ≠ 1 := by
    intro hone
    obtain ⟨r, hr⟩ := Fintype.card_eq_one_iff.mp hone
    let q : Fin n := r.1
    have hq : x q ≠ 0 := r.2
    have hoff : ∀ j : Fin n, j ≠ q → x j = 0 := by
      intro j hj
      by_contra hxj
      have heq := congrArg Subtype.val (hr ⟨j, hxj⟩)
      exact hj heq
    have heq : ∀ i, ∑ j, stoich i j * x j = stoich i q * x q := by
      intro i
      rw [Finset.sum_eq_single q]
      · intro j _ hj
        simp [hoff j hj]
      · simp
    have hstoich : (fun i ↦ stoich i q) = 0 := by
      funext i
      fin_cases i
      · have hi := congrFun hx.2 (0 : Fin 3)
        simp [equilibriumNormalizationMap, normalizedEquilibriumTarget] at hi
        rw [heq 0] at hi
        exact (mul_eq_zero.mp hi).resolve_right hq
      · have hi := congrFun hx.2 (1 : Fin 3)
        simp [equilibriumNormalizationMap, normalizedEquilibriumTarget] at hi
        rw [heq 1] at hi
        exact (mul_eq_zero.mp hi).resolve_right hq
    exact hcol q hstoich
  omega

theorem exists_pair_support_of_card_eq_two {n : ℕ} (x : Fin n → ℝ)
    (hcard : Fintype.card {i : Fin n // x i ≠ 0} = 2) :
    ∃ r s : Fin n, r ≠ s ∧ ∀ q, x q ≠ 0 ↔ q = r ∨ q = s := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun i ↦ x i ≠ 0
  have hScard : S.card = 2 := by
    simpa [S, Fintype.card_subtype] using hcard
  obtain ⟨r, s, hrs, hS⟩ := Finset.card_eq_two.mp hScard
  refine ⟨r, s, hrs, ?_⟩
  intro q
  have hmem : q ∈ S ↔ q = r ∨ q = s := by rw [hS]; simp
  simpa [S] using hmem

theorem exists_triple_support_of_card_eq_three {n : ℕ} (x : Fin n → ℝ)
    (hcard : Fintype.card {i : Fin n // x i ≠ 0} = 3) :
    ∃ r s t : Fin n, r ≠ s ∧ r ≠ t ∧ s ≠ t ∧
      ∀ q, x q ≠ 0 ↔ q = r ∨ q = s ∨ q = t := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun i ↦ x i ≠ 0
  have hScard : S.card = 3 := by
    simpa [S, Fintype.card_subtype] using hcard
  obtain ⟨r, s, t, hrs, hrt, hst, hS⟩ := Finset.card_eq_three.mp hScard
  refine ⟨r, s, t, hrs, hrt, hst, ?_⟩
  intro q
  have hmem : q ∈ S ↔ q = r ∨ q = s ∨ q = t := by rw [hS]; simp
  simpa [S] using hmem

/-- The normalization row makes the nonnegative equilibrium fiber compact:
each coordinate lies in `[0,1]`. -/
theorem compact_normalizedEquilibriumFiber {n : ℕ}
    (stoich : Fin 2 → Fin n → ℝ) :
    IsCompact (nonnegativeLinearFiber
      (equilibriumNormalizationMap stoich) normalizedEquilibriumTarget) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have hnonneg : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
      have h : IsClosed (⋂ i, (fun x : Fin n → ℝ ↦ x i) ⁻¹' Set.Ici 0) :=
        isClosed_iInter fun i ↦ (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).preimage
          (continuous_apply i : Continuous (fun x : Fin n → ℝ ↦ x i))
      convert h using 1
      ext x
      simp
    have heq : IsClosed {x : Fin n → ℝ |
        equilibriumNormalizationMap stoich x = normalizedEquilibriumTarget} :=
      isClosed_singleton.preimage
        (equilibriumNormalizationMap stoich).continuous_of_finiteDimensional
    exact hnonneg.inter heq
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨1, fun x hx ↦ (pi_norm_le_iff_of_nonneg (by norm_num)).2 ?_⟩
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 i)]
    have hsum : ∑ r, x r = 1 := by
      have hlast := congrFun hx.2 (2 : Fin 3)
      simpa [equilibriumNormalizationMap, normalizedEquilibriumTarget] using hlast
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)

theorem finite_normalizedCircuitGenerators_cover {n : ℕ}
    (stoich : Fin 2 → Fin n → ℝ) (generators : Set (Fin n → ℝ))
    (hfinite : generators.Finite)
    (hsubset : generators ⊆ nonnegativeLinearFiber
      (equilibriumNormalizationMap stoich) normalizedEquilibriumTarget)
    (hsmall : ∀ x ∈ nonnegativeLinearFiber
        (equilibriumNormalizationMap stoich) normalizedEquilibriumTarget,
      Fintype.card {i : Fin n // x i ≠ 0} ≤ 3 → x ∈ generators) :
    nonnegativeLinearFiber
        (equilibriumNormalizationMap stoich) normalizedEquilibriumTarget =
      convexHull ℝ generators :=
  finite_smallSupport_generators_cover_threeFiber
    (equilibriumNormalizationMap stoich) normalizedEquilibriumTarget generators
    (compact_normalizedEquilibriumFiber stoich) hfinite hsubset hsmall

theorem finite_normalizedSupportMinimalGenerators_cover {n : ℕ}
    (stoich : Fin 2 → Fin n → ℝ) (generators : Set (Fin n → ℝ))
    (hfinite : generators.Finite)
    (hsubset : generators ⊆ nonnegativeLinearFiber
      (equilibriumNormalizationMap stoich) normalizedEquilibriumTarget)
    (hminimal : ∀ x ∈ nonnegativeLinearFiber
        (equilibriumNormalizationMap stoich) normalizedEquilibriumTarget,
      Function.Injective
        ((equilibriumNormalizationMap stoich).comp (supportExtension x)) →
      x ∈ generators) :
    nonnegativeLinearFiber
        (equilibriumNormalizationMap stoich) normalizedEquilibriumTarget =
      convexHull ℝ generators :=
  finite_supportMinimal_generators_cover
    (equilibriumNormalizationMap stoich) normalizedEquilibriumTarget generators
    (compact_normalizedEquilibriumFiber stoich) hfinite hsubset hminimal

/-- Carathéodory compression in a two-dimensional affine fiber.  If the
direction space `ker A` has dimension at most two, every convex-hull point is
a positive convex combination of at most three generators. -/
theorem eq_pos_convex_span_card_le_three_of_mem_threeFiber {n : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (b : Fin 3 → ℝ)
    (generators : Set (Fin n → ℝ))
    (hsubset : generators ⊆ nonnegativeLinearFiber A b)
    (hker : Module.finrank ℝ (LinearMap.ker A) ≤ 2)
    {x : Fin n → ℝ} (hx : x ∈ convexHull ℝ generators) :
    ∃ (ι : Type) (_ : Fintype ι),
      ∃ (z : ι → Fin n → ℝ) (w : ι → ℝ),
        Set.range z ⊆ generators ∧ AffineIndependent ℝ z ∧
        (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
        ∑ i, w i • z i = x ∧ Fintype.card ι ≤ 3 := by
  obtain ⟨ι, hι, z, w, hz, hzi, hwpos, hwsum, hwcenter⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  letI : Fintype ι := hι
  have huniv : (Finset.univ : Finset ι).Nonempty := by
    by_contra hu
    have hzero : ∑ i, w i = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hu, Finset.sum_empty]
    linarith
  let i0 : ι := huniv.choose
  letI : Nonempty ι := ⟨i0⟩
  have hzfiber : ∀ i, A (z i) = b := by
    intro i
    exact (hsubset (hz ⟨i, rfl⟩)).2
  have hvspan : vectorSpan ℝ (Set.range z) ≤ LinearMap.ker A := by
    rw [vectorSpan_range_eq_span_range_vsub_right ℝ z i0]
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    change A (z i - z i0) = 0
    rw [map_sub, hzfiber i, hzfiber i0, sub_self]
  have hdim : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ 2 :=
    (Submodule.finrank_mono hvspan).trans hker
  have hcard : Fintype.card ι ≤ 3 := by
    have hi := hzi.finrank_vectorSpan_add_one
    omega
  exact ⟨ι, hι, z, w, hz, hzi, hwpos, hwsum, hwcenter, hcard⟩

end SmallCusp
