import proofs.OverlappingSiphonInvasion.BoundaryGrowth
import proofs.OverlappingSiphonInvasion.GrowthCocycle
import proofs.OverlappingSiphonInvasion.AccumulatedGrowth
import proofs.OverlappingSiphonInvasion.CompactGrowthWindow

noncomputable section
open Set
namespace OverlappingSiphonInvasion

/-- A single positive accumulated-growth window for the entire extinction
boundary, derived from the literal source and strict invasion assumptions. -/
theorem source_uniform_boundary_window (p : Rates) (hp : PositiveRates p)
    (he1 : p.mu1/p.alpha1 < p.recruitment/p.mu0)
    (he2 : p.mu2/p.alpha2 < p.recruitment/p.mu0) (hi : StrictMutualInvasion p)
    (R : ℝ) (hR : p.recruitment/deathFloor p+1 ≤ R) :
    ∃ ru rv rj : ℝ, ∃ k N : ℕ, ∃ Φ : LiftState → ℝ → LiftState, ∃ A : LiftState → ℝ → ℝ,
      0 < ru ∧ 0 < rv ∧ 0 < rj ∧ 0 < k ∧ 0 < N ∧
      (∀ z, Φ z 0 = z) ∧ (∀ z, A z 0 = 0) ∧
      (∀ t, 0 ≤ t → Continuous (fun z => Φ z t) ∧ Continuous (fun z => A z t)) ∧
      (∀ z s t, 0 ≤ s → 0 ≤ t → Φ z (s+t) = Φ (Φ z s) t) ∧
      (∀ z ∈ physicalLiftClosure ru rv rj R, ∀ t, 0 ≤ t →
        Φ z t ∈ physicalLiftClosure ru rv rj R ∧
        HasDerivAt (Φ z) (normalizedField p ru rv rj (Φ z t)) t ∧
        extinctionProduct ru rv rj k (Φ z t) =
          Real.exp (A z t)*extinctionProduct ru rv rj k z) ∧
      (∀ z ∈ physicalLiftClosure ru rv rj R, extinctionProduct ru rv rj k z = 0 → 1 < A z N) := by
  have hΛ : 0 < p.recruitment := by simpa [rateVector] using hp 0
  have hm := deathFloor_pos p hp
  have hR0 : 0 ≤ R := le_trans (by positivity : (0:ℝ) ≤ p.recruitment/deathFloor p+1) hR
  obtain ⟨ru,rv,rj,k,hru,hrv,hrj,hk,hboundary⟩ := source_boundary_eventual_growth p hp he1 he2 hi
  obtain ⟨Φ,A,hΦ0,hA0,hcont,hflow,hadd⟩ := normalized_growth_cocycle p hp ru rv rj R k hru hrv hrj hR
  let K := physicalLiftClosure ru rv rj R
  let P := extinctionProduct ru rv rj k
  have hK : IsCompact K := physicalLiftClosure_isCompact ru rv rj R hru hrv hrj
  have hPc : Continuous P := by unfold P extinctionProduct massU massV massJ; fun_prop
  have hmult : ∀ z ∈ K, ∀ t, 0 ≤ t → P (Φ z t) = Real.exp (A z t)*P z := by
    intro z hz
    have hpderiv : ∀ t, 0 ≤ t → HasDerivAt (fun s => P (Φ z s))
        (normalGrowth p ru rv rj k (Φ z t)*P (Φ z t)) t := by
      intro t ht
      exact normalized_product_derivative p ru rv rj R k hru hrv hrj (Φ z) t
        (hflow z hz t ht).1 (hflow z hz t ht).2.1
    simpa only [hΦ0] using exponential_growth_identity _ (A z) _ hpderiv
      (fun t ht => (hflow z hz t ht).2.2) (hA0 z)
  let B := K ∩ {z | P z = 0}
  have hBK : IsCompact B := hK.inter_right (isClosed_eq hPc continuous_const)
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hBK
  have hBflow : ∀ z ∈ B, ∀ t, 0 ≤ t → Φ z t ∈ B := by
    intro z hz t ht
    refine ⟨(hflow z hz.1 t ht).1,?_⟩
    change P (Φ z t) = 0
    rw [hmult z hz.1 t ht,hz.2,mul_zero]
  let f : B → B := fun z => ⟨Φ z 1,hBflow z z.property 1 (by norm_num)⟩
  have hiter : ∀ (n : ℕ) (z : B), ((f^[n] z : B) : LiftState) = Φ z n := by
    intro n
    induction n with
    | zero => intro z; simp only [Function.iterate_zero,Function.id_def,Nat.cast_zero,hΦ0]
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply']
      change Φ (↑(f^[n] z)) 1 = Φ z (↑(n+1))
      rw [ih,Nat.cast_add,Nat.cast_one]
      exact (hadd z n 1 (Nat.cast_nonneg n) (by norm_num)).1.symm
  let An : ℕ → B → ℝ := fun n z => A z n
  have hAn : ∀ n, Continuous (An n) := fun n =>
    ((hcont n (Nat.cast_nonneg n)).2).comp continuous_subtype_val
  have hAn0 : ∀ z, An 0 z = 0 := by
    intro z
    simpa only [An,Nat.cast_zero] using hA0 z
  have hAc : ∀ n m z, An (n+m) z = An n z+An m (f^[n] z) := by
    intro n m z
    change A z (↑(n+m)) = A z n+A (↑(f^[n] z)) m
    rw [Nat.cast_add,hiter]
    exact (hadd z n m (Nat.cast_nonneg n) (Nat.cast_nonneg m)).2
  have hpoint : ∀ z : B, ∃ n : ℕ, 1 < An (n+1) z := by
    intro z
    have hg := hboundary R hR0 (Φ z) (fun t ht => (hflow z z.property.1 t ht).1)
      (fun t ht => (hflow z z.property.1 t ht).2.1)
      (by simpa only [hΦ0] using z.property.2)
    simpa only [An,Nat.cast_add,Nat.cast_one] using
      accumulated_growth_positive_time (A z) _ (fun t ht => (hflow z z.property.1 t ht).2.2) hg
  obtain ⟨N,hN,hwindow⟩ := compact_positive_growth_window f An hAn hAn0 hAc hpoint
  refine ⟨ru,rv,rj,k,N,Φ,A,hru,hrv,hrj,hk,hN,hΦ0,hA0,hcont,?_,?_,?_⟩
  · intro z s t hs ht
    exact (hadd z s t hs ht).1
  · intro z hz t ht
    exact ⟨(hflow z hz t ht).1,(hflow z hz t ht).2.1,hmult z hz t ht⟩
  · intro z hz hp0
    exact hwindow ⟨z,hz,hp0⟩

end OverlappingSiphonInvasion
