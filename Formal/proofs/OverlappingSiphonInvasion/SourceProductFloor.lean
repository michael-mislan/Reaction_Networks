import proofs.OverlappingSiphonInvasion.SourceGrowthWindow
import proofs.OverlappingSiphonInvasion.ProductCollar
import proofs.OverlappingSiphonInvasion.BetweenSamples

noncomputable section
open Set Filter
namespace OverlappingSiphonInvasion

theorem closure_product_nonneg (ru rv rj R : ℝ) (k : ℕ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (z : LiftState)
    (hz : z ∈ physicalLiftClosure ru rv rj R) : 0 ≤ extinctionProduct ru rv rj k z := by
  have hx := (physicalLiftClosure_projection ru rv rj R z hz).1
  have ha := hx 1
  have hb := hx 2
  have hc := hx 3
  dsimp [extinctionProduct,massU,massV,massJ]
  positivity

/-- Uniform continuous-time product persistence for the actual compact source
flow. The floor is independent of its positive initial product. -/
theorem source_flow_product_floor (p : Rates) (hp : PositiveRates p)
    (he1 : p.mu1/p.alpha1 < p.recruitment/p.mu0)
    (he2 : p.mu2/p.alpha2 < p.recruitment/p.mu0) (hi : StrictMutualInvasion p)
    (R : ℝ) (hR : p.recruitment/deathFloor p+1 ≤ R) :
    ∃ ru rv rj : ℝ, ∃ k : ℕ, ∃ δ : ℝ, ∃ Φ : LiftState → ℝ → LiftState,
      0 < ru ∧ 0 < rv ∧ 0 < rj ∧ 0 < k ∧ 0 < δ ∧
      (∀ z, Φ z 0 = z) ∧
      (∀ z ∈ physicalLiftClosure ru rv rj R, ∀ t, 0 ≤ t →
        Φ z t ∈ physicalLiftClosure ru rv rj R ∧
        HasDerivAt (Φ z) (normalizedField p ru rv rj (Φ z t)) t) ∧
      (∀ z ∈ physicalLiftClosure ru rv rj R, 0 < extinctionProduct ru rv rj k z →
        ∀ᶠ t : ℝ in atTop, δ ≤ extinctionProduct ru rv rj k (Φ z t)) := by
  obtain ⟨ru,rv,rj,k,N,Φ,A,hru,hrv,hrj,hk,hN,hΦ0,_hA0,hcont,hadd,hflow,hwindow⟩ :=
    source_uniform_boundary_window p hp he1 he2 hi R hR
  let K := physicalLiftClosure ru rv rj R
  let P := extinctionProduct ru rv rj k
  let f : LiftState → LiftState := fun z => Φ z N
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hK : IsCompact K := physicalLiftClosure_isCompact ru rv rj R hru hrv hrj
  have hPc : Continuous P := by unfold P extinctionProduct massU massV massJ; fun_prop
  have hP0 : ∀ z ∈ K, 0 ≤ P z := closure_product_nonneg ru rv rj R k hru hrv hrj
  obtain ⟨η,hη,hsamples⟩ := compact_sampled_product_floor K hK f P (fun z => A z N)
    (fun z hz => (hflow z hz N hNR.le).1) hPc (hcont N hNR.le).2 hP0
    (fun z hz => (hflow z hz N hNR.le).2.2) hwindow
  let G := normalGrowth p ru rv rj k
  have hGc : Continuous G := by
    unfold G normalGrowth normalHU normalHV normalHJ privateA privateB sharedC
    fun_prop
  obtain ⟨b,hb⟩ := hK.bddAbove_image hGc.continuousOn
  let L := max b 0
  have hL : 0 ≤ L := le_max_right _ _
  have hG : ∀ z ∈ K, G z ≤ L := fun z hz =>
    (hb ⟨z,hz,rfl⟩).trans (le_max_left _ _)
  have hu : ∀ z ∈ K, ∀ t, 0 ≤ t → P (Φ z t) ≤ Real.exp (L*t)*P z := by
    intro z hz t ht
    have hderiv : ∀ s, 0 ≤ s → HasDerivAt (fun u => P (Φ z u))
        (G (Φ z s)*P (Φ z s)) s := by
      intro s hs
      exact normalized_product_derivative p ru rv rj R k hru hrv hrj (Φ z) s
        (hflow z hz s hs).1 (hflow z hz s hs).2.1
    have hh := relative_growth_upper (fun s => P (Φ z s)) (fun s => G (Φ z s)*P (Φ z s)) L
      hderiv (fun s hs => mul_le_mul_of_nonneg_right
        (hG _ (hflow z hz s hs).1) (hP0 _ (hflow z hz s hs).1)) t ht
    simpa only [hΦ0] using hh
  have hiter : ∀ (n : ℕ) z, f^[n] z = Φ z ((n:ℝ)*N) := by
    intro n
    induction n with
    | zero => intro z; simp only [Function.iterate_zero,Function.id_def,Nat.cast_zero,zero_mul,hΦ0]
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply']
      change Φ (f^[n] z) N = Φ z ((↑(n+1))*N)
      rw [ih,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
      exact (hadd z ((n:ℝ)*N) N (mul_nonneg (Nat.cast_nonneg n) hNR.le) hNR.le).symm
  refine ⟨ru,rv,rj,k,η/Real.exp (L*N),Φ,hru,hrv,hrj,hk,div_pos hη (Real.exp_pos _),hΦ0,?_,?_⟩
  · intro z hz t ht
    exact ⟨(hflow z hz t ht).1,(hflow z hz t ht).2.1⟩
  · intro z hz hpz
    have hs : ∀ᶠ n : ℕ in atTop, η ≤ P (Φ z ((n:ℝ)*N)) := by
      filter_upwards [hsamples z hz hpz] with n hn
      simpa only [hiter] using hn
    apply sampled_to_continuous_floor (fun t => P (Φ z t)) N (Real.exp (L*N)) η hNR (Real.exp_pos _) ?_ hs
    intro t s ht hs hsN
    change P (Φ z (t+s)) ≤ Real.exp (L*N)*P (Φ z t)
    rw [hadd z t s ht hs]
    exact (hu (Φ z t) (hflow z hz t ht).1 s hs).trans
      (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsN hL))
        (hP0 _ (hflow z hz t ht).1))

end OverlappingSiphonInvasion
