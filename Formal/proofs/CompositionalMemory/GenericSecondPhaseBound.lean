import proofs.CompositionalMemory.GenericGenerationLaw
import proofs.HeritableCompositions.KernelComposition

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

noncomputable def generalStillActive {k d : ℕ} (N : ℕ) (D : Finset (GeneralCountState k d)) :
    Set (Option {s : GeneralCountState k d // s ∈ D}) :=
  {x | match x with | none => False | some s => s.val.2 < 2*(k*N)}

/-- The second interval's failure is covered by unsafe exit, failure to divide,
and the derived complementary daughter-partition tail. -/
theorem general_second_phase_failure {k d : ℕ} {R : Type*} [Fintype R]
    (hk : 1 ≤ k) (next : GeneralCountState k d → R → GeneralCountState k d)
    (rate : GeneralCountState k d → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (N C : ℕ) (hN : 0 < N) (hC : 0 < C)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hQ : ∀ i x y, Q i x y=Q i y x) (center : Fin k → Fin d → ℝ)
    (c radius birth parent L r δ : ℝ) (hc : 0 < c) (hradius : 0 ≤ radius)
    (hb : birth ≤ c*radius^2) (hL : 0 ≤ L) (hr : 0 ≤ r) (hδ : 0 < δ)
    (hcenter : ∀ i a, center i a ≤ (C:ℝ)-radius)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y) (hop : ∀ i x y, |Q i x y| ≤ L*‖x‖*‖y‖)
    (hsize : parent ≤ c*r^2) (hmargin : parent+2*L*r*δ+L*δ^2 < birth)
    (q t : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center (fun i y => Q i y y) parent)).total s ≤ q)
    (s : {s : GeneralCountState k d // s ∈ generalProductDomain N C center (fun i y => Q i y y) parent}) :
    (generalSecondPhaseLaw next rate hrate N C hN Q center c radius birth parent hc hradius hb hcenter hcoerc
      q t hq hclock s).mass none ≤
    ((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center (fun i y => Q i y y) parent)).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {none}) (some s)+
    ((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N))
      (generalProductDomain N C center (fun i y => Q i y y) parent)).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator (generalStillActive N (generalProductDomain N C center (fun i y => Q i y y) parent))) (some s)+
    2*(k:ℝ)*(d:ℝ)*Real.exp (-2*(N:ℝ)*δ^2/(2*(C:ℝ))) := by
  classical
  let domain := generalProductDomain N C center (fun i y => Q i y y) parent
  let ε := 2*(k:ℝ)*(d:ℝ)*Real.exp (-2*(N:ℝ)*δ^2/(2*(C:ℝ)))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hpartition (x : {s : GeneralCountState k d // s ∈ domain}) (hdiv : x.val.2=2*(k*N)) :
      (generalPartitionLaw N C hN Q center c radius birth hc hradius hb hcenter hcoerc x.val.1).mass none ≤ ε := by
    rw [generalPartitionLaw_failure_eq]
    have hx := x.property
    simp only [domain,generalProductDomain,Finset.mem_filter,Finset.product_eq_sprod,
      Finset.mem_product,Finset.mem_Icc] at hx
    have hn (i a) : (x.val.1 i a:ℝ) ≤ (2*(C:ℝ))*(N:ℝ) := by
      have hh := (mem_generalCountBox k d (C*(2*N)) x.val.1).mp hx.1.1 i a
      have hh' : (x.val.1 i a:ℝ) ≤ (C:ℝ)*(2*(N:ℝ)) := by exact_mod_cast hh
      nlinarith only [hh']
    have hfun (i) : generalConcentration x.val i=(fun a => (x.val.1 i a:ℝ)/(2*(N:ℝ))) := by
      have heq : x.val=(x.val.1,k*(2*N)) := Prod.ext rfl (by rw [hdiv]; ring)
      rw [heq,general_lattice_concentration hk]
      simp only [Nat.cast_mul,Nat.cast_ofNat]
    have hparent (i) : Q i (fun a => (x.val.1 i a:ℝ)/(2*(N:ℝ))-center i a)
        (fun a => (x.val.1 i a:ℝ)/(2*(N:ℝ))-center i a) ≤ parent := by
      have he := (hx.2 i).le
      simpa only [hfun] using he
    exact general_partition_failure N hN Q hQ center c L r δ parent birth (2*C)
      hc hL hr hδ (by positivity) hcoerc hop hsize hmargin x.val.1 hn hparent
  have hpoint (x : Option {s : GeneralCountState k d // s ∈ domain}) :
      (generalAfterDivision N C hN Q center c radius birth parent hc hradius hb hcenter hcoerc x).mass none ≤
      FiniteKernel.eventIndicator {none} x+FiniteKernel.eventIndicator (generalStillActive N domain) x+ε := by
    cases x with
    | none =>
      simpa [generalAfterDivision,FiniteLaw.pure,FiniteKernel.eventIndicator,generalStillActive] using
        (le_add_of_nonneg_right hε : (1:ℝ) ≤ 1+ε)
    | some x =>
      by_cases hdiv : x.val.2=2*(k*N)
      · simpa [generalAfterDivision,hdiv,FiniteKernel.eventIndicator,generalStillActive] using hpartition x hdiv
      · have hx := x.property
        simp only [domain,generalProductDomain,Finset.mem_filter,Finset.product_eq_sprod,
          Finset.mem_product,Finset.mem_Icc] at hx
        have hactive : x.val.2 < 2*(k*N) := by omega
        simpa [generalAfterDivision,hdiv,FiniteLaw.pure,FiniteKernel.eventIndicator,generalStillActive,hactive] using
          (le_add_of_nonneg_right hε : (1:ℝ) ≤ 1+ε)
  change (poissonLaw _ _ _).expect (fun x =>
    (generalAfterDivision N C hN Q center c radius birth parent hc hradius hb hcenter hcoerc x).mass none) ≤ _
  rw [poissonLaw_expect]
  have h := poisson_mono ((retainedReactionModel next rate hrate (fun s => s.2 < 2*(k*N)) domain).uniformize
    q hq hclock) (q*t) _ _ hpoint (some s)
  rw [poisson_additive,poisson_additive,poisson_constant] at h
  exact h

end CompositionalMemory
