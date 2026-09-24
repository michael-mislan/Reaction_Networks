import proofs.CoreCouplingGlobal.RoutedSource
import proofs.CoreCouplingGlobal.RoutedRegion

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

private theorem vec_eight_fifth {α : Type*} (a b c d e f g h : α) :
    (![a,b,c,d,e,f,g,h] : Fin 8 → α) 5 = f := rfl

theorem routed_core_current_formulas (e g : ℝ) (x : State) :
    routedCurrent (flagshipRates e) g x 0 = g*(x.A-x.B*x.z) ∧
    routedCurrent (flagshipRates e) g x 5 = e*(x.B-x.A^2) ∧
    routedCurrent (flagshipRates e) g x 1 = 16*x.z-x.H ∧
    routedCurrent (flagshipRates e) g x 2 = x.H-2*x.z^2 := by
  refine ⟨?_,?_,?_,?_⟩ <;>
    norm_num [routedCurrent,routedForward,routedReverse,routedInput,routedOutput,
      bufferedCoordinates,flagshipRates,Fin.prod_univ_succ,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail,
      vec_eight_fifth] <;> ring

/-- Both cores are productive at one literal positive state, with the same rates.
This witness is not asserted stationary or attracting. -/
theorem routed_common_productive_state (e g : ℝ) (he : 0 < e) (heu : e ≤ 1/50000)
    (hg : (999/1000:ℝ) ≤ g) :
    ∃ x : State, x.Positive ∧
      CoreProductive (routedCurrent (flagshipRates e) g x 0)
        (routedCurrent (flagshipRates e) g x 5) ∧
      CoreProductive (routedCurrent (flagshipRates e) g x 1)
        (routedCurrent (flagshipRates e) g x 2) := by
  have hgp : 0 < g := by linarith
  have hq : 0 < 3*e/(2*g) := by positivity
  have hqu : 3*e/(2*g) < 1 := by
    apply (div_lt_one (by positivity : 0 < 2*g)).2
    linarith
  let z : ℝ := (1-3*e/(2*g))/2
  have hz : 0 < z := by dsimp [z]; linarith
  have hzu : z < 1/2 := by dsimp [z]; linarith
  let x : State := ⟨1,2,z,8*z⟩
  obtain ⟨h₀,h₅,h₁,h₂⟩ := routed_core_current_formulas e g x
  have hj : g*(x.A-x.B*x.z) = 3*e/2 := by
    dsimp [x,z]
    field_simp
    ring
  refine ⟨x,⟨by norm_num [x],by norm_num [x],hz,by dsimp [x]; positivity⟩,?_,?_⟩
  · rw [h₀,h₅,hj]
    dsimp [CoreProductive,x]
    constructor <;> nlinarith
  · rw [h₁,h₂]
    dsimp [CoreProductive,x]
    have hpos := mul_pos hz (show 0 < 2-z by linarith)
    have hz2 := sq_pos_of_pos hz
    constructor <;> nlinarith

theorem gain_two_oriented_currents (j k : ℝ) (h : CoreProductive j k) :
    0 < j ∧ 0 < k := by
  obtain ⟨h₁,h₂⟩ := h
  constructor <;> linarith

/-- Under route isolation the buffered AB and autonomous ZH systems each have
exactly one positive equilibrium, not merely at most one. -/
theorem routed_isolated_modules_unique (e : ℝ) (he : 0 ≤ e) :
    (∃! u : ℝ × ℝ, 0 < u.1 ∧ 0 < u.2 ∧
      fA (flagshipRates e) u.1 u.2 1 = 0 ∧ fB (flagshipRates e) u.1 u.2 1 = 0) ∧
    (∃! u : ℝ × ℝ, 0 < u.1 ∧ 0 < u.2 ∧
      -16*u.1-4*u.1^2+3*u.2 = 0 ∧ fH (flagshipRates e) u.1 u.2 = 0) := by
  obtain ⟨x,hx,hsx⟩ := routed_zero_exists e he
  have hA : fA (flagshipRates e) x.A x.B 1 = 0 := by simpa using hsx.1
  have hB : fB (flagshipRates e) x.A x.B 1 = 0 := by simpa using hsx.2.1
  constructor
  · refine ⟨(x.A,x.B),⟨hx.1,hx.2.1,hA,hB⟩,?_⟩
    intro u hu
    obtain ⟨ha,hb⟩ := isolated_AB_unistationary (flagshipRates e) he 1
      u.1 u.2 x.A x.B (by norm_num) hu.1 hx.1 hu.2.2.1 hu.2.2.2 hA hB
    exact Prod.ext ha hb
  · refine ⟨(x.z,x.H),⟨hx.2.2.1,hx.2.2.2,?_,hsx.2.2.2⟩,?_⟩
    · have hz := hsx.2.2.1
      dsimp [routedZ] at hz
      linarith
    · intro u hu
      let y : State := ⟨x.A,x.B,u.1,u.2⟩
      have hy : y.Positive := ⟨hx.1,hx.2.1,hu.1,hu.2.1⟩
      have hsy : RoutedStationary e 0 y := by
        refine ⟨?_,?_,?_,hu.2.2.2⟩
        · simpa [y] using hA
        · simpa [y] using hB
        · dsimp [routedZ,y]
          linarith [hu.2.2.1]
      have hxy := routed_zero_unique e he y x hy hx hsy hsx
      exact Prod.ext (congrArg State.z hxy) (congrArg State.H hxy)

private theorem vec_eight_seventh {α : Type*} (a b c d e f g h : α) :
    (![a,b,c,d,e,f,g,h] : Fin 8 → α) 7 = h := rfl

theorem routed_buffered_current (e : ℝ) (x : State) :
    routedCurrent (flagshipRates e) 0 x 7 = x.A-x.B := by
  norm_num [routedCurrent,routedForward,routedReverse,routedInput,routedOutput,
    bufferedCoordinates,flagshipRates,Fin.prod_univ_succ,vec_eight_seventh]

/-- The selected buffered AB core remains realizably productive under isolation;
ZH is productive at the same witness state and unchanged intrinsic rates. -/
theorem routed_isolated_productive_state (e : ℝ) (he : 0 < e) :
    ∃ x : State, x.Positive ∧
      CoreProductive (routedCurrent (flagshipRates e) 0 x 7)
        (routedCurrent (flagshipRates e) 0 x 5) ∧
      CoreProductive (routedCurrent (flagshipRates e) 0 x 1)
        (routedCurrent (flagshipRates e) 0 x 2) := by
  let q : ℝ := 1/(4+6*e)
  have hq : 0 < q := by dsimp [q]; positivity
  let x : State := ⟨1/2,1/4+q,1,8⟩
  obtain ⟨_,h₅,h₁,h₂⟩ := routed_core_current_formulas e 0 x
  have hj : x.A-x.B = (3/2)*e*q := by
    dsimp [x,q]
    field_simp
    ring
  have hk : e*(x.B-x.A^2) = e*q := by dsimp [x]; ring
  refine ⟨x,⟨by norm_num [x],by dsimp [x]; positivity,
    by norm_num [x],by norm_num [x]⟩,?_,?_⟩
  · rw [routed_buffered_current,h₅,hj,hk]
    dsimp [CoreProductive]
    have hpos := mul_pos he hq
    constructor <;> nlinarith
  · rw [h₁,h₂]
    norm_num [CoreProductive,x]

/-- Concrete simultaneous certificates for the two embedded gain-two cores.
The ideal irreversible sink is explicit; potential ratios apply to reversible pairs. -/
structure RoutedCoreCertificate (e g : ℝ) : Prop where
  rates_positive : (flagshipRates e).Positive
  AB_embedding : ∀ i r : Fin 2,
    routedInput (![0,1] i) (![0,5] r) = coreInput i r ∧
    routedOutput (![0,1] i) (![0,5] r) = coreOutput i r
  isolated_AB_embedding : ∀ i r : Fin 2,
    routedInput (![0,1] i) (![7,5] r) = coreInput i r ∧
    routedOutput (![0,1] i) (![7,5] r) = coreOutput i r
  ZH_embedding : ∀ i r : Fin 2,
    routedInput (![2,3] i) (![1,2] r) = coreInput i r ∧
    routedOutput (![2,3] i) (![1,2] r) = coreOutput i r
  autonomous : AutonomousRestriction Finset.univ Finset.univ
  reaction_minimal : ∀ j k : ℝ, j=0 ∨ k=0 → ¬ CoreProductive j k
  species_minimal : ∀ S R : Finset (Fin 2), R.Nonempty →
    AutonomousRestriction S R → S=Finset.univ
  common_productive : ∃ x : State, x.Positive ∧
    CoreProductive (routedCurrent (flagshipRates e) g x 0)
      (routedCurrent (flagshipRates e) g x 5) ∧
    CoreProductive (routedCurrent (flagshipRates e) g x 1)
      (routedCurrent (flagshipRates e) g x 2)
  isolated_productive : ∃ x : State, x.Positive ∧
    CoreProductive (routedCurrent (flagshipRates e) 0 x 7)
      (routedCurrent (flagshipRates e) 0 x 5) ∧
    CoreProductive (routedCurrent (flagshipRates e) 0 x 1)
      (routedCurrent (flagshipRates e) 0 x 2)
  mass_balance : ∀ r : Fin 8,
    (∑ i, routedMass i*routedInput i r)+(∑ i, externalMass i*routedExternalInput i r)=
    (∑ i, routedMass i*routedOutput i r)+(∑ i, externalMass i*routedExternalOutput i r)
  reaction_rates : ∀ r : Fin 8, 0 < routedForward (flagshipRates e) g r ∧
    (r ≠ 6 → 0 < routedReverse (flagshipRates e) g r)
  common_potentials : ∀ r : Fin 8, r ≠ 6 →
    routedForward (flagshipRates e) g r/routedReverse (flagshipRates e) g r =
      Real.exp (routedAffinity (flagshipRates e) r)
  ideal_sink : routedReverse (flagshipRates e) g 6 = 0
  fixed_capacity : routedForward (flagshipRates e) g 0+routedForward (flagshipRates e) g 7=1 ∧
    routedReverse (flagshipRates e) g 0+routedReverse (flagshipRates e) g 7=1

theorem routed_core_certificate (e g : ℝ)
    (he : e ∈ Ioo (1/200000:ℝ) (1/50000)) (hg : g ∈ Ioo (999/1000:ℝ) 1) :
    RoutedCoreCertificate e g := by
  have hep : 0 < e := by linarith [he.1]
  have hp : (flagshipRates e).Positive := by
    norm_num [Rates.Positive,flagshipRates]
    exact hep
  have hrate : ∀ r : Fin 8, 0 < routedForward (flagshipRates e) g r ∧
      (r ≠ 6 → 0 < routedReverse (flagshipRates e) g r) := by
    intro r
    constructor
    · fin_cases r <;> norm_num [routedForward,flagshipRates] <;>
        linarith [he.1,hg.1,hg.2]
    · intro hr
      fin_cases r
      all_goals simp_all [routedReverse,flagshipRates,Fin.ext_iff]
      all_goals linarith [he.1,hg.1,hg.2]
  exact ⟨hp,routed_AB_core false,routed_AB_core true,routed_ZH_core,by unfold AutonomousRestriction; decide,
    gain_two_core_reaction_minimal,core_species_minimal,
    routed_common_productive_state e g hep he.2.le hg.1.le,routed_isolated_productive_state e hep,routed_mass_balance,hrate,
    routed_reversible_ratios (flagshipRates e) hp g (by linarith [hg.1]) hg.2,
    rfl,fork_capacity_preserved (flagshipRates e) g⟩

/-- Actual two-core certificates and causal multiplicity at every point of the
same nonempty open parameter region. Stability remains a separate obligation. -/
theorem admissible_routed_multiplicity (e g : ℝ)
    (he : e ∈ Ioo (1/200000:ℝ) (1/50000)) (hg : g ∈ Ioo (999/1000:ℝ) 1) :
    RoutedCoreCertificate e g ∧
    (∃! x : State, x.Positive ∧ RoutedStationary e 0 x) ∧
    ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
      RoutedStationary e g x ∧ RoutedStationary e g y ∧ RoutedStationary e g w ∧
      x.z < y.z ∧ y.z < w.z :=
  ⟨routed_core_certificate e g he hg,routed_open_region_creation e g he hg⟩

end CoreCouplingGlobal
