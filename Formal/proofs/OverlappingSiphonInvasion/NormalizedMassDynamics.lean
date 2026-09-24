import proofs.OverlappingSiphonInvasion.NormalizedGrowth

noncomputable section
open Set
namespace OverlappingSiphonInvasion

def extinctionProduct (ru rv rj : ℝ) (k : ℕ) (z : LiftState) : ℝ :=
  massU ru z.1*massV rv z.1*massJ rj z.1^k

theorem normalized_mass_derivatives (p : Rates) (ru rv rj R : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (X : ℝ → LiftState) (t : ℝ)
    (hX : X t ∈ physicalLiftClosure ru rv rj R)
    (hd : HasDerivAt X (normalizedField p ru rv rj (X t)) t) :
    HasDerivAt (fun s => massU ru (X s).1)
      (normalHU p ru (X t).1 ((X t).2 0)*massU ru (X t).1) t ∧
    HasDerivAt (fun s => massV rv (X s).1)
      (normalHV p rv (X t).1 ((X t).2 1)*massV rv (X t).1) t ∧
    HasDerivAt (fun s => massJ rj (X s).1)
      (normalHJ p rj (X t).1 ((X t).2 2) ((X t).2 3)*massJ rj (X t).1) t := by
  have hc := hasDerivAt_pi.1 hd.fst
  obtain ⟨hU,hV,hJ⟩ := closure_mass_identities p ru rv rj R hru hrv hrj (X t) hX
  rw [hU,hV,hJ]
  exact ⟨(hc 1).add ((hc 3).const_mul ru),
    (hc 2).add ((hc 3).const_mul rv),((hc 1).add (hc 2)).add ((hc 3).const_mul rj)⟩

theorem normalized_product_derivative (p : Rates) (ru rv rj R : ℝ) (k : ℕ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (X : ℝ → LiftState) (t : ℝ)
    (hX : X t ∈ physicalLiftClosure ru rv rj R)
    (hd : HasDerivAt X (normalizedField p ru rv rj (X t)) t) :
    HasDerivAt (fun s => extinctionProduct ru rv rj k (X s))
      (normalGrowth p ru rv rj k (X t)*extinctionProduct ru rv rj k (X t)) t := by
  obtain ⟨hU,hV,hJ⟩ := normalized_mass_derivatives p ru rv rj R hru hrv hrj X t hX hd
  cases k with
  | zero => simpa [extinctionProduct,normalGrowth,mul_add,add_mul,mul_comm,mul_left_comm,
      mul_assoc] using hU.mul hV
  | succ n =>
    convert (hU.mul hV).mul (hJ.pow (n+1)) using 1
    simp only [Pi.mul_apply,Pi.pow_apply,Nat.add_sub_cancel,extinctionProduct,normalGrowth,
      pow_succ,Nat.cast_add,Nat.cast_one]
    ring

private theorem scalar_zero_linear (y v : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt y (v t) t) (h0 : y 0 = 0)
    (hy : ∀ t, 0 ≤ t → 0 ≤ y t) (hv : ∀ t, 0 ≤ t → v t ≤ L*y t)
    (t : ℝ) (ht : 0 ≤ t) : y t = 0 := by
  have hg := le_gronwallBound_of_liminf_deriv_right_le (b := t) (K := L) (ε := 0)
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs _ hr => (hd s hs.1).hasDerivWithinAt.liminf_right_slope_le hr)
    (show y 0 ≤ 0 by rw [h0]) (fun s hs => by simpa using hv s hs.1)
  have hh := hg t (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩)
  have hle : y t ≤ 0 := by simpa [gronwallBound] using hh
  exact le_antisymm hle (hy t ht)

/-- A missing mass that vanishes stays zero along the actual lifted field.
The coefficient bound comes from compactness of the physical closure. -/
theorem normalized_massU_zero (p : Rates) (ru rv rj R : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (X : ℝ → LiftState)
    (hX : ∀ t, 0 ≤ t → X t ∈ physicalLiftClosure ru rv rj R)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (normalizedField p ru rv rj (X t)) t)
    (h0 : massU ru (X 0).1 = 0) : ∀ t, 0 ≤ t → massU ru (X t).1 = 0 := by
  let H : LiftState → ℝ := fun z => normalHU p ru z.1 (z.2 0)
  have hc : Continuous H := by dsimp [H,normalHU,privateA,sharedC]; fun_prop
  obtain ⟨M,hM⟩ := (physicalLiftClosure_isCompact ru rv rj R hru hrv hrj).bddAbove_image hc.continuousOn
  have hy : ∀ t, 0 ≤ t → 0 ≤ massU ru (X t).1 := by
    intro t ht
    have hx := (physicalLiftClosure_projection ru rv rj R (X t) (hX t ht)).1
    have ha := hx 1
    have hb := hx 3
    dsimp [massU]
    positivity
  exact scalar_zero_linear (fun t => massU ru (X t).1)
    (fun t => H (X t)*massU ru (X t).1) M
    (fun t ht => (normalized_mass_derivatives p ru rv rj R hru hrv hrj X t (hX t ht) (hd t ht)).1)
    h0 hy (fun t ht => mul_le_mul_of_nonneg_right (hM ⟨X t,hX t ht,rfl⟩) (hy t ht))

theorem normalized_massV_zero (p : Rates) (ru rv rj R : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj) (X : ℝ → LiftState)
    (hX : ∀ t, 0 ≤ t → X t ∈ physicalLiftClosure ru rv rj R)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (normalizedField p ru rv rj (X t)) t)
    (h0 : massV rv (X 0).1 = 0) : ∀ t, 0 ≤ t → massV rv (X t).1 = 0 := by
  let H : LiftState → ℝ := fun z => normalHV p rv z.1 (z.2 1)
  have hc : Continuous H := by dsimp [H,normalHV,privateB,sharedC]; fun_prop
  obtain ⟨M,hM⟩ := (physicalLiftClosure_isCompact ru rv rj R hru hrv hrj).bddAbove_image hc.continuousOn
  have hy : ∀ t, 0 ≤ t → 0 ≤ massV rv (X t).1 := by
    intro t ht
    have hx := (physicalLiftClosure_projection ru rv rj R (X t) (hX t ht)).1
    have ha := hx 2
    have hb := hx 3
    dsimp [massV]
    positivity
  exact scalar_zero_linear (fun t => massV rv (X t).1)
    (fun t => H (X t)*massV rv (X t).1) M
    (fun t ht => (normalized_mass_derivatives p ru rv rj R hru hrv hrj X t (hX t ht) (hd t ht)).2.1)
    h0 hy (fun t ht => mul_le_mul_of_nonneg_right (hM ⟨X t,hX t ht,rfl⟩) (hy t ht))

end OverlappingSiphonInvasion
