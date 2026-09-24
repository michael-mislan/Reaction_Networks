import proofs.ProductiveMemory.ExtractionGrowthLocal
import proofs.ResourceLimitedCompetition.SourceDivisionBarrier

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition Set
set_option Elab.async false

theorem extraction_source_growth_ratio (E : Point → ℝ) (P : Point → Point → ℝ)
    (hquad : ∀ y v q, E (fun i => y i-q*v i)=E y-2*q*P y v+q^2*E v)
    (hlower : ∀ y, (1/200)*normSq y ≤ E y)
    (hbox : ∀ v : Point, (∀ i, |v i| ≤ 36) → E v ≤ 211722)
    (hpair : ∀ y v r, 0 ≤ r → (∀ i, |y i| ≤ r) → (∀ i, |v i| ≤ 36) → |P y v| ≤ 5600*r)
    (s : Point) (hs : ∀ i, s i ≤ 34) (hsz : s 2 ≤ 3)
    (N : ℕ) (hN : 1 ≤ N) (c : Compartment) (hNm : N ≤ c.2) (hn : 1 ≤ c.1 2)
    (he : E (fun i => concentration c.2 c.1 i-s i) < 1/32000000) :
    Real.exp ((N : ℝ)*localAlpha*E (fun i =>
      concentration (nextCompartment c (.inr ())).2 (nextCompartment c (.inr ())).1 i-s i)) ≤
      2*Real.exp ((N : ℝ)*localAlpha*E (fun i => concentration c.2 c.1 i-s i)) := by
  let x := concentration c.2 c.1
  let y : Point := fun i => x i-s i
  let v : Point := fun i => x i+membraneDirection i
  let q : ℝ := 1/((c.2 : ℝ)+1)
  have hg := small_growth_energy_geometry c.2 c.1 s hs hsz E hlower he
  have hv := membrane_vector_bounds x hg.2.2.1
  have hp := hpair y v (1/400) (by norm_num) hg.1 hv.1
  have hL : -2*P y v ≤ 36 := by linarith only [(abs_le.mp hp).1]
  have hQ : 0 ≤ E v := by linarith only [hlower v,normSq_nonneg v]
  have hQmax : E v ≤ 211722 := hbox v hv.1
  have hj : (fun i => concentration (nextCompartment c (.inr ())).2
      (nextCompartment c (.inr ())).1 i-s i) = (fun i => y i-q*v i) := by
    funext i
    have h := membrane_concentration_update c (by omega) hn i
    dsimp [y,q,v,x]
    rw [eq_add_of_sub_eq h]
    ring
  rw [hj]
  apply membrane_exponential_ratio (N : ℝ) (c.2 : ℝ) (E y)
    (E (fun i => y i-q*v i)) (-2*P y v) (E v)
    (Nat.cast_nonneg _) (by exact_mod_cast (hN.trans hNm)) (by exact_mod_cast hNm) hL hQ hQmax
  rw [hquad]
  dsimp [q]
  ring

theorem extraction_spatial_identity (rho β lam : ℝ) (N : ℕ)
    (f : Compartment → ℝ) (c : Compartment) :
    growingCompartmentGenerator rho β (fun d => spatialWeight lam N d.2*f d) c =
      spatialWeight lam N c.2*growingCompartmentGenerator rho β f c+
      β*(c.1 2:ℝ)*spatialWeight lam N c.2*(Real.exp lam-1)*f (nextCompartment c (.inr ())) := by
  rw [growing_generator_split,growing_generator_split,spatial_generator_identity]
  ring

theorem extraction_spatial_barrier_drift (β lam rate N k W Wnext g C LW : ℝ)
    (hN : 0 ≤ N) (hβmax : β ≤ 1/100000000000)
    (hlam : lam=1/1000000000000000) (hr : 0 ≤ rate) (hrmax : rate ≤ 8*β*N)
    (hW : 0 ≤ W) (hnext : 0 ≤ Wnext) (hratio : Wnext ≤ 2*W)
    (hg : 0 ≤ g) (hg1 : g ≤ 1) (hC : 0 ≤ C)
    (hk : k=N*localAlpha*innerEnergy/960)
    (hgen : LW ≤ -k*W+k*C) :
    g*LW+rate*g*(Real.exp lam-1)*Wnext ≤ -(k/2)*(g*W)+k*C := by
  subst lam
  have hex0 : 0 ≤ Real.exp (1/1000000000000000 : ℝ)-1 := by
    have h := Real.add_one_le_exp (1/1000000000000000 : ℝ)
    linarith only [h]
  have hex : Real.exp (1/1000000000000000 : ℝ)-1 ≤ 2/1000000000000000 := by
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
      (by norm_num : |(1/1000000000000000 : ℝ)| ≤ 1))).2
    linarith only [h]
  have hterm := mul_le_mul hex hratio hnext (by norm_num : (0:ℝ) ≤ 2/1000000000000000)
  have hterm' := mul_le_mul_of_nonneg_left hterm (mul_nonneg hr hg)
  have hrate := mul_le_mul_of_nonneg_right hrmax (mul_nonneg hg hW)
  have hbet := mul_le_mul_of_nonneg_right hβmax (mul_nonneg hN (mul_nonneg hg hW))
  have hbase := mul_le_mul_of_nonneg_left hgen hg
  have hk0 : 0 ≤ k := by rw [hk]; unfold localAlpha innerEnergy outerEnergy; positivity
  have hfloor := mul_le_mul_of_nonneg_right hg1 (mul_nonneg hk0 hC)
  have hpos := mul_nonneg hN (mul_nonneg hg hW)
  rw [hk] at hbase hfloor ⊢
  unfold localAlpha innerEnergy outerEnergy at hbase hfloor ⊢
  nlinarith only [hterm',hrate,hbet,hbase,hfloor,hpos]

theorem extraction_compartment_spatial_bound (rho β : ℝ) (hβ : 0 ≤ β)
    (hβmax : β ≤ 1/100000000000) (N : ℕ) (c : Compartment)
    (hm : 0 < c.2) (hmmax : c.2 ≤ 2*N)
    (hz : concentration c.2 c.1 2 ≤ 4)
    (f : Compartment → ℝ) (hf : ∀ d, 0 ≤ f d)
    (hratio : f (nextCompartment c (.inr ())) ≤ 2*f c)
    (hgen : growingCompartmentGenerator rho β f c ≤
      -((N : ℝ)*localAlpha*innerEnergy/960)*f c+
      ((N : ℝ)*localAlpha*innerEnergy/960)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2))) :
    growingCompartmentGenerator rho β (fun d => spatialWeight (1/1000000000000000) N d.2*f d) c ≤
      -(((N : ℝ)*localAlpha*innerEnergy/960)/2)*
        (spatialWeight (1/1000000000000000) N c.2*f c)+
      ((N : ℝ)*localAlpha*innerEnergy/960)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  rw [extraction_spatial_identity]
  have hmR : (0 : ℝ) < c.2 := by exact_mod_cast hm
  have hcount : (c.1 2 : ℝ) ≤ 8*(N : ℝ) := by
    have h := (div_le_iff₀ hmR).mp hz
    have hmax : (c.2 : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hmmax
    linarith only [h,hmax]
  have hrate : β*(c.1 2 : ℝ) ≤ 8*β*(N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hcount hβ
    nlinarith only [h]
  have hg : spatialWeight (1/1000000000000000) N c.2 ≤ 1 := by
    unfold spatialWeight
    apply Real.exp_le_one_iff.mpr
    have hmax : (c.2 : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hmmax
    linarith only [hmax]
  exact extraction_spatial_barrier_drift β (1/1000000000000000) (β*(c.1 2 : ℝ)) (N : ℝ)
    ((N : ℝ)*localAlpha*innerEnergy/960) (f c) (f (nextCompartment c (.inr ())))
    (spatialWeight (1/1000000000000000) N c.2)
    (2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) (growingCompartmentGenerator rho β f c)
    (Nat.cast_nonneg _) hβmax rfl (by positivity) hrate (hf c) (hf _) hratio
    (Real.exp_pos _).le hg (by positivity) rfl hgen


end ProductiveMemory
