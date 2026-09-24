import proofs.ProductiveMemory.ExtractionNoise
import proofs.ProductiveMemory.ExtractionReturn

namespace ProductiveMemory
open FiniteCopy Set
noncomputable section
set_option Elab.async false

def countGenerator (rho : ℝ) (N : ℕ) (W : Point → ℝ) (x : Point) : ℝ :=
  (N:ℝ)*∑ c : ExtractionChannel, channelDensity rho (1/(N:ℝ)) x c*
    (W (fun i => x i+channelJump c i/(N:ℝ))-W x)
def energyExponential (E : Point → ℝ) (N : ℕ) (s x : Point) : ℝ :=
  Real.exp ((N:ℝ)*localAlpha*E (fun i => x i-s i))

theorem channel_rate_sum_upper (rho q : ℝ) (hr : rho ≤ 1/100) (hq : 0 ≤ q)
    (x : Point) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 35) :
    ∑ c : ExtractionChannel, channelDensity rho q x c ≤ 200000 := by
  have hp (c : ExtractionChannel) : channelDensity rho q x c ≤ 10000 := by
    cases c with
    | inl r => exact local_rate_upper x q hq hx r
    | inr r =>
      change rho*x 2 ≤ 10000
      have hh := mul_le_mul_of_nonneg_right hr (hx 2).1
      linarith [(hx 2).2]
  have hh := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hp c)
  norm_num [Fintype.sum_sum_type] at hh ⊢
  linarith only [hh]

theorem low_generator_identity (rho : ℝ) (N : ℕ) (hN : 1 ≤ N) (s x : Point) :
    countGenerator rho N (energyExponential lowExtractionEnergy N s) x =
      (N:ℝ)*energyExponential lowExtractionEnergy N s x*∑ c : ExtractionChannel,
        channelDensity rho (1/(N:ℝ)) x c*(Real.exp (localAlpha*
          (2*lowExtractionPair (fun i => x i-s i) (channelJump c)+(1/(N:ℝ))*lowExtractionEnergy (channelJump c)))-1) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hs (c : ExtractionChannel) : energyExponential lowExtractionEnergy N s (fun i => x i+channelJump c i/(N:ℝ)) =
      energyExponential lowExtractionEnergy N s x*Real.exp (localAlpha*
        (2*lowExtractionPair (fun i => x i-s i) (channelJump c)+(1/(N:ℝ))*lowExtractionEnergy (channelJump c))) := by
    unfold energyExponential
    rw [← Real.exp_add]
    congr 1
    unfold lowExtractionEnergy lowExtractionPair
    field_simp
    ring
  unfold countGenerator
  simp_rw [hs]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem low_count_generator (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N) (n : Counts)
    (hy : ∀ i, |concentration N n i-lift rho z i| ≤ 1/400)
    (hcenter : ∀ i, lift rho z i ≤ 34) :
    countGenerator rho N (energyExponential lowExtractionEnergy N (lift rho z)) (concentration N n) ≤
      localAlpha*energyExponential lowExtractionEnergy N (lift rho z) (concentration N n)*
        (-(N:ℝ)/2*normSq (fun i => concentration N n i-lift rho z i)+100000000) := by
  let x := concentration N n
  let s := lift rho z
  let y : Point := fun i => x i-s i
  let q : ℝ := 1/(N:ℝ)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one hNp).mpr hNr
  have hx (i : Fin 4) : 0 ≤ x i ∧ x i ≤ 35 := by
    constructor
    · dsimp [x,concentration]; positivity
    · have hh := (abs_le.mp (hy i)).2
      change x i-s i ≤ 1/400 at hh
      linarith [hcenter i]
  have hxa (i : Fin 4) : |x i| ≤ 35 := by rw [abs_of_nonneg (hx i).1]; exact (hx i).2
  have hd := low_extraction_dissipation rho z hr hz he y hy
  have hxy : (fun i => lift rho z i+y i) = x := by funext i; dsimp [y,s]; ring
  rw [hxy] at hd
  have hc := mul_le_mul_of_nonneg_left (low_correction_bound y x hy hxa) hq
  have hfirst : (∑ c : ExtractionChannel, channelDensity rho q x c*(2*lowExtractionPair y (channelJump c))) ≤
      -(59/100)*normSq y+10000*q := by
    rw [low_pair_drift,low_pair_correction]
    nlinarith only [hd,hc]
  have ht := extraction_exponential_rate_bound (channelDensity rho q x)
    (fun c => 2*lowExtractionPair y (channelJump c)) (fun c => lowExtractionEnergy (channelJump c)) q (normSq y)
    (extraction_rate_nonneg rho (by linarith [hr.1]) N n)
    (channel_rate_sum_upper rho q hr.2 hq x hx) hq hq1 (normSq_nonneg y) (normSq_small y hy)
    (low_channel_pair_sq y) low_channel_energy hfirst
  rw [low_generator_identity rho N hN]
  have hm := mul_le_mul_of_nonneg_left ht (by unfold energyExponential; positivity : 0 ≤ (N:ℝ)*energyExponential lowExtractionEnergy N s x)
  have hid : (N:ℝ)*energyExponential lowExtractionEnergy N s x*(localAlpha*(-(1/2)*normSq y+100000000*q)) =
      localAlpha*energyExponential lowExtractionEnergy N s x*(-(N:ℝ)/2*normSq y+100000000) := by
    dsimp [q]
    field_simp
  rw [hid] at hm
  exact hm

theorem high_generator_identity (rho : ℝ) (N : ℕ) (hN : 1 ≤ N) (s x : Point) :
    countGenerator rho N (energyExponential highExtractionEnergy N s) x =
      (N:ℝ)*energyExponential highExtractionEnergy N s x*∑ c : ExtractionChannel,
        channelDensity rho (1/(N:ℝ)) x c*(Real.exp (localAlpha*
          (2*highExtractionPair (fun i => x i-s i) (channelJump c)+(1/(N:ℝ))*highExtractionEnergy (channelJump c)))-1) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hs (c : ExtractionChannel) : energyExponential highExtractionEnergy N s (fun i => x i+channelJump c i/(N:ℝ)) =
      energyExponential highExtractionEnergy N s x*Real.exp (localAlpha*
        (2*highExtractionPair (fun i => x i-s i) (channelJump c)+(1/(N:ℝ))*highExtractionEnergy (channelJump c))) := by
    unfold energyExponential
    rw [← Real.exp_add]
    congr 1
    unfold highExtractionEnergy highExtractionPair
    field_simp
    ring
  unfold countGenerator
  simp_rw [hs]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem high_count_generator (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N) (n : Counts)
    (hy : ∀ i, |concentration N n i-lift rho z i| ≤ 1/400)
    (hcenter : ∀ i, lift rho z i ≤ 34) :
    countGenerator rho N (energyExponential highExtractionEnergy N (lift rho z)) (concentration N n) ≤
      localAlpha*energyExponential highExtractionEnergy N (lift rho z) (concentration N n)*
        (-(N:ℝ)/2*normSq (fun i => concentration N n i-lift rho z i)+100000000) := by
  let x := concentration N n
  let s := lift rho z
  let y : Point := fun i => x i-s i
  let q : ℝ := 1/(N:ℝ)
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one hNp).mpr hNr
  have hx (i : Fin 4) : 0 ≤ x i ∧ x i ≤ 35 := by
    constructor
    · dsimp [x,concentration]; positivity
    · have hh := (abs_le.mp (hy i)).2
      change x i-s i ≤ 1/400 at hh
      linarith [hcenter i]
  have hxa (i : Fin 4) : |x i| ≤ 35 := by rw [abs_of_nonneg (hx i).1]; exact (hx i).2
  have hd := high_extraction_dissipation rho z hr hz he y hy
  have hxy : (fun i => lift rho z i+y i) = x := by funext i; dsimp [y,s]; ring
  rw [hxy] at hd
  have hc := mul_le_mul_of_nonneg_left (high_correction_bound y x hy hxa) hq
  have hfirst : (∑ c : ExtractionChannel, channelDensity rho q x c*(2*highExtractionPair y (channelJump c))) ≤
      -(59/100)*normSq y+10000*q := by
    rw [high_pair_drift,high_pair_correction]
    nlinarith only [hd,hc]
  have ht := extraction_exponential_rate_bound (channelDensity rho q x)
    (fun c => 2*highExtractionPair y (channelJump c)) (fun c => highExtractionEnergy (channelJump c)) q (normSq y)
    (extraction_rate_nonneg rho (by linarith [hr.1]) N n)
    (channel_rate_sum_upper rho q hr.2 hq x hx) hq hq1 (normSq_nonneg y) (normSq_small y hy)
    (high_channel_pair_sq y) high_channel_energy hfirst
  rw [high_generator_identity rho N hN]
  have hm := mul_le_mul_of_nonneg_left ht (by unfold energyExponential; positivity : 0 ≤ (N:ℝ)*energyExponential highExtractionEnergy N s x)
  have hid : (N:ℝ)*energyExponential highExtractionEnergy N s x*(localAlpha*(-(1/2)*normSq y+100000000*q)) =
      localAlpha*energyExponential highExtractionEnergy N s x*(-(N:ℝ)/2*normSq y+100000000) := by
    dsimp [q]
    field_simp
  rw [hid] at hm
  exact hm

end
end ProductiveMemory
