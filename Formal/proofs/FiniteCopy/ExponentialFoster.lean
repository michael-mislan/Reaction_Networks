import proofs.FiniteCopy.Source

namespace FiniteCopy

noncomputable def weightJump (e : ℝ) (r : Fin 13) : ℝ := ∑ i, weight e i*jump r i
noncomputable def exponentialMassRate (e q : ℝ) (x : Point) : ℝ :=
  ∑ r, densityRates e q x r*(Real.exp (weightJump e r/10000)-1)

/-- Upper bounds for individual exponential jump factors, divided by theta. -/
noncomputable def expUpper : Fin 13 → ℝ :=
  ![501/1000,0,20001/40000,-19999/40000,20001/40000,-19999/40000,
    1501/1000,-1499/1000,1001/1000,-999/1000,5001/2500,0,-59991/40000]

lemma exp_small_mono_bound (t b u : ℝ) (ht : t ≤ b) (hb : |b| ≤ 1)
    (hu : 1+b+b^2 ≤ u) : Real.exp t ≤ u := by
  have hx := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hb)).2
  have hm := Real.exp_le_exp.mpr ht
  linarith

theorem exponential_jump_upper (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (r : Fin 13) : Real.exp (weightJump e r/10000)-1 ≤ expUpper r/10000 := by
  fin_cases r <;> norm_num [weightJump, weight, jump, expUpper, Fin.sum_univ_succ]
  · apply exp_small_mono_bound _ (50002/1000000000) _ <;> norm_num
    linarith
  · have h : Real.exp ((-(1/2)-e)/10000) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  · apply exp_small_mono_bound _ (1/20000) _ <;> norm_num
  · apply exp_small_mono_bound _ (-(1/20000)) _ <;> norm_num
  · apply exp_small_mono_bound _ (1/20000) _ <;> norm_num
  · apply exp_small_mono_bound _ (-(1/20000)) _ <;> norm_num
  · apply exp_small_mono_bound _ (150002/1000000000) _ <;> norm_num
    linarith
  · apply exp_small_mono_bound _ (-(3/20000)) _ <;> norm_num
    linarith
  · apply exp_small_mono_bound _ (100004/1000000000) _ <;> norm_num
    linarith
  · apply exp_small_mono_bound _ (-(1/10000)) _ <;> norm_num
    linarith
  · apply exp_small_mono_bound _ (1/5000) _ <;> norm_num
    linarith
  · have h : Real.exp (-(1/5000)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  · apply exp_small_mono_bound _ (-(3/20000)) _ <;> norm_num

theorem exponential_mass_foster (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (N : ℕ) (hN : 1 ≤ N) (n : Counts) :
    exponentialMassRate e (1/(N : ℝ)) (concentration N n) ≤
      (62-mass e (concentration N n)/20000)/10000 := by
  let x := concentration N n
  let q : ℝ := 1/(N : ℝ)
  have hpos (i : Fin 4) : 0 ≤ x i := by dsimp [x, concentration]; positivity
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  have h3 := hpos 3
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : q ≤ 1 := (div_le_one (by linarith)).2 hNr
  have hpair : 0 ≤ x 2*(x 2-q) := lattice_pair_nonneg N (n 2)
  have hsum : exponentialMassRate e q x ≤
      ∑ r, densityRates e q x r*(expUpper r/10000) := by
    apply Finset.sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_left (exponential_jump_upper e he he' r)
      (lattice_rates_nonneg e he N n r)
  have hupper : (∑ r, densityRates e q x r*(expUpper r/10000)) ≤
      (37-99/100*x 0-99/100*x 1+9*x 2-99/100*(x 2)^2-
        99/1000000*x 3)/10000 := by
    norm_num [densityRates, expUpper, Fin.sum_univ_succ]
    have heB := mul_nonneg (sub_nonneg.mpr he') h1
    have hqz := mul_nonneg (sub_nonneg.mpr hq) h2
    nlinarith
  have hrem : (37-99/100*x 0-99/100*x 1+9*x 2-99/100*(x 2)^2-
        99/1000000*x 3)/10000 ≤ (62-mass e x/20000)/10000 := by
    have hA : 0 ≤ 99/100-(e+3/2)/20000 := by linarith
    have hB : 0 ≤ 99/100-(2*e+1)/20000 := by linarith
    have hA' := mul_nonneg hA h0
    have hB' := mul_nonneg hB h1
    norm_num [mass, weight, Fin.sum_univ_succ,
      show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
    nlinarith [sq_nonneg (x 2-5)]
  exact hsum.trans (hupper.trans hrem)

noncomputable def generator (e : ℝ) (N : ℕ) (f : Point → ℝ) (x : Point) : ℝ :=
  (N : ℝ)*∑ r, densityRates e (1/(N : ℝ)) x r *
    (f (fun i => x i+jump r i/(N : ℝ))-f x)

noncomputable def exponentialMass (e : ℝ) (N : ℕ) (x : Point) : ℝ :=
  Real.exp ((N : ℝ)*mass e x/10000)

lemma mass_shift (e q : ℝ) (x : Point) (r : Fin 13) :
    mass e (fun i => x i+q*jump r i) = mass e x+q*weightJump e r := by
  unfold mass weightJump
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem exponential_generator_identity (e : ℝ) (N : ℕ) (hN : 1 ≤ N) (x : Point) :
    generator e N (exponentialMass e N) x =
      (N : ℝ)*exponentialMass e N x*exponentialMassRate e (1/(N : ℝ)) x := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hstep (r : Fin 13) : exponentialMass e N (fun i => x i+jump r i/(N : ℝ)) =
      exponentialMass e N x*Real.exp (weightJump e r/10000) := by
    have hs : (fun i => x i+jump r i/(N : ℝ)) = (fun i => x i+(1/(N : ℝ))*jump r i) := by
      funext i; ring
    rw [hs]
    unfold exponentialMass
    rw [mass_shift, ← Real.exp_add]
    congr 1
    field_simp
  unfold generator exponentialMassRate
  simp_rw [hstep]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem exponential_generator_foster (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (N : ℕ) (hN : 1 ≤ N) (n : Counts) :
    generator e N (exponentialMass e N) (concentration N n) ≤
      (N : ℝ)*exponentialMass e N (concentration N n)*
        ((62-mass e (concentration N n)/20000)/10000) := by
  rw [exponential_generator_identity e N hN]
  exact mul_le_mul_of_nonneg_left (exponential_mass_foster e he he' N hN n)
    (by unfold exponentialMass; positivity)

end FiniteCopy
