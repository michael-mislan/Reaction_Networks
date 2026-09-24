import proofs.RAF1519.Refinement.RelaxedOperating
import proofs.RAF1519.Refinement.Mission

namespace RAF1519.Refinement.Relaxed
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopyReactor Filter
open scoped BigOperators ENNReal
set_option maxHeartbeats 50000

theorem count_small_volume_trivial (V Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hsmall : V ≤ 40/countTolerance Δ) :
    1 ≤ 2*ENNReal.ofReal (Real.exp (-V/(2000000000000*(1+Δ)^3))) := by
  have ha : 0 < 1+Δ := by positivity
  have he : 40/countTolerance Δ = 400000*(1+Δ) := by
    unfold countTolerance relaxedTolerance
    field_simp
    ring
  rw [he] at hsmall
  have hs : 1 ≤ (1+Δ)^2 := by nlinarith
  have hc : 1+Δ ≤ (1+Δ)^3 := by
    have hh := mul_le_mul_of_nonneg_right hs ha.le
    nlinarith
  have hx : V/(2000000000000*(1+Δ)^3) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hex : (1:ℝ) ≤ 2*Real.exp (-V/(2000000000000*(1+Δ)^3)) := by
    have hh := Real.add_one_le_exp (-V/(2000000000000*(1+Δ)^3))
    simp only [neg_div] at hh ⊢
    linarith
  have hh := ENNReal.ofReal_le_ofReal hex
  simpa only [ENNReal.ofReal_one,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ENNReal.ofReal_ofNat] using hh

theorem molecular_coordinate_tail_large {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hsym : ∀ i j, k i j = k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (hlarge : 40/countTolerance Δ ≤ V)
    (initial : MolecularState n) (p : Fin n × Fin 7)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV initial
      (countIntervalFailure r d k V Δ p stop) ≤
      2*ENNReal.ofReal (Real.exp (-V/(2000000000000*(1+Δ)^3))) := by
  have he : countTolerance Δ ≤ 1 := by
    unfold countTolerance relaxedTolerance
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb := molecular_coordinate_budget hn r d k V Δ (countTolerance Δ) hr hd hk hV hΔ hsym hdegree
    (count_tolerance_positive Δ hΔ) he hlarge initial p stop hstop
  exact hb.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (relaxed_exponent_margin V Δ hV hΔ))) 2)

theorem molecular_coordinate_tail {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hsym : ∀ i j, k i j = k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (initial : MolecularState n) (p : Fin n × Fin 7)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV initial
      (countIntervalFailure r d k V Δ p stop) ≤
      2*ENNReal.ofReal (Real.exp (-V/(2000000000000*(1+Δ)^3))) := by
  by_cases hlarge : 40/countTolerance Δ ≤ V
  · exact molecular_coordinate_tail_large hn r d k V Δ hr hd hk hV hΔ hsym hdegree
      hlarge initial p stop hstop
  · exact prob_le_one.trans (count_small_volume_trivial V Δ hΔ (le_of_not_ge hlarge))


theorem molecular_all_coordinate_tail {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hsym : ∀ i j, k i j = k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (initial : MolecularState n)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV initial
      (⋃ p, countIntervalFailure r d k V Δ p stop) ≤
      14*n*ENNReal.ofReal (Real.exp (-V/(2000000000000*(1+Δ)^3))) := by
  calc
    _ ≤ ∑ p, molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV initial
        (countIntervalFailure r d k V Δ p stop) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Fin n × Fin 7,
        2*ENNReal.ofReal (Real.exp (-V/(2000000000000*(1+Δ)^3))) :=
      Finset.sum_le_sum (fun p _ => molecular_coordinate_tail hn r d k V Δ hr hd hk hV hΔ
        hsym hdegree initial p stop hstop)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]; ring


theorem mark_exponent_root_margin (V Δ : ℝ) (hV : 0 ≤ V) (hΔ : 0 ≤ Δ) :
    -V/160000000 ≤ -V/(2000000000000*(1+Δ)^3) := by
  have hc : 1 ≤ (1+Δ)^3 := one_le_pow₀ (by linarith : (1:ℝ) ≤ 1+Δ)
  have hd : (160000000:ℝ) ≤ 2000000000000*(1+Δ)^3 := by linarith
  have hh := div_le_div_of_nonneg_left hV (by norm_num : (0:ℝ) < 160000000) hd
  simpa only [neg_div] using neg_le_neg hh


theorem molecular_operating_noise_tail {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hsym : ∀ i j, k i j=k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (initial : MolecularState n)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV initial
      ((⋃ p, countIntervalFailure r d k V Δ p stop) ∪
       (⋃ p : Fin n × PhysicalMark, markIntervalFailure r d k V p.1 p.2 stop)) ≤
      24*n*ENNReal.ofReal (Real.exp (-V/(2000000000000*(1+Δ)^3))) := by
  have hc := molecular_all_coordinate_tail hn r d k V Δ hr hd hk hV hΔ hsym hdegree initial stop hstop
  have hm := molecular_all_mark_tail hn r d k V (fun i => (hr i).1) hd hk hV initial stop hstop
  have he := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mark_exponent_root_margin V Δ hV.le hΔ))
  have hm' := hm.trans (mul_le_mul_right he (10*(n:ℝ≥0∞)))
  exact (measure_union_le _ _).trans ((add_le_add hc hm').trans_eq (by ring))


theorem molecular_operating_failure {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ) (N : MolecularState n)
    (h0 : ∀ b i, |materialNode b V N i-1| ≤ 1/25)
    (hD : ∀ i, (N (i,6):ℝ)/V ≤ 1101/100000)
    (hY : ∀ i, 12/1000 ≤ stock (concentration V (fun s => N (i,s)))) :
    molecularLaw hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk hV N {z | ¬operatingSuccess V z} ≤
      24*n*ENNReal.ofReal (Real.exp (-V/(2000000000000*(1+Δ)^3))) := by
  let hr0 : ∀ i, 0 ≤ r i := fun i => le_trans (by norm_num) (hr i).1
  let hd0 : ∀ i, 0 ≤ d i := fun i => le_trans (by norm_num) (hd i).1
  let Bad := (⋃ p, countIntervalFailure r d k V Δ p (materialExit V)) ∪
    (⋃ p : Fin n × PhysicalMark, markIntervalFailure r d k V p.1 p.2 (materialExit V))
  have hi := jumpTrajectory_initial_population N (molecularNext r d k) (molecularRate r d k V)
    (molecular_rate_nonnegative r d k V hr0 hd0 hk hV.le)
    (molecular_total_positive hn r d k V hr0 hd0 hk hV)
  have hc := jumpTrajectory_consistent N (molecularNext r d k) (molecularRate r d k V)
    (molecular_rate_nonnegative r d k V hr0 hd0 hk hV.le)
    (molecular_total_positive hn r d k V hr0 hd0 hk hV)
  have hs : ∀ᵐ z ∂molecularLaw hn r d k V hr0 hd0 hk hV N,
      z ∉ Bad → operatingSuccess V z := by
    filter_upwards [hi,hc,molecular_wait_positive hn r d k V hr0 hd0 hk hV N,
      molecular_nonexplosive hn r d k V hr0 hd0 hk hV N] with z hinit hcons hwait hdiv
    intro hz
    have hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V) := by
      intro p hp
      exact hz (Or.inl (Set.mem_iUnion.mpr ⟨p,hp⟩))
    have hmarks : ∀ i m, z ∉ markIntervalFailure r d k V i m (materialExit V) := by
      intro i m hp
      exact hz (Or.inr (Set.mem_iUnion.mpr ⟨(i,m),hp⟩))
    have hevent : ∀ᶠ K in atTop, 4 < waitingSum (fun i => (z (i+1)).2.2) K :=
      hdiv.eventually (eventually_gt_atTop 4)
    obtain ⟨K,hK⟩ := hevent.exists
    have hclock : 4 < prefixElapsed K (Preorder.frestrictLe K z) := by
      rw [prefix_elapsed_holdingClock]
      unfold holdingClock
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (z (i+1)).2.2) K]
      exact hK
    apply operatingSuccess_of_noise r d k V Δ hV hΔ hr hd hk hsym hdegree z hwait hcons hnoise hmarks
      _ _ _ K hclock
    · rw [hinit]; exact h0
    · rw [hinit]; exact hD
    · rw [hinit]; exact hY
  have hb := molecular_operating_noise_tail hn r d k V Δ
    (fun i => ⟨hr0 i,(hr i).2⟩) (fun i => ⟨hd0 i,(hd i).2⟩)
    hk hV hΔ hsym hdegree N (materialExit V) (materialExit_measurable V)
  apply le_trans (measure_mono_ae ?_) hb
  filter_upwards [hs] with z hz
  intro hfail
  by_contra hnb
  exact hfail (hz hnb)


theorem pulse_error_root_budget (n : ℕ) (V Δ : ℝ) (hV : 0 ≤ V) (hΔ : 0 ≤ Δ) :
    4*n*Real.exp (-V/100000)+n*Real.exp (-V/100000000) ≤
      5*n*Real.exp (-V/(2000000000000*(1+Δ)^3)) := by
  have hm := mark_exponent_root_margin V Δ hV hΔ
  have h1 : -V/100000 ≤ -V/160000000 := by linarith
  have h2 : -V/100000000 ≤ -V/160000000 := by linarith
  have he1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h1.trans hm))
    (show 0 ≤ 4*(n:ℝ) by positivity)
  have he2 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h2.trans hm)) (Nat.cast_nonneg (α := ℝ) n)
  linarith


theorem graphPulse_preparation_root_failure {n : ℕ} (N : MolecularState n) (V : ℕ) (hV : 10000 ≤ V)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (p : Fin n → Intervention)
    (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s)))) :
    (graphPulsePMF N p).toMeasure {o | ¬CountPrepared V (postPulseState N V p o)} ≤
      5*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3))) := by
  have hb := (graphPulse_preparation_failure N V hV p hready).trans
    (ENNReal.ofReal_le_ofReal (pulse_error_root_budget n V Δ (Nat.cast_nonneg _) hΔ))
  simpa only [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 5*n),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5),ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast] using hb


theorem pulseFlow_operating_failure {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hV : 10000 ≤ V) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ) (N : MolecularState n) (p : Fin n → Intervention)
    (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s)))) :
    pulseFlowLaw hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk (by exact_mod_cast (show 0 < V by omega)) N p
      {z | ¬operatingSuccess V z} ≤
      29*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3))) := by
  have hV0 : (0:ℝ) < V := by exact_mod_cast (show 0 < V by omega)
  let hr0 : ∀ i, 0 ≤ r i := fun i => le_trans (by norm_num) (hr i).1
  let hd0 : ∀ i, 0 ≤ d i := fun i => le_trans (by norm_num) (hd i).1
  have hb := kernel_failure_bound (graphPulsePMF N p).toMeasure
    (pulseFlowKernel hn r d k V hr0 hd0 hk hV0 N p)
    {o | ¬CountPrepared V (postPulseState N V p o)} (Set.to_countable _).measurableSet
    {z | ¬operatingSuccess V z} (operatingSuccess_measurable V).compl
    (24*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3)))) ?_
  · calc
      _ ≤ (graphPulsePMF N p).toMeasure {o | ¬CountPrepared V (postPulseState N V p o)}+
          24*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3))) := hb
      _ ≤ 5*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3)))+
          24*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3))) :=
        add_le_add (graphPulse_preparation_root_failure N V hV Δ hΔ p hready) le_rfl
      _ = _ := by ring
  · intro o ho
    have hp : CountPrepared V (postPulseState N V p o) := not_not.mp ho
    exact molecular_operating_failure hn r d k V Δ hV0 hΔ hr hd hk hsym hdegree
      (postPulseState N V p o) hp.1 hp.2.1 hp.2.2


theorem molecular_integer_transfer {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) (N : MolecularState n) (p : Fin n → Intervention) :
    ∀ᵐ z ∂molecularLaw hn r d k V hr hd hk hV N,
      operatingSuccess V z → integerCycleSuccess V p z := by
  filter_upwards [molecular_wait_positive hn r d k V hr hd hk hV N,
    molecular_nonexplosive hn r d k V hr hd hk hV N] with z hwait hdiv
  intro hs
  have hevent : ∀ᶠ K in atTop, 4 < waitingSum (fun i => (z (i+1)).2.2) K :=
    hdiv.eventually (eventually_gt_atTop 4)
  obtain ⟨K,hK⟩ := hevent.exists
  have hclock : 4 < prefixElapsed K (Preorder.frestrictLe K z) := by
    rw [prefix_elapsed_holdingClock]
    unfold holdingClock
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (z (i+1)).2.2) K]
    exact hK
  exact integerCycleSuccess_of_operating V hV p z (fun j => (hwait j).le) K hclock hs


theorem pulseFlow_integer_failure {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hV : 10000 ≤ V) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ) (N : MolecularState n) (p : Fin n → Intervention)
    (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s)))) :
    pulseFlowLaw hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk (by exact_mod_cast (show 0 < V by omega)) N p
      {z | ¬integerCycleSuccess V p z} ≤
      29*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3))) := by
  have hV0 : (0:ℝ) < V := by exact_mod_cast (show 0 < V by omega)
  let hr0 : ∀ i, 0 ≤ r i := fun i => le_trans (by norm_num) (hr i).1
  let hd0 : ∀ i, 0 ≤ d i := fun i => le_trans (by norm_num) (hd i).1
  have hmeas : MeasurableSet {z : MolecularPath n | operatingSuccess V z → integerCycleSuccess V p z} := by
    simpa only [imp_iff_not_or,Set.setOf_or] using
      (operatingSuccess_measurable (n := n) V).compl.union (integerCycleSuccess_measurable V p)
  have htransfer : ∀ᵐ z ∂pulseFlowLaw hn r d k V hr0 hd0 hk hV0 N p,
      operatingSuccess V z → integerCycleSuccess V p z := by
    apply Measure.ae_comp_of_ae_ae hmeas
    exact Filter.Eventually.of_forall (fun o =>
      molecular_integer_transfer hn r d k V hr0 hd0 hk hV0 (postPulseState N V p o) p)
  apply le_trans (measure_mono_ae ?_) (pulseFlow_operating_failure hn r d k V hV Δ hΔ hr hd hk hsym hdegree N p hready)
  filter_upwards [htransfer] with z hz
  exact fun hf hs => hf (hz hs)


end
end RAF1519.Refinement.Relaxed
