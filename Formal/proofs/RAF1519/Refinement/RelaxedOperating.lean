import proofs.RAF1519.Refinement.RelaxedStock
import proofs.RAF1519.Refinement.IntegerCycle

namespace RAF1519.Refinement.Relaxed
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 50000

theorem count_inventory_from_stock (V : ℝ) (hV : 0 < V) {n : ℕ}
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (t : ℝ) (i : Fin n)
    (hY : 1029/20000 ≤ countStock V z t i) :
    147/4000 ≤ ProductiveRecovery.inventory (free (fun s => countPath V z t (i,s))) := by
  have hc : ∀ s, 0 ≤ countPath V z t (i,s) := fun s => div_nonneg (Nat.cast_nonneg _) hV.le
  have hf : ProductiveRecovery.Nonneg (free (fun s => countPath V z t (i,s))) := by
    intro p
    fin_cases p <;> simpa [free] using hc _
  have hi := ProductiveRecovery.inventory_lower _ hf
  change (5/7)*countStock V z t i ≤ _ at hi
  linarith

theorem count_service_rate {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (hD : ∀ i, ((z 0).1 (i,6):ℝ)/V ≤ 1101/100000)
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z))
    (t : ℝ) (ht : 0 ≤ t) (ht4 : t ≤ 4) (i : Fin n) :
    service (d i) (1/100) (1/100) (fun s => countPath V z t (i,s)) ≤ 448924/10000000 := by
  have hs := material_no_exit r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0
  have hcoord := countPath_coordinate_bound V hV z (fun j => (hh j).le) hs K t ht ht4 (ht4.trans_lt hK)
  have hmid := intermediate_time_bound r d k V Δ hV hΔ hd hk hsym hdegree z hh hc hnoise h0 hD
    K t ht ht4 (ht4.trans_lt hK) i
  have hx := hcoord (i,2)
  have hy := hcoord (i,6)
  have hm := (intermediate_envelope_margins t _ ht hmid).1
  have hmul := mul_le_mul_of_nonneg_left (show (101/100)*countPath V z t (i,2)+countPath V z t (i,6) ≤ (101/100)*(11/10)+1131/100000 by linarith) (by linarith [(hd i).1] : 0 ≤ d i)
  unfold service
  nlinarith [(hd i).2]

theorem count_operating_compensators {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (hD : ∀ i, ((z 0).1 (i,6):ℝ)/V ≤ 1101/100000)
    (hY : ∀ i, 12/1000 ≤ stock (concentration V (fun s => (z 0).1 (i,s))))
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z)) (i : Fin n) :
    147/4000 ≤ countOutputI V z i ∧ 901/160000 ≤ countOutputX V z i ∧ countTotalService d V z i ≤ 9/50 := by
  have hh0 := fun j => (hh j).le
  have hIint := count_observable_integrable (fun c => ProductiveRecovery.inventory (free c)) V z hh0 K 3 4
    (by norm_num) (by norm_num) hK i
  have hXint := count_observable_integrable (fun c => c 2) V z hh0 K 3 4
    (by norm_num) (by norm_num) hK i
  have hSint := count_observable_integrable (service (d i) (1/100) (1/100)) V z hh0 K 0 4
    (by norm_num) (by norm_num) hK i
  have hIlower : ∀ t ∈ Set.Icc (3:ℝ) 4,
      147/4000 ≤ ProductiveRecovery.inventory (free (fun s => countPath V z t (i,s))) := by
    intro t ht
    have hstock := count_stock_fence r d k V Δ hV hΔ hr hd hk hsym hdegree z hh hc hnoise h0 hD hY
      K t (by linarith [ht.1]) ht.2 (ht.2.trans_lt hK) i
    exact (count_inventory_from_stock V hV z t i (stock_recovered_of_fence t _ (by linarith [ht.1]) hstock))
  have hXlower : ∀ t ∈ Set.Icc (3:ℝ) 4, 901/160000 ≤ countPath V z t (i,2) := by
    intro t ht
    exact (count_phase_output r d k V Δ hV hΔ hr hd hk hsym hdegree z hh hc hnoise h0 hD hY K hK t ht.1 ht.2 i)
  have hSupper : ∀ t ∈ Set.Icc (0:ℝ) 4,
      service (d i) (1/100) (1/100) (fun s => countPath V z t (i,s)) ≤ 448924/10000000 := by
    intro t ht
    exact count_service_rate r d k V Δ hV hΔ hd hk hsym hdegree z hh hc hnoise h0 hD K hK t ht.1 ht.2 i
  have hI := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (147/4000:ℝ)) volume 3 4) hIint hIlower
  have hXout := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (901/160000:ℝ)) volume 3 4) hXint hXlower
  have hS := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 4) (by norm_num) hSint
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (448924/10000000:ℝ)) volume 0 4) hSupper
  norm_num at hI hXout hS
  exact ⟨by simpa only [countOutputI,show (147/4000:ℝ)=147/4000 by rfl] using hI,
    hXout,hS.trans (by norm_num)⟩

theorem material_time_four_margin : (1/25:ℝ)*Real.exp (-4)+18/10000 ≤ 13/5000 := by
  have he : 50 ≤ Real.exp 4 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 4) 8
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hi : Real.exp (-4) ≤ 1/50 := by
    rw [Real.exp_neg,inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 4)).mpr
    linarith
  linarith

theorem material_return_four {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z)) (b : Bool) (i : Fin n) :
    |countMaterial b V z 4 i-1| ≤ 13/5000 :=
  (material_time_bound r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0 K 4
    (by norm_num) le_rfl hK b i).trans material_time_four_margin

theorem count_ready_return {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (hD : ∀ i, ((z 0).1 (i,6):ℝ)/V ≤ 1101/100000)
    (hY : ∀ i, 12/1000 ≤ stock (concentration V (fun s => (z 0).1 (i,s))))
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z)) (i : Fin n) :
    Ready (1/100) (fun s => countPath V z 4 (i,s)) := by
  have ha := material_return_four r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0 K hK false i
  have hb := material_return_four r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0 K hK true i
  have hd4 := intermediate_time_bound r d k V Δ hV hΔ hd hk hsym hdegree z hh hc hnoise h0 hD
    K 4 (by norm_num) le_rfl hK i
  have hdret := (intermediate_envelope_margins 4 _ (by norm_num) hd4).2 rfl
  have hy4 := count_stock_fence r d k V Δ hV hΔ hr hd hk hsym hdegree z hh hc hnoise h0 hD hY
    K 4 (by norm_num) le_rfl hK i
  have hyret := stock_recovered_of_fence 4 _ (by norm_num) hy4
  simp only [countMaterial,materialWeight,← materialA_weighted] at ha
  simp only [countMaterial,materialWeight,← materialB_weighted] at hb
  change 1029/20000 ≤ stock (fun s => countPath V z 4 (i,s)) at hyret
  obtain ⟨haL,haU⟩ := abs_le.mp ha
  obtain ⟨hbL,hbU⟩ := abs_le.mp hb
  refine ⟨?_,⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,by linarith,?_⟩
  · intro s
    exact div_nonneg (Nat.cast_nonneg _) hV.le
  · dsimp only
    linarith

theorem marked_operating_outputs {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (hV : V ≠ 0) (i : Fin n)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ j, 0 < (z (j+1)).2.2)
    (hnoise : ∀ m, z ∉ markIntervalFailure r d k V i m (materialExit V))
    (hsafe : ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1)
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z))
    (hI : 147/4000 ≤ countOutputI V z i) (hX : 901/160000 ≤ countOutputX V z i)
    (hS : countTotalService d V z i ≤ 9/50) :
    143/4000 ≤ markedWindow V i .inventory z 3 4 ∧
    741/160000 ≤ markedWindow V i .freeX z 3 4 ∧
    markedWindow V i .foodU z 0 4 ≤ 4001/1000 ∧
    markedWindow V i .foodW z 0 4 ≤ 4001/1000 ∧
    markedWindow V i .service z 0 4 ≤ 181/1000 := by
  have hi := markedWindow_noise r d k V hV i .inventory z hh (hnoise _) hsafe K 3 4
    (by norm_num) (by norm_num) le_rfl hK
  have hx := markedWindow_noise r d k V hV i .freeX z hh (hnoise _) hsafe K 3 4
    (by norm_num) (by norm_num) le_rfl hK
  have hu := markedWindow_noise r d k V hV i .foodU z hh (hnoise _) hsafe K 0 4
    (by norm_num) (by norm_num) le_rfl hK
  have hw := markedWindow_noise r d k V hV i .foodW z hh (hnoise _) hsafe K 0 4
    (by norm_num) (by norm_num) le_rfl hK
  have hs := markedWindow_noise r d k V hV i .service z hh (hnoise _) hsafe K 0 4
    (by norm_num) (by norm_num) le_rfl hK
  change |markedWindow V i .inventory z 3 4-countOutputI V z i| < 1/1000 at hi
  change |markedWindow V i .freeX z 3 4-countOutputX V z i| < 1/1000 at hx
  change |markedWindow V i .service z 0 4-countTotalService d V z i| < 1/1000 at hs
  norm_num [markRate] at hu hw
  obtain ⟨hi1,hi2⟩ := abs_lt.mp hi
  obtain ⟨hx1,hx2⟩ := abs_lt.mp hx
  obtain ⟨hu1,hu2⟩ := abs_lt.mp hu
  obtain ⟨hw1,hw2⟩ := abs_lt.mp hw
  obtain ⟨hs1,hs2⟩ := abs_lt.mp hs
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- One literal operating period, before adding the pulse's food dose. -/
def operatingSuccess {n : ℕ} (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) : Prop :=
  ∀ i, Ready (1/100) (fun s => countPath V z 4 (i,s)) ∧
    143/4000 ≤ markedWindow V i .inventory z 3 4 ∧
    741/160000 ≤ markedWindow V i .freeX z 3 4 ∧
    markedWindow V i .foodU z 0 4 ≤ 4001/1000 ∧
    markedWindow V i .foodW z 0 4 ≤ 4001/1000 ∧
    markedWindow V i .service z 0 4 ≤ 181/1000

theorem operatingSuccess_measurable {n : ℕ} (V : ℝ) :
    MeasurableSet {z : ℕ → JumpState (MolecularState n) (CountChannel n) | operatingSuccess V z} := by
  have hr : ∀ i : Fin n, MeasurableSet {z : ℕ → JumpState (MolecularState n) (CountChannel n) |
      Ready (1/100) (fun s => countPath V z 4 (i,s))} := by
    intro i
    exact (Set.to_countable {N : MolecularState n |
      Ready (1/100) (concentration V (fun s => N (i,s)))}).measurableSet.preimage
        (molecularStateAt_measurable 4)
  unfold operatingSuccess
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (hr i).inter ((measurableSet_le measurable_const (markedWindow_measurable V i .inventory 3 4)).inter
    ((measurableSet_le measurable_const (markedWindow_measurable V i .freeX 3 4)).inter
    ((measurableSet_le (markedWindow_measurable V i .foodU 0 4) measurable_const).inter
    ((measurableSet_le (markedWindow_measurable V i .foodW 0 4) measurable_const).inter
      (measurableSet_le (markedWindow_measurable V i .service 0 4) measurable_const)))))

theorem operatingSuccess_of_noise {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (hmarks : ∀ i m, z ∉ markIntervalFailure r d k V i m (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (hD : ∀ i, ((z 0).1 (i,6):ℝ)/V ≤ 1101/100000)
    (hY : ∀ i, 12/1000 ≤ stock (concentration V (fun s => (z 0).1 (i,s))))
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z)) : operatingSuccess V z := by
  have hsafe := material_no_exit r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0
  intro i
  have hcomp := count_operating_compensators r d k V Δ hV hΔ hr hd hk hsym hdegree z hh hc
    hnoise h0 hD hY K hK i
  exact ⟨count_ready_return r d k V Δ hV hΔ hr hd hk hsym hdegree z hh hc hnoise h0 hD hY K hK i,
    marked_operating_outputs r d k V hV.ne' i z hh (hmarks i) hsafe K hK hcomp.1 hcomp.2.1 hcomp.2.2⟩

theorem collection_inventory_integer (V Q : ℕ) (hV : 0 < (V:ℝ))
    (hQ : 143/4000 ≤ (Q:ℝ)/(V:ℝ)) : ⌈(V:ℝ)/56⌉₊ ≤ Q := by
  apply Nat.ceil_le.mpr
  have hh := (le_div_iff₀ hV).mp hQ
  linarith

theorem collection_freeX_integer (V Q : ℕ) (hV : 0 < (V:ℝ))
    (hQ : 741/160000 ≤ (Q:ℝ)/(V:ℝ)) : ⌈(V:ℝ)/1080⌉₊ ≤ Q := by
  apply Nat.ceil_le.mpr
  have hh := (le_div_iff₀ hV).mp hQ
  linarith

theorem integerCycleSuccess_of_operating {n : ℕ} (V : ℕ) (hV : 0 < (V:ℝ))
    (p : Fin n → Intervention) (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ j, 0 ≤ (z (j+1)).2.2) (K : ℕ)
    (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z)) (hs : operatingSuccess V z) :
    integerCycleSuccess V p z := by
  have he : ∀ i m a, 0 ≤ a → a ≤ 4 →
      markedWindow V i m z a 4=(naturalMarkedWindow i m z a 4:ℝ)/(V:ℝ) := by
    intro i m a ha hab
    exact markedWindow_natural V i m z hh K a 4 ha hab hK
  intro i
  obtain ⟨hr,hI,hX,hU,hW,hG⟩ := hs i
  rw [he i .inventory 3 (by norm_num) (by norm_num)] at hI
  rw [he i .freeX 3 (by norm_num) (by norm_num)] at hX
  rw [he i .foodU 0 (by norm_num) (by norm_num)] at hU
  rw [he i .foodW 0 (by norm_num) (by norm_num)] at hW
  rw [he i .service 0 (by norm_num) (by norm_num)] at hG
  exact ⟨hr,collection_inventory_integer V _ hV hI,collection_freeX_integer V _ hV hX,
    pulse_food_integer V _ _ hV hU (pulseDose_budget V (p i) 0),
    pulse_food_integer V _ _ hV hW (pulseDose_budget V (p i) 1),gross_service_integer V _ hV hG⟩


end
end RAF1519.Refinement.Relaxed
