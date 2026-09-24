import proofs.RAF1519.Refinement.CountOperatingRates
import proofs.RAF1519.Refinement.HoldingObservable

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

theorem count_observable_integrable {n : ℕ} (φ : State → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hK : b < prefixElapsed K (Preorder.frestrictLe K z)) (i : Fin n) :
    IntervalIntegrable (fun t => φ (fun s => countPath V z t (i,s))) volume a b :=
  holdingObservable_integrable (fun j => (z (j+1)).2.2)
    (fun j => φ (concentration V (fun s => (z j).1 (i,s)))) hh K a b ha hab hK

def countOutputI {n : ℕ} (V : ℝ) (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (i : Fin n) : ℝ :=
  ∫ t in (3:ℝ)..4, ProductiveRecovery.inventory (free (fun s => countPath V z t (i,s)))
def countOutputX {n : ℕ} (V : ℝ) (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (i : Fin n) : ℝ :=
  ∫ t in (3:ℝ)..4, countPath V z t (i,2)
def countTotalService {n : ℕ} (d : Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (i : Fin n) : ℝ :=
  ∫ t in (0:ℝ)..4, service (d i) (1/100) (1/100) (fun s => countPath V z t (i,s))

/-- Bounds for the actual physical-path compensators, with integrability proved
    by the finite holding partition, rather than assumed continuity of counts. -/
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
    4/100 ≤ countOutputI V z i ∧ 7/1000 ≤ countOutputX V z i ∧ countTotalService d V z i ≤ 9/50 := by
  have hh0 := fun j => (hh j).le
  have hIint := count_observable_integrable (fun c => ProductiveRecovery.inventory (free c)) V z hh0 K 3 4
    (by norm_num) (by norm_num) hK i
  have hXint := count_observable_integrable (fun c => c 2) V z hh0 K 3 4
    (by norm_num) (by norm_num) hK i
  have hSint := count_observable_integrable (service (d i) (1/100) (1/100)) V z hh0 K 0 4
    (by norm_num) (by norm_num) hK i
  have hIlower : ∀ t ∈ Set.Icc (3:ℝ) 4,
      4/100 ≤ ProductiveRecovery.inventory (free (fun s => countPath V z t (i,s))) := by
    intro t ht
    have hstock := count_stock_fence r d k V Δ hV hΔ hr hd hk hsym hdegree z hh hc hnoise h0 hD hY
      K t (by linarith [ht.1]) ht.2 (ht.2.trans_lt hK) i
    exact (count_inventory_from_stock V hV z t i (stock_recovered_of_fence t _ (by linarith [ht.1]) hstock)).le
  have hXlower : ∀ t ∈ Set.Icc (3:ℝ) 4, 7/1000 ≤ countPath V z t (i,2) := by
    intro t ht
    exact (count_phase_output r d k V Δ hV hΔ hr hd hk hsym hdegree z hh hc hnoise h0 hD hY K hK t ht.1 ht.2 i).le
  have hSupper : ∀ t ∈ Set.Icc (0:ℝ) 4,
      service (d i) (1/100) (1/100) (fun s => countPath V z t (i,s)) ≤ 448816/10000000 := by
    intro t ht
    exact count_service_rate r d k V Δ hV hΔ hd hk hsym hdegree z hh hc hnoise h0 hD K hK t ht.1 ht.2 i
  have hI := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (4/100:ℝ)) volume 3 4) hIint hIlower
  have hXout := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (7/1000:ℝ)) volume 3 4) hXint hXlower
  have hS := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 4) (by norm_num) hSint
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (448816/10000000:ℝ)) volume 0 4) hSupper
  norm_num at hI hXout hS
  exact ⟨by simpa only [countOutputI,show (4/100:ℝ)=1/25 by norm_num] using hI,
    hXout,hS.trans (by norm_num)⟩

end
end RAF1519.Refinement
