import proofs.ProductiveMemory.ExtractionRegions
import proofs.ProductiveMemory.ExtractionEnvelope
import proofs.ProductiveMemory.ExtractionStoppedDecay
import proofs.FiniteCopy.WellDomains

namespace ProductiveMemory
open FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

theorem low_extraction_root_upper (rho z : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000)) (i : Fin 4) : lift rho z i ≤ 34 := by
  have hb := low_extraction_box rho z hr hz
  apply lift_coordinate_upper rho z _ _ _ i
  · constructor <;> linarith [hz.1,hz.2]
  · linarith [hb.1.2]
  · linarith [hb.2.2]

def lowExtractionWell (rho z : ℝ) (N : ℕ) (b : ℝ) : Finset Counts :=
  energyDomain N (lift rho z) lowExtractionEnergy b

theorem low_extraction_generator_ceiling (rho z : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N) (n : Counts)
    (hy : ∀ i, |concentration N n i-lift rho z i| ≤ 1/400) :
    countGenerator rho N (energyExponential lowExtractionEnergy N (lift rho z)) (concentration N n) ≤ extractionCeiling := by
  let y : Point := fun i => concentration N n i-lift rho z i
  exact (low_count_generator rho z hr hz he N hN n hy (low_extraction_root_upper rho z hr hz)).trans
    (extraction_drift_envelope (N:ℝ) (normSq y) (lowExtractionEnergy y) (Nat.cast_nonneg N)
      (normSq_nonneg y) (lowExtractionEnergy_upper y))

theorem low_extraction_exit_bound (rho z : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N)
    (b : ℝ) (hb : b ≤ 1/32000000) (q t : ℝ≥0) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (extractionStoppedModel rho (by linarith [hr.1]) N (lowExtractionWell rho z N b)).total s ≤ q)
    (n : {n : Counts // n ∈ lowExtractionWell rho z N b}) :
    Real.exp ((N:ℝ)*localAlpha*b)*
      ((extractionStoppedModel rho (by linarith [hr.1]) N (lowExtractionWell rho z N b)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator {none}) (some n) ≤
      energyExponential lowExtractionEnergy N (lift rho z) (concentration N n.val)+(t:ℝ)*extractionCeiling := by
  classical
  let s := lift rho z
  have hmem (m : Counts) : m ∈ lowExtractionWell rho z N b ↔ lowExtractionEnergy (fun i => concentration N m i-s i) < b :=
    mem_energyDomain N hN m s (low_extraction_root_upper rho z hr hz) lowExtractionEnergy lowExtractionEnergy_lower b hb
  apply extraction_stopped_source_event_bound rho (by linarith [hr.1]) N
    (lowExtractionWell rho z N b) (energyExponential lowExtractionEnergy N s)
    (Real.exp ((N:ℝ)*localAlpha*b)) extractionCeiling (Real.exp_pos _).le extractionCeiling_nonneg
  · intro m _; exact (Real.exp_pos _).le
  · intro m _ c _ hout
    have hE : b ≤ lowExtractionEnergy (fun i => concentration N (channelNext m c) i-s i) :=
      le_of_not_gt (fun h => hout ((hmem _).mpr h))
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hE (by unfold localAlpha; positivity)
  · intro m hm
    apply low_extraction_generator_ceiling rho z hr hz he N hN m
    exact small_energy_coordinates lowExtractionEnergy lowExtractionEnergy_lower _ (((hmem m).mp hm).trans_le hb)

def lowExtractionAnnulus (rho z : ℝ) (N : ℕ) (a b : ℝ) : Finset Counts := by
  classical
  exact (lowExtractionWell rho z N b).filter (fun n => a < lowExtractionEnergy (fun i => concentration N n i-lift rho z i))

theorem low_extraction_annulus_bound (rho z : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N)
    (a b : ℝ) (hb : b ≤ 1/32000000) (hNa : 240*100000000 ≤ (N:ℝ)*a)
    (q t : ℝ≥0) (hq : 0 < (q:ℝ)) (hkq : (N:ℝ)*localAlpha*a/240 ≤ q)
    (hclock : ∀ s, (extractionStoppedModel rho (by linarith [hr.1]) N (lowExtractionAnnulus rho z N a b)).total s ≤ q)
    (n : {n : Counts // n ∈ lowExtractionAnnulus rho z N a b}) :
    ((extractionStoppedModel rho (by linarith [hr.1]) N (lowExtractionAnnulus rho z N a b)).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {s | s ≠ none}) (some n) ≤
      Real.exp (-((N:ℝ)*localAlpha*a/240)*(t:ℝ))*energyExponential lowExtractionEnergy N (lift rho z) (concentration N n.val) := by
  classical
  let s := lift rho z
  have hmem (m : Counts) (hm : m ∈ lowExtractionAnnulus rho z N a b) :
      a < lowExtractionEnergy (fun i => concentration N m i-s i) ∧ lowExtractionEnergy (fun i => concentration N m i-s i) < b := by
    have hh := Finset.mem_filter.mp hm
    exact ⟨hh.2,(mem_energyDomain N hN m s (low_extraction_root_upper rho z hr hz) lowExtractionEnergy lowExtractionEnergy_lower b hb).mp hh.1⟩
  apply extraction_killed_survival_bound rho (by linarith [hr.1]) N
    (lowExtractionAnnulus rho z N a b) (energyExponential lowExtractionEnergy N s) (fun _ => (Real.exp_pos _).le)
    ?_ ((N:ℝ)*localAlpha*a/240) ?_ q t hq hkq hclock n
  · intro m _
    apply Real.one_le_exp_iff.mpr
    have hE := lowExtractionEnergy_lower (fun i => concentration N m i-s i)
    have hnon : 0 ≤ lowExtractionEnergy (fun i => concentration N m i-s i) :=
      (mul_nonneg (by norm_num) (normSq_nonneg _)).trans hE
    exact mul_nonneg (by unfold localAlpha; positivity) hnon
  · intro m hm
    let y : Point := fun i => concentration N m i-s i
    have hmE := hmem m hm
    have hy := small_energy_coordinates lowExtractionEnergy lowExtractionEnergy_lower y (hmE.2.trans_le hb)
    exact (low_count_generator rho z hr hz he N hN m hy (low_extraction_root_upper rho z hr hz)).trans
      (extraction_decay_envelope (N:ℝ) (normSq y) (lowExtractionEnergy y) a (Nat.cast_nonneg N) (lowExtractionEnergy_upper y) hmE.1.le hNa)

theorem high_extraction_root_upper (rho z : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000)) (i : Fin 4) : lift rho z i ≤ 34 := by
  have hb := high_extraction_box rho z hr hz
  apply lift_coordinate_upper rho z _ _ _ i
  · constructor <;> linarith [hz.1,hz.2]
  · linarith [hb.1.2]
  · linarith [hb.2.2]

def highExtractionWell (rho z : ℝ) (N : ℕ) (b : ℝ) : Finset Counts :=
  energyDomain N (lift rho z) highExtractionEnergy b

theorem high_extraction_generator_ceiling (rho z : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N) (n : Counts)
    (hy : ∀ i, |concentration N n i-lift rho z i| ≤ 1/400) :
    countGenerator rho N (energyExponential highExtractionEnergy N (lift rho z)) (concentration N n) ≤ extractionCeiling := by
  let y : Point := fun i => concentration N n i-lift rho z i
  exact (high_count_generator rho z hr hz he N hN n hy (high_extraction_root_upper rho z hr hz)).trans
    (extraction_drift_envelope (N:ℝ) (normSq y) (highExtractionEnergy y) (Nat.cast_nonneg N)
      (normSq_nonneg y) (highExtractionEnergy_upper y))

theorem high_extraction_exit_bound (rho z : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N)
    (b : ℝ) (hb : b ≤ 1/32000000) (q t : ℝ≥0) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (extractionStoppedModel rho (by linarith [hr.1]) N (highExtractionWell rho z N b)).total s ≤ q)
    (n : {n : Counts // n ∈ highExtractionWell rho z N b}) :
    Real.exp ((N:ℝ)*localAlpha*b)*
      ((extractionStoppedModel rho (by linarith [hr.1]) N (highExtractionWell rho z N b)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator {none}) (some n) ≤
      energyExponential highExtractionEnergy N (lift rho z) (concentration N n.val)+(t:ℝ)*extractionCeiling := by
  classical
  let s := lift rho z
  have hmem (m : Counts) : m ∈ highExtractionWell rho z N b ↔ highExtractionEnergy (fun i => concentration N m i-s i) < b :=
    mem_energyDomain N hN m s (high_extraction_root_upper rho z hr hz) highExtractionEnergy highExtractionEnergy_lower b hb
  apply extraction_stopped_source_event_bound rho (by linarith [hr.1]) N
    (highExtractionWell rho z N b) (energyExponential highExtractionEnergy N s)
    (Real.exp ((N:ℝ)*localAlpha*b)) extractionCeiling (Real.exp_pos _).le extractionCeiling_nonneg
  · intro m _; exact (Real.exp_pos _).le
  · intro m _ c _ hout
    have hE : b ≤ highExtractionEnergy (fun i => concentration N (channelNext m c) i-s i) :=
      le_of_not_gt (fun h => hout ((hmem _).mpr h))
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hE (by unfold localAlpha; positivity)
  · intro m hm
    apply high_extraction_generator_ceiling rho z hr hz he N hN m
    exact small_energy_coordinates highExtractionEnergy highExtractionEnergy_lower _ (((hmem m).mp hm).trans_le hb)

def highExtractionAnnulus (rho z : ℝ) (N : ℕ) (a b : ℝ) : Finset Counts := by
  classical
  exact (highExtractionWell rho z N b).filter (fun n => a < highExtractionEnergy (fun i => concentration N n i-lift rho z i))

theorem high_extraction_annulus_bound (rho z : ℝ) (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (he : extractDrift rho 0 (lift rho z) = 0) (N : ℕ) (hN : 1 ≤ N)
    (a b : ℝ) (hb : b ≤ 1/32000000) (hNa : 240*100000000 ≤ (N:ℝ)*a)
    (q t : ℝ≥0) (hq : 0 < (q:ℝ)) (hkq : (N:ℝ)*localAlpha*a/240 ≤ q)
    (hclock : ∀ s, (extractionStoppedModel rho (by linarith [hr.1]) N (highExtractionAnnulus rho z N a b)).total s ≤ q)
    (n : {n : Counts // n ∈ highExtractionAnnulus rho z N a b}) :
    ((extractionStoppedModel rho (by linarith [hr.1]) N (highExtractionAnnulus rho z N a b)).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {s | s ≠ none}) (some n) ≤
      Real.exp (-((N:ℝ)*localAlpha*a/240)*(t:ℝ))*energyExponential highExtractionEnergy N (lift rho z) (concentration N n.val) := by
  classical
  let s := lift rho z
  have hmem (m : Counts) (hm : m ∈ highExtractionAnnulus rho z N a b) :
      a < highExtractionEnergy (fun i => concentration N m i-s i) ∧ highExtractionEnergy (fun i => concentration N m i-s i) < b := by
    have hh := Finset.mem_filter.mp hm
    exact ⟨hh.2,(mem_energyDomain N hN m s (high_extraction_root_upper rho z hr hz) highExtractionEnergy highExtractionEnergy_lower b hb).mp hh.1⟩
  apply extraction_killed_survival_bound rho (by linarith [hr.1]) N
    (highExtractionAnnulus rho z N a b) (energyExponential highExtractionEnergy N s) (fun _ => (Real.exp_pos _).le)
    ?_ ((N:ℝ)*localAlpha*a/240) ?_ q t hq hkq hclock n
  · intro m _
    apply Real.one_le_exp_iff.mpr
    have hE := highExtractionEnergy_lower (fun i => concentration N m i-s i)
    have hnon : 0 ≤ highExtractionEnergy (fun i => concentration N m i-s i) :=
      (mul_nonneg (by norm_num) (normSq_nonneg _)).trans hE
    exact mul_nonneg (by unfold localAlpha; positivity) hnon
  · intro m hm
    let y : Point := fun i => concentration N m i-s i
    have hmE := hmem m hm
    have hy := small_energy_coordinates highExtractionEnergy highExtractionEnergy_lower y (hmE.2.trans_le hb)
    exact (high_count_generator rho z hr hz he N hN m hy (high_extraction_root_upper rho z hr hz)).trans
      (extraction_decay_envelope (N:ℝ) (normSq y) (highExtractionEnergy y) a (Nat.cast_nonneg N) (highExtractionEnergy_upper y) hmE.1.le hNa)

end
end ProductiveMemory
