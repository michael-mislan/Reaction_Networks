import proofs.HeritableCompositions.Lineage
import proofs.FiniteCopy.InitialLattice

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

noncomputable def compositionalReadout (n : Counts) : ℝ := 10*(n 2 : ℝ)-(n 1 : ℝ)

theorem readout_scaling (n : Counts) (N : ℕ) (hN : 0 < N) :
    compositionalReadout n = (10*concentration N n 2-concentration N n 1)*(N : ℝ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have h₂ : concentration N n 2*(N : ℝ) = (n 2 : ℝ) := div_mul_cancel₀ _ hNr
  have h₁ : concentration N n 1*(N : ℝ) = (n 1 : ℝ) := div_mul_cancel₀ _ hNr
  unfold compositionalReadout
  nlinarith only [h₂,h₁]

theorem low_birth_nonempty (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1000000000000 ≤ N) :
    Nonempty (BirthCount (lowCertificate z γ hz hs hγ hγmax) N) := by
  obtain ⟨n,_,hn⟩ := low_initial_lattice_nonempty z hz N hN
  refine ⟨⟨n,(mem_birthDomain (lowCertificate z γ hz hs hγ hγmax) N (by omega) n).mpr ?_⟩⟩
  change lowEnergy (fun i => concentration N n i-pointOfState (lift sourceRates z) i) ≤ 4*innerEnergy
  norm_num [innerEnergy,outerEnergy]
  linarith only [hn]

theorem low_birth_readout (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (n : BirthCount (lowCertificate z γ hz hs hγ hγmax) N) :
    compositionalReadout n.val < 0 := by
  have hbirth := (mem_birthDomain (lowCertificate z γ hz hs hγ hγmax) N hN n.val).mp n.property
  have he : lowEnergy (fun i => concentration N n.val i-pointOfState (lift sourceRates z) i) < 1/32000000 := by
    change lowEnergy (fun i => concentration N n.val i-pointOfState (lift sourceRates z) i) ≤ 4*innerEnergy at hbirth
    norm_num [innerEnergy,outerEnergy] at hbirth ⊢
    linarith only [hbirth]
  have hy := small_energy_coordinates lowEnergy lowEnergy_lower _ he
  have hy₁ := abs_le.mp (hy 1)
  have hy₂ := abs_le.mp (hy 2)
  change -(1/400) ≤ concentration N n.val 1-reducedB sourceRates z ∧
    concentration N n.val 1-reducedB sourceRates z ≤ 1/400 at hy₁
  change -(1/400) ≤ concentration N n.val 2-z ∧ concentration N n.val 2-z ≤ 1/400 at hy₂
  have hb := low_source_box z hz
  have hread : 10*concentration N n.val 2-concentration N n.val 1 < 0 := by
    linarith only [hy₁.1,hy₂.2,hb.2.1.1,hz.2]
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [readout_scaling n.val N (by omega)]
  simpa only [zero_mul] using mul_lt_mul_of_pos_right hread hNr

theorem high_birth_nonempty (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1000000000000 ≤ N) :
    Nonempty (BirthCount (highCertificate z γ hz hs hγ hγmax) N) := by
  obtain ⟨n,_,hn⟩ := high_initial_lattice_nonempty z hz N hN
  refine ⟨⟨n,(mem_birthDomain (highCertificate z γ hz hs hγ hγmax) N (by omega) n).mpr ?_⟩⟩
  change highEnergy (fun i => concentration N n i-pointOfState (lift sourceRates z) i) ≤ 4*innerEnergy
  norm_num [innerEnergy,outerEnergy]
  linarith only [hn]

theorem high_birth_readout (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (n : BirthCount (highCertificate z γ hz hs hγ hγmax) N) :
    0 < compositionalReadout n.val := by
  have hbirth := (mem_birthDomain (highCertificate z γ hz hs hγ hγmax) N hN n.val).mp n.property
  have he : highEnergy (fun i => concentration N n.val i-pointOfState (lift sourceRates z) i) < 1/32000000 := by
    change highEnergy (fun i => concentration N n.val i-pointOfState (lift sourceRates z) i) ≤ 4*innerEnergy at hbirth
    norm_num [innerEnergy,outerEnergy] at hbirth ⊢
    linarith only [hbirth]
  have hy := small_energy_coordinates highEnergy highEnergy_lower _ he
  have hy₁ := abs_le.mp (hy 1)
  have hy₂ := abs_le.mp (hy 2)
  change -(1/400) ≤ concentration N n.val 1-reducedB sourceRates z ∧
    concentration N n.val 1-reducedB sourceRates z ≤ 1/400 at hy₁
  change -(1/400) ≤ concentration N n.val 2-z ∧ concentration N n.val 2-z ≤ 1/400 at hy₂
  have hb := high_source_box z hz
  have hread : 0 < 10*concentration N n.val 2-concentration N n.val 1 := by
    linarith only [hy₁.2,hy₂.1,hb.2.1.2,hz.1]
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [readout_scaling n.val N (by omega)]
  simpa only [zero_mul] using mul_lt_mul_of_pos_right hread hNr

end HeritableCompositions

