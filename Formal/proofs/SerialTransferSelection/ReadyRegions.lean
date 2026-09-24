import proofs.FiniteCopy.InitialLattice
import proofs.HeritableCompositions.SourceAffine

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

def ReadyCell (N : ℕ) (s : Point) (E : Point → ℝ) (c : Compartment) : Prop :=
  N ≤ c.2 ∧ c.2 < 2*N ∧ E (fun i => concentration c.2 c.1 i-s i) ≤ innerEnergy

/-- Every admitted division phase has an integer low-state ready preparation. -/
theorem low_ready_nonempty (z : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (N m : ℕ) (hN : 1000000000000 ≤ N) (hm : N ≤ m) (hm' : m < 2*N) :
    ∃ n : Counts, ReadyCell N (pointOfState (lift sourceRates z)) lowEnergy (n,m) := by
  obtain ⟨n,_,hn⟩ := low_initial_lattice_nonempty z hz m (hN.trans hm)
  refine ⟨n,hm,hm',?_⟩
  change lowEnergy (fun i => concentration m n i-pointOfState (lift sourceRates z) i) ≤ innerEnergy
  norm_num [innerEnergy,outerEnergy]
  linarith only [hn]

/-- Every admitted division phase has an integer high-state ready preparation. -/
theorem high_ready_nonempty (z : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (N m : ℕ) (hN : 1000000000000 ≤ N) (hm : N ≤ m) (hm' : m < 2*N) :
    ∃ n : Counts, ReadyCell N (pointOfState (lift sourceRates z)) highEnergy (n,m) := by
  obtain ⟨n,_,hn⟩ := high_initial_lattice_nonempty z hz m (hN.trans hm)
  refine ⟨n,hm,hm',?_⟩
  change highEnergy (fun i => concentration m n i-pointOfState (lift sourceRates z) i) ≤ innerEnergy
  norm_num [innerEnergy,outerEnergy]
  linarith only [hn]

theorem nested_recovery_thresholds :
    (0 : ℝ) < innerEnergy ∧ innerEnergy < 4*innerEnergy ∧
      4*innerEnergy < 8*innerEnergy ∧ 8*innerEnergy < outerEnergy := by
  norm_num [innerEnergy,outerEnergy]

end SerialTransferSelection
