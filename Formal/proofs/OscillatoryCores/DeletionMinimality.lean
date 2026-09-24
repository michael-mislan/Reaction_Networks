import proofs.OscillatoryCores.FluxCircuit
import proofs.OscillatoryCores.PeriodicMeanFlux

namespace OscillatoryCores

open DUnstableCores
open scoped BigOperators

def trajectoryFlux (k : Fin 5 → ℝ) (x : ℝ → Fin 4 → ℝ)
    (t : ℝ) (j : Fin 5) : ℝ := k j * massActionMonomial source (x t) j

def Solves (k : Fin 5 → ℝ) (x : ℝ → Fin 4 → ℝ) : Prop :=
  ∀ t i, HasDerivAt (fun s => x s i)
    (∑ j, (source.stoich i j : ℝ) * trajectoryFlux k x t j) t

theorem trajectoryFlux_continuous (k : Fin 5 → ℝ) (x : ℝ → Fin 4 → ℝ)
    (hx : ∀ i, Continuous (fun t => x t i)) (j : Fin 5) :
    Continuous (fun t => trajectoryFlux k x t j) := by
  apply continuous_const.mul
  exact continuous_finsetProd _ (fun i _ => (hx i).pow _)

/-- Any nonnegative rate choice with an omitted channel has only constant
positive trajectories returning after a positive time. This covers every
proper reaction deletion, including the empty network, without retuning gaps. -/
theorem proper_deletion_returning_trajectory_constant
    (k : Fin 5 → ℝ) (hk : ∀ j, 0 ≤ k j)
    (j0 : Fin 5) (hj0 : k j0 = 0)
    (x : ℝ → Fin 4 → ℝ) (hpos : ∀ t i, 0 < x t i)
    (hode : Solves k x) (T : ℝ) (hT : 0 < T) (hreturn : x T = x 0) :
    ∀ t, x t = x 0 := by
  have hx (i : Fin 4) : Continuous (fun t => x t i) :=
    continuous_iff_continuousAt.mpr (fun t => (hode t i).continuousAt)
  have hv := trajectoryFlux_continuous k x hx
  let u : Fin 5 → ℝ := fun j => ∫ t in (0 : ℝ)..T, trajectoryFlux k x t j
  have hbalance : ∀ i, ∑ j, (source.stoich i j : ℝ) * u j = 0 :=
    integrated_flux_balanced (fun i j => (source.stoich i j : ℝ)) x
      (trajectoryFlux k x) T hv hode hreturn
  have hu0 : u j0 = 0 := by simp [u, trajectoryFlux, hj0]
  have hu : u = 0 := kernel_zero_of_missing_channel u hbalance j0 hu0
  have hall : ∀ j, k j = 0 := by
    intro j
    by_contra hne
    have hkpos : 0 < k j := lt_of_le_of_ne (hk j) (Ne.symm hne)
    have hupos : 0 < u j := integrated_flux_positive _ T hT (hv j)
      (fun t => mul_pos hkpos (massActionMonomial_pos source (x t) (hpos t) j))
    simp [hu] at hupos
  apply constant_of_zero_velocity x
  intro t i
  simpa [trajectoryFlux, hall] using hode t i

end OscillatoryCores
