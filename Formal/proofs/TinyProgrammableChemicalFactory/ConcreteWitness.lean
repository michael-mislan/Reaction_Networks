import proofs.TinyProgrammableChemicalFactory.Invariants
import proofs.TinyProgrammableChemicalFactory.IntegerBounds

namespace TinyProgrammableChemicalFactory

/-- The literal fueled reaction has the uniform exponential repair-clock bound.
This is the new one-minority mechanism, not an assumed factory probability. -/
theorem literal_repair_clock (γ β ε : ℝ) (hγ : 1000000000≤γ)
    (z : Counts) (hx : 8≤z 0) (hy : z 1=1) (hh : z 5=1) :
    Real.exp (-(rate γ β ε z 10 / 1000000000)) ≤ 1/1000000 ∧
    rate γ β ε z 12=0 := by
  constructor
  · rw [repair_rate γ β ε z hy hh]
    have hf : (56 : ℝ)≤(z 0*(z 0-1) : ℕ) := by
      exact_mod_cast repair_factor_lower (z 0) hx
    have hb : (56 : ℝ)≤γ*(z 0*(z 0-1) : ℕ)/1000000000 := by
      nlinarith
    exact (Real.exp_le_exp.mpr (neg_le_neg hb)).trans repair_exponential_bound
  · exact opposing_majority_vanishes γ β ε z (by omega)

/-- A finite one-event source update removes the minority without adding resident material. -/
theorem corrected_inventory (z : Counts) (hz : restartX z) (hy : z 1=1) :
    coreMass (update z 10)=80 ∧ fuelMass (update z 10)=1 ∧
    (update z 10) 1=0 ∧ 8≤(update z 10) 0 := by
  obtain ⟨hm,hx,_,hp,hq,hh,hw⟩:=hz
  have hx2 : 2≤z 0 := by omega
  have hc:=reaction_conserves z 10 (repair_enabled z hx2 hy hh)
  have hr:=repair_result z hx2 hy hh
  constructor
  · exact hc.1.trans hm
  constructor
  · simpa [fuelMass,hh,hw] using hc.2
  rw [hr]
  simp
  omega

end TinyProgrammableChemicalFactory
