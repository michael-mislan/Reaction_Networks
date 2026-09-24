import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
RBC-GEM source columns at commit 43fd381d9eb8a8a4079629012362312960e1c009.
This is a conditional finite-extent accounting result, not a calibrated RBC
operating theorem. Amounts share one fixed volume basis. Any omitted reaction
must be assigned to the explicit signed residual inputs before applying it.
-/
namespace StoredRedCells
noncomputable section

structure Pools where
  nadph : ℝ
  gsh : ℝ
  trx : ℝ
  prx : ℝ
  sulfenic : ℝ
  disulfide : ℝ
  sulfinic : ℝ
  sulfonic : ℝ
  atp : ℝ

structure Extents where
  gsr : ℝ
  gpx : ℝ
  trdr : ℝ
  prxOx : ℝ
  resolution : ℝ
  prxReduction : ℝ
  hyperOne : ℝ
  hyperTwo : ℝ
  catalase : ℝ
  gshSynthesis : ℝ
  prxImport : ℝ
  prxExport : ℝ
  nadphSupply : ℝ
  atpSupply : ℝ
  atpService : ℝ

def advance (x : Pools) (v : Extents) : Pools where
  nadph := x.nadph + v.nadphSupply - v.gsr - v.trdr
  gsh := x.gsh + 2*v.gsr - 2*v.gpx + v.gshSynthesis
  trx := x.trx + v.trdr - v.prxReduction
  prx := x.prx - v.prxOx + v.prxReduction + v.prxImport
  sulfenic := x.sulfenic + v.prxOx - v.resolution - v.hyperOne
  disulfide := x.disulfide + v.resolution - v.prxReduction
  sulfinic := x.sulfinic + v.hyperOne - v.hyperTwo
  sulfonic := x.sulfonic + v.hyperTwo - v.prxExport
  atp := x.atp + v.atpSupply - v.atpService - v.gshSynthesis

def reserve (x : Pools) : ℝ := x.nadph + x.gsh / 2 + x.trx + x.prx
def protective (v : Extents) : ℝ := v.gpx + v.prxOx + 2*v.catalase
def disappearance (v : Extents) : ℝ := protective v + v.hyperOne + v.hyperTwo
def injuryInventory (x : Pools) : ℝ := x.sulfinic + 2*x.sulfonic

/-- Recycling cancels exactly. GSH synthesis and Prx import are genuine inputs
to this restricted inventory; they are not free closed-system production. -/
theorem reserve_identity (x : Pools) (v : Extents) :
    reserve (advance x v) + v.gpx + v.prxOx =
      reserve x + v.nadphSupply + v.gshSynthesis / 2 + v.prxImport := by
  dsimp [reserve, advance]
  ring

/-- Peroxide consumed by hyperoxidation is charged to injury, including exported
damaged protein. Disappearance alone cannot be equated with protective output. -/
theorem injury_identity (x : Pools) (v : Extents) :
    injuryInventory (advance x v) + 2*v.prxExport =
      injuryInventory x + v.hyperOne + v.hyperTwo := by
  dsimp [injuryInventory, advance]
  ring

theorem energy_identity (x : Pools) (v : Extents) :
    (advance x v).atp + v.atpService + v.gshSynthesis = x.atp + v.atpSupply := by
  dsimp [advance]
  ring

/-- A joint bound using the literal ATP cost of the retained GTHS step.
The upstream precursor cost belongs in atpSupply's net accounting or an
explicit extra sink. This is necessary, not sufficient, for operation. -/
theorem joint_capacity (x : Pools) (v : Extents)
    (rmin amin pmax emax cmax imax : ℝ)
    (hr : rmin ≤ reserve (advance x v))
    (ha : amin ≤ (advance x v).atp)
    (hp : v.nadphSupply ≤ pmax) (he : v.atpSupply ≤ emax)
    (hc : 2*v.catalase ≤ cmax) (hi : v.prxImport ≤ imax) :
    protective v + v.atpService / 2 ≤
      reserve x - rmin + pmax + (x.atp + emax - amin)/2 + cmax + imax := by
  have hR := reserve_identity x v
  have hA := energy_identity x v
  dsimp [protective]
  linarith

/-- Prefix obstruction for a closed peroxide balance. All allowed harmful
fates are bounded explicitly by dmax, and all other clearance by omax. -/
theorem prefix_obstruction (x : Pools) (v : Extents)
    (rmin amin pmax emax cmax imax h0 ht hmax dose other dmax omax : ℝ)
    (hr : rmin ≤ reserve (advance x v))
    (ha : amin ≤ (advance x v).atp)
    (hp : v.nadphSupply ≤ pmax) (he : v.atpSupply ≤ emax)
    (hc : 2*v.catalase ≤ cmax) (hi : v.prxImport ≤ imax)
    (hd : v.hyperOne + v.hyperTwo ≤ dmax) (ho : other ≤ omax)
    (hb : ht = h0 + dose - disappearance v - other)
    (hload : hmax - h0 + reserve x - rmin + pmax +
      (x.atp + emax - amin)/2 + cmax + imax + dmax + omax <
      dose + v.atpService/2) :
    hmax < ht := by
  have hC := joint_capacity x v rmin amin pmax emax cmax imax hr ha hp he hc hi
  dsimp [disappearance] at hb
  linarith

end
end StoredRedCells
