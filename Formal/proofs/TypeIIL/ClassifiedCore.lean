import proofs.TypeIIL.CyclicChain
import proofs.TypeII3.Network.QuotientAllZero

namespace TypeIIL

open TypeII3

/-- The two minimal normal forms left by the published Type II_l
classification once the core-minimality condition is enforced: strictly
separated back-branch endpoints (with arbitrary finite unit subdivisions),
and the exceptional fully coincident three-fork quotient.

Mixed coincidences are deliberately absent: they expose a proper
autocatalytic restriction.  `SourceCounterexample.lean` demonstrates that
dropping minimality would genuinely change the theorem. -/
inductive ClassifiedSourceTypeIILCore : ℕ → Type
  | positive {l : ℕ} (data : CyclicChainData l) : ClassifiedSourceTypeIILCore l
  | allZeroThree (data : AllZeroParams) : ClassifiedSourceTypeIILCore 3

def ClassifiedSourceTypeIILState :
    {l : ℕ} → ClassifiedSourceTypeIILCore l → Type
  | _, .positive data => CyclicChainState data
  | _, .allZeroThree _ => AllZeroState

def PositiveClassifiedSourceTypeIILState :
    {l : ℕ} → (D : ClassifiedSourceTypeIILCore l) →
      ClassifiedSourceTypeIILState D → Prop
  | _, .positive _, x => PositiveCyclicChainState x
  | _, .allZeroThree _, x => PositiveAllZeroState x

def IsClassifiedSourceTypeIILStationary :
    {l : ℕ} → (D : ClassifiedSourceTypeIILCore l) →
      ClassifiedSourceTypeIILState D → Prop
  | _, .positive _, x => IsCyclicChainStationary x
  | _, .allZeroThree p, x => IsAllZeroStationary p x

/-- Terminal source-normal-form result: every positive stationary state of a
minimal Type II_l core, l >= 3, is unique. -/
theorem classified_source_typeII_l_unistationarity
    {l : ℕ} (hl : 3 ≤ l) (D : ClassifiedSourceTypeIILCore l)
    (x y : ClassifiedSourceTypeIILState D)
    (hx : PositiveClassifiedSourceTypeIILState D x)
    (hy : PositiveClassifiedSourceTypeIILState D y)
    (hxs : IsClassifiedSourceTypeIILStationary D x)
    (hys : IsClassifiedSourceTypeIILStationary D y) : x = y := by
  cases D with
  | positive data =>
      letI : NeZero l := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hl)⟩
      exact cyclic_chain_unistationarity data x y hx hy hxs hys
  | allZeroThree data =>
      exact all_zero_unistationarity data x y hx hy hxs hys

end TypeIIL
