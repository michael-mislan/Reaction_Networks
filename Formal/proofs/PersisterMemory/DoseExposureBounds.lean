import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
namespace PersisterMemory
theorem dose_rearrangement (A K T vmax B : ℝ)
    (hden : 0 < K*T+A) (hgap : 0 < vmax*T-B)
    (hb : B ≤ vmax*T*A/(K*T+A)) :
    K*T*B/(vmax*T-B) ≤ A := by
  apply (div_le_iff₀ hgap).2
  have h := (le_div_iff₀ hden).1 hb
  nlinarith
end PersisterMemory
