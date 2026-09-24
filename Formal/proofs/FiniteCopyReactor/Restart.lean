import proofs.FiniteCopyReactor.Source

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding

def stockInteger (N : Counts) : ℕ := 40*N 2+45*N 3+56*N 4+72*N 5
def Restart (V : ℕ) (N : Counts) : Prop :=
  159*(V:ℝ)/160 ≤ uCount N ∧ uCount N ≤ 161*(V:ℝ)/160 ∧
  159*(V:ℝ)/160 ≤ wCount N ∧ wCount N ≤ 161*(V:ℝ)/160 ∧
  2*V ≤ stockInteger N

theorem stock_integer_real (N : Counts) : (stockInteger N : ℝ) = 40*weightedCount N := by
  simp only [stockInteger, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  dsimp [weightedCount, weighted]
  ring

/-- Explicit lattice witness at all positive scales divisible by 1000. -/
theorem restart_witness (k : ℕ) :
    Restart (1000*k) ![934*k,935*k,60*k,k,k,k] := by
  have ha : uCount ![934*k,935*k,60*k,k,k,k] = 1000*(k:ℝ) := by
    rw [uCount_expansion]
    change (↑(934*k):ℝ)+↑(60*k)+2*↑k+2*↑k+2*↑k = _
    push_cast
    ring
  have hb : wCount ![934*k,935*k,60*k,k,k,k] = 1000*(k:ℝ) := by
    rw [wCount_expansion]
    change (↑(935*k):ℝ)+↑(60*k)+↑k+2*↑k+2*↑k = _
    push_cast
    ring
  have hy : stockInteger ![934*k,935*k,60*k,k,k,k] = 2573*k := by
    change 40*(60*k)+45*k+56*k+72*k = _
    omega
  unfold Restart
  rw [ha,hb,hy]
  push_cast
  constructor
  · nlinarith [Nat.cast_nonneg (α := ℝ) k]
  constructor
  · nlinarith [Nat.cast_nonneg (α := ℝ) k]
  constructor
  · nlinarith [Nat.cast_nonneg (α := ℝ) k]
  constructor
  · nlinarith [Nat.cast_nonneg (α := ℝ) k]
  · omega

theorem restart_nonempty (k : ℕ) : ∃ N, Restart (1000*k) N :=
  ⟨_, restart_witness k⟩

end
end FiniteCopyReactor
