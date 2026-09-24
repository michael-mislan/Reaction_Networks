import proofs.RAF1519.Refinement.CountLocality

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators

inductive PhysicalMark
  | inventory | freeX | foodU | foodW | service
  deriving DecidableEq, Fintype

/-- Collection credits actual template washouts. It does not add observer
    arrivals or credit intermediate washout. -/
def localMarkReward : PhysicalMark → LocalChannel → ℕ
  | .inventory, .inr (.inr s) => match s.val with
    | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 2 | _ => 0
  | .freeX, .inr (.inr s) => if s.val=2 then 1 else 0
  | .foodU, .inr (.inl j) => if j.val=0 then 1 else 0
  | .foodW, .inr (.inl j) => if j.val=1 then 1 else 0
  | .service, .inl (j,_) => if j.val=5 then 1 else 0
  | _, _ => 0

def physicalMarkReward {n : ℕ} (i : Fin n) (m : PhysicalMark) : CountChannel n → ℕ
  | .inl (j,a) => if j=i then localMarkReward m a else 0
  | .inr _ => 0

def markIncrement {n : ℕ} (V : ℝ) (i : Fin n) (m : PhysicalMark)
    (_N : MolecularState n) (a : CountChannel n) : ℝ := (physicalMarkReward i m a:ℝ)/V

theorem localMarkReward_bound (m : PhysicalMark) (a : LocalChannel) : localMarkReward m a ≤ 2 := by
  exact (by decide : ∀ m a, localMarkReward m a ≤ 2) m a

theorem physicalMarkReward_bound {n : ℕ} (i : Fin n) (m : PhysicalMark) (a : CountChannel n) :
    physicalMarkReward i m a ≤ 2 := by
  rcases a with ⟨j,a⟩|a
  · change (if j=i then localMarkReward m a else 0) ≤ 2
    split_ifs
    · exact localMarkReward_bound m a
    · norm_num
  · norm_num [physicalMarkReward]

theorem markIncrement_bound {n : ℕ} (V : ℝ) (hV : 0 < V) (i : Fin n) (m : PhysicalMark)
    (N : MolecularState n) (a : CountChannel n) : |markIncrement V i m N a| ≤ 2/V := by
  unfold markIncrement
  rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hV.le)]
  apply div_le_div_of_nonneg_right _ hV.le
  exact_mod_cast physicalMarkReward_bound i m a

end
end RAF1519.Refinement
