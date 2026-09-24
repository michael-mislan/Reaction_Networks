import proofs.CompositionalMemory.SemenovStructure
import proofs.FiniteCopy.FiniteJump

namespace CompositionalMemory.Semenov
open FiniteCopy

/-- A finite resident cap and finite cumulative feed inventory. None denotes
an absorbing failed reactor. The count cap is not a reflecting boundary. -/
abbrev ReactorState (B K : ℕ) := Option ((Fin 8 → Fin (B+1)) × Fin K)
abbrev Channel := (Fin 11) ⊕ (Fin 8 ⊕ Fin 8)

def reactantA : Fin 11 → Fin 8 := ![4,1,4,1,6,2,0,0,1,2,3]
def reactantB : Fin 11 → Fin 8 := ![3,5,2,6,3,5,1,0,7,7,7]
noncomputable def nominalRate (r : Fin 11) : ℝ :=
  if r.val<6 then 13/20 else if r.val=6 then 41/100 else
    if r.val=7 then 463/50000000 else 150
noncomputable def nominalFeed (j : Fin 8) : ℝ := feed (1/20) (1/10) (231/100000) j

def encodeReactor (B K : ℕ) (n : Fin 8 → ℕ) (c : ℕ) : ReactorState B K :=
  if h : (∀ j,n j ≤ B) ∧ c<K then some (fun j => ⟨n j,Nat.lt_succ_of_le (h.1 j)⟩,⟨c,h.2⟩)
  else none

def rawChemicalNext (n : Fin 8 → ℕ) (r : Fin 11) (j : Fin 8) : ℕ :=
  n j+(stoich r j).toNat-(-(stoich r j)).toNat

def reactorNext (B K : ℕ) : ReactorState B K → Channel → ReactorState B K
  | none,_ => none
  | some (n,c),Sum.inl r => encodeReactor B K (rawChemicalNext (fun j => (n j).val) r) c.val
  | some (n,c),Sum.inr (Sum.inl j) =>
      encodeReactor B K (fun i => (n i).val+if i=j then 1 else 0) (c.val+1)
  | some (n,c),Sum.inr (Sum.inr j) =>
      encodeReactor B K (fun i => (n i).val-if i=j then 1 else 0) c.val

noncomputable def reactorRate (Ω : ℝ) {B K : ℕ} : ReactorState B K → Channel → ℝ
  | none,_ => 0
  | some (n,_),Sum.inl r =>
      if r.val=7 then nominalRate r*(n (reactantA r)).val else
        nominalRate r*(n (reactantA r)).val*(n (reactantB r)).val/Ω
  | some _,Sum.inr (Sum.inl j) => Ω*(1/500)*nominalFeed j
  | some (n,_),Sum.inr (Sum.inr j) => (1/500)*(n j).val

theorem nominalRate_nonneg (r : Fin 11) : 0 ≤ nominalRate r := by
  unfold nominalRate
  split_ifs <;> norm_num

theorem nominalFeed_nonneg (j : Fin 8) : 0 ≤ nominalFeed j := by
  unfold nominalFeed feed
  split_ifs <;> norm_num

theorem reactorRate_nonneg (Ω : ℝ) (hΩ : 0 ≤ Ω) {B K : ℕ}
    (x : ReactorState B K) (r : Channel) : 0 ≤ reactorRate Ω x r := by
  cases x with
  | none => simp [reactorRate]
  | some p =>
    rcases p with ⟨n,c⟩
    rcases r with r | (j | j)
    · dsimp only [reactorRate]
      have hn := nominalRate_nonneg r
      split_ifs <;> positivity
    · dsimp only [reactorRate]
      have hn := nominalFeed_nonneg j
      positivity
    · dsimp only [reactorRate]
      positivity

noncomputable def nominalReactor (B K : ℕ) (Ω : ℝ) (hΩ : 0 ≤ Ω) :
    FiniteJumpModel (ReactorState B K) Channel where
  next := reactorNext B K
  rate := reactorRate Ω
  nonneg := reactorRate_nonneg Ω hΩ

theorem failed_reactor_absorbing (B K : ℕ) (Ω : ℝ) (hΩ : 0 ≤ Ω) (r : Channel) :
    (nominalReactor B K Ω hΩ).next none r=none ∧
      (nominalReactor B K Ω hΩ).rate none r=0 := by
  exact ⟨rfl,rfl⟩

theorem feed_total_nominal : (∑ j,nominalFeed j)=(15231/100000 : ℝ) := by
  norm_num [nominalFeed,feed,Fin.sum_univ_succ,Fin.succ]

end CompositionalMemory.Semenov
