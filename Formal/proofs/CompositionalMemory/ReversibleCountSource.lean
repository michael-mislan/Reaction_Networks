import proofs.CompositionalMemory.CoupledCountSource
import proofs.CompositionalMemory.ReversibleFiniteSource

namespace CompositionalMemory
open FiniteCopy

instance : MeasurableSpace (Option ReversibleChannel) := ⊤
instance : MeasurableSingletonClass (Option ReversibleChannel) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def reversibleCountReactionNext (N : Nat) (s : CoupledCountState N) (r : ReversibleChannel) :
    CoupledCountState N :=
  if hr : r.2.val<8 then coupledCountReactionNext N s (r.1,⟨r.2.val,hr⟩) else
  if s.1.val=N then s else
  let x := (s.2 r.1).1
  let y := (s.2 r.1).2
  let changed := fun p => Function.update s.2 r.1 p
  if r.2.val=8 then (s.1,changed (x-1,y))
  else if r.2.val=9 then (s.1,changed (x-2,y+1))
  else if r.2.val=10 then (s.1,changed (x+1,y-1))
  else (s.1,changed (x+1,y))

noncomputable def reversibleCountReactionRate (N : Nat) (ε : ℝ)
    (s : CoupledCountState N) (r : ReversibleChannel) : ℝ :=
  if s.1.val=N ∨ (∃ k, (s.2 k).1 < 0 ∨ (s.2 k).2 < 0) then 0 else
  let x := (s.2 r.1).1.toNat
  let y := (s.2 r.1).2.toNat
  let other : Fin 2 := ⟨1-r.1.val,by omega⟩
  let z := (s.2 other).2.toNat
  let m : ℝ := N+s.1.val
  ![(193/5)*m,1555*(y : ℝ),15*(x*(x-1) : Nat)/m,100*(x : ℝ)*(y : ℝ)/m,
    (105/2)*(x : ℝ),(x : ℝ)/10,ε*(x : ℝ)*(z : ℝ)/m,ε*(y : ℝ)*(z : ℝ)/m,
    (193/750000)*(x : ℝ),(311/30000)*(x*(x-1) : Nat)/m,
    15*(x : ℝ)*(y : ℝ)/m,(1/1000)*(y : ℝ),(21/40000)*m] r.2

theorem reversibleCountReactionRate_nonneg (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (s : CoupledCountState N) (r : ReversibleChannel) : 0 ≤ reversibleCountReactionRate N ε s r := by
  unfold reversibleCountReactionRate
  split_ifs
  · exact le_rfl
  · rcases r with ⟨k,r⟩
    fin_cases r <;> norm_num <;> positivity

def reversibleCountNext (N : Nat) (s : CoupledCountState N) : Option ReversibleChannel → CoupledCountState N
  | none => s
  | some r => reversibleCountReactionNext N s r

noncomputable def reversibleCountRate (N : Nat) (ε : ℝ) (s : CoupledCountState N) : Option ReversibleChannel → ℝ
  | none => 1
  | some r => reversibleCountReactionRate N ε s r

theorem reversibleCountRate_nonneg (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (s : CoupledCountState N) (r : Option ReversibleChannel) : 0 ≤ reversibleCountRate N ε s r := by
  cases r with
  | none => norm_num [reversibleCountRate]
  | some r => exact reversibleCountReactionRate_nonneg N ε hε s r

theorem reversibleCountRate_total_pos (N : Nat) (ε : ℝ) (hε : 0 ≤ ε) (s : CoupledCountState N) :
    0 < ∑ r,reversibleCountRate N ε s r := by
  rw [Fintype.sum_option]
  have hh : 0 ≤ ∑ r : ReversibleChannel,reversibleCountReactionRate N ε s r :=
    Finset.sum_nonneg (fun r _ => reversibleCountReactionRate_nonneg N ε hε s r)
  change 0 < 1+∑ r : ReversibleChannel,reversibleCountReactionRate N ε s r
  linarith

theorem reversibleCountReactionRate_embed (N : Nat) (ε : ℝ) (s : CoupledLiveState N)
    (r : ReversibleChannel) :
    reversibleCountReactionRate N ε (coupledCountEmbed N s) r=reversibleRate N ε (some s) r := by
  rcases s with ⟨j,a⟩
  have hx (k : Fin 2) : ¬((a k).1.val : Int) < 0 := not_lt_of_ge (Int.natCast_nonneg _)
  have hy (k : Fin 2) : ¬((a k).2.val : Int) < 0 := not_lt_of_ge (Int.natCast_nonneg _)
  simp [reversibleCountReactionRate,coupledCountEmbed,reversibleRate,hx,hy]

theorem reversibleCountReactionNext_embed (N : Nat) (s : CoupledLiveState N) (r : ReversibleChannel) :
    coupledCountClip N (reversibleCountReactionNext N (coupledCountEmbed N s) r)=reversibleNext N (some s) r := by
  rcases s with ⟨j,a⟩
  rfl

noncomputable def reversibleEncodedModel (N : Nat) (ε : ℝ) (hε : 0 ≤ ε) :
    FiniteJumpModel (CoupledFiniteState N) (Option ReversibleChannel) :=
  encodedFiniteModel (reversibleCountNext N) (reversibleCountRate N ε) (reversibleCountRate_nonneg N ε hε)
    (coupledCountEmbed N) (coupledCountClip N)

theorem reversibleEncoded_generator (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (f : CoupledFiniteState N → ℝ) (s : CoupledFiniteState N) :
    (reversibleEncodedModel N ε hε).generator f s=(reversibleFiniteModel N ε hε).generator f s := by
  cases s with
  | none => simp [FiniteJumpModel.generator,reversibleEncodedModel,encodedFiniteModel,reversibleFiniteModel,reversibleRate]
  | some s =>
    simp only [FiniteJumpModel.generator,reversibleEncodedModel,encodedFiniteModel,Fintype.sum_option,
      reversibleCountRate,reversibleCountNext,coupledCount_clip_embed,sub_self,mul_zero,zero_add,
      reversibleCountReactionRate_embed,reversibleCountReactionNext_embed]
    rfl

end CompositionalMemory
