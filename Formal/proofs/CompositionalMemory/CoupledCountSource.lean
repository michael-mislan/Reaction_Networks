import proofs.CompositionalMemory.CoupledFiniteSource
import proofs.CompositionalMemory.FiniteEncoding

namespace CompositionalMemory
open FiniteCopy

instance : MeasurableSpace (Option CoupledChannel) := ⊤
instance : MeasurableSingletonClass (Option CoupledChannel) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Unbounded resident counts with a common membrane. Negative coordinates
are inert auxiliary states, as in the one-module source construction. -/
abbrev CoupledCountState (N : Nat) := Fin (N+1) × (Fin 2 → Int × Int)

def coupledCountEmbed (N : Nat) (s : CoupledLiveState N) : CoupledCountState N :=
  (s.1,fun k => ((s.2 k).1.val,(s.2 k).2.val))

def coupledCountClip (N : Nat) (s : CoupledCountState N) : CoupledFiniteState N :=
  coupledClipped N s.1 s.2

theorem coupledCount_clip_embed (N : Nat) (s : CoupledLiveState N) :
    coupledCountClip N (coupledCountEmbed N s)=some s := by
  rcases s with ⟨j,a⟩
  have hx (k : Fin 2) : ((a k).1.val : Int) ≤ 16*((N : Int)+j.val) := by
    exact_mod_cast Nat.le_of_lt_succ (a k).1.isLt
  have hy (k : Fin 2) : ((a k).2.val : Int) ≤ 4*((N : Int)+j.val) := by
    exact_mod_cast Nat.le_of_lt_succ (a k).2.isLt
  simp [coupledCountClip,coupledCountEmbed,coupledClipped,hx,hy]

theorem coupledCount_embed_clip (N : Nat) (z : CoupledCountState N) (s : CoupledLiveState N)
    (h : coupledCountClip N z=some s) : coupledCountEmbed N s=z := by
  rcases z with ⟨j,a⟩
  simp only [coupledCountClip,coupledClipped] at h
  split_ifs at h with hc
  cases h
  dsimp only [coupledCountEmbed]
  apply Prod.ext
  · rfl
  funext k
  have hk := hc k
  simp [Int.toNat_of_nonneg hk.1,Int.toNat_of_nonneg hk.2.2.1]

def coupledCountReactionNext (N : Nat) (s : CoupledCountState N) (r : CoupledChannel) :
    CoupledCountState N :=
  if hj : s.1.val=N then s else
  let x := (s.2 r.1).1
  let y := (s.2 r.1).2
  let changed := fun p => Function.update s.2 r.1 p
  if r.2.val=5 then
    if x=0 then s else (⟨s.1.val+1,by omega⟩,changed (x-1,y))
  else if r.2.val=0 then (s.1,changed (x+1,y))
  else if r.2.val=1 then (s.1,changed (x+2,y-1))
  else if r.2.val=2 ∨ r.2.val=6 then (s.1,changed (x-1,y+1))
  else if r.2.val=7 then (s.1,changed (x+1,y-1))
  else (s.1,changed (x-1,y))

noncomputable def coupledCountReactionRate (N : Nat) (ε : ℝ)
    (s : CoupledCountState N) (r : CoupledChannel) : ℝ :=
  if s.1.val=N ∨ (∃ k, (s.2 k).1 < 0 ∨ (s.2 k).2 < 0) then 0 else
  let x := (s.2 r.1).1.toNat
  let y := (s.2 r.1).2.toNat
  let other : Fin 2 := ⟨1-r.1.val,by omega⟩
  let z := (s.2 other).2.toNat
  let m : ℝ := N+s.1.val
  ![40*m,1500*(y : ℝ),15*(x*(x-1) : Nat)/m,100*(x : ℝ)*(y : ℝ)/m,
    54*(x : ℝ),(x : ℝ)/10,ε*(x : ℝ)*(z : ℝ)/m,ε*(y : ℝ)*(z : ℝ)/m] r.2

theorem coupledCountReactionRate_nonneg (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (s : CoupledCountState N) (r : CoupledChannel) : 0 ≤ coupledCountReactionRate N ε s r := by
  unfold coupledCountReactionRate
  split_ifs
  · exact le_rfl
  · rcases r with ⟨k,r⟩
    fin_cases r <;> norm_num <;> positivity

def coupledCountNext (N : Nat) (s : CoupledCountState N) : Option CoupledChannel → CoupledCountState N
  | none => s
  | some r => coupledCountReactionNext N s r

noncomputable def coupledCountRate (N : Nat) (ε : ℝ) (s : CoupledCountState N) : Option CoupledChannel → ℝ
  | none => 1
  | some r => coupledCountReactionRate N ε s r

theorem coupledCountRate_nonneg (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (s : CoupledCountState N) (r : Option CoupledChannel) : 0 ≤ coupledCountRate N ε s r := by
  cases r with
  | none => norm_num [coupledCountRate]
  | some r => exact coupledCountReactionRate_nonneg N ε hε s r

theorem coupledCountRate_total_pos (N : Nat) (ε : ℝ) (hε : 0 ≤ ε) (s : CoupledCountState N) :
    0 < ∑ r,coupledCountRate N ε s r := by
  rw [Fintype.sum_option]
  have hh : 0 ≤ ∑ r : CoupledChannel,coupledCountReactionRate N ε s r :=
    Finset.sum_nonneg (fun r _ => coupledCountReactionRate_nonneg N ε hε s r)
  change 0 < 1+∑ r : CoupledChannel,coupledCountReactionRate N ε s r
  linarith

theorem coupledCountReactionRate_embed (N : Nat) (ε : ℝ) (s : CoupledLiveState N)
    (r : CoupledChannel) :
    coupledCountReactionRate N ε (coupledCountEmbed N s) r=coupledRate N ε (some s) r := by
  rcases s with ⟨j,a⟩
  have hx (k : Fin 2) : ¬((a k).1.val : Int) < 0 := not_lt_of_ge (Int.natCast_nonneg _)
  have hy (k : Fin 2) : ¬((a k).2.val : Int) < 0 := not_lt_of_ge (Int.natCast_nonneg _)
  simp [coupledCountReactionRate,coupledCountEmbed,coupledRate,hx,hy]

theorem coupledCountReactionNext_embed (N : Nat) (s : CoupledLiveState N) (r : CoupledChannel) :
    coupledCountClip N (coupledCountReactionNext N (coupledCountEmbed N s) r)=coupledNext N (some s) r := by
  rcases s with ⟨j,a⟩
  rfl

noncomputable def coupledEncodedModel (N : Nat) (ε : ℝ) (hε : 0 ≤ ε) :
    FiniteJumpModel (CoupledFiniteState N) (Option CoupledChannel) :=
  encodedFiniteModel (coupledCountNext N) (coupledCountRate N ε) (coupledCountRate_nonneg N ε hε)
    (coupledCountEmbed N) (coupledCountClip N)

theorem coupledEncoded_generator (N : Nat) (ε : ℝ) (hε : 0 ≤ ε)
    (f : CoupledFiniteState N → ℝ) (s : CoupledFiniteState N) :
    (coupledEncodedModel N ε hε).generator f s=(coupledFiniteModel N ε hε).generator f s := by
  cases s with
  | none => simp [FiniteJumpModel.generator,coupledEncodedModel,encodedFiniteModel,coupledFiniteModel,coupledRate]
  | some s =>
    simp only [FiniteJumpModel.generator,coupledEncodedModel,encodedFiniteModel,Fintype.sum_option,
      coupledCountRate,coupledCountNext,coupledCount_clip_embed,sub_self,mul_zero,zero_add,
      coupledCountReactionRate_embed,coupledCountReactionNext_embed]
    rfl

end CompositionalMemory
