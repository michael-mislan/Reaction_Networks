import proofs.CompositionalMemory.ReversibleCountSource
import proofs.CompositionalMemory.ReversibleGrowthMonitor

namespace CompositionalMemory
open FiniteCopy

/-- The sum tag is a passive record of whether reverse growth has occurred.
The right branch keeps the actual counts and continues the chemistry. -/
abbrev ReversiblePhysicalState (N : Nat) :=
  CoupledCountState N ⊕ (Nat × (Fin 2 → Int × Int))
abbrev ReversiblePhysicalChannel := Fin 2 × Fin 14

def reversiblePhysicalCounts (N : Nat) : ReversiblePhysicalState N → Nat × (Fin 2 → Int × Int)
  | .inl s => (N+s.1.val,s.2)
  | .inr s => s

def reversibleRawNext (N : Nat) (s : Nat × (Fin 2 → Int × Int))
    (r : ReversiblePhysicalChannel) : Nat × (Fin 2 → Int × Int) :=
  if s.1=0 ∨ s.1=2*N then s else
  let x := (s.2 r.1).1
  let y := (s.2 r.1).2
  let changed := fun p => Function.update s.2 r.1 p
  if r.2.val=13 then (s.1-1,changed (x+1,y))
  else if r.2.val=5 then (s.1+1,changed (x-1,y))
  else if r.2.val=0 ∨ r.2.val=11 ∨ r.2.val=12 then (s.1,changed (x+1,y))
  else if r.2.val=1 then (s.1,changed (x+2,y-1))
  else if r.2.val=2 ∨ r.2.val=6 then (s.1,changed (x-1,y+1))
  else if r.2.val=7 ∨ r.2.val=10 then (s.1,changed (x+1,y-1))
  else if r.2.val=9 then (s.1,changed (x-2,y+1))
  else (s.1,changed (x-1,y))

noncomputable def reversibleRawRate (N : Nat) (ε ρ : ℝ)
    (s : Nat × (Fin 2 → Int × Int)) (r : ReversiblePhysicalChannel) : ℝ :=
  if s.1=0 ∨ s.1=2*N ∨ (∃ k, (s.2 k).1<0 ∨ (s.2 k).2<0) then 0 else
  let x := (s.2 r.1).1.toNat
  let y := (s.2 r.1).2.toNat
  let z := (s.2 ⟨1-r.1.val,by omega⟩).2.toNat
  let m : ℝ := s.1
  ![(193/5)*m,1555*(y : ℝ),15*(x*(x-1) : Nat)/m,
    100*(x : ℝ)*(y : ℝ)/m,(105/2)*(x : ℝ),(x : ℝ)/10,
    ε*(x : ℝ)*(z : ℝ)/m,ε*(y : ℝ)*(z : ℝ)/m,
    (193/750000)*(x : ℝ),(311/30000)*(x*(x-1) : Nat)/m,
    15*(x : ℝ)*(y : ℝ)/m,(1/1000)*(y : ℝ),(21/40000)*m,ρ*m] r.2

theorem reversibleRawRate_nonneg (N : Nat) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (s : Nat × (Fin 2 → Int × Int)) (r : ReversiblePhysicalChannel) :
    0 ≤ reversibleRawRate N ε ρ s r := by
  unfold reversibleRawRate
  split_ifs
  · exact le_rfl
  · rcases r with ⟨k,r⟩
    fin_cases r <;> norm_num <;> positivity

def reversiblePhysicalReactionNext (N : Nat) (s : ReversiblePhysicalState N)
    (r : ReversiblePhysicalChannel) : ReversiblePhysicalState N :=
  match s with
  | .inr s => .inr (reversibleRawNext N s r)
  | .inl s =>
    if hr : r.2.val<13 then .inl (reversibleCountReactionNext N s (r.1,⟨r.2.val,hr⟩))
    else if s.1.val=N then .inl s
    else .inr (reversibleRawNext N (reversiblePhysicalCounts N (.inl s)) r)

noncomputable def reversiblePhysicalReactionRate (N : Nat) (ε ρ : ℝ)
    (s : ReversiblePhysicalState N) (r : ReversiblePhysicalChannel) : ℝ :=
  reversibleRawRate N ε ρ (reversiblePhysicalCounts N s) r

def reversiblePhysicalEmbed (N : Nat) (s : CoupledLiveState N) : ReversiblePhysicalState N :=
  .inl (coupledCountEmbed N s)

def reversiblePhysicalClip (N : Nat) : ReversiblePhysicalState N → CoupledFiniteState N
  | .inl s => coupledCountClip N s
  | .inr _ => none

theorem reversiblePhysical_clip_embed (N : Nat) (s : CoupledLiveState N) :
    reversiblePhysicalClip N (reversiblePhysicalEmbed N s)=some s :=
  coupledCount_clip_embed N s

theorem reversiblePhysical_embed_clip (N : Nat) (z : ReversiblePhysicalState N)
    (s : CoupledLiveState N) (h : reversiblePhysicalClip N z=some s) :
    reversiblePhysicalEmbed N s=z := by
  cases z with
  | inl z => exact congrArg Sum.inl (coupledCount_embed_clip N z s h)
  | inr z => cases h

instance : MeasurableSpace (Option ReversiblePhysicalChannel) := ⊤
instance : MeasurableSingletonClass (Option ReversiblePhysicalChannel) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def reversiblePhysicalNext (N : Nat) (s : ReversiblePhysicalState N) :
    Option ReversiblePhysicalChannel → ReversiblePhysicalState N
  | none => s
  | some r => reversiblePhysicalReactionNext N s r

noncomputable def reversiblePhysicalRate (N : Nat) (ε ρ : ℝ) (s : ReversiblePhysicalState N) :
    Option ReversiblePhysicalChannel → ℝ
  | none => 1
  | some r => reversiblePhysicalReactionRate N ε ρ s r

theorem reversiblePhysicalRate_nonneg (N : Nat) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (s : ReversiblePhysicalState N) (r : Option ReversiblePhysicalChannel) :
    0 ≤ reversiblePhysicalRate N ε ρ s r := by
  cases r with
  | none => norm_num [reversiblePhysicalRate]
  | some r => exact reversibleRawRate_nonneg N ε ρ hε hρ _ r

theorem reversiblePhysicalRate_total_pos (N : Nat) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (s : ReversiblePhysicalState N) : 0 < ∑ r,reversiblePhysicalRate N ε ρ s r := by
  rw [Fintype.sum_option]
  have hh : 0 ≤ ∑ r : ReversiblePhysicalChannel,reversiblePhysicalReactionRate N ε ρ s r :=
    Finset.sum_nonneg (fun r _ => reversibleRawRate_nonneg N ε ρ hε hρ _ r)
  change 0 < 1+∑ r : ReversiblePhysicalChannel,reversiblePhysicalReactionRate N ε ρ s r
  linarith

noncomputable def reversiblePhysicalEncodedModel (N : Nat) (ε ρ : ℝ)
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) :=
  encodedFiniteModel (reversiblePhysicalNext N) (reversiblePhysicalRate N ε ρ)
    (reversiblePhysicalRate_nonneg N ε ρ hε hρ) (reversiblePhysicalEmbed N) (reversiblePhysicalClip N)

end CompositionalMemory
