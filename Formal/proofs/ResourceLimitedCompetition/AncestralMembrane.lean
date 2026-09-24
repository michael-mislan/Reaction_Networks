import proofs.ResourceLimitedCompetition.PopulationSupport

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

def ancestralMembrane (tag : Bool) (cs : List TaggedCell) : ℕ :=
  (cs.map (fun c => if c.high=tag then c.compartment.2 else 0)).sum

def ancestralCount (tag : Bool) (cs : List TaggedCell) : ℕ :=
  (cs.filter (fun c => c.high=tag)).length

@[simp] theorem ancestralMembrane_nil (tag : Bool) : ancestralMembrane tag []=0 := rfl

@[simp] theorem ancestralMembrane_cons (tag : Bool) (c : TaggedCell) (cs : List TaggedCell) :
    ancestralMembrane tag (c::cs)=(if c.high=tag then c.compartment.2 else 0)+ancestralMembrane tag cs := rfl

@[simp] theorem ancestralMembrane_append (tag : Bool) (a b : List TaggedCell) :
    ancestralMembrane tag (a++b)=ancestralMembrane tag a+ancestralMembrane tag b := by
  simp [ancestralMembrane,List.sum_append]

theorem ancestral_membrane_total (cs : List TaggedCell) :
    ancestralMembrane true cs+ancestralMembrane false cs=membrane cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases hb : c.high <;> simp [hb,← ih] <;> omega

theorem ancestral_count_bounds (N : ℕ) (tag : Bool) (cs : List TaggedCell)
    (hv : ∀ c ∈ cs, N ≤ c.compartment.2 ∧ c.compartment.2 ≤ 2*N) :
    N*ancestralCount tag cs ≤ ancestralMembrane tag cs ∧
      ancestralMembrane tag cs ≤ 2*N*ancestralCount tag cs := by
  induction cs with
  | nil => simp [ancestralCount]
  | cons c cs ih =>
    have hc := hv c (by simp)
    have ht := ih (fun d hd => hv d (by simp [hd]))
    by_cases he : c.high=tag
    · simp only [ancestralMembrane_cons,he,if_true,ancestralCount,List.filter_cons,
        decide_true,List.length_cons]
      change N*(ancestralCount tag cs+1) ≤ c.compartment.2+ancestralMembrane tag cs ∧
        c.compartment.2+ancestralMembrane tag cs ≤ 2*N*(ancestralCount tag cs+1)
      constructor <;> nlinarith only [hc.1,hc.2,ht.1,ht.2]
    · simpa [ancestralCount,he] using ht

theorem resident_ancestral_membrane (tag : Bool) (Q D : ℕ) (a b : List TaggedCell)
    (c : TaggedCell) (r : Fin 13) :
    ancestralMembrane tag (residentAt Q D a c b r).live=
      ancestralMembrane tag (sourceAt Q D a c b).live := by
  simp [residentAt,sourceAt,nextCompartment]

theorem growth_ancestral_membrane (tag : Bool) (N Q D : ℕ) (a b : List TaggedCell)
    (c : TaggedCell) (d : Counts) :
    ancestralMembrane tag (growthAt N Q D a c b d).live=
      ancestralMembrane tag (sourceAt Q D a c b).live+(if c.high=tag then 1 else 0) := by
  classical
  unfold growthAt sourceAt
  simp only [nextCompartment]
  by_cases hm : c.compartment.2+1=2*N
  · simp only [hm,if_true,ancestralMembrane_append,ancestralMembrane_cons]
    split_ifs <;> omega
  · simp only [hm,if_false,ancestralMembrane_append,ancestralMembrane_cons]
    split_ifs <;> omega

theorem event_ancestral_membrane (N : ℕ) (tag : Bool) (D : Finset PopulationState)
    (s : ActiveState D) (e : CellEvent s.val) :
    ancestralMembrane tag (eventOutcome N ⟨s,e⟩).live=
      ancestralMembrane tag s.val.live+
        (match e.2 with | .inl _ => 0 | .inr _ => if (selectedCell s.val e.1).high=tag then 1 else 0) := by
  rcases e with ⟨i,ch⟩
  have hs := sourceAt_selected s.val i
  cases ch with
  | inl r =>
    have h := resident_ancestral_membrane tag s.val.resource s.val.divisions
      (s.val.live.take i.val) (s.val.live.drop (i.val+1)) (selectedCell s.val i) r
    rw [hs] at h
    simpa only [add_zero] using h
  | inr d =>
    have h := growth_ancestral_membrane tag N s.val.resource s.val.divisions
      (s.val.live.take i.val) (s.val.live.drop (i.val+1)) (selectedCell s.val i) d.val
    rwa [hs] at h

end ResourceLimitedCompetition
