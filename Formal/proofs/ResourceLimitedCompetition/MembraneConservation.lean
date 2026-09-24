import proofs.ResourceLimitedCompetition.ResourceSource
import proofs.HeritableCompositions.PartitionProduct

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

structure TaggedCell where
  high : Bool
  compartment : Compartment

structure PopulationState where
  resource : ℕ
  live : List TaggedCell
  divisions : ℕ

def membrane (xs : List TaggedCell) : ℕ :=
  (xs.map (fun x => x.compartment.2)).sum

@[simp] theorem membrane_nil : membrane [] = 0 := rfl
@[simp] theorem membrane_cons (c : TaggedCell) (cs : List TaggedCell) :
    membrane (c::cs) = c.compartment.2+membrane cs := rfl
@[simp] theorem membrane_append (a b : List TaggedCell) :
    membrane (a++b) = membrane a+membrane b := by
  simp [membrane, List.map_append, List.sum_append]

/-- Literal jump support. Final growth and complementary partition are one step. -/
inductive PopulationStep (N : ℕ) : PopulationState → PopulationState → Prop
  | resident (Q D : ℕ) (a b : List TaggedCell) (tag : Bool) (c : Compartment)
      (r : Fin 13) (hr : reactants c.1 r) :
      PopulationStep N ⟨Q,a++⟨tag,c⟩::b,D⟩
        ⟨Q,a++⟨tag,nextCompartment c (.inl r)⟩::b,D⟩
  | growth (Q D : ℕ) (a b : List TaggedCell) (tag : Bool) (c : Compartment)
      (hQ : 0 < Q) (hz : 0 < c.1 2) (hm : c.2+1 < 2*N) :
      PopulationStep N ⟨Q,a++⟨tag,c⟩::b,D⟩
        ⟨Q-1,a++⟨tag,nextCompartment c (.inr ())⟩::b,D⟩
  | division (Q D : ℕ) (a b : List TaggedCell) (tag : Bool) (c : Compartment)
      (hQ : 0 < Q) (hz : 0 < c.1 2) (hm : c.2+1 = 2*N)
      (d : Counts) (hd : d ∈ daughterDraws (nextCompartment c (.inr ())).1) :
      PopulationStep N ⟨Q,a++⟨tag,c⟩::b,D⟩
        ⟨Q-1,a++⟨tag,(d,N)⟩::
          ⟨tag,((fun i => (nextCompartment c (.inr ())).1 i-d i),N)⟩::b,D+1⟩

theorem step_conservation {N : ℕ} {s t : PopulationState} (h : PopulationStep N s t) :
    t.resource+membrane t.live = s.resource+membrane s.live := by
  cases h with
  | resident Q D a b tag c r hr => simp [nextCompartment]
  | growth Q D a b tag c hQ hz hm =>
    simp only [membrane_append, membrane_cons, nextCompartment]
    omega
  | division Q D a b tag c hQ hz hm d hd =>
    simp only [membrane_append, membrane_cons]
    omega

theorem step_live_divisions {N M : ℕ} {s t : PopulationState}
    (h : PopulationStep N s t) (hs : s.live.length = M+s.divisions) :
    t.live.length = M+t.divisions := by
  cases h <;> simp_all only [List.length_append, List.length_cons]
  all_goals omega

def ValidVolumes (N : ℕ) (s : PopulationState) : Prop :=
  ∀ c ∈ s.live, N ≤ c.compartment.2 ∧ c.compartment.2 < 2*N

theorem step_valid_volumes {N : ℕ} (hN : 0 < N) {s t : PopulationState}
    (h : PopulationStep N s t) (hs : ValidVolumes N s) : ValidVolumes N t := by
  cases h with
  | resident Q D a b tag c r hr =>
    have hc := hs ⟨tag,c⟩ (by simp)
    intro x hx
    simp only [List.mem_append,List.mem_cons] at hx
    rcases hx with ha | rfl | hb
    · exact hs x (by simp [ha])
    · exact hc
    · exact hs x (by simp [hb])
  | growth Q D a b tag c hQ hz hm =>
    have hc := hs ⟨tag,c⟩ (by simp)
    change N ≤ c.2 ∧ c.2 < 2*N at hc
    intro x hx
    simp only [List.mem_append,List.mem_cons] at hx
    rcases hx with ha | rfl | hb
    · exact hs x (by simp [ha])
    · change N ≤ c.2+1 ∧ c.2+1 < 2*N
      exact ⟨by omega,hm⟩
    · exact hs x (by simp [hb])
  | division Q D a b tag c hQ hz hm d hd =>
    intro x hx
    simp only [List.mem_append,List.mem_cons] at hx
    rcases hx with ha | rfl | rfl | hb
    · exact hs x (by simp [ha])
    · change N ≤ N ∧ N < 2*N
      omega
    · change N ≤ N ∧ N < 2*N
      omega
    · exact hs x (by simp [hb])

theorem membrane_lower (N : ℕ) (cs : List TaggedCell)
    (h : ∀ c ∈ cs, N ≤ c.compartment.2) : N*cs.length ≤ membrane cs := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := h c (by simp)
    have hcs := ih (fun d hd => h d (by simp [hd]))
    simp only [List.length_cons, membrane_cons]
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem membrane_upper (N : ℕ) (cs : List TaggedCell)
    (h : ∀ c ∈ cs, c.compartment.2 ≤ 2*N) : membrane cs ≤ 2*N*cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := h c (by simp)
    have hcs := ih (fun d hd => h d (by simp [hd]))
    simp only [List.length_cons, membrane_cons]
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem resource_population_budget (N M : ℕ) (hN : 0 < N) (s : PopulationState)
    (hv : ValidVolumes N s) (hres : s.resource+membrane s.live = 5*(N*M))
    (hQ : N*M ≤ s.resource) (hl : s.live.length=M+s.divisions) :
    s.live.length ≤ 4*M ∧ s.divisions ≤ 3*M ∧ M+2*s.divisions ≤ 7*M := by
  have hlow := membrane_lower N s.live (fun c hc => (hv c hc).1)
  have hup : membrane s.live ≤ 4*(N*M) := by omega
  have hn : N*s.live.length ≤ N*(4*M) := by nlinarith only [hlow,hup]
  have hcount : s.live.length ≤ 4*M := by nlinarith only [hn,hN]
  omega

theorem resource_endpoint (N M : ℕ) (s : PopulationState)
    (hres : s.resource+membrane s.live=5*(N*M)) (hQ : s.resource=N*M) :
    membrane s.live=4*(N*M) := by omega

theorem path_conservation {N : ℕ} {s t : PopulationState}
    (h : Relation.ReflTransGen (PopulationStep N) s t) :
    t.resource+membrane t.live = s.resource+membrane s.live := by
  induction h with
  | refl => rfl
  | tail hxy hyz ih => exact (step_conservation hyz).trans ih

theorem path_live_divisions {N M : ℕ} {s t : PopulationState}
    (h : Relation.ReflTransGen (PopulationStep N) s t)
    (hs : s.live.length=M+s.divisions) : t.live.length=M+t.divisions := by
  induction h with
  | refl => exact hs
  | tail hxy hyz ih => exact step_live_divisions hyz ih

theorem path_valid_volumes {N : ℕ} (hN : 0 < N) {s t : PopulationState}
    (h : Relation.ReflTransGen (PopulationStep N) s t)
    (hs : ValidVolumes N s) : ValidVolumes N t := by
  induction h with
  | refl => exact hs
  | tail hxy hyz ih => exact step_valid_volumes hN hyz ih

theorem newborn_membrane (N : ℕ) (cs : List TaggedCell)
    (h : ∀ c ∈ cs, c.compartment.2=N) : membrane cs=N*cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := h c (by simp)
    have hcs := ih (fun d hd => h d (by simp [hd]))
    simp only [membrane_cons,List.length_cons,hc,hcs]
    ring

end ResourceLimitedCompetition
