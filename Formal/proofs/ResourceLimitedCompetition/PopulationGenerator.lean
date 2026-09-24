import proofs.ResourceLimitedCompetition.MembraneConservation

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

def sourceAt (Q D : ℕ) (a : List TaggedCell) (c : TaggedCell) (b : List TaggedCell) :
    PopulationState := ⟨Q,a++c::b,D⟩

def residentAt (Q D : ℕ) (a : List TaggedCell) (c : TaggedCell) (b : List TaggedCell)
    (r : Fin 13) : PopulationState :=
  ⟨Q,a++⟨c.high,nextCompartment c.compartment (.inl r)⟩::b,D⟩

/-- A partition is processed even on the resource-endpoint growth jump. -/
def growthAt (N Q D : ℕ) (a : List TaggedCell) (c : TaggedCell) (b : List TaggedCell)
    (d : Counts) : PopulationState :=
  let parent := nextCompartment c.compartment (.inr ())
  if parent.2=2*N then
    ⟨Q-1,a++⟨c.high,(d,N)⟩::⟨c.high,((fun i => parent.1 i-d i),N)⟩::b,D+1⟩
  else ⟨Q-1,a++⟨c.high,parent⟩::b,D⟩

noncomputable def cellGenerator (γ : ℝ) (Ω N Q D : ℕ)
    (a : List TaggedCell) (c : TaggedCell) (b : List TaggedCell)
    (f : PopulationState → ℝ) : ℝ :=
  (∑ r : Fin 13, propensity (resourceCoefficient γ Q Ω) c.compartment (.inl r)*
    (f (residentAt Q D a c b r)-f (sourceAt Q D a c b))) +
  propensity (resourceCoefficient γ Q Ω) c.compartment (.inr ()) *
    ((∑ d ∈ daughterDraws (nextCompartment c.compartment (.inr ())).1,
      daughterWeight (nextCompartment c.compartment (.inr ())).1 d *
        f (growthAt N Q D a c b d))-f (sourceAt Q D a c b))

noncomputable def scanGenerator (γ : ℝ) (Ω N Q D : ℕ)
    (f : PopulationState → ℝ) (a : List TaggedCell) : List TaggedCell → ℝ
  | [] => 0
  | c::b => cellGenerator γ Ω N Q D a c b f+
      scanGenerator γ Ω N Q D f (a++[c]) b

noncomputable def populationGenerator (γ : ℝ) (Ω N : ℕ)
    (f : PopulationState → ℝ) (s : PopulationState) : ℝ :=
  scanGenerator γ Ω N s.resource s.divisions f [] s.live

theorem resident_membrane (Q D : ℕ) (a : List TaggedCell) (c : TaggedCell)
    (b : List TaggedCell) (r : Fin 13) :
    membrane (residentAt Q D a c b r).live=membrane (sourceAt Q D a c b).live := by
  simp [residentAt, sourceAt, nextCompartment]

theorem growth_membrane (N Q D : ℕ) (a : List TaggedCell) (c : TaggedCell)
    (b : List TaggedCell) (d : Counts) :
    membrane (growthAt N Q D a c b d).live=membrane (sourceAt Q D a c b).live+1 := by
  dsimp only [growthAt]
  split_ifs with h
  · simp only [nextCompartment] at h
    simp only [sourceAt,membrane_append,membrane_cons]
    omega
  · simp [sourceAt,nextCompartment]
    omega

theorem cell_membrane_generator (γ : ℝ) (Ω N Q D : ℕ)
    (a : List TaggedCell) (c : TaggedCell) (b : List TaggedCell) :
    cellGenerator γ Ω N Q D a c b (fun s => (membrane s.live : ℝ)) =
      resourceCoefficient γ Q Ω*(c.compartment.1 2 : ℝ) := by
  classical
  unfold cellGenerator
  simp only [resident_membrane,sub_self,mul_zero,Finset.sum_const_zero,zero_add,
    growth_membrane,Nat.cast_add,Nat.cast_one]
  rw [← Finset.sum_mul, daughterWeight_sum]
  simp [propensity]

def totalZ (cs : List TaggedCell) : ℕ := (cs.map (fun c => c.compartment.1 2)).sum

theorem scan_membrane_generator (γ : ℝ) (Ω N Q D : ℕ) (a cs : List TaggedCell) :
    scanGenerator γ Ω N Q D (fun s => (membrane s.live : ℝ)) a cs =
      resourceCoefficient γ Q Ω*(totalZ cs : ℝ) := by
  induction cs generalizing a with
  | nil => simp [scanGenerator,totalZ]
  | cons c cs ih =>
    rw [scanGenerator,cell_membrane_generator,ih]
    simp only [totalZ,List.map_cons,List.sum_cons,Nat.cast_add]
    ring

theorem population_membrane_generator (γ : ℝ) (Ω N : ℕ) (s : PopulationState) :
    populationGenerator γ Ω N (fun x => (membrane x.live : ℝ)) s =
      resourceCoefficient γ s.resource Ω*(totalZ s.live : ℝ) :=
  scan_membrane_generator γ Ω N s.resource s.divisions [] s.live

end ResourceLimitedCompetition
