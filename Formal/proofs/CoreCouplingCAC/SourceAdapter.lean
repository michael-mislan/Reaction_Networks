import proofs.CoreCouplingCAC.Isolation

namespace CoreCouplingCAC

/-- Species order A,B,z,H; column order A↔B+z, z↔H, H↔2z,
0↔A, 0↔B, B↔2A, H→0. -/
def inputComplex : Fin 4 → Fin 7 → ℕ :=
  ![![1,0,0,0,0,0,0], ![0,0,0,0,0,1,0],
    ![0,1,0,0,0,0,0], ![0,0,1,0,0,0,1]]

def outputComplex : Fin 4 → Fin 7 → ℕ :=
  ![![0,0,0,1,0,2,0], ![1,0,0,0,1,0,0],
    ![1,0,2,0,0,0,0], ![0,1,0,0,0,0,0]]

noncomputable def forwardRate (p : Rates) : Fin 7 → ℝ :=
  ![1,p.u,1,p.a,p.b,p.e,p.d]
noncomputable def reverseRate (p : Rates) : Fin 7 → ℝ :=
  ![1,1,p.v,1,1,p.e,0]
noncomputable def coordinates (x : State) : Fin 4 → ℝ := ![x.A,x.B,x.z,x.H]
noncomputable def sourceCurrent (p : Rates) (x : State) (r : Fin 7) : ℝ :=
  forwardRate p r * (∏ i : Fin 4, coordinates x i ^ inputComplex i r) -
  reverseRate p r * (∏ i : Fin 4, coordinates x i ^ outputComplex i r)
noncomputable def sourceDerivative (p : Rates) (x : State) (i : Fin 4) : ℝ :=
  ∑ r : Fin 7, ((outputComplex i r : ℝ) - inputComplex i r) * sourceCurrent p x r

theorem literal_source_adapter (p : Rates) (x : State) :
    sourceDerivative p x =
      ![fA p x.A x.B x.z, fB p x.A x.B x.z,
        fZ p x.A x.B x.z x.H, fH p x.z x.H] := by
  funext i
  fin_cases i <;>
    norm_num [sourceDerivative,sourceCurrent,inputComplex,outputComplex,
      forwardRate,reverseRate,coordinates,Fin.sum_univ_succ,Fin.prod_univ_succ,
      fA,fB,fZ,fH] <;> ring

/-- Local core input/output matrices after clamping external partners. -/
def coreInput : Fin 2 → Fin 2 → ℕ := ![![1,0],![0,1]]
def coreOutput : Fin 2 → Fin 2 → ℕ := ![![0,2],![1,0]]

def abSpecies : Fin 2 → Fin 4 := ![0,1]
def abReactions : Fin 2 → Fin 7 := ![0,5]
def zhSpecies : Fin 2 → Fin 4 := ![2,3]
def zhReactions : Fin 2 → Fin 7 := ![1,2]

theorem AB_literal_core (i r : Fin 2) :
    inputComplex (abSpecies i) (abReactions r) = coreInput i r ∧
    outputComplex (abSpecies i) (abReactions r) = coreOutput i r := by
  fin_cases i <;> fin_cases r <;> decide

theorem ZH_literal_core (i r : Fin 2) :
    inputComplex (zhSpecies i) (zhReactions r) = coreInput i r ∧
    outputComplex (zhSpecies i) (zhReactions r) = coreOutput i r := by
  fin_cases i <;> fin_cases r <;> decide

def AutonomousRestriction (S R : Finset (Fin 2)) : Prop :=
  ∀ r ∈ R, (∃ i ∈ S, 0 < coreInput i r) ∧ (∃ i ∈ S, 0 < coreOutput i r)

/-- Any nonempty autonomous restriction already needs both species. -/
theorem core_species_minimal (S R : Finset (Fin 2)) (hr : R.Nonempty)
    (h : AutonomousRestriction S R) : S = Finset.univ := by
  obtain ⟨r,hr⟩ := hr
  obtain ⟨⟨i,hi,hin⟩,⟨j,hj,hout⟩⟩ := h r hr
  have h0 : (0:Fin 2) ∈ S := by
    fin_cases r <;> fin_cases i <;> fin_cases j <;>
      simp_all [coreInput,coreOutput]
  have h1 : (1:Fin 2) ∈ S := by
    fin_cases r <;> fin_cases i <;> fin_cases j <;>
      simp_all [coreInput,coreOutput]
  apply Finset.eq_univ_of_forall
  intro i
  fin_cases i <;> assumption

end CoreCouplingCAC
