import proofs.CoreCouplingCAC.SourceAdapter

namespace CoreCouplingCAC

/-- Buffered external species F,G,RA,RB,WH. WH is an ideal output sink;
all buffered monomial activities are one and the sink reverse rate is zero. -/
def externalInput : Fin 5 → Fin 7 → ℕ :=
  ![![0,1,0,0,0,0,0], ![0,0,0,0,0,1,0],
    ![0,0,0,1,0,0,0], ![0,0,0,0,1,0,0], ![0,0,0,0,0,0,0]]
def externalOutput : Fin 5 → Fin 7 → ℕ :=
  ![![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,1]]
def dynamicMass : Fin 4 → ℕ := ![2,1,1,2]
def externalMass : Fin 5 → ℕ := ![1,3,2,1,2]

theorem completed_mass_balance (r : Fin 7) :
    (∑ i : Fin 4, dynamicMass i*inputComplex i r) +
      (∑ i : Fin 5, externalMass i*externalInput i r) =
    (∑ i : Fin 4, dynamicMass i*outputComplex i r) +
      (∑ i : Fin 5, externalMass i*externalOutput i r) := by
  fin_cases r <;> norm_num [dynamicMass,externalMass,inputComplex,outputComplex,
    externalInput,externalOutput,Fin.sum_univ_succ]

noncomputable def completedCurrent (p : Rates) (x : State) (r : Fin 7) : ℝ :=
  forwardRate p r * (∏ i : Fin 4, coordinates x i ^ inputComplex i r) *
    (∏ i : Fin 5, (1:ℝ)^externalInput i r) -
  reverseRate p r * (∏ i : Fin 4, coordinates x i ^ outputComplex i r) *
    (∏ i : Fin 5, (1:ℝ)^externalOutput i r)

theorem buffered_current_agrees (p : Rates) (x : State) (r : Fin 7) :
    completedCurrent p x r = sourceCurrent p x r := by
  simp [completedCurrent,sourceCurrent]

noncomputable def dynamicPotential (p : Rates) : Fin 4 → ℝ := ![0,0,0,-Real.log p.v]
noncomputable def externalPotential (p : Rates) : Fin 5 → ℝ :=
  ![Real.log p.u-Real.log p.v,0,Real.log p.a,Real.log p.b,0]
noncomputable def chemicalAffinity (p : Rates) (r : Fin 7) : ℝ :=
  (∑ i : Fin 4, dynamicPotential p i * ((inputComplex i r : ℝ)-outputComplex i r)) +
  (∑ i : Fin 5, externalPotential p i * ((externalInput i r : ℝ)-externalOutput i r))

/-- Every reversible pair has its stated common potential realization.
Channel 6 is explicitly excluded because it is the ideal irreversible sink. -/
theorem reversible_rate_ratios (p : Rates) (hp : p.Positive) (r : Fin 7) (hr : r ≠ 6) :
    forwardRate p r / reverseRate p r = Real.exp (chemicalAffinity p r) := by
  rcases hp with ⟨ha,hb,hu,hv,he,hd⟩
  fin_cases r <;>
    norm_num [forwardRate,reverseRate,chemicalAffinity,dynamicPotential,externalPotential,
      inputComplex,outputComplex,externalInput,externalOutput,Fin.sum_univ_succ] at hr ⊢
  · rw [Real.exp_log hu]
  · rw [Real.exp_neg,Real.exp_log hv]
  · rw [Real.exp_log ha]
  · rw [Real.exp_log hb]
  · exact ne_of_gt he
  · exact (hr rfl).elim

theorem ideal_sink_declared (p : Rates) : reverseRate p 6 = 0 := rfl

end CoreCouplingCAC
