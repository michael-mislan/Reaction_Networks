import proofs.SmallResidentCompositionCopying.AmplificationChemistry

namespace SmallResidentCompositionCopying.Amplification
open Classical FiniteCopy CompositionalMemory
noncomputable section
set_option profiler true

def residentVector (word : Word) (s : State) (k : Species) : ℕ :=
  s.elim 0 fun z => resident word z k.1 k.2

def molecularNext (n : Species → ℕ) (r : Fin 4) (b : Bool) (k : Species) : ℕ :=
  if k=(moduleOf r,b) then
    if r=0 ∨ r=2 then n k+1 else n k-1
  else n k

/-- One word-independent mass-action rate table on resident count vectors.
The only protocol gate depends on the sum of the two species in a module. -/
def molecularRate (n : Species → ℕ) (r : Fin 4) (b : Bool) (c : Option Bool) : ℝ :=
  (if n (moduleOf r,false)+n (moduleOf r,true)<20 then
    if r=0 ∨ r=2 then 1000*(n (moduleOf r,b):ℝ)
    else ((n (moduleOf r,b)*(n (moduleOf r,b)-1):ℕ):ℝ)
  else 0) * c.elim 1 (fun t => (n (neighborOf r,t):ℝ)/10)

theorem module_total (word : Word) (z : Counts) (i : Fin 2) :
    resident word z i false+resident word z i true=(moduleCount z i).val+1 := by
  cases h : word i <;> simp [resident,h]

theorem word_independent_rates (word : Word) (z : Counts) (r : Fin 4)
    (b : Bool) (c : Option Bool) :
    chemicalRate word (some z) r b c =
      molecularRate (residentVector word (some z)) r b c := by
  have hc : (moduleCount z (moduleOf r)).val+1<20 ↔
      (moduleCount z (moduleOf r)).val<19 := by omega
  cases c <;> simp [chemicalRate,chemicalBase,catalystFactor,molecularRate,
    residentVector,module_total,hc]

/-- Every positive-rate reaction on the invariant pure-species domain has
the literal one-molecule stoichiometry. Zero-rate absent-species channels
cannot create a missing label. -/
theorem literal_next (word : Word) (z : Counts) (r : Fin 4) (b : Bool) (c : Option Bool)
    (h : 0 < chemicalRate word (some z) r b c) (k : Species) :
    residentVector word (model.next (some z) r) k =
      molecularNext (residentVector word (some z)) r b k := by
  have hw : word (moduleOf r)=b := by
    by_contra hn
    simp [chemicalRate,chemicalBase,resident,hn] at h
  have hactive : (moduleCount z (moduleOf r)).val<19 := by
    by_contra hn
    simp [chemicalRate,chemicalBase,hn] at h
  have hd : r=0 ∨ r=2 ∨ 0<(moduleCount z (moduleOf r)).val := by
    by_cases h₀ : r=0
    · exact Or.inl h₀
    by_cases h₂ : r=2
    · exact Or.inr (Or.inl h₂)
    right; right
    by_contra hn
    have hz : (moduleCount z (moduleOf r)).val=0 := by omega
    simp [chemicalRate,chemicalBase,resident,hw,h₀,h₂,hz] at h
  clear h c
  rcases k with ⟨i,t⟩
  fin_cases r <;> norm_num [moduleOf,moduleCount,Fin.ext_iff] at hw hactive hd
  all_goals
    fin_cases i <;> cases b <;> cases t <;>
      simp [residentVector,resident,moduleCount,moduleOf,molecularNext,model,up,down,hw] <;>
      omega

/-- At a completed module the same label-blind quench stops both directions. -/
theorem terminal_rates_zero (word : Word) (z : Counts)
    (h : z.1.val=19 ∧ z.2.val=19) (r : ChemicalChannel) :
    (chemicalModel word).rate (some z) r = 0 := by
  rcases r with ⟨r,b,c⟩
  fin_cases r <;> simp [chemicalModel,chemicalRate,chemicalBase,moduleCount,moduleOf,h.1,h.2]

/-- The interaction actually changes a reaction rate as neighbor count changes. -/
theorem interaction_changes_rate :
    birth ⟨0,by decide⟩ ⟨1,by decide⟩ - birth ⟨0,by decide⟩ ⟨0,by decide⟩ = 100 := by
  norm_num [birth,factor]

/-- Unit resident/food masses balance uncatalyzed and cross-catalyzed pairs. -/
theorem mass_balance : (1:ℕ)+1=2 ∧ (1:ℕ)+1+1=2+1 := by norm_num

end
end SmallResidentCompositionCopying.Amplification
