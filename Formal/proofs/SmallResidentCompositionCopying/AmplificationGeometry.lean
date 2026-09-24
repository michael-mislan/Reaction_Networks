import proofs.SmallResidentCompositionCopying.AmplificationChemistry
import proofs.SmallResidentCompositionCopying.AmplificationPartition

namespace SmallResidentCompositionCopying.Amplification
open Classical FiniteCopy CompositionalMemory
noncomputable section

def totalResidents (z : Counts) : ℕ := z.1.val+z.2.val+2
def composition (word : Word) (z : Counts) (s : Species) : ℝ :=
  (resident word z s.1 s.2 : ℝ)/(totalResidents z:ℝ)
def distance (word word' : Word) (z z' : Counts) : ℝ :=
  ∑ s : Species, |composition word z s-composition word' z' s|
def preparation : Counts := (⟨9,by decide⟩,⟨9,by decide⟩)

theorem preparation_admitted : newborn preparation := by norm_num [newborn,preparation]

theorem newborn_budget (z : Counts) (h : newborn z) : totalResidents z ≤ 38 := by
  dsimp [totalResidents,newborn] at *
  omega

theorem parent_budget (z : Counts) : totalResidents z ≤ 40 := by
  have ha := z.1.isLt
  have hb := z.2.isLt
  dsimp [totalResidents]
  omega

theorem resident_sum (word : Word) (z : Counts) :
    (∑ s : Species, resident word z s.1 s.2)=totalResidents z := by
  simp [resident,moduleCount,totalResidents,Fintype.sum_prod_type,Fin.sum_univ_succ]
  omega

theorem occupied_mass (word : Word) (z : Counts) (hz : newborn z) (i : Fin 2) :
    (1:ℝ)/20 ≤ composition word z (i,word i) := by
  have ht : (0:ℝ)<totalResidents z := by
    dsimp [totalResidents]
    positivity
  simp only [composition,resident]
  apply (le_div_iff₀ ht).2
  rcases hz with ⟨ha,hb⟩
  have ha' : (z.1.val:ℝ) ≤ 18 := by exact_mod_cast (show z.1.val ≤ 18 by omega)
  have hb' : (z.2.val:ℝ) ≤ 18 := by exact_mod_cast (show z.2.val ≤ 18 by omega)
  have ha₀ : (0:ℝ) ≤ z.1.val := Nat.cast_nonneg _
  have hb₀ : (0:ℝ) ≤ z.2.val := Nat.cast_nonneg _
  fin_cases i <;> norm_num [moduleCount,totalResidents] <;> linarith

/-- A fixed decoder uses normalized resident composition alone. -/
def decoder (p : Species → ℝ) (i : Fin 2) : Bool := decide (0 < p (i,true))

theorem decoder_correct (word : Word) (z : Counts) (hz : newborn z) :
    decoder (composition word z) = word := by
  funext i
  have hm := occupied_mass word z hz i
  cases h : word i
  · simp [decoder,composition,resident,h]
  · have hp : 0 < composition word z (i,true) := by rw [h] at hm; linarith
    simp [decoder,hp]

theorem separated_words (word word' : Word) (z z' : Counts)
    (hz : newborn z) (hne : word ≠ word') : (1:ℝ)/20 ≤ distance word word' z z' := by
  obtain ⟨i,hi⟩ : ∃ i, word i ≠ word' i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hm := occupied_mass word z hz i
  have he : composition word' z' (i,word i)=0 := by
    simp [composition,resident,Ne.symm hi]
  have hh := Finset.single_le_sum
    (fun (s : Species) (_ : s ∈ Finset.univ) =>
      abs_nonneg (composition word z s-composition word' z' s))
    (Finset.mem_univ (i,word i))
  rw [he,sub_zero,abs_of_nonneg (by linarith : 0 ≤ composition word z (i,word i))] at hh
  exact hm.trans hh

end
end SmallResidentCompositionCopying.Amplification
