import proofs.SerialTransferSelection.TransferConcentration
import proofs.ResourceLimitedCompetition.AncestralGenerator

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem retainSubset_sum {α : Type*} (L M : ℕ) (cells : Fin L → α) (S : TransferSubset L M)
    (F : α → ℝ) :
    ((retainSubset L M cells S).map F).sum=∑ i ∈ S.val, F (cells i) := by
  have h := ((Finset.sort_perm_toList S.val (· ≤ ·)).map (fun i => F (cells i))).sum_eq
  simpa only [retainSubset,List.map_map,Function.comp_def,Finset.sum_map_toList] using h

theorem weightedSubsetTotal_selected (L M : ℕ) (w : Fin L → ℝ) (S : TransferSubset L M) :
    weightedSubsetTotal L M w S=∑ i ∈ S.val, w i := by
  classical
  simp [weightedSubsetTotal,subsetIndicator,ite_mul]

noncomputable def ancestralWeight (N : ℕ) (tag : Bool) (c : TaggedCell) : ℝ :=
  if c.high=tag then (c.compartment.2 : ℝ)/(2*(N : ℝ)) else 0

theorem ancestralWeight_sum (N : ℕ) (tag : Bool) (cs : List TaggedCell) :
    (cs.map (ancestralWeight N tag)).sum=(ancestralMembrane tag cs : ℝ)/(2*(N : ℝ)) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    by_cases he : c.high=tag
    · simp [ancestralWeight,he,ancestralMembrane_cons,ih,add_div]
    · simp [ancestralWeight,he,ancestralMembrane_cons,ih]

theorem ancestralWeight_bounds (N : ℕ) (hN : 0 < N) (tag : Bool) (c : TaggedCell)
    (hm : c.compartment.2 ≤ 2*N) : 0 ≤ ancestralWeight N tag c ∧ ancestralWeight N tag c ≤ 1 := by
  unfold ancestralWeight
  split_ifs
  · constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < 2*(N : ℝ))).mpr
      exact_mod_cast hm
  · norm_num

def exchangeSelectedMedium (M : ℕ) (s : PopulationState) (S : TransferSubset s.live.length M) : PopulationState :=
  ⟨0,retainSubset s.live.length M (selectedCell s) S,0⟩

theorem exchangeSelectedMedium_length (M : ℕ) (s : PopulationState) (S : TransferSubset s.live.length M) :
    (exchangeSelectedMedium M s S).live.length=M :=
  retainSubset_length _ _ _ _

theorem exchangeSelectedMedium_preserves (M : ℕ) (s : PopulationState) (S : TransferSubset s.live.length M)
    (c : TaggedCell) (hc : c ∈ (exchangeSelectedMedium M s S).live) : c ∈ s.live := by
  obtain ⟨i,_,hi⟩ := retainSubset_mem _ _ _ S c hc
  rw [← hi]
  exact selected_mem s i

theorem exchangeSelectedMedium_resource (M : ℕ) (s : PopulationState) (S : TransferSubset s.live.length M) :
    (exchangeSelectedMedium M s S).resource=0 := rfl

theorem selected_weight_membrane (N M : ℕ) (tag : Bool) (s : PopulationState)
    (S : TransferSubset s.live.length M) :
    weightedSubsetTotal s.live.length M (fun i => ancestralWeight N tag (selectedCell s i)) S=
      (ancestralMembrane tag (exchangeSelectedMedium M s S).live : ℝ)/(2*(N : ℝ)) := by
  rw [weightedSubsetTotal_selected]
  rw [← retainSubset_sum s.live.length M (selectedCell s) S (ancestralWeight N tag)]
  exact ancestralWeight_sum N tag _

theorem full_weight_membrane (N : ℕ) (tag : Bool) (s : PopulationState) :
    (∑ i : Fin s.live.length, ancestralWeight N tag (selectedCell s i))=
      (ancestralMembrane tag s.live : ℝ)/(2*(N : ℝ)) := by
  rw [sum_selected_cells]
  exact ancestralWeight_sum N tag _

end SerialTransferSelection
