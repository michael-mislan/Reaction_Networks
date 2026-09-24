import proofs.ProductiveMemory.ExtractionInventory
import proofs.ProductiveMemory.ExtractionSupport

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy
noncomputable section
set_option Elab.async false

theorem productive_positive_enabled (N : ℕ) (rho gamma : ℝ) (s : ProductiveState)
    (e : ProductiveEvent s) (hr : 0 < productiveRate rho gamma N s e) : ProductiveEnabled s e := by
  rcases e with ⟨i,r | d⟩ | i
  · exact positive_resident_reactants (resourceCoefficient gamma s.population.resource N) (selectedCell s.population i).compartment r hr
  · by_contra hn
    have hz : (selectedCell s.population i).compartment.1 2=0 := by
      change ¬1 ≤ (selectedCell s.population i).compartment.1 2 at hn
      omega
    simp [productiveRate,propensity,hz] at hr
  · by_contra hn
    have hz : (selectedCell s.population i).compartment.1 2=0 := by
      change ¬1 ≤ (selectedCell s.population i).compartment.1 2 at hn
      omega
    simp [productiveRate,hz] at hr

/-- Literal history with separately accumulated resident production, growth consumption,
and intact-cell discard. Extraction counts include every batch/recovery extraction event. -/
inductive ProductiveHistory (N : ℕ) (initial : ProductiveState) : ProductiveState → ℝ → ℕ → ℕ → Prop
  | nil : ProductiveHistory N initial initial 0 0 0
  | event {s P G D} (h : ProductiveHistory N initial s P G D)
      (e : ProductiveEvent s) (he : ProductiveEnabled s e) :
      ProductiveHistory N initial (productiveOutcome N s e)
        (P+productiveInternalProduction s e) (G+productiveGrowthMark s e) D
  | transfer {s P G D} (h : ProductiveHistory N initial s P G D) (M : ℕ)
      (S : SerialTransferSelection.TransferSubset s.population.live.length M) :
      ProductiveHistory N initial ⟨SerialTransferSelection.exchangeSelectedMedium M s.population S,s.collected⟩
        P G (D+zInventory (SerialTransferSelection.discardedCells s.population.live.length M (selectedCell s.population) S))
  | refill {s P G D} (h : ProductiveHistory N initial s P G D) (Q : ℕ) :
      ProductiveHistory N initial ⟨⟨Q,s.population.live,0⟩,s.collected⟩ P G D

theorem chemicalInventory_z_cast (cs : List TaggedCell) : chemicalInventory cs 2=(zInventory cs:ℝ) := by
  simp [chemicalInventory,zInventory,Nat.cast_list_sum,List.map_map,Function.comp_def]

theorem productive_history_z_account (N : ℕ) (initial s : ProductiveState) (P : ℝ) (G D : ℕ)
    (h : ProductiveHistory N initial s P G D) :
    P=chemicalInventory s.population.live 2-chemicalInventory initial.population.live 2+
      ((s.collected:ℝ)-initial.collected)+(G:ℝ)+(D:ℝ) := by
  induction h with
  | nil => simp
  | event h e he ih =>
    have hs := productive_z_account_step N _ e he
    push_cast
    linarith only [ih,hs]
  | @transfer s P G D h M S ih =>
    have ht := SerialTransferSelection.actual_transfer_material_balance M _ S (fun c => c.compartment.1 2)
    have hh : chemicalInventory (SerialTransferSelection.exchangeSelectedMedium M _ S).live 2+
      (zInventory (SerialTransferSelection.discardedCells _ M (selectedCell _) S):ℝ)=chemicalInventory s.population.live 2 := by
      simp only [chemicalInventory_z_cast]
      exact_mod_cast ht
    dsimp only
    push_cast
    linarith only [ih,hh]
  | refill h Q ih => exact ih

theorem productive_positive_net_formation (N : ℕ) (initial s : ProductiveState) (P : ℝ) (G D : ℕ)
    (h : ProductiveHistory N initial s P G D) (hE : initial.collected=0)
    (hout : zInventory initial.population.live < s.collected) : 0 < P := by
  have hi := productive_history_z_account N initial s P G D h
  rw [chemicalInventory_z_cast,chemicalInventory_z_cast,hE] at hi
  have hz : (zInventory initial.population.live:ℝ)<s.collected := by exact_mod_cast hout
  have hl := Nat.cast_nonneg (α:=ℝ) (zInventory s.population.live)
  have hg := Nat.cast_nonneg (α:=ℝ) G
  have hd := Nat.cast_nonneg (α:=ℝ) D
  norm_num only [Nat.cast_zero,sub_zero] at hi
  linarith only [hi,hz,hl,hg,hd]

end
end ProductiveMemory
