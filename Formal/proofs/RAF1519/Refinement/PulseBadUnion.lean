import proofs.RAF1519.Refinement.PulseTailEvents
import proofs.RAF1519.Refinement.PulsePrepared

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 40000

def pulseBad {n : ℕ} (N : MolecularState n) (V : ℕ) (p : Fin n → Intervention) : Set (PulseOutcomes N) :=
  (⋃ q : Fin n × Bool × Bool, pulseMaterialBad N V p q.1 q.2.1 q.2.2) ∪
  (⋃ i : Fin n, pulseStockBad N V p i)

theorem postPulse_prepared_of_not_bad {n : ℕ} (N : MolecularState n) (V : ℕ) (hV : 10000 ≤ V)
    (p : Fin n → Intervention) (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s))))
    (o : PulseOutcomes N) (ho : o ∉ pulseBad N V p) : CountPrepared V (postPulseState N V p o) := by
  apply postPulse_prepared N V hV p hready o
  · intro b i
    have hh : ∀ sign, o ∉ pulseMaterialBad N V p i b sign := by
      intro sign hm
      exact ho (Or.inl (Set.mem_iUnion.mpr ⟨(i,b,sign),hm⟩))
    have hp := hh true
    have hn := hh false
    change ¬(V:ℝ)/100 ≤ (-1)*(categoricalStock (pulseNodeWeight i (materialWeight b)) o-
      categoricalMean (graphPulseCategory N p) (pulseNodeWeight i (materialWeight b))) at hn
    change ¬(V:ℝ)/100 ≤ 1*(categoricalStock (pulseNodeWeight i (materialWeight b)) o-
      categoricalMean (graphPulseCategory N p) (pulseNodeWeight i (materialWeight b))) at hp
    have hn := lt_of_not_ge hn
    have hp := lt_of_not_ge hp
    rw [one_mul] at hp
    exact abs_lt.mpr ⟨by linarith, hp⟩
  · intro i
    apply lt_of_not_ge
    intro hs
    exact ho (Or.inr (Set.mem_iUnion.mpr ⟨i,hs⟩))

theorem pulseBad_probability {n : ℕ} (N : MolecularState n) (V : ℕ) (hV : 0 < (V:ℝ))
    (p : Fin n → Intervention) (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s)))) :
    categoricalProbability (graphPulseCategory N p) (pulseBad N V p) ≤
      4*n*Real.exp (-(V:ℝ)/100000)+n*Real.exp (-(V:ℝ)/100000000) := by
  have hmat := (categoricalProbability_iUnion (graphPulseCategory N p) (graphPulseCategory_nonnegative N p)
    (fun q : Fin n × Bool × Bool => pulseMaterialBad N V p q.1 q.2.1 q.2.2)).trans
      (Finset.sum_le_sum (fun q _ => pulseMaterialBad_probability N V hV p q.1 (hready q.1) q.2.1 q.2.2))
  have hstock := (categoricalProbability_iUnion (graphPulseCategory N p) (graphPulseCategory_nonnegative N p)
    (pulseStockBad N V p)).trans
      (Finset.sum_le_sum (fun i _ => pulseStockBad_probability N V hV p i (hready i)))
  have hu := categoricalProbability_union (graphPulseCategory N p) (graphPulseCategory_nonnegative N p)
    (⋃ q : Fin n × Bool × Bool, pulseMaterialBad N V p q.1 q.2.1 q.2.2) (⋃ i, pulseStockBad N V p i)
  apply (hu.trans (add_le_add hmat hstock)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  ring

end
end RAF1519.Refinement
