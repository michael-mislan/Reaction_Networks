import proofs.SerialTransferSelection.BatchSource
import proofs.SerialTransferSelection.BatchInitialPotential

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem phase_active_cell_count (N M W0 : ℕ) (zL zH : ℝ)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) : s.val.live.length ≤ 8*M := by
  classical
  exact ((mem_phasePopulationBox N M W0 s.val).mp (Finset.mem_filter.mp s.property).1).2.1.1

theorem phase_active_source_energy (N M W0 : ℕ) (zL zH : ℝ)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH))
    (c : TaggedCell) (hc : c ∈ s.val.live) : cellEnergy zL zH c < outerEnergy := by
  have hs := phaseActiveDomain_safe N M W0 zL zH s.val s.property
  exact (hs.2.2.2.2.2 c hc).trans (by norm_num [innerEnergy,outerEnergy])

theorem phase_active_reserve (N M W0 : ℕ) (hN : 0 < N) (hW : W0 ≤ 2*N*M)
    (zL zH : ℝ) (s : ActiveState (phaseActiveDomain N M W0 zL zH)) :
    s.val.divisions < 7*M := by
  have hs := phaseActiveDomain_safe N M W0 zL zH s.val s.property
  exact phase_batch_division_reserve N M W0 hN hW s.val hs.2.2.2.2.1
    hs.2.2.1 hs.1 hs.2.2.2.1

/-- The literal summed raw-cell drift on the new phase domain.
Boundary/partition comparisons are still needed to bound the stopped observable. -/
theorem phase_raw_spatial_generator_bound (N M W0 : ℕ) (hN : 1 ≤ N)
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (zL zH γ : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (s : ActiveState (phaseActiveDomain N M W0 zL zH)) :
    (∑ e : CellEvent s.val, eventRate γ (4*W0) ⟨s,e⟩*
      (rawEventPotential (cellSpatial N zL zH) s.val e-potentialSum (cellSpatial N zL zH) s.val)) ≤
      8*(M : ℝ)*(((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2))) := by
  rw [raw_event_generator_sum]
  have hs := phaseActiveDomain_safe N M W0 zL zH s.val s.property
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s.val.live.length)))
    (fun i _ => cellSpatial_source_bound N hN hlarge zL zH γ hzL hzH hsL hsH hγ hγmax
      s.val.resource (4*W0) hs.2.1 (selectedCell s.val i)
      (hs.2.2.2.2.1 _ (selected_mem s.val i)).1
      (hs.2.2.2.2.1 _ (selected_mem s.val i)).2.le
      (phase_active_source_energy N M W0 zL zH s _ (selected_mem s.val i)))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  have hc : (s.val.live.length : ℝ) ≤ 8*(M : ℝ) := by
    exact_mod_cast phase_active_cell_count N M W0 zL zH s
  exact hb.trans (mul_le_mul_of_nonneg_right hc
    (by unfold localAlpha innerEnergy outerEnergy; positivity))

end SerialTransferSelection
