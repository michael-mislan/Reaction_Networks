import proofs.SerialTransferSelection.InitialPopulation
import proofs.SerialTransferSelection.PopulationPhase
import proofs.SerialTransferSelection.ParameterMargins

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem balanced_initial_newborn (N K : ℕ) (hN : 1000000000000 ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)) :
    ∃ s : ReadyPopulation N (2*K) zL zH, (∀ b, ancestralCount b s.val.live=K) ∧ (∀ c ∈ s.val.live, c.compartment.2=N) := by
  obtain ⟨nL,hL⟩ := low_ready_nonempty zL hzL N N hN le_rfl (by omega)
  obtain ⟨nH,hH⟩ := high_ready_nonempty zH hzH N N hN le_rfl (by omega)
  let s := preparePhaseBatch (balancedCells K N nL nH)
  have hmem (c : TaggedCell) (hc : c ∈ s.live) :
      c=⟨false,(nL,N)⟩ ∨ c=⟨true,(nH,N)⟩ := by
    obtain hc | hc := List.mem_append.mp hc
    · exact Or.inl (List.mem_replicate.mp hc).2
    · exact Or.inr (List.mem_replicate.mp hc).2
  have hs : PhaseReadyPopulation N (2*K) zL zH s := by
    refine ⟨?_,rfl,rfl,?_,?_⟩
    · simp [s,preparePhaseBatch,balancedCells]
      omega
    · intro c hc
      obtain rfl | rfl := hmem c hc <;> exact ⟨le_rfl,by change N < 2*N; omega⟩
    · intro c hc
      obtain rfl | rfl := hmem c hc
      · exact hL.2.2
      · exact hH.2.2
  refine ⟨⟨s,readyPopulation_mem N (2*K) (by omega) zL zH hzL hzH s hs⟩,?_⟩
  constructor
  · intro b
    exact balancedCells_count K N nL nH b
  · intro c hc
    obtain rfl | rfl := hmem c hc <;> rfl



theorem newborn_ancestral_size (N : ℕ) (cs : List TaggedCell)
    (h : ∀ c ∈ cs, c.compartment.2=N) (b : Bool) :
    ancestralMembrane b cs=N*ancestralCount b cs := by
  induction cs with
  | nil => simp [ancestralCount]
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (fun d hd => h d (by simp [hd]))
    by_cases hb : c.high=b
    · simp [ancestralMembrane_cons,ancestralCount,hb,hc] at ht ⊢
      rw [ht]
      ring
    · simp [ancestralMembrane_cons,ancestralCount,hb] at ht ⊢
      exact ht

theorem newborn_phase_zero (N : ℕ) (hN : 0 < N) (s : PopulationState)
    (h : ∀ c ∈ s.live, c.compartment.2=N)
    (hc : ∀ b, 0 < ancestralCount b s.live) : populationPhase s=0 := by
  have hm (b : Bool) : (ancestralMembrane b s.live : ℝ)/(ancestralCount b s.live : ℝ)=N := by
    rw [newborn_ancestral_size N s.live h b, Nat.cast_mul]
    exact mul_div_cancel_right₀ _ (by exact_mod_cast Nat.ne_of_gt (hc b))
  unfold populationPhase
  rw [hm true,hm false,div_self (by exact_mod_cast Nat.ne_of_gt hN),Real.log_one]

theorem newborn_endpoint_count_gain (N : ℕ) (hN : 0 < N) (s t : PopulationState)
    (hvs : ValidVolumes N s) (hvt : ValidVolumes N t)
    (hnew : ∀ c ∈ s.live, c.compartment.2=N)
    (hcs : ∀ b, 0 < ancestralCount b s.live) (hct : ∀ b, 0 < ancestralCount b t.live)
    (g : ℝ) (hg : g < sizeLogOdds t-sizeLogOdds s) :
    g-Real.log 2 < countLogOdds t-countLogOdds s := by
  have hs := population_phase_identity_bounds N hN s hvs hcs
  have ht := population_phase_identity_bounds N hN t hvt hct
  have hz := newborn_phase_zero N hN s hnew hcs
  rw [hs.1,ht.1]
  linarith only [hg,hz,ht.2.2]

theorem newborn_one_cycle_rational : (519/24500 : ℝ) ≤ cycleSizeGain (1/50)-Real.log 2 := by
  have h := two_cycle_count_gain_lower
  unfold cycleSizeGain
  linarith only [h]

theorem newborn_two_cycle_rational : (3322/6125 : ℝ) ≤ 2*cycleSizeGain (1/50)-Real.log 2 := by
  have h := two_cycle_count_gain_lower
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hl
  unfold cycleSizeGain
  linarith only [h,hl]

end SerialTransferSelection
