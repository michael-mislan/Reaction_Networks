import proofs.ResourceLimitedCompetition.DeadlineScalar
import proofs.ResourceLimitedCompetition.PopulationOddsValue

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

noncomputable def deadlineValue (N W0 H L : ℕ) : ℝ :=
  Real.exp (-((N : ℝ)/1000)*(Real.log ((H : ℝ)+(L : ℝ))-Real.log (W0 : ℝ)))

theorem deadlineValue_nonneg (N W0 H L : ℕ) : 0 ≤ deadlineValue N W0 H L :=
  (Real.exp_pos _).le

theorem deadlineValue_growth_high (N W0 H L : ℕ) (hw : 0 < H+L) :
    deadlineValue N W0 (H+1) L=deadlineValue N W0 H L*Real.exp (deadlineJump N ((H : ℝ)+L)) := by
  unfold deadlineValue deadlineJump
  rw [← Real.exp_add]
  simp only [Nat.cast_add,Nat.cast_one]
  have hwr : 0 < (H : ℝ)+L := by exact_mod_cast hw
  have he : (H : ℝ)+1+L=((H : ℝ)+L)+1 := by ring
  rw [he,log_increment_identity _ hwr]
  congr 1
  ring

theorem deadlineValue_growth_low (N W0 H L : ℕ) (hw : 0 < H+L) :
    deadlineValue N W0 H (L+1)=deadlineValue N W0 H L*Real.exp (deadlineJump N ((H : ℝ)+L)) := by
  unfold deadlineValue deadlineJump
  rw [← Real.exp_add]
  simp only [Nat.cast_add,Nat.cast_one]
  have hwr : 0 < (H : ℝ)+L := by exact_mod_cast hw
  have he : (H : ℝ)+(L+1)=((H : ℝ)+L)+1 := by ring
  rw [he,log_increment_identity _ hwr]
  congr 1
  ring

noncomputable def activeAncestralObservable (N : ℕ) {D : Finset PopulationState}
    (f : ℕ → ℕ → ℝ) (x : StoppedPopulation D) : ℝ :=
  match x with
  | .inl s => ancestralObservable N f (.inl s)
  | .inr _ => 0

theorem active_ancestral_generator_le (γ : ℝ) (hγ : 0 ≤ γ) (Ω N M : ℕ)
    (zL zH : ℝ) (D : Finset PopulationState) (f : ℕ → ℕ → ℝ)
    (hf : ∀ H L, 0 ≤ f H L) (s : ActiveState D) :
    (stoppedPopulationModel γ hγ Ω N M zL zH D).generator (activeAncestralObservable N f) (.inl s) ≤
      (stoppedPopulationModel γ hγ Ω N M zL zH D).generator (ancestralObservable N f) (.inl s) := by
  classical
  have hnext (e : CellEvent s.val) :
      activeAncestralObservable N f (stoppedNext N M zL zH D (.inl s) ⟨s,e⟩) ≤
        ancestralObservable N f (stoppedNext N M zL zH D (.inl s) ⟨s,e⟩) := by
    generalize stoppedNext N M zL zH D (.inl s) ⟨s,e⟩=x
    cases x with
    | inl t => exact le_rfl
    | inr e => exact hf _ _
  have h := active_generator_le γ hγ Ω N M zL zH D (activeAncestralObservable N f) s
    (fun e => ancestralObservable N f (stoppedNext N M zL zH D (.inl s) ⟨s,e⟩)) hnext
  exact h.trans_eq (active_generator γ hγ Ω N M zL zH D (ancestralObservable N f) s).symm

end ResourceLimitedCompetition
