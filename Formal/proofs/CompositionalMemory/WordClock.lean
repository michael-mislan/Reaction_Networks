import proofs.CompositionalMemory.EarlyClock
import proofs.CompositionalMemory.LateClock
import proofs.CompositionalMemory.WordRecovery

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set

noncomputable def modularDeadline (γ : ℝ) (hγ : 0 < γ) : NNReal :=
  ⟨11/(5*γ),by positivity⟩

theorem modular_deadline_after_recovery (γ : ℝ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) : (2688 : ℝ) ≤ modularDeadline γ hγ := by
  change (2688 : ℝ) ≤ 11/(5*γ)
  apply (le_div_iff₀ (by positivity : 0 < 5*γ)).mpr
  linarith only [hγmax]

theorem modular_deadline_physical (k : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    (k : ℝ)*(modularDeadline γ hγ : ℝ) = 11*(k : ℝ)/(5*γ) := by
  change (k : ℝ)*(11/(5*γ)) = _
  ring

theorem word_early_division {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (z₀ z₁ γ : ℝ) (σ : Fin k → Bool) (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (b : ℝ) (hb : b ≤ 1/32000000) (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (retainedModularModel γ w hγ hw N
      (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b)).total s ≤ q)
    (s : {s : ModularCountState k // s ∈ productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b})
    (hstart : s.val.2=k*N) :
    ((retainedModularModel γ w hγ hw N (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b)).uniformize q hq hclock).poissonized (q*2688)
      (FiniteKernel.eventIndicator (modularDivisionRecorded N (productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b))) (some s) ≤
      Real.exp (-((k*N : ℕ) : ℝ)/125) := by
  apply modular_early_division_tail γ (4*γ) w hw hγ (by positivity) N _
    (fun u hu _ => (word_membrane_rate_bounds hk N hN z₀ z₁ γ σ hγ h₀ h₁ b hb u hu).2)
    q 2688 hq _ hclock s hstart
  norm_num
  linarith only [hγmax]

theorem word_late_division {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (z₀ z₁ γ : ℝ) (σ : Fin k → Bool) (hγ : 0 < γ)
    (h₀ : z₀ ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (h₁ : z₁ ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (b : ℝ) (hb : b ≤ 1/32000000) (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (killedModularModel γ w hγ.le hw (wordPredivisionDomain N z₀ z₁ σ b)).total s ≤ q)
    (hdecay : 19*(γ/2)*((k*N : ℕ) : ℝ)/400 ≤ q)
    (s : {s : ModularCountState k // s ∈ wordPredivisionDomain N z₀ z₁ σ b}) :
    ((killedModularModel γ w hγ.le hw (wordPredivisionDomain N z₀ z₁ σ b)).uniformize q hq hclock).poissonized (q*modularDeadline γ hγ)
      (FiniteKernel.eventIndicator (modularStillLiving (wordPredivisionDomain N z₀ z₁ σ b))) (some s) ≤
      Real.exp (-9*((k*N : ℕ) : ℝ)/4000) := by
  classical
  have hc := word_center_bounds z₀ z₁ σ h₀ h₁
  have hsprod : s.val ∈ productDomain N (wordCenter z₀ z₁ σ) (wordEnergy σ) b :=
    (Finset.mem_filter.mp s.property).1
  have hstart := ((mem_productDomain hk N hN _ hc.1 _ (word_energy_lower σ) b hb s.val).mp hsprod).1
  apply modular_late_division_tail γ (γ/2) w hw hγ.le (by positivity) N _
    (fun u hu => (Finset.mem_filter.mp hu).2)
    (fun u hu => (word_membrane_rate_bounds hk N hN z₀ z₁ γ σ hγ.le h₀ h₁ b hb u
      (Finset.mem_filter.mp hu).1).1)
    q (modularDeadline γ hγ) hq _ hclock hdecay s hstart
  change (γ/2)*(11/(5*γ))=11/10
  field_simp
  ring

end CompositionalMemory
