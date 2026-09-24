import proofs.CompositionalMemory.DivisionNecessity

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

noncomputable def necessitySurvival (k N : ℕ) : ℝ := (1-(1/2 : ℝ)^(280*N))^k

theorem necessitySurvival_nonneg (k N : ℕ) : 0 ≤ necessitySurvival k N := by
  apply pow_nonneg
  exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))

theorem finite_bind_failure_lower {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (K : α → FiniteLaw (Option β)) (p : ℝ)
    (h : ∀ x, p ≤ (K x).mass none) : p ≤ (μ.bind K).mass none := by
  have hm := μ.expect_mono (fun _ => p) (fun x => (K x).mass none) h
  rw [μ.expect_const] at hm
  exact hm

theorem source_after_division_failure_lower {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool)
    (x : StoppedModularState (productDomain N (sourceWordCenter σ) (wordEnergy σ) (2*innerEnergy))) :
    1-necessitySurvival k N ≤
      (wordAfterDivision N hN (sourceWordCenter σ) (sourceWordCenter_upper σ) σ x).mass none := by
  classical
  have hp : 1-necessitySurvival k N ≤ 1 := sub_le_self _ (necessitySurvival_nonneg k N)
  cases x with
  | none => simpa [wordAfterDivision,FiniteLaw.pure] using hp
  | some s =>
    by_cases hs : s.val.2=2*(k*N)
    · simpa only [wordAfterDivision,if_pos hs,necessitySurvival] using
        source_division_partition_obstruction N hN σ (2*innerEnergy) s
    · simpa [wordAfterDivision,hs,FiniteLaw.pure] using hp

theorem source_phase_two_failure_lower {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N) (σ : Fin k → Bool)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hc : ∀ x, (retainedModularModel γ w hγ hw N
      (productDomain N (sourceWordCenter σ) (wordEnergy σ) (2*innerEnergy))).total x ≤ q)
    (s : {s // s ∈ productDomain N (sourceWordCenter σ) (wordEnergy σ) (2*innerEnergy)}) :
    1-necessitySurvival k N ≤
      (wordPhaseTwoLaw γ w hw hγ N hN (sourceWordCenter σ) (sourceWordCenter_upper σ) σ q t hq hc s).mass none :=
  finite_bind_failure_lower _ _ _ (source_after_division_failure_lower N hN σ)

theorem source_after_recovery_failure_lower {k : ℕ} (hk : 1 ≤ k)
    (γ : ℝ) (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ)
    (N : ℕ) (hN : 1 ≤ N) (σ : Fin k → Bool) (q t : NNReal) (hq : 0 < (q : ℝ))
    (hc : ∀ x, (retainedModularModel γ w hγ hw N
      (productDomain N (sourceWordCenter σ) (wordEnergy σ) (2*innerEnergy))).total x ≤ q)
    (x : StoppedModularState (productDomain N (sourceWordCenter σ) (wordEnergy σ) outerEnergy)) :
    1-necessitySurvival k N ≤
      (wordAfterRecovery hk γ w hw hγ N hN (sourceWordCenter σ) (sourceWordCenter_upper σ) σ q t hq hc x).mass none := by
  classical
  have hp : 1-necessitySurvival k N ≤ 1 := sub_le_self _ (necessitySurvival_nonneg k N)
  cases x with
  | none => simpa [wordAfterRecovery,FiniteLaw.pure] using hp
  | some s =>
    dsimp only [wordAfterRecovery]
    split
    · exact source_phase_two_failure_lower γ w hw hγ N hN σ q t hq hc _
    · simpa [FiniteLaw.pure] using hp

theorem source_generation_failure_lower {k : ℕ} (hk : 1 ≤ k)
    (γ : ℝ) (hγ : 0 < γ) (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (N : ℕ) (hN : 1 ≤ N) (σ : Fin k → Bool)
    (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀ : ℝ)) (hq₁ : 0 < (q₁ : ℝ))
    (hc₀ : ∀ x, (retainedModularModel γ w hγ.le hw N
      (productDomain N (sourceWordCenter σ) (wordEnergy σ) outerEnergy)).total x ≤ q₀)
    (hc₁ : ∀ x, (retainedModularModel γ w hγ.le hw N
      (productDomain N (sourceWordCenter σ) (wordEnergy σ) (2*innerEnergy))).total x ≤ q₁)
    (n : WordBirthCount N (sourceWordCenter σ) σ) :
    1-necessitySurvival k N ≤
      (wordGenerationLaw hk γ hγ w hw N hN (sourceWordCenter σ) (sourceWordCenter_upper σ)
        σ q₀ q₁ hq₀ hq₁ hc₀ hc₁ n).mass none :=
  finite_bind_failure_lower _ _ _
    (source_after_recovery_failure_lower hk γ w hw hγ.le N hN σ q₁ (modularDeadline γ hγ) hq₁ hc₁)

end CompositionalMemory
