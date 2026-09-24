import proofs.DigraphRealizability.HornElimination
namespace DigraphRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A family-only rule: choose a minimal residual set and a fresh forced coordinate. -/
inductive PolicyEliminates (K : Finset (Finset E)) (pick : Finset (Finset E) → Finset E) :
    Finset (Finset E) → Set E → Prop
  | done (H) : PolicyEliminates K pick K H
  | step {U H B r}
      (chosen : B = pick U)
      (bad : B ∈ U ∧ B ∉ K)
      (minimal : ∀ T ∈ U, T ∉ K → T ⊆ B → T = B)
      (outside : r ∉ B)
      (forced : ∀ X ∈ K, B ⊆ X → r ∈ X)
      (fresh : r ∉ H)
      (tail : PolicyEliminates K pick (trim U B r) (insert r H)) :
      PolicyEliminates K pick U H

/-- Completeness has no hypothesized normalizer: it invokes the proved replacement lemma. -/
theorem policy_complete (K U : Finset (Finset E))
    (pick : Finset (Finset E) → Finset E)
    (valid : ∀ W, K ⊆ W → W ≠ K →
      pick W ∈ W ∧ pick W ∉ K ∧
      ∀ T ∈ W, T ∉ K → T ⊆ pick W → T = pick W) :
    ∀ G L : Set (Rule E), G ⊆ L → SingleHead L →
    (∀ X, X ∈ U ↔ Models G X) →
    (∀ X, X ∈ K ↔ Models L X) →
    PolicyEliminates K pick U (Heads G) := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro G L hGL hL hU hK
    by_cases heq : U = K
    · subst U
      exact PolicyEliminates.done _
    have hKU : K ⊆ U := by
      intro X hX
      exact (hU X).mpr (fun q hq => (hK X).mp hX q (hGL hq))
    let B := pick U
    obtain ⟨hBU,hBK,minimal⟩ := valid U hKU heq
    have hres : MinimalResidual G L B := by
      refine ⟨(hU B).mp hBU, fun h => hBK ((hK B).mpr h), ?_⟩
      intro T hTG hTL hTB
      exact minimal T ((hU T).mpr hTG) (fun h => hTL ((hK T).mp h)) hTB
    obtain ⟨r, L', hr, hf, hs, hi, hm, hforce⟩ := extend_completion hGL hL hres
    have htrim : trim U B r ⊂ U := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro eq
      have : B ∈ trim U B r := eq.symm ▸ hBU
      have cond := (Finset.mem_filter.mp this).2
      exact cond.elim (fun h => h (Finset.Subset.refl B)) hr
    have hmodels : ∀ X, X ∈ trim U B r ↔ Models (insert (B,r) G) X := by
      intro X
      rw [models_insert]
      simp only [trim, Finset.mem_filter, hU X]
      tauto
    have htarget : ∀ X, X ∈ K ↔ Models L' X := fun X => (hK X).trans (hm X).symm
    have tail := ih (trim U B r) htrim (insert (B,r) G) L' hi hs hmodels htarget
    rw [heads_insert] at tail
    exact PolicyEliminates.step rfl ⟨hBU,hBK⟩ minimal hr
      (fun X hX => hforce X ((hK X).mp hX)) hf tail


end DigraphRealizability
