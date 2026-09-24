import proofs.CompositionalMemory.WordBirthLaw
import proofs.CompositionalMemory.WordFirstPhase

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

noncomputable def wordAfterDivision {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a, center i a ≤ 34) (σ : Fin k → Bool) :
    StoppedModularState (productDomain N center (wordEnergy σ) (2*innerEnergy)) →
      FiniteLaw (WordBirthOutcome N center σ)
  | none => FiniteLaw.pure none
  | some s => if s.val.2=2*(k*N) then wordPartitionLaw N hN center hc σ s.val.1 else FiniteLaw.pure none

noncomputable def wordPhaseTwoLaw {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a, center i a ≤ 34) (σ : Fin k → Bool)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (retainedModularModel γ w hγ hw N (productDomain N center (wordEnergy σ) (2*innerEnergy))).total x ≤ q)
    (s : {s : ModularCountState k // s ∈ productDomain N center (wordEnergy σ) (2*innerEnergy)}) :
    FiniteLaw (WordBirthOutcome N center σ) :=
  (poissonLaw ((retainedModularModel γ w hγ hw N (productDomain N center (wordEnergy σ) (2*innerEnergy))).uniformize q hq hclock)
    (q*t) (some s)).bind (wordAfterDivision N hN center hc σ)

noncomputable def wordEnterInner {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a, center i a ≤ 34) (σ : Fin k → Bool)
    (s : {s : ModularCountState k // s ∈ productDomain N center (wordEnergy σ) outerEnergy})
    (he : ∀ i, wordEnergy σ i (fun a => modularConcentration s.val i a-center i a) ≤ innerEnergy) :
    {s : ModularCountState k // s ∈ productDomain N center (wordEnergy σ) (2*innerEnergy)} := by
  have hmem := (mem_productDomain hk N hN center hc _ (word_energy_lower σ) outerEnergy (by norm_num [outerEnergy]) s.val).mp s.property
  refine ⟨s.val,(mem_productDomain hk N hN center hc _ (word_energy_lower σ) (2*innerEnergy)
    (by norm_num [innerEnergy,outerEnergy]) s.val).mpr ⟨hmem.1,hmem.2.1,?_⟩⟩
  intro i
  have hA : 0 < innerEnergy := by norm_num [innerEnergy,outerEnergy]
  linarith only [he i,hA]

noncomputable def wordAfterRecovery {k : ℕ} (hk : 1 ≤ k)
    (γ : ℝ) (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ)
    (N : ℕ) (hN : 1 ≤ N) (center : Fin k → Point) (hc : ∀ i a, center i a ≤ 34) (σ : Fin k → Bool)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (retainedModularModel γ w hγ hw N (productDomain N center (wordEnergy σ) (2*innerEnergy))).total x ≤ q) :
    StoppedModularState (productDomain N center (wordEnergy σ) outerEnergy) → FiniteLaw (WordBirthOutcome N center σ) := by
  classical
  exact fun x => match x with
  | none => FiniteLaw.pure none
  | some s => if h : s.val.2 < 2*(k*N) ∧ ∀ i,
      wordEnergy σ i (fun a => modularConcentration s.val i a-center i a) ≤ innerEnergy then
      wordPhaseTwoLaw γ w hw hγ N hN center hc σ q t hq hclock (wordEnterInner hk N hN center hc σ s h.2)
    else FiniteLaw.pure none

noncomputable def wordBirthAsOuter {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a, center i a ≤ 34) (σ : Fin k → Bool)
    (n : WordBirthCount N center σ) :
    {s : ModularCountState k // s ∈ productDomain N center (wordEnergy σ) outerEnergy} := by
  have he := (mem_wordBirthCounts N hN center hc σ n.val).mp n.property
  refine ⟨(n.val,k*N),(mem_productDomain hk N hN center hc _ (word_energy_lower σ) outerEnergy
    (by norm_num [outerEnergy]) (n.val,k*N)).mpr ⟨le_rfl,by omega,?_⟩⟩
  intro i
  rw [module_lattice_concentration hk N n.val i]
  have h := he i
  norm_num [innerEnergy,outerEnergy] at h ⊢
  linarith only [h]

/-- Literal growth in two deterministic intervals, retaining division states,
then complementary partition. None denotes a prescribed certificate failure. -/
noncomputable def wordGenerationLaw {k : ℕ} (hk : 1 ≤ k)
    (γ : ℝ) (hγ : 0 < γ) (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (N : ℕ) (hN : 1 ≤ N) (center : Fin k → Point) (hc : ∀ i a, center i a ≤ 34) (σ : Fin k → Bool)
    (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀ : ℝ)) (hq₁ : 0 < (q₁ : ℝ))
    (hc₀ : ∀ x, (retainedModularModel γ w hγ.le hw N (productDomain N center (wordEnergy σ) outerEnergy)).total x ≤ q₀)
    (hc₁ : ∀ x, (retainedModularModel γ w hγ.le hw N (productDomain N center (wordEnergy σ) (2*innerEnergy))).total x ≤ q₁)
    (n : WordBirthCount N center σ) : FiniteLaw (WordBirthOutcome N center σ) :=
  (poissonLaw ((retainedModularModel γ w hγ.le hw N (productDomain N center (wordEnergy σ) outerEnergy)).uniformize q₀ hq₀ hc₀)
    (q₀*2688) (some (wordBirthAsOuter hk N hN center hc σ n))).bind
      (wordAfterRecovery hk γ w hw hγ.le N hN center hc σ q₁ (modularDeadline γ hγ) hq₁ hc₁)

end CompositionalMemory
