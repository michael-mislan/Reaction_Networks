import proofs.OverlappingSiphonInvasion.GeneralPermanence
import proofs.OverlappingSiphonInvasion.SourceComposition

noncomputable section
open Matrix CoreCriticalSiphon Filter Topology
namespace OverlappingSiphonInvasion

/-- Full covered normal-space version of the source overlap identity. The
equivalence explicitly prevents omitted modes or repeated normal coordinates. -/
theorem covered_source_overlap_charpoly {U V I : Type*}
    [Fintype U] [Fintype V] [Fintype I] [DecidableEq U] [DecidableEq V] [DecidableEq I]
    (Q : SourceCRN) (k : Q.Reaction → ℝ) (hk : ∀ r, 0 < k r)
    (S1 S2 : Finset Q.Species) (hS1 : IsSiphon Q S1) (hS2 : IsSiphon Q S2)
    (y : Q.Species → ℝ) (hy1 : y ∈ BoundaryFace Q S1) (hy2 : y ∈ BoundaryFace Q S2)
    (e : ((U ⊕ V) ⊕ I) ≃ ↥(S1 ∪ S2))
    (hu1 : ∀ u, (e (privateU u)).val ∈ S1) (hu2 : ∀ u, (e (privateU u)).val ∉ S2)
    (hv1 : ∀ v, (e (privateV v)).val ∉ S1) (hv2 : ∀ v, (e (privateV v)).val ∈ S2)
    (hi1 : ∀ i, (e (sharedI i)).val ∈ S1) (hi2 : ∀ i, (e (sharedI i)).val ∈ S2) :
    let N : Matrix ↥(S1 ∪ S2) ↥(S1 ∪ S2) ℝ := fun i j => normalEntry Q k y i.val j.val
    let M := N.submatrix e e
    N.charpoly*(M.submatrix sharedI sharedI).charpoly =
      (M.submatrix siphonU siphonU).charpoly*(M.submatrix siphonV siphonV).charpoly := by
  intro N M
  have he : M.charpoly = N.charpoly := Matrix.charpoly_reindex e.symm N
  rw [← he]
  exact source_overlap_charpoly Q k hk S1 S2 hS1 hS2 y hy1 hy2 (fun i => (e i).val)
    hu1 hu2 hv1 hv2 hi1 hi2

abbrev ConcreteNormalIndex := (Fin 1 ⊕ Fin 1) ⊕ Fin 1

def concreteNormalMap : ConcreteNormalIndex → ↥(siphonA ∪ siphonB)
  | Sum.inl (Sum.inl _) => ⟨1,by decide⟩
  | Sum.inl (Sum.inr _) => ⟨2,by decide⟩
  | Sum.inr _ => ⟨3,by decide⟩

def concreteNormalEquiv : ConcreteNormalIndex ≃ ↥(siphonA ∪ siphonB) :=
  Equiv.ofBijective concreteNormalMap (by decide)

def fullNormalMatrix (p : Rates) (s : ℝ) :
    Matrix ↥(siphonA ∪ siphonB) ↥(siphonA ∪ siphonB) ℝ :=
  fun i j => normalEntry source (rateVector p) (face1 s 0) i.val j.val

def indexedNormalMatrix (p : Rates) (s : ℝ) : Matrix ConcreteNormalIndex ConcreteNormalIndex ℝ :=
  (fullNormalMatrix p s).submatrix concreteNormalEquiv concreteNormalEquiv

theorem concrete_full_overlap (p : Rates) (hp : PositiveRates p) (s : ℝ) :
    (fullNormalMatrix p s).charpoly*
      ((indexedNormalMatrix p s).submatrix sharedI sharedI).charpoly =
    ((indexedNormalMatrix p s).submatrix siphonU siphonU).charpoly*
      ((indexedNormalMatrix p s).submatrix siphonV siphonV).charpoly := by
  have hy1 : face1 s 0 ∈ BoundaryFace source siphonA := by
    intro i hi
    simp only [siphonA,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> rfl
  have hy2 : face1 s 0 ∈ BoundaryFace source siphonB := by
    intro i hi
    simp only [siphonB,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> rfl
  exact covered_source_overlap_charpoly source (rateVector p) hp siphonA siphonB
    source_siphonA source_siphonB (face1 s 0) hy1 hy2 concreteNormalEquiv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Integrated selected root: the exact full-space source overlap correction
and arbitrary-positive-rate strict permanence, including positive global
existence. No fixed witness, asymptotic premise, or omitted normal mode. -/
theorem source_composition_and_strict_permanence (p : Rates) (hp : PositiveRates p)
    (he1 : p.mu1/p.alpha1 < p.recruitment/p.mu0)
    (he2 : p.mu2/p.alpha2 < p.recruitment/p.mu0) (hi : StrictMutualInvasion p) :
    (∀ s : ℝ, (fullNormalMatrix p s).charpoly*
      ((indexedNormalMatrix p s).submatrix sharedI sharedI).charpoly =
      ((indexedNormalMatrix p s).submatrix siphonU siphonU).charpoly*
      ((indexedNormalMatrix p s).submatrix siphonV siphonV).charpoly) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ x0 : State, (∀ i, 0 < x0 i) →
      ∃ X : ℝ → State, X 0 = x0 ∧ IsTrajectory p X ∧
        ∀ᶠ t in atTop, ∀ i, ε ≤ X t i ∧ X t i ≤ p.recruitment/deathFloor p+1 :=
  ⟨concrete_full_overlap p hp,source_strict_permanence p hp he1 he2 hi⟩

end OverlappingSiphonInvasion
