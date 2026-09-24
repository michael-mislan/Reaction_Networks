import proofs.ResourceLimitedCompetition.FiniteBatchCompetition
import proofs.ResourceLimitedCompetition.Founders
import proofs.ResourceLimitedCompetition.ErrorDecay

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set Filter
open scoped NNReal Topology

noncomputable local instance MainDecidableEq (D : Finset PopulationState) :
    DecidableEq (StoppedPopulation D) := Classical.decEq _

/-- The source birth regions are inhabited, and their founders compete under the
literal finite-batch jump law with an explicit error tending to zero. -/
def SourceCompetitionConclusion : Prop :=
  ∃ zL zH : ℝ,
    zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000) ∧
    zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000) ∧
    Stationary sourceRates (lift sourceRates zL) ∧
    Stationary sourceRates (lift sourceRates zH) ∧
    (∀ M γ, Tendsto (fun N : ℕ => competitionError N M γ) atTop (𝓝 0)) ∧
    ∀ (γ : ℝ) (hγ : 0 < γ), γ ≤ 1/100000000000 →
    ∀ N h l : ℕ, 0 < h → 0 < l → (140000000000000000000 : ℝ) ≤ N →
    (∃ nH nL, SourceBirths N zL zH nH nL) ∧
    ∀ nH nL, SourceBirths N zL zH nH nL →
    ∃ s : ActiveState (activeDomain N (h+l) zL zH),
      s.val=founderPopulation N h l nH nL ∧
      ∃ (q t : ℝ≥0) (hq : 0 < (q : ℝ))
        (hbound : ∀ x, (stoppedPopulationModel γ hγ.le (4*(N*(h+l))) N (h+l) zL zH
          (activeDomain N (h+l) zL zH)).total x ≤ q),
        (t : ℝ)=8/γ ∧
        1-competitionError N (h+l) γ ≤
          ((stoppedPopulationModel γ hγ.le (4*(N*(h+l))) N (h+l) zL zH
            (activeDomain N (h+l) zL zH)).uniformize q hq hbound).poissonized
            (q*t) (FiniteKernel.eventIndicator (competitionSuccessSet N h l zL zH)) (.inl s)

theorem source_resource_limited_competition : SourceCompetitionConclusion := by
  classical
  obtain ⟨zL,hzL,hsL⟩ := low_source_root
  obtain ⟨zH,hzH,hsH⟩ := high_source_root
  refine ⟨zL,zH,hzL,hzH,hsL,hsH,competition_error_tendsto_zero,?_⟩
  intro γ hγ hγmax N h l hh hl hlarge
  have hN : 1000000000000 ≤ N := by
    have hn : (1000000000000 : ℝ) ≤ N := by linarith only [hlarge]
    exact_mod_cast hn
  refine ⟨source_births_nonempty N hN zL zH hzL hzH,?_⟩
  intro nH nL hb
  let s : ActiveState (activeDomain N (h+l) zL zH) :=
    ⟨founderPopulation N h l nH nL,
      founder_mem_activeDomain N h l (by omega) hh hl zL zH hzL hzH nH nL hb⟩
  obtain ⟨q,hq,hkq,hbound⟩ :=
    (stoppedPopulationModel γ hγ.le (4*(N*(h+l))) N (h+l) zL zH
      (activeDomain N (h+l) zL zH)).exists_clock ((9/40000)*(N : ℝ)*γ)
  let t : ℝ≥0 := ⟨8/γ,by positivity⟩
  refine ⟨s,rfl,q,t,hq,hbound,rfl,?_⟩
  apply finite_batch_competition γ hγ hγmax N h l hh hl hlarge zL zH hzL hzH hsL hsH
    q t hq hbound hkq rfl s
  · simp [s,founderPopulation]
  · rfl
  · exact founder_volumes N h l nH nL
  · exact founder_birth_energy N h l zL zH nH nL hb
  · exact (founder_ancestral_membrane N h l nH nL).1
  · exact (founder_ancestral_membrane N h l nH nL).2

end ResourceLimitedCompetition
