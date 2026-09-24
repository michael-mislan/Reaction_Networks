import proofs.ResourceLimitedCompetition.EnrichmentCoverage
import proofs.ResourceLimitedCompetition.DeadlineFamily
import proofs.ResourceLimitedCompetition.ChemicalProbability

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal

noncomputable local instance TradeoffDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) :=
  Classical.decEq _

theorem finite_batch_tradeoff (gain : ℝ) (γ : ℝ) (hγ : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (N h l : ℕ) (hh : 0 < h) (hl : 0 < l)
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, (stoppedPopulationModel γ hγ.le (4*(N*(h+l))) N (h+l) zL zH (activeDomain N (h+l) zL zH)).total x ≤ q)
    (hkq : (9/40000)*(N : ℝ)*γ ≤ q)
    (s : ActiveState (activeDomain N (h+l) zL zH))
    (hlen : s.val.live.length=h+l) (hD : s.val.divisions=0)
    (hm : ∀ c ∈ s.val.live, c.compartment.2=N)
    (he : ∀ c ∈ s.val.live, cellEnergy zL zH c ≤ 4*innerEnergy)
    (hH0 : ancestralMembrane true s.val.live=N*h)
    (hL0 : ancestralMembrane false s.val.live=N*l) :
    1-(chemicalRawError N ((h+l : ℕ) : ℝ) t+Real.exp (-((N : ℝ)/1000)*((3/5)*Real.log 4-Real.log 2-gain))+Real.exp (-((N : ℝ)/1000)*((9/40)*γ*(t : ℝ)-Real.log 4))) ≤
      ((stoppedPopulationModel γ hγ.le (4*(N*(h+l))) N (h+l) zL zH (activeDomain N (h+l) zL zH)).uniformize q hq hbound).poissonized
        (q*t) (FiniteKernel.eventIndicator (enrichmentSet gain N h l zL zH)) (.inl s) := by
  classical
  have hN : 1000 ≤ N := by
    have hn : (1000 : ℝ) ≤ N := by linarith only [hlarge]
    exact_mod_cast hn
  have hNpos : 0 < N := by omega
  have hN1 : 1 ≤ N := by omega
  have hHpos : 0 < ancestralMembrane true s.val.live := by rw [hH0]; exact Nat.mul_pos hNpos hh
  have hLpos : 0 < ancestralMembrane false s.val.live := by rw [hL0]; exact Nat.mul_pos hNpos hl
  have hHmin : N ≤ ancestralMembrane true s.val.live := by rw [hH0]; exact Nat.le_mul_of_pos_right N hh
  have hLmin : N ≤ ancestralMembrane false s.val.live := by rw [hL0]; exact Nat.le_mul_of_pos_right N hl
  have hmem : membrane s.val.live=N*(h+l) := by
    rw [← ancestral_membrane_total,hH0,hL0]
    ring
  let P := (stoppedPopulationModel γ hγ.le (4*(N*(h+l))) N (h+l) zL zH (activeDomain N (h+l) zL zH)).uniformize q hq hbound
  have hchem := global_chemical_probability N (h+l) hN1 hlarge zL zH γ hzL hzH hsL hsH hγ.le hγmax
    q t hq hbound s hlen hD hm he
  have hodds := global_gain_probability gain γ hγ.le (4*(N*(h+l))) N (h+l) hN zL zH hzL hzH
    q t hq hbound s hHpos hLpos
  rw [hH0,hL0] at hodds
  have hdeadline := deadline_probability_family γ hγ N (h+l) hN zL zH hzL hzH q t hq hbound hkq s hmem
  have hhigh := ancestry_below_probability γ hγ.le (4*(N*(h+l))) N (h+l) N zL zH _ true
    q t hq hbound (.inl s) hHmin
  have hlow := ancestry_below_probability γ hγ.le (4*(N*(h+l))) N (h+l) N zL zH _ false
    q t hq hbound (.inl s) hLmin
  have hunflagged := unflagged_probability γ hγ.le N (h+l) hN1 zL zH hzL hzH q t hq hbound s
  have hcover := poissonized_event_cover P (q*t) (enrichmentSet gain N h l zL zH)ᶜ
    (enrichmentFailureSet gain N h l zL zH)
    (enrichment_failure_coverage gain N h l hNpos hh hl zL zH hzL hzH) (.inl s)
  apply probability_complement_lower P (q*t) (enrichmentSet gain N h l zL zH) ((chemicalRawError N ((h+l : ℕ) : ℝ) t+Real.exp (-((N : ℝ)/1000)*((3/5)*Real.log 4-Real.log 2-gain))+Real.exp (-((N : ℝ)/1000)*((9/40)*γ*(t : ℝ)-Real.log 4)))) (.inl s)
  apply hcover.trans
  simp [enrichmentFailureSet,Fin.sum_univ_succ]
  dsimp only [P]
  dsimp only at hchem
  simp only [Nat.cast_add] at hchem
  simp only [neg_mul] at hodds hdeadline
  linarith only [hchem,hodds,hdeadline,hhigh,hlow,hunflagged]

end ResourceLimitedCompetition
