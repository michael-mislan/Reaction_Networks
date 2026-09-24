import proofs.ResourceLimitedCompetition.GainNutrient
import proofs.ResourceLimitedCompetition.ChemicalLabels
import proofs.ResourceLimitedCompetition.AncestralPersistence
import proofs.ResourceLimitedCompetition.UnflaggedProbability
import proofs.ResourceLimitedCompetition.GlobalSpatial
import proofs.ResourceLimitedCompetition.OuterFailure
import proofs.ResourceLimitedCompetition.GlobalPartition
import proofs.ResourceLimitedCompetition.DeadlineProbability
import proofs.ResourceLimitedCompetition.ProbabilityUnion

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy Set

def enrichmentSet (gain : ℝ) (N h l : ℕ) (zL zH : ℝ) :
    Set (StoppedPopulation (activeDomain N (h+l) zL zH)) :=
  {x | ∃ e, x=.inr e ∧ eventReason N (h+l) zL zH e=.nutrient ∧
    (eventOutcome N e).resource=N*(h+l) ∧
    (∀ c ∈ (eventOutcome N e).live, chemicalLabelMatches c) ∧
    0 < ancestralCount true (eventOutcome N e).live ∧
    0 < ancestralCount false (eventOutcome N e).live ∧
    Real.exp gain*(h : ℝ)/(l : ℝ) ≤
      (ancestralCount true (eventOutcome N e).live : ℝ)/(ancestralCount false (eventOutcome N e).live : ℝ)}

def enrichmentFailureSet (gain : ℝ) (N h l : ℕ) (zL zH : ℝ) :
    Fin 8 → Set (StoppedPopulation (activeDomain N (h+l) zL zH)) :=
  ![outerFailureSet N (h+l) zL zH _, divisionFailureSet N (h+l) zL zH _,
    partitionFailureSet N (h+l) zL zH _, activePopulationSet _,
    gainExceptionalSet gain N (N*h) (N*l) _, ancestryBelowSet N N true _,
    ancestryBelowSet N N false _, unflaggedTerminalSet N (h+l) zL zH _]

theorem enrichment_failure_coverage (gain : ℝ) (N h l : ℕ) (hN : 0 < N) (hh : 0 < h) (hl : 0 < l)
    (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (x : StoppedPopulation (activeDomain N (h+l) zL zH))
    (hx : x ∉ enrichmentSet gain N h l zL zH) : ∃ i, x ∈ enrichmentFailureSet gain N h l zL zH i := by
  classical
  cases x with
  | inl s => exact ⟨3,⟨s,rfl⟩⟩
  | inr e =>
    cases hr : eventReason N (h+l) zL zH e with
    | active => exact ⟨7,⟨e,rfl,hr⟩⟩
    | outer => exact ⟨0,⟨e,rfl,hr⟩⟩
    | divisionEnergy => exact ⟨1,⟨e,rfl,hr⟩⟩
    | partition => exact ⟨2,⟨e,rfl,hr⟩⟩
    | nutrient =>
      by_cases hH : N ≤ ancestralMembrane true (eventOutcome N e).live
      · by_cases hL : N ≤ ancestralMembrane false (eventOutcome N e).live
        · have hHp := hN.trans_le hH
          have hLp := hN.trans_le hL
          by_cases hb : (ancestralCount true (eventOutcome N e).live : ℝ)*l ≤
              Real.exp gain*(h : ℝ)*ancestralCount false (eventOutcome N e).live
          · exact ⟨4,nutrient_bad_gain_exceptional gain N h l hN hh hl zL zH e hr hHp hLp hb⟩
          · have hs := activeDomain_safe N (h+l) zL zH e.1.val e.1.property
            have hv := event_valid_volumes N hN _ e.1 e.2 hs.2.2.2.2.1
            have hcpos (tag : Bool) (hB : 0 < ancestralMembrane tag (eventOutcome N e).live) :
                0 < ancestralCount tag (eventOutcome N e).live := by
              have hbnd := (ancestral_count_bounds N tag (eventOutcome N e).live
                (fun c hc => ⟨(hv c hc).1,(hv c hc).2.le⟩)).2
              by_contra hc
              have hz : ancestralCount tag (eventOutcome N e).live=0 := by omega
              rw [hz,mul_zero] at hbnd
              omega
            have hCH := hcpos true hHp
            have hCL := hcpos false hLp
            have hfreq : Real.exp gain*(h : ℝ)/(l : ℝ) ≤
                (ancestralCount true (eventOutcome N e).live : ℝ)/(ancestralCount false (eventOutcome N e).live : ℝ) := by
              apply (div_le_div_iff₀ (by exact_mod_cast hl) (by exact_mod_cast hCL)).mpr
              exact (lt_of_not_ge hb).le
            exact False.elim (hx ⟨e,rfl,hr,(nutrient_event_resource N (h+l) zL zH _ e.1 e.2 hr).2.1,
              nutrient_chemical_labels N (h+l) hN zL zH hzL hzH e hr,hCH,hCL,hfreq⟩)
        · exact ⟨6,lt_of_not_ge hL⟩
      · exact ⟨5,lt_of_not_ge hH⟩

end ResourceLimitedCompetition
