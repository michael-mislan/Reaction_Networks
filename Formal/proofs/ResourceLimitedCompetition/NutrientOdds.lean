import proofs.ResourceLimitedCompetition.NutrientEndpoint
import proofs.ResourceLimitedCompetition.EndpointOdds

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

theorem nutrient_bad_odds_exceptional (N h l : ℕ) (hN : 0 < N) (hh : 0 < h) (hl : 0 < l)
    (zL zH : ℝ) (e : PopulationEvent (activeDomain N (h+l) zL zH))
    (hn : eventReason N (h+l) zL zH e=.nutrient)
    (hH : 0 < ancestralMembrane true (eventOutcome N e).live)
    (hL : 0 < ancestralMembrane false (eventOutcome N e).live)
    (hbad : (ancestralCount true (eventOutcome N e).live : ℝ)*l ≤
      Real.exp (1/10)*(h : ℝ)*ancestralCount false (eventOutcome N e).live) :
    Sum.inr e ∈ oddsExceptionalSet N (N*h) (N*l) (activeDomain N (h+l) zL zH) := by
  have hs := activeDomain_safe N (h+l) zL zH e.1.val e.1.property
  have hv := event_valid_volumes N hN _ e.1 e.2 hs.2.2.2.2.1
  have hhigh := ancestral_count_bounds N true (eventOutcome N e).live
    (fun c hc => ⟨(hv c hc).1,(hv c hc).2.le⟩)
  have hlow := ancestral_count_bounds N false (eventOutcome N e).live
    (fun c hc => ⟨(hv c hc).1,(hv c hc).2.le⟩)
  have hp := count_to_membrane_odds N h l _ _ _ _ hhigh.2 hlow.1 hbad
  have hNH : 0 < N*h := Nat.mul_pos hN hh
  have hNL : 0 < N*l := Nat.mul_pos hN hl
  have hlog := membrane_odds_log_bound ((N*h : ℕ) : ℝ) ((N*l : ℕ) : ℝ)
    (ancestralMembrane true (eventOutcome N e).live) (ancestralMembrane false (eventOutcome N e).live)
    (by exact_mod_cast hNH) (by exact_mod_cast hNL) (by exact_mod_cast hH) (by exact_mod_cast hL) hp
  have hw : ancestralMembrane true (eventOutcome N e).live+ancestralMembrane false (eventOutcome N e).live=
      4*(N*h+N*l) := by
    rw [ancestral_membrane_total,nutrient_endpoint_membrane N (h+l) zL zH e.1 e.2 hn]
    ring
  exact endpoint_odds_barrier N (N*h) (N*l) _ _ hNH hNL hH hL hw hlog

end ResourceLimitedCompetition
