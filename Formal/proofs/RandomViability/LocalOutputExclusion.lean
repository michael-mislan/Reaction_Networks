import proofs.RandomViability.OutsiderIncidenceOutput
import proofs.RandomViability.NeutralIncidenceOutput
import proofs.RandomViability.MixedIncidenceOutput
import proofs.RandomViability.PhysicalOutputProbability

set_option Elab.async false
namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 80000

def LocalIncidence {n : ℕ} (K : ℕ) (c : SourceMoleculeFibreConfig n)
    (z : Molecule n) (r : Reaction n) : Prop :=
  molLength z ≤ K ∧ reactionProductLength r ≤ K+2 ∧ r ∈ c z

def AtMostOneLocalIncidence {n : ℕ} (K : ℕ) (c : SourceMoleculeFibreConfig n) : Prop :=
  ∀ z r z' r',LocalIncidence K c z r → LocalIncidence K c z' r' → z = z' ∧ r = r'

def localOutputNoiseUpper (n : ℕ) (V : NNReal) : ℝ :=
  4*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))+
  2*Real.exp (-((1/200 : ℝ)^2*(V : ℝ)/(4*(n : ℝ)*(96011*101+1/200))))+
  2*Real.exp (-((1/200000 : ℝ)^2*(V : ℝ)/(4*(n : ℝ)*(96011*101+1/200000))))

theorem nonfood_coordinate_zero_of_mass_zero {n : ℕ} (N : Molecule n → ℕ)
    (hM : countNonfoodMass N = 0) (q : Molecule n) (hq : 2 < molLength q) : N q = 0 := by
  have hh : ((molLength q : ℝ)-foodMassWeight q)*(N q : ℝ) ≤ countNonfoodMass N := by
    unfold countNonfoodMass
    apply Finset.single_le_sum _ (Finset.mem_univ q)
    intro z _
    unfold foodMassWeight
    split_ifs <;> simp only [sub_self,zero_mul,sub_zero] <;> positivity
  rw [hM,foodMassWeight,if_neg (not_le.mpr hq),sub_zero] at hh
  have hlen : (0 : ℝ) < molLength q := by exact_mod_cast (show 0 < molLength q by omega)
  have hzero : (N q : ℝ) = 0 := by nlinarith only [hh,hlen,show (0 : ℝ) ≤ N q by positivity]
  exact_mod_cast hzero

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- H3: complete uniform kinetic exclusion from the literal source hypotheses.
No pointwise drift, trajectory comparison, or independence assumption is left as an input. -/
theorem physical_output_upper_at_most_one_local (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (hone : AtMostOneLocalIncidence singleIncidenceCutoff c)
    (hno : ∀ z r,r ∈ c z → ¬ProductiveSingletonIncidence r z)
    (V : NNReal) (hV : 0 < (V : ℝ)) (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ))
    (hsmallscale : (n : ℝ)/V ≤ 1/200000)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hinit : countNonfoodMass N = 0) :
    (physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | physicalOutputEvent V z}).toReal ≤ localOutputNoiseUpper n V := by
  have hscale' : (n : ℝ)/V ≤ 1/200 := hsmallscale.trans (by norm_num)
  have he0 : 0 ≤ 4*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by positivity
  have hem : 0 ≤ 2*Real.exp (-((1/200 : ℝ)^2*(V : ℝ)/(4*(n : ℝ)*(96011*101+1/200)))) := by positivity
  have heo : 0 ≤ 2*Real.exp (-((1/200000 : ℝ)^2*(V : ℝ)/(4*(n : ℝ)*(96011*101+1/200000)))) := by positivity
  by_cases hshort : ShortIncidence collectiveUpperCutoff c
  · obtain ⟨z,hz,r,hr,hmem⟩ := hshort
    have hzlen : molLength z ≤ collectiveUpperCutoff := (Finset.mem_filter.mp hz).2
    have hloc : LocalIncidence singleIncidenceCutoff c z r :=
      ⟨hzlen.trans (by norm_num [collectiveUpperCutoff,singleIncidenceCutoff]),
        hr.trans (by norm_num [collectiveUpperCutoff,singleIncidenceCutoff]),hmem⟩
    have hiso : SingleLocalIncidence singleIncidenceCutoff c z r :=
      fun z' r' hz' hr' hm' => hone z' r' z r ⟨hz',hr',hm'⟩ hloc
    have hprod : molLength (reactionProduct r) ≤ singleIncidenceHalfCutoff := by
      rw [molLength_reactionProduct]
      exact hr.trans (by norm_num [collectiveUpperCutoff,singleIncidenceHalfCutoff])
    have hzsmall : molLength z ≤ singleIncidenceCutoff+2 := by
      exact hzlen.trans (by norm_num [collectiveUpperCutoff,singleIncidenceCutoff])
    rcases local_incidence_classification r z with hneutral | hmixed | hout | hsingleton
    · have hh := physical_isolated_neutral_output_upper hn c z r hiso hneutral V hV hscale' basal cat hb hcat N hinit
      have hh' := ENNReal.toReal_mono (by finiteness) hh
      simp only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (Real.exp_pos _).le] at hh'
      exact hh'.trans (by unfold localOutputNoiseUpper; linarith only [he0,hem,heo])
    · have hh := physical_isolated_mixed_output_upper hn c z r hiso hmixed hprod V hV hscale' basal cat hb hcat N hinit
      have hh' := ENNReal.toReal_mono (by finiteness) hh
      simp only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (Real.exp_pos _).le] at hh'
      exact hh'.trans (by unfold localOutputNoiseUpper; linarith only [he0,hem,heo])
    · have hh := physical_isolated_outsider_output_upper hn c z r hiso hout hzsmall V hV hsmallscale basal cat hb hcat N hinit
        (nonfood_coordinate_zero_of_mass_zero N hinit z hout.2.2.2.1)
      have hh' := ENNReal.toReal_mono (by finiteness) hh
      simp only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (Real.exp_pos _).le] at hh'
      exact hh'.trans (by unfold localOutputNoiseUpper; linarith only [he0,hem,heo])
    · exact False.elim (hno z r hmem hsingleton)
  · exact (physical_output_upper_without_short_incidence hn c hshort V hV hscale basal cat hb hcat N hinit).trans
      (by unfold localOutputNoiseUpper; linarith only [he0,hem,heo])

end
end RandomViability
