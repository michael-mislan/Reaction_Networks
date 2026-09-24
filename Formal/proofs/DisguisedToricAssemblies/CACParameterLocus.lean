import proofs.DisguisedToricAssemblies.ExtendedFlux
import proofs.DisguisedToricAssemblies.CACThreshold

namespace DisguisedToricAssemblies
open CoreCouplingCAC

/-- The guide's piecewise rational criterion, including both equality boundaries. -/
def ParameterCriterion (p : Rates) : Prop :=
  residual p (admissibleCut p) ≤ 0 ∧
    (p.e ≤ 1 ∨ threshold p ≤ admissibleCut p ∨ reducedA p (threshold p) ≤ p.a+p.b)

theorem stationary_reservoir_identity (p : Rates) (x : State) (hs : Stationary p x) :
    p.a+p.b = x.A+x.B-p.e*(x.B-x.A^2) := by
  have ha := hs.1
  have hb := hs.2.1
  dsimp [fA] at ha
  dsimp [fB] at hb
  linear_combination ha+hb

theorem cacParameterLocus (p : Rates) (hp : p.Positive) :
    DisguisedToric p ↔ ParameterCriterion p := by
  constructor
  · rintro ⟨x,hx,hr⟩
    obtain ⟨hs,hK,hJ⟩ := (cac_state_characterization p x hp hx).mp hr
    have hzden : x.z+2 ≠ 0 := by have := hx.2.2.1; positivity
    have hdd : 2+p.d ≠ 0 := by have := hp.2.2.2.2.2; positivity
    have hrec := stationary_reconstruction p x hzden hdd hs
    have hA : x.A = reducedA p x.z := congrArg State.A hrec
    have hB : x.B = reducedB p x.z := congrArg State.B hrec
    have hk : x.A-x.B*x.z = reducedK p x.z := by
      rw [hA,hB,reducedA]
      ring
    rw [hk] at hK
    have hcut := (K_nonneg_iff_cut p hp x.z hx.2.2.1).mp hK
    have hE : residual p x.z = 0 := by
      have hb := hs.2.1
      rw [hrec] at hb
      exact (lift_residual p x.z hzden hdd).2.1.symm.trans hb
    have hport := stationary_reservoir_identity p x hs
    have hAs : reducedA p x.z ≤ p.a+p.b := by rw [← hA]; linarith
    have ht := (root_threshold_comparison p hp x.z hcut hE).mp hAs
    refine ⟨admissible_root_cut_sign p hp x.z hcut hE, ?_⟩
    by_cases he : p.e ≤ 1
    · exact Or.inl he
    · apply Or.inr
      by_cases htc : threshold p ≤ admissibleCut p
      · exact Or.inl htc
      · apply Or.inr
        have hct := (lt_of_not_ge htc).le
        have het := (root_sign_comparison p hp x.z (threshold p) hcut hct hE).mpr ht
        exact (threshold_residual_sign p hp hct).mp het
  · rintro ⟨he,hcriterion⟩
    obtain ⟨z,hzp,hcut,hE⟩ := admissible_root_exists p hp he
    have ht : threshold p ≤ z := by
      by_cases htc : threshold p ≤ admissibleCut p
      · exact htc.trans hcut
      · have hct := (lt_of_not_ge htc).le
        rcases hcriterion with hsmall | hsmall | hAt
        · exact False.elim (htc (small_e_threshold p hp hsmall))
        · exact False.elim (htc hsmall)
        · have het := (threshold_residual_sign p hp hct).mpr hAt
          exact (root_sign_comparison p hp z (threshold p) hcut hct hE).mp het
    have hAs := (root_threshold_comparison p hp z hcut hE).mpr ht
    have hK := admissible_K_nonneg p hp z hcut
    have hB : 0 < reducedB p z := by
      have := hp.1
      have := hp.2.1
      unfold reducedB
      positivity
    have hx : (lift p z).Positive := by
      refine ⟨add_pos_of_pos_of_nonneg (mul_pos hzp hB) hK,hB,hzp,?_⟩
      have := hp.2.2.1
      have := hp.2.2.2.1
      have := hp.2.2.2.2.2
      dsimp [lift,reducedH]
      positivity
    have hdd : 2+p.d ≠ 0 := by have := hp.2.2.2.2.2; positivity
    have hs := lift_stationary p z (by positivity) hdd hE
    have hcurr : 0 ≤ (lift p z).A-(lift p z).B*(lift p z).z := by
      have hi : (lift p z).A-(lift p z).B*(lift p z).z = reducedK p z := by
        dsimp [lift,reducedA]
        ring
      rwa [hi]
    have hport := stationary_reservoir_identity p (lift p z) hs
    have hJ : p.e*((lift p z).B-(lift p z).A^2) ≤ (lift p z).B := by
      change reducedA p z ≤ p.a+p.b at hAs
      dsimp [lift] at hport ⊢
      linarith
    exact ⟨lift p z,hx,(cac_state_characterization p _ hp hx).mpr ⟨hs,hcurr,hJ⟩⟩

end DisguisedToricAssemblies
