import proofs.DisguisedToricAssemblies.CACExamples

namespace DisguisedToricAssemblies
open CoreCouplingCAC

noncomputable def sliceRates (η : ℝ) : Rates := ⟨(19-2*η)/25,(η-4)/25,1,5,η,3⟩
noncomputable def sliceState : State := ⟨2/5,1/5,1/5,2/25⟩

theorem slice_positive (η : ℝ) (hlo : 4 < η) (hhi : η < 19/2) :
    (sliceRates η).Positive := by
  dsimp [sliceRates,Rates.Positive]
  constructor
  · linarith
  constructor
  · linarith
  norm_num
  linarith

theorem slice_stationary (η : ℝ) : sliceState.Positive ∧ Stationary (sliceRates η) sliceState := by
  constructor
  · norm_num [sliceState,State.Positive]
  · unfold Stationary
    refine ⟨?_,?_,?_,?_⟩ <;>
      norm_num [sliceRates,sliceState,fA,fB,fZ,fH] <;> ring

theorem slice_unique (η : ℝ) (hlo : 4 < η) (hhi : η < 19/2)
    (x : State) (hx : x.Positive) (hs : Stationary (sliceRates η) x) : x = sliceState :=
  loss_regime_unistationary _ (slice_positive η hlo hhi) (by norm_num [sliceRates])
    x sliceState hx (slice_stationary η).1 hs (slice_stationary η).2

theorem slice_toric_iff (η : ℝ) (hlo : 4 < η) (hhi : η < 19/2) :
    DisguisedToric (sliceRates η) ↔ η ≤ 5 := by
  have hp := slice_positive η hlo hhi
  constructor
  · rintro ⟨x,hx,hr⟩
    obtain ⟨hs,_,hJ⟩ := (cac_state_characterization _ _ hp hx).mp hr
    rw [slice_unique η hlo hhi x hx hs] at hJ
    norm_num [sliceRates,sliceState] at hJ
    linarith
  · intro hη
    refine ⟨sliceState,(slice_stationary η).1,?_⟩
    apply (cac_state_characterization _ _ hp (slice_stationary η).1).mpr
    refine ⟨(slice_stationary η).2,?_,?_⟩
    · norm_num [sliceState]
    · norm_num [sliceRates,sliceState]
      linarith

theorem slice_productivity (η : ℝ) :
    CoreProductive (sliceState.A-sliceState.B*sliceState.z)
      ((sliceRates η).e*(sliceState.B-sliceState.A^2)) ↔ 9/2 < η ∧ η < 9 := by
  norm_num [CoreProductive,sliceState,sliceRates]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

noncomputable def hurwitzCoefficients (η : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  ((67+13*η)/5,(1290+707*η)/25,(1885+1558*η)/25,(905+769*η)/25)

theorem slice_hurwitz (η : ℝ) (hη : 0 < η) :
    let c := hurwitzCoefficients η
    0 < c.1 ∧ 0 < c.2.1 ∧ 0 < c.2.2.1 ∧ 0 < c.2.2.2 ∧
    0 < c.1*c.2.1-c.2.2.1 ∧
    0 < c.1*c.2.1*c.2.2.1-c.2.2.1^2-c.1^2*c.2.2.2 := by
  dsimp [hurwitzCoefficients]
  have h2 : (67+13*η)/5*((1290+707*η)/25)-(1885+1558*η)/25 =
      (77005+56349*η+9191*η^2)/125 := by ring
  have h3 : (67+13*η)/5*((1290+707*η)/25)*((1885+1558*η)/25)-
      ((1885+1558*η)/25)^2-((67+13*η)/5)^2*((905+769*η)/25) =
      (124841700+201048900*η+97654062*η^2+13669773*η^3)/3125 := by ring
  rw [h2,h3]
  exact ⟨by positivity,by positivity,by positivity,by positivity,by positivity,by positivity⟩

end DisguisedToricAssemblies
