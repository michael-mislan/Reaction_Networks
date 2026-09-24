import proofs.SerialTransferSelection.CycleProbability

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

noncomputable def sourceCycleError (N M JB JR : ℕ) (qb qr t p ε : ℝ) : ℝ :=
  (phaseChemicalRawError N M t+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))+t*qb/JB)+
    (32/(ε^2*p*(M : ℝ))+(M : ℝ)*(recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*qr/JR))

def twoCycleRelation (N M : ℕ) (zL zH : ℝ) (s : PopulationState) (ε : ℝ)
    (y : ReadyPopulation N M zL zH) : Prop :=
  (∀ b, 0 < ancestralCount b y.val.live) ∧
    2*cycleSizeGain ε < sizeLogOdds y.val-sizeLogOdds s

variable (N M JB JR : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (zL zH : ℝ)
  (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
  (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
  (qr : NNReal) (hqr : 0 < (qr : ℝ))
  (hclockr : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ qr)
  (γ : ℝ) (hγ : 0 ≤ γ) (qb t : NNReal) (hqb : 0 < (qb : ℝ))
  (hclockb : ∀ (s : ReadyPopulation N M zL zH) x, (cycleBatchModel N M zL zH γ hγ s).total x ≤ qb)

noncomputable def sourceCycleKernel (s : ReadyPopulation N M zL zH) :
    FiniteLaw (Option (ReadyPopulation N M zL zH)) :=
  sourceCycleLaw N M JB JR hN hM zL zH hzL hzH s qr hqr hclockr γ hγ qb t hqb (hclockb s)

noncomputable def sourceCycleOptionKernel (s : Option (ReadyPopulation N M zL zH)) :
    FiniteLaw (Option (ReadyPopulation N M zL zH)) :=
  match s with
  | none => FiniteLaw.pure none
  | some y => sourceCycleKernel N M JB JR hN hM zL zH hzL hzH qr hqr hclockr γ hγ qb t hqb hclockb y

noncomputable def sourceTwoCycleLaw (s : ReadyPopulation N M zL zH) :
    FiniteLaw (Option (ReadyPopulation N M zL zH)) :=
  (sourceCycleKernel N M JB JR hN hM zL zH hzL hzH qr hqr hclockr γ hγ qb t hqb hclockb s).bind
    (sourceCycleOptionKernel N M JB JR hN hM zL zH hzL hzH qr hqr hclockr γ hγ qb t hqb hclockb)

theorem sourceTwoCycleLaw_probability
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (h1000 : 1000 ≤ N)
    (hJB : 0 < JB) (hJR : 0 < JR) (hγpos : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (hkr : (N : ℝ)*localAlpha*innerEnergy/672 ≤ qr)
    (hkb : (9/40000)*(N : ℝ)*γ ≤ qb) (htime : (t : ℝ)=8/γ)
    (p₀ p₁ ε : ℝ) (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hε : 0 < ε) (hε1 : ε < 1)
    (hnext : p₁ ≤ (1-ε)*p₀/16) (s : ReadyPopulation N M zL zH)
    (hfloor : ∀ b, p₀*(M : ℝ) ≤ ancestralCount b s.val.live) :
    1-(sourceCycleError N M JB JR qb qr t p₀ ε+sourceCycleError N M JB JR qb qr t p₁ ε) ≤
      (sourceTwoCycleLaw N M JB JR hN hM zL zH hzL hzH qr hqr hclockr γ hγ qb t hqb hclockb s).expect
        (FiniteKernel.eventIndicator (successfulOutput (twoCycleRelation N M zL zH s.val ε))) := by
  classical
  unfold sourceTwoCycleLaw
  apply finiteLaw_joint_bind_lower _ _ (successfulOutput (cycleReadyRelation N M zL zH s.val p₀ ε)) _ _ _
    (by unfold sourceCycleError phaseChemicalRawError recoveryError partitionError localAlpha innerEnergy outerEnergy; positivity)
  · exact sourceCycleLaw_probability N M JB JR hN hM zL zH hzL hzH s qr hqr hclockr
      hsL hsH hlarge hJR hkr p₀ ε hp₀ hε hε1 hfloor h1000 hJB γ hγpos hγmax qb t hqb (hclockb s) hkb htime
  · intro o ho
    cases o with
    | none => exact False.elim ho
    | some y =>
      change cycleReadyRelation N M zL zH s.val p₀ ε y at ho
      have hyfloor (b : Bool) : p₁*(M : ℝ) ≤ ancestralCount b y.val.live := by
        have hh := hnext.trans (ho.1 b).2
        exact (le_div_iff₀ (by positivity : (0 : ℝ) < M)).mp hh
      have hcy := sourceCycleLaw_probability N M JB JR hN hM zL zH hzL hzH y qr hqr hclockr
        hsL hsH hlarge hJR hkr p₁ ε hp₁ hε hε1 hyfloor h1000 hJB γ hγpos hγmax qb t hqb (hclockb y) hkb htime
      apply hcy.trans
      apply finiteLaw_successful_mono
      intro z hz
      refine ⟨fun b => (hz.1 b).1,?_⟩
      linarith only [ho.2,hz.2]

end SerialTransferSelection
