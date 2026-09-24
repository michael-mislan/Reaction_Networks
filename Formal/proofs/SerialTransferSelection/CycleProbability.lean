import proofs.SerialTransferSelection.CycleLaw

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

variable (N M JB JR : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (zL zH : ℝ)
  (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
  (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
  (s : ReadyPopulation N M zL zH)
  (qr : NNReal) (hqr : 0 < (qr : ℝ))
  (hclockr : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ qr)
  (hsL : Stationary sourceRates (lift sourceRates zL))
  (hsH : Stationary sourceRates (lift sourceRates zH))
  (hlarge : (140000000000000000000 : ℝ) ≤ N) (hJR : 0 < JR)
  (hkr : (N : ℝ)*localAlpha*innerEnergy/672 ≤ qr)
  (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) (hε1 : ε < 1)
  (hfloor : ∀ b, p*(M : ℝ) ≤ ancestralCount b s.val.live)

include hsL hsH hlarge hJR hkr hp hε hε1 hfloor

theorem cycleContinuation_probability
    (x : CycleBatchState N M zL zH s × Fin (JB+1))
    (hx : x ∈ cycleBatchGoodSet N M JB zL zH s) :
    1-(32/(ε^2*p*(M : ℝ))+(M : ℝ)*(recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*(qr : ℝ)/JR)) ≤
      (cycleContinuation N M JB JR hN hM zL zH hzL hzH s qr hqr hclockr x).expect
        (FiniteKernel.eventIndicator (successfulOutput (cycleReadyRelation N M zL zH s.val p ε))) := by
  classical
  simp only [cycleContinuation,dif_pos hx]
  have hg := phase_good_transfer_inputs N M (by omega) hM zL zH s.val
    (readyPopulation_ready N M zL zH s) p hfloor x.1 hx.1
  have ht := transferRecoveryLaw_probability N M JR hN zL zH hzL hzH (physicalState N x.1)
    hg.2.1 hg.2.2.2.1 hg.2.2.2.2.2 qr hqr hclockr hsL hsH hlarge hJR hkr
    hM hg.1 hg.2.2.1 p ε hp hε hε1 hg.2.2.2.2.1
  exact ht.trans (finiteLaw_successful_mono _ _ _ (fun y hy =>
    source_cycle_outcome N M zL zH s.val p ε x.1 hx.1 y hy))

/-- One complete source-derived cycle inequality: actual batch, uniform intact
transfer, source recovery and physical refill, with both stage quotas retained. -/
theorem sourceCycleLaw_probability (h1000 : 1000 ≤ N) (hJB : 0 < JB)
    (γ : ℝ) (hγ : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (qb t : NNReal) (hqb : 0 < (qb : ℝ))
    (hclockb : ∀ x, (cycleBatchModel N M zL zH γ hγ.le s).total x ≤ qb)
    (hkb : (9/40000)*(N : ℝ)*γ ≤ qb) (htime : (t : ℝ)=8/γ) :
    1-((phaseChemicalRawError N M t+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))+
        (t : ℝ)*qb/JB)+(32/(ε^2*p*(M : ℝ))+
        (M : ℝ)*(recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*(qr : ℝ)/JR))) ≤
      (sourceCycleLaw N M JB JR hN hM zL zH hzL hzH s qr hqr hclockr γ hγ.le qb t hqb hclockb).expect
        (FiniteKernel.eventIndicator (successfulOutput (cycleReadyRelation N M zL zH s.val p ε))) := by
  classical
  unfold sourceCycleLaw
  apply finiteLaw_joint_bind_lower _ _ (cycleBatchGoodSet N M JB zL zH s) _ _ _
    (by unfold recoveryError localAlpha innerEnergy outerEnergy; positivity)
  · rw [poissonLaw_expect]
    have hready := readyPopulation_ready N M zL zH s
    have hw := membrane_upper N s.val.live (fun c hc => (hready.2.2.2.1 c hc).2.le)
    rw [hready.1] at hw
    have hb (b : Bool) : 0 < ancestralMembrane b s.val.live := by
      have hf := ready_ancestral_membrane_floor N M s.val hready.2.2.2.1 p b (hfloor b)
      have hn : (0 : ℝ) < (N : ℝ)*p*M := by positivity
      exact_mod_cast hn.trans_le hf
    exact phase_source_batch_with_service N M (membrane s.val.live) JB hJB h1000 hM hw hlarge
      zL zH γ hzL hzH hsL hsH hγ hγmax qb t hqb hclockb
      ⟨s.val,phase_ready_mem_domain N M hN hM zL zH hzL hzH s.val hready⟩
      hready rfl (hb true) (hb false) hkb htime
  · exact cycleContinuation_probability N M JB JR hN hM zL zH hzL hzH s qr hqr hclockr
      hsL hsH hlarge hJR hkr p ε hp hε hε1 hfloor

end SerialTransferSelection
