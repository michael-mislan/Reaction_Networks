import proofs.SerialTransferSelection.ShareCycleGeometry

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

def shareCycleReadyRelation (N M : ℕ) (zL zH : ℝ) (s : PopulationState) (q ε : ℝ)
    (y : ReadyPopulation N M zL zH) : Prop :=
  (∀ b, (1-ε)/(4*(1+ε))*q ≤ ancestralShare b y.val) ∧
    cycleReadyRelation N M zL zH s (q/2) ε y

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
  (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε) (hε1 : ε < 1)
  (hshare : ∀ b, q ≤ ancestralShare b s.val)

include hN hM hshare

theorem share_count_floor (b : Bool) : q/2*(M : ℝ) ≤ ancestralCount b s.val.live := by
  have hh := (div_le_div_of_nonneg_right (hshare b) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (ready_share_count N M (by omega) hM zL zH s b)
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < M)).mp hh

include hsL hsH hlarge hJR hkr hq hε hε1

theorem cycleContinuation_share_probability
    (x : CycleBatchState N M zL zH s × Fin (JB+1))
    (hx : x ∈ cycleBatchGoodSet N M JB zL zH s) :
    1-(16/(ε^2*(M : ℝ)*q)+(M : ℝ)*(recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*(qr : ℝ)/JR)) ≤
      (cycleContinuation N M JB JR hN hM zL zH hzL hzH s qr hqr hclockr x).expect
        (FiniteKernel.eventIndicator (successfulOutput (shareCycleReadyRelation N M zL zH s.val q ε))) := by
  classical
  have hf := share_count_floor N M hN hM zL zH s q hshare
  have hg := phase_good_transfer_inputs N M (by omega) hM zL zH s.val
    (readyPopulation_ready N M zL zH s) (q/2) hf x.1 hx.1
  have hcons : membrane (physicalState N x.1).live=4*membrane s.val.live := by
    obtain ⟨e,he,_,_,_,hw,_,_,_⟩ := hx.1
    simpa [he,physicalState] using hw
  have hgrow (b : Bool) : ancestralMembrane b s.val.live ≤ ancestralMembrane b (physicalState N x.1).live := by
    obtain ⟨e,he,_,_,_,_,hh,hl,_⟩ := hx.1
    cases b with
    | false => simpa [he,physicalState] using hl
    | true => simpa [he,physicalState] using hh
  simp only [cycleContinuation,dif_pos hx]
  unfold transferRecoveryLaw
  apply finiteLaw_joint_bind_lower _ _ (ancestralTransferGoodSet N M (physicalState N x.1) hg.2.1 ε) _ _ _
    (by unfold recoveryError localAlpha innerEnergy outerEnergy; positivity)
  · exact source_transfer_share_probability N M (by omega) hM _ hg.1 hg.2.1 hg.2.2.2.1
      q ε hq hε (fun b => batch_share_floor s.val _ b q (hshare b) (hgrow b) hcons)
  · intro S hS
    have hr := selectedRecoveryLaw_probability N M JR hN zL zH hzL hzH _ hg.2.2.2.1
      hg.2.2.2.2.2 qr hqr hclockr hsL hsH hlarge hJR hkr S
    apply hr.trans (finiteLaw_successful_mono _ _ _ ?_)
    intro y hy
    constructor
    · intro b
      have hm : 0 ≤ 1-ε := by linarith
      have hs := selected_return_share_recurrence N M (by omega) hM zL zH s _
        (by omega) hg.2.1 hcons hgrow ε hε.le hε1 S hS y hy b
      exact (mul_le_mul_of_nonneg_left (hshare b) (by positivity)).trans hs
    · apply source_cycle_outcome N M zL zH s.val (q/2) ε x.1 hx.1 y
      exact transfer_preserved_ready_relation N M (by omega) hM zL zH _ hg.1 hg.2.1 hg.2.2.1
        hg.2.2.2.1 (q/2) ε (by positivity) hε hε1 hg.2.2.2.2.1 S hS y hy

theorem sourceCycleLaw_share_probability (h1000 : 1000 ≤ N) (hJB : 0 < JB)
    (γ : ℝ) (hγ : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (qb t : NNReal) (hqb : 0 < (qb : ℝ))
    (hclockb : ∀ x, (cycleBatchModel N M zL zH γ hγ.le s).total x ≤ qb)
    (hkb : (9/40000)*(N : ℝ)*γ ≤ qb) (htime : (t : ℝ)=8/γ) :
    1-((phaseChemicalRawError N M t+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))+
        (t : ℝ)*qb/JB)+(16/(ε^2*(M : ℝ)*q)+
        (M : ℝ)*(recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*(qr : ℝ)/JR))) ≤
      (sourceCycleLaw N M JB JR hN hM zL zH hzL hzH s qr hqr hclockr γ hγ.le qb t hqb hclockb).expect
        (FiniteKernel.eventIndicator (successfulOutput (shareCycleReadyRelation N M zL zH s.val q ε))) := by
  classical
  have hf := share_count_floor N M hN hM zL zH s q hshare
  unfold sourceCycleLaw
  apply finiteLaw_joint_bind_lower _ _ (cycleBatchGoodSet N M JB zL zH s) _ _ _
    (by unfold recoveryError localAlpha innerEnergy outerEnergy; positivity)
  · rw [poissonLaw_expect]
    have hready := readyPopulation_ready N M zL zH s
    have hw := membrane_upper N s.val.live (fun c hc => (hready.2.2.2.1 c hc).2.le)
    rw [hready.1] at hw
    have hb (b : Bool) : 0 < ancestralMembrane b s.val.live := by
      have hbound := ready_ancestral_membrane_floor N M s.val hready.2.2.2.1 (q/2) b (hf b)
      have hn : (0 : ℝ) < (N : ℝ)*(q/2)*M := by positivity
      exact_mod_cast hn.trans_le hbound
    exact phase_source_batch_with_service N M (membrane s.val.live) JB hJB h1000 hM hw hlarge
      zL zH γ hzL hzH hsL hsH hγ hγmax qb t hqb hclockb
      ⟨s.val,phase_ready_mem_domain N M hN hM zL zH hzL hzH s.val hready⟩
      hready rfl (hb true) (hb false) hkb htime
  · exact cycleContinuation_share_probability N M JB JR hN hM zL zH hzL hzH s qr hqr hclockr
      hsL hsH hlarge hJR hkr q ε hq hε hε1 hshare

end SerialTransferSelection
