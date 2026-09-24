import proofs.ProductiveMemory.ExtractionCycleLaw

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

variable (N M J JS : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (hlarge : recoveryCount ≤ N) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : ProductiveReady N M rho zL zH)
    (hsL : extractDrift rho 0 (lift rho zL)=0) (hsH : extractDrift rho 0 (lift rho zH)=0)
    (p eps : ℝ) (hp : 0 < p) (heps : 0 < eps) (heps1 : eps < 1)
    (hfloor : ∀ b, p*(M:ℝ) ≤ ancestralCount b s.val.population.live)

include hsL hsH hp heps heps1 hfloor

theorem productive_continuation_probability
    (x : ProductiveCycleBatchState N M J rho zL zH s × Fin (JS+1))
    (hx : x ∈ productiveCycleBatchGood N M J JS rho zL zH s) :
    1-(32/(eps^2*p*(M:ℝ))+2*(M:ℝ)/10^18) ≤
      (productiveCycleContinuation N M J JS hN hM hlarge rho zL zH hr hzL hzH s x).expect
        (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput
          (productiveCycleRelation N M J rho zL zH s.val p eps))) := by
  classical
  simp only [productiveCycleContinuation,dif_pos hx]
  rw [productive_record_probability]
  have hg := productive_good_transfer_inputs N M J (by omega) hM rho zL zH s.val
    (productiveReady_ready N M rho zL zH s) p hfloor x.1 hx.1
  have ht := extraction_transfer_recovery_probability N M hN hlarge rho zL zH hr hzL hzH
    (productivePhysical N x.1).population hg.2.1 hg.2.2.2.1 hg.2.2.2.2.2 hsL hsH
    hM hg.1 hg.2.2.1 p eps hp heps heps1 hg.2.2.2.2.1
  exact ht.trans (SerialTransferSelection.finiteLaw_successful_mono _ _ _ (fun y hy =>
    productive_cycle_outcome N M J rho zL zH s.val p eps x.1 hx.1 y hy _ rfl))

theorem productive_source_cycle_probability (hJ : 0 < J) (hJS : 0 < JS)
    (gamma : ℝ) (hg : 0 < gamma) (hgmax : gamma ≤ 1/100000000000)
    (qb t : NNReal) (hqb : 0 < (qb:ℝ))
    (hclockb : ∀ x, (productiveCycleBatchModel N M J rho zL zH gamma (by linarith [hr.1]) hg.le s).total x ≤ qb)
    (hkb : (9/40000)*(N:ℝ)*gamma ≤ qb) (htime : (t:ℝ)=8/gamma) :
    1-((productiveChemicalRawError N M t+Real.exp (-(N:ℝ)/2500)+Real.exp (-(19*(N:ℝ)/500000))+
      (t:ℝ)*(560*(N:ℝ)*(M:ℝ)*rho)/J+Real.exp (-(membrane s.val.population.live:ℝ))+(t:ℝ)*qb/JS)+
      (32/(eps^2*p*(M:ℝ))+2*(M:ℝ)/10^18)) ≤
      (productiveSourceCycleLaw N M J JS hN hM hlarge rho zL zH hr hzL hzH s hJ gamma hg.le qb t hqb hclockb).expect
        (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput
          (productiveCycleRelation N M J rho zL zH s.val p eps))) := by
  classical
  unfold productiveSourceCycleLaw
  apply SerialTransferSelection.finiteLaw_joint_bind_lower _ _
    (productiveCycleBatchGood N M J JS rho zL zH s) _ _ _ (by positivity)
  · rw [poissonLaw_expect]
    have hready := productiveReady_ready N M rho zL zH s
    have hw := membrane_upper N s.val.population.live (fun c hc => (hready.2.2.2.1 c hc).2.le)
    rw [hready.1] at hw
    have hb (b : Bool) : 0 < ancestralMembrane b s.val.population.live := by
      have hf := SerialTransferSelection.ready_ancestral_membrane_floor N M s.val.population hready.2.2.2.1 p b (hfloor b)
      have hn : (0:ℝ) < (N:ℝ)*p*M := by positivity
      exact_mod_cast hn.trans_le hf
    have h1000 : 1000 ≤ N := (by norm_num [recoveryCount] : 1000 ≤ recoveryCount).trans hlarge
    have hNreal : (200000000000000000000:ℝ) ≤ N := by
      have hnat : 200000000000000000000 ≤ N :=
        (by norm_num [recoveryCount] : 200000000000000000000 ≤ recoveryCount).trans hlarge
      exact_mod_cast hnat
    exact productive_batch_with_service N M (membrane s.val.population.live) J JS hJ hJS h1000 hM hw hNreal
      rho zL zH gamma hr hzL hzH hsL hsH hg hgmax qb t hqb hclockb
      ⟨s.val,productive_ready_mem_domain N M J hN hM hJ rho zL zH hr hzL hzH s.val hready⟩
      hready rfl (hb true) (hb false) hkb htime
  · exact productive_continuation_probability N M J JS hN hM hlarge rho zL zH hr hzL hzH s hsL hsH p eps hp heps heps1 hfloor

end
end ProductiveMemory
