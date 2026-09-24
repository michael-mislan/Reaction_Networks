import proofs.ProductiveMemory.ExtractionCycleProbability
import proofs.ProductiveMemory.ExtractionParameters

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

variable (N M : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (hlarge : recoveryCount ≤ N) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (gamma : ℝ) (hg : 0 < gamma) (t : NNReal)

abbrev productiveCollectionQuota := (extractionCollectionCapacity N M rho t).quota

def productiveCycleKernel (s : ProductiveReady N M rho zL zH) :
    FiniteLaw (Option (ProductiveCycleResult N M (productiveCollectionQuota N M rho t) rho zL zH)) := by
  let c := extractionCollectionCapacity N M rho t
  let q := extractionBatchSchedule rho gamma (by linarith [hr.1]) hg.le N M
    (membrane s.val.population.live) c.quota zL zH t
  exact productiveSourceCycleLaw N M c.quota q.service hN hM hlarge rho zL zH hr hzL hzH s c.positive
    gamma hg.le q.clock t q.clock_pos q.total_le

theorem productive_ready_membrane_lower (s : ProductiveReady N M rho zL zH) :
    N*M ≤ membrane s.val.population.live := by
  have h := productiveReady_ready N M rho zL zH s
  have hm := membrane_lower N s.val.population.live (fun c hc => (h.2.2.2.1 c hc).1)
  simpa only [h.1] using hm

theorem productive_cycle_kernel_probability
    (hsL : extractDrift rho 0 (lift rho zL)=0) (hsH : extractDrift rho 0 (lift rho zH)=0)
    (hgmax : gamma ≤ 1/100000000000) (htime : (t:ℝ)=8/gamma)
    (p eps : ℝ) (hp : 0 < p) (heps : 0 < eps) (heps1 : eps < 1)
    (s : ProductiveReady N M rho zL zH)
    (hfloor : ∀ b, p*(M:ℝ) ≤ ancestralCount b s.val.population.live) :
    1-productiveCycleError N M t p eps ≤
      (productiveCycleKernel N M hN hM hlarge rho zL zH hr hzL hzH gamma hg t s).expect
        (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput
          (productiveCycleRelation N M (productiveCollectionQuota N M rho t) rho zL zH s.val p eps))) := by
  let c := extractionCollectionCapacity N M rho t
  let q := extractionBatchSchedule rho gamma (by linarith [hr.1]) hg.le N M
    (membrane s.val.population.live) c.quota zL zH t
  have hb := productive_source_cycle_probability N M c.quota q.service hN hM hlarge rho zL zH
    hr hzL hzH s hsL hsH p eps hp heps heps1 hfloor c.positive q.service_pos gamma hg hgmax
    q.clock t q.clock_pos q.total_le q.decay_le htime
  have ho : Real.exp (-(membrane s.val.population.live:ℝ)) ≤ Real.exp (-((N:ℝ)*M)) := by
    apply Real.exp_le_exp.mpr
    have hh : (N:ℝ)*M ≤ (membrane s.val.population.live:ℝ) := by
      exact_mod_cast productive_ready_membrane_lower N M rho zL zH s
    linarith only [hh]
  have hc := c.error_le
  have hq := q.error_le
  change _ ≤ (productiveCycleKernel N M hN hM hlarge rho zL zH hr hzL hzH gamma hg t s).expect _ at hb
  apply le_trans _ hb
  unfold productiveCycleError
  linarith only [hc,hq,ho]

end
end ProductiveMemory
