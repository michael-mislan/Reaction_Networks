import proofs.ProductiveMemory.ExtractionTwoCycle

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

def productiveCountOutput (N M J : ℕ) (rho zL zH : ℝ) (s : ProductiveState)
    (y : ProductiveTwoResult N M J rho zL zH) : Prop :=
  (∀ b, 0 < ancestralCount b y.1.1.val.population.live) ∧
  519/12250 < SerialTransferSelection.countLogOdds y.1.1.val.population-
    SerialTransferSelection.countLogOdds s.population ∧
  5*membrane s.population.live < y.2.val ∧ 5*(N*M) < y.1.2.val

theorem productive_count_output_probability (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hsL : extractDrift rho 0 (lift rho zL)=0) (hsH : extractDrift rho 0 (lift rho zH)=0)
    (s : ProductiveReady recoveryCount productiveM rho zL zH)
    (hfloor : ∀ b, (1/2:ℝ)*productiveM ≤ ancestralCount b s.val.population.live) :
    995994/1000000 ≤
      (productiveTwoCycleLaw recoveryCount productiveM (by norm_num [recoveryCount])
        (by norm_num [productiveM]) le_rfl rho zL zH hr hzL hzH productiveGamma
        (by norm_num [productiveGamma]) productiveTime s).expect
        (FiniteKernel.eventIndicator (SerialTransferSelection.successfulOutput
          (productiveCountOutput recoveryCount productiveM
            (productiveJ recoveryCount productiveM rho productiveTime) rho zL zH s.val))) := by
  have h := productive_two_cycle_probability recoveryCount productiveM
    (by norm_num [recoveryCount]) (by norm_num [productiveM]) le_rfl rho zL zH hr hzL hzH
    productiveGamma (by norm_num [productiveGamma]) productiveTime hsL hsH
    (by norm_num [productiveGamma]) (by norm_num [productiveGamma,productiveTime])
    (1/2) (1/100) (1/50) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) s hfloor
  have he0 := productive_cycle_error_evaluated (1/2) (by norm_num)
  have he1 := productive_cycle_error_evaluated (1/100) le_rfl
  apply le_trans (show (995994/1000000:ℝ) ≤ 1-(productiveCycleError recoveryCount productiveM productiveTime (1/2) (1/50)+
      productiveCycleError recoveryCount productiveM productiveTime (1/100) (1/50)) by linarith only [he0,he1])
  apply h.trans
  apply SerialTransferSelection.finiteLaw_successful_mono
  intro y hy
  have hcs (b : Bool) : 0 < ancestralCount b s.val.population.live := by
    have hp : (0:ℝ) < (1/2:ℝ)*productiveM := by norm_num [productiveM]
    exact_mod_cast hp.trans_le (hfloor b)
  have hc := SerialTransferSelection.endpoint_count_gain recoveryCount (by norm_num [recoveryCount])
    s.val.population y.1.1.val.population
    (productiveReady_ready recoveryCount productiveM rho zL zH s).2.2.2.1
    (productiveReady_ready recoveryCount productiveM rho zL zH y.1.1).2.2.2.1 hcs hy.1 _ hy.2.1
  exact ⟨hy.1,SerialTransferSelection.two_cycle_count_gain_lower.trans_lt hc,hy.2.2⟩

end
end ProductiveMemory
