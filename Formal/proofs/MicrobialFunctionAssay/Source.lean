import Mathlib.Tactic

namespace MicrobialFunctionAssay

/-- Finite material history. Fresh input enters convertible inventory; release,
uptake, collection, and both loss channels are distinct events. -/
structure Window where
  p0 : ℝ
  r0 : ℝ
  fresh : ℝ
  release : ℝ
  uptake : ℝ
  collect : ℝ
  lossP : ℝ
  lossR : ℝ
  nonneg : 0 ≤ p0 ∧ 0 ≤ r0 ∧ 0 ≤ fresh ∧ 0 ≤ release ∧
    0 ≤ uptake ∧ 0 ≤ collect ∧ 0 ≤ lossP ∧ 0 ≤ lossR
  enoughR : release + lossR ≤ r0 + fresh + uptake
  enoughP : uptake + collect + lossP ≤ p0 + release
  release_available : release ≤ r0 + fresh

def Window.p (w : Window) : ℝ := w.p0 + w.release - w.uptake - w.collect - w.lossP
def Window.r (w : Window) : ℝ := w.r0 + w.fresh + w.uptake - w.release - w.lossR

theorem pool_nonneg (w : Window) : 0 ≤ w.p ∧ 0 ≤ w.r := by
  dsimp [Window.p, Window.r]
  constructor <;> linarith [w.enoughR, w.enoughP]

theorem source_balance (w : Window) :
    w.collect + w.p + w.r + w.lossP + w.lossR = w.p0 + w.r0 + w.fresh := by
  unfold Window.p Window.r
  ring

theorem source_account (w : Window) :
    w.collect + w.p + w.r ≤ w.p0 + w.r0 + w.fresh := by
  have hn := w.nonneg
  linarith [source_balance w]

/-- Recovery inputs are actual amounts, not an assumption of the certificate. -/
structure History where
  first : Window
  second : Window
  e : ℝ
  s : ℝ
  inputP : ℝ
  inputR : ℝ
  fractions : 0 ≤ e ∧ e ≤ s ∧ s ≤ 1
  inputs_nonneg : 0 ≤ inputP ∧ 0 ≤ inputR
  p_recovery : second.p0 ≤ e * first.p + inputP
  r_recovery : second.r0 ≤ s * first.r + inputR

theorem recovery_account (h : History) :
    h.second.collect ≤ h.e*h.first.p + h.s*h.first.r +
      h.inputP + h.inputR + h.second.fresh := by
  have hn := pool_nonneg h.second
  have hb := source_account h.second
  linarith [h.p_recovery, h.r_recovery]

/-- Neutral-acid stoichiometric witness: 4 lactate + 2 acetate produce
3 butyrate + 4 carbon dioxide + 2 hydrogen + 2 water. -/
theorem balanced_conversion :
    (4*3+2*2 : ℕ) = 3*4+4 ∧
    (4*6+2*4 : ℕ) = 3*8+2*2+2*2 ∧
    (4*3+2*2 : ℕ) = 3*2+4*2+2 := by norm_num

theorem sample_amount (v c a : ℝ) : (v-a)*c+a*c=v*c := by ring

end MicrobialFunctionAssay
