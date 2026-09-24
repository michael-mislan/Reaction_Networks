import proofs.RobustPermanence.RateBox

namespace RobustPermanence
open CoreCouplingGlobal CoreCouplingCAC

theorem small_rate_monomial (d t : ℝ) (hd : |d| ≤ rateRadius) (ht : |t| ≤ 2000) :
    -(1/100000000000000:ℝ) ≤ d*t ∧ d*t ≤ 1/100000000000000 := by
  have hh := mul_le_mul hd ht (abs_nonneg t) (by norm_num [rateRadius] : 0 ≤ rateRadius)
  rw [← abs_mul] at hh
  have hb : |d*t| ≤ 1/100000000000000 := by
    dsimp [rateRadius] at hh
    linarith only [hh]
  exact abs_le.1 hb

/-- The entire literal field error is uniformly small on the common absorber.
Every error term is a rate difference times its actual mass-action monomial. -/
theorem rate_resident_errors (e : ℝ) (r : AssemblyRates) (hr : RateNeighborhood e r)
    (A B z H X : ℝ) (hA : 0 ≤ A) (hA' : A ≤ 34) (hB : 0 ≤ B) (hB' : B ≤ 34)
    (hz : 0 ≤ z) (hz' : z ≤ 12) (hH : 0 ≤ H) (hH' : H ≤ 1536/7)
    (hX : 0 ≤ X) (hX' : X ≤ 12) :
    |rateA r A B z-fA (flagshipRates e) A B z| ≤ 1/10000000000000 ∧
    |rateB r A B z-fB (flagshipRates e) A B z| ≤ 1/10000000000000 ∧
    |rateZ r A B z H X-(fZ (flagshipRates e) A B z H-z*X)| ≤ 1/10000000000000 ∧
    |rateH r z H-fH (flagshipRates e) z H| ≤ 1/10000000000000 ∧
    |(r.k*z-r.mu-r.rho*X)-(z-1/2-X)| ≤ 1/10000000000000 := by
  have h1 : |(1:ℝ)| ≤ 2000 := by norm_num
  have hAa : |A| ≤ 2000 := abs_le.2 ⟨by linarith,by linarith⟩
  have hBa : |B| ≤ 2000 := abs_le.2 ⟨by linarith,by linarith⟩
  have hza : |z| ≤ 2000 := abs_le.2 ⟨by linarith,by linarith⟩
  have hHa : |H| ≤ 2000 := abs_le.2 ⟨by linarith,by linarith⟩
  have hXa : |X| ≤ 2000 := abs_le.2 ⟨by linarith,by linarith⟩
  have hAA : |A^2| ≤ 2000 := by rw [abs_of_nonneg (sq_nonneg A)]; nlinarith
  have hzz : |z^2| ≤ 2000 := by rw [abs_of_nonneg (sq_nonneg z)]; nlinarith
  have hBz : |B*z| ≤ 2000 := by
    rw [abs_of_nonneg (mul_nonneg hB hz)]
    have hh := mul_le_mul hB' hz' hz (by norm_num : (0:ℝ) ≤ 34)
    linarith only [hh]
  have hzX : |z*X| ≤ 2000 := by
    rw [abs_of_nonneg (mul_nonneg hz hX)]
    have hh := mul_le_mul hz' hX' hX (by norm_num : (0:ℝ) ≤ 12)
    linarith only [hh]
  have ea := small_rate_monomial _ _ hr.a h1
  have eb := small_rate_monomial _ _ hr.b h1
  have ep := small_rate_monomial _ _ hr.p hAa
  have eq := small_rate_monomial _ _ hr.q hBz
  have ealpha := small_rate_monomial _ _ hr.alpha hAa
  have ebeta := small_rate_monomial _ _ hr.beta hBa
  have eef := small_rate_monomial _ _ hr.ef hBa
  have eer := small_rate_monomial _ _ hr.er hAA
  have eu := small_rate_monomial _ _ hr.u hza
  have ev := small_rate_monomial _ _ hr.v hzz
  have eh1 := small_rate_monomial _ _ hr.h1 hHa
  have eh2 := small_rate_monomial _ _ hr.h2 hHa
  have ed := small_rate_monomial _ _ hr.d hHa
  have ek := small_rate_monomial _ _ hr.k hzX
  have ekz := small_rate_monomial _ _ hr.k hza
  have emu := small_rate_monomial _ _ hr.mu h1
  have erho := small_rate_monomial _ _ hr.rho hXa
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply abs_le.2
    dsimp [rateA,fA,flagshipRates]
    constructor <;> nlinarith only [ea.1,ea.2,ep.1,ep.2,eq.1,eq.2,ealpha.1,ealpha.2,eef.1,eef.2,eer.1,eer.2]
  · apply abs_le.2
    dsimp [rateB,fB,flagshipRates]
    constructor <;> nlinarith only [eb.1,eb.2,ep.1,ep.2,eq.1,eq.2,ebeta.1,ebeta.2,eef.1,eef.2,eer.1,eer.2]
  · apply abs_le.2
    dsimp [rateZ,fZ,flagshipRates]
    constructor <;> nlinarith only [ep.1,ep.2,eq.1,eq.2,eu.1,eu.2,ev.1,ev.2,eh1.1,eh1.2,eh2.1,eh2.2,ek.1,ek.2]
  · apply abs_le.2
    dsimp [rateH,fH,flagshipRates]
    constructor <;> nlinarith only [eu.1,eu.2,ev.1,ev.2,eh1.1,eh1.2,eh2.1,eh2.2,ed.1,ed.2]
  · apply abs_le.2
    constructor <;> nlinarith only [ekz.1,ekz.2,emu.1,emu.2,erho.1,erho.2]

end RobustPermanence
