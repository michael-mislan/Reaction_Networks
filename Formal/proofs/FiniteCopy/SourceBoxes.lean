import proofs.FiniteCopy.SourceAdapter

namespace FiniteCopy
open CoreCouplingCAC Set

theorem low_source_box (z : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000)) :
    reducedA sourceRates z ∈ Icc 12 14 ∧
    reducedB sourceRates z ∈ Icc (200280/10000) (200282/10000) ∧
    reducedH sourceRates z ∈ Icc 8 10 := by
  have hd : 0 < z+2 := by linarith [hz.1]
  have hb : reducedB sourceRates z ∈ Icc (200280/10000) (200282/10000) := by
    unfold reducedB sourceRates
    norm_num only
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [hz.2]
    · apply (div_le_iff₀ hd).mpr
      linarith [hz.1]
  have zz : z^2 ∈ Icc ((99/100)^2) ((101/100)^2) := by
    constructor <;> nlinarith [hz.1,hz.2]
  have zb : z*reducedB sourceRates z ∈ Icc (199/10) (201/10) := by
    constructor <;> nlinarith [hz.1,hz.2,hb.1,hb.2]
  dsimp only [sourceRates] at zb
  refine ⟨?_,hb,?_⟩
  · unfold reducedA reducedK sourceRates
    norm_num only
    constructor <;> nlinarith [hz.1,hz.2,zz.1,zz.2,zb.1,zb.2]
  · unfold reducedH sourceRates
    norm_num only
    constructor <;> nlinarith [hz.1,hz.2,zz.1,zz.2]

theorem high_source_box (z : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)) :
    reducedA sourceRates z ∈ Icc 20 22 ∧
    reducedB sourceRates z ∈ Icc (120569/10000) (120571/10000) ∧
    reducedH sourceRates z ∈ Icc 32 34 := by
  have hd : 0 < z+2 := by linarith [hz.1]
  have hb : reducedB sourceRates z ∈ Icc (120569/10000) (120571/10000) := by
    unfold reducedB sourceRates
    norm_num only
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [hz.2]
    · apply (div_le_iff₀ hd).mpr
      linarith [hz.1]
  have zz : z^2 ∈ Icc ((297/100)^2) ((298/100)^2) := by
    constructor <;> nlinarith [hz.1,hz.2]
  have zb : z*reducedB sourceRates z ∈ Icc (358/10) 36 := by
    constructor <;> nlinarith [hz.1,hz.2,hb.1,hb.2]
  dsimp only [sourceRates] at zb
  refine ⟨?_,hb,?_⟩
  · unfold reducedA reducedK sourceRates
    norm_num only
    constructor <;> nlinarith [hz.1,hz.2,zz.1,zz.2,zb.1,zb.2]
  · unfold reducedH sourceRates
    norm_num only
    constructor <;> nlinarith [hz.1,hz.2,zz.1,zz.2]

end FiniteCopy


