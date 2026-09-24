import proofs.PowerLawSmallRAF.LigationStaticHistoryLaw
import proofs.PowerLawSmallRAF.LigationDensityProbability

namespace PowerLawSmallRAF

open scoped BigOperators

/-- Target failure under the static product of full split-position rows.
The schedule is duplicate-free, so repeated occurrences of a word share its
single physical row. The ambient set is intended to be the target substrings. -/
theorem ligationTarget_static_mass_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (words : List LigationWord) (hnd : words.Nodup)
    (horder : words.Pairwise (fun u v => u.length ≤ v.length))
    (ambient known : Finset LigationWord) (L : Nat) (hL : 4 ≤ L)
    (hlarge : 32 * Real.log 2 ≤ p * (L : ℝ))
    (hclosed : ∀ w ∈ ambient, ∀ i ∈ ligationCuts w, ∀ isPrefix : Bool,
      ligationCutPart isPrefix w i ∈ ambient)
    (hfood : ∀ w ∈ ambient, w.length ≤ L → w ∈ known)
    (hcover : ambient ⊆ words.toFinset) (target : LigationWord)
    (htarget : target ∈ ambient) (htlen : L ≤ target.length) :
    (∑ cfg : LigationRawConfiguration words,
      if target ∉ ligationRawKnown words cfg known then ligationRawWeight p words cfg else 0) ≤
      Real.exp (-p * (target.length : ℝ) / 2) +
        2 * (ambient.card : ℝ) * Real.exp (-p * (L : ℝ)^2 / 32) := by
  classical
  have heq := ligationRaw_history_expectation p words known
    (fun state => if target ∉ state then 1 else 0)
  have hleft : (∑ cfg : LigationRawConfiguration words,
      ligationRawWeight p words cfg *
        (if target ∉ ligationRawKnown words cfg known then 1 else 0)) =
      ∑ cfg : LigationRawConfiguration words,
        if target ∉ ligationRawKnown words cfg known then ligationRawWeight p words cfg else 0 := by
    apply Finset.sum_congr rfl
    intro cfg _
    split_ifs <;> simp
  have hright : (∑ bits : Fin words.length → Bool,
      ligationHistoryWeight p words bits known *
        (if target ∉ ligationHistoryKnown words bits known then 1 else 0)) =
      ligationHistoryEventMass p words known (fun bits =>
        target ∉ ligationHistoryKnown words bits known) := by
    unfold ligationHistoryEventMass
    apply Finset.sum_congr rfl
    intro bits _
    simp only [mul_ite, mul_one, mul_zero]
    congr 1
  rw [hleft, hright] at heq
  rw [heq]
  exact ligationTarget_history_mass_le hp hp1 words hnd horder ambient known L hL hlarge
    hclosed hfood hcover target htarget htlen

end PowerLawSmallRAF
