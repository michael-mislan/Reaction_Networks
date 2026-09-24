import proofs.RAF1519.Refinement.MarkPath
import proofs.RAF1519.Refinement.RewardEndpoint

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 50000

theorem markPath_noise {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (i : Fin n) (m : PhysicalMark)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ j, 0 < (z (j+1)).2.2)
    (hnoise : z ∉ markIntervalFailure r d k V i m (materialExit V))
    (hsafe : ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hT : t ≤ 4)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z)) :
    |markPath V i m z t-markPrimitive r d k V i m z K t| < markTolerance := by
  let j := countPathIndex z t
  let s := t-prefixElapsed j (Preorder.frestrictLe j z)
  have hh0 := fun q => (hh q).le
  have hi := countPathIndex_spec z hh0 K t ht hK
  have hm := holdingClock_monotone (fun q => (z (q+1)).2.2) hh0
  have hstop : ∀ q, prefixElapsed q (Preorder.frestrictLe q z) < 4 →
      ¬coordinateStop {N | materialSafe V N} 4 (materialExit V) q (Preorder.frestrictLe q z) := by
    intro q hq
    simp only [coordinateStop,not_or,not_not]
    refine ⟨?_,?_,not_le.mpr hq⟩
    · rintro ⟨l,hl⟩
      apply hl
      simpa only [Preorder.frestrictLe_apply] using
        hsafe l ((hm (Finset.mem_Iic.mp l.property)).trans hq.le)
    · simpa only [Preorder.frestrictLe_apply] using hsafe q hq.le
  have hsh : s ≤ min (z (j+1)).2.2 (4-prefixElapsed j (Preorder.frestrictLe j z)) := by
    apply le_min
    · dsimp [s,j]
      linarith [hi.2.2]
    · exact sub_le_sub_right hT _
  have hbound : |coordinateWithin (molecularRate r d k V) (markIncrement V i m)
      {N | materialSafe V N} 4 (materialExit V) z j s| < markTolerance := by
    apply lt_of_not_ge
    intro hcross
    exact hnoise ⟨j,s,sub_nonneg.mpr hi.2.1,hsh,hcross⟩
  have he : markPath V i m z t-markPrimitive r d k V i m z K t =
      coordinateWithin (molecularRate r d k V) (markIncrement V i m)
        {N | materialSafe V N} 4 (materialExit V) z j s := by
    by_cases hj : prefixElapsed j (Preorder.frestrictLe j z) < 4
    · have he := reward_minus_compensation_primitive (molecularRate r d k V) (markIncrement V i m)
        {N | materialSafe V N} 4 (materialExit V) z hh0 K j hi.1 t hT hi.2.1 hi.2.2
        (fun q hq => hstop q ((hm hq).trans_lt hj))
      change rewardPrefix (markIncrement V i m) z j-_ = _
      change rewardPrefix (markIncrement V i m) z j-_ = markPrimitive r d k V i m z K t at he
      linarith
    · have hclock : prefixElapsed j (Preorder.frestrictLe j z)=t := by
        have hhj := hi.2.1
        change prefixElapsed j (Preorder.frestrictLe j z) ≤ t at hhj
        linarith
      have hpast : ∀ q < j,
          ¬coordinateStop {N | materialSafe V N} 4 (materialExit V) q (Preorder.frestrictLe q z) := by
        intro q hq
        exact hstop q ((holdingClock_strictMono _ hh hq).trans_le (hi.2.1.trans hT))
      have he := reward_endpoint_primitive (molecularRate r d k V) (markIncrement V i m)
        {N | materialSafe V N} 4 (materialExit V) z hh0 K j hi.1.le (hi.2.1.trans hT) hpast
      have hs0 : s=0 := by dsimp [s]; rw [hclock]; ring
      rw [hs0]
      simp only [coordinateWithin,mul_zero,sub_zero,ite_self]
      rw [hclock] at he
      change rewardPrefix (markIncrement V i m) z j-_ = _
      change rewardPrefix (markIncrement V i m) z j-_ = markPrimitive r d k V i m z K t at he
      linarith
  rw [he]
  exact hbound

end
end RAF1519.Refinement
