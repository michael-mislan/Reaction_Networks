import proofs.RAF1519.Refinement.GraphComparison

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

/-- Exponential rescaling permits positive linear growth of violations. -/
theorem graph_right_barrier_growth {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (w v : ℝ → ι → ℝ) (T C : ℝ)
    (hc : ∀ i, ContinuousOn (fun t => w t i) (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, ∀ i, HasDerivWithinAt (fun u => w u i) (v t i) (Set.Ici t) t)
    (h0 : ∀ i, w 0 i ≤ 0)
    (hb : ∀ t ∈ Set.Ico 0 T, ∀ i, 0 < w t i →
      v t i ≤ (∑ j, k i j*(w t j-w t i))+C*w t i) :
    ∀ t ∈ Set.Icc 0 T, ∀ i, w t i ≤ 0 := by
  let A := fun t => Real.exp (-C*t)
  have hA (t : ℝ) : HasDerivAt A (-C*A t) t := by
    simpa [A,mul_comm] using ((hasDerivAt_id t).const_mul (-C)).exp
  have hpos (t : ℝ) : 0 < A t := Real.exp_pos _
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hbound := graph_right_barrier k hk hsym (fun t i => A t*w t i)
    (fun t i => A t*(v t i-C*w t i)) T
    (fun i => hAc.continuousOn.mul (hc i))
    (fun t ht i => by convert (hA t).hasDerivWithinAt.mul (hd t ht i) using 1; ring)
    (fun i => by simpa [A] using h0 i) (by
      intro t ht i hi
      have hw : 0 < w t i := pos_of_mul_pos_right hi (hpos t).le
      have hm := mul_le_mul_of_nonneg_left (hb t ht i hw) (hpos t).le
      have he : (∑ j, k i j*(A t*w t j-A t*w t i)) =
          A t*(∑ j, k i j*(w t j-w t i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he]
      nlinarith)
  intro t ht i
  by_contra hi
  have hp := mul_pos (hpos t) (lt_of_not_ge hi)
  linarith [hbound t ht i]

end
end RAF1519.Refinement
