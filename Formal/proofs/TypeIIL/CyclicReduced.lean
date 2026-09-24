import proofs.TypeIIL.CyclicComparison
import proofs.TypeII3.Algebra.TransferMap
import proofs.TypeII3.Reduced.Defs

namespace TypeIIL

open TypeII3

/-- The sector comparison theorem with the physical forward-gain inequality
retained.  The older Type II_3 theorem needed only positivity of `u,v`; an
arbitrary even cycle also needs `f < e`. -/
theorem sector_comparison_with_gain
    (q : SectorParams) (hef : q.f < q.e)
    {xPrev x xNext yPrev y yNext : ℝ}
    (hxPrev : 0 < xPrev) (hx : 0 < x) (hxNext : 0 < xNext)
    (hyPrev : 0 < yPrev) (hy : 0 < y) (hyNext : 0 < yNext)
    (hFx : reducedF q xPrev x xNext = 0)
    (hFy : reducedF q yPrev y yNext = 0) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ v * y < u * yNext ∧
      xPrev / yPrev - 1 =
        (1 + u) * (x / y - 1) + v * (xNext / yNext - 1) := by
  let tx := q.e * x + q.f * xNext
  let ty := q.e * y + q.f * yNext
  have htx : 0 < tx := by
    dsimp [tx]
    exact add_pos (mul_pos q.e_pos hx) (mul_pos q.f_pos hxNext)
  have hty : 0 < ty := by
    dsimp [ty]
    exact add_pos (mul_pos q.e_pos hy) (mul_pos q.f_pos hyNext)
  have hrearrX :
      (q.A - q.lam * tx ^ q.m * q.a) * xPrev =
        (q.B + q.lam * q.b * tx ^ q.m) * x := by
    unfold reducedF at hFx
    dsimp [tx]
    linear_combination hFx
  have hrearrY :
      (q.A - q.lam * ty ^ q.m * q.a) * yPrev =
        (q.B + q.lam * q.b * ty ^ q.m) * y := by
    unfold reducedF at hFy
    dsimp [ty]
    linear_combination hFy
  have hdenX : 0 < q.A - q.lam * tx ^ q.m * q.a :=
    denominator_pos_of_root q.B_pos q.lam_pos q.b_pos htx hxPrev hx hrearrX
  have hdenY : 0 < q.A - q.lam * ty ^ q.m * q.a :=
    denominator_pos_of_root q.B_pos q.lam_pos q.b_pos hty hyPrev hy hrearrY
  have hratioX :
      xPrev / x = transfer q.A q.B q.lam q.a q.b q.m tx :=
    ratio_eq_transfer_of_root hx hdenX hrearrX
  have hratioY :
      yPrev / y = transfer q.A q.B q.lam q.a q.b q.m ty :=
    ratio_eq_transfer_of_root hy hdenY hrearrY
  let K := transferGain q.A q.B q.lam q.a q.b tx ty q.m
  have hK : 0 < K := by
    dsimp [K]
    exact transferGain_pos q.A_pos q.B_pos q.lam_pos q.a_pos q.b_pos
      htx hty q.m_pos hdenX hdenY
  have hdiff :
      xPrev / x - yPrev / y = K * (tx - ty) := by
    rw [hratioX, hratioY]
    simpa [K] using
      (transfer_difference (A := q.A) (B := q.B) (lam := q.lam)
        (a := q.a) (b := q.b) (r := tx) (s := ty) (m := q.m)
        (ne_of_gt hdenX) (ne_of_gt hdenY))
  have hdiff' :
      xPrev / x - yPrev / y =
        K * ((q.e * x + q.f * xNext) - (q.e * y + q.f * yNext)) := by
    simpa [tx, ty] using hdiff
  let u := K * q.e * (x / y) * y ^ 2 / yPrev
  let v := K * q.f * (x / y) * y * yNext / yPrev
  have hxy : 0 < x / y := div_pos hx hy
  have hu : 0 < u := by
    dsimp [u]
    exact div_pos
      (mul_pos (mul_pos (mul_pos hK q.e_pos) hxy) (pow_pos hy 2)) hyPrev
  have hv : 0 < v := by
    dsimp [v]
    exact div_pos
      (mul_pos (mul_pos (mul_pos (mul_pos hK q.f_pos) hxy) hy) hyNext) hyPrev
  have hcommon : 0 < K * (x / y) * y ^ 2 * yNext / yPrev := by
    exact div_pos
      (mul_pos (mul_pos (mul_pos hK hxy) (pow_pos hy 2)) hyNext) hyPrev
  have hgain : v * y < u * yNext := by
    have hmul := mul_lt_mul_of_pos_right hef hcommon
    dsimp [u, v]
    convert hmul using 1 <;> ring
  refine ⟨u, v, hu, hv, hgain, ?_⟩
  simpa [u, v] using
    (comparison_equation hx hyPrev hy hyNext hdiff')

/-- An arbitrary single cycle of reduced Type II sectors. -/
structure CyclicReducedData (l : ℕ) where
  next : Fin l ≃ Fin l
  next_singleCycle : IsSingleCycle next
  q : Fin l → SectorParams
  response_gain : ∀ i, (q i).f < (q i).e

def IsCyclicReducedRoot (D : CyclicReducedData l) (x : Fin l → ℝ) : Prop :=
  ∀ i, reducedF (D.q i) (x (D.next.symm i)) (x i) (x (D.next i)) = 0

/-- Positive roots of an arbitrary cyclic reduced Type II system coincide. -/
theorem cyclic_reduced_unistationarity
    [NeZero l] (D : CyclicReducedData l) (x y : Fin l → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hX : IsCyclicReducedRoot D x) (hY : IsCyclicReducedRoot D y) :
    x = y := by
  classical
  have hsector : ∀ i, ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
      v * y i < u * y (D.next i) ∧
      x (D.next.symm i) / y (D.next.symm i) - 1 =
        (1 + u) * (x i / y i - 1) +
          v * (x (D.next i) / y (D.next i) - 1) := by
    intro i
    exact sector_comparison_with_gain (D.q i) (D.response_gain i)
      (hx _) (hx _) (hx _) (hy _) (hy _) (hy _) (hX i) (hY i)
  choose u v hu hv hgain hrec using hsector
  let z : Fin l → ℝ := fun i => x i / y i - 1
  have hz := cyclic_comparison_eq_zero D.next D.next_singleCycle u v y z
    hu hv hy hgain (by simpa [z] using hrec)
  funext i
  have hzi := hz i
  dsimp [z] at hzi
  field_simp [ne_of_gt (hy i)] at hzi
  linarith

end TypeIIL
