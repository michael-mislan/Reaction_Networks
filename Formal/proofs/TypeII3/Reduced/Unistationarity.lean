import proofs.TypeII3.Algebra.TransferMap
import proofs.TypeII3.Algebra.CyclicThree
import proofs.TypeII3.Reduced.Defs

namespace TypeII3

theorem sector_comparison
    (q : SectorParams)
    {xPrev x xNext yPrev y yNext : ℝ}
    (hxPrev : 0 < xPrev) (hx : 0 < x) (hxNext : 0 < xNext)
    (hyPrev : 0 < yPrev) (hy : 0 < y) (hyNext : 0 < yNext)
    (hFx : reducedF q xPrev x xNext = 0)
    (hFy : reducedF q yPrev y yNext = 0) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
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
  refine ⟨u, v, hu, hv, ?_⟩
  simpa [u, v] using
    (comparison_equation hx hyPrev hy hyNext hdiff')

theorem reduced_unistationarity
    (p : ReducedParams)
    {x0 x1 x2 y0 y1 y2 : ℝ}
    (hx : PositiveTriple x0 x1 x2)
    (hy : PositiveTriple y0 y1 y2)
    (hrootX : IsReducedRoot p x0 x1 x2)
    (hrootY : IsReducedRoot p y0 y1 y2) :
    x0 = y0 ∧ x1 = y1 ∧ x2 = y2 := by
  rcases hx with ⟨hx0, hx1, hx2⟩
  rcases hy with ⟨hy0, hy1, hy2⟩
  rcases hrootX with ⟨hX0, hX1, hX2⟩
  rcases hrootY with ⟨hY0, hY1, hY2⟩
  rcases sector_comparison p.q0 hx2 hx0 hx1 hy2 hy0 hy1 hX0 hY0 with
    ⟨u0, v0, hu0, hv0, h0⟩
  rcases sector_comparison p.q1 hx0 hx1 hx2 hy0 hy1 hy2 hX1 hY1 with
    ⟨u1, v1, hu1, hv1, h1⟩
  rcases sector_comparison p.q2 hx1 hx2 hx0 hy1 hy2 hy0 hX2 hY2 with
    ⟨u2, v2, hu2, hv2, h2⟩
  have hz := cyclic_three_eq_zero hu0 hu1 hu2 hv0 hv1 hv2 h0 h1 h2
  rcases hz with ⟨hz0, hz1, hz2⟩
  have heq0 : x0 = y0 := by
    have h := hz0
    field_simp [ne_of_gt hy0] at h
    linarith
  have heq1 : x1 = y1 := by
    have h := hz1
    field_simp [ne_of_gt hy1] at h
    linarith
  have heq2 : x2 = y2 := by
    have h := hz2
    field_simp [ne_of_gt hy2] at h
    linarith
  exact ⟨heq0, heq1, heq2⟩

end TypeII3
