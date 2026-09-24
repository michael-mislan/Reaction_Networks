import proofs.TypeIIL.SourceWrapEndpointBudget

namespace TypeIIL

/-- A literal finite source path, with its proper prefix reserved, satisfies
the coupled wrap margin directly from its row equations and the two signed
endpoint budgets.  The terminal unit weight is the only minimality input.

The `xf` equations are the difference of the two adjacent fork responses;
their penultimate forcing is the successor coefficient.  The `yw` equations
are the left-fork response.  Thus the four terminal response identities are
derived here from `finiteSourcePathMatrix`, rather than exposed as hypotheses. -/
theorem finiteSourcePath_response_raw_two_edge_margin_of_endpoint_budgets
    {m : ℕ} (hm : 1 < m) (A c s : Fin (m + 1) → ℝ)
    {scale k h g X Bprev Fprev W followingBudget precedingCorrection : ℝ}
    (xf yw : Fin (m + 1) → ℝ)
    (hA : ∀ i, 0 < A i) (hc : ∀ i, 0 < c i) (hs : ∀ i, 0 < s i)
    (hterminalUnit : s (Fin.last m) = 1)
    (hscale : 0 < scale) (hk : 0 < k) (hh : 0 < h) (hg : 0 ≤ g)
    (hfollowing : 0 ≤ followingBudget)
    (hpreceding : precedingCorrection ≤ 0)
    (hX :
      let eff := natWrapPrefixState (finitePathNatLift A)
        (finitePathNatLift c) (finitePathNatLift s) scale k (m - 1)
      let Aeff := wrapCondensedA eff.A
        (finitePathNatLift A m) (finitePathNatLift c (m - 1))
        (finitePathNatLift s (m - 1))
      let heffR := wrapCondensedH eff.A (finitePathNatLift c (m - 1))
        (finitePathNatLift s (m - 1)) h
      let d := 1 + Aeff + finitePathNatLift c m
      X = (d + g + heffR) / d + followingBudget)
    (hBprev :
      let eff := natWrapPrefixState (finitePathNatLift A)
        (finitePathNatLift c) (finitePathNatLift s) scale k (m - 1)
      let Aeff := wrapCondensedA eff.A
        (finitePathNatLift A m) (finitePathNatLift c (m - 1))
        (finitePathNatLift s (m - 1))
      let seff := wrapCondensedScale eff.A
        (finitePathNatLift s (m - 1)) eff.scale
      let keff := wrapCondensedK eff.A (finitePathNatLift c (m - 1))
        (finitePathNatLift s (m - 1)) eff.k
      let d := 1 + Aeff + finitePathNatLift c m
      Bprev = (d + keff * seff * (1 + finitePathNatLift c m)) / d -
        precedingCorrection)
    (hxfFirst : ∑ j, finiteSourcePathMatrix A c s 0 j * xf j = 0)
    (hxfRows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m - 1 →
      ∑ j, finiteSourcePathMatrix A c s i j * xf j = 0)
    (hxfPenultimate :
      ∑ j, finiteSourcePathMatrix A c s ⟨m - 1, by omega⟩ j * xf j =
        c ⟨m - 1, by omega⟩)
    (hxfTerminal :
      ∑ j, finiteSourcePathMatrix A c s (Fin.last m) j * xf j =
        -(A (Fin.last m) + c (Fin.last m)))
    (hFprev :
      let eff := natWrapPrefixState (finitePathNatLift A)
        (finitePathNatLift c) (finitePathNatLift s) scale k (m - 1)
      Fprev = eff.k * finitePathNatLift xf (m - 1))
    (hywFirst :
      ∑ j, finiteSourcePathMatrix A c s 0 j * yw j = -(A 0 * scale))
    (hywRows : ∀ i : Fin (m + 1), 0 < i.val → i.val < m - 1 →
      ∑ j, finiteSourcePathMatrix A c s i j * yw j = 0)
    (hywPenultimate :
      ∑ j, finiteSourcePathMatrix A c s ⟨m - 1, by omega⟩ j * yw j = 0)
    (hywTerminal :
      ∑ j, finiteSourcePathMatrix A c s (Fin.last m) j * yw j = 0)
    (hW : W = -(h * finitePathNatLift s (m - 1) *
        finitePathNatLift yw (m - 1) - (g + h) * finitePathNatLift yw m)) :
    W * Fprev < X * Bprev := by
  let An := finitePathNatLift A
  let cn := finitePathNatLift c
  let sn := finitePathNatLift s
  let xfn := finitePathNatLift xf
  let ywn := finitePathNatLift yw
  let eff := natWrapPrefixState An cn sn scale k (m - 1)
  have hforward₀ :
      wrapPrefixPivot eff.A (cn (m - 1)) (sn (m - 1)) * xfn (m - 1) -
          cn (m - 1) * xfn m = cn (m - 1) := by
    have h := finiteSourcePath_properPrefixEquation_final_rhs hm A c s xf
      (L := 0) (rhs := c ⟨m - 1, by omega⟩) hA hc hs hscale hk
      (by simpa using hxfFirst) hxfRows hxfPenultimate
    simpa [An, cn, sn, xfn, eff, wrapPrefixPivot,
      finitePathNatLift_of_lt] using h
  have hforward₁ :
      -(An m * sn (m - 1)) * xfn (m - 1) +
          (1 + An m + cn m) * xfn m = -(An m + cn m) := by
    have ht := hxfTerminal
    rw [finiteSourcePathMatrix_mul_apply] at ht
    have hmpos : 0 < m := by omega
    simp only [Fin.val_last, lt_self_iff_false, dite_false] at ht
    rw [dif_pos hmpos] at ht
    have hprevEq : finitePathPrev (Fin.last m) hmpos =
        ⟨m - 1, by omega⟩ := by
      apply Fin.ext
      simp [finitePathPrev]
    rw [hprevEq, hterminalUnit] at ht
    have hAm : An m = A (Fin.last m) := by
      dsimp [An]
      rw [finitePathNatLift_of_lt (i := m) A (by omega)]
      rfl
    have hcm : cn m = c (Fin.last m) := by
      dsimp [cn]
      rw [finitePathNatLift_of_lt (i := m) c (by omega)]
      rfl
    have hsp : sn (m - 1) = s ⟨m - 1, by omega⟩ := by
      dsimp [sn]
      rw [finitePathNatLift_of_lt (i := m - 1) s (by omega)]
    have hxp : xfn (m - 1) = xf ⟨m - 1, by omega⟩ := by
      dsimp [xfn]
      rw [finitePathNatLift_of_lt (i := m - 1) xf (by omega)]
    have hxm : xfn m = xf (Fin.last m) := by
      dsimp [xfn]
      rw [finitePathNatLift_of_lt (i := m) xf (by omega)]
      rfl
    rw [hAm, hcm, hsp, hxp, hxm]
    linarith
  have hwrap₀ :
      wrapPrefixPivot eff.A (cn (m - 1)) (sn (m - 1)) * ywn (m - 1) -
          cn (m - 1) * ywn m = -(eff.A * eff.scale) := by
    have h := finiteSourcePath_properPrefixEquation_final_rhs hm A c s yw
      (L := -1) (rhs := 0) hA hc hs hscale hk
      (by simpa using hywFirst) hywRows hywPenultimate
    change (1 + eff.A + cn (m - 1) * sn (m - 1)) * ywn (m - 1) -
        cn (m - 1) * ywn m - eff.A * eff.scale * (-1) = 0 at h
    unfold wrapPrefixPivot
    linear_combination h
  have hwrap₁ :
      -(An m * sn (m - 1)) * ywn (m - 1) +
          (1 + An m + cn m) * ywn m = 0 := by
    have ht := hywTerminal
    rw [finiteSourcePathMatrix_mul_apply] at ht
    have hmpos : 0 < m := by omega
    simp only [Fin.val_last, lt_self_iff_false, dite_false] at ht
    rw [dif_pos hmpos] at ht
    have hprevEq : finitePathPrev (Fin.last m) hmpos =
        ⟨m - 1, by omega⟩ := by
      apply Fin.ext
      simp [finitePathPrev]
    rw [hprevEq, hterminalUnit] at ht
    have hAm : An m = A (Fin.last m) := by
      dsimp [An]
      rw [finitePathNatLift_of_lt (i := m) A (by omega)]
      rfl
    have hcm : cn m = c (Fin.last m) := by
      dsimp [cn]
      rw [finitePathNatLift_of_lt (i := m) c (by omega)]
      rfl
    have hsp : sn (m - 1) = s ⟨m - 1, by omega⟩ := by
      dsimp [sn]
      rw [finitePathNatLift_of_lt (i := m - 1) s (by omega)]
    have hyp : ywn (m - 1) = yw ⟨m - 1, by omega⟩ := by
      dsimp [ywn]
      rw [finitePathNatLift_of_lt (i := m - 1) yw (by omega)]
    have hym : ywn m = yw (Fin.last m) := by
      dsimp [ywn]
      rw [finitePathNatLift_of_lt (i := m) yw (by omega)]
      rfl
    rw [hAm, hcm, hsp, hyp, hym]
    linarith
  apply natWrapPrefix_response_raw_two_edge_margin_of_endpoint_budgets
      An cn sn (m - 1) (scale := scale) (k := k)
      (nextA := An m) (edgeC := cn (m - 1)) (edgeS := sn (m - 1))
      (terminalC := cn m) (h := h) (g := g)
      (xf₀ := xfn (m - 1)) (xf₁ := xfn m)
      (yw₀ := ywn (m - 1)) (yw₁ := ywn m)
      (followingBudget := followingBudget)
      (precedingCorrection := precedingCorrection)
  · intro i
    exact hA _
  · intro i
    exact hc _
  · intro i
    exact hs _
  · exact hscale
  · exact hk
  · exact hA _
  · exact hc _
  · exact hs _
  · exact hc _
  · exact hh
  · exact hg
  · exact hfollowing
  · exact hpreceding
  · simpa [An, cn, sn, eff] using hX
  · simpa [An, cn, sn, eff] using hBprev
  · exact hforward₀
  · exact hforward₁
  · simpa [An, cn, sn, xfn, eff] using hFprev
  · exact hwrap₀
  · exact hwrap₁
  · simpa [sn, ywn] using hW

end TypeIIL
