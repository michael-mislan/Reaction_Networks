import proofs.CoreCouplingGlobal.SpectralSigns

namespace CoreCouplingGlobal
open Set Polynomial

theorem polynomial_strict_sign_root (P : ℝ[X]) (a b : ℝ) (hab : a < b)
    (ha : P.eval a < 0) (hb : 0 < P.eval b) :
    ∃ x ∈ Ioo a b, P.eval x = 0 := by
  obtain ⟨x,hx,hroot⟩ := intermediate_value_Icc hab.le P.continuous.continuousOn ⟨ha.le,hb.le⟩
  have hxa : a < x := by
    rcases lt_or_eq_of_le hx.1 with h | h
    · exact h
    · rw [← h] at hroot; linarith
  have hxb : x < b := by
    rcases lt_or_eq_of_le hx.2 with h | h
    · exact h
    · rw [h] at hroot; linarith
  exact ⟨x,⟨hxa,hxb⟩,hroot⟩

theorem monic_quartic_factor_of_four_roots (P : ℝ[X]) (hP : P.Monic)
    (hdeg : P.natDegree = 4) (a b c d : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : P.eval a = 0) (hb : P.eval b = 0) (hc : P.eval c = 0) (hd : P.eval d = 0) :
    P = (X-C a)*(X-C b)*(X-C c)*(X-C d) := by
  classical
  let S : Finset ℝ := {a,b,c,d}
  have hac := hab.trans hbc
  have hbd := hbc.trans hcd
  have had := hac.trans hcd
  have hcard : S.card = 4 := by simp [S,hab.ne,hac.ne,had.ne,hbc.ne,hbd.ne,hcd.ne]
  have hroots : P.roots = S.val := roots_eq_of_natDegree_le_card_of_ne_zero
    (by intro x hx; simp only [S,Finset.mem_insert,Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    (by rw [hdeg,hcard]) hP.ne_zero
  have hcount : P.roots.card = P.natDegree := by rw [hroots,hdeg]; exact hcard
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP hcount
  rw [hroots] at hprod
  have heq : (S.val.map (fun a => X-C a)).prod = (X-C a)*(X-C b)*(X-C c)*(X-C d) := by
    change (∏ a ∈ S, (X-C a)) = _
    simp [S,hab.ne,hac.ne,had.ne,hbc.ne,hbd.ne,hcd.ne,mul_assoc]
  exact hprod.symm.trans heq

theorem characteristic_sign_of_scaled (e p z l σ : ℝ) (hz : 0 < z+2)
    (h : 0 < σ*scaledCharacteristic e p z l) :
    0 < σ*(stationaryJacobian e p z).charpoly.eval l := by
  rw [scaledCharacteristic_eq e p z l hz.ne'] at h
  have hh : σ*((z+2)*(stationaryJacobian e p z).charpoly.eval l) =
      (z+2)*(σ*(stationaryJacobian e p z).charpoly.eval l) := by ring
  rw [hh] at h
  exact (mul_pos_iff_of_pos_left hz).1 h

/-- Four disjoint real brackets exhaust a degree-four characteristic polynomial. -/
theorem stationary_four_real_roots (e p z u v : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/50000) (hp : 0 ≤ p) (hpu : p ≤ 17/25000)
    (hz : z ∈ Icc (9/10:ℝ) (31/10)) (hu : -(1/2:ℝ) ≤ u) (huv : u < v)
    (hleft : (stationaryJacobian e p z).charpoly.eval u < 0)
    (hright : 0 < (stationaryJacobian e p z).charpoly.eval v) :
    ∃ a b c d : ℝ, a ∈ Ioo (-80:ℝ) (-10) ∧ b ∈ Ioo (-10:ℝ) (-2) ∧
      c ∈ Ioo (-2:ℝ) (-(1/2)) ∧ d ∈ Ioo u v ∧
      (stationaryJacobian e p z).charpoly = (X-C a)*(X-C b)*(X-C c)*(X-C d) := by
  let P := (stationaryJacobian e p z).charpoly
  have hz0 : 0 < z+2 := by linarith [hz.1]
  have h80 := characteristic_sign_of_scaled e p z (-80) 1 hz0 (spectral_sign_neg80 e p z he heu hp hpu hz)
  have h10 := characteristic_sign_of_scaled e p z (-10) (-1) hz0 (spectral_sign_neg10 e p z he heu hp hpu hz)
  have h2 := characteristic_sign_of_scaled e p z (-2) 1 hz0 (spectral_sign_neg2 e p z he heu hp hpu hz)
  have hh := characteristic_sign_of_scaled e p z (-(1/2)) (-1) hz0
    (by simpa only [neg_div] using spectral_sign_negHalf e p z he heu hp hpu hz)
  have h80' : P.eval (-80) > 0 := by simpa only [one_mul] using h80
  have h10' : P.eval (-10) < 0 := by dsimp [P]; linarith
  have h2' : P.eval (-2) > 0 := by simpa only [one_mul] using h2
  have hh' : P.eval (-(1/2)) < 0 := by dsimp [P]; linarith
  obtain ⟨a,ha,ha0⟩ := polynomial_strict_sign_root (-P) (-80) (-10) (by norm_num)
    (by simpa using neg_neg_of_pos h80') (by simpa using neg_pos.mpr h10')
  obtain ⟨b,hb,hb0⟩ := polynomial_strict_sign_root P (-10) (-2) (by norm_num) h10' h2'
  obtain ⟨c,hc,hc0⟩ := polynomial_strict_sign_root (-P) (-2) (-(1/2)) (by norm_num)
    (by simpa using neg_neg_of_pos h2') (by simpa using neg_pos.mpr hh')
  obtain ⟨d,hd,hd0⟩ := polynomial_strict_sign_root P u v huv hleft hright
  refine ⟨a,b,c,d,ha,hb,hc,hd,?_⟩
  apply monic_quartic_factor_of_four_roots P (stationaryJacobian e p z).charpoly_monic
    (by simp [P,Matrix.charpoly_natDegree_eq_dim]) a b c d
    (ha.2.trans hb.1) (hb.2.trans hc.1) (hc.2.trans_le hu |>.trans hd.1)
    (by simpa using ha0) hb0 (by simpa using hc0) hd0

theorem middle_four_real_spectral_roots (e p z : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/50000) (hp : 0 ≤ p) (hpu : p ≤ 17/25000)
    (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ a b c d : ℝ, a ∈ Ioo (-80:ℝ) (-10) ∧ b ∈ Ioo (-10:ℝ) (-2) ∧
      c ∈ Ioo (-2:ℝ) (-(1/2)) ∧ d ∈ Ioo (0:ℝ) (1/10) ∧
      (stationaryJacobian e p z).charpoly = (X-C a)*(X-C b)*(X-C c)*(X-C d) := by
  have hw : z ∈ Icc (9/10:ℝ) (31/10) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hz0 : 0 < z+2 := by linarith [hz.1]
  have h0 := characteristic_sign_of_scaled e p z 0 (-1) hz0 (spectral_sign_middleZero e p z he heu hp hpu hz)
  have h1 := characteristic_sign_of_scaled e p z (1/10) 1 hz0 (spectral_sign_posTenth e p z he heu hp hpu hw)
  exact stationary_four_real_roots e p z 0 (1/10) he heu hp hpu hw (by norm_num) (by norm_num)
    (by linarith) (by simpa only [one_mul] using h1)

theorem outer_four_real_spectral_roots (e p z : ℝ)
    (he : 0 ≤ e) (heu : e ≤ 1/50000) (hp : 0 ≤ p) (hpu : p ≤ 17/25000)
    (hz : z ∈ Icc (9/10:ℝ) (11/10) ∨ z ∈ Icc (29/10:ℝ) (31/10)) :
    ∃ a b c d : ℝ, a ∈ Ioo (-80:ℝ) (-10) ∧ b ∈ Ioo (-10:ℝ) (-2) ∧
      c ∈ Ioo (-2:ℝ) (-(1/2)) ∧ d ∈ Ioo (-(1/2):ℝ) 0 ∧
      (stationaryJacobian e p z).charpoly = (X-C a)*(X-C b)*(X-C c)*(X-C d) := by
  have hw : z ∈ Icc (9/10:ℝ) (31/10) := by
    rcases hz with h | h <;> exact ⟨by linarith [h.1],by linarith [h.2]⟩
  have hz0 : 0 < z+2 := by linarith [hw.1]
  have h0s : 0 < (1:ℝ)*scaledCharacteristic e p z 0 := by
    rcases hz with h | h
    · exact spectral_sign_lowZero e p z he heu hp hpu h
    · exact spectral_sign_highZero e p z he heu hp hpu h
  have h0 := characteristic_sign_of_scaled e p z 0 1 hz0 h0s
  have hh := characteristic_sign_of_scaled e p z (-(1/2)) (-1) hz0
    (by simpa only [neg_div] using spectral_sign_negHalf e p z he heu hp hpu hw)
  exact stationary_four_real_roots e p z (-(1/2)) 0 he heu hp hpu hw le_rfl (by norm_num)
    (by linarith) (by simpa only [one_mul] using h0)

end CoreCouplingGlobal
