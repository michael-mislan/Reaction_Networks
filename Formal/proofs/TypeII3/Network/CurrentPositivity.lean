import proofs.TypeII3.Network.Canonical

namespace TypeII3

theorem fork_current_pos_of_arc
    (a : ArcRates) {m : ℕ} {delta deltaNext R P Q : ℝ}
    (hm : 0 < m) (hRpos : 0 < R) (hPpos : 0 < P) (hQpos : 0 < Q)
    (hsteady : ArcSteady a m delta deltaNext R P Q) :
    0 < delta := by
  rcases hsteady with ⟨hR, hP, hQ⟩
  have hsum :
      (m : ℝ) * delta = a.dR * R + a.dP * P + a.dQ * Q := by
    linear_combination hR + hP + hQ
  have hprod : 0 < (m : ℝ) * delta := by
    rw [hsum]
    exact add_pos (add_pos (mul_pos a.dR_pos hRpos) (mul_pos a.dP_pos hPpos))
      (mul_pos a.dQ_pos hQpos)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rcases (mul_pos_iff.mp hprod) with h | h
  · exact h.2
  · nlinarith [hmR, h.1]

theorem canonical_currents_pos
    (p : CanonicalParams) (x : CanonicalState)
    (hx : PositiveCanonicalState x)
    (hstat : IsCanonicalStationary p x) :
    0 < forkCurrent p.fork0 x.Q0 x.P0 x.R0 ∧
    0 < forkCurrent p.fork1 x.Q1 x.P1 x.R1 ∧
    0 < forkCurrent p.fork2 x.Q2 x.P2 x.R2 := by
  rcases hx with ⟨hP0, hQ0, hR0, hP1, hQ1, hR1, hP2, hQ2, hR2⟩
  simp only [IsCanonicalStationary] at hstat
  rcases hstat with ⟨hs0, hs1, hs2⟩
  have hd0 := fork_current_pos_of_arc p.arc1 p.fork0.m_pos hR0 hP1 hQ1 hs1
  have hd1 := fork_current_pos_of_arc p.arc2 p.fork1.m_pos hR1 hP2 hQ2 hs2
  have hd2 := fork_current_pos_of_arc p.arc0 p.fork2.m_pos hR2 hP0 hQ0 hs0
  exact ⟨hd0, hd1, hd2⟩

end TypeII3
