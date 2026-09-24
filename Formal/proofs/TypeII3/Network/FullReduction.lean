import proofs.TypeII3.Network.ArcReduction
import proofs.TypeII3.Network.CurrentPositivity
import proofs.TypeII3.Reduced.Unistationarity

namespace TypeII3

theorem arcPUp_pos (a : ArcRates) {m : ℕ} (hm : 0 < m) : 0 < arcPUp a m :=
  (arc_coefficients_pos a hm).1

theorem arcPLocal_pos (a : ArcRates) {m : ℕ} (hm : 0 < m) : 0 < arcPLocal a :=
  (arc_coefficients_pos a hm).2.1

theorem arcQUp_pos (a : ArcRates) {m : ℕ} (hm : 0 < m) : 0 < arcQUp a m :=
  (arc_coefficients_pos a hm).2.2.1

theorem arcQLocal_pos (a : ArcRates) {m : ℕ} (hm : 0 < m) : 0 < arcQLocal a :=
  (arc_coefficients_pos a hm).2.2.2.1

theorem arcRUp_pos (a : ArcRates) {m : ℕ} (hm : 0 < m) : 0 < arcRUp a m :=
  (arc_coefficients_pos a hm).2.2.2.2.1

theorem arcRLocal_pos (a : ArcRates) {m : ℕ} (hm : 0 < m) : 0 < arcRLocal a :=
  (arc_coefficients_pos a hm).2.2.2.2.2

noncomputable def reducedParamsOfCanonical (p : CanonicalParams) : ReducedParams :=
  {
    q0 := {
      A := p.fork0.plus * arcQUp p.arc0 p.fork2.m
      B := 1 + p.fork0.plus * arcQLocal p.arc0
      lam := p.fork0.minus
      a := arcPUp p.arc0 p.fork2.m
      b := arcPLocal p.arc0
      e := arcRUp p.arc1 p.fork0.m
      f := arcRLocal p.arc1
      m := p.fork0.m
      A_pos := mul_pos p.fork0.plus_pos (arcQUp_pos p.arc0 p.fork2.m_pos)
      B_pos := add_pos_of_pos_of_nonneg zero_lt_one
        (le_of_lt (mul_pos p.fork0.plus_pos (arcQLocal_pos p.arc0 p.fork2.m_pos)))
      lam_pos := p.fork0.minus_pos
      a_pos := arcPUp_pos p.arc0 p.fork2.m_pos
      b_pos := arcPLocal_pos p.arc0 p.fork2.m_pos
      e_pos := arcRUp_pos p.arc1 p.fork0.m_pos
      f_pos := arcRLocal_pos p.arc1 p.fork0.m_pos
      m_pos := p.fork0.m_pos }
    q1 := {
      A := p.fork1.plus * arcQUp p.arc1 p.fork0.m
      B := 1 + p.fork1.plus * arcQLocal p.arc1
      lam := p.fork1.minus
      a := arcPUp p.arc1 p.fork0.m
      b := arcPLocal p.arc1
      e := arcRUp p.arc2 p.fork1.m
      f := arcRLocal p.arc2
      m := p.fork1.m
      A_pos := mul_pos p.fork1.plus_pos (arcQUp_pos p.arc1 p.fork0.m_pos)
      B_pos := add_pos_of_pos_of_nonneg zero_lt_one
        (le_of_lt (mul_pos p.fork1.plus_pos (arcQLocal_pos p.arc1 p.fork0.m_pos)))
      lam_pos := p.fork1.minus_pos
      a_pos := arcPUp_pos p.arc1 p.fork0.m_pos
      b_pos := arcPLocal_pos p.arc1 p.fork0.m_pos
      e_pos := arcRUp_pos p.arc2 p.fork1.m_pos
      f_pos := arcRLocal_pos p.arc2 p.fork1.m_pos
      m_pos := p.fork1.m_pos }
    q2 := {
      A := p.fork2.plus * arcQUp p.arc2 p.fork1.m
      B := 1 + p.fork2.plus * arcQLocal p.arc2
      lam := p.fork2.minus
      a := arcPUp p.arc2 p.fork1.m
      b := arcPLocal p.arc2
      e := arcRUp p.arc0 p.fork2.m
      f := arcRLocal p.arc0
      m := p.fork2.m
      A_pos := mul_pos p.fork2.plus_pos (arcQUp_pos p.arc2 p.fork1.m_pos)
      B_pos := add_pos_of_pos_of_nonneg zero_lt_one
        (le_of_lt (mul_pos p.fork2.plus_pos (arcQLocal_pos p.arc2 p.fork1.m_pos)))
      lam_pos := p.fork2.minus_pos
      a_pos := arcPUp_pos p.arc2 p.fork1.m_pos
      b_pos := arcPLocal_pos p.arc2 p.fork1.m_pos
      e_pos := arcRUp_pos p.arc0 p.fork2.m_pos
      f_pos := arcRLocal_pos p.arc0 p.fork2.m_pos
      m_pos := p.fork2.m_pos }
  }

theorem canonical_to_reduced_root
    (p : CanonicalParams) (x : CanonicalState)
    (hstat : IsCanonicalStationary p x) :
    IsReducedRoot (reducedParamsOfCanonical p)
      (forkCurrent p.fork0 x.Q0 x.P0 x.R0)
      (forkCurrent p.fork1 x.Q1 x.P1 x.R1)
      (forkCurrent p.fork2 x.Q2 x.P2 x.R2) := by
  let d0 := forkCurrent p.fork0 x.Q0 x.P0 x.R0
  let d1 := forkCurrent p.fork1 x.Q1 x.P1 x.R1
  let d2 := forkCurrent p.fork2 x.Q2 x.P2 x.R2
  change
    ArcSteady p.arc0 p.fork2.m d2 d0 x.R2 x.P0 x.Q0 ∧
    ArcSteady p.arc1 p.fork0.m d0 d1 x.R0 x.P1 x.Q1 ∧
    ArcSteady p.arc2 p.fork1.m d1 d2 x.R1 x.P2 x.Q2 at hstat
  rcases hstat with ⟨hs0, hs1, hs2⟩
  rcases arc_response p.arc0 hs0 with ⟨hR2, hP0, hQ0⟩
  rcases arc_response p.arc1 hs1 with ⟨hR0, hP1, hQ1⟩
  rcases arc_response p.arc2 hs2 with ⟨hR1, hP2, hQ2⟩
  change IsReducedRoot (reducedParamsOfCanonical p) d0 d1 d2
  have hd0 : d0 = p.fork0.plus * x.Q0 - p.fork0.minus * x.P0 * x.R0 ^ p.fork0.m := by
    rfl
  have hd1 : d1 = p.fork1.plus * x.Q1 - p.fork1.minus * x.P1 * x.R1 ^ p.fork1.m := by
    rfl
  have hd2 : d2 = p.fork2.plus * x.Q2 - p.fork2.minus * x.P2 * x.R2 ^ p.fork2.m := by
    rfl
  rw [hQ0, hP0, hR0] at hd0
  rw [hQ1, hP1, hR1] at hd1
  rw [hQ2, hP2, hR2] at hd2
  constructor
  · dsimp [IsReducedRoot, reducedF, reducedParamsOfCanonical]
    linear_combination -hd0
  constructor
  · dsimp [IsReducedRoot, reducedF, reducedParamsOfCanonical]
    linear_combination -hd1
  · dsimp [IsReducedRoot, reducedF, reducedParamsOfCanonical]
    linear_combination -hd2

theorem canonical_state_eq_of_currents_eq
    (p : CanonicalParams) (x y : CanonicalState)
    (hxstat : IsCanonicalStationary p x)
    (hystat : IsCanonicalStationary p y)
    (h0 : forkCurrent p.fork0 x.Q0 x.P0 x.R0 =
      forkCurrent p.fork0 y.Q0 y.P0 y.R0)
    (h1 : forkCurrent p.fork1 x.Q1 x.P1 x.R1 =
      forkCurrent p.fork1 y.Q1 y.P1 y.R1)
    (h2 : forkCurrent p.fork2 x.Q2 x.P2 x.R2 =
      forkCurrent p.fork2 y.Q2 y.P2 y.R2) :
    x = y := by
  simp only [IsCanonicalStationary] at hxstat hystat
  rcases hxstat with ⟨hxs0, hxs1, hxs2⟩
  rcases hystat with ⟨hys0, hys1, hys2⟩
  rcases arc_response p.arc0 hxs0 with ⟨hxR2, hxP0, hxQ0⟩
  rcases arc_response p.arc1 hxs1 with ⟨hxR0, hxP1, hxQ1⟩
  rcases arc_response p.arc2 hxs2 with ⟨hxR1, hxP2, hxQ2⟩
  rcases arc_response p.arc0 hys0 with ⟨hyR2, hyP0, hyQ0⟩
  rcases arc_response p.arc1 hys1 with ⟨hyR0, hyP1, hyQ1⟩
  rcases arc_response p.arc2 hys2 with ⟨hyR1, hyP2, hyQ2⟩
  have eP0 : x.P0 = y.P0 := by
    calc
      x.P0 = arcPUp p.arc0 p.fork2.m * forkCurrent p.fork2 x.Q2 x.P2 x.R2 +
          arcPLocal p.arc0 * forkCurrent p.fork0 x.Q0 x.P0 x.R0 := hxP0
      _ = arcPUp p.arc0 p.fork2.m * forkCurrent p.fork2 y.Q2 y.P2 y.R2 +
          arcPLocal p.arc0 * forkCurrent p.fork0 y.Q0 y.P0 y.R0 := by rw [h0, h2]
      _ = y.P0 := hyP0.symm
  have eQ0 : x.Q0 = y.Q0 := by
    calc
      x.Q0 = arcQUp p.arc0 p.fork2.m * forkCurrent p.fork2 x.Q2 x.P2 x.R2 -
          arcQLocal p.arc0 * forkCurrent p.fork0 x.Q0 x.P0 x.R0 := hxQ0
      _ = arcQUp p.arc0 p.fork2.m * forkCurrent p.fork2 y.Q2 y.P2 y.R2 -
          arcQLocal p.arc0 * forkCurrent p.fork0 y.Q0 y.P0 y.R0 := by rw [h0, h2]
      _ = y.Q0 := hyQ0.symm
  have eR0 : x.R0 = y.R0 := by
    calc
      x.R0 = arcRUp p.arc1 p.fork0.m * forkCurrent p.fork0 x.Q0 x.P0 x.R0 +
          arcRLocal p.arc1 * forkCurrent p.fork1 x.Q1 x.P1 x.R1 := hxR0
      _ = arcRUp p.arc1 p.fork0.m * forkCurrent p.fork0 y.Q0 y.P0 y.R0 +
          arcRLocal p.arc1 * forkCurrent p.fork1 y.Q1 y.P1 y.R1 := by rw [h0, h1]
      _ = y.R0 := hyR0.symm
  have eP1 : x.P1 = y.P1 := by
    calc
      x.P1 = arcPUp p.arc1 p.fork0.m * forkCurrent p.fork0 x.Q0 x.P0 x.R0 +
          arcPLocal p.arc1 * forkCurrent p.fork1 x.Q1 x.P1 x.R1 := hxP1
      _ = arcPUp p.arc1 p.fork0.m * forkCurrent p.fork0 y.Q0 y.P0 y.R0 +
          arcPLocal p.arc1 * forkCurrent p.fork1 y.Q1 y.P1 y.R1 := by rw [h0, h1]
      _ = y.P1 := hyP1.symm
  have eQ1 : x.Q1 = y.Q1 := by
    calc
      x.Q1 = arcQUp p.arc1 p.fork0.m * forkCurrent p.fork0 x.Q0 x.P0 x.R0 -
          arcQLocal p.arc1 * forkCurrent p.fork1 x.Q1 x.P1 x.R1 := hxQ1
      _ = arcQUp p.arc1 p.fork0.m * forkCurrent p.fork0 y.Q0 y.P0 y.R0 -
          arcQLocal p.arc1 * forkCurrent p.fork1 y.Q1 y.P1 y.R1 := by rw [h0, h1]
      _ = y.Q1 := hyQ1.symm
  have eR1 : x.R1 = y.R1 := by
    calc
      x.R1 = arcRUp p.arc2 p.fork1.m * forkCurrent p.fork1 x.Q1 x.P1 x.R1 +
          arcRLocal p.arc2 * forkCurrent p.fork2 x.Q2 x.P2 x.R2 := hxR1
      _ = arcRUp p.arc2 p.fork1.m * forkCurrent p.fork1 y.Q1 y.P1 y.R1 +
          arcRLocal p.arc2 * forkCurrent p.fork2 y.Q2 y.P2 y.R2 := by rw [h1, h2]
      _ = y.R1 := hyR1.symm
  have eP2 : x.P2 = y.P2 := by
    calc
      x.P2 = arcPUp p.arc2 p.fork1.m * forkCurrent p.fork1 x.Q1 x.P1 x.R1 +
          arcPLocal p.arc2 * forkCurrent p.fork2 x.Q2 x.P2 x.R2 := hxP2
      _ = arcPUp p.arc2 p.fork1.m * forkCurrent p.fork1 y.Q1 y.P1 y.R1 +
          arcPLocal p.arc2 * forkCurrent p.fork2 y.Q2 y.P2 y.R2 := by rw [h1, h2]
      _ = y.P2 := hyP2.symm
  have eQ2 : x.Q2 = y.Q2 := by
    calc
      x.Q2 = arcQUp p.arc2 p.fork1.m * forkCurrent p.fork1 x.Q1 x.P1 x.R1 -
          arcQLocal p.arc2 * forkCurrent p.fork2 x.Q2 x.P2 x.R2 := hxQ2
      _ = arcQUp p.arc2 p.fork1.m * forkCurrent p.fork1 y.Q1 y.P1 y.R1 -
          arcQLocal p.arc2 * forkCurrent p.fork2 y.Q2 y.P2 y.R2 := by rw [h1, h2]
      _ = y.Q2 := hyQ2.symm
  have eR2 : x.R2 = y.R2 := by
    calc
      x.R2 = arcRUp p.arc0 p.fork2.m * forkCurrent p.fork2 x.Q2 x.P2 x.R2 +
          arcRLocal p.arc0 * forkCurrent p.fork0 x.Q0 x.P0 x.R0 := hxR2
      _ = arcRUp p.arc0 p.fork2.m * forkCurrent p.fork2 y.Q2 y.P2 y.R2 +
          arcRLocal p.arc0 * forkCurrent p.fork0 y.Q0 y.P0 y.R0 := by rw [h0, h2]
      _ = y.R2 := hyR2.symm
  apply CanonicalState.ext
  all_goals assumption

theorem canonical_unistationarity
    (p : CanonicalParams) (x y : CanonicalState)
    (hx : PositiveCanonicalState x) (hy : PositiveCanonicalState y)
    (hxstat : IsCanonicalStationary p x)
    (hystat : IsCanonicalStationary p y) :
    x = y := by
  rcases canonical_currents_pos p x hx hxstat with ⟨hxd0, hxd1, hxd2⟩
  rcases canonical_currents_pos p y hy hystat with ⟨hyd0, hyd1, hyd2⟩
  have hrootX := canonical_to_reduced_root p x hxstat
  have hrootY := canonical_to_reduced_root p y hystat
  have hcurr := reduced_unistationarity (reducedParamsOfCanonical p)
    ⟨hxd0, hxd1, hxd2⟩ ⟨hyd0, hyd1, hyd2⟩ hrootX hrootY
  exact canonical_state_eq_of_currents_eq p x y hxstat hystat hcurr.1 hcurr.2.1 hcurr.2.2

end TypeII3
