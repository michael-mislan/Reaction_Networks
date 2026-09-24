import proofs.TypeIIL.CyclicReduced
import proofs.TypeII3.Network.ArcReduction
import proofs.TypeII3.Network.CurrentPositivity

namespace TypeIIL

open TypeII3

/-- The canonical positive-gap Type II_l network after each of its two linear
unit chains in a sector has been compressed to a three-species arc. -/
structure CyclicArcData (l : ℕ) where
  next : Fin l ≃ Fin l
  next_singleCycle : IsSingleCycle next
  arc : Fin l → ArcRates
  fork : Fin l → ForkRates

structure CyclicArcState (l : ℕ) where
  P : Fin l → ℝ
  Q : Fin l → ℝ
  R : Fin l → ℝ

def PositiveCyclicArcState (x : CyclicArcState l) : Prop :=
  (∀ i, 0 < x.P i) ∧ (∀ i, 0 < x.Q i) ∧ (∀ i, 0 < x.R i)

noncomputable def cyclicForkCurrent (D : CyclicArcData l)
    (x : CyclicArcState l) (i : Fin l) : ℝ :=
  forkCurrent (D.fork i) (x.Q i) (x.P i) (x.R i)

/-- Sector `i` runs from `R (prev i)` through `P i,Q i`; the fork current at
`prev i` enters it and the fork current at `i` leaves it. -/
def IsCyclicArcStationary (D : CyclicArcData l) (x : CyclicArcState l) : Prop :=
  ∀ i, ArcSteady (D.arc i) (D.fork (D.next.symm i)).m
    (cyclicForkCurrent D x (D.next.symm i)) (cyclicForkCurrent D x i)
    (x.R (D.next.symm i)) (x.P i) (x.Q i)

noncomputable def reducedOfCyclicArc (D : CyclicArcData l) : CyclicReducedData l :=
  { next := D.next
    next_singleCycle := D.next_singleCycle
    q := fun i =>
      { A := (D.fork i).plus * arcQUp (D.arc i) (D.fork (D.next.symm i)).m
        B := 1 + (D.fork i).plus * arcQLocal (D.arc i)
        lam := (D.fork i).minus
        a := arcPUp (D.arc i) (D.fork (D.next.symm i)).m
        b := arcPLocal (D.arc i)
        e := arcRUp (D.arc (D.next i)) (D.fork i).m
        f := arcRLocal (D.arc (D.next i))
        m := (D.fork i).m
        A_pos := mul_pos (D.fork i).plus_pos
          (arc_coefficients_pos (D.arc i) (D.fork (D.next.symm i)).m_pos).2.2.1
        B_pos := add_pos_of_pos_of_nonneg zero_lt_one
          (le_of_lt (mul_pos (D.fork i).plus_pos
            (arc_coefficients_pos (D.arc i)
              (D.fork (D.next.symm i)).m_pos).2.2.2.1))
        lam_pos := (D.fork i).minus_pos
        a_pos := (arc_coefficients_pos (D.arc i)
          (D.fork (D.next.symm i)).m_pos).1
        b_pos := (arc_coefficients_pos (D.arc i)
          (D.fork (D.next.symm i)).m_pos).2.1
        e_pos := (arc_coefficients_pos (D.arc (D.next i))
          (D.fork i).m_pos).2.2.2.2.1
        f_pos := (arc_coefficients_pos (D.arc (D.next i))
          (D.fork i).m_pos).2.2.2.2.2
        m_pos := (D.fork i).m_pos }
    response_gain := fun i =>
      arcRLocal_lt_arcRUp (D.arc (D.next i)) (D.fork i).m_pos }

theorem cyclic_arc_currents_pos
    (D : CyclicArcData l) (x : CyclicArcState l)
    (hx : PositiveCyclicArcState x) (hstat : IsCyclicArcStationary D x) :
    ∀ i, 0 < cyclicForkCurrent D x i := by
  intro i
  have hs := hstat (D.next i)
  have hs' : ArcSteady (D.arc (D.next i)) (D.fork i).m
      (cyclicForkCurrent D x i) (cyclicForkCurrent D x (D.next i))
      (x.R i) (x.P (D.next i)) (x.Q (D.next i)) := by
    simpa only [Equiv.symm_apply_apply] using hs
  have h := fork_current_pos_of_arc (D.arc (D.next i)) (D.fork i).m_pos
    (hx.2.2 i) (hx.1 (D.next i)) (hx.2.1 (D.next i)) hs'
  exact h

theorem cyclic_arc_to_reduced_root
    (D : CyclicArcData l) (x : CyclicArcState l)
    (hstat : IsCyclicArcStationary D x) :
    IsCyclicReducedRoot (reducedOfCyclicArc D) (cyclicForkCurrent D x) := by
  intro i
  let dp := cyclicForkCurrent D x (D.next.symm i)
  let d := cyclicForkCurrent D x i
  let dn := cyclicForkCurrent D x (D.next i)
  have hsI := hstat i
  have hsN := hstat (D.next i)
  rcases arc_response (D.arc i) hsI with ⟨hRp, hP, hQ⟩
  rcases arc_response (D.arc (D.next i)) hsN with ⟨hR, hPN, hQN⟩
  have hd : d = (D.fork i).plus * x.Q i -
      (D.fork i).minus * x.P i * x.R i ^ (D.fork i).m := by rfl
  simp only [Equiv.symm_apply_apply] at hR
  change reducedF ((reducedOfCyclicArc D).q i) dp d dn = 0
  change x.P i = arcPUp (D.arc i) (D.fork (D.next.symm i)).m * dp +
    arcPLocal (D.arc i) * d at hP
  change x.Q i = arcQUp (D.arc i) (D.fork (D.next.symm i)).m * dp -
    arcQLocal (D.arc i) * d at hQ
  change x.R i = arcRUp (D.arc (D.next i)) (D.fork i).m * d +
    arcRLocal (D.arc (D.next i)) * dn at hR
  rw [hQ, hP, hR] at hd
  dsimp [reducedOfCyclicArc, reducedF]
  linear_combination -hd

theorem cyclic_arc_state_eq_of_currents_eq
    (D : CyclicArcData l) (x y : CyclicArcState l)
    (hxstat : IsCyclicArcStationary D x)
    (hystat : IsCyclicArcStationary D y)
    (hcur : cyclicForkCurrent D x = cyclicForkCurrent D y) : x = y := by
  have hP : x.P = y.P := by
    funext i
    have hx := (arc_response (D.arc i) (hxstat i)).2.1
    have hy := (arc_response (D.arc i) (hystat i)).2.1
    rw [hcur] at hx
    exact hx.trans hy.symm
  have hQ : x.Q = y.Q := by
    funext i
    have hx := (arc_response (D.arc i) (hxstat i)).2.2
    have hy := (arc_response (D.arc i) (hystat i)).2.2
    rw [hcur] at hx
    exact hx.trans hy.symm
  have hR : x.R = y.R := by
    funext i
    have hx := (arc_response (D.arc (D.next i)) (hxstat (D.next i))).1
    have hy := (arc_response (D.arc (D.next i)) (hystat (D.next i))).1
    simp only [Equiv.symm_apply_apply] at hx hy
    rw [hcur] at hx
    exact hx.trans hy.symm
  cases x
  cases y
  simp_all

/-- Unistationarity of the canonical arbitrary-l positive-gap arc model. -/
theorem cyclic_arc_unistationarity [NeZero l]
    (D : CyclicArcData l) (x y : CyclicArcState l)
    (hx : PositiveCyclicArcState x) (hy : PositiveCyclicArcState y)
    (hxstat : IsCyclicArcStationary D x)
    (hystat : IsCyclicArcStationary D y) : x = y := by
  have hdx := cyclic_arc_currents_pos D x hx hxstat
  have hdy := cyclic_arc_currents_pos D y hy hystat
  have hrx := cyclic_arc_to_reduced_root D x hxstat
  have hry := cyclic_arc_to_reduced_root D y hystat
  have hcur := cyclic_reduced_unistationarity (reducedOfCyclicArc D)
    (cyclicForkCurrent D x) (cyclicForkCurrent D y) hdx hdy hrx hry
  exact cyclic_arc_state_eq_of_currents_eq D x y hxstat hystat hcur

end TypeIIL
