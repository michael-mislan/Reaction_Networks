import Mathlib

namespace DisguisedToricAssemblies

/-- A balanced circulation annihilates every vertex potential difference. -/
theorem circulation_potential {I : Type*} [Fintype I]
    (q : I → I → ℝ) (P : I → ℝ)
    (hb : ∀ i, ∑ j, q i j = ∑ j, q j i) :
    (∑ i, ∑ j, q i j*(P j-P i)) = 0 := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have he : (∑ i, ∑ j, q i j*P j) = ∑ i, ∑ j, q i j*P i := by
    calc
      (∑ i, ∑ j, q i j*P j) = ∑ j, (∑ i, q i j)*P j := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
      _ = ∑ j, (∑ i, q j i)*P j := by simp_rw [← hb]
      _ = _ := by simp_rw [Finset.sum_mul]
  linarith

/-- Supporting affine functions give obstructions on any finite auxiliary graph,
including vertices with zero coefficient drift outside the original support. -/
theorem supporting_dual_nonneg {I S : Type*} [Fintype I] [Fintype S]
    (q : I → I → ℝ) (y h r : I → S → ℝ) (P : I → ℝ)
    (hq : ∀ i j, 0 ≤ q i j)
    (hb : ∀ i, ∑ j, q i j = ∑ j, q j i)
    (hd : ∀ i k, ∑ j, q i j*(y j k-y i k) = r i k)
    (hp : ∀ i j, 0 ≤ (∑ k, h i k*(y j k-y i k))+P j-P i) :
    0 ≤ ∑ i, ∑ k, h i k*r i k := by
  have hn : 0 ≤ ∑ i, ∑ j, q i j*((∑ k, h i k*(y j k-y i k))+P j-P i) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => mul_nonneg (hq i j) (hp i j)))
  have he : (∑ i, ∑ k, h i k*r i k) =
      ∑ i, ∑ j, q i j*(∑ k, h i k*(y j k-y i k)) := by
    simp_rw [← hd, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hz := circulation_potential q P hb
  have hs : (∑ i, ∑ j, q i j*((∑ k, h i k*(y j k-y i k))+P j-P i)) =
      (∑ i, ∑ j, q i j*(∑ k, h i k*(y j k-y i k))) +
      ∑ i, ∑ j, q i j*(P j-P i) := by
    simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  rw [hs, hz, add_zero, ← he] at hn
  exact hn

/-- Extend finitely many consistent supporting planes to any extra vertices.
The prescribed slope at every original vertex is retained, including ties. -/
theorem complete_supports {T S E : Type*} [Fintype T] [Nonempty T] [Fintype S]
    (y h : T → S → ℝ) (p : T → ℝ) (z : E → S → ℝ)
    (hs : ∀ i j, 0 ≤ (∑ k, h i k*(y j k-y i k))+p j-p i) :
    ∃ H : T ⊕ E → S → ℝ, ∃ P : T ⊕ E → ℝ,
      (∀ i, H (.inl i) = h i ∧ P (.inl i) = p i) ∧
      ∀ u v, 0 ≤ (∑ k, H u k*((Sum.elim y z v) k-(Sum.elim y z u) k))+P v-P u := by
  classical
  let f : T → (S → ℝ) → ℝ := fun i w => p i-∑ k, h i k*(w k-y i k)
  have hex : ∀ w : S → ℝ, ∃ i : T, ∀ j : T, f j w ≤ f i w := by
    intro w
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => f i w)
      Finset.univ_nonempty
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  choose g hg using hex
  let sel : T ⊕ E → T := Sum.elim id (fun j => g (z j))
  let Y : T ⊕ E → S → ℝ := Sum.elim y z
  have hself : ∀ i, f i (y i) = p i := by intro i; simp [f]
  have hmax : ∀ u, ∀ j, f j (Y u) ≤ f (sel u) (Y u) := by
    intro u j
    cases u with
    | inl i =>
      change f j (y i) ≤ f i (y i)
      rw [hself]
      have hi := hs j i
      dsimp [f]
      linarith
    | inr i => exact hg (z i) j
  refine ⟨fun u => h (sel u), fun u => f (sel u) (Y u), ?_, ?_⟩
  · intro i
    exact ⟨rfl, hself i⟩
  · intro u v
    have hm := hmax v (sel u)
    have hf : f (sel u) (Y v)-f (sel u) (Y u) =
        -(∑ k, h (sel u) k*(Y v k-Y u k)) := by
      dsimp [f]
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      ring
    change 0 ≤ (∑ k, h (sel u) k*(Y v k-Y u k))+f (sel v) (Y v)-f (sel u) (Y u)
    linarith

end DisguisedToricAssemblies
