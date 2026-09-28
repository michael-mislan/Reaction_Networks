import proofs.DStabilityLocalization.Boundary

/-!
# Channelwise induction and localization of non-real eigenvalues

Applying the exit lemma at a fixed non-real `z` with `Re z ≥ 0` to the channels one at a time
(any order) turns a generalized contact into one whose configuration is of boundary type in
every channel; no stability of any intermediate core is used.  Hence every such eigenvalue of a
positive scaling of a star is the same eigenvalue of a positive scaling of one of its boundary
systems.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Matrix Complex Set
open scoped BigOperators

namespace DStabilityLocalization
open DUnstableCores

variable {ι κ C : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype C] [DecidableEq C]

/-- **Channel induction.** Every generalized contact at `z` yields one of boundary type in every
channel, after a dilation of the core inverse rates. -/
theorem localize_all {z : ℂ} (hre : 0 ≤ z.re) (hz : z.im ≠ 0)
    (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ)
    (hr : ∀ p, r p ≠ 0) (q : ι → ℝ) (hq : ∀ i, 0 < q i) (s : κ → ℝ)
    (hs : ∀ p, s p ∈ Icc (0 : ℝ) 1) (hcon : (pencil B u v q (chanVal z ch r s) z).det = 0) :
    ∃ q' : ι → ℝ, (∀ i, 0 < q' i) ∧ ∃ s' : κ → ℝ, (∀ p, s' p ∈ Icc (0 : ℝ) 1) ∧
      (∀ c, BoundaryType ch s' c) ∧ (pencil B u v q' (chanVal z ch r s') z).det = 0 := by
  have key : ∀ T : Finset C, ∃ q' : ι → ℝ, (∀ i, 0 < q' i) ∧ ∃ s' : κ → ℝ,
      (∀ p, s' p ∈ Icc (0 : ℝ) 1) ∧ (∀ c ∈ T, BoundaryType ch s' c) ∧
      (pencil B u v q' (chanVal z ch r s') z).det = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨q, hq, s, hs, by simp, hcon⟩
    | @insert c T hcT ih =>
      obtain ⟨q', hq', s', hs', hbT, hcon'⟩ := ih
      obtain ⟨τ, hτ, s'', hs'', hoff, hbc, hcon''⟩ :=
        exit_channel hre hz B u v ch r hr c q' hq' s' hs' hcon'
      refine ⟨fun i => τ * q' i, fun i => mul_pos (by linarith) (hq' i), s'', hs'', ?_,
        hcon''⟩
      intro c' hc'
      rcases Finset.mem_insert.mp hc' with rfl | hc'T
      · exact hbc
      · have hne : c' ≠ c := fun h => hcT (h ▸ hc'T)
        intro p p' hp hp' h1 h2 h3 h4
        have e1 : s'' p = s' p := hoff p (by rw [hp]; exact hne)
        have e2 : s'' p' = s' p' := hoff p' (by rw [hp']; exact hne)
        rw [e1] at h1 h2
        rw [e2] at h3 h4
        rw [e1, e2]
        exact hbT c' hc'T p p' hp hp' h1 h2 h3 h4
  obtain ⟨q', hq', s', hs', hb, hcon'⟩ := key Finset.univ
  exact ⟨q', hq', s', hs', fun c => hb c (Finset.mem_univ c), hcon'⟩

theorem lagValue_eq_chanVal {z : ℂ} (hre : 0 ≤ z.re) (ch : κ → C) (r t : κ → ℝ)
    (ht : ∀ p, 0 < t p) :
    lagValue ch r t z = chanVal z ch r (fun p => t p / (1 + t p)) := by
  funext c
  unfold lagValue chanVal
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs
  · rw [← lag_eq_val hre _ (ht p)]
    ring
  · rfl

/-- **Localization of non-real eigenvalues.** If a positive scaling of the star has a non-real
eigenvalue `z` with `Re z ≥ 0`, then some boundary system has the same eigenvalue `z` at a
positive scaling.  No stability hypothesis on the core is needed. -/
theorem localization_nonreal (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C)
    (r : κ → ℝ) (hr : ∀ p, r p ≠ 0) (d : ι ⊕ κ → ℝ) (hd : ∀ a, 0 < d a) {z : ℂ}
    (hre : 0 ≤ z.re) (hz : z.im ≠ 0) (y : ι ⊕ κ → ℂ)
    (hy : HasEigenpair (rightScale (star B u v ch r) d) z y) :
    ∃ σ : κ → Role, ∃ d' : ι ⊕ C → ℝ, (∀ a, 0 < d' a) ∧ ∃ y',
      HasEigenpair (rightScale (bdSystem B u v ch r σ) d') z y' := by
  set t : κ → ℝ := fun p => (d (.inr p))⁻¹
  have ht : ∀ p, 0 < t p := fun p => inv_pos.mpr (hd _)
  have hz1 : ∀ p, 1 + z * ((d (.inr p))⁻¹ : ℝ) ≠ 0 := fun p => one_add_mul_ne hre (ht p).le
  obtain ⟨x, hx, hker⟩ := pencil_kernel_of_eigenpair B u v ch r d hd _ y hy hz1
  have hdet : (pencil B u v (fun i => (d (.inl i))⁻¹) (lagValue ch r t z) z).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hker⟩
  rw [lagValue_eq_chanVal hre ch r t ht] at hdet
  have hs : ∀ p, t p / (1 + t p) ∈ Icc (0 : ℝ) 1 := by
    intro p
    have h0 := ht p
    constructor
    · positivity
    · rw [div_le_one (by linarith)]; linarith
  obtain ⟨q', hq', s', hs', hb, hcon⟩ := localize_all hre hz B u v ch r hr _
    (fun i => inv_pos.mpr (hd _)) _ hs hdet
  obtain ⟨y', hy'⟩ := boundary_eigenpair hre B u v ch r q' hq' s' hs' hb hcon
  refine ⟨roleOf s', _, fun a => ?_, y', hy'⟩
  rcases a with i | c
  · exact inv_pos.mpr (hq' i)
  · exact inv_pos.mpr (groupRate_pos ch s' c)

end DStabilityLocalization
