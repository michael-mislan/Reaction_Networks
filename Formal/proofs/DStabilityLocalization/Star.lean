import proofs.DUnstableCores.DScaling

/-!
# T-LOC: attachment stars with several interface channels

A core `B : Matrix ι ι ℝ`, channels `c : C` with interface vectors `u c, v c`, and pieces
`p : κ` with channel `ch p` and load `r p`.  Piece `p` obeys `ẇ_p = d_p (v_{ch p}ᵀ x − w_p)`
and feeds `r_p u_{ch p} w_p` into the core.  Eliminating the pieces at an eigenvalue `z`
(with `1 + z t_p ≠ 0`) leaves the reduced pencil `z Q − B − Σ_c ℓ_c u_c v_cᵀ`
(the contact equation, node N1 of the campaign).
-/

set_option linter.unusedSectionVars false

noncomputable section
open Matrix Complex
open scoped BigOperators

namespace DStabilityLocalization
open DUnstableCores

variable {ι κ C : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype C] [DecidableEq C]

/-- The attachment star with channels. -/
def star (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ
  | .inl i, .inl j => B i j
  | .inl i, .inr p => r p * u (ch p) i
  | .inr p, .inl j => v (ch p) j
  | .inr p, .inr q => if p = q then -1 else 0

/-- Channel value at the eigenvalue `z` with piece inverse rates `t`. -/
def lagValue (ch : κ → C) (r t : κ → ℝ) (z : ℂ) (c : C) : ℂ :=
  ∑ p, if ch p = c then (r p : ℂ) / (1 + z * t p) else 0

/-- The reduced pencil `z Q − B − Σ_c ℓ_c u_c v_cᵀ`. -/
def pencil (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (q : ι → ℝ) (ℓ : C → ℂ) (z : ℂ) :
    Matrix ι ι ℂ :=
  fun i j => (if i = j then z * q i else 0) - B i j - ∑ c, ℓ c * u c i * v c j

theorem star_mulVec_inl (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ)
    (d : ι ⊕ κ → ℝ) (y : ι ⊕ κ → ℂ) (i : ι) :
    (complexify (rightScale (star B u v ch r) d) *ᵥ y) (.inl i) =
      (∑ j, (B i j : ℂ) * ((d (.inl j) : ℂ) * y (.inl j))) +
      ∑ p, (r p : ℂ) * u (ch p) i * ((d (.inr p) : ℂ) * y (.inr p)) := by
  simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Fintype.sum_sum_type, star,
    Complex.ofReal_mul, mul_assoc]

theorem star_mulVec_inr (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ)
    (d : ι ⊕ κ → ℝ) (y : ι ⊕ κ → ℂ) (p : κ) :
    (complexify (rightScale (star B u v ch r) d) *ᵥ y) (.inr p) =
      (∑ j, (v (ch p) j : ℂ) * ((d (.inl j) : ℂ) * y (.inl j))) -
      (d (.inr p) : ℂ) * y (.inr p) := by
  simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Fintype.sum_sum_type, star,
    Complex.ofReal_mul, mul_assoc]
  simp [apply_ite (fun a : ℝ => (a : ℂ)), ite_mul, sub_eq_add_neg]

theorem pencil_mulVec (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (q : ι → ℝ) (ℓ : C → ℂ)
    (z : ℂ) (x : ι → ℂ) (i : ι) :
    (pencil B u v q ℓ z *ᵥ x) i =
      z * q i * x i - (∑ j, (B i j : ℂ) * x j) -
        ∑ c, ℓ c * u c i * ∑ j, (v c j : ℂ) * x j := by
  simp only [pencil, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- Regrouping the piece feedback by channel. -/
theorem sum_pieces_by_channel (ch : κ → C) (r t : κ → ℝ) (z : ℂ) (u : C → ι → ℝ)
    (i : ι) (a : C → ℂ) :
    (∑ p, (r p : ℂ) * u (ch p) i * (a (ch p) / (1 + z * t p))) =
      ∑ c, lagValue ch r t z c * u c i * a c := by
  have : ∀ p, (r p : ℂ) * u (ch p) i * (a (ch p) / (1 + z * t p)) =
      ∑ c, if ch p = c then (r p : ℂ) / (1 + z * t p) * u c i * a c else 0 := by
    intro p
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    ring
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [lagValue, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> simp

/-- Elimination (Lemma 1.1, forward): an eigenpair of a positive scaling of the star at an
eigenvalue with `1 + z t_p ≠ 0` gives a nonzero kernel vector of the reduced pencil. -/
theorem pencil_kernel_of_eigenpair (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C)
    (r : κ → ℝ) (d : ι ⊕ κ → ℝ) (hd : ∀ i, 0 < d i) (z : ℂ) (y : ι ⊕ κ → ℂ)
    (hy : HasEigenpair (rightScale (star B u v ch r) d) z y)
    (hz : ∀ p, 1 + z * ((d (.inr p))⁻¹ : ℝ) ≠ 0) :
    ∃ x : ι → ℂ, x ≠ 0 ∧
      pencil B u v (fun i => (d (.inl i))⁻¹)
        (lagValue ch r (fun p => (d (.inr p))⁻¹) z) z *ᵥ x = 0 := by
  have hdn (a : ι ⊕ κ) : (d a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd a))
  have hinv (a : ι ⊕ κ) : (((d a)⁻¹ : ℝ) : ℂ) * (d a : ℂ) = 1 := by
    push_cast; field_simp [hdn a]
  let x : ι → ℂ := fun i => (d (.inl i) : ℂ) * y (.inl i)
  let w : κ → ℂ := fun p => (d (.inr p) : ℂ) * y (.inr p)
  have hrow_piece : ∀ p, (∑ j, (v (ch p) j : ℂ) * x j) - w p =
      z * ((d (.inr p))⁻¹ : ℝ) * w p := by
    intro p
    have h := hy.2 (.inr p)
    rw [star_mulVec_inr] at h
    have := hinv (.inr p)
    simp only [x, w]
    linear_combination h - z * y (.inr p) * this
  have hw : ∀ p, w p = (∑ j, (v (ch p) j : ℂ) * x j) / (1 + z * ((d (.inr p))⁻¹ : ℝ)) := by
    intro p
    rw [eq_div_iff (hz p)]
    linear_combination (hrow_piece p).symm
  have hx : x ≠ 0 := by
    intro h0
    apply hy.1
    funext a
    cases a with
    | inl i =>
      have := congrFun h0 i
      simp only [x, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left (hdn _)
    | inr p =>
      have hwp := hw p
      simp only [h0, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_div] at hwp
      simp only [w] at hwp
      exact (mul_eq_zero.mp hwp).resolve_left (hdn _)
  refine ⟨x, hx, ?_⟩
  funext i
  have h := hy.2 (.inl i)
  rw [star_mulVec_inl] at h
  have e2 : ∀ p, (r p : ℂ) * u (ch p) i * ((d (.inr p) : ℂ) * y (.inr p)) =
      (r p : ℂ) * u (ch p) i * ((∑ j, (v (ch p) j : ℂ) * x j) /
        (1 + z * ((d (.inr p))⁻¹ : ℝ))) := by
    intro p
    rw [← hw p]
  simp_rw [e2] at h
  rw [sum_pieces_by_channel ch r (fun p => (d (.inr p))⁻¹) z u i
    (fun c => ∑ j, (v c j : ℂ) * x j)] at h
  rw [pencil_mulVec, Pi.zero_apply]
  have := hinv (.inl i)
  simp only [x] at h ⊢
  linear_combination -h + z * y (.inl i) * this

/-- Elimination (Lemma 1.1, backward): a nonzero kernel vector of the reduced pencil at
positive inverse rates gives an eigenpair of the corresponding positive scaling. -/
theorem eigenpair_of_pencil_kernel (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C)
    (r : κ → ℝ) (q : ι → ℝ) (t : κ → ℝ) (hq : ∀ i, 0 < q i) (ht : ∀ p, 0 < t p)
    (z : ℂ) (hz : ∀ p, 1 + z * (t p : ℂ) ≠ 0) (x : ι → ℂ) (hx : x ≠ 0)
    (hker : pencil B u v q (lagValue ch r t z) z *ᵥ x = 0) :
    ∃ y, HasEigenpair (rightScale (star B u v ch r)
      (Sum.elim (fun i => (q i)⁻¹) (fun p => (t p)⁻¹))) z y := by
  have hqn (i : ι) : (q i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hq i))
  have htn (p : κ) : (t p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (ht p))
  let w : κ → ℂ := fun p => (∑ j, (v (ch p) j : ℂ) * x j) / (1 + z * (t p : ℂ))
  let y : ι ⊕ κ → ℂ := Sum.elim (fun i => (q i : ℂ) * x i) (fun p => (t p : ℂ) * w p)
  have hdq (i : ι) : (((Sum.elim (fun i => (q i)⁻¹) (fun p => (t p)⁻¹)
      (Sum.inl i : ι ⊕ κ) : ℝ)) : ℂ) * y (.inl i) = x i := by
    simp only [Sum.elim_inl, y]; push_cast; field_simp [hqn i]
  have hdt (p : κ) : (((Sum.elim (fun i => (q i)⁻¹) (fun p => (t p)⁻¹)
      (Sum.inr p : ι ⊕ κ) : ℝ)) : ℂ) * y (.inr p) = w p := by
    simp only [Sum.elim_inr, y]; push_cast; field_simp [htn p]
  refine ⟨y, ?_, ?_⟩
  · intro h0
    apply hx
    funext i
    have := congrFun h0 (.inl i)
    simp only [y, Sum.elim_inl, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (hqn i)
  · intro a
    cases a with
    | inl i =>
      have hk := congrFun hker i
      rw [pencil_mulVec, Pi.zero_apply] at hk
      rw [star_mulVec_inl]
      simp_rw [hdq, hdt]
      rw [sum_pieces_by_channel ch r t z u i (fun c => ∑ j, (v c j : ℂ) * x j)]
      simp only [y, Sum.elim_inl]
      linear_combination -hk
    | inr p =>
      rw [star_mulVec_inr]
      simp_rw [hdq, hdt]
      simp only [y, Sum.elim_inr]
      have hwp : w p * (1 + z * t p) = ∑ j, (v (ch p) j : ℂ) * x j := by
        simp only [w]; field_simp [hz p]
      linear_combination hwp.symm

end DStabilityLocalization
