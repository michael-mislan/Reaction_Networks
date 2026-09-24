import proofs.CompositionalMemory.SemenovMetricGeometryData
import proofs.CompositionalMemory.WhitenedMetricBounds

namespace CompositionalMemory.Semenov
open Polynomial Matrix

noncomputable def coefficientValue {N : ℕ} (c : Fin N → ℚ) (t : ℝ) : ℝ :=
  aeval t (rationalChebyshevPolynomial c)

noncomputable def coefficientMatrix {N D : ℕ} (c : Fin N → Fin N → Fin D → ℚ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j => coefficientValue (c i j) t

noncomputable def rationalMatrix {N : ℕ} (A : Fin N → Fin N → ℚ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (A i j : ℝ)

theorem cached_ofFn_value {α : Type*} {N : ℕ} (f : Fin N → α) (i : Fin N) (fallback : α) :
    (List.ofFn f).getD i.val fallback=f i := by
  simp

theorem coefficientValue_linear {N M : ℕ} (weights : Fin M → ℚ) (c : Fin M → Fin N → ℚ) (t : ℝ) :
    coefficientValue (fun k => ∑ j,weights j*c j k) t=
      ∑ j,(weights j : ℝ)*coefficientValue (c j) t := by
  simp only [coefficientValue,rationalChebyshevPolynomial_eval,Rat.cast_sum,Rat.cast_mul,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem coefficient_congruence_symmetric {N D : ℕ} (pc wc : Fin N → Fin N → Fin D → ℚ)
    (A : Fin N → Fin N → ℚ) (t : ℝ)
    (hw : coefficientMatrix wc t = rationalMatrix A * coefficientMatrix pc t * (rationalMatrix A).transpose)
    (hp : ∀ i j,coefficientValue (pc i j) t=coefficientValue (pc j i) t) :
    ∀ i j,coefficientValue (wc i j) t=coefficientValue (wc j i) t := by
  have hP : (coefficientMatrix pc t).transpose=coefficientMatrix pc t := by
    ext i j
    exact hp j i
  have hW : (coefficientMatrix wc t).transpose=coefficientMatrix wc t := by
    rw [hw,Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,hP,Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun hW j) i

theorem whitened_replay_sound (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (P : Fin 8 → Fin 8 → QCoefficients) (A : Fin 8 → Fin 8 → ℚ)
    (hP : ∀ i j,P i j=qchebyshevSeries (pc i j))
    (hcheck : ∀ i j,qzeroCheck (qsub (whitenedPolynomial P A i j) (qchebyshevSeries (wc i j)))=true)
    (t : ℝ) : coefficientMatrix wc t = rationalMatrix A * coefficientMatrix pc t * (rationalMatrix A).transpose := by
  ext i j
  have he := congrArg (fun p : Polynomial ℚ => aeval t p) (qidentity_sound _ _ (hcheck i j))
  simp only [whitenedPolynomial,qpolynomial_qsumFin,qpolynomial_qscale,hP,
    qchebyshevSeries_semantics,map_sum,map_mul,aeval_C] at he
  change aeval t (rationalChebyshevPolynomial (wc i j)) = _
  rw [← he]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,rationalMatrix,coefficientMatrix,coefficientValue,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change (A i l : ℝ)*(A j k : ℝ)*aeval t (rationalChebyshevPolynomial (pc l k)) = _
  ring

theorem coefficientValue_abs {N : ℕ} (c : Fin N → ℚ) (t : ℝ)
    (hl : -1 ≤ t) (hu : t ≤ 1) : |coefficientValue c t| ≤ (coefficientNorm c : ℝ) := by
  exact rationalChebyshevPolynomial_abs_bound c (coefficientNorm c) le_rfl t hl hu

theorem coefficientValue_tail {N : ℕ} (c : Fin (N+1) → ℚ) (t : ℝ)
    (hl : -1 ≤ t) (hu : t ≤ 1) :
    |coefficientValue c t-(c 0 : ℝ)| ≤ ∑ i : Fin N,|(c i.succ : ℝ)| := by
  rw [coefficientValue,rationalChebyshevPolynomial_eval,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Int.ofNat_zero,Chebyshev.T_zero,eval_one,mul_one,add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (chebyshev_abs_le_one i.succ.val t hl hu)
    (abs_nonneg (c i.succ : ℝ))

theorem coefficientValue_bounds {N : ℕ} (c : Fin (N+1) → ℚ) (t : ℝ)
    (hl : -1 ≤ t) (hu : t ≤ 1) :
    (coefficientLower c : ℝ) ≤ coefficientValue c t ∧
    coefficientValue c t ≤ (coefficientUpper c : ℝ) := by
  have h := abs_le.mp (coefficientValue_tail c t hl hu)
  simp only [coefficientLower,coefficientUpper,Rat.cast_sub,Rat.cast_add,Rat.cast_sum,Rat.cast_abs]
  constructor <;> linarith only [h.1,h.2]

theorem coefficient_matrix_row_bound {N D : ℕ} (pc : Fin N → Fin N → Fin D → ℚ)
    (L : ℚ) (hrow : ∀ i,(∑ j,coefficientNorm (pc i j)) ≤ L)
    (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1) (i : Fin N) :
    (∑ j,|coefficientValue (pc i j) t|) ≤ (L : ℝ) := by
  calc
    _ ≤ ∑ j,(coefficientNorm (pc i j) : ℝ) :=
      Finset.sum_le_sum (fun j _ => coefficientValue_abs _ t hl hu)
    _ ≤ _ := by exact_mod_cast hrow i

theorem coefficient_matrix_diagonal_bound {N D : ℕ}
    (wc : Fin N → Fin N → Fin (D+1) → ℚ) (margin : ℚ)
    (hdiag : ∀ i,margin ≤ coefficientLower (wc i i)-∑ j,if j=i then 0 else coefficientNorm (wc i j))
    (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1) (i : Fin N) :
    (margin : ℝ) ≤ coefficientValue (wc i i) t-
      ∑ j,if j=i then 0 else |coefficientValue (wc i j) t| := by
  have hd := (coefficientValue_bounds (wc i i) t hl hu).1
  have ho : (∑ j,if j=i then (0 : ℝ) else |coefficientValue (wc i j) t|) ≤
      ∑ j,if j=i then (0 : ℝ) else (coefficientNorm (wc i j) : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> first | exact le_rfl | exact coefficientValue_abs _ t hl hu
  have hh : (margin : ℝ) ≤ (coefficientLower (wc i i) : ℝ)-
      ∑ j,if j=i then (0 : ℝ) else (coefficientNorm (wc i j) : ℝ) := by
    have hc : (margin : ℝ) ≤ ((coefficientLower (wc i i)-
        ∑ j,if j=i then 0 else coefficientNorm (wc i j) : ℚ) : ℝ) := by
      exact_mod_cast hdiag i
    simpa only [Rat.cast_sub,Rat.cast_sum,apply_ite,Rat.cast_zero] using hc
  linarith only [hd,ho,hh]

/-- The matrix checks imply a real tube radius at every time in the interval.
The congruence identity is supplied by exact polynomial replay. -/
theorem geometry_tube_radius
    (zc : Fin 8 → Fin 17 → ℚ) (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (A : Fin 8 → Fin 8 → ℚ) (nr : Fin 11 → ℚ) (eta radius margin L Q H : ℚ)
    (hg : MetricGeometryChecks zc pc wc A nr eta radius margin L Q H)
    (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1)
    (hw : coefficientMatrix wc t = rationalMatrix A * coefficientMatrix pc t * (rationalMatrix A).transpose)
    (hsym : ∀ i j,coefficientValue (wc i j) t=coefficientValue (wc j i) t)
    (x : Fin 8 → ℝ) (hx : matrixEnergy (fun i j => coefficientValue (pc i j) t) x ≤ (eta : ℝ)) :
    vectorSquares x ≤ (radius : ℝ)^2 := by
  rcases hg with ⟨hpos,htri,hdiag,hmargin,hnr,hcurv,heta,hL,hH,hJ,hQ⟩
  apply whitened_metric_radius (coefficientMatrix pc t)
    (rationalMatrix A) ?_ (margin : ℝ) (eta : ℝ) (radius : ℝ) ?_ ?_ ?_ x hx
  · apply lower_triangular_det_ne_zero
    · intro i j hij
      change (A i j : ℝ)=0
      exact_mod_cast htri i j hij
    · intro i
      change (0 : ℝ) < (A i i : ℝ)
      exact_mod_cast hdiag i
  · exact_mod_cast hpos.2.2.1
  · intro y
    rw [← hw]
    exact matrix_energy_diagonal_lower _ hsym (margin : ℝ)
      (coefficient_matrix_diagonal_bound wc margin hmargin t hl hu) y
  · unfold frobeniusSquared
    unfold whiteningNormSquared at heta
    dsimp only [rationalMatrix]
    exact_mod_cast heta

end CompositionalMemory.Semenov
