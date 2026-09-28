import proofs.DStabilityLocalization.ArcGeometry

/-!
# The exit lemma at an eigenvalue `z`

Generalized contacts at a non-real `z` with `Re z ≥ 0` use the compact parametrization
`s ∈ [0,1]` of every piece: `det (pencil B u v q (chanVal z ch r s) z) = 0`.  With all channels but `c` frozen, the
contact determinant is affine in the value of channel `c` (`det_sub_smul_vecMulVec`), a
Gershgorin bound excludes contacts at large core dilation, and at the largest dilation that
still admits a contact the configuration of channel `c` is of boundary type: all interior
parameters of the channel are equal (one synchronized group), since otherwise the channel
value map is open there (`open_two_pieces`) and the contact persists to a larger dilation.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Matrix Complex Filter Topology Set
open scoped BigOperators

namespace DStabilityLocalization
open DUnstableCores

variable {ι κ C : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype C] [DecidableEq C]

/-! ### Rank-one updates are affine (Lemma 1.2) -/

/-- The coefficient of the rank-one direction. -/
def rankOneCoeff (M : Matrix ι ι ℂ) (a b : ι → ℂ) : ℂ :=
  (updateRow (fromBlocks M (replicateCol Unit a) 0 (1 : Matrix Unit Unit ℂ)) (Sum.inr ())
    (Sum.elim b (0 : Unit → ℂ))).det

theorem det_sub_smul_vecMulVec (M : Matrix ι ι ℂ) (a b : ι → ℂ) (m : ℂ) :
    (M - m • vecMulVec a b).det = M.det + m * rankOneCoeff M a b := by
  have h1 : M - m • vecMulVec a b = M - replicateCol Unit a * (m • replicateRow Unit b) := by
    rw [Matrix.mul_smul, ← vecMulVec_eq]
  have h2 : (fromBlocks M (replicateCol Unit a) (m • replicateRow Unit b)
      (1 : Matrix Unit Unit ℂ)).det = (M - m • vecMulVec a b).det := by
    rw [det_fromBlocks_one₂₂, h1]
  rw [← h2]
  have h3 : fromBlocks M (replicateCol Unit a) (m • replicateRow Unit b) (1 : Matrix Unit Unit ℂ)
      = updateRow (fromBlocks M (replicateCol Unit a) 0 (1 : Matrix Unit Unit ℂ)) (Sum.inr ())
          (m • Sum.elim b (0 : Unit → ℂ) + Sum.elim (0 : ι → ℂ) (1 : Unit → ℂ)) := by
    ext i j
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;> simp [updateRow_apply]
  have h4 : updateRow (fromBlocks M (replicateCol Unit a) 0 (1 : Matrix Unit Unit ℂ))
      (Sum.inr ()) (Sum.elim (0 : ι → ℂ) (1 : Unit → ℂ)) = fromBlocks M (replicateCol Unit a) 0 1 := by
    ext i j
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;> simp [updateRow_apply]
  rw [h3, det_updateRow_add, det_updateRow_smul, h4, det_fromBlocks_zero₂₁]
  simp [rankOneCoeff]
  ring

/-! ### Channel values -/

/-- Value of channel `c` in the compact parametrization at `z`. -/
def chanVal (z : ℂ) (ch : κ → C) (r s : κ → ℝ) (c : C) : ℂ :=
  ∑ p, if ch p = c then (r p : ℂ) * val z (s p) else 0

/-- All interior parameters of channel `c` coincide (at most one synchronized group). -/
def BoundaryType (ch : κ → C) (s : κ → ℝ) (c : C) : Prop :=
  ∀ p q, ch p = c → ch q = c → 0 < s p → s p < 1 → 0 < s q → s q < 1 → s p = s q

theorem norm_val_le_one {z : ℂ} (hre : 0 ≤ z.re) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖val z s‖ ≤ 1 := by
  unfold val
  rw [norm_div]
  apply div_le_one_of_le₀ _ (norm_nonneg _)
  have h1 : ‖(1 : ℂ) - (s : ℂ)‖ = 1 - s := by
    rw [show (1 : ℂ) - (s : ℂ) = ((1 - s : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
  rw [h1]
  have h2 := Complex.re_le_norm (1 - (s : ℂ) + (s : ℂ) * z)
  have h3 : (1 - (s : ℂ) + (s : ℂ) * z).re = 1 - s + s * z.re := by simp
  rw [h3] at h2
  nlinarith [mul_nonneg hs.1 hre]

theorem norm_chanVal_le {z : ℂ} (hre : 0 ≤ z.re) (ch : κ → C) (r s : κ → ℝ)
    (hs : ∀ p, s p ∈ Icc (0 : ℝ) 1) (c : C) :
    ‖chanVal z ch r s c‖ ≤ ∑ p, |r p| := by
  unfold chanVal
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => ?_))
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_val_le_one hre (hs p))
  · simp

theorem continuous_chanVal {z : ℂ} (hz : z.im ≠ 0) (ch : κ → C) (r : κ → ℝ) (c : C) :
    Continuous (fun s : κ → ℝ => chanVal z ch r s c) := by
  unfold chanVal
  refine continuous_finsetSum _ (fun p _ => ?_)
  split_ifs
  · exact continuous_const.mul ((continuous_val hz).comp (continuous_apply p))
  · exact continuous_const

/-- Changing one coordinate changes a separable sum by the difference of one term. -/
theorem sum_update_eq {β : Type*} [AddCommGroup β] (g : κ → ℝ → β) (s : κ → ℝ) (j : κ)
    (x : ℝ) : (∑ p, g p (Function.update s j x p)) = (∑ p, g p (s p)) - g j (s j) + g j x := by
  rw [Fintype.sum_eq_add_sum_compl j, Fintype.sum_eq_add_sum_compl j (fun p => g p (s p))]
  simp only [Function.update_self]
  have : (∑ p ∈ ({j}ᶜ : Finset κ), g p (Function.update s j x p)) =
      ∑ p ∈ ({j}ᶜ : Finset κ), g p (s p) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Function.update_of_ne (by simpa using hp)]
  rw [this]
  abel

theorem chanVal_update_two (z : ℂ) (ch : κ → C) (r s : κ → ℝ) (c : C) {j k : κ}
    (hjk : j ≠ k) (hj : ch j = c) (hk : ch k = c) (x y : ℝ) :
    chanVal z ch r (Function.update (Function.update s j x) k y) c =
      (chanVal z ch r s c - (r j : ℂ) * val z (s j) - (r k : ℂ) * val z (s k)) +
        (r j : ℂ) * val z x + (r k : ℂ) * val z y := by
  let g : κ → ℝ → ℂ := fun p w => if ch p = c then (r p : ℂ) * val z w else 0
  have e : ∀ s', chanVal z ch r s' c = ∑ p, g p (s' p) := fun s' => rfl
  rw [e, sum_update_eq g _ k y, sum_update_eq g s j x, e]
  simp only [g, hj, hk, if_true, Function.update_of_ne (Ne.symm hjk)]
  ring

theorem chanVal_congr (z : ℂ) (ch : κ → C) (r : κ → ℝ) {s s' : κ → ℝ} (c : C)
    (h : ∀ p, ch p = c → s' p = s p) : chanVal z ch r s' c = chanVal z ch r s c := by
  unfold chanVal
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs with hp
  · rw [h p hp]
  · rfl

/-! ### Frozen channels and the affine contact determinant -/

theorem pencil_update (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (q : ι → ℝ) (ℓ : C → ℂ)
    (c : C) (m : ℂ) (z : ℂ) :
    pencil B u v q (Function.update ℓ c m) z =
      pencil B u v q (Function.update ℓ c 0) z -
        m • vecMulVec (fun i => (u c i : ℂ)) (fun j => (v c j : ℂ)) := by
  ext i j
  simp only [pencil, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  have key := sum_update_eq (κ := C) (fun c' (w : ℝ) => (0 : ℂ)) (fun _ => 0) c 0
  have hsum : (∑ c', Function.update ℓ c m c' * (u c' i : ℂ) * (v c' j : ℂ)) =
      (∑ c', Function.update ℓ c 0 c' * (u c' i : ℂ) * (v c' j : ℂ)) +
        m * (u c i : ℂ) * (v c j : ℂ) := by
    rw [Fintype.sum_eq_add_sum_compl c, Fintype.sum_eq_add_sum_compl c
      (fun c' => Function.update ℓ c 0 c' * (u c' i : ℂ) * (v c' j : ℂ))]
    simp only [Function.update_self, zero_mul, zero_add]
    have : (∑ c' ∈ ({c}ᶜ : Finset C), Function.update ℓ c m c' * (u c' i : ℂ) * (v c' j : ℂ)) =
        ∑ c' ∈ ({c}ᶜ : Finset C), Function.update ℓ c 0 c' * (u c' i : ℂ) * (v c' j : ℂ) := by
      refine Finset.sum_congr rfl (fun c' hc' => ?_)
      have hne : c' ≠ c := by simpa using hc'
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    rw [this]
    ring
  rw [hsum]
  ring

/-! ### Large dilations admit no contact (Lemma 3.1) -/

theorem pencil_det_ne_of_large (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (q : ι → ℝ)
    (hq : ∀ i, 0 < q i) {z : ℂ} (hz0 : z ≠ 0) (K : ℝ) (hK : 0 ≤ K) :
    ∃ τ₀ : ℝ, 1 ≤ τ₀ ∧ ∀ τ : ℝ, τ₀ ≤ τ → ∀ ℓ : C → ℂ, (∀ c, ‖ℓ c‖ ≤ K) →
      (pencil B u v (fun i => τ * q i) ℓ z).det ≠ 0 := by
  let R : ι → ℝ := fun i => ∑ j, (|B i j| + K * ∑ c, |u c i| * |v c j|)
  have hR : ∀ i, 0 ≤ R i := fun i => Finset.sum_nonneg (fun j _ =>
    add_nonneg (abs_nonneg _) (mul_nonneg hK (Finset.sum_nonneg (fun c _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)))))
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hqz : ∀ i, 0 < ‖z‖ * q i := fun i => mul_pos hzn (hq i)
  have hS : 0 ≤ ∑ i, R i / (‖z‖ * q i) :=
    Finset.sum_nonneg (fun i _ => div_nonneg (hR i) (hqz i).le)
  refine ⟨1 + ∑ i, R i / (‖z‖ * q i), by linarith, ?_⟩
  intro τ hτ ℓ hℓ
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  set E : ι → ℂ := fun j => (B i j : ℂ) + ∑ c, ℓ c * u c i * v c j with hE
  have hEb : ∀ j, ‖E j‖ ≤ |B i j| + K * ∑ c, |u c i| * |v c j| := by
    intro j
    refine (norm_add_le _ _).trans (add_le_add (by simp) ?_)
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun c _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have := hℓ c
    have h0 : 0 ≤ |u c i| * |v c j| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith [norm_nonneg (ℓ c)]
  have hsumE : ∑ j, ‖E j‖ ≤ R i := Finset.sum_le_sum (fun j _ => hEb j)
  have hRi : R i / (‖z‖ * q i) ≤ ∑ i, R i / (‖z‖ * q i) :=
    Finset.single_le_sum (f := fun i => R i / (‖z‖ * q i))
      (fun i _ => div_nonneg (hR i) (hqz i).le) (Finset.mem_univ i)
  have hτq : R i < ‖z‖ * (τ * q i) := by
    have h1 : R i / (‖z‖ * q i) < τ := by linarith
    rw [div_lt_iff₀ (hqz i)] at h1
    linarith
  have hτpos : 0 < τ * q i := mul_pos (by linarith) (hq i)
  have hent : ∀ j, pencil B u v (fun i => τ * q i) ℓ z i j =
      (if i = j then z * ((τ * q i : ℝ) : ℂ) else 0) - E j := by
    intro j; simp only [pencil, hE]; push_cast; ring
  have hdiag : ‖pencil B u v (fun i => τ * q i) ℓ z i i‖ ≥ ‖z‖ * (τ * q i) - ‖E i‖ := by
    rw [hent i, if_pos rfl]
    have h1 := norm_sub_norm_le (z * ((τ * q i : ℝ) : ℂ)) (E i)
    have h2 : ‖z * ((τ * q i : ℝ) : ℂ)‖ = ‖z‖ * (τ * q i) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτpos]
    linarith
  have hoff : ∑ j ∈ Finset.univ.erase i, ‖pencil B u v (fun i => τ * q i) ℓ z i j‖ =
      ∑ j ∈ Finset.univ.erase i, ‖E j‖ := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hent j, if_neg (Ne.symm (Finset.ne_of_mem_erase hj)), zero_sub, norm_neg]
  rw [hoff]
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => ‖E j‖) (Finset.mem_univ i)
  linarith

/-! ### The exit lemma (Lemma 3.2) -/

/-- **Exit lemma at `z`.** A generalized contact can be pushed, by a core dilation `τ ≥ 1` and a
change of the parameters of channel `c` only, to a generalized contact in which channel `c` is of
boundary type. -/
theorem exit_channel {z : ℂ} (hre : 0 ≤ z.re) (hz : z.im ≠ 0)
    (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ)
    (hr : ∀ p, r p ≠ 0) (c : C) (q : ι → ℝ) (hq : ∀ i, 0 < q i) (s : κ → ℝ)
    (hs : ∀ p, s p ∈ Icc (0 : ℝ) 1)
    (hcon : (pencil B u v q (chanVal z ch r s) z).det = 0) :
    ∃ τ : ℝ, 1 ≤ τ ∧ ∃ s' : κ → ℝ, (∀ p, s' p ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, ch p ≠ c → s' p = s p) ∧ BoundaryType ch s' c ∧
      (pencil B u v (fun i => τ * q i) (chanVal z ch r s') z).det = 0 := by
  have hz0 : z ≠ 0 := fun h => hz (by rw [h]; simp)
  set K : ℝ := ∑ p, |r p| with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg (fun p _ => abs_nonneg _)
  set ℓ0 : C → ℂ := Function.update (chanVal z ch r s) c 0 with hℓ0
  set a : ℝ → ℂ := fun τ => (pencil B u v (fun i => τ * q i) ℓ0 z).det with ha
  set b : ℝ → ℂ := fun τ => rankOneCoeff (pencil B u v (fun i => τ * q i) ℓ0 z)
    (fun i => (u c i : ℂ)) (fun j => (v c j : ℂ)) with hb
  -- the contact determinant is affine in the value of channel `c`
  have hval : ∀ s' : κ → ℝ, (∀ p, ch p ≠ c → s' p = s p) →
      chanVal z ch r s' = Function.update ℓ0 c (chanVal z ch r s' c) := by
    intro s' hs'
    funext c'
    by_cases hc : c' = c
    · subst hc; simp [hℓ0]
    · rw [Function.update_of_ne hc, hℓ0, Function.update_of_ne hc]
      exact chanVal_congr z ch r c' (fun p hp => hs' p (by rw [hp]; exact hc))
  have haff : ∀ τ (m : ℂ), (pencil B u v (fun i => τ * q i) (Function.update ℓ0 c m) z).det
      = a τ + m * b τ := by
    intro τ m
    rw [pencil_update, hℓ0, Function.update_idem, ← hℓ0, det_sub_smul_vecMulVec]
  have hpen : ∀ i j, Continuous (fun τ : ℝ => pencil B u v (fun i => τ * q i) ℓ0 z i j) := by
    intro i j
    by_cases hij : i = j
    · simp only [pencil, hij, if_true]; fun_prop
    · simp only [pencil, hij, if_false]; fun_prop
  have hacont : Continuous a := by
    apply Continuous.matrix_det
    exact continuous_pi (fun i => continuous_pi (fun j => hpen i j))
  have hbcont : Continuous b := by
    simp only [hb, rankOneCoeff]
    apply Continuous.matrix_det
    refine continuous_pi (fun x => continuous_pi (fun y => ?_))
    rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩ <;>
      simp only [updateRow_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, reduceCtorEq, if_false, if_true, Sum.elim_inl, Sum.elim_inr] <;>
      first | exact hpen _ _ | exact continuous_const
  -- Gershgorin
  obtain ⟨τ₀, hτ₀1, hτ₀⟩ := pencil_det_ne_of_large B u v q hq hz0 K hK
  have hℓ0b : ∀ m : ℂ, ‖m‖ ≤ K → ∀ c', ‖Function.update ℓ0 c m c'‖ ≤ K := by
    intro m hm c'
    by_cases hc : c' = c
    · subst hc; simpa using hm
    · rw [Function.update_of_ne hc, hℓ0, Function.update_of_ne hc]
      exact norm_chanVal_le hre ch r s hs c'
  have hbig : ∀ τ, τ₀ ≤ τ → ∀ m : ℂ, ‖m‖ ≤ K → a τ + m * b τ ≠ 0 := by
    intro τ hτ m hm
    rw [← haff]
    exact hτ₀ τ hτ _ (hℓ0b m hm)
  -- the compact set of contacts
  let S : Set (ℝ × (κ → ℝ)) := {x | x.1 ∈ Icc 1 τ₀ ∧ (∀ p, x.2 p ∈ Icc (0 : ℝ) 1) ∧
    (∀ p, ch p ≠ c → x.2 p = s p) ∧ a x.1 + chanVal z ch r x.2 c * b x.1 = 0}
  have hSsub : S ⊆ Icc 1 τ₀ ×ˢ Set.pi univ (fun _ => Icc (0 : ℝ) 1) := by
    rintro x ⟨h1, h2, -, -⟩
    exact ⟨h1, fun p _ => h2 p⟩
  have hSclosed : IsClosed S := by
    have hc1 : IsClosed {x : ℝ × (κ → ℝ) | x.1 ∈ Icc 1 τ₀} :=
      isClosed_Icc.preimage continuous_fst
    have hc2 : IsClosed {x : ℝ × (κ → ℝ) | ∀ p, x.2 p ∈ Icc (0 : ℝ) 1} := by
      simp only [setOf_forall]
      exact isClosed_iInter (fun p => isClosed_Icc.preimage
        ((continuous_apply p).comp continuous_snd))
    have hc3 : IsClosed {x : ℝ × (κ → ℝ) | ∀ p, ch p ≠ c → x.2 p = s p} := by
      simp only [setOf_forall]
      exact isClosed_iInter (fun p => isClosed_iInter (fun _ =>
        isClosed_eq ((continuous_apply p).comp continuous_snd) continuous_const))
    have hc4 : IsClosed {x : ℝ × (κ → ℝ) | a x.1 + chanVal z ch r x.2 c * b x.1 = 0} :=
      isClosed_eq ((hacont.comp continuous_fst).add
        (((continuous_chanVal hz ch r c).comp continuous_snd).mul (hbcont.comp continuous_fst)))
        continuous_const
    exact hc1.inter (hc2.inter (hc3.inter hc4))
  have hScompact : IsCompact S :=
    (isCompact_Icc.prod (isCompact_univ_pi (fun _ => isCompact_Icc))).of_isClosed_subset
      hSclosed hSsub
  have hmem1 : ((1 : ℝ), s) ∈ S := by
    refine ⟨⟨le_refl _, hτ₀1⟩, hs, fun p _ => rfl, ?_⟩
    rw [← haff, ← hval s (fun p _ => rfl)]
    simpa using hcon
  obtain ⟨x, hxS, hxmax⟩ := hScompact.exists_isMaxOn ⟨_, hmem1⟩ continuous_fst.continuousOn
  obtain ⟨⟨hx1, hx2⟩, hxcube, hxoff, hxzero⟩ := hxS
  set τs := x.1
  set ss := x.2
  by_cases hb0 : b τs = 0
  · -- all-slow configuration of channel `c`
    refine ⟨τs, hx1, fun p => if ch p = c then 1 else s p, ?_, ?_, ?_, ?_⟩
    · intro p
      show (if ch p = c then (1 : ℝ) else s p) ∈ Icc (0 : ℝ) 1
      split_ifs
      · exact ⟨zero_le_one, le_refl _⟩
      · exact hs p
    · intro p hp; simp [hp]
    · intro p p' hp _ _ h1 _ _
      simp [hp] at h1
    · have hoffs : ∀ p, ch p ≠ c → (fun p => if ch p = c then (1 : ℝ) else s p) p = s p := by
        intro p hp; simp [hp]
      rw [hval _ hoffs, haff]
      have hzero : chanVal z ch r (fun p => if ch p = c then (1 : ℝ) else s p) c = 0 := by
        unfold chanVal
        refine Finset.sum_eq_zero (fun p _ => ?_)
        split_ifs with hp
        · simp [hp, val_one z]
        · rfl
      rw [hzero]
      have h' := hxzero
      rw [hb0, mul_zero, add_zero] at h'
      rw [h']
      ring
  · refine ⟨τs, hx1, ss, hxcube, hxoff, ?_, ?_⟩
    · -- boundary type at the maximal dilation
      intro j k hj hk hj0 hj1 hk0 hk1
      by_contra hne
      have hjk : j ≠ k := by rintro rfl; exact hne rfl
      set c₀ : ℂ := chanVal z ch r ss c - (r j : ℂ) * val z (ss j) - (r k : ℂ) * val z (ss k)
      set F : ℝ × ℝ → ℂ := fun p => c₀ + (r j : ℂ) * val z p.1 + (r k : ℂ) * val z p.2
      have hFmap := open_two_pieces hre hz c₀ (hr j) (hr k) hj0 hj1 hk0 hk1 hne
      have hF0 : c₀ + (r j : ℂ) * val z (ss j) + (r k : ℂ) * val z (ss k) = chanVal z ch r ss c := by
        simp only [c₀]; ring
      have hU : Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ∈ 𝓝 (ss j, ss k) :=
        prod_mem_nhds (Ioo_mem_nhds hj0 hj1) (Ioo_mem_nhds hk0 hk1)
      have hFU : F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ∈ 𝓝 (chanVal z ch r ss c) := by
        rw [← hF0, ← hFmap]
        exact image_mem_map hU
      -- the contact curve of channel `c`
      have hh : ContinuousAt (fun τ => -a τ / b τ) τs :=
        (hacont.continuousAt.neg).div hbcont.continuousAt hb0
      have hhval : -a τs / b τs = chanVal z ch r ss c := by
        rw [div_eq_iff hb0]; linear_combination -hxzero
      have hev : ∀ᶠ τ in 𝓝 τs, (-a τ / b τ ∈ F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) ∧
          b τ ≠ 0 := by
        refine (hh.eventually (by
          rw [show (fun τ => -a τ / b τ) τs = chanVal z ch r ss c from hhval]; exact hFU)).and ?_
        exact hbcont.continuousAt.eventually_ne hb0
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
      set τ₁ := τs + ε / 2
      have hτ₁ : dist τ₁ τs < ε := by
        rw [Real.dist_eq, show τ₁ - τs = ε / 2 by simp [τ₁]]
        rw [abs_of_pos (by linarith)]; linarith
      obtain ⟨⟨⟨xy1, xy2⟩, ⟨hx1', hx2'⟩, hFxy⟩, hbτ₁⟩ := hball hτ₁
      set s₁ := Function.update (Function.update ss j xy1) k xy2
      have hs₁val : chanVal z ch r s₁ c = F (xy1, xy2) := by
        rw [chanVal_update_two z ch r ss c hjk hj hk]
      have hs₁cube : ∀ p, s₁ p ∈ Icc (0 : ℝ) 1 := by
        intro p
        by_cases hpk : p = k
        · subst hpk; simp [s₁]; exact ⟨hx2'.1.le, hx2'.2.le⟩
        · by_cases hpj : p = j
          · subst hpj
            simp [s₁, Function.update_of_ne hpk]; exact ⟨hx1'.1.le, hx1'.2.le⟩
          · simp [s₁, Function.update_of_ne hpk, Function.update_of_ne hpj]
            exact hxcube p
      have hs₁off : ∀ p, ch p ≠ c → s₁ p = s p := by
        intro p hp
        have hpk : p ≠ k := by rintro rfl; exact hp hk
        have hpj : p ≠ j := by rintro rfl; exact hp hj
        simp only [s₁, Function.update_of_ne hpk, Function.update_of_ne hpj]
        exact hxoff p hp
      have hzero₁ : a τ₁ + chanVal z ch r s₁ c * b τ₁ = 0 := by
        rw [hs₁val, hFxy]; field_simp; ring
      have hτ₁le : τ₁ ≤ τ₀ := by
        by_contra hlt
        exact hbig τ₁ (le_of_lt (not_le.mp hlt)) _
          (norm_chanVal_le hre ch r s₁ hs₁cube c) hzero₁
      have hmem : (τ₁, s₁) ∈ S :=
        ⟨⟨by show 1 ≤ τs + ε / 2; linarith, hτ₁le⟩, hs₁cube, hs₁off, hzero₁⟩
      have hle : τs + ε / 2 ≤ τs := hxmax hmem
      linarith
    · rw [hval ss hxoff, haff]
      exact hxzero

end DStabilityLocalization
