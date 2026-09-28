import proofs.DStabilityLocalization.ExitPath

/-!
# Boundary systems

A boundary choice `σ : κ → Role` sends every piece to `F` (fast: static load), `S` (slow:
removed) or `D` (its channel's synchronized group).  The boundary system is the lumped star
with core `B + Σ_{σ p = F} r_p u_{ch p} v_{ch p}ᵀ` and one lump per channel carrying
`Σ_{ch p = c, σ p = D} r_p`.  A generalized contact at `z` whose configuration is of boundary
type in every channel is an eigenvalue `z` of the corresponding boundary system.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Matrix Complex Set
open scoped BigOperators

namespace DStabilityLocalization
open DUnstableCores

/-- Role of a piece in a boundary system. -/
inductive Role
  | F
  | S
  | D
  deriving DecidableEq

variable {ι κ C : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype C] [DecidableEq C]

/-- Core of a boundary system: `B` plus the static loads of the fast pieces. -/
def bdCore (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ) (σ : κ → Role) :
    Matrix ι ι ℝ :=
  fun i j => B i j + ∑ p, if σ p = Role.F then r p * u (ch p) i * v (ch p) j else 0

/-- Lump of channel `c`: the total load of its synchronized group. -/
def bdLoad (ch : κ → C) (r : κ → ℝ) (σ : κ → Role) (c : C) : ℝ :=
  ∑ p, if ch p = c ∧ σ p = Role.D then r p else 0

/-- The boundary system: a lumped star with one attachment per channel. -/
def bdSystem (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ) (σ : κ → Role) :
    Matrix (ι ⊕ C) (ι ⊕ C) ℝ :=
  star (bdCore B u v ch r σ) u v id (bdLoad ch r σ)

/-- Number of synchronized groups (dynamic attachments) of a boundary choice. -/
def groups (ch : κ → C) (σ : κ → Role) : ℕ :=
  (Finset.univ.filter (fun c => ∃ p, ch p = c ∧ σ p = Role.D)).card

/-- Roles read off a configuration in `[0,1]^κ`. -/
def roleOf (s : κ → ℝ) (p : κ) : Role :=
  if s p = 0 then Role.F else if s p = 1 then Role.S else Role.D

/-- Inverse rate of the synchronized group of channel `c` (`1` if the group is empty). -/
def groupRate (ch : κ → C) (s : κ → ℝ) (c : C) : ℝ := by
  classical
  exact if h : ∃ p, ch p = c ∧ 0 < s p ∧ s p < 1 then s h.choose / (1 - s h.choose) else 1

theorem groupRate_pos (ch : κ → C) (s : κ → ℝ) (c : C) : 0 < groupRate ch s c := by
  classical
  unfold groupRate
  split_ifs with h
  · exact div_pos h.choose_spec.2.1 (by linarith [h.choose_spec.2.2])
  · exact one_pos

/-- Regrouping a channel-indexed sum over pieces. -/
theorem sum_channel_regroup (ch : κ → C) (f : κ → ℂ) (g : C → ℂ) :
    (∑ c, (∑ p, if ch p = c then f p else 0) * g c) = ∑ p, f p * g (ch p) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [ite_mul]

theorem val_of_boundaryType {z : ℂ} (hre : 0 ≤ z.re) (ch : κ → C) (s : κ → ℝ)
    (hs : ∀ p, s p ∈ Icc (0 : ℝ) 1) (hb : ∀ c, BoundaryType ch s c) (p : κ) :
    val z (s p) = (if roleOf s p = Role.F then 1 else 0) +
      (if roleOf s p = Role.D then 1 / (1 + z * (groupRate ch s (ch p) : ℂ)) else 0) := by
  classical
  unfold roleOf
  by_cases h0 : s p = 0
  · simp [h0, val_zero z]
  · by_cases h1 : s p = 1
    · simp [h1, val_one z]
    · simp only [h0, h1, if_false, reduceCtorEq, zero_add, if_true]
      have hp0 : 0 < s p := lt_of_le_of_ne (hs p).1 (Ne.symm h0)
      have hp1 : s p < 1 := lt_of_le_of_ne (hs p).2 h1
      have hex : ∃ q, ch q = ch p ∧ 0 < s q ∧ s q < 1 := ⟨p, rfl, hp0, hp1⟩
      have hrate : groupRate ch s (ch p) = s p / (1 - s p) := by
        unfold groupRate
        rw [dif_pos hex]
        have hq := hex.choose_spec
        have : s hex.choose = s p :=
          hb (ch p) hex.choose p hq.1 rfl hq.2.1 hq.2.2 hp0 hp1
        rw [this]
      rw [hrate, val_eq_lag hre _ hp0 hp1]

/-- A generalized contact of boundary type is the reduced pencil of a boundary system. -/
theorem pencil_boundary {z : ℂ} (hre : 0 ≤ z.re) (B : Matrix ι ι ℝ) (u v : C → ι → ℝ)
    (ch : κ → C) (r : κ → ℝ) (q : ι → ℝ) (s : κ → ℝ) (hs : ∀ p, s p ∈ Icc (0 : ℝ) 1)
    (hb : ∀ c, BoundaryType ch s c) :
    pencil B u v q (chanVal z ch r s) z =
      pencil (bdCore B u v ch r (roleOf s)) u v q
        (lagValue id (bdLoad ch r (roleOf s)) (groupRate ch s) z) z := by
  classical
  set σ := roleOf s
  set t := groupRate ch s
  have hlag : ∀ c, lagValue id (bdLoad ch r σ) t z c =
      (bdLoad ch r σ c : ℂ) / (1 + z * t c) := by
    intro c
    show (∑ p : C, if p = c then (bdLoad ch r σ p : ℂ) / (1 + z * (t p : ℂ)) else 0) = _
    rw [Fintype.sum_eq_single c (fun x hx => if_neg hx), if_pos rfl]
  have hchan : ∀ c, chanVal z ch r s c =
      (∑ p, if ch p = c then (if σ p = Role.F then (r p : ℂ) else 0) else 0) +
        (bdLoad ch r σ c : ℂ) / (1 + z * t c) := by
    intro c
    unfold chanVal bdLoad
    push_cast
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [val_of_boundaryType hre ch s hs hb p]
    by_cases hc : ch p = c
    · subst hc
      by_cases hF : σ p = Role.F
      · simp [σ, hF] at *
      · by_cases hD : σ p = Role.D
        · simp [σ, hF, hD] at *; ring
        · simp [σ, hF, hD] at *
    · simp [hc]
  ext i j
  simp only [pencil, bdCore]
  push_cast
  simp_rw [hlag, hchan, add_mul]
  rw [Finset.sum_add_distrib]
  have hF : (∑ c, (∑ p, if ch p = c then (if σ p = Role.F then (r p : ℂ) else 0) else 0) *
      (u c i : ℂ) * (v c j : ℂ)) =
      ∑ p, if σ p = Role.F then (r p : ℂ) * (u (ch p) i : ℂ) * (v (ch p) j : ℂ) else 0 := by
    have := sum_channel_regroup ch (fun p => if σ p = Role.F then (r p : ℂ) else 0)
      (fun c => (u c i : ℂ) * (v c j : ℂ))
    simp only [mul_assoc] at this ⊢
    rw [this]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  rw [hF]
  have hcast : (∑ p, ((if σ p = Role.F then r p * u (ch p) i * v (ch p) j else 0 : ℝ) : ℂ)) =
      ∑ p, if σ p = Role.F then (r p : ℂ) * (u (ch p) i : ℂ) * (v (ch p) j : ℂ) else 0 := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  simp only [id] at *
  rw [← hcast]
  ring

/-- `1 + z t ≠ 0` for `Re z ≥ 0` and `t ≥ 0`. -/
theorem one_add_mul_ne {z : ℂ} (hre : 0 ≤ z.re) {t : ℝ} (ht : 0 ≤ t) : 1 + z * (t : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  nlinarith [mul_nonneg hre ht]

/-- **Boundary contact.** A generalized contact at `z` whose configuration is of boundary type in
every channel gives the eigenvalue `z` of the boundary system at the core inverse rates `q` and
the group inverse rates `groupRate`. -/
theorem boundary_eigenpair {z : ℂ} (hre : 0 ≤ z.re) (B : Matrix ι ι ℝ) (u v : C → ι → ℝ)
    (ch : κ → C) (r : κ → ℝ)
    (q : ι → ℝ) (hq : ∀ i, 0 < q i) (s : κ → ℝ) (hs : ∀ p, s p ∈ Icc (0 : ℝ) 1)
    (hb : ∀ c, BoundaryType ch s c) (hcon : (pencil B u v q (chanVal z ch r s) z).det = 0) :
    ∃ y, HasEigenpair (rightScale (bdSystem B u v ch r (roleOf s))
      (Sum.elim (fun i => (q i)⁻¹) (fun c => (groupRate ch s c)⁻¹))) z y := by
  rw [pencil_boundary hre B u v ch r q s hs hb] at hcon
  obtain ⟨x, hx, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hcon
  have ht := groupRate_pos ch s
  have hz : ∀ c, 1 + z * (groupRate ch s c : ℂ) ≠ 0 := fun c => one_add_mul_ne hre (ht c).le
  obtain ⟨y, hy⟩ := eigenpair_of_pencil_kernel (bdCore B u v ch r (roleOf s)) u v id
    (bdLoad ch r (roleOf s)) q (groupRate ch s) hq ht z hz x hx hker
  exact ⟨y, hy⟩

end DStabilityLocalization
