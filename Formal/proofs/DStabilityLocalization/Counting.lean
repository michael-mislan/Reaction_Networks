import proofs.DStabilityLocalization.Main

/-!
# Distinct boundary systems (follow-ups A1, A2; not used by the root theorems)

A boundary system depends on the boundary choice only through the fast and synchronized load
sums of every channel (`bdSystem_eq_of_loads`).  For loads that are positive integer multiples
of `δ`, the number of distinct boundary systems is at most `∏_c (N_c + 1)²`, where `N_c δ` is the
total load of channel `c` (`card_bdSystems_le`), while there are `3^{#pieces}` boundary choices.
Deciding D-semistability (and certifying D-stability) of the star therefore reduces to the list
of distinct boundary systems (`dUnstable_iff_distinct`, `dStable_of_distinct`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Matrix
open scoped BigOperators

namespace DStabilityLocalization
open DUnstableCores

instance : Fintype Role where
  elems := {Role.F, Role.S, Role.D}
  complete := fun ρ => by cases ρ <;> simp

variable {ι κ C : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype C] [DecidableEq C]

/-- Fast load of channel `c`. -/
def fastLoad (ch : κ → C) (r : κ → ℝ) (σ : κ → Role) (c : C) : ℝ :=
  ∑ p, if ch p = c ∧ σ p = Role.F then r p else 0

theorem bdCore_eq (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ)
    (σ : κ → Role) :
    bdCore B u v ch r σ = fun i j => B i j + ∑ c, fastLoad ch r σ c * u c i * v c j := by
  ext i j
  unfold bdCore fastLoad
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Fintype.sum_eq_single (ch p) (fun c hc => by simp [Ne.symm hc])]
  by_cases hF : σ p = Role.F <;> simp [hF]

/-- **Invariance.** A boundary system depends on the boundary choice only through the fast and
synchronized load sums of every channel. -/
theorem bdSystem_eq_of_loads (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ)
    (σ σ' : κ → Role) (hF : ∀ c, fastLoad ch r σ c = fastLoad ch r σ' c)
    (hD : ∀ c, bdLoad ch r σ c = bdLoad ch r σ' c) :
    bdSystem B u v ch r σ = bdSystem B u v ch r σ' := by
  unfold bdSystem
  rw [bdCore_eq, bdCore_eq]
  simp_rw [hF]
  congr 1
  funext c
  exact hD c

/-- Integer sum of the pieces of channel `c` with a given role. -/
def roleSum (ch : κ → C) (n : κ → ℕ) (σ : κ → Role) (ρ : Role) (c : C) : ℕ :=
  ∑ p, if ch p = c ∧ σ p = ρ then n p else 0

/-- Integer total of channel `c`. -/
def chanTotal (ch : κ → C) (n : κ → ℕ) (c : C) : ℕ :=
  ∑ p, if ch p = c then n p else 0

theorem roleSum_le (ch : κ → C) (n : κ → ℕ) (σ : κ → Role) (ρ : Role) (c : C) :
    roleSum ch n σ ρ c ≤ chanTotal ch n c := by
  unfold roleSum chanTotal
  refine Finset.sum_le_sum (fun p _ => ?_)
  by_cases hc : ch p = c <;> by_cases hρ : σ p = ρ <;> simp [hc, hρ]

/-- The pair of integer fast and synchronized sums of every channel. -/
def rolePairs (ch : κ → C) (n : κ → ℕ) (σ : κ → Role) : C → ℕ × ℕ :=
  fun c => (roleSum ch n σ Role.F c, roleSum ch n σ Role.D c)

/-- The boundary system determined by channel pairs. -/
def pairSystem (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (δ : ℝ) (P : C → ℕ × ℕ) :
    Matrix (ι ⊕ C) (ι ⊕ C) ℝ :=
  star (fun i j => B i j + ∑ c, δ * ((P c).1 : ℝ) * u c i * v c j) u v id
    (fun c => δ * ((P c).2 : ℝ))

theorem bdSystem_eq_pairSystem (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (δ : ℝ)
    (n : κ → ℕ) (σ : κ → Role) :
    bdSystem B u v ch (fun p => δ * (n p : ℝ)) σ = pairSystem B u v δ (rolePairs ch n σ) := by
  unfold bdSystem pairSystem rolePairs roleSum
  rw [bdCore_eq]
  congr 1
  · funext i j
    congr 1
    refine Finset.sum_congr rfl (fun c _ => ?_)
    unfold fastLoad
    push_cast
    rw [Finset.mul_sum]
    congr 1
    congr 1
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  · funext c
    unfold bdLoad
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp

/-- **Counting.** For loads `δ n_p` the number of distinct boundary systems is at most
`∏_c (N_c + 1)²` with `N_c = Σ_{ch p = c} n_p`. -/
theorem card_bdSystems_le (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (δ : ℝ)
    (n : κ → ℕ) :
    ((Finset.univ : Finset (κ → Role)).image
        (fun σ => bdSystem B u v ch (fun p => δ * (n p : ℝ)) σ)).card ≤
      ∏ c, (chanTotal ch n c + 1) ^ 2 := by
  have himg : (Finset.univ : Finset (κ → Role)).image
      (fun σ => bdSystem B u v ch (fun p => δ * (n p : ℝ)) σ) =
      ((Finset.univ : Finset (κ → Role)).image (rolePairs ch n)).image
        (pairSystem B u v δ) := by
    rw [Finset.image_image]
    congr 1
    funext σ
    exact bdSystem_eq_pairSystem B u v ch δ n σ
  rw [himg]
  refine (Finset.card_image_le).trans ?_
  have hsub : (Finset.univ : Finset (κ → Role)).image (rolePairs ch n) ⊆
      Fintype.piFinset (fun c => Finset.range (chanTotal ch n c + 1) ×ˢ
        Finset.range (chanTotal ch n c + 1)) := by
    intro P hP
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hP
    rw [Fintype.mem_piFinset]
    intro c
    simp only [rolePairs, Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (roleSum_le ch n σ _ c), Nat.lt_succ_of_le (roleSum_le ch n σ _ c)⟩
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Fintype.card_piFinset]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [Finset.card_product, Finset.card_range, sq]

/-- **Reduction to distinct boundary systems (D-semistability, exact).** -/
theorem dUnstable_iff_distinct (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C)
    (r : κ → ℝ) (hr : ∀ p, r p ≠ 0) :
    DUnstable (star B u v ch r) ↔
      ∃ M ∈ (Finset.univ : Finset (κ → Role)).image (bdSystem B u v ch r), DUnstable M := by
  rw [dUnstable_iff B u v ch r hr]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ σ), hσ⟩
  · rintro ⟨M, hM, hU⟩
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hM
    exact ⟨σ, hU⟩

/-- **Reduction to distinct boundary systems (D-stability, sufficient).** -/
theorem dStable_of_distinct (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C)
    (r : κ → ℝ) (hr : ∀ p, r p ≠ 0)
    (h : ∀ M ∈ (Finset.univ : Finset (κ → Role)).image (bdSystem B u v ch r), DStable M) :
    DStable (star B u v ch r) :=
  dStable_of_boundary B u v ch r hr
    (fun σ => h _ (Finset.mem_image_of_mem _ (Finset.mem_univ σ)))

end DStabilityLocalization
