import proofs.RAFReactionCriticality.Pivotality
import proofs.RAFReactionCriticality.LossClosure

namespace RAFReactionCriticality.CatalyticModules
open RAF RAFQueryCompilation FunctionalSource FiniteThinning
open scoped BigOperators
variable {J : Type*} (length : J → ℕ)

/-- Module j has length `length j + 1`, so every declared module is nonempty. -/
abbrev Reaction := (j : J) × ZMod (length j + 1)

def parent (r : Reaction length) : Reaction length := ⟨r.1, r.2 + 1⟩

noncomputable def moduleSet (j : J) : Finset (Reaction length) :=
  Finset.univ.map (Function.Embedding.sigmaMk j)

theorem iterate_parent (j : J) (x : ZMod (length j + 1)) (k : ℕ) :
    (parent length)^[k] ⟨j,x⟩ = ⟨j, x + k⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [parent, Nat.cast_add, add_assoc]

theorem mem_moduleSet (j : J) (r : Reaction length) :
    r ∈ moduleSet length j ↔ r.1 = j := by
  classical
  constructor
  · intro hr
    obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hr
    exact (congrArg Sigma.fst hx).symm
  · intro hr
    rcases r with ⟨k,x⟩
    dsimp at hr
    subst k
    exact Finset.mem_map.mpr ⟨x, Finset.mem_univ _, rfl⟩

theorem module_card (j : J) : (moduleSet length j).card = length j + 1 := by
  simp [moduleSet, ZMod.card]

variable [Fintype J]

theorem orbit_eq_module (r : Reaction length) :
    orbitSet (parent length) r = moduleSet length r.1 := by
  classical
  rcases r with ⟨j,x⟩
  ext t
  simp only [orbitSet, Finset.mem_filter, Finset.mem_univ, true_and, mem_moduleSet]
  constructor
  · rintro ⟨k,hk⟩
    rw [iterate_parent] at hk
    exact (congrArg Sigma.fst hk).symm
  · intro ht
    rcases t with ⟨j',y⟩
    dsimp at ht
    subst j'
    refine ⟨(y-x).val, ?_⟩
    rw [iterate_parent, ZMod.natCast_zmod_val]
    congr 1
    abel

variable [DecidableEq J]

theorem singleton_loss (r : Reaction length) :
    loss source (catalysts (parent length)) Finset.univ {r} = moduleSet length r.1 := by
  classical
  ext t
  simp only [loss, Finset.mem_sdiff, Finset.mem_univ, true_and, deletion_iff,
    Finset.mem_singleton]
  have h : (∃ k : ℕ, (parent length)^[k] t = r) ↔
      r ∈ orbitSet (parent length) t := by simp [orbitSet]
  rw [h, orbit_eq_module, mem_moduleSet, mem_moduleSet]
  exact eq_comm

theorem singleton_loss_card (r : Reaction length) :
    (loss source (catalysts (parent length)) Finset.univ {r}).card = length r.1 + 1 := by
  rw [singleton_loss, module_card]

theorem target_probability (r : Reaction length) (p : ℝ) :
    targetProbability (parent length) (parent length) r p = p^(length r.1+1) := by
  have h := redundant_target_probability (parent length) (parent length) r
    (fun _ _ => rfl) r p
  simpa only [orbit_eq_module, Finset.union_self, module_card, add_sub_cancel_right] using h

/-- Exact mean robustness curve for an arbitrary finite family of catalytic cycles. -/
theorem mean_size (p : ℝ) :
    expectedSize (parent length) (parent length) p =
      ∑ j, ((length j + 1 : ℕ) : ℝ) * p^(length j+1) := by
  rw [expectedSize_eq_sum_targets, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simp only [target_probability, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul]

/-- Counting reactions, rather than modules, produces the exact size bias. -/
theorem size_bias_count (k : ℕ) :
    (Finset.univ.filter (fun r : Reaction length =>
      (loss source (catalysts (parent length)) Finset.univ {r}).card = k)).card =
      k * (Finset.univ.filter (fun j : J => length j + 1 = k)).card := by
  classical
  have hc : (Finset.univ.filter (fun r : Reaction length => length r.1+1=k)).card =
      ∑ j : J, if length j+1=k then length j+1 else 0 := by
    have hb : (Finset.univ.filter (fun r : Reaction length => length r.1+1=k)).card =
        ∑ r : Reaction length, if length r.1+1=k then 1 else 0 := by simp
    rw [hb, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : length j+1=k <;> simp [hj, ZMod.card]
  simp_rw [singleton_loss_card]
  rw [hc]
  calc
    (∑ j : J, if length j+1=k then length j+1 else 0) =
        ∑ j : J, if length j+1=k then k else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      split <;> simp_all
    _ = k * (Finset.univ.filter (fun j : J => length j+1=k)).card := by
      simp [Finset.sum_ite, mul_comm]

end RAFReactionCriticality.CatalyticModules
