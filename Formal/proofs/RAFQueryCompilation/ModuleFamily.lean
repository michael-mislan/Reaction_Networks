import proofs.RAFQueryCompilation.PruningWork

namespace RAFQueryCompilation.ModuleFamily
open RAF

abbrev Reaction (n : ℕ) := Option (Fin n × Bool)
abbrev Molecule (n : ℕ) := Option (Reaction n)

/-- A food-to-hub reaction feeds arbitrarily many mutually catalysing pairs. -/
def source (n : ℕ) : CRS (Molecule n) (Reaction n) where
  inputs r := {if r = none then none else some none}
  outputs r := {some r}
  food := {none}

def catalysis {n : ℕ} (x : Molecule n) (r : Reaction n) : Prop :=
  x = match r with
    | none => none
    | some (i,b) => some (some (i,!b))

instance {n : ℕ} (x : Molecule n) (r : Reaction n) : Decidable (catalysis x r) :=
  inferInstanceAs (Decidable (x = _))

def region {n : ℕ} (i : Fin n) : Finset (Reaction n) :=
  {some (i,false), some (i,true)}

theorem region_card {n : ℕ} (i : Fin n) : (region i).card = 2 := by
  simp [region]

theorem reaction_card (n : ℕ) : Fintype.card (Reaction n) = 2*n+1 := by
  simp [Reaction, Nat.mul_comm]

/-- Every reaction is incident with the same nonfood hub, so the reaction
incidence graph is connected, even though downstream modules remain local. -/
theorem hub_incident {n : ℕ} (r : Reaction n) :
    some none ∈ (source n).inputs r ∪ (source n).outputs r := by
  cases r <;> simp [source]

theorem region_independent {n : ℕ} (i : Fin n) :
    OutsideIndependent (source n) catalysis (region i) := by
  intro e he r hr x hx hs
  simp only [source, Finset.mem_singleton] at hx
  subst x
  simp only [region, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with he | he <;> subst e
  · cases r with
    | none => simp [source, catalysis] at hs
    | some p =>
      rcases p with ⟨j,b⟩
      cases b <;> simp_all [source, catalysis, region]
  · cases r with
    | none => simp [source, catalysis] at hs
    | some p =>
      rcases p with ⟨j,b⟩
      cases b <;> simp_all [source, catalysis, region]

/-- Literal unit-stoichiometry column; catalysts are annotations, not net inputs. -/
def column {n : ℕ} (r : Reaction n) (x : Molecule n) : ℝ :=
  (if x ∈ (source n).outputs r then 1 else 0) -
  (if x ∈ (source n).inputs r then 1 else 0)

theorem own_product {n : ℕ} (r : Reaction n) : column r (some r) = 1 := by
  cases r <;> simp [column, source]

theorem other_product_nonpositive {n : ℕ} {r s : Reaction n} (h : r ≠ s) :
    column s (some r) ≤ 0 := by
  simp only [column, source, Finset.mem_singleton, Option.some.injEq, if_neg h]
  split_ifs <;> norm_num

theorem no_common_positive_ray {n : ℕ} {r s : Reaction n} (h : r ≠ s)
    {a : ℝ} (ha : 0 < a) : ¬ (∀ x, column r x = a * column s x) := by
  intro he
  have hn := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha)
    (other_product_nonpositive h)
  have hh := he (some r)
  rw [own_product] at hh
  linarith

/-- The general localization theorem applies to every availability context of
this family; it does not assume that the old answer contains every module. -/
theorem family_update {n : ℕ} (i : Fin n) (A B : Finset (Reaction n))
    (h : A \ region i = B \ region i) :
    evaluate (source n) catalysis B =
      (evaluate (source n) catalysis A \ region i) ∪
      evaluate (residualSource (source n) (evaluate (source n) catalysis A \ region i))
        catalysis (B ∩ region i) :=
  evaluate_cone_update (source n) catalysis A B (region i) (region_independent i) h

/-- A local checker needs at most three rounds on this unbounded family,
regardless of its boundary food, old availability, or malformed certificate. -/
theorem family_rounds {n : ℕ} (i : Fin n) (A : Finset (Reaction n))
    (food : Finset (Molecule n)) (cert : List (List (Reaction n))) :
    pruningRounds {source n with food := food} catalysis (A ∩ region i) cert ≤ 3 := by
  have hc : (A ∩ region i).card ≤ 2 := by
    simpa only [region_card] using
      Finset.card_le_card (Finset.inter_subset_right : A ∩ region i ⊆ region i)
  have hr := pruningRounds_le {source n with food := food} catalysis cert (A ∩ region i)
  omega

theorem family_rows {n : ℕ} (i : Fin n) (A : Finset (Reaction n))
    (food : Finset (Molecule n)) (cert : List (List (Reaction n))) :
    pruningRows {source n with food := food} catalysis (A ∩ region i) cert ≤ 6 := by
  have hc : (A ∩ region i).card ≤ 2 := by
    simpa only [region_card] using
      Finset.card_le_card (Finset.inter_subset_right : A ∩ region i ⊆ region i)
  have hr := pruningRows_le_rounds {source n with food := food} catalysis cert (A ∩ region i)
  have hb := family_rounds i A food cert
  nlinarith

end RAFQueryCompilation.ModuleFamily
