import proofs.RAF.Frankl.SupplierCoreAbundance

namespace RAF.Frankl
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

def InternalSubstrateRank (Q : CRS M R) (U : Finset R) (rank : R → ℕ) : Prop :=
  ∀ p ∈ U, ∀ r ∈ U, ∀ x, x ∈ Q.outputs p → x ∈ Q.inputs r →
    x ∉ Q.food → rank p < rank r

def closureExterior (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (S : Finset {r // r ∈ U}) : Prop :=
  ∀ t ∈ T, Supported Q C (fromRestricted S ∪ T) t

omit [Fintype R] in
theorem closureExterior_mono (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) {A B : Finset {r // r ∈ U}} (hab : A ⊆ B) :
    closureExterior Q C U T A → closureExterior Q C U T B := by
  intro ha t ht
  exact supported_mono Q C
    (Finset.union_subset_union (fromRestricted_mono hab) (Finset.Subset.refl T)) (ha t ht)

omit [Fintype R] in
theorem internal_rank_foodGenerated (Q : CRS M R) (U : Finset R) (rank : R → ℕ)
    (hrank : InternalSubstrateRank Q U rank) (S T : Finset R) (hSU : S ⊆ U)
    (hT : ∀ t ∈ T, ∃ k, Q.inputs t ⊆ closureAt Q (S ∪ T) k)
    (hS : ∀ r ∈ S, ∀ x ∈ Q.inputs r, x ∉ Q.food →
      ∃ p ∈ S ∪ T, x ∈ Q.outputs p) : FoodGenerated Q (S ∪ T) := by
  classical
  let k : R → ℕ := fun t => if ht : t ∈ T then Nat.find (hT t ht) else 0
  let K := T.sup k
  have hk : ∀ t ∈ T, Q.inputs t ⊆ closureAt Q (S ∪ T) K := by
    intro t ht
    have hle : k t ≤ K := Finset.le_sup (f := k) ht
    have hen : Q.inputs t ⊆ closureAt Q (S ∪ T) (k t) := by
      simpa [k,ht] using Nat.find_spec (hT t ht)
    exact fun x hx => ranked_closure_mono Q (S ∪ T) hle (hen hx)
  have hout : ∀ t ∈ T, ∀ x ∈ Q.outputs t, x ∈ closureAt Q (S ∪ T) (K+1) := by
    intro t ht x hx
    have he : Enabled Q (closureAt Q (S ∪ T) K) t := hk t ht
    change x ∈ closureStep Q (S ∪ T) (closureAt Q (S ∪ T) K)
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_union_right S ht,by simpa only [if_pos he] using hx⟩
  have hen : ∀ n r, rank r = n → r ∈ S →
      Q.inputs r ⊆ closureAt Q (S ∪ T) (K+n+1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro r he hr x hx
      by_cases hf : x ∈ Q.food
      · exact ranked_closure_mono Q (S ∪ T) (Nat.zero_le _) hf
      · obtain ⟨p,hp,ho⟩ := hS r hr x hx hf
        rcases Finset.mem_union.mp hp with hp | hp
        · have hlt : rank p < n := he ▸ hrank p (hSU hp) r (hSU hr) x ho hx hf
          have hEnabled : Enabled Q (closureAt Q (S ∪ T) (K+rank p+1)) p :=
            ih (rank p) hlt p rfl hp
          have hm : x ∈ closureAt Q (S ∪ T) (K+rank p+1+1) := by
            change x ∈ closureStep Q (S ∪ T) (closureAt Q (S ∪ T) (K+rank p+1))
            apply Finset.mem_union_right
            exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_union_left T hp,by simpa only [if_pos hEnabled] using ho⟩
          exact ranked_closure_mono Q (S ∪ T) (by omega) hm
        · exact ranked_closure_mono Q (S ∪ T) (by omega) (hout p hp x ho)
  intro r hr
  rcases Finset.mem_union.mp hr with hr | hr
  · exact ⟨K+rank r+1,hen (rank r) r rfl hr⟩
  · exact ⟨K,hk r hr⟩

theorem local_rank_fibre_iff (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (rank : R → ℕ) (hrank : InternalSubstrateRank Q U rank)
    (T : Finset R) (S : Finset {r // r ∈ U}) :
    fromRestricted S ∪ T ∈ fixedFamily Q C ↔
      closureExterior Q C U T S ∧
        ∀ r ∈ S, LocalSupply Q C (fromRestricted S ∪ T) r.1 := by
  rw [fixedFamily_iff_food_support]
  constructor
  · rintro ⟨hfg,hcat⟩
    refine ⟨?_,?_⟩
    · intro t ht
      have hm := Finset.mem_union_right (fromRestricted S) ht
      exact ⟨hfg t hm,(catalyzedFromClosure_iff_productGraph Q C hfg t).mpr (hcat t hm)⟩
    · intro r hr
      have hm := Finset.mem_union_left T ((mem_fromRestricted S r.1).mpr ⟨r.2,hr⟩)
      refine ⟨?_,hcat r.1 hm⟩
      intro x hx hn
      obtain ⟨k,hk⟩ := hfg r.1 hm
      exact (mem_closureAt_imp_food_or_output Q _ (hk hx)).resolve_left hn
  · rintro ⟨he,hs⟩
    have hfg : FoodGenerated Q (fromRestricted S ∪ T) := by
      apply internal_rank_foodGenerated Q U rank hrank (fromRestricted S) T
      · intro r hr
        exact ((mem_fromRestricted S r).mp hr).1
      · exact fun t ht => (he t ht).1
      · intro r hr
        obtain ⟨hu,hr⟩ := (mem_fromRestricted S r).mp hr
        exact (hs ⟨r,hu⟩ hr).1
    refine ⟨hfg,?_⟩
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨hu,hr⟩ := (mem_fromRestricted S r).mp hr
      exact (hs ⟨r,hu⟩ hr).2
    · exact (catalyzedFromClosure_iff_productGraph Q C hfg r).mp (he r hr).2

end RAF.Frankl
