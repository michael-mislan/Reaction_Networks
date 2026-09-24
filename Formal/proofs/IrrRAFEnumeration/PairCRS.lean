import proofs.IrrRAFEnumeration.PairBlockerExplosion
import proofs.RAF.Frankl.ElementaryHorn

namespace IrrRAFEnumeration

open RAF RAF.Frankl

/-- The other reaction in the same two-reaction component. -/
def pairPartner {k : Nat} (r : Fin k × Bool) : Fin k × Bool :=
  (r.1, !r.2)

@[simp] theorem pairPartner_fst {k : Nat} (r : Fin k × Bool) :
    (pairPartner r).1 = r.1 := rfl

@[simp] theorem pairPartner_partner {k : Nat} (r : Fin k × Bool) :
    pairPartner (pairPartner r) = r := by
  ext <;> simp [pairPartner]

theorem pairEdge_fst_eq {k : Nat} (r : Fin k × Bool) :
    pairEdge r.1 = {r, pairPartner r} := by
  rcases r with ⟨i, b⟩
  cases b <;> simp [pairEdge, pairPartner, Finset.pair_comm]

/-- A literal elementary CRS of size `2k`: every reaction has no inputs and
produces its own name as a molecule. -/
def pairCRS (k : Nat) : CRS (Fin k × Bool) (Fin k × Bool) where
  inputs _ := ∅
  outputs r := {r}
  food := ∅

/-- A reaction is catalyzed precisely by its partner's product. -/
def pairCatalysis {k : Nat} : Catalysis (Fin k × Bool) (Fin k × Bool) :=
  fun x r => x = pairPartner r

theorem pairCRS_elementary (k : Nat) : Elementary (pairCRS k) := by
  intro r
  simp [SeedReaction, Enabled, pairCRS]

/-- In the pair CRS, a nonempty set is a RAF exactly when it is closed under
the partner involution. -/
theorem pair_isRAF_iff {k : Nat} (S : Finset (Fin k × Bool)) :
    IsRAF (pairCRS k) pairCatalysis S ↔
      S.Nonempty ∧ ∀ r ∈ S, pairPartner r ∈ S := by
  classical
  rw [isRAF_iff_foodGenerated_and_productGraph]
  constructor
  · rintro ⟨hne, -, hgraph⟩
    refine ⟨hne, ?_⟩
    intro r hr
    rcases hgraph r hr with hfood | ⟨u, hu, x, hx, hcat⟩
    · simp [pairCRS] at hfood
    · have hxu : x = u := by simpa [pairCRS] using hx
      have hxp : x = pairPartner r := hcat
      have hup : u = pairPartner r := hxu.symm.trans hxp
      rwa [← hup]
  · rintro ⟨hne, hclosed⟩
    refine ⟨hne, elementary_foodGenerated (pairCRS k)
      (pairCRS_elementary k) S, ?_⟩
    intro r hr
    exact Or.inr ⟨pairPartner r, hclosed r hr, pairPartner r,
      by simp [pairCRS], rfl⟩

@[simp] theorem pairEdge_partner_closed {k : Nat} (i : Fin k)
    {r : Fin k × Bool} (hr : r ∈ pairEdge i) :
    pairPartner r ∈ pairEdge i := by
  rcases r with ⟨j, b⟩
  simp only [pairEdge, Finset.mem_insert, Finset.mem_singleton] at hr ⊢
  rcases hr with h | h <;> cases h <;> simp [pairPartner]

theorem pairEdge_isRAF {k : Nat} (i : Fin k) :
    IsRAF (pairCRS k) pairCatalysis (pairEdge i) := by
  rw [pair_isRAF_iff]
  exact ⟨by simp [pairEdge], fun r hr => pairEdge_partner_closed i hr⟩

/-- The irreducible RAFs of the compact pair CRS are exactly its `k`
two-reaction components. -/
theorem pair_isIrreducibleRAF_iff {k : Nat} (S : Finset (Fin k × Bool)) :
    MinRAFApprox.SetCoverSource.IsIrreducibleRAF
        (pairCRS k) pairCatalysis S ↔
      ∃ i : Fin k, S = pairEdge i := by
  classical
  constructor
  · rintro ⟨hraf, hmin⟩
    obtain ⟨r, hr⟩ := (pair_isRAF_iff S).mp hraf |>.1
    have hpairsub : pairEdge r.1 ⊆ S := by
      rw [pairEdge_fst_eq]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hr
      · exact (pair_isRAF_iff S).mp hraf |>.2 r hr
    refine ⟨r.1, Finset.Subset.antisymm ?_ hpairsub⟩
    exact hmin (pairEdge r.1) (pairEdge_isRAF r.1) hpairsub
  · rintro ⟨i, rfl⟩
    refine ⟨pairEdge_isRAF i, ?_⟩
    intro B hBraf hBsub
    obtain ⟨r, hrB⟩ := (pair_isRAF_iff B).mp hBraf |>.1
    have hrEdge := hBsub hrB
    rcases r with ⟨j, b⟩
    simp only [pairEdge, Finset.mem_insert, Finset.mem_singleton] at hrEdge
    rcases hrEdge with h | h <;> cases h
    · intro x hx
      simp only [pairEdge, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx <;> cases hx
      · exact hrB
      · simpa [pairPartner] using
          ((pair_isRAF_iff B).mp hBraf |>.2 (i, false) hrB)
    · intro x hx
      simp only [pairEdge, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx <;> cases hx
      · simpa [pairPartner] using
          ((pair_isRAF_iff B).mp hBraf |>.2 (i, true) hrB)
      · exact hrB

theorem pair_irrRAFFamily_eq (k : Nat) :
    irrRAFFamily (pairCRS k) pairCatalysis = pairFamily k := by
  classical
  ext S
  simp only [mem_irrRAFFamily, pair_isIrreducibleRAF_iff, pairFamily,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/-- A size-`2k` literal CRS whose minimal RAF-destroying deletion frontier has
at least `2^k` members. -/
theorem two_pow_le_pairCRS_deletion_frontier (k : Nat) :
    2 ^ k ≤ (blocker (irrRAFFamily (pairCRS k) pairCatalysis)).card := by
  rw [pair_irrRAFFamily_eq]
  exact two_pow_le_pairFamily_blocker_card k

end IrrRAFEnumeration
