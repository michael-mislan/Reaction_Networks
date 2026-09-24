import proofs.ThermoCoreCompatibility.GeneralCompatibility.ClosedMargin
import Mathlib.Data.Finset.Max

namespace ThermoCoreCompatibility.GeneralCompatibility

def LowerSystem {V E : Type*} (src dst : E → V) (f : E → ℝ → ℝ)
    (lo hi z : V → ℝ) : Prop :=
  (∀ v, lo v ≤ z v ∧ z v ≤ hi v) ∧ ∀ e, f e (z (src e)) ≤ z (dst e)

/-- At a least solution, each coordinate is anchored or has a tight incoming
implication. No continuity is needed for this abstract implication form. -/
theorem active_support_coverage {V E : Type*} [Fintype E]
    (src dst : E → V) (f : E → ℝ → ℝ) (lo hi z : V → ℝ)
    (hlo : ∀ v, 0 ≤ lo v) (hf : ∀ e, MonotoneOn (f e) (Set.Ici 0))
    (hnoloop : ∀ e, src e ≠ dst e)
    (hz : IsLeast {x | LowerSystem src dst f lo hi x} z) (v : V) :
    z v = lo v ∨ ∃ e, dst e = v ∧ z v = f e (z (src e)) := by
  classical
  let S : Finset ℝ := insert (lo v)
    ((Finset.univ.filter (fun e => dst e = v)).image (fun e => f e (z (src e))))
  have hS : S.Nonempty := ⟨lo v, Finset.mem_insert_self _ _⟩
  have hmem (r : ℝ) : r ∈ S ↔ r = lo v ∨ ∃ e, dst e = v ∧ f e (z (src e)) = r := by
    simp [S]
  let a := S.max' hS
  have halo : lo v ≤ a := S.le_max' _ (Finset.mem_insert_self _ _)
  have haz : a ≤ z v := S.max'_le _ _ (by
    intro r hr
    rcases (hmem r).mp hr with h | ⟨e, he, hr⟩
    · simpa [h] using (hz.1.1 v).1
    · rw [← hr, ← he]
      exact hz.1.2 e)
  let y := Function.update z v a
  have hybox : ∀ u, lo u ≤ y u ∧ y u ≤ hi u := by
    intro u
    by_cases hu : u = v
    · subst u
      simpa [y] using And.intro halo (haz.trans (hz.1.1 v).2)
    · simpa [y, hu] using hz.1.1 u
  have hyz : y ≤ z := by
    intro u
    by_cases hu : u = v
    · subst u
      simpa [y] using haz
    · simp [y, hu]
  have hy : LowerSystem src dst f lo hi y := by
    refine ⟨hybox, ?_⟩
    intro e
    by_cases he : dst e = v
    · have hsrc : src e ≠ v := by simpa [he] using hnoloop e
      have hb : f e (z (src e)) ≤ a :=
        S.le_max' _ ((hmem _).mpr (Or.inr ⟨e, he, rfl⟩))
      simpa [y, he, hsrc] using hb
    · have hm := hf e (le_trans (hlo _) (hybox _).1)
        (le_trans (hlo _) (hz.1.1 _).1) (hyz (src e))
      have hb := hm.trans (hz.1.2 e)
      simpa [y, he] using hb
  have hza : z v ≤ a := by simpa [y] using hz.2 hy v
  have heq : z v = a := le_antisymm hza haz
  rcases (hmem a).mp (S.max'_mem hS) with h | ⟨e, he, hr⟩
  · exact Or.inl (heq.trans h)
  · exact Or.inr ⟨e, he, heq.trans hr.symm⟩

end ThermoCoreCompatibility.GeneralCompatibility
