import proofs.AllIrrRAFCert.WPHardness.Source
import proofs.IrrRAFEnumeration.Irreducibility

namespace AllIrrRAFCert.WPHardness

open RAF RAF.Frankl
open MinRAFApprox.SetCoverSource (IsIrreducibleRAF)

variable {k n q : Nat} (bad : System n q)

theorem selector_foodGenerated (S : Finset (Rxn k n q))
    (hS : ∀ r ∈ S, ∃ v, r = Rxn.selector v) : FoodGenerated (crs bad) S := by
  intro r hr
  obtain ⟨v,rfl⟩ := hS r hr
  exact ⟨0, Finset.Subset.rfl⟩

theorem guard_isRAF (i : Fin k) : IsRAF (crs bad) cat (guard (n := n) (q := q) i) := by
  have hfg : FoodGenerated (crs bad) (guard (n := n) (q := q) i) := by
    apply selector_foodGenerated
    intro r hr
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨(i,w),rfl⟩
  refine ⟨⟨Rxn.selector (i,0), by simp⟩,hfg,?_⟩
  intro r hr
  obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hr
  apply (catalyzedFromClosure_iff_productGraph (crs bad) cat hfg _).mpr
  exact Or.inr ⟨Rxn.selector (next (i,w)), by simp [next],
    Mol.guardCat (next (i,w)), by simp [crs], rfl⟩

theorem no_close_selector (S : Finset (Rxn k n q))
    (hS : IsRAF (crs bad) cat S) (ht : Rxn.close ∉ S)
    {r : Rxn k n q} (hr : r ∈ S) : ∃ v, r = Rxn.selector v := by
  obtain ⟨x,t,hx,hc⟩ := hS.2.2 r hr
  cases x with
  | globalCat => exact (ht (globalCat_origin bad S hx)).elim
  | guardCat v =>
    cases r <;> simp [cat] at hc
    exact ⟨_,rfl⟩
  | food => simp [cat] at hc
  | signal v => simp [cat] at hc
  | colorOK i => simp [cat] at hc
  | statement e => simp [cat] at hc

theorem no_close_next (S : Finset (Rxn k n q))
    (hS : IsRAF (crs bad) cat S) (ht : Rxn.close ∉ S)
    {v : Vertex k n} (hv : Rxn.selector v ∈ S) : Rxn.selector (next v) ∈ S := by
  obtain ⟨x,t,hx,hc⟩ := hS.2.2 _ hv
  cases x with
  | globalCat => exact (ht (globalCat_origin bad S hx)).elim
  | guardCat u =>
    change u = next v at hc
    subst u
    exact guardCat_origin bad S hx
  | food => simp [cat] at hc
  | signal u => simp [cat] at hc
  | colorOK i => simp [cat] at hc
  | statement e => simp [cat] at hc

theorem no_close_contains_guard (S : Finset (Rxn k n q))
    (hS : IsRAF (crs bad) cat S) (ht : Rxn.close ∉ S)
    {v : Vertex k n} (hv : Rxn.selector v ∈ S) : guard v.1 ⊆ S := by
  have hall : ∀ w, Rxn.selector (v.1,w) ∈ S :=
    IrrRAFEnumeration.CircuitSource.cyclic_all
      (fun w => Rxn.selector (v.1,w) ∈ S)
      (fun w hw => no_close_next bad S hS ht hw) hv
  intro r hr
  obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hr
  exact hall w

theorem guard_isIrrRAF (i : Fin k) :
    IsIrreducibleRAF (crs bad) cat (guard (n := n) (q := q) i) := by
  refine ⟨guard_isRAF bad i,?_⟩
  intro S hS hsub
  have ht : Rxn.close ∉ S := fun h => close_not_mem_guard i (hsub h)
  obtain ⟨r,hr⟩ := hS.1
  obtain ⟨v,rfl⟩ := no_close_selector bad S hS ht hr
  have hi := (selector_mem_guard i v).mp (hsub hr)
  simpa [hi] using no_close_contains_guard bad S hS ht hr

theorem irrRAF_without_close_eq_guard (S : Finset (Rxn k n q))
    (hS : IsIrreducibleRAF (crs bad) cat S) (ht : Rxn.close ∉ S) :
    ∃ i, S = guard i := by
  obtain ⟨r,hr⟩ := hS.1.1
  obtain ⟨v,rfl⟩ := no_close_selector bad S hS.1 ht hr
  have hsub := no_close_contains_guard bad S hS.1 ht hr
  exact ⟨v.1, Finset.Subset.antisymm
    (hS.2 _ (guard_isRAF bad _) hsub) hsub⟩

theorem guards_injective : Function.Injective (guard (k := k) (n := n) (q := q)) := by
  intro i j h
  have hi : Rxn.selector (i,0) ∈ guard (n := n) (q := q) i := by simp
  rw [h] at hi
  exact (selector_mem_guard j (i,0)).mp hi

end AllIrrRAFCert.WPHardness
