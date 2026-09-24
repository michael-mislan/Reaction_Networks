import proofs.AllIrrRAFCert.WPHardness.GuardPromise
namespace AllIrrRAFCert.WPHardness
open RAF RAF.Frankl
open MinRAFApprox.SetCoverSource (IsIrreducibleRAF)
variable {k n q : Nat}
def Extra (A : System n q) : Prop :=
  ∃ S : Finset (Rxn k n q), IsIrreducibleRAF (crs A) cat S ∧ ∀ i, S ≠ guard i
theorem extra_contains_close (bad : System n q) (S : Finset (Rxn k n q))
    (hS : IsIrreducibleRAF (crs bad) cat S) (hu : ∀ i, S ≠ guard i) :
    Rxn.close ∈ S := by
  by_contra ht
  obtain ⟨i,hi⟩ := irrRAF_without_close_eq_guard bad S hS ht
  exact hu i hi

theorem extra_avoids_guard (bad : System n q) (S : Finset (Rxn k n q))
    (hS : IsIrreducibleRAF (crs bad) cat S) (hu : ∀ i, S ≠ guard i) (i : Fin k) :
    ¬ guard i ⊆ S := by
  intro h
  exact hu i (Finset.Subset.antisymm (hS.2 _ (guard_isRAF bad i) h) h)

theorem close_forces_color (bad : System n q) (S : Finset (Rxn k n q))
    (hS : IsRAF (crs bad) cat S) (ht : Rxn.close ∈ S) (i : Fin k) :
    ∃ w, ∀ u, u ≠ w → Rxn.selector (i,u) ∈ S := by
  obtain ⟨t,htin⟩ := hS.2.1 _ ht
  have hb : Mol.colorOK i ∈ closureAt (crs bad) S t :=
    htin (by simp [crs])
  obtain ⟨w,hw⟩ := colorOK_origin bad S hb
  obtain ⟨t',hg⟩ := hS.2.1 _ hw
  refine ⟨w,fun u huw => signal_origin bad S (hg ?_)⟩
  simp [crs,huw]

theorem extra_omission_pattern (bad : System n q) (S : Finset (Rxn k n q))
    (hS : IsIrreducibleRAF (crs bad) cat S) (hu : ∀ i, S ≠ guard i) :
    ∃ a : Fin k → Fin (n + 2), ∀ i u, Rxn.selector (i,u) ∈ S ↔ u ≠ a i := by
  classical
  have ht := extra_contains_close bad S hS hu
  choose a ha using close_forces_color bad S hS.1 ht
  refine ⟨a,?_⟩
  intro i u
  have hmissing : Rxn.selector (i,a i) ∉ S := by
    intro hm
    apply extra_avoids_guard bad S hS hu i
    intro r hr
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hr
    by_cases hw : w = a i
    · simpa [hw] using hm
    · exact ha i w hw
  exact ⟨fun h he => hmissing (by simpa [he] using h), ha i u⟩


end AllIrrRAFCert.WPHardness
