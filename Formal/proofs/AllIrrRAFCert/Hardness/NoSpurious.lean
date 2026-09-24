import proofs.AllIrrRAFCert.Hardness.GuardCycles

namespace AllIrrRAFCert.Hardness

open RAF RAF.Frankl
open MinRAFApprox.SetCoverSource (IsIrreducibleRAF)

variable {k n : Nat}

def Compatible (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2)) : Prop :=
  ∀ e, bad e = true → e.1.2 ≠ a e.1.1 ∨ e.2.2 ≠ a e.2.1

def HasClique (bad : Pair k n → Bool) : Prop := ∃ a, Compatible bad a

def Extra (bad : Pair k n → Bool) : Prop :=
  ∃ S, IsIrreducibleRAF (crs bad) cat S ∧ ∀ i, S ≠ guard i

theorem extra_contains_close (bad : Pair k n → Bool) (S : Finset (Rxn k n))
    (hS : IsIrreducibleRAF (crs bad) cat S) (hu : ∀ i, S ≠ guard i) :
    Rxn.close ∈ S := by
  by_contra ht
  obtain ⟨i,hi⟩ := irrRAF_without_close_eq_guard bad S hS ht
  exact hu i hi

theorem extra_avoids_guard (bad : Pair k n → Bool) (S : Finset (Rxn k n))
    (hS : IsIrreducibleRAF (crs bad) cat S) (hu : ∀ i, S ≠ guard i) (i : Fin k) :
    ¬ guard i ⊆ S := by
  intro h
  exact hu i (Finset.Subset.antisymm (hS.2 _ (guard_isRAF bad i) h) h)

theorem close_forces_color (bad : Pair k n → Bool) (S : Finset (Rxn k n))
    (hS : IsRAF (crs bad) cat S) (ht : Rxn.close ∈ S) (i : Fin k) :
    ∃ w, ∀ u, u ≠ w → Rxn.selector (i,u) ∈ S := by
  obtain ⟨t,htin⟩ := hS.2.1 _ ht
  have hb : Mol.colorOK i ∈ closureAt (crs bad) S t :=
    htin (by simp [crs])
  obtain ⟨w,hw⟩ := colorOK_origin bad S hb
  obtain ⟨t',hg⟩ := hS.2.1 _ hw
  refine ⟨w,fun u huw => signal_origin bad S (hg ?_)⟩
  simp [crs,huw]

theorem extra_omission_pattern (bad : Pair k n → Bool) (S : Finset (Rxn k n))
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

theorem close_forces_pair (bad : Pair k n → Bool) (S : Finset (Rxn k n))
    (hS : IsRAF (crs bad) cat S) (ht : Rxn.close ∈ S)
    (e : Pair k n) (he : bad e = true) :
    Rxn.selector e.1 ∈ S ∨ Rxn.selector e.2 ∈ S := by
  obtain ⟨t,htin⟩ := hS.2.1 _ ht
  have hq : Mol.pairOK e ∈ closureAt (crs bad) S t := htin (by simp [crs])
  rcases pairOK_origin bad S hq with hl | hr
  · obtain ⟨j,hj⟩ := hS.2.1 _ hl
    exact Or.inl (signal_origin bad S (hj (by simp [crs,he])))
  · obtain ⟨j,hj⟩ := hS.2.1 _ hr
    exact Or.inr (signal_origin bad S (hj (by simp [crs,he])))

theorem extra_implies_clique (bad : Pair k n → Bool) : Extra bad → HasClique bad := by
  rintro ⟨S,hS,hu⟩
  obtain ⟨a,ha⟩ := extra_omission_pattern bad S hS hu
  refine ⟨a,?_⟩
  intro e he
  have hp := close_forces_pair bad S hS.1 (extra_contains_close bad S hS hu) e he
  exact hp.imp ((ha e.1.1 e.1.2).mp) ((ha e.2.1 e.2.2).mp)

end AllIrrRAFCert.Hardness
