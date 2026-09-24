import proofs.AllIrrRAFCert.Hardness.NoSpurious
import proofs.IrrRAFEnumeration.FiniteDuality

namespace AllIrrRAFCert.Hardness

open RAF RAF.Frankl

variable {k n : Nat}

def chosen (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2)) : Rxn k n → Prop
  | .selector v => v.2 ≠ a v.1
  | .colorGate v => v.2 = a v.1
  | .pairLeft e => bad e = false ∨ e.1.2 ≠ a e.1.1
  | .pairRight e => bad e = false ∨ e.2.2 ≠ a e.2.1
  | .close => True

noncomputable def witness (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2)) :
    Finset (Rxn k n) := by
  classical
  exact Finset.univ.filter (chosen bad a)

@[simp] theorem mem_witness (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2))
    (r : Rxn k n) : r ∈ witness bad a ↔ chosen bad a r := by
  classical
  simp [witness]

theorem emit (Q : CRS (Mol k n) (Rxn k n)) (S : Finset (Rxn k n))
    {r : Rxn k n} {x : Mol k n} {t : Nat} (hr : r ∈ S)
    (hi : Q.inputs r ⊆ closureAt Q S t) (ho : x ∈ Q.outputs r) :
    x ∈ closureAt Q S (t+1) := by
  have he : Enabled Q (closureAt Q S t) r := hi
  simp only [closureAt,closureStep,Finset.mem_union,Finset.mem_biUnion]
  exact Or.inr ⟨r,hr,by simpa [he] using ho⟩

theorem persist (Q : CRS (Mol k n) (Rxn k n)) (S : Finset (Rxn k n)) (t : Nat) :
    closureAt Q S t ⊆ closureAt Q S (t+1) := by
  exact Finset.subset_union_left

theorem food_stage (bad : Pair k n → Bool) (S : Finset (Rxn k n)) (t : Nat) :
    Mol.food ∈ closureAt (crs bad) S t := by
  induction t with
  | zero => simp [closureAt,crs]
  | succ t ih => exact persist _ _ t ih

theorem witness_signal (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2))
    (v : Vertex k n) (hv : v.2 ≠ a v.1) :
    Mol.signal v ∈ closureAt (crs bad) (witness bad a) 1 := by
  apply emit (r := .selector v)
  · simpa [chosen] using hv
  · exact Finset.Subset.rfl
  · simp [crs]

theorem witness_color_inputs (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2))
    (i : Fin k) : (crs bad).inputs (.colorGate (i,a i)) ⊆
      closureAt (crs bad) (witness bad a) 1 := by
  intro x hx
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
  exact witness_signal bad a (i,w) (Finset.mem_erase.mp hw).1

theorem witness_color (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2))
    (i : Fin k) : Mol.colorOK i ∈ closureAt (crs bad) (witness bad a) 2 := by
  apply emit (r := .colorGate (i,a i))
  · simp [chosen]
  · exact witness_color_inputs bad a i
  · simp [crs]

theorem witness_left_inputs (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2))
    (e : Pair k n) (h : chosen bad a (.pairLeft e)) :
    (crs bad).inputs (.pairLeft e) ⊆ closureAt (crs bad) (witness bad a) 1 := by
  cases he : bad e with
  | false => simpa [crs,he] using food_stage bad (witness bad a) 1
  | true =>
    have hv : e.1.2 ≠ a e.1.1 := by simpa [chosen,he] using h
    simpa [crs,he] using witness_signal bad a e.1 hv

theorem witness_right_inputs (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2))
    (e : Pair k n) (h : chosen bad a (.pairRight e)) :
    (crs bad).inputs (.pairRight e) ⊆ closureAt (crs bad) (witness bad a) 1 := by
  cases he : bad e with
  | false => simpa [crs,he] using food_stage bad (witness bad a) 1
  | true =>
    have hv : e.2.2 ≠ a e.2.1 := by simpa [chosen,he] using h
    simpa [crs,he] using witness_signal bad a e.2 hv

theorem witness_pair (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2))
    (ha : Compatible bad a) (e : Pair k n) :
    Mol.pairOK e ∈ closureAt (crs bad) (witness bad a) 2 := by
  have hchoice : chosen bad a (.pairLeft e) ∨ chosen bad a (.pairRight e) := by
    cases he : bad e with
    | false => simp [chosen,he]
    | true => simpa [chosen,he] using ha e he
  rcases hchoice with hl | hr
  · exact emit _ _ ((mem_witness _ _ _).mpr hl)
      (witness_left_inputs bad a e hl) (by simp [crs])
  · exact emit _ _ ((mem_witness _ _ _).mpr hr)
      (witness_right_inputs bad a e hr) (by simp [crs])

theorem witness_close_inputs (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2))
    (ha : Compatible bad a) : (crs bad).inputs .close ⊆
      closureAt (crs bad) (witness bad a) 2 := by
  intro x hx
  rcases Finset.mem_union.mp hx with hc | hp
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
    exact witness_color bad a i
  · obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hp
    exact witness_pair bad a ha e

theorem witness_isRAF (bad : Pair k n → Bool) (a : Fin k → Fin (n + 2))
    (ha : Compatible bad a) : IsRAF (crs bad) cat (witness bad a) := by
  have ht : Rxn.close ∈ witness bad a := by simp [chosen]
  have hz : Mol.globalCat ∈ closureAt (crs bad) (witness bad a) 3 :=
    emit _ _ ht (witness_close_inputs bad a ha) (by simp [crs])
  refine ⟨⟨_,ht⟩,?_,?_⟩
  · intro r hr
    have hc := (mem_witness _ _ _).mp hr
    cases r with
    | selector v => exact ⟨0,Finset.Subset.rfl⟩
    | colorGate v =>
      have hv : v.2 = a v.1 := hc
      exact ⟨1,by simpa [crs,hv] using witness_color_inputs bad a v.1⟩
    | pairLeft e => exact ⟨1,witness_left_inputs bad a e hc⟩
    | pairRight e => exact ⟨1,witness_right_inputs bad a e hc⟩
    | close => exact ⟨2,witness_close_inputs bad a ha⟩
  · intro r _
    exact ⟨Mol.globalCat,3,hz,trivial⟩

theorem clique_implies_extra (bad : Pair k n → Bool) : HasClique bad → Extra bad := by
  classical
  rintro ⟨a,ha⟩
  obtain ⟨S,hsub,hmin⟩ := IrrRAFEnumeration.exists_minimal_subset
    (IsRAF (crs bad) cat) (witness_isRAF bad a ha)
  refine ⟨S,hmin,?_⟩
  intro i he
  have hm : Rxn.selector (i,a i) ∈ S := by rw [he]; simp
  have := hsub hm
  simp [chosen] at this

theorem clique_iff_extra (bad : Pair k n → Bool) : HasClique bad ↔ Extra bad :=
  ⟨clique_implies_extra bad,extra_implies_clique bad⟩

end AllIrrRAFCert.Hardness
