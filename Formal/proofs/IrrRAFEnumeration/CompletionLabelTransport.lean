import proofs.IrrRAFEnumeration.CompletionOriginalApplication

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

variable {M R : Type} [DecidableEq M] [DecidableEq R] {d r : Nat}

def indexedCRS (Q : CRS M R) (em : M ≃ Fin d) (er : R ≃ Fin r) : CRS (Fin d) (Fin r) where
  inputs j := (Q.inputs (er.symm j)).map em.toEmbedding
  outputs j := (Q.outputs (er.symm j)).map em.toEmbedding
  food := Q.food.map em.toEmbedding

def indexedCatalysis (C : Catalysis M R) (em : M ≃ Fin d) (er : R ≃ Fin r) :
    Catalysis (Fin d) (Fin r) := fun x j => C (em.symm x) (er.symm j)

instance indexedCatalysis_decidable (C : Catalysis M R) [DecidableRel C]
    (em : M ≃ Fin d) (er : R ≃ Fin r) : DecidableRel (indexedCatalysis C em er) :=
  fun _ _ => inferInstanceAs (Decidable (C _ _))

omit [DecidableEq R] in
theorem closureStep_mem_iff (Q : CRS M R) (S : Finset R) (A : Finset M) (x : M) :
    x ∈ closureStep Q S A ↔ x ∈ A ∨ ∃ j ∈ S, Enabled Q A j ∧ x ∈ Q.outputs j := by
  simp only [closureStep,Finset.mem_union,Finset.mem_biUnion]
  apply or_congr Iff.rfl
  apply exists_congr
  intro j
  by_cases h : Enabled Q A j <;> simp [h]

omit [DecidableEq R] in
theorem indexedClosure_mem (Q : CRS M R) (em : M ≃ Fin d) (er : R ≃ Fin r)
    (S : Finset R) (k : Nat) (x : M) :
    em x ∈ closureAt (indexedCRS Q em er) (S.map er.toEmbedding) k ↔
      x ∈ closureAt Q S k := by
  induction k generalizing x with
  | zero => simp [closureAt,indexedCRS]
  | succ k ih =>
    have hen (j : Fin r) :
        Enabled (indexedCRS Q em er)
          (closureAt (indexedCRS Q em er) (S.map er.toEmbedding) k) j ↔
        Enabled Q (closureAt Q S k) (er.symm j) := by
      constructor
      · intro h y hy
        exact (ih y).mp (h (by simpa [indexedCRS] using hy))
      · intro h y hy
        have hm : em.symm y ∈ Q.inputs (er.symm j) := by simpa [indexedCRS] using hy
        have hh := (ih (em.symm y)).mpr (h hm)
        simpa using hh
    simp only [closureAt,closureStep_mem_iff]
    apply or_congr (ih x)
    constructor
    · rintro ⟨j,hj,he,hx⟩
      exact ⟨er.symm j,by simpa using hj,(hen j).mp he,by simpa [indexedCRS] using hx⟩
    · rintro ⟨j,hj,he,hx⟩
      refine ⟨er j,by simpa using hj,(hen (er j)).mpr (by simpa using he),?_⟩
      simpa [indexedCRS] using hx

omit [DecidableEq R] in
theorem indexedRAF_iff (Q : CRS M R) (C : Catalysis M R)
    (em : M ≃ Fin d) (er : R ≃ Fin r) (S : Finset R) :
    IsRAF (indexedCRS Q em er) (indexedCatalysis C em er) (S.map er.toEmbedding) ↔
      IsRAF Q C S := by
  constructor
  · rintro ⟨hn,hfood,hcat⟩
    refine ⟨Finset.map_nonempty.mp hn,?_,?_⟩
    · intro j hj
      obtain ⟨k,hk⟩ := hfood (er j) (by simpa using hj)
      refine ⟨k,fun x hx => (indexedClosure_mem Q em er S k x).mp (hk ?_)⟩
      simpa [indexedCRS] using hx
    · intro j hj
      obtain ⟨x,k,hx,hc⟩ := hcat (er j) (by simpa using hj)
      refine ⟨em.symm x,k,(indexedClosure_mem Q em er S k _).mp (by simpa using hx),?_⟩
      simpa [indexedCatalysis] using hc
  · rintro ⟨hn,hfood,hcat⟩
    refine ⟨Finset.map_nonempty.mpr hn,?_,?_⟩
    · intro j hj
      obtain ⟨k,hk⟩ := hfood (er.symm j) (by simpa using hj)
      refine ⟨k,?_⟩
      intro x hx
      have hm : em.symm x ∈ Q.inputs (er.symm j) := by simpa [indexedCRS] using hx
      simpa using (indexedClosure_mem Q em er S k (em.symm x)).mpr (hk hm)
    · intro j hj
      obtain ⟨x,k,hx,hc⟩ := hcat (er.symm j) (by simpa using hj)
      exact ⟨em x,k,(indexedClosure_mem Q em er S k x).mpr hx,by simpa [indexedCatalysis] using hc⟩

theorem indexedIrreducible_iff (Q : CRS M R) (C : Catalysis M R)
    (em : M ≃ Fin d) (er : R ≃ Fin r) (S : Finset R) :
    MinRAFApprox.SetCoverSource.IsIrreducibleRAF
      (indexedCRS Q em er) (indexedCatalysis C em er) (er.finsetCongr S) ↔
    MinRAFApprox.SetCoverSource.IsIrreducibleRAF Q C S := by
  constructor
  · rintro ⟨hr,hm⟩
    refine ⟨(indexedRAF_iff Q C em er S).mp hr,?_⟩
    intro B hB hBS
    exact Finset.map_subset_map.mp (hm (B.map er.toEmbedding)
      ((indexedRAF_iff Q C em er B).mpr hB) (Finset.map_subset_map.mpr hBS))
  · rintro ⟨hr,hm⟩
    refine ⟨(indexedRAF_iff Q C em er S).mpr hr,?_⟩
    intro B hB hBS
    obtain ⟨A,rfl⟩ := er.finsetCongr.surjective B
    exact Finset.map_subset_map.mpr (hm A ((indexedRAF_iff Q C em er A).mp hB)
      (Finset.map_subset_map.mp hBS))

omit [DecidableEq R] in
theorem indexedInput_eq (Q : CRS M R) (C : Catalysis M R) [DecidableRel C]
    (em : M ≃ Fin d) (er : R ≃ Fin r) :
    inputBits (indexedCRS Q em er) (indexedCatalysis C em er) (Equiv.refl _) (Equiv.refl _) =
      inputBits Q C em er := by
  have hi : ∀ s, incidence (indexedCRS Q em er) (indexedCatalysis C em er)
      (Equiv.refl _) (Equiv.refl _) s = incidence Q C em er s := by
    intro s
    cases s with
    | inl x => simp [incidence,indexedCRS]
    | inr v =>
      rcases v with ⟨j,c,x⟩
      simp [incidence,indexedCRS,indexedCatalysis]
      split_ifs <;> exact decide_eq_decide.mpr Iff.rfl
  simp only [inputBits,hi]

theorem indexedOutput_eq (er : R ≃ Fin r) (rows : List (Finset (Fin r))) :
    outputBits er (rows.map er.finsetCongr.symm) = outputBits (Equiv.refl _) rows := by
  simp [outputBits,outputBody,List.flatMap_map,Equiv.finsetCongr_symm]
  congr 1

/-- Relabeling changes interpretation only: both input and output byte strings
and the actual run are unchanged. Reaction identity is preserved bijectively. -/
theorem enumerates_of_finEnumerates {n : Nat} (E : TM n) (p : Polynomial Nat)
    (hE : FinEnumerates E p) : Enumerates E p := by
  intro M R _ _ _ d r em er Q C _
  obtain ⟨rows,c,t,hnd,hrows,ht,hr,hh,ho⟩ :=
    hE d r (indexedCRS Q em er) (indexedCatalysis C em er)
  let back := er.finsetCongr.symm
  have hf : (rows.map back).toFinset = irrRAFFamily Q C := by
    ext S
    simp only [List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨T,hT,he⟩
      have htmem : T ∈ irrRAFFamily (indexedCRS Q em er) (indexedCatalysis C em er) := by
        rw [← hrows]; exact List.mem_toFinset.mpr hT
      have he' : T = er.finsetCongr S := by
        rw [← he]
        exact (er.finsetCongr.apply_symm_apply T).symm
      rw [he',mem_irrRAFFamily,indexedIrreducible_iff] at htmem
      exact (mem_irrRAFFamily Q C S).mpr htmem
    · intro hS
      refine ⟨er.finsetCongr S,?_,er.finsetCongr.symm_apply_apply S⟩
      apply List.mem_toFinset.mp
      rw [hrows,mem_irrRAFFamily,indexedIrreducible_iff]
      exact (mem_irrRAFFamily Q C S).mp hS
  have hin := indexedInput_eq Q C em er
  have hout := indexedOutput_eq er rows
  refine ⟨rows.map back,c,t,hnd.map back.injective,hf,?_,?_,hh,?_⟩
  · simpa only [hin,back,hout] using ht
  · simpa only [hin] using hr
  · simpa only [back,hout] using ho

end IrrRAFEnumeration.CompletionQuery
