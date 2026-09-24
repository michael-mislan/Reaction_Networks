import proofs.IrrRAFEnumeration.SATUniformCompiler
import proofs.Complexitylib.SAT.Verifier

namespace IrrRAFEnumeration.SATSource

open SATCompletion Complexity

/-- Rectangular incidence matrix of the library CNF; duplicates collapse. -/
def libraryRect (φ : SAT.CNF) (N : Nat) (j : Fin φ.length) : Finset (Choice N) :=
  Finset.univ.filter (fun x => ({sign := x.2, var := x.1.val} : SAT.Lit) ∈ φ[j])

@[simp] theorem mem_libraryRect (φ : SAT.CNF) (N : Nat) (j : Fin φ.length) (x : Choice N) :
    x ∈ libraryRect φ N j ↔ ({sign := x.2, var := x.1.val} : SAT.Lit) ∈ φ[j] := by
  simp [libraryRect]

theorem libraryRect_eval_iff (φ : SAT.CNF) (N : Nat) (α : SAT.Assignment) (f : Fin N → Bool)
    (hbound : ∀ j : Fin φ.length, ∀ ℓ ∈ φ[j], ℓ.var < N)
    (hassign : ∀ i : Fin N, SAT.Assignment.get α i.val = f i) :
    Satisfies (libraryRect φ N) f ↔ SAT.CNF.eval α φ = true := by
  simp only [SAT.CNF.eval,List.all_eq_true]
  constructor
  · intro h c hc
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hc
    obtain ⟨x,hx,hxf⟩ := h j
    have hmem := (mem_libraryRect φ N j x).mp hx
    apply List.any_eq_true.mpr
    refine ⟨{sign := x.2,var := x.1.val},hmem,?_⟩
    simp only [SAT.Lit.eval,hassign,hxf,beq_self_eq_true]
  · intro h j
    have hc := h φ[j] (List.getElem_mem j.isLt)
    obtain ⟨ℓ,hℓ,he⟩ := List.any_eq_true.mp hc
    let i : Fin N := ⟨ℓ.var,hbound j ℓ hℓ⟩
    refine ⟨(i,ℓ.sign),?_,?_⟩
    · apply (mem_libraryRect φ N j (i,ℓ.sign)).mpr
      simpa [i] using hℓ
    · have ha : SAT.Assignment.get α ℓ.var = ℓ.sign := by
        simpa only [SAT.Lit.eval,beq_iff_eq] using he
      exact (hassign i).symm.trans ha

theorem libraryRect_satisfiable_iff (φ : SAT.CNF) (N : Nat)
    (hbound : ∀ j : Fin φ.length, ∀ ℓ ∈ φ[j], ℓ.var < N) :
    (∃ f, Satisfies (libraryRect φ N) f) ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨List.ofFn f,(libraryRect_eval_iff φ N (List.ofFn f) f hbound ?_).mp hf⟩
    intro i
    simp [SAT.Assignment.get,i.isLt]
  · rintro ⟨α,hα⟩
    refine ⟨fun i => SAT.Assignment.get α i.val,?_⟩
    exact (libraryRect_eval_iff φ N α _ hbound (fun _ => rfl)).mpr hα

theorem libraryRect_input_bound (φ : SAT.CNF) :
    ∀ j : Fin φ.length, ∀ ℓ ∈ φ[j], ℓ.var < φ.encode.length+2 := by
  intro j ℓ hℓ
  have h1 := SAT.Clause.var_le_maxVar hℓ
  have h2 : (φ[j]).maxVar ≤ φ.maxVar :=
    SAT.CNF.clause_maxVar_le_maxVar (List.getElem_mem j.isLt)
  have h3 := SAT.CNF.maxVar_le_encode_length φ
  omega

def libraryRectangle (φ : SAT.CNF) : List Bool := cnfBits (libraryRect φ (φ.encode.length+2))

def librarySATAdapter (z : List Bool) : List Bool :=
  match SAT.CNF.decode? z with
  | some φ => libraryRectangle φ
  | none => cnfBits (fun _ : Fin 1 => (∅ : Finset (Choice 2)))

theorem librarySATAdapter_encode (φ : SAT.CNF) :
    librarySATAdapter φ.encode = libraryRectangle φ := by
  simp [librarySATAdapter]

theorem libraryRect_encode_satisfiable (φ : SAT.CNF) :
    (∃ f, Satisfies (libraryRect φ (φ.encode.length+2)) f) ↔ φ.Satisfiable :=
  libraryRect_satisfiable_iff φ _ (libraryRect_input_bound φ)

end IrrRAFEnumeration.SATSource
