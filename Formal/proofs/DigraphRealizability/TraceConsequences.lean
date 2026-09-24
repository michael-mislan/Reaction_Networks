import proofs.DigraphRealizability.TraceChecker
namespace DigraphRealizability
open RAFInteriorRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
theorem singleton_support (P : E → Finset E) (r : E) :
    PredSupported P {r} ↔ r ∈ P r := by simp [PredSupported]

omit [Fintype E] [DecidableEq E] in
theorem realizing_loops {F : Finset (Finset E)} {P : E → Finset E}
    (h : ∀ S, S ∈ F ↔ PredSupported P S) (r : E) :
    r ∈ P r ↔ {r} ∈ F := (singleton_support P r).symm.trans (h {r}).symm

theorem trace_fresh {F U : Finset (Finset E)} {H : Finset E}
    {xs : List (Finset E × E)} (h : checkTrace F U H xs = true) :
    (xs.map Prod.snd).Nodup ∧ ∀ r ∈ xs.map Prod.snd, r ∉ H := by
  induction xs generalizing U H with
  | nil => simp
  | cons q xs ih =>
    obtain ⟨S,r⟩ := q
    simp only [checkTrace, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨legal, tail⟩ := h
    obtain ⟨hn, hf⟩ := ih tail
    constructor
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun hr => hf r hr (Finset.mem_insert_self _ _), hn⟩
    · intro v hv
      simp only [List.map_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact legal.2.2.2.2
      · intro hH
        exact hf v hv (Finset.mem_insert_of_mem hH)

omit [Fintype E] in
theorem singleton_delete (U : Finset (Finset E)) (S : Finset E) (r t : E)
    (hr : r ∈ S) :
    {t} ∈ deleteInterval U S r ↔ {t} ∈ U ∧ t ≠ r := by
  by_cases he : t = r
  · subst t
    simp [deleteInterval, hr]
  · simp [deleteInterval, Ne.symm he, he]

theorem trace_singletons {F U : Finset (Finset E)} {H : Finset E}
    {xs : List (Finset E × E)} (h : checkTrace F U H xs = true) (t : E) :
    {t} ∈ F ↔ {t} ∈ U ∧ t ∉ xs.map Prod.snd := by
  induction xs generalizing U H with
  | nil =>
    have he : U = F := of_decide_eq_true h
    simp [he]
  | cons q xs ih =>
    obtain ⟨S,r⟩ := q
    simp only [checkTrace, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [ih h.2, singleton_delete U S r t h.1.2.2.1]
    simp [and_assoc]

theorem exact_trace_roots {F : Finset (Finset E)} {xs : List (Finset E × E)}
    (h : checkTrace F Finset.univ ∅ xs = true) :
    (xs.map Prod.snd).toFinset = Finset.univ.filter (fun r => {r} ∉ F) := by
  classical
  ext r
  have hh := trace_singletons h r
  simp only [Finset.mem_univ, true_and] at hh
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa using (not_congr hh).symm

theorem exact_trace_length {F : Finset (Finset E)} {xs : List (Finset E × E)}
    (h : checkTrace F Finset.univ ∅ xs = true) :
    xs.length = (Finset.univ.filter (fun r => {r} ∉ F)).card := by
  classical
  rw [← exact_trace_roots h, List.toFinset_card_of_nodup (trace_fresh h).1, List.length_map]
end DigraphRealizability
