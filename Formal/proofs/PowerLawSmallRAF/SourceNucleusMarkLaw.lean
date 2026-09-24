import proofs.PowerLawSmallRAF.SourceLigationIIDLaw

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def ligationRawAllMarked : (words : List LigationWord) → LigationRawConfiguration words → Prop
  | [], _ => True
  | _ :: rest, cfg => (¬ ∀ i, cfg.1 i = false) ∧ ligationRawAllMarked rest cfg.2

theorem ligationRawAllMarked_mass (p : ℝ) (words : List LigationWord) :
    (∑ cfg : LigationRawConfiguration words,
      ligationRawWeight p words cfg * (if ligationRawAllMarked words cfg then 1 else 0)) =
      (words.map (fun w => 1-(1-p)^(w.length-1))).prod := by
  induction words with
  | nil => simp [ligationRawWeight,ligationRawAllMarked,LigationRawConfiguration]
  | cons w rest ih =>
    let f : ((ligationCuts w) → Bool) × LigationRawConfiguration rest → ℝ :=
      fun cfg => ligationRawWeight p (w::rest) cfg *
        (if ligationRawAllMarked (w::rest) cfg then 1 else 0)
    change (∑ cfg : ((ligationCuts w) → Bool) × LigationRawConfiguration rest, f cfg) = _
    rw [Fintype.sum_prod_type]
    dsimp only [f,ligationRawWeight,ligationRawAllMarked]
    trans ∑ row : (ligationCuts w) → Bool, bernoulliFullRowWeight p row *
      (if ∀ i, row i = false then 0 else
        (rest.map (fun v => 1-(1-p)^(v.length-1))).prod)
    · apply Finset.sum_congr rfl
      intro row _
      by_cases hrow : ∀ i, row i = false
      · simp [hrow]
      · simp only [hrow,not_false_eq_true,true_and,ite_false,mul_assoc,← Finset.mul_sum,ih]
    · have hh := bernoulliFullRow_subset_choice p (Finset.univ : Finset (ligationCuts w)) 0
        ((rest.map (fun v => 1-(1-p)^(v.length-1))).prod)
      simp only [Finset.mem_univ,forall_const] at hh
      simpa [ligationCuts] using hh

theorem source_rawAllMarked_iff (n : Nat) (H : Finset (Reaction n))
    (words : List LigationWord) (hb : ∀ w ∈ words, w.length ≤ n) :
    ligationRawAllMarked words (sourceLigationRawConfiguration n H words hb) ↔
      ∀ w (hw : w ∈ words), ∃ i : ligationCuts w,
        ligationCutReaction n w (hb w hw) i ∈ H := by
  induction words with
  | nil => simp [ligationRawAllMarked]
  | cons w rest ih =>
    simp only [ligationRawAllMarked,sourceLigationRawConfiguration]
    rw [ih]
    simp
    constructor
    · rintro ⟨hh,ht⟩ v hv
      rcases hv with rfl | hv
      · exact hh
      · exact ht v hv
    · intro h
      exact ⟨h w (Or.inl rfl),fun v hv => h v (Or.inr hv)⟩

/-- Exact all-word marking probability in the actual source channel field.
This uses independence of distinct split coordinates, not of generated words. -/
theorem source_nucleus_mark_probability (p : ℝ) (n : Nat)
    (words : List LigationWord) (hb : ∀ w ∈ words, w.length ≤ n) (hnd : words.Nodup) :
    (∑ H : Finset (Reaction n), bernoulliSubsetRowWeight p H *
      (if ∀ w (hw : w ∈ words), ∃ i : ligationCuts w,
        ligationCutReaction n w (hb w hw) i ∈ H then 1 else 0)) =
      (words.map (fun w => 1-(1-p)^(w.length-1))).prod := by
  have hh := sourceLigationRawConfiguration_expectation p n words hb hnd
    (fun cfg => if ligationRawAllMarked words cfg then 1 else 0)
  simp_rw [source_rawAllMarked_iff] at hh
  exact hh.trans (ligationRawAllMarked_mass p words)

end
end PowerLawSmallRAF
