import proofs.PowerLawSmallRAF.LigationDensityCertificate

namespace PowerLawSmallRAF

def ligationSubstrings (w : LigationWord) : Finset LigationWord :=
  ((Finset.range w.length).product (Finset.Icc 1 w.length)).image
    (fun ij => (w.drop ij.1).take ij.2)

theorem mem_ligationSubstrings_iff (w u : LigationWord) :
    u ∈ ligationSubstrings w ↔ u.IsInfix w ∧ u ≠ [] := by
  constructor
  · intro hu
    obtain ⟨⟨i,j⟩, hij, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨(List.take_prefix j (w.drop i)).isInfix.trans (List.drop_suffix i w).isInfix, ?_⟩
    intro heq
    have hlen := congrArg List.length heq
    simp only [List.length_take, List.length_drop, List.length_nil] at hlen
    omega
  · rintro ⟨⟨a,b,heq⟩, hne⟩
    have hu : 0 < u.length := by
      cases u <;> simp_all
    have hlen := congrArg List.length heq
    simp only [List.length_append] at hlen
    apply Finset.mem_image.mpr
    refine ⟨(a.length,u.length), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, ?_⟩
    rw [← heq]
    simp [List.append_assoc]

theorem ligationSubstrings_card_le (w : LigationWord) :
    (ligationSubstrings w).card ≤ w.length^2 := by
  calc
    _ ≤ ((Finset.range w.length).product (Finset.Icc 1 w.length)).card := Finset.card_image_le
    _ = _ := by simp [Finset.card_product, sq]

theorem ligationSubstrings_cut_closed (w : LigationWord) :
    ∀ u ∈ ligationSubstrings w, ∀ i ∈ ligationCuts u, ∀ isPrefix : Bool,
      ligationCutPart isPrefix u i ∈ ligationSubstrings w := by
  intro u hu i hi isPrefix
  obtain ⟨hinfix, _⟩ := (mem_ligationSubstrings_iff w u).mp hu
  apply (mem_ligationSubstrings_iff w _).mpr
  have hi' := Finset.mem_Ioo.mp hi
  cases isPrefix
  · refine ⟨(List.drop_suffix i u).isInfix.trans hinfix, ?_⟩
    intro heq
    have hlen := congrArg List.length heq
    simp only [ligationCutPart, Bool.false_eq_true, ↓reduceIte, List.length_drop,
      List.length_nil] at hlen
    omega
  · refine ⟨(List.take_prefix i u).isInfix.trans hinfix, ?_⟩
    intro heq
    have hlen := congrArg List.length heq
    simp only [ligationCutPart, ↓reduceIte, List.length_take, List.length_nil] at hlen
    omega

noncomputable def ligationSubstringSchedule (w : LigationWord) : List LigationWord :=
  (ligationSubstrings w).toList.mergeSort (fun u v => decide (u.length ≤ v.length))

theorem ligationSubstringSchedule_toFinset (w : LigationWord) :
    (ligationSubstringSchedule w).toFinset = ligationSubstrings w := by
  ext u
  simp [ligationSubstringSchedule]

theorem ligationSubstringSchedule_nodup (w : LigationWord) :
    (ligationSubstringSchedule w).Nodup := by
  exact (List.mergeSort_perm (ligationSubstrings w).toList _).nodup_iff.mpr
    (Finset.nodup_toList _)

theorem ligationSubstringSchedule_order (w : LigationWord) :
    (ligationSubstringSchedule w).Pairwise (fun u v => u.length ≤ v.length) := by
  have ht : ∀ (a b c : LigationWord),
      decide (a.length ≤ b.length) = true → decide (b.length ≤ c.length) = true →
        decide (a.length ≤ c.length) = true := by
    intro a b c hab hbc
    simpa only [decide_eq_true_eq] using (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have htotal : ∀ a b : LigationWord,
      (decide (a.length ≤ b.length) || decide (b.length ≤ a.length)) = true := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  simpa only [ligationSubstringSchedule, decide_eq_true_eq] using
    (List.pairwise_mergeSort ht htotal (ligationSubstrings w).toList)

end PowerLawSmallRAF
