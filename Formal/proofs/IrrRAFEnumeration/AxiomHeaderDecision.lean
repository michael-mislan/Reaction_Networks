import proofs.IrrRAFEnumeration.AxiomSourceIntegration
import proofs.IrrRAFEnumeration.HeaderComparison

namespace IrrRAFEnumeration.AxiomSource
open RAF AllIrrRAFCert.WPHardness Complexity Complexity.TM HeaderComparison

theorem source_card_eq_iff_no_smallGenerating {k n q : Nat} (A : System n q) :
    (irrRAFFamily (crs A) cat : Finset (Finset (Rxn k n q))).card = k ↔
      ¬ SmallGenerating A k := by
  classical
  have hsub : listedFamily k n q ⊆ irrRAFFamily (crs A) cat := by
    intro S hS
    exact (mem_irrRAFFamily _ _ _).mpr (listed_valid A S hS)
  have hcard : (irrRAFFamily (crs A) cat : Finset (Finset (Rxn k n q))).card = k ↔
      irrRAFFamily (crs A) cat = listedFamily k n q := by
    constructor
    · intro h
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [h,parameter_eq])).symm
    · intro h
      rw [h,parameter_eq]
  rw [hcard,← exactCertification_iff_family_eq,
    AllIrrRAFCert.axiom_iff_not_exactCertification,not_not]

theorem output_has_unary_prefix (out : Tape) (count : Nat) (body : List Bool)
    (h : out.HasOutput (List.replicate count true ++ false :: body)) :
    UnaryPrefix (parkOutput out) count Γ.zero := by
  constructor
  · intro j hj
    have hh := h.1 j (by simp; omega)
    simpa [parkOutput,List.getElem_append,hj,Γ.ofBool,Nat.add_comm] using hh
  · have hh := h.1 count (by simp)
    simpa [parkOutput,List.getElem_append,Γ.ofBool,Nat.add_comm] using hh

/-- The compiled final-header routine decides the new source's no-instances.
The output comes from a completed exact enumeration, in the existing unary
count/fixed-mask format. It is never inspected before the enumerator halts. -/
theorem source_header_decides_no {k n q : Nat} (A : System n q)
    (rows : List (Finset (Rxn k n q))) (hnd : rows.Nodup)
    (hrows : rows.toFinset = irrRAFFamily (crs A) cat)
    (body : List Bool) (inp expected flag out : Tape)
    (hi : Parked inp) (he : Parked expected) (hf : Parked flag)
    (ho : out.StartInvariant) (hE : UnaryPrefix expected k Γ.blank)
    (houtput : out.HasOutput (List.replicate rows.length true ++ false :: body)) :
    ∃ final t, t ≤ out.head+k+2 ∧
      headerTM.reachesIn t (config 0 inp expected flag out) final ∧
      headerTM.halted final ∧
      ((final.work 1).read = Γ.one ↔ ¬ SmallGenerating A k) ∧
      final.output.cells = out.cells := by
  obtain ⟨final,t,ht,hr,hh,hflag,hcells⟩ := header_comparison_correct rows.length k
    inp expected flag out hi he hf ho hE (output_has_unary_prefix out _ body houtput)
  refine ⟨final,t,ht,hr,hh,?_,hcells⟩
  rw [hflag]
  have hlen : rows.length = (irrRAFFamily (crs (k := k) A) cat).card := by
    rw [← hrows,List.toFinset_card_of_nodup hnd]
  have hbool : Γ.ofBool (decide (rows.length = k)) = Γ.one ↔ rows.length = k := by
    by_cases h : rows.length = k <;> simp [h,Γ.ofBool]
  rw [hbool,hlen,source_card_eq_iff_no_smallGenerating]

end IrrRAFEnumeration.AxiomSource
