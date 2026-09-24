import proofs.DigraphRealizability.HornElimination
import proofs.RAFInteriorRealizability.PredSupport

namespace DigraphRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

def graphRules (P : E → Finset E) : Set (Rule E) :=
  {q | q.1 = P q.2}

omit [Fintype E] [DecidableEq E] in
theorem graphRules_singleHead (P : E → Finset E) : SingleHead (graphRules P) := by
  intro q hq t ht he
  exact Prod.ext (hq.trans ((congrArg P he).trans ht.symm)) he

omit [Fintype E] [DecidableEq E] in
theorem graphRules_models (P : E → Finset E) (X : Finset E) :
    Models (graphRules P) X ↔ ∀ r, P r ⊆ X → r ∈ X := by
  constructor
  · intro h r
    exact h (P r,r) rfl
  · intro h q hq hb
    exact h q.2 (hq ▸ hb)

theorem support_iff_models (P : E → Finset E) (S : Finset E) :
    RAFInteriorRealizability.PredSupported P S ↔ Models (graphRules P) Sᶜ := by
  classical
  rw [graphRules_models]
  constructor
  · intro h r hr
    apply Finset.mem_compl.mpr
    intro hrs
    obtain ⟨u, huS, huP⟩ := h r hrs
    exact Finset.mem_compl.mp (hr huP) huS
  · intro h r hrs
    by_contra hn
    have hsub : P r ⊆ Sᶜ := by
      intro u hu
      apply Finset.mem_compl.mpr
      intro hus
      exact hn ⟨u, hus, hu⟩
    exact Finset.mem_compl.mp (h r hsub) hrs

/-- Unused coordinates receive loops, while empty bodies remain empty bodies. -/
noncomputable def reconstruct (L : Set (Rule E)) (r : E) : Finset E := by
  classical
  exact if h : ∃ q ∈ L, q.2 = r then (Classical.choose h).1 else {r}

theorem reconstruct_row {L : Set (Rule E)} (hs : SingleHead L) {q : Rule E}
    (hq : q ∈ L) : reconstruct L q.2 = q.1 := by
  classical
  have h : ∃ t ∈ L, t.2 = q.2 := ⟨q,hq,rfl⟩
  have hc := Classical.choose_spec h
  have eq := hs (Classical.choose h) hc.1 q hq hc.2
  simp only [reconstruct, dif_pos h]
  exact congrArg Prod.fst eq

theorem reconstruct_models {L : Set (Rule E)} (hs : SingleHead L) (X : Finset E) :
    Models (graphRules (reconstruct L)) X ↔ Models L X := by
  classical
  rw [graphRules_models]
  constructor
  · intro h q hq hb
    exact h q.2 ((reconstruct_row hs hq).symm ▸ hb)
  · intro h r hb
    by_cases he : ∃ q ∈ L, q.2 = r
    · obtain ⟨q,hq,rfl⟩ := he
      exact h q hq ((reconstruct_row hs hq) ▸ hb)
    · have hr : reconstruct L r = {r} := by simp [reconstruct, he]
      exact hb (hr.symm ▸ Finset.mem_singleton_self r)

def dual (F : Finset (Finset E)) : Finset (Finset E) :=
  F.image fun X => Xᶜ

@[simp] theorem mem_dual (F : Finset (Finset E)) (X : Finset E) :
    X ∈ dual F ↔ Xᶜ ∈ F := by
  classical
  simp only [dual, Finset.mem_image]
  constructor
  · rintro ⟨Y,hY,rfl⟩
    simpa using hY
  · intro h
    exact ⟨Xᶜ,h,by simp⟩

@[simp] theorem dual_dual (F : Finset (Finset E)) : dual (dual F) = F := by
  ext X
  simp

/-- A family-only complementary elimination criterion, without an unknown graph or rules. -/
def ComplementPeelable (F : Finset (Finset E)) : Prop :=
  Eliminates (dual F) Finset.univ ∅

theorem digraphRealizable_iff_complementPeelable (F : Finset (Finset E)) :
    (∃ P : E → Finset E, ∀ S, S ∈ F ↔ RAFInteriorRealizability.PredSupported P S) ↔
      ComplementPeelable F := by
  classical
  rw [ComplementPeelable, ← singleHead_iff_eliminates]
  constructor
  · rintro ⟨P,hP⟩
    refine ⟨graphRules P, graphRules_singleHead P, ?_⟩
    intro X
    rw [mem_dual, hP, support_iff_models]
    simp
  · rintro ⟨L,hs,hm⟩
    refine ⟨reconstruct L, ?_⟩
    intro S
    rw [support_iff_models, reconstruct_models hs, ← hm]
    simp

theorem reconstructed_support {F : Finset (Finset E)} {L : Set (Rule E)}
    (hs : SingleHead L) (hm : ∀ X, X ∈ dual F ↔ Models L X) (S : Finset E) :
    RAFInteriorRealizability.PredSupported (reconstruct L) S ↔ S ∈ F := by
  rw [support_iff_models, reconstruct_models hs, ← hm]
  simp
end DigraphRealizability
