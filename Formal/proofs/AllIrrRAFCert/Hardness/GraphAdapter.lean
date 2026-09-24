import proofs.AllIrrRAFCert.Hardness.CliqueToRAF
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace AllIrrRAFCert.Hardness

variable {k n : Nat}

def graphBad (G : SimpleGraph (Fin (n+2))) [DecidableRel G.Adj] : Pair k n → Bool :=
  fun e => decide (e.1.1 ≠ e.2.1 ∧ ¬ G.Adj e.1.2 e.2.2)

theorem compatible_graph_iff (G : SimpleGraph (Fin (n+2))) [DecidableRel G.Adj]
    (a : Fin k → Fin (n+2)) :
    Compatible (graphBad G) a ↔ ∀ i j, i ≠ j → G.Adj (a i) (a j) := by
  constructor
  · intro h i j hij
    by_contra hn
    have hb : graphBad G ((i,a i),(j,a j)) = true := by simp [graphBad,hij,hn]
    have := h _ hb
    simp at this
  · intro h e he
    have hb : e.1.1 ≠ e.2.1 ∧ ¬ G.Adj e.1.2 e.2.2 := by simpa [graphBad] using he
    by_contra hn
    push Not at hn
    exact hb.2 (by simpa [hn.1,hn.2] using h e.1.1 e.2.1 hb.1)

theorem indexed_clique_iff (G : SimpleGraph (Fin (n+2))) :
    (∃ a : Fin k → Fin (n+2), ∀ i j, i ≠ j → G.Adj (a i) (a j)) ↔
      ∃ s : Finset (Fin (n+2)), G.IsNClique k s := by
  classical
  constructor
  · rintro ⟨a,ha⟩
    have hinj : Function.Injective a := by
      intro i j he
      by_contra hn
      exact (ha i j hn).ne he
    refine ⟨Finset.univ.image a,?_,?_⟩
    · intro v hv w hw hvw
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
      exact ha i j (fun hij => hvw (congrArg a hij))
    · rw [Finset.card_image_of_injective _ hinj]
      simp
  · rintro ⟨s,hs⟩
    let e := (Finset.equivFinOfCardEq hs.card_eq).symm
    refine ⟨fun i => (e i).val,?_⟩
    intro i j hij
    apply hs.isClique (e i).property (e j).property
    intro he
    exact hij (e.injective (Subtype.ext he))

theorem graph_clique_iff_extra (G : SimpleGraph (Fin (n+2))) [DecidableRel G.Adj] :
    (∃ s : Finset (Fin (n+2)), G.IsNClique k s) ↔ Extra (graphBad (k := k) G) := by
  rw [← clique_iff_extra]
  unfold HasClique
  simp_rw [compatible_graph_iff]
  exact (indexed_clique_iff G).symm

end AllIrrRAFCert.Hardness
