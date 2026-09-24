import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset

namespace DigraphRealizability

variable {E : Type*} [Fintype E] [DecidableEq E]

abbrev Rule (E : Type*) := Finset E × E

def Models (G : Set (Rule E)) (X : Finset E) : Prop :=
  ∀ q ∈ G, q.1 ⊆ X → q.2 ∈ X

def SingleHead (G : Set (Rule E)) : Prop :=
  ∀ q ∈ G, ∀ t ∈ G, q.2 = t.2 → q = t

def Heads (G : Set (Rule E)) : Set E := {r | ∃ q ∈ G, q.2 = r}

noncomputable def closure (G : Set (Rule E)) (A : Finset E) : Finset E := by
  classical
  exact Finset.univ.filter fun r => ∀ X, Models G X → A ⊆ X → r ∈ X

theorem subset_closure (G : Set (Rule E)) (A : Finset E) : A ⊆ closure G A := by
  classical
  intro r hr
  simp only [closure, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun _ _ h => h hr

theorem closure_le {G : Set (Rule E)} {A X : Finset E}
    (hX : Models G X) (hA : A ⊆ X) : closure G A ⊆ X := by
  classical
  intro r hr
  exact (Finset.mem_filter.mp hr).2 X hX hA

theorem closure_models (G : Set (Rule E)) (A : Finset E) : Models G (closure G A) := by
  classical
  intro q hq hbody
  simp only [closure, Finset.mem_filter, Finset.mem_univ, true_and]
  intro X hX hAX
  exact hX q hq (hbody.trans (closure_le hX hAX))

/-- Minimal among current models outside the target. -/
def MinimalResidual (G L : Set (Rule E)) (B : Finset E) : Prop :=
  Models G B ∧ ¬ Models L B ∧
    ∀ T, Models G T → ¬ Models L T → T ⊆ B → T = B

/-- An original body may be strictly smaller than the prescribed residual. -/
theorem normalize {G L : Set (Rule E)} {B : Finset E}
    (hGL : G ⊆ L) (hL : SingleHead L) (hB : MinimalResidual G L B) :
    ∃ q ∈ L, q.1 ⊆ B ∧ q.2 ∉ B ∧ q.2 ∉ Heads G ∧ closure G q.1 = B := by
  classical
  obtain ⟨hGB, hLB, hmin⟩ := hB
  simp only [Models, not_forall] at hLB
  obtain ⟨q, hq, hbody, hhead⟩ := hLB
  have fresh : q.2 ∉ Heads G := by
    rintro ⟨t, ht, heq⟩
    have eq : t = q := hL t (hGL ht) q hq heq
    subst t
    exact hhead (hGB q ht hbody)
  have hle : closure G q.1 ⊆ B := closure_le hGB hbody
  have hnot : ¬ Models L (closure G q.1) := by
    intro hm
    exact hhead (hle (hm q hq (subset_closure G q.1)))
  exact ⟨q, hq, hbody, hhead, fresh,
    hmin _ (closure_models G q.1) hnot hle⟩

end DigraphRealizability
