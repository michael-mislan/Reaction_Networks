import proofs.ThermoCoreCompatibility.MultiInterface.PathReconstruction

namespace ThermoCoreCompatibility.MultiInterface.Path

def Vertex : Path → Type
  | .single _ => Bool
  | .snoc p _ => Sum p.Vertex Unit

def first : (p : Path) → p.Vertex
  | .single _ => false
  | .snoc p _ => Sum.inl p.first

def last : (p : Path) → p.Vertex
  | .single _ => true
  | .snoc _ _ => Sum.inr ()

def ProductiveState : (p : Path) → (p.Vertex → ℝ) → Prop
  | .single w, z => w.Productive (z false) (z true)
  | .snoc p w, z => p.ProductiveState (fun i => z (.inl i)) ∧
      w.Productive (z (.inl p.last)) (z (.inr ()))

theorem coordinates {p : Path} {ell x y : ℝ} (h : p.BoxRealizes ell x y) :
    ∃ z : p.Vertex → ℝ, z p.first = x ∧ z p.last = y ∧
      (∀ i, ell ≤ z i ∧ z i ≤ 1) ∧ p.ProductiveState z := by
  induction p generalizing x y with
  | single w =>
    refine ⟨(fun (b : Bool) => cond b y x), rfl, rfl, ?_, ?_⟩
    · intro i
      cases i
      · exact ⟨h.1,h.2.1⟩
      · exact ⟨h.2.2.1,h.2.2.2.1⟩
    · exact h.2.2.2.2
  | snoc p w ih =>
    obtain ⟨t,hp,hy,hy1,hw⟩ := h
    obtain ⟨z,hx,ht,hbox,hz⟩ := ih hp
    refine ⟨Sum.elim z (fun _ => y),hx,rfl,?_,?_⟩
    · intro i
      cases i with
      | inl i => exact hbox i
      | inr _ => exact ⟨hy,hy1⟩
    · exact ⟨hz,by simpa only [Sum.elim_inl,Sum.elim_inr,ht] using hw⟩

theorem of_coordinates {p : Path} {ell : ℝ} (z : p.Vertex → ℝ)
    (hbox : ∀ i, ell ≤ z i ∧ z i ≤ 1) (hz : p.ProductiveState z) :
    p.BoxRealizes ell (z p.first) (z p.last) := by
  induction p with
  | single w => exact ⟨(hbox false).1,(hbox false).2,(hbox true).1,(hbox true).2,hz⟩
  | snoc p w ih =>
    exact ⟨z (.inl p.last),ih (fun i => z (.inl i)) (fun i => hbox (.inl i)) hz.1,
      (hbox (.inr ())).1,(hbox (.inr ())).2,hz.2⟩

end ThermoCoreCompatibility.MultiInterface.Path
