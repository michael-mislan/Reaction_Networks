import proofs.ThermoCoreCompatibility.MultiInterface.PathCoordinates

namespace ThermoCoreCompatibility.MultiInterface

/-- Explicit path placement. Every nonjunction occurrence has a unique physical
species; junction occurrences are precisely the path endpoints. -/
structure JunctionAssembly (V I : Type*) where
  path : I → Path
  vertex : (i : I) → (path i).Vertex → V
  junction : V → Prop
  endpoint_iff : ∀ i v, junction (vertex i v) ↔
    v = (path i).first ∨ v = (path i).last
  private_unique : ∀ (o q : Σ i, (path i).Vertex),
    vertex o.1 o.2 = vertex q.1 q.2 → ¬ junction (vertex o.1 o.2) → o = q

namespace JunctionAssembly

variable {V I : Type*} (A : JunctionAssembly V I)

def firstJ (i : I) : {v // A.junction v} :=
  ⟨A.vertex i (A.path i).first,(A.endpoint_iff _ _).2 (Or.inl rfl)⟩

def lastJ (i : I) : {v // A.junction v} :=
  ⟨A.vertex i (A.path i).last,(A.endpoint_iff _ _).2 (Or.inr rfl)⟩

def Feasible (lo hi : {v // A.junction v} → ℝ) : Prop :=
  ∃ j : {v // A.junction v} → ℝ,
    (∀ v, lo v ≤ j v ∧ j v ≤ hi v) ∧
    ∀ i, (A.path i).lower (j (A.firstJ i)) < j (A.lastJ i) ∧
      j (A.lastJ i) < (A.path i).upper (j (A.firstJ i))

def Compatible (ell : ℝ) (lo hi : {v // A.junction v} → ℝ) : Prop :=
  ∃ z : V → ℝ, (∀ v, ell ≤ z v ∧ z v ≤ 1) ∧
    (∀ v : {v // A.junction v}, lo v ≤ z v ∧ z v ≤ hi v) ∧
    ∀ i, (A.path i).ProductiveState (fun v => z (A.vertex i v))

/-- Merge local vectors using actual species identity. -/
theorem merge (ell : ℝ) (j : {v // A.junction v} → ℝ)
    (z : (i : I) → (A.path i).Vertex → ℝ)
    (hf : ∀ i, z i (A.path i).first = j (A.firstJ i))
    (hl : ∀ i, z i (A.path i).last = j (A.lastJ i))
    (hb : ∀ i v, ell ≤ z i v ∧ z i v ≤ 1)
    (hj : ∀ v, ell ≤ j v ∧ j v ≤ 1) (hell : ell ≤ 1) :
    ∃ g : V → ℝ, (∀ i v, g (A.vertex i v) = z i v) ∧
      (∀ v : {v // A.junction v}, g v = j v) ∧
      ∀ v, ell ≤ g v ∧ g v ≤ 1 := by
  classical
  let value : (Σ i, (A.path i).Vertex) → ℝ := fun o => z o.1 o.2
  have hjloc : ∀ i v (h : A.junction (A.vertex i v)),
      z i v = j ⟨A.vertex i v,h⟩ := by
    intro i v h
    rcases (A.endpoint_iff i v).1 h with rfl | rfl
    · exact hf i
    · exact hl i
  have agree : ∀ o q : Σ i, (A.path i).Vertex,
      A.vertex o.1 o.2 = A.vertex q.1 q.2 → value o = value q := by
    intro o q he
    by_cases h : A.junction (A.vertex o.1 o.2)
    · dsimp [value]
      rw [hjloc _ _ h, hjloc _ _ (he ▸ h)]
      congr 1
      exact Subtype.ext he
    · exact congrArg value (A.private_unique o q he h)
  let g : V → ℝ := fun v =>
    if hv : A.junction v then j ⟨v,hv⟩
    else if ho : ∃ o : Σ i, (A.path i).Vertex, A.vertex o.1 o.2 = v
      then value (Classical.choose ho) else ell
  refine ⟨g,?_,?_,?_⟩
  · intro i v
    dsimp [g]
    split_ifs with h ho
    · exact (hjloc i v h).symm
    · exact agree (Classical.choose ho) ⟨i,v⟩ (Classical.choose_spec ho)
    · exact False.elim (ho ⟨⟨i,v⟩,rfl⟩)
  · intro v
    simp [g,v.property]
  · intro v
    dsimp [g]
    split_ifs with h ho
    · exact hj ⟨v,h⟩
    · exact hb _ _
    · exact ⟨le_rfl,hell⟩

theorem compatible_iff_feasible (ell : ℝ) (hell : 0 < ell) (hell1 : ell < 1)
    (lo hi : {v // A.junction v} → ℝ)
    (hlo : ∀ v, ell ≤ lo v) (hhi : ∀ v, hi v ≤ 1) :
    A.Compatible ell lo hi ↔ A.Feasible lo hi := by
  constructor
  · rintro ⟨g,hbox,hj,hp⟩
    refine ⟨fun v => g v,hj,?_⟩
    intro i
    have hc := Path.of_coordinates (fun v => g (A.vertex i v))
      (fun v => hbox (A.vertex i v)) (hp i)
    exact (Path.boxed_iff (A.path i) hell (hbox _).1 (hbox _).2 (hbox _).1).1 hc
  · rintro ⟨j,hj,hp⟩
    have hbox : ∀ v, ell ≤ j v ∧ j v ≤ 1 :=
      fun v => ⟨(hlo v).trans (hj v).1,(hj v).2.trans (hhi v)⟩
    have hlocals : ∀ i, ∃ z : (A.path i).Vertex → ℝ,
        z (A.path i).first = j (A.firstJ i) ∧ z (A.path i).last = j (A.lastJ i) ∧
        (∀ v, ell ≤ z v ∧ z v ≤ 1) ∧ (A.path i).ProductiveState z := by
      intro i
      apply Path.coordinates
      exact (Path.boxed_iff (A.path i) hell (hbox _).1 (hbox _).2 (hbox _).1).2 (hp i)
    choose z hf hl hb hz using hlocals
    obtain ⟨g,hg,hgj,hgb⟩ := A.merge ell j z hf hl hb hbox hell1.le
    refine ⟨g,hgb,?_,?_⟩
    · intro v
      rw [hgj v]
      exact hj v
    · intro i
      have he : (fun v => g (A.vertex i v)) = z i := funext (hg i)
      rw [he]
      exact hz i

end JunctionAssembly
end ThermoCoreCompatibility.MultiInterface
