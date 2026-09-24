import proofs.AllIrrRAFCert.WPHardness.NoSpurious
namespace AllIrrRAFCert.WPHardness
open RAF RAF.Frankl
variable {k n q : Nat}

def chosen (a : Fin k → Fin (n+2)) : Rxn k n q → Prop
  | .selector v => v.2 ≠ a v.1
  | .colorGate v => v.2 = a v.1
  | .rule _ => True
  | .close => True
noncomputable def witness (a : Fin k → Fin (n+2)) : Finset (Rxn k n q) := by
  classical
  exact Finset.univ.filter (chosen a)
@[simp] theorem mem_witness (a : Fin k → Fin (n+2)) (r : Rxn k n q) :
    r ∈ witness a ↔ chosen a r := by
  classical
  simp [witness]

theorem emit (A : System n q) (S : Finset (Rxn k n q))
    {r : Rxn k n q} {x : Mol k n} {t : Nat} (hr : r ∈ S)
    (hi : (crs A).inputs r ⊆ closureAt (crs A) S t)
    (ho : x ∈ (crs A).outputs r) : x ∈ closureAt (crs A) S (t+1) := by
  have he : Enabled (crs A) (closureAt (crs A) S t) r := hi
  simp only [closureAt,closureStep,Finset.mem_union,Finset.mem_biUnion]
  exact Or.inr ⟨r,hr,by simpa [he] using ho⟩

theorem time_mono (A : System n q) (S : Finset (Rxn k n q)) {s t : Nat}
    (h : s ≤ t) : closureAt (crs A) S s ⊆ closureAt (crs A) S t := by
  induction h with
  | refl => exact Finset.Subset.rfl
  | step h ih => exact ih.trans Finset.subset_union_left

theorem common_stage (A : System n q) (S : Finset (Rxn k n q)) (B : Finset (Mol k n))
    (hB : ∀ x ∈ B, ∃ t, x ∈ closureAt (crs A) S t) :
    ∃ t, B ⊆ closureAt (crs A) S t := by
  induction B using Finset.induction_on with
  | empty => exact ⟨0,Finset.empty_subset _⟩
  | @insert x B hx ih =>
    obtain ⟨t,ht⟩ := hB x (Finset.mem_insert_self _ _)
    obtain ⟨s,hs⟩ := ih (fun y hy => hB y (Finset.mem_insert_of_mem hy))
    refine ⟨max t s,Finset.insert_subset ?_ ?_⟩
    · exact time_mono A S (le_max_left _ _) ht
    · exact hs.trans (time_mono A S (le_max_right _ _))

theorem witness_signal (A : System n q) (a : Fin k → Fin (n+2))
    (v : Vertex k n) (hv : v.2 ≠ a v.1) :
    Mol.signal v ∈ closureAt (crs A) (witness a) 1 := by
  apply emit (r := .selector v)
  · simpa [chosen] using hv
  · exact Finset.Subset.rfl
  · simp [crs]
theorem decoder_inputs (A : System n q) (a : Fin k → Fin (n+2)) (i : Fin k) :
    (crs A).inputs (.colorGate (i,a i)) ⊆ closureAt (crs A) (witness a) 1 := by
  intro x hx
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
  exact witness_signal A a (i,w) (Finset.mem_erase.mp hw).1
theorem decoder_outputs (A : System n q) (a : Fin k → Fin (n+2)) (i : Fin k)
    {x : Mol k n} (hx : x ∈ (crs A).outputs (.colorGate (i,a i))) :
    x ∈ closureAt (crs A) (witness a) 2 :=
  emit A _ (by simp [chosen]) (decoder_inputs A a i) hx

theorem derivation_reaches (A : System n q) (a : Fin k → Fin (n+2)) {u : Fin (n+2)}
    (hu : Derives A (seeds a) u) :
    ∃ t, Mol.statement u ∈ closureAt (crs A) (witness a) t := by
  induction hu with
  | @seed u hu =>
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    exact ⟨2,decoder_outputs A a i (by simp [crs])⟩
  | rule j h ih =>
    have hi : ∀ x ∈ (crs A).inputs (.rule j),
        ∃ t, x ∈ closureAt (crs A) (witness a) t := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨0,by simp [closureAt,crs]⟩
      · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
        exact ih v hv
    obtain ⟨t,ht⟩ := common_stage A (witness a) _ hi
    exact ⟨t+1,emit A _ (r := .rule j) (by simp [chosen]) ht (by simp [crs])⟩

theorem all_inputs_reach (A : System n q) (a : Fin k → Fin (n+2)) (ha : Generates A a)
    (r : Rxn k n q) (hr : r ∈ witness a) :
    ∃ t, (crs A).inputs r ⊆ closureAt (crs A) (witness a) t := by
  have hc := (mem_witness a r).mp hr
  cases r with
  | selector v => exact ⟨0,Finset.Subset.rfl⟩
  | colorGate v =>
    have hv : v.2 = a v.1 := hc
    exact ⟨1,by simpa [crs,hv] using decoder_inputs A a v.1⟩
  | rule j =>
    apply common_stage
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨0,by simp [closureAt,crs]⟩
    · obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
      exact derivation_reaches A a (ha u)
  | close =>
    apply common_stage
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨2,decoder_outputs A a i (by simp [crs])⟩
    · obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
      exact derivation_reaches A a (ha u)

theorem witness_isRAF (A : System n q) (a : Fin k → Fin (n+2)) (ha : Generates A a) :
    IsRAF (crs A) cat (witness a) := by
  have hc : Rxn.close ∈ witness (q := q) a := by simp [chosen]
  obtain ⟨t,ht⟩ := all_inputs_reach A a ha .close hc
  have hz := emit A (witness a) hc ht (x := .globalCat) (by simp [crs])
  refine ⟨⟨_,hc⟩,all_inputs_reach A a ha,?_⟩
  intro r _
  exact ⟨.globalCat,t+1,hz,trivial⟩

theorem generating_implies_extra (A : System n q) :
    (∃ a : Fin k → Fin (n+2), Generates A a) → Extra (k := k) A := by
  classical
  rintro ⟨a,ha⟩
  obtain ⟨S,hsub,hmin⟩ := IrrRAFEnumeration.exists_minimal_subset
    (IsRAF (crs A) cat) (witness_isRAF A a ha)
  refine ⟨S,hmin,?_⟩
  intro i he
  have hm : Rxn.selector (i,a i) ∈ S := by rw [he]; simp
  have := hsub hm
  simp [chosen] at this

theorem generating_iff_extra (A : System n q) :
    (∃ a : Fin k → Fin (n+2), Generates A a) ↔ Extra (k := k) A :=
  ⟨generating_implies_extra A,extra_implies_generating A⟩
end AllIrrRAFCert.WPHardness
