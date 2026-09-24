import proofs.RAFBiochemicalInterventions.SmallSource
import proofs.RAFBiochemicalInterventions.SupportNecessity
namespace RAFBiochemicalLiteral.SmallSource
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
theorem force5_4 (S : List Row) (hs : Subrows S rows) (hr : RAF S food)
    (ha : r5 ∈ S) : r4 ∈ S :=
  input_forces rows S food r5 r4 38 hs hr ha
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem force5_6 (S : List Row) (hs : Subrows S rows) (hr : RAF S food)
    (ha : r5 ∈ S) : r6 ∈ S :=
  input_forces rows S food r5 r6 132 hs hr ha
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem force6_2 (S : List Row) (hs : Subrows S rows) (hr : RAF S food)
    (ha : r6 ∈ S) : r2 ∈ S :=
  input_forces rows S food r6 r2 2316 hs hr ha
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem force2_1 (S : List Row) (hs : Subrows S rows) (hr : RAF S food)
    (ha : r2 ∈ S) : r1 ∈ S :=
  input_forces rows S food r2 r1 3038 hs hr ha
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem force2_3 (S : List Row) (hs : Subrows S rows) (hr : RAF S food)
    (ha : r2 ∈ S) : r3 ∈ S :=
  input_forces rows S food r2 r3 3 hs hr ha
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem force1_0 (S : List Row) (hs : Subrows S rows) (hr : RAF S food)
    (ha : r1 ∈ S) : r0 ∈ S :=
  input_forces rows S food r1 r0 2643 hs hr ha
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem force3_8 (S : List Row) (hs : Subrows S rows) (hr : RAF S food)
    (ha : r3 ∈ S) : r8 ∈ S :=
  input_forces rows S food r3 r8 60 hs hr ha
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem force8_7 (S : List Row) (hs : Subrows S rows) (hr : RAF S food)
    (ha : r8 ∈ S) : r7 ∈ S :=
  input_forces rows S food r8 r7 590 hs hr ha
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem force3_9 (S : List Row) (hs : Subrows S rows) (hr : RAF S food)
    (ha : r3 ∈ S) : r9 ∈ S :=
  catalyst_forces rows S food r3 r9 5730 hs hr ha
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem force9_3 (S : List Row) (hs : Subrows S rows) (hr : RAF S food)
    (ha : r9 ∈ S) : r3 ∈ S :=
  input_forces rows S food r9 r3 3 hs hr ha
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem target_forces_all (S : List Row) (hs : Subrows S rows) (hr : RAF S food)
    (hv : Generated S food 168) : SameRows S rows := by
  have h5 : r5 ∈ S := unique_producer_forced rows S food 168 r5 hs
    (by decide +kernel) (by decide +kernel) hv
  have h4 := force5_4 S hs hr h5
  have h6 := force5_6 S hs hr h5
  have h2 := force6_2 S hs hr h6
  have h1 := force2_1 S hs hr h2
  have h3 := force2_3 S hs hr h2
  have h0 := force1_0 S hs hr h1
  have h8 := force3_8 S hs hr h3
  have h7 := force8_7 S hs hr h8
  have h9 := force3_9 S hs hr h3
  refine ⟨hs,?_⟩
  intro r hh
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with h | h | h | h | h | h | h | h | h | h
  · subst r; exact h0
  · subst r; exact h1
  · subst r; exact h2
  · subst r; exact h3
  · subst r; exact h4
  · subst r; exact h5
  · subst r; exact h6
  · subst r; exact h7
  · subst r; exact h8
  · subst r; exact h9

theorem lower_forced (C : List Row) (hc : ClosedRAF rows C food) : Subrows lower C := by
  have h := prefix_forces rows C food hc lowerOrder food
    (by unfold Subrows; decide +kernel) (fun _ hx => Generated.food hx) (by decide +kernel)
  have he : Subrows lower lowerOrder := by unfold Subrows; decide +kernel
  exact fun r hr => h r (he r hr)

def extensionPool : List Nat := food ++ lower.flatMap Row.outputs ++ r3.outputs
def extensionOrder : List Row := [r9,r2,r6,r5]

theorem extension_forced (C : List Row) (hc : ClosedRAF rows C food) (h3 : r3 ∈ C) :
    Subrows rows C := by
  have hl := lower_forced C hc
  have hp : ∀ x ∈ extensionPool, Generated C food x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact Generated.food hx
      · exact generated_mono hl (outputs_generated lower food lower_raf x hx)
    · exact Generated.reaction r3 h3 (hc.1.2 r3 h3).1 x hx
  have he := prefix_forces rows C food hc extensionOrder extensionPool
    (by unfold Subrows; decide +kernel) hp (by decide +kernel)
  have hcover : Subrows rows (lower ++ r3 :: extensionOrder) := by unfold Subrows; decide +kernel
  intro r hr
  rcases List.mem_append.mp (hcover r hr) with hh | hh
  · exact hl r hh
  · rcases List.mem_cons.mp hh with hh | hh
    · exact hh ▸ h3
    · exact he r hh

theorem outside_forces_three (C : List Row) (hs : Subrows C rows) (hc : RAF C food)
    (hnot : ¬ Subrows C lower) : r3 ∈ C := by
  apply Classical.byContradiction
  intro h3
  apply hnot
  intro r hr
  have h := hs r hr
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst r; decide +kernel
  · subst r; decide +kernel
  · subst r; exact False.elim (h3 ((force2_3 C hs hc) hr))
  · exact False.elim (h3 (h ▸ hr))
  · subst r; decide +kernel
  · subst r; exact False.elim (h3 ((fun h5 => force2_3 C hs hc (force6_2 C hs hc (force5_6 C hs hc h5))) hr))
  · subst r; exact False.elim (h3 ((fun h6 => force2_3 C hs hc (force6_2 C hs hc h6)) hr))
  · subst r; decide +kernel
  · subst r; decide +kernel
  · subst r; exact False.elim (h3 ((force9_3 C hs hc) hr))

theorem closed_catalogue (C : List Row) (hs : Subrows C rows) :
    ClosedRAF rows C food ↔ SameRows C lower ∨ SameRows C rows := by
  constructor
  · intro hc
    by_cases h : Subrows C lower
    · exact Or.inl ⟨h,lower_forced C hc⟩
    · exact Or.inr ⟨hs,extension_forced C hc (outside_forces_three C hs hc.1 h)⟩
  · intro h
    have transport : ∀ T, ClosedRAF rows T food → SameRows C T → ClosedRAF rows C food := by
      intro T ht he
      refine ⟨raf_of_same_rows ⟨he.2,he.1⟩ ht.1,?_⟩
      intro r hr hi hc
      have hp := fun x (hx : Generated C food x) => generated_mono he.1 hx
      exact he.2 r (ht.2 r hr (fun x hx => hp x (hi x hx)) (r.catalyst.sat_mono hp hc))
    exact h.elim (transport lower lower_closed) (transport rows whole_closed)

theorem same_irreducibles (S : List Row) :
    (Subrows S rows ∧ Irreducible S food) ↔ (Subrows S lower ∧ Irreducible S food) := by
  constructor
  · rintro ⟨hs,hi⟩
    refine ⟨?_,hi⟩
    have he := (irreducible_catalogue S hs).mp hi
    have h0 : Subrows [r0] lower := by unfold Subrows; decide +kernel
    have h7 : Subrows [r7] lower := by unfold Subrows; decide +kernel
    exact he.elim (fun h r hr => h0 r (h.1 r hr)) (fun h r hr => h7 r (h.1 r hr))
  · rintro ⟨hs,hi⟩
    exact ⟨fun r hr => lower_proper.1 r (hs r hr),hi⟩

theorem lower_not_capable : ¬ Capable lower food 168 := by
  rintro ⟨S,hs,hr,hv⟩
  have he := target_forces_all S (fun r hr => lower_proper.1 r (hs r hr)) hr hv
  exact lower_proper.2 (fun r hr => hs r (he.2 r hr))

theorem catalogue_information_loss :
    (∀ S, (Subrows S rows ∧ Irreducible S food) ↔ (Subrows S lower ∧ Irreducible S food)) ∧
    Capable rows food 168 ∧ ¬ Capable lower food 168 :=
  ⟨same_irreducibles,valine_capable,lower_not_capable⟩
end RAFBiochemicalLiteral.SmallSource
