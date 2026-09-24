import proofs.ThermoCoreCompatibility.Hypergraph.FanSourceTheorem
import proofs.ThermoCoreCompatibility.Hypergraph.MonomialTriple
import proofs.ThermoCoreCompatibility.Toric
import proofs.ThermoCoreCompatibility.Direction

namespace ThermoCoreCompatibility.Hypergraph.MonomialTriple

noncomputable section

private theorem none_ne_some' {α : Type*} (x : α) : (none : Option α) ≠ some x := by
  intro h
  cases h

noncomputable def data : FanData (Fin 3) where
  gain := ![3,4,3]
  gain_ge_two := by intro i; fin_cases i <;> norm_num
  sharedFactor := 1
  sharedFactor_pos := by norm_num
  firstFactor := ![4,1/2,1]
  firstFactor_pos := by intro i; fin_cases i <;> norm_num
  secondFactor := ![2,1,1]
  secondFactor_pos := by intro i; fin_cases i <;> norm_num
  lower := fun _ => 13/20
  upper := ![71/100,19/25,19/25]
  lower_pos := by intro i; norm_num
  box_nonempty := by intro i; fin_cases i <;> norm_num

theorem source_full_incompatible : ¬ data.SourceCompatible Set.univ (1/10) (9/10) (1/10) (9/10) := by
  intro h
  obtain ⟨a,b,ha,_,_,_,c,hc,hp⟩ :=
    (data.sourceCompatible_iff Set.univ (1/10) (9/10) (1/10) (9/10)
      (by norm_num) (by norm_num)).1 h
  have h₀ := hp 0 (Set.mem_univ 0)
  have h₁ := hp 1 (Set.mem_univ 1)
  have h₂ := hp 2 (Set.mem_univ 2)
  have hu₀ := (hc 0).2
  have hl₁ := (hc 1).1
  norm_num [data] at h₀ h₁ h₂ hu₀ hl₁
  exact no_common_state (by linarith) hu₀ (by linarith) h₀ h₁ h₂

theorem source_deletions : ∀ i : Fin 3,
    data.SourceCompatible {k | k ≠ i} (1/10) (9/10) (1/10) (9/10) := by
  intro i
  apply (data.sourceCompatible_iff _ (1/10) (9/10) (1/10) (9/10)
    (by norm_num) (by norm_num)).2
  fin_cases i
  · refine ⟨22/25,157/200,by norm_num,by norm_num,by norm_num,by norm_num,
      ![13/20,13/20,18/25],?_,?_⟩
    · norm_num [data,Fin.forall_fin_succ]
    · norm_num [data,Fin.forall_fin_succ,TriangleProduction]
  · refine ⟨169/200,88/125,by norm_num,by norm_num,by norm_num,by norm_num,
      ![67/100,13/20,653/1000],?_,?_⟩
    · norm_num [data,Fin.forall_fin_succ]
    · norm_num [data,Fin.forall_fin_succ,TriangleProduction]
  · refine ⟨141/160,93/125,by norm_num,by norm_num,by norm_num,by norm_num,
      ![71/100,13/20,13/20],?_,?_⟩
    · norm_num [data,Fin.forall_fin_succ]
    · norm_num [data,Fin.forall_fin_succ,TriangleProduction]
      decide

noncomputable def family : CoreFamily (Core := Fin 3) data.network where
  core := fun i => (data.triangle i).motif
  core_isPAC := data.source_isPAC
  orientation := fun _ => 1
  orientation_unit := fun _ => Or.inl rfl
  owner
    | none => 0
    | some (i,_) => i
  owner_mem := by
    intro r
    rcases r with _ | ⟨i,(_|_)⟩ <;> simp [TriangleIn.motif,FanData.triangle]

noncomputable def relaxedActivity (c : Complex (FanSpecies (Fin 3))) : ℝ :=
  if c none = 3 then 157/250 else
  if c none = 4 then 61/100 else
  if c none = 1 then 9/10 else
  if c (some none) = 1 then 37/50 else
  if c (some (some 0)) = 1 then 701/1000 else
  if c (some (some 1)) = 1 then 651/1000 else
  if c (some (some 2)) = 1 then 341/500 else 1

theorem source_linearComplexCompatible : family.LinearComplexCompatible := by
  refine ⟨relaxedActivity,?_,?_,?_⟩
  · intro c
    unfold relaxedActivity
    split_ifs <;> norm_num
  · intro r
    rcases r with _ | ⟨i,(_|_)⟩
    · norm_num [family,ReversibleCRN.linearCurrent,FanData.network,relaxedActivity,atom,data,none_ne_some']
    · fin_cases i <;>
        norm_num [family,ReversibleCRN.linearCurrent,FanData.network,relaxedActivity,atom,data,none_ne_some']
      split_ifs with h
      · norm_num
      · exact (h rfl).elim
    · fin_cases i <;>
        norm_num [family,ReversibleCRN.linearCurrent,FanData.network,relaxedActivity,atom,data,none_ne_some']
      split_ifs with h
      · norm_num
      · exact (h rfl).elim
  · intro i
    change (data.triangle i).motif.Productive _
    rw [(data.triangle i).productive_iff]
    fin_cases i <;>
      norm_num [FanData.triangle,ReversibleCRN.linearCurrent,FanData.network,relaxedActivity,atom,data,none_ne_some']
    split_ifs with h
    · norm_num
    · exact (h rfl).elim

theorem source_directionCompatible : family.DirectionCompatible := by
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h22 : (2 : Fin 3) = ⟨2,by decide⟩ := rfl
  refine ⟨(fun s => match s with | none => -1 | some none => -3/2 | some (some _) => -2),?_⟩
  intro r
  rcases r with _ | ⟨i,(_|_)⟩
  · norm_num [CoreFamily.directionalAffinity,CoreFamily.orientedDisplacement,
      family,FanData.network,atom,data,Fintype.sum_option,Fin.sum_univ_succ,none_ne_some',Option.some_ne_none,h21,h22]
  · fin_cases i <;>
      norm_num [CoreFamily.directionalAffinity,CoreFamily.orientedDisplacement,
        family,FanData.network,atom,data,Fintype.sum_option,Fin.sum_univ_succ,none_ne_some',Option.some_ne_none,h21,h22]
  · fin_cases i <;>
      norm_num [CoreFamily.directionalAffinity,CoreFamily.orientedDisplacement,
        family,FanData.network,atom,data,Fintype.sum_option,Fin.sum_univ_succ,none_ne_some',Option.some_ne_none,h21,h22]

end

end ThermoCoreCompatibility.Hypergraph.MonomialTriple
