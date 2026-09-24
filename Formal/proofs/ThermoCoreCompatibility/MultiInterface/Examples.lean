import proofs.ThermoCoreCompatibility.MultiInterface.RationalWitness
import proofs.ThermoCoreCompatibility.Hypergraph.PairResponseBounds

namespace ThermoCoreCompatibility.MultiInterface.Examples

def graph : Hypergraph.PairAssembly (Fin 3) (Fin 3) where
  src := fun e => if e = 1 then 1 else 0
  dst := fun e => if e = 0 then 1 else 2
  distinct := by intro e; fin_cases e <;> decide

def a (e : Fin 3) : ℚ := if e = 2 then 2 else 9
def z (v : Fin 3) : ℚ := if v = 0 then 99/100 else if v = 1 then 593/600 else 3551/3600

theorem a_pos (e : Fin 3) : 0 < a e := by unfold a; split_ifs <;> norm_num

theorem weighted_certificate : rationalFamilyCheck graph a (fun _ => 1) z
    (fun _ => 9/10) (fun _ => 1) = true := by
  apply rationalFamilyCheck_eq_true
  · intro v
    fin_cases v
    · change (9/10 : ℚ) ≤ 99/100 ∧ (99/100 : ℚ) ≤ 1
      norm_num
    · change (9/10 : ℚ) ≤ 593/600 ∧ (593/600 : ℚ) ≤ 1
      norm_num
    · change (9/10 : ℚ) ≤ 3551/3600 ∧ (3551/3600 : ℚ) ≤ 1
      norm_num
  · intro e
    fin_cases e
    · change rationalEdgeCheck 9 1 (99/100) (593/600) = true
      norm_num [rationalEdgeCheck]
    · change rationalEdgeCheck 9 1 (593/600) (3551/3600) = true
      norm_num [rationalEdgeCheck]
    · change rationalEdgeCheck 2 1 (99/100) (3551/3600) = true
      norm_num [rationalEdgeCheck]

theorem weighted_source :
    (∀ v, (9/10 : ℝ) ≤ (z v : ℝ) ∧ (z v : ℝ) ≤ 1) ∧
    ∀ e, (WeightedSource.motif graph (fun e => rationalFactors (a e) 1 (a_pos e) (by norm_num)) e).IsPAC ∧
      (WeightedSource.motif graph (fun e => rationalFactors (a e) 1 (a_pos e) (by norm_num)) e).Productive
        ((WeightedSource.network graph (fun e => rationalFactors (a e) 1 (a_pos e) (by norm_num))).current
          (fun v => (z v : ℝ))) := by
  simpa using rationalFamilyCheck_sound graph a (fun _ => 1) z (fun _ => 9/10)
    (fun _ => 1) a_pos (fun _ => by norm_num) weighted_certificate

theorem nongraded : ¬ ∃ rank : Fin 3 → ℤ, ∀ e, rank (graph.dst e) = rank (graph.src e)+1 := by
  rintro ⟨rank,h⟩
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  change rank 1 = rank 0 + 1 at h₀
  change rank 2 = rank 1 + 1 at h₁
  change rank 2 = rank 0 + 1 at h₂
  omega

theorem unit_source_incompatible : ¬ ∃ x : Fin 3 → ℝ,
    (∀ v, 0 < x v) ∧ ∀ e, (graph.motif e).Productive (graph.network.current x) := by
  rintro ⟨x,hx,hp⟩
  have h₀ := (graph.current_productive_iff 0 x).1 (hp 0)
  have h₁ := (graph.current_productive_iff 1 x).1 (hp 1)
  have h₂ := (graph.current_productive_iff 2 x).1 (hp 2)
  change Hypergraph.Ring.Productive (x 0) (x 1) at h₀
  change Hypergraph.Ring.Productive (x 1) (x 2) at h₁
  change Hypergraph.Ring.Productive (x 0) (x 2) at h₂
  have hh := Hypergraph.PairResponse.two_step (hx 0) (hx 1) h₀ h₁
  have hl := ((Hypergraph.PairResponse.interval_iff _ _).1 h₂).1
  exact lt_asymm hh hl

end ThermoCoreCompatibility.MultiInterface.Examples
