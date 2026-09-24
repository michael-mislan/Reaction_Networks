import proofs.CompositionalMemory.GenericGlobalReactions
import proofs.CompositionalMemory.GenericMembraneGeometry

namespace CompositionalMemory

theorem unit_consumption_count_cast {d : ℕ} (z : Fin d) (n : Fin d → ℕ)
    (hn : 1 ≤ n z) (a : Fin d) :
    (countReactionNext (speciesUnit z) (fun _ => 0) n a:ℝ) =
      (n a:ℝ)-(if a=z then 1 else 0) := by
  have hneed : speciesUnit z a ≤ n a := by
    by_cases h : a=z
    · subst a; simpa [speciesUnit] using hn
    · simp [speciesUnit,h]
  change ((n a-speciesUnit z a+0:ℕ):ℝ) = _
  rw [Nat.add_zero,Nat.cast_sub hneed]
  simp [speciesUnit]

theorem general_membrane_concentration {k d : ℕ} (hk : 1 ≤ k) (z : Fin d)
    (s : GeneralCountState k d) (hm : 0 < s.2) (i j : Fin k) (hn : 1 ≤ s.1 j z) :
    generalConcentration (generalMembraneNext z s j) i =
      generalConcentration s i + membraneVectorJump (generalConcentration s i)
        (fun a => if a=z then (1:ℝ) else 0) (if j=i then (k:ℝ) else 0) s.2 := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hm0 : (s.2:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hm1 : (s.2:ℝ)+1 ≠ 0 := by positivity
  have hz : s.1 j z ≠ 0 := by omega
  by_cases h : j=i
  · subst j
    funext a
    simp [generalMembraneNext,hz,generalConcentration,membraneVectorJump,
      unit_consumption_count_cast z (s.1 i) hn a]
    split_ifs <;> field_simp [hk0,hm0,hm1] <;> ring
  · funext a
    simp [generalMembraneNext,hz,generalConcentration,membraneVectorJump,h,Ne.symm h]
    field_simp [hk0,hm0,hm1]
    ring

theorem general_membrane_observable_local {k d : ℕ} (hk : 1 ≤ k) (z : Fin d)
    (s : GeneralCountState k d) (hm : 0 < s.2) (i j : Fin k) (γ : ℝ)
    (W : (Fin d → ℝ) → ℝ) :
    (γ*(s.1 j z:ℝ))*(W (generalConcentration (generalMembraneNext z s j) i)-W (generalConcentration s i)) =
    (γ*((s.2:ℝ)/k)*generalConcentration s j z)*
      (W (generalConcentration s i+membraneVectorJump (generalConcentration s i)
        (fun a => if a=z then (1:ℝ) else 0) (if j=i then (k:ℝ) else 0) s.2)-W (generalConcentration s i)) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hm0 : (s.2:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hrate : γ*((s.2:ℝ)/k)*generalConcentration s j z=γ*(s.1 j z:ℝ) := by
    unfold generalConcentration
    field_simp
  rw [hrate]
  by_cases hn : 1 ≤ s.1 j z
  · rw [general_membrane_concentration hk z s hm i j hn]
  · have hz : s.1 j z=0 := by omega
    simp [hz]

end CompositionalMemory
