import proofs.CompositionalMemory.CoupledCounts
import proofs.CompositionalMemory.ScalingLocalGenerator

namespace CompositionalMemory
open FiniteCopy

noncomputable def modularConcentration {k : ℕ} (s : ModularCountState k) (i : Fin k) : Point :=
  effectiveConcentration ((s.2 : ℝ)/k) (s.1 i)

theorem resident_local_term {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (s : ModularCountState k) (i j : Fin k) (r : Fin 13) (W : Point → ℝ) :
    modularRate γ w s (.inl (j,r))*
      (W (modularConcentration (modularNext s (.inl (j,r))) i)-W (modularConcentration s i)) =
    if j=i then ((s.2 : ℝ)/k)*densityRates (1/100000) (1/((s.2 : ℝ)/k))
      (modularConcentration s i) r*
      (W (fun a => modularConcentration s i a+jump r a/((s.2 : ℝ)/k))-W (modularConcentration s i))
    else 0 := by
  classical
  by_cases h : j=i
  · subst j
    simp only [modularRate,modularNext,modularConcentration,Function.update_self,ite_true]
    by_cases hr : reactants (s.1 i) r
    · rw [effective_concentration_next _ _ _ hr]
    · have hz := effective_disabled_density (1/100000) ((s.2 : ℝ)/k) (s.1 i) r hr
      rw [hz]
      simp only [mul_zero,zero_mul]
  · simp [modularRate,modularNext,modularConcentration,h,Ne.symm h]

theorem membrane_concentration_local {k : ℕ} (hk : 1 ≤ k)
    (s : ModularCountState k) (hm : 0 < s.2) (i j : Fin k) (hn : 1 ≤ s.1 j 2) :
    modularConcentration (modularNext s (.inr (.inr j))) i =
      fun a => modularConcentration s i a+localMembraneJump (s.2 : ℝ) i j (modularConcentration s i) a := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hm0 : (s.2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hm1 : (s.2 : ℝ)+1 ≠ 0 := by positivity
  by_cases h : j=i
  · subst j
    simp only [modularNext,modularConcentration,Function.update_self]
    change effectiveConcentration (((s.2+1 : ℕ) : ℝ)/k)
      (Function.update (s.1 i) 2 (s.1 i 2-1)) = _
    funext a
    dsimp [effectiveConcentration,modularConcentration,localMembraneJump]
    rw [consuming_count_cast (s.1 i) hn a,Nat.cast_add,Nat.cast_one]
    simp only [ite_true]
    split_ifs <;> field_simp [hk0,hm0,hm1] <;> ring
  · funext a
    simp [modularNext,modularConcentration,effectiveConcentration,localMembraneJump,
      h,Ne.symm h]
    field_simp [hk0,hm0,hm1]
    ring

theorem membrane_local_term {k : ℕ} (hk : 1 ≤ k) (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (s : ModularCountState k) (hm : 0 < s.2)
    (i j : Fin k) (W : Point → ℝ) :
    modularRate γ w s (.inr (.inr j))*
      (W (modularConcentration (modularNext s (.inr (.inr j))) i)-W (modularConcentration s i)) =
    incidentRate γ (s.2 : ℝ) (fun j => modularConcentration s j 2) (w i) i (.inl j)*
      (W (fun a => modularConcentration s i a+localIncidentJump (s.2 : ℝ) i
        (modularConcentration s i) (.inl j) a)-W (modularConcentration s i)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hmpos : (0 : ℝ) < s.2 := by exact_mod_cast hm
  have hrate : ((s.2 : ℝ)/k)*modularConcentration s j 2 = (s.1 j 2 : ℝ) := by
    dsimp [modularConcentration,effectiveConcentration]
    field_simp
  by_cases hn : 1 ≤ s.1 j 2
  · rw [membrane_concentration_local hk s hm i j hn]
    simp only [modularRate,incidentRate,localIncidentJump,Sum.elim_inl]
    rw [show γ*((s.2 : ℝ)/k)*modularConcentration s j 2 = γ*(s.1 j 2 : ℝ) by
      rw [mul_assoc,hrate]]
  · have hn0 : s.1 j 2=0 := by omega
    simp [modularRate,incidentRate,modularConcentration,effectiveConcentration,hn0]

end CompositionalMemory
