import proofs.HeritableCompositions.StoppedGrowth
import proofs.FiniteCopy.ExponentialFoster

namespace HeritableCompositions
open FiniteCopy

noncomputable def growthGenerator (γ : ℝ) (m : ℕ) (f : Point → ℝ) (x : Point) : ℝ :=
  generator (1/100000) m f x + γ*(m : ℝ)*x 2*
    (f (fun i => x i-(1/((m : ℝ)+1))*(x i+membraneDirection i))-f x)

theorem compartment_generator_binding (γ : ℝ) (m : ℕ) (hm : 0 < m)
    (n : Counts) (f : Point → ℝ) :
    compartmentGenerator γ (fun s => f (concentration s.2 s.1)) (n,m) =
      growthGenerator γ m f (concentration m n) := by
  classical
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hres (r : Fin 13) :
      propensity γ (n,m) (.inl r)*
        (f (concentration (nextCompartment (n,m) (.inl r)).2
          (nextCompartment (n,m) (.inl r)).1)-f (concentration m n)) =
      (m : ℝ)*(densityRates (1/100000) (1/(m : ℝ)) (concentration m n) r*
        (f (fun i => concentration m n i+jump r i/(m : ℝ))-f (concentration m n))) := by
    by_cases hr : reactants n r
    · simp only [propensity,nextCompartment,concentration_next m n r hr]
      ring
    · have hh := disabled_density_zero (1/100000) m n r hr
      simp only [one_div] at hh
      simp [propensity,hh]
  have hmem : propensity γ (n,m) (.inr ()) *
      (f (concentration (nextCompartment (n,m) (.inr ())).2
        (nextCompartment (n,m) (.inr ())).1)-f (concentration m n)) =
      γ*(m : ℝ)*concentration m n 2*
        (f (fun i => concentration m n i-(1/((m : ℝ)+1))*
          (concentration m n i+membraneDirection i))-f (concentration m n)) := by
    by_cases hn : 1 ≤ n 2
    · have hx : concentration (nextCompartment (n,m) (.inr ())).2
          (nextCompartment (n,m) (.inr ())).1 =
          fun i => concentration m n i-(1/((m : ℝ)+1))*(concentration m n i+membraneDirection i) := by
        funext i
        have hh := membrane_concentration_update (n,m) hm hn i
        dsimp only at hh
        calc
          _ = -(concentration m n i+membraneDirection i)/((m : ℝ)+1)+concentration m n i :=
            eq_add_of_sub_eq hh
          _ = _ := by ring
      have hrate : γ*(m : ℝ)*concentration m n 2 = γ*(n 2 : ℝ) := by
        dsimp [concentration]
        field_simp
      rw [hx]
      rw [hrate]
      rfl
    · have hn0 : n 2=0 := by omega
      simp [propensity,concentration,hn0]
  unfold compartmentGenerator growthGenerator generator
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique]
  rw [hmem,Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun r _ => hres r)

end HeritableCompositions
