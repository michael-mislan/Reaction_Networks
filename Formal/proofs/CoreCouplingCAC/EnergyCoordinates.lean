import proofs.CoreCouplingCAC.LocalEnergy

namespace CoreCouplingCAC

noncomputable def energyVelocity (L R c x v : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, 2*(L i/R i)*(x i-c i)*v i

theorem energy_hasDerivAt (L R c : Fin 4 → ℝ)
    (x : ℝ → Fin 4 → ℝ) (v : Fin 4 → ℝ) (t : ℝ)
    (hd : HasDerivAt x v t) :
    HasDerivAt (fun s => energy L R c (x s)) (energyVelocity L R c (x t) v) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => ((((hasDerivAt_pi.1 hd) i).sub_const (c i)).pow 2).const_mul (L i/R i))
  convert h using 1
  unfold energyVelocity
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

theorem energy_coordinate_small (L R c x : Fin 4 → ℝ)
    (hw : ∀ i, (1/4:ℝ) ≤ L i/R i)
    (he : energy L R c x ≤ (1/1000000000000:ℝ)) (i : Fin 4) :
    |x i-c i| ≤ (1/200000:ℝ) := by
  have hn : ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      0 ≤ (L j/R j)*(x j-c j)^2 := by
    intro j _
    exact mul_nonneg (by linarith [hw j]) (sq_nonneg _)
  have hi : (L i/R i)*(x i-c i)^2 ≤ energy L R c x :=
    Finset.single_le_sum hn (Finset.mem_univ i)
  have hmul := mul_nonneg (sub_nonneg.mpr (hw i)) (sq_nonneg (x i-c i))
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (x i-c i)]

theorem energy_hasDerivWithinAt (p : Rates) (L R c : Fin 4 → ℝ)
    (x : ℝ → Fin 4 → ℝ) (t : ℝ) (S : Set ℝ)
    (hd : ∀ i, HasDerivWithinAt (fun s => x s i) (dynamics p (x t) i) S t) :
    HasDerivWithinAt (fun s => energy L R c (x s)) (energyRate p L R c (x t)) S t := by
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ)
    (fun i _ => (((hd i).sub_const (c i)).pow 2).const_mul (L i/R i))
  convert h using 1
  unfold energyRate
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

end CoreCouplingCAC
