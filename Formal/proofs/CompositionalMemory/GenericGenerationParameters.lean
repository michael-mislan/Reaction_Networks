import proofs.CompositionalMemory.GenericUniformLocalBudgets
import proofs.CompositionalMemory.GenericUniformPartitionParameters
import proofs.CompositionalMemory.GenericGenerationTiming
import proofs.CompositionalMemory.GenericSixErrorBudget

namespace CompositionalMemory

/-- All scalar choices precede the module count and population size. -/
theorem exists_uniform_generation_parameters
    (lam rho M c A P R D U Z L rmax recover parent birth outer lo C : ℝ)
    (hlam : 0 < lam) (hrho : 0 < rho) (hM : 0 < M) (hc : 0 < c)
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hrmax : 0 ≤ rmax)
    (hcore : M*rho < recover) (hrec : recover < parent)
    (hparent : parent < birth) (hbirth : birth < outer) (hlo : 0 < lo) (hC : 0 < C) :
    ∃ α coupling N0 γ t₀ t₁ rpart δ cgen : ℝ,
      0 < α ∧ 0 < coupling ∧ coupling ≤ 1 ∧ 1 ≤ N0 ∧
      0 < γ ∧ γ ≤ coupling ∧ 0 < t₀ ∧ 0 < t₁ ∧
      4*birth ≤ lam*rho*t₀ ∧ γ*Z*t₀ ≤ 2/5 ∧ γ*lo*t₁=11/10 ∧
      0 < rpart ∧ parent ≤ c*rpart^2 ∧ 0 < δ ∧ δ ≤ 1 ∧
      parent+2*L*rpart*δ+L*δ^2 < birth ∧
      0 < cgen ∧ cgen ≤ α*(outer-birth)/2 ∧ cgen ≤ α*(parent-recover)/2 ∧
      cgen ≤ α*(recover-M*rho) ∧ cgen ≤ 1/125 ∧ cgen ≤ 9/4000 ∧ cgen ≤ δ^2/C ∧
      ∀ N r κ : ℝ, N0 ≤ N → 0 ≤ r → r ≤ rmax → 0 ≤ κ → κ ≤ coupling →
        α*(2*(P*r)+R/N) ≤ 1 ∧
        α*(2*L*r*(U+1)+L*(U+1)^2/N) ≤ 1 ∧
        α*(8*A*P^2+8*L^2*γ*Z*(U+1)^2+16*L^2*Z*κ) ≤ lam/4 ∧
        (2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)^2 ≤ lam^2*rho/8 ∧
        (A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
          α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N ≤ lam*N*rho/8 := by
  obtain ⟨α,coupling,N0,hα,hcoupling,hcoupling1,hN0,hbudgets⟩ :=
    exists_uniform_local_budgets lam rho A P R D U Z L rmax
      hlam hrho hA hP hR hD hU hZ hL hrmax
  have hp : 0 < parent := (mul_pos hM hrho).trans (hcore.trans hrec)
  have hb : 0 < birth := hp.trans hparent
  obtain ⟨γ,t₀,t₁,hγ,hγc,ht₀,ht₁,hrecover,hearly,hlate⟩ :=
    exists_generation_timing (lam*rho) birth Z lo coupling (mul_pos hlam hrho) hb.le hZ hlo hcoupling
  obtain ⟨rpart,hrpart,hsize⟩ := exists_coercive_parent_radius c parent hc hp.le
  obtain ⟨δ,hδ,hδ1,hmargin⟩ := exists_partition_tolerance L rpart parent birth hL hrpart.le hparent
  obtain ⟨cgen,hcgen,hc₀,hc₁,hcr,hce,hcl,hcp⟩ :=
    exists_generation_exponent α (outer-birth) (parent-recover) (recover-M*rho) δ C
      hα (sub_pos.mpr hbirth) (sub_pos.mpr hrec) (sub_pos.mpr hcore) hδ hC
  refine ⟨α,coupling,N0,γ,t₀,t₁,rpart,δ,cgen,hα,hcoupling,hcoupling1,hN0,
    hγ,hγc,ht₀,ht₁,hrecover,hearly,hlate,hrpart,hsize,hδ,hδ1,hmargin,
    hcgen,hc₀,hc₁,hcr,hce,hcl,hcp,?_⟩
  intro N r κ hN hr hrr hκ hκc
  exact hbudgets N r γ κ hN hr hrr hγ.le hγc hκ hκc

/-- A common positive growth interval; the exponent and copy floor do not depend on the chosen rate. -/
theorem exists_uniform_generation_interval
    (lam rho M c A P R D U Z L rmax recover parent birth outer lo C : ℝ)
    (hlam : 0 < lam) (hrho : 0 < rho) (hM : 0 < M) (hc : 0 < c)
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hrmax : 0 ≤ rmax)
    (hcore : M*rho < recover) (hrec : recover < parent)
    (hparent : parent < birth) (hbirth : birth < outer) (hlo : 0 < lo) (hC : 0 < C) :
    ∃ α coupling N0 γ₀ t₀ rpart δ cgen : ℝ,
      0 < α ∧ 0 < coupling ∧ coupling ≤ 1 ∧ 1 ≤ N0 ∧
      0 < γ₀ ∧ γ₀ ≤ coupling ∧ 0 < t₀ ∧
      0 < rpart ∧ parent ≤ c*rpart^2 ∧ 0 < δ ∧ δ ≤ 1 ∧
      parent+2*L*rpart*δ+L*δ^2 < birth ∧
      0 < cgen ∧ cgen ≤ α*(outer-birth)/2 ∧ cgen ≤ α*(parent-recover)/2 ∧
      cgen ≤ α*(recover-M*rho) ∧ cgen ≤ 1/125 ∧ cgen ≤ 9/4000 ∧ cgen ≤ δ^2/C ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ → ∃ t₁ : ℝ,
      0 < t₁ ∧ 4*birth ≤ lam*rho*t₀ ∧ γ*Z*t₀ ≤ 2/5 ∧ γ*lo*t₁=11/10 ∧
      ∀ N r κ : ℝ, N0 ≤ N → 0 ≤ r → r ≤ rmax → 0 ≤ κ → κ ≤ coupling →
        α*(2*(P*r)+R/N) ≤ 1 ∧
        α*(2*L*r*(U+1)+L*(U+1)^2/N) ≤ 1 ∧
        α*(8*A*P^2+8*L^2*γ*Z*(U+1)^2+16*L^2*Z*κ) ≤ lam/4 ∧
        (2*L*D/N+2*L*γ*Z*(U+1)+4*L*Z*κ)^2 ≤ lam^2*rho/8 ∧
        (A*R+L*γ*Z*(U+1)^2+2*L*Z*κ)+
          α*(2*A*R^2+2*L^2*γ*Z*(U+1)^4+4*L^2*Z*κ)/N ≤ lam*N*rho/8 := by
  obtain ⟨α,coupling,N0,hα,hcoupling,hcoupling1,hN0,hbudgets⟩ :=
    exists_uniform_local_budgets lam rho A P R D U Z L rmax
      hlam hrho hA hP hR hD hU hZ hL hrmax
  have hp : 0 < parent := (mul_pos hM hrho).trans (hcore.trans hrec)
  have hb : 0 < birth := hp.trans hparent
  obtain ⟨γ₀,t₀,_t₁,hγ₀,hγ₀c,ht₀,_ht₁,hrecover,hearly,_hlate⟩ :=
    exists_generation_timing (lam*rho) birth Z lo coupling (mul_pos hlam hrho) hb.le hZ hlo hcoupling
  obtain ⟨rpart,hrpart,hsize⟩ := exists_coercive_parent_radius c parent hc hp.le
  obtain ⟨δ,hδ,hδ1,hmargin⟩ := exists_partition_tolerance L rpart parent birth hL hrpart.le hparent
  obtain ⟨cgen,hcgen,hc₀,hc₁,hcr,hce,hcl,hcp⟩ :=
    exists_generation_exponent α (outer-birth) (parent-recover) (recover-M*rho) δ C
      hα (sub_pos.mpr hbirth) (sub_pos.mpr hrec) (sub_pos.mpr hcore) hδ hC
  refine ⟨α,coupling,N0,γ₀,t₀,rpart,δ,cgen,hα,hcoupling,hcoupling1,hN0,
    hγ₀,hγ₀c,ht₀,hrpart,hsize,hδ,hδ1,hmargin,hcgen,hc₀,hc₁,hcr,hce,hcl,hcp,?_⟩
  intro γ hγ hγmax
  refine ⟨11/(10*γ*lo),by positivity,hrecover,?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγmax hZ) ht₀.le).trans hearly
  · field_simp
  · intro N r κ hN hr hrr hκ hκc
    exact hbudgets N r γ κ hN hr hrr hγ.le (hγmax.trans hγ₀c) hκ hκc

end CompositionalMemory
