import proofs.CommonEnvironmentProtection.LiteralSteady
import proofs.CommonEnvironmentProtection.SourceExample

namespace CommonEnvironmentProtection
noncomputable section
open SourceFamilies LiteralSteady CoupledPrivate

/-- Root theorem: literal enzyme/carrier steady states under one shared source
exist exactly above the sharp regeneration threshold, in the stated admitted
positive-pool, attainable-quota domain. No equilibrium witness is assumed. -/
theorem jointProtection_iff_minimumRegeneration
    (G : Glutathione) (T : Thioredoxin) (s V N D qG qT : ℝ)
    (hs : 0<s) (hV : 0<V) (hND : N<D) (hqG : 0<qG) (hqT : 0<qT)
    (hcapG : 0<G.branch.p-qG*G.branch.v) (hcapT : 0<T.branch.p-qT*T.branch.v)
    (hmG : 0<G.branch.margin qG) (hmT : 0<T.branch.margin qT)
    (hLN : max (G.branch.floor qG) (T.branch.floor qT)<N) :
    FullJoint G T s V N D qG qT ↔
      minimumScale G.branch T.branch V N D
        (max (G.branch.floor qG) (T.branch.floor qT))≤s :=
  (full_joint_iff_pool G T s V N D qG qT).trans
    (pool_joint_iff_repair G T s V N D qG qT hs hV hND hqG hqT hcapG hcapT hmG hmT hLN)

open SourceExample

theorem source_initial_incompatible :
    ¬FullJoint glutathione thioredoxin (1/10) 375 30 (873/10) 10 4 := by
  rw [full_joint_iff_pool]
  exact initial_joint_fails

theorem source_certified_repair :
    FullJoint glutathione thioredoxin (11371268/100000000) 375 30 (873/10) 10 4 := by
  rw [full_joint_iff_pool]
  exact certified_repair_passes

theorem source_exact_minimum_attained :
    FullJoint glutathione thioredoxin requiredScale 375 30 (873/10) 10 4 ∧
    ∀ s : ℝ, 0<s → s<requiredScale →
      ¬FullJoint glutathione thioredoxin s 375 30 (873/10) 10 4 := by
  have hp : 0<requiredScale := by have h := certified_scale_bounds.1; linarith
  constructor
  · rw [full_joint_iff_pool,exact_joint_boundary _ hp]
    exact le_rfl
  · intro s hs hlt
    rw [full_joint_iff_pool,exact_joint_boundary _ hs]
    exact not_le_of_gt hlt

end
end CommonEnvironmentProtection
