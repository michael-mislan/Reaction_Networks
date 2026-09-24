import proofs.C4Assemblies.Family
import proofs.C4Assemblies.GlobalFlow
import proofs.C4Assemblies.Material
import proofs.C4Assemblies.StockRecovery

namespace C4Assemblies
noncomputable section
open ProductiveRecovery
variable {ι : Type*} [Fintype ι]

theorem assembly_material_bounds (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyAdmitted c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    (∀ t, 0 ≤ t → ∀ i, (9/10 ≤ A (X t i) ∧ A (X t i) ≤ 11/10) ∧
      (9/10 ≤ B (X t i) ∧ B (X t i) ≤ 11/10)) ∧
    (∀ t, 3 ≤ t → ∀ i, (159/160 ≤ A (X t i) ∧ A (X t i) ≤ 161/160) ∧
      (159/160 ≤ B (X t i) ∧ B (X t i) ≤ 161/160)) := by
  have hda : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => A (X s i))
      (1-A (X t i)+diffusion P.k (fun j => A (X t j)) i) t := by
    intro t ht i
    simpa only [assembly_A] using deriv_A (fun s => X s i) _ t (hasDerivAt_pi.1 (hX t ht) i)
  have hdb : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => B (X s i))
      (1-B (X t i)+diffusion P.k (fun j => B (X t j)) i) t := by
    intro t ht i
    simpa only [assembly_B] using deriv_B (fun s => X s i) _ t (hasDerivAt_pi.1 (hX t ht) i)
  have hinit (i : ι) := pulse_material (p i) (c i) (hc i).1 (hc i).2.1 (hc i).2.2.1
  have ha0 : ∀ i, |A (X 0 i)-1| ≤ 1/10 := by
    intro i
    rw [h0]
    obtain ⟨ha,_⟩ := hinit i
    apply abs_le.mpr
    dsimp [assemblyPulse]
    constructor <;> linarith [ha.1,ha.2]
  have hb0 : ∀ i, |B (X 0 i)-1| ≤ 1/10 := by
    intro i
    rw [h0]
    obtain ⟨_,hb⟩ := hinit i
    apply abs_le.mpr
    dsimp [assemblyPulse]
    constructor <;> linarith [hb.1,hb.2]
  have ha := material_decay P.k P.exchange_nonneg (fun t i => A (X t i)) (1/10) hda ha0
  have hb := material_decay P.k P.exchange_nonneg (fun t i => B (X t i)) (1/10) hdb hb0
  have hca (i : ι) := corridor_from_decay (fun t => A (X t i)) (fun t ht => ha t ht i)
  have hcb (i : ι) := corridor_from_decay (fun t => B (X t i)) (fun t ht => hb t ht i)
  exact ⟨fun t ht i => ⟨(hca i).1 t ht,(hcb i).1 t ht⟩,
    fun t ht i => ⟨(hca i).2 t ht,(hcb i).2 t ht⟩⟩

theorem assembly_trajectory_return (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyAdmitted c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c)
    (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t)
    (b0 D : ℝ) (hb0 : 0 < b0) (hy0 : ∀ i, b0 ≤ Y (X 0 i))
    (hD : 0 ≤ D) (he : (1/20)/b0 ≤ Real.exp ((3/5)*D)) :
    (∀ t, D ≤ t → ∀ i, 1/20 ≤ Y (X t i)) ∧
    ∀ t, max 3 D ≤ t → AssemblyReady (X t) := by
  obtain ⟨hcor,hmat⟩ := assembly_material_bounds P p c hc X h0 hX
  have hy := assembly_scheduled_recovery (fun t i => Y (X t i))
    (fun t i => Y (assemblyField P.k P.r P.d (X t) i))
    (fun t ht i => deriv_Y (fun s => X s i) _ t (hasDerivAt_pi.1 (hX t ht) i))
    b0 D hb0 hy0 hD he (fun t ht i _ hlow hmin =>
      assembly_guarded_growth_at_min P.k P.exchange_nonneg P.r P.d (X t) i
        (hn t ht i) (P.r_lower i) (P.r_upper i) (by linarith [P.d_lower i])
        (P.d_upper i) (hcor t ht i).1.1 (hcor t ht i).2.1 hlow hmin)
  refine ⟨hy,?_⟩
  intro t ht i
  have ht3 : 3 ≤ t := (le_max_left _ _).trans ht
  have htD : D ≤ t := (le_max_right _ _).trans ht
  exact ⟨hn t (by linarith) i,(hmat t ht3 i).1,(hmat t ht3 i).2,hy t htD i⟩

end
end C4Assemblies
