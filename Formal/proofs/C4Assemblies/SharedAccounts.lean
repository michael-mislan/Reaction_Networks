import proofs.C4Assemblies.OutputSupplies

namespace C4Assemblies
noncomputable section
open ProductiveRecovery MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem assembly_conditioning_supplies (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyAdmitted c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    ∀ i, 12+(1-(p i).q+(p i).eU) ≤ 2551/200 ∧
      12+(1-(p i).q+(p i).eW) ≤ 2551/200 ∧
      (∫ t in (0:ℝ)..12, P.d i*X t i 2+P.d i*(1/8000000000)*X t i 0*X t i 1) ≤ 27/50 := by
  have hcor := (assembly_material_bounds P p c hc X h0 hX).1
  intro i
  have hcont : ContinuousOn (fun t => X t i) (Icc (0:ℝ) 12) := fun t ht =>
    (hasDerivAt_pi.1 (hX t ht.1) i).continuousAt.continuousWithinAt
  have hg : Continuous (fun c : State => P.d i*c 2+P.d i*(1/8000000000)*c 0*c 1) := by fun_prop
  have hi : IntervalIntegrable (fun t => P.d i*X t i 2+P.d i*(1/8000000000)*X t i 0*X t i 1) volume 0 12 :=
    (hg.comp_continuousOn hcont).intervalIntegrable_of_Icc (by norm_num)
  have hh := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 12) (by norm_num) hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (9/200:ℝ)) volume 0 12)
    (fun t ht => gross_service_bound (P.d i) (X t i) (hn t ht.1 i) (P.d_upper i)
      (hcor t ht.1 i).1.2 (hcor t ht.1 i).2.2)
  obtain ⟨_,hu,_,hw⟩ := food_feasible (p i)
  refine ⟨by linarith,by linarith,?_⟩
  norm_num at hh
  exact hh

def grossTransfer (k : ι → ι → ℝ) (c : Assembly ι) : ℝ :=
  ∑ i, ∑ j, k i j*(∑ s : Fin 6, c i s)

theorem species_sum_le_material (c : State) (hc : Nonneg c) :
    (∑ s : Fin 6, c s) ≤ A c+B c := by
  norm_num [Fin.sum_univ_succ,A,B]
  change c 0+(c 1+(c 2+(c 3+(c 4+c 5)))) ≤
    c 0+c 2+2*c 3+2*c 4+2*c 5+(c 1+c 2+c 3+2*c 4+2*c 5)
  linarith [hc 2,hc 3,hc 4,hc 5]

theorem gross_transfer_bound (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j)
    (c : Assembly ι) (hc : ∀ i, Nonneg (c i))
    (ha : ∀ i, A (c i) ≤ 11/10) (hb : ∀ i, B (c i) ≤ 11/10) :
    grossTransfer k c ≤ (11/5)*(∑ i, ∑ j, k i j) := by
  have hsum : ∀ i, (∑ s : Fin 6, c i s) ≤ 11/5 := by
    intro i
    have h := species_sum_le_material (c i) (hc i)
    linarith [ha i,hb i]
  unfold grossTransfer
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_comm,Finset.mul_sum] using mul_le_mul_of_nonneg_left (hsum i) (hk i j)

/-- One shared quota dominates every prefix of a nondecreasing mission account. -/
theorem common_quota_prefix (spend : ℝ → ℝ) (T quota : ℝ)
    (hm : MonotoneOn spend (Icc 0 T)) (hT : 0 ≤ T) (hq : spend T ≤ quota) :
    ∀ t ∈ Icc 0 T, spend t ≤ quota := by
  intro t ht
  exact (hm ht ⟨hT,le_rfl⟩ ht.2).trans hq

/-- A cutoff equation agrees with the maintained field at every certified prefix. -/
theorem cutoff_field_agreement {E : Type*} [Zero E]
    (f : ℝ → E) (spend : ℝ → ℝ) (T quota : ℝ)
    (hm : MonotoneOn spend (Icc 0 T)) (hT : 0 ≤ T) (hq : spend T ≤ quota) :
    ∀ t ∈ Icc 0 T, (if spend t ≤ quota then f t else 0) = f t := by
  intro t ht
  exact if_pos (common_quota_prefix spend T quota hm hT hq t ht)

end
end C4Assemblies
