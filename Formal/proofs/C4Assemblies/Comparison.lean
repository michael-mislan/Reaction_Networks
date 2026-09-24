import proofs.C4Assemblies.Transport

namespace C4Assemblies
noncomputable section
open Set Filter Topology

variable {ι : Type*} [Fintype ι]

/-- Finite simultaneous first-contact principle, including changing active vertices. -/
theorem finite_strict_lower_barrier (y v : ℝ → ι → ℝ) (a b : ℝ)
    (hd : ∀ t ∈ Icc a b, ∀ i, HasDerivAt (fun s => y s i) (v t i) t)
    (h0 : ∀ i, 0 ≤ y a i)
    (hv : ∀ t ∈ Ico a b, (∀ i, 0 ≤ y t i) → ∀ i, y t i = 0 → 0 < v t i) :
    ∀ t ∈ Icc a b, ∀ i, 0 ≤ y t i := by
  let S : Set ℝ := {t | ∀ i, 0 ≤ y t i}
  have hc : ContinuousOn y (Icc a b) := continuousOn_pi.2 fun i t ht =>
    (hd t ht i).continuousAt.continuousWithinAt
  have hclosed : IsClosed (S ∩ Icc a b) := by
    rw [inter_comm]
    exact hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici : IsClosed (Ici (0 : ι → ℝ)))
  apply hclosed.Icc_subset_of_forall_mem_nhdsWithin h0
  rintro t ⟨htS, ht⟩
  have he : ∀ i, ∀ᶠ s in 𝓝[>] t, 0 ≤ y s i := by
    intro i
    rcases (htS i).lt_or_eq with hp | heq
    · have hh : ∀ᶠ s in 𝓝 t, 0 < y s i :=
        (hd t (Ico_subset_Icc_self ht) i).continuousAt (Ioi_mem_nhds hp)
      exact (hh.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
    · have hz : y t i = 0 := heq.symm
      have hp := hv t ht htS i hz
      have hs : Tendsto (slope (fun s => y s i) t) (𝓝[>] t) (𝓝 (v t i)) :=
        (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).1
          (hd t (Ico_subset_Icc_self ht) i).hasDerivWithinAt
      have hh := hs (Ioi_mem_nhds hp)
      filter_upwards [hh, self_mem_nhdsWithin] with s hsl hst
      change 0 < slope (fun s => y s i) t s at hsl
      rw [slope_def_field, hz, sub_zero] at hsl
      exact ((div_pos_iff_of_pos_right (sub_pos.mpr hst)).1 hsl).le
  exact Filter.eventually_all.2 he

end
end C4Assemblies
