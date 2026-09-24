import proofs.RAF1519.Reservoir.CommunityCoercivity
import proofs.RAF1519.Reservoir.CoreEnergy
import proofs.RAF1519.Reservoir.EnergyNeighborhood

namespace RAF1519.Reservoir
noncomputable section
open Set Filter Topology
open scoped BigOperators

theorem communityField_contDiff {n : ℕ} (q : Fin n → ℝ) : ContDiff ℝ 1 (communityField q) := by
  apply contDiff_pi.2
  intro i
  cases i with
  | inl i =>
    change ContDiff ℝ 1 (fun x : Community n => field (aggregate x) i.castSucc)
    have h := field_contDiff.comp (@aggregate_contDiff n)
    exact contDiff_pi.1 h i.castSucc
  | inr i =>
    change ContDiff ℝ 1 (fun x : Community n =>
      x (.inr i)*(x (.inl 4)*x (.inl 2)-1/2-x (.inr i)/q i))
    fun_prop

theorem stationary_growth (s : ℝ) (hs : 0 < s) (hf : field (state s) = 0) :
    reservoir s*resource s-1/2-2*s = -s := by
  have h := congrFun hf 5
  change s*(reservoir s*resource s-1/2-s) = 0 at h
  have h' := (mul_eq_zero.mp h).resolve_left (ne_of_gt hs)
  linarith

/-- A full-community attraction theorem. Every energy/source hypothesis here
is supplied by the fixed source certificates in the final root assembly. -/
theorem community_attraction {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Fin n → ℝ) (hq : ∑ i, q i = 1) (hpos : ∀ i, 0 < q i)
    (s : ℝ) (l u : Fin 6 → ℝ) (hs : 3/100 < s) (hf : field (state s) = 0)
    (hpositive : ∀ i, 0 < lift q s i)
    (hbox : ∀ i, l i < state s i ∧ state s i < u i)
    (hP : ∀ y, (1/1000:ℝ)*(∑ i, (y i)^2) ≤ quadratic P y)
    (hdec : ∀ x, InBox l u x → quadraticRate P (field x) (x-state s) ≤
      -(1/400:ℝ)*quadratic P (x-state s)) :
    ∃ ε > 0, ∀ x₀, dist x₀ (lift q s) < ε →
      ∃ X : ℝ → Community n, X 0 = x₀ ∧
        (∀ t, 0 ≤ t → HasDerivAt X (communityField q (X t)) t) ∧
        (∀ t, 0 ≤ t → ∀ i, 0 < X t i) ∧ Tendsto X atTop (𝓝 (lift q s)) := by
  have ha := (@aggregate_contDiff n).continuous.continuousAt (x := lift q s)
  have hboxN : ∀ᶠ x in 𝓝 (lift q s), InBox l u (aggregate x) := by
    apply eventually_all.2
    intro i
    have hi := continuousAt_pi.1 ha i
    have hci : l i < aggregate (lift q s) i ∧ aggregate (lift q s) i < u i := by
      rw [aggregate_lift q hq s]
      exact hbox i
    filter_upwards [hi.eventually (Ioo_mem_nhds hci.1 hci.2)] with x hx
    exact ⟨hx.1.le,hx.2.le⟩
  have hgradN : ∀ᶠ x in 𝓝 (lift q s),
      |quadraticRate P consumerAxis (aggregate x-state s)| ≤ 1 := by
    have hc : ContinuousAt (fun x : Community n => quadraticRate P consumerAxis (aggregate x-state s))
        (lift q s) := by
      have hagg := (@aggregate_contDiff n).continuous
      unfold quadraticRate
      fun_prop
    have hz : quadraticRate P consumerAxis (aggregate (lift q s)-state s) = 0 := by
      simp [aggregate_lift q hq s,quadraticRate]
    have hlo : (-1:ℝ) < quadraticRate P consumerAxis (aggregate (lift q s)-state s) := by rw [hz]; norm_num
    have hhi : quadraticRate P consumerAxis (aggregate (lift q s)-state s) < (1:ℝ) := by rw [hz]; norm_num
    filter_upwards [hc.eventually (Ioo_mem_nhds hlo hhi)] with x hx
    exact abs_le.mpr ⟨hx.1.le,hx.2.le⟩
  have hgN : ∀ᶠ x in 𝓝 (lift q s),
      x (.inl 4)*x (.inl 2)-1/2-2*totalConsumers x ≤ -3/100 := by
    have hc : ContinuousAt (fun x : Community n => x (.inl 4)*x (.inl 2)-1/2-2*totalConsumers x)
        (lift q s) := by unfold totalConsumers; fun_prop
    have hz : lift q s (.inl 4)*lift q s (.inl 2)-1/2-2*totalConsumers (lift q s) = -s := by
      rw [total_lift q hq s]
      exact stationary_growth s (by linarith) hf
    have hlt : lift q s (.inl 4)*lift q s (.inl 2)-1/2-2*totalConsumers (lift q s) < -3/100 := by
      rw [hz]; linarith
    filter_upwards [hc.eventually (Iio_mem_nhds hlt)] with x hx
    exact hx.le
  have hyN : ∀ᶠ x in 𝓝 (lift q s), ∀ i, -(1/100:ℝ) ≤ normalizedDeviation q x i := by
    apply eventually_all.2
    intro i
    have hc := continuousAt_pi.1
      ((deviation_contDiff q).continuous.continuousAt (x := lift q s)) i
    have hz : normalizedDeviation q (lift q s) i = 0 := congrFun (deviation_lift q hq hpos s) i
    have hlt : -(1/100:ℝ) < normalizedDeviation q (lift q s) i := by rw [hz]; norm_num
    filter_upwards [hc.eventually (Ioi_mem_nhds hlt)] with x hx
    exact hx.le
  have hposN : ∀ᶠ x in 𝓝 (lift q s), ∀ i, 0 < x i := by
    apply eventually_all.2
    intro i
    exact (continuous_apply i).continuousAt.eventually (Ioi_mem_nhds (hpositive i))
  apply local_energy_attraction (communityField q) (communityEnergy P q s)
    (fun x => fderiv ℝ (communityEnergy P q s) x) (lift q s) {x | ∀ i, 0 < x i}
    2000 (1/400) (by norm_num) (by norm_num) (communityField_contDiff q)
    (fun x => ((communityEnergy_contDiff P q s).differentiable (by norm_num) x).hasFDerivAt)
    (communityEnergy_center P q hq hpos s)
    (fun x => communityEnergy_nonnegative P q hpos s x hP)
    (communityEnergy_coercive P q hq hpos s hP)
  filter_upwards [hboxN,hgradN,hgN,hyN,hposN] with x hx hgrad hg hy hp
  exact ⟨communityEnergy_source_decay P q s x hq hpos (hdec (aggregate x) hx) hgrad hg hy,hp⟩

end
end RAF1519.Reservoir
