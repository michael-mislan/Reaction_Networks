import proofs.RAF1519.Reservoir.CommunityCoordinates
import proofs.RAF1519.Reservoir.QuadraticCalculus

namespace RAF1519.Reservoir
noncomputable section
open scoped BigOperators

def communityEnergy {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ) (q : Fin n → ℝ)
    (s : ℝ) (x : Community n) : ℝ :=
  quadratic P (aggregate x-state s)+100*variance q (normalizedDeviation q x)

def communityEnergyRate {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ) (q : Fin n → ℝ)
    (s : ℝ) (x v : Community n) : ℝ :=
  quadraticRate P (aggregate v) (aggregate x-state s)+
    100*∑ i, 2*q i*normalizedDeviation q x i*normalizedDeviation q v i

theorem communityEnergy_contDiff {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Fin n → ℝ) (s : ℝ) : ContDiff ℝ 1 (communityEnergy P q s) := by
  have he := (quadratic_contDiff P (state s)).comp (@aggregate_contDiff n)
  have hv : ContDiff ℝ 1 (fun x : Community n => variance q (normalizedDeviation q x)) := by
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul (((contDiff_pi.1 (deviation_contDiff q)) i).pow 2)
  exact he.add (contDiff_const.mul hv)

theorem communityEnergy_deriv {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Fin n → ℝ) (s : ℝ) (X : ℝ → Community n) (v : Community n) (t : ℝ)
    (hX : HasDerivAt X v t) :
    HasDerivAt (fun t => communityEnergy P q s (X t))
      (communityEnergyRate P q s (X t) v) t := by
  have he := quadratic_deriv P (state s) (fun t => aggregate (X t)) (aggregate v) t
    (aggregate_deriv X v t hX)
  have hv := variance_deriv q (fun t => normalizedDeviation q (X t))
    (normalizedDeviation q v) t (normalizedDeviation_deriv q X v t hX)
  exact he.add (hv.const_mul 100)

theorem communityEnergy_fderiv {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Fin n → ℝ) (s : ℝ) (x v : Community n) :
    fderiv ℝ (communityEnergy P q s) x v = communityEnergyRate P q s x v := by
  have hg : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa only [Pi.add_apply,zero_add,one_smul] using
      (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v)
  have hw := ((communityEnergy_contDiff P q s).differentiable (by norm_num) x).hasFDerivAt
  have hw' : HasFDerivAt (communityEnergy P q s) (fderiv ℝ (communityEnergy P q s) x)
      ((fun t : ℝ => x+t • v) 0) := by simpa only [zero_smul,add_zero] using hw
  have hc := hw'.comp_hasDerivAt (0:ℝ) hg
  have hd := communityEnergy_deriv P q s (fun t : ℝ => x+t • v) v 0 hg
  simpa only [zero_smul,add_zero] using hc.unique hd

theorem quadraticRate_sub_smul {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (v w y : Fin n → ℝ) (a : ℝ) :
    quadraticRate P (v-a • w) y = quadraticRate P v y-a*quadraticRate P w y := by
  unfold quadraticRate
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem communityEnergy_source_decay {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Fin n → ℝ) (s : ℝ) (x : Community n)
    (hq : ∑ i, q i = 1) (hpos : ∀ i, 0 < q i)
    (hcore : quadraticRate P (field (aggregate x)) (aggregate x-state s) ≤
      -(1/400:ℝ)*quadratic P (aggregate x-state s))
    (hgrad : |quadraticRate P consumerAxis (aggregate x-state s)| ≤ 1)
    (hg : x (.inl 4)*x (.inl 2)-1/2-2*totalConsumers x ≤ -3/100)
    (hy : ∀ i, -(1/100:ℝ) ≤ normalizedDeviation q x i) :
    fderiv ℝ (communityEnergy P q s) x (communityField q x) ≤
      -(1/400:ℝ)*communityEnergy P q s x := by
  have hn := variance_nonnegative q (normalizedDeviation q x) (fun i => (hpos i).le)
  have hm := deviation_mean_zero q x hq hpos
  have hv := variance_rate_bound q (normalizedDeviation q x)
    (x (.inl 4)*x (.inl 2)-1/2-2*totalConsumers x) (1/100)
    (fun i => (hpos i).le) hm hy
  have hvar : (∑ i, 2*q i*normalizedDeviation q x i*
      deviationField q (normalizedDeviation q x)
        (x (.inl 4)*x (.inl 2)-1/2-2*totalConsumers x) i) ≤
      -(1/25:ℝ)*variance q (normalizedDeviation q x) := by
    have hmul := mul_nonneg hn (sub_nonneg.mpr hg)
    nlinarith
  have hcross : -variance q (normalizedDeviation q x)*
      quadraticRate P consumerAxis (aggregate x-state s) ≤ variance q (normalizedDeviation q x) := by
    have h := mul_nonneg hn (show 0 ≤ quadraticRate P consumerAxis (aggregate x-state s)+1 by
      linarith [(abs_le.mp hgrad).1])
    linarith
  have hdev : normalizedDeviation q (communityField q x) =
      deviationField q (normalizedDeviation q x)
        (x (.inl 4)*x (.inl 2)-1/2-2*totalConsumers x) := by
    funext i
    exact deviation_source q x hq hpos i
  rw [communityEnergy_fderiv]
  unfold communityEnergyRate
  rw [aggregate_source q x hq hpos,quadraticRate_sub_smul,hdev]
  unfold communityEnergy
  nlinarith

theorem total_lift {n : ℕ} (q : Fin n → ℝ) (hq : ∑ i, q i = 1) (s : ℝ) :
    totalConsumers (lift q s) = s := by
  change (∑ i, q i*s) = s
  rw [← Finset.sum_mul,hq,one_mul]

theorem deviation_lift {n : ℕ} (q : Fin n → ℝ) (hq : ∑ i, q i = 1)
    (hpos : ∀ i, 0 < q i) (s : ℝ) : normalizedDeviation q (lift q s) = 0 := by
  funext i
  unfold normalizedDeviation
  rw [total_lift q hq s]
  change q i*s/q i-s = 0
  have hqi := ne_of_gt (hpos i)
  field_simp
  ring

theorem communityEnergy_center {n : ℕ} (P : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Fin n → ℝ) (hq : ∑ i, q i = 1) (hpos : ∀ i, 0 < q i) (s : ℝ) :
    communityEnergy P q s (lift q s) = 0 := by
  simp [communityEnergy,aggregate_lift q hq s,deviation_lift q hq hpos s,quadratic,variance]

end
end RAF1519.Reservoir
