import proofs.RAF1519.Reservoir.Composition
import proofs.RAF1519.Reservoir.Variance

namespace RAF1519.Reservoir
noncomputable section
open scoped BigOperators

def totalConsumers {n : ℕ} (x : Community n) : ℝ := ∑ i, x (.inr i)
def normalizedDeviation {n : ℕ} (q : Fin n → ℝ) (x : Community n) (i : Fin n) : ℝ :=
  x (.inr i)/q i-totalConsumers x

theorem deviation_mean_zero {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hq : ∑ i, q i = 1) (hpos : ∀ i, 0 < q i) :
    (∑ i, q i*normalizedDeviation q x i) = 0 := by
  have hi (i : Fin n) : q i*(x (.inr i)/q i) = x (.inr i) := by
    have hqi := ne_of_gt (hpos i)
    field_simp
  simp only [normalizedDeviation,mul_sub,Finset.sum_sub_distrib,hi,
    ← Finset.sum_mul,hq,one_mul,totalConsumers,sub_self]

theorem consumer_reconstruction {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hpos : ∀ i, 0 < q i) (i : Fin n) :
    q i*(totalConsumers x+normalizedDeviation q x i) = x (.inr i) := by
  have hqi := ne_of_gt (hpos i)
  unfold normalizedDeviation
  field_simp
  ring

theorem total_source {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hq : ∑ i, q i = 1) (hpos : ∀ i, 0 < q i) :
    totalConsumers (communityField q x) =
      totalConsumers x*(x (.inl 4)*x (.inl 2)-1/2-totalConsumers x)-
        variance q (normalizedDeviation q x) := by
  have hi (i : Fin n) : communityField q x (.inr i) =
      q i*(totalConsumers x+normalizedDeviation q x i)*
        (x (.inl 4)*x (.inl 2)-1/2-totalConsumers x-normalizedDeviation q x i) := by
    rw [consumer_reconstruction q x hpos i]
    change x (.inr i)*(x (.inl 4)*x (.inl 2)-1/2-x (.inr i)/q i) = _
    unfold normalizedDeviation
    ring
  unfold totalConsumers at ⊢
  simp_rw [hi]
  exact total_consumer_drift q (normalizedDeviation q x)
    (x (.inl 4)*x (.inl 2)-1/2) (totalConsumers x) hq (deviation_mean_zero q x hq hpos)

theorem deviation_source {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hq : ∑ i, q i = 1) (hpos : ∀ i, 0 < q i) (i : Fin n) :
    normalizedDeviation q (communityField q x) i =
      deviationField q (normalizedDeviation q x)
        (x (.inl 4)*x (.inl 2)-1/2-2*totalConsumers x) i := by
  have hi : communityField q x (.inr i)/q i =
      (totalConsumers x+normalizedDeviation q x i)*
        (x (.inl 4)*x (.inl 2)-1/2-totalConsumers x-normalizedDeviation q x i) := by
    change (x (.inr i)*(x (.inl 4)*x (.inl 2)-1/2-x (.inr i)/q i))/q i = _
    unfold normalizedDeviation
    ring
  change communityField q x (.inr i)/q i-totalConsumers (communityField q x) = _
  rw [hi,total_source q x hq hpos]
  exact deviation_identity q (normalizedDeviation q x)
    (x (.inl 4)*x (.inl 2)-1/2) (totalConsumers x) i

def consumerAxis (i : Fin 6) : ℝ := if i.val = 5 then 1 else 0

theorem aggregate_coordinate {n : ℕ} (x : Community n) (i : Fin 5) :
    aggregate x i.castSucc = x (.inl i) := by
  fin_cases i <;> rfl

theorem aggregate_total {n : ℕ} (x : Community n) : aggregate x 5 = totalConsumers x := rfl

theorem aggregate_source {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hq : ∑ i, q i = 1) (hpos : ∀ i, 0 < q i) :
    aggregate (communityField q x) = field (aggregate x)-
      variance q (normalizedDeviation q x) • consumerAxis := by
  have hfirst (i : Fin 5) : aggregate (communityField q x) i.castSucc =
      (field (aggregate x)-variance q (normalizedDeviation q x) • consumerAxis) i.castSucc := by
    rw [aggregate_coordinate]
    change field (aggregate x) i.castSucc = field (aggregate x) i.castSucc-
      variance q (normalizedDeviation q x)*consumerAxis i.castSucc
    have hi : i.val ≠ 5 := by omega
    simp [consumerAxis,hi]
  funext i
  fin_cases i
  · exact hfirst 0
  · exact hfirst 1
  · exact hfirst 2
  · exact hfirst 3
  · exact hfirst 4
  · change totalConsumers (communityField q x) =
      totalConsumers x*(x (.inl 4)*x (.inl 2)-1/2-totalConsumers x)-
        variance q (normalizedDeviation q x)*1
    simpa only [mul_one] using total_source q x hq hpos

theorem totalConsumers_deriv {n : ℕ} (X : ℝ → Community n) (v : Community n) (t : ℝ)
    (hX : HasDerivAt X v t) :
    HasDerivAt (fun t => totalConsumers (X t)) (totalConsumers v) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hasDerivAt_pi.1 hX (.inr i))

theorem aggregate_deriv {n : ℕ} (X : ℝ → Community n) (v : Community n) (t : ℝ)
    (hX : HasDerivAt X v t) : HasDerivAt (fun t => aggregate (X t)) (aggregate v) t := by
  apply hasDerivAt_pi.2
  intro i
  fin_cases i
  · exact hasDerivAt_pi.1 hX (.inl 0)
  · exact hasDerivAt_pi.1 hX (.inl 1)
  · exact hasDerivAt_pi.1 hX (.inl 2)
  · exact hasDerivAt_pi.1 hX (.inl 3)
  · exact hasDerivAt_pi.1 hX (.inl 4)
  · exact totalConsumers_deriv X v t hX

theorem normalizedDeviation_deriv {n : ℕ} (q : Fin n → ℝ)
    (X : ℝ → Community n) (v : Community n) (t : ℝ) (hX : HasDerivAt X v t) :
    HasDerivAt (fun t => normalizedDeviation q (X t)) (normalizedDeviation q v) t := by
  apply hasDerivAt_pi.2
  intro i
  exact ((hasDerivAt_pi.1 hX (.inr i)).div_const (q i)).sub (totalConsumers_deriv X v t hX)

theorem variance_deriv {n : ℕ} (q : Fin n → ℝ) (Y : ℝ → Fin n → ℝ)
    (v : Fin n → ℝ) (t : ℝ) (hY : HasDerivAt Y v t) :
    HasDerivAt (fun t => variance q (Y t)) (∑ i, 2*q i*Y t i*v i) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((hasDerivAt_pi.1 hY i).pow 2).const_mul (q i))
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  norm_num
  ring

theorem aggregate_contDiff {n : ℕ} : ContDiff ℝ 1 (@aggregate n) := by
  apply contDiff_pi.2
  intro i
  fin_cases i
  · change ContDiff ℝ 1 (fun x : Community n => x (.inl 0)); fun_prop
  · change ContDiff ℝ 1 (fun x : Community n => x (.inl 1)); fun_prop
  · change ContDiff ℝ 1 (fun x : Community n => x (.inl 2)); fun_prop
  · change ContDiff ℝ 1 (fun x : Community n => x (.inl 3)); fun_prop
  · change ContDiff ℝ 1 (fun x : Community n => x (.inl 4)); fun_prop
  · change ContDiff ℝ 1 (fun x : Community n => ∑ i, x (.inr i)); fun_prop

theorem deviation_contDiff {n : ℕ} (q : Fin n → ℝ) : ContDiff ℝ 1 (normalizedDeviation q) := by
  apply contDiff_pi.2
  intro i
  unfold normalizedDeviation totalConsumers
  fun_prop

end
end RAF1519.Reservoir
