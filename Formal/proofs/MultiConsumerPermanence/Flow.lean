import proofs.MultiConsumerPermanence.Source
import proofs.RobustPermanence.ConsumerFlowBounds

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence
open scoped BigOperators

abbrev Vector (n : ℕ) := (Fin 4 ⊕ Fin n) → ℝ

noncomputable def donorVector {n : ℕ} (y : Vector n) : ConsumerVector :=
  ![y (.inl 0),y (.inl 1),y (.inl 2),y (.inl 3),total (fun i => y (.inr i))]

noncomputable def field {n : ℕ} (e : ℝ) (y : Vector n) : Vector n :=
  Sum.elim (fun i => consumerField e (donorVector y) i.castSucc)
    (fun i => y (.inr i)*(y (.inl 2)-1/2-(n:ℝ)*y (.inr i)))

def positivePart {n : ℕ} (y : Vector n) : Vector n := fun i => max 0 (y i)

theorem positivePart_lipschitz (n : ℕ) : LipschitzWith 1 (@positivePart n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0 ≤ dist x y)).2
  intro i
  calc
    dist (positivePart x i) (positivePart y i) ≤ dist (x i) (y i) := by
      have hh := ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max 0).dist_le_mul (x i) (y i)
      simpa only [positivePart,id_eq,NNReal.coe_one,one_mul] using hh
    _ ≤ dist x y := dist_le_pi_dist x y i

theorem field_contDiff (n : ℕ) (e : ℝ) : ContDiff ℝ 1 (@field n e) := by
  apply contDiff_pi.2
  intro i
  cases i with
  | inl i =>
    fin_cases i <;> simp [field,consumerField,donorVector,total,fA,fB,fZ,fH,flagshipRates] <;> fun_prop
  | inr i =>
    simp only [field,Sum.elim_inr]
    fun_prop

theorem extension_solution (n : ℕ) (e R : ℝ) (hR : 0 < R) (x₀ : Vector n) :
    ∃ b : Vector n → ℝ, ∃ X : ℝ → Vector n,
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → b x = 1) ∧
      X 0 = x₀ ∧ ∀ t, HasDerivAt X
        (b (positivePart (X t)) • field e (positivePart (X t))) t := by
  let b : ContDiffBump (0 : Vector n) := ⟨R,2*R,hR,by linarith⟩
  let f : Vector n → Vector n := fun x => b x • field e x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (field_contDiff n e)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (positivePart x)) := by
    simpa only [mul_one] using hK.comp (positivePart_lipschitz n)
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (positivePart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) x₀
  refine ⟨b,X,(fun _ => ⟨b.nonneg,b.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem donorVector_nonneg {n : ℕ} (y : Vector n) (hy : ∀ i, 0 ≤ y i) :
    ∀ i, 0 ≤ donorVector y i := by
  intro i
  fin_cases i
  · exact hy (.inl 0)
  · exact hy (.inl 1)
  · exact hy (.inl 2)
  · exact hy (.inl 3)
  · exact total_nonneg _ (fun i => hy (.inr i))

theorem boundary_nonneg {n : ℕ} (e : ℝ) (he : 0 ≤ e) (y : Vector n)
    (hy : ∀ i, 0 ≤ y i) (i : Fin 4 ⊕ Fin n) (hi : y i = 0) : 0 ≤ field e y i := by
  cases i with
  | inl i =>
    apply consumer_boundary_nonneg e he (donorVector y) (donorVector_nonneg y hy) i.castSucc
    fin_cases i <;> exact hi
  | inr i => simp [field,hi]

theorem extension_nonnegative {n : ℕ} (e : ℝ) (he : 0 ≤ e) (b : Vector n → ℝ)
    (hb : ∀ x, 0 ≤ b x) (X : ℝ → Vector n) (h0 : ∀ i, 0 ≤ X 0 i)
    (hd : ∀ t, HasDerivAt X (b (positivePart (X t)) • field e (positivePart (X t))) t) :
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i := by
  intro t ht i
  apply scalar_lower_barrier (fun t => X t i)
    (fun t => b (positivePart (X t))*field e (positivePart (X t)) i) 0
    (fun t _ => (hasDerivAt_pi.1 (hd t)) i) (h0 i) ?_ t ht
  intro s _ hs
  apply mul_nonneg (hb _)
  apply boundary_nonneg e he _ (fun j => le_max_left 0 (X s j)) i
  exact max_eq_left hs

end MultiConsumerPermanence
