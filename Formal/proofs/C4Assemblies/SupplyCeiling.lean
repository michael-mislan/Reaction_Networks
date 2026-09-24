import proofs.C4Assemblies.Inventory

namespace C4Assemblies
noncomputable section
open ProductiveRecovery MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem scalar_supply_ceiling (a q : ℝ → ℝ) (N T : ℝ) (hT : 0 ≤ T)
    (ha : ∀ t, 0 ≤ t → HasDerivAt a (N-a t) t)
    (hq : ContinuousOn q (Icc 0 T)) (hfinal : 0 ≤ a T)
    (hqa : ∀ t ∈ Icc 0 T, q t ≤ a t) :
    (∫ t in (0:ℝ)..T, q t) ≤ a 0+N*T := by
  have hac : ContinuousOn a (Icc 0 T) := fun t ht => (ha t ht.1).continuousAt.continuousWithinAt
  have hai : IntervalIntegrable a volume 0 T := hac.intervalIntegrable_of_Icc hT
  have hqi : IntervalIntegrable q volume 0 T := hq.intervalIntegrable_of_Icc hT
  have hdi : IntervalIntegrable (fun t => N-a t) volume 0 T :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => N) volume 0 T).sub hai
  have hder : ∀ t ∈ uIcc (0:ℝ) T, HasDerivAt a (N-a t) t := by
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) T := by simpa [uIcc_of_le hT] using ht
    exact ha t ht'.1
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hdi
  rw [intervalIntegral.integral_sub intervalIntegrable_const hai] at hh
  have hm := intervalIntegral.integral_mono_on hT hqi hai hqa
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hh
  nlinarith

theorem inventory_le_material (c : State) (hc : Nonneg c) : inventory c ≤ A c ∧ inventory c ≤ B c := by
  dsimp [inventory,A,B]
  constructor <;> linarith [hc 0,hc 1,hc 3,hc 4]

theorem assembly_food_ceiling (k : ι → ι → ℝ) (hs : ∀ i j, k i j = k j i)
    (r d : ι → ℝ) (X : ℝ → Assembly ι) (T : ℝ) (hT : 0 ≤ T)
    (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField k r d (X t)) t) :
    (∫ t in (0:ℝ)..T, totalInventory (X t)) ≤ totalA (X 0)+(Fintype.card ι : ℝ)*T ∧
    (∫ t in (0:ℝ)..T, totalInventory (X t)) ≤ totalB (X 0)+(Fintype.card ι : ℝ)*T := by
  have hq : ContinuousOn (fun t => totalInventory (X t)) (Icc 0 T) :=
    (show Continuous (@totalInventory ι _) by unfold totalInventory inventory; fun_prop).comp_continuousOn
      (fun t ht => (hX t ht.1).continuousAt.continuousWithinAt)
  have hma : ∀ t, 0 ≤ t → ∀ i, 0 ≤ A (X t i) := by
    intro t ht i
    have hi := inventory_nonnegative (X t i) (hn t ht i)
    exact hi.trans (inventory_le_material _ (hn t ht i)).1
  have hmb : ∀ t, 0 ≤ t → ∀ i, 0 ≤ B (X t i) := by
    intro t ht i
    have hi := inventory_nonnegative (X t i) (hn t ht i)
    exact hi.trans (inventory_le_material _ (hn t ht i)).2
  constructor
  · apply scalar_supply_ceiling (fun t => totalA (X t)) _ _ T hT
      (fun t ht => by simpa only [totalA_field k hs] using deriv_totalA X _ t (hX t ht)) hq
      (Finset.sum_nonneg fun i _ => hma T hT i)
    intro t ht
    exact Finset.sum_le_sum fun i _ => (inventory_le_material _ (hn t ht.1 i)).1
  · apply scalar_supply_ceiling (fun t => totalB (X t)) _ _ T hT
      (fun t ht => by simpa only [totalB_field k hs] using deriv_totalB X _ t (hX t ht)) hq
      (Finset.sum_nonneg fun i _ => hmb T hT i)
    intro t ht
    exact Finset.sum_le_sum fun i _ => (inventory_le_material _ (hn t ht.1 i)).2

end
end C4Assemblies
