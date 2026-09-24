import proofs.ResourceLimitedCompetition.PopulationPotential
namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

noncomputable def countWeight (n : Counts) : ℝ := ∑ i, weight (1/100000) i*(n i : ℝ)
noncomputable def sizeWeight (c : Compartment) : ℝ := countWeight c.1+(c.2 : ℝ)

theorem countWeight_nonneg (n : Counts) : 0 ≤ countWeight n := by
  unfold countWeight weight
  norm_num [Fin.sum_univ_succ]
  positivity

theorem resident_weight_increment (n : Counts) (r : Fin 13) (hr : reactants n r) :
    countWeight (nextCounts n r)-countWeight n = ∑ i, weight (1/100000) i*jump r i := by
  unfold countWeight
  simp_rw [nextCounts_cast n r hr,mul_add]
  rw [Finset.sum_add_distrib]
  ring

theorem growth_sizeWeight (c : Compartment) (hz : 1 ≤ c.1 2) :
    sizeWeight (nextCompartment c (.inr ()))=sizeWeight c := by
  unfold sizeWeight countWeight
  simp only [membrane_count_update c hz]
  simp [nextCompartment,weight,membraneDirection,Fin.sum_univ_succ]
  ring

theorem complementary_sizeWeight (n d : Counts) (N : ℕ) (hd : ∀ i, d i ≤ n i) :
    sizeWeight (d,N)+sizeWeight ((fun i => n i-d i),N)=sizeWeight (n,2*N) := by
  unfold sizeWeight countWeight
  simp only [Nat.cast_sub (hd _),Nat.cast_mul,Nat.cast_ofNat,mul_sub,Finset.sum_sub_distrib]
  ring

theorem sizeWeight_generator_binding (β : ℝ) (c : Compartment) :
    compartmentGenerator β sizeWeight c =
      (c.2 : ℝ)*massDrift (1/100000) (1/(c.2 : ℝ)) (concentration c.2 c.1) := by
  classical
  have hg : propensity β c (.inr ())*(sizeWeight (nextCompartment c (.inr ()))-sizeWeight c)=0 := by
    by_cases hz : 1 ≤ c.1 2
    · rw [growth_sizeWeight c hz,sub_self,mul_zero]
    · have hz0 : c.1 2=0 := by omega
      simp [propensity,hz0]
  have hr (r : Fin 13) : propensity β c (.inl r)*(sizeWeight (nextCompartment c (.inl r))-sizeWeight c)=
      (c.2 : ℝ)*densityRates (1/100000) (1/(c.2 : ℝ)) (concentration c.2 c.1) r*
        (∑ i, weight (1/100000) i*jump r i) := by
    by_cases he : reactants c.1 r
    · have h := resident_weight_increment c.1 r he
      simp only [propensity,nextCompartment,sizeWeight]
      rw [show countWeight (nextCounts c.1 r)+(c.2 : ℝ)-(countWeight c.1+(c.2 : ℝ))=
        countWeight (nextCounts c.1 r)-countWeight c.1 by ring,h]
    · have hz := disabled_density_zero (1/100000) c.2 c.1 r he
      simp only [propensity,hz,mul_zero,zero_mul]
  unfold compartmentGenerator
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique,hg,add_zero,hr]
  unfold massDrift drift
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sizeWeight_generator_bound (β : ℝ) (c : Compartment) (hm : 1 ≤ c.2) :
    compartmentGenerator β sizeWeight c ≤ (61+60/100000)*sizeWeight c := by
  rw [sizeWeight_generator_binding]
  have hf := lattice_foster (1/100000) (by norm_num) (by norm_num) c.2 hm c.1
  have hmR : (0 : ℝ) ≤ c.2 := Nat.cast_nonneg _
  have hmass : 0 ≤ mass (1/100000) (concentration c.2 c.1) := by
    unfold mass weight concentration
    norm_num [Fin.sum_univ_succ]
    positivity
  have hh := mul_le_mul_of_nonneg_left hf hmR
  have hw := countWeight_nonneg c.1
  unfold sizeWeight
  nlinarith only [hh,mul_nonneg hmR hmass,hw]

/-- The literal joint raw generator sums the resident drift; the resource-dependent
growth coefficient disappears from this bound. Complementary splitting preserves it. -/
theorem joint_weight_drift (γ : ℝ) (Ω : ℕ) (D : Finset PopulationState) (s : ActiveState D)
    (hm : ∀ c ∈ s.val.live, 1 ≤ c.compartment.2) :
    (∑ e : CellEvent s.val, eventRate γ Ω ⟨s,e⟩*
      (rawEventPotential (fun c => sizeWeight c.compartment) s.val e-
        potentialSum (fun c => sizeWeight c.compartment) s.val)) ≤
      ∑ i : Fin s.val.live.length, (61+60/100000)*sizeWeight (selectedCell s.val i).compartment := by
  rw [raw_event_generator_sum]
  apply Finset.sum_le_sum
  intro i _
  exact sizeWeight_generator_bound _ _ (hm _ (selected_mem s.val i))

end ResourceLimitedCompetition
