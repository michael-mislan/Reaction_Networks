import proofs.FiniteReservoir.SharpEnvelope
import proofs.FiniteReservoir.InverseDesign

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

variable {H : Type*} [MeasurableSpace H]

def physicalHistorySharpSuccess {V M : ℕ} {params : Parameters M} {hV}
    (R : PhysicalHistory H V M params hV) : Set H :=
  {h | SharpCountCycleSuccess V M (R.observe h)}

theorem physical_history_sharp_measurable {V M : ℕ} {params : Parameters M} {hV}
    (R : PhysicalHistory H V M params hV) : MeasurableSet (physicalHistorySharpSuccess R) :=
  R.observe_measurable ((Set.to_countable {X : JointCounts M | SharpCountCycleSuccess V M X}).measurableSet)

theorem physical_history_sharp_one_cycle {V R : ℕ} {params : Parameters R} {hV}
    (S : PhysicalHistory H V R params hV) (hlarge : 1000000 ≤ V) (hR : 0 < (R:ℝ))
    (hcapacity : params.capacity=R) (hd : params.cleavage=1/50)
    (h : H) (hh : Restart V (S.current h).1) :
    ENNReal.ofReal (1-sharpBothError V) ≤ S.step h (physicalHistorySharpSuccess S) := by
  have hp := literal_both_cycle_bound (S.current h).1 V R (S.policy h) hh hlarge params
    (S.current h).2 hV hR hcapacity hd
  rw [← S.conditional_law h,Measure.map_apply S.observe_measurable
    (Set.to_countable {X : JointCounts R | SharpCountCycleSuccess V R X}).measurableSet] at hp
  exact hp

theorem physical_history_sharp_linear {V R : ℕ} {params : Parameters R} {hV}
    (S : PhysicalHistory H V R params hV) (hscale : 50000000000 ≤ V) (hR : 0 < (R:ℝ))
    (hcapacity : params.capacity=R) (hd : params.cleavage=1/50) (n : ℕ) (h : H)
    (hh : Restart V (S.current h).1) :
    ENNReal.ofReal (1-(n:ℝ)*sharpBothError V) ≤
      successfulHistoryKernel S.step (physicalHistorySharpSuccess S)
        (physical_history_sharp_measurable S) n h Set.univ := by
  apply history_survival_linear S.step {y | Restart V (S.current y).1} (physicalHistorySharpSuccess S)
    (physical_history_sharp_measurable S) _ (sharpBothError V) _
    (fun y hy => physical_history_sharp_one_cycle S (by omega) hR hcapacity hd y hy) n h hh
  · intro y hy
    change Restart V (S.current y).1
    rw [S.current_return y]
    exact hy.1.1
  · have hs := sharp_error_small V (by exact_mod_cast hscale)
    linarith

def returnedGoodSharp (V M : ℕ) (h : ReturnedHistory M) : Prop :=
  ∀ X ∈ h,SharpCountCycleSuccess V M X

def returnedFinalSharp (V M L : ℕ) : Set (ReturnedHistory M) :=
  {h | h.length=L ∧ returnedGoodSharp V M h}

theorem returnedFinalSharp_subset (V M L : ℕ) : returnedFinalSharp V M L ⊆ returnedFinal V M L :=
  fun _ hh => ⟨hh.1,fun X hx => (hh.2 X hx).1⟩

theorem returned_sharp_support (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) (policy : ReturnedHistory M → Intervention)
    (n : ℕ) (h : ReturnedHistory M) (hh : returnedGoodSharp V M h) :
    successfulHistoryKernel (returnedHistoryStep M N V params hV policy)
      (physicalHistorySharpSuccess (returnedPhysicalHistory M N V params hV policy))
      (physical_history_sharp_measurable _) n h (returnedFinalSharp V M (h.length+n))ᶜ=0 := by
  let K := returnedHistoryStep M N V params hV policy
  let R := returnedPhysicalHistory M N V params hV policy
  let S := physicalHistorySharpSuccess R
  have hS := physical_history_sharp_measurable R
  change successfulHistoryKernel K S hS n h (returnedFinalSharp V M (h.length+n))ᶜ=0
  induction n generalizing h with
  | zero =>
    have hm : h ∈ returnedFinalSharp V M (h.length+0) := ⟨by omega,hh⟩
    simp only [successfulHistoryKernel,Kernel.id_apply,Measure.dirac_apply'
      (h) (Set.to_countable ((returnedFinalSharp V M (h.length+0))ᶜ)).measurableSet]
    exact Set.indicator_of_notMem (not_not.mpr hm) _
  | succ n ih =>
    let A := (returnedFinalSharp V M (h.length+(n+1)))ᶜ
    have hA : MeasurableSet A := (Set.to_countable A).measurableSet
    rw [successfulHistoryKernel,Kernel.comp_apply' _ _ _ hA,Kernel.restrict_apply,
      ← lintegral_indicator hS]
    change (∫⁻ y,S.indicator (fun z => successfulHistoryKernel K S hS n z A) y
      ∂(literalPulseCycleMeasure (returnedObservation N h).1.1 V M (policy h) params
        (returnedObservation N h).1.2 hV).map (fun X => X::h))=0
    rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
    apply (lintegral_eq_zero_iff (measurable_of_countable _)).mpr
    apply Filter.Eventually.of_forall
    intro X
    change S.indicator (fun z => successfulHistoryKernel K S hS n z A) (X::h)=0
    by_cases hx : SharpCountCycleSuccess V M X
    · have hs : X::h ∈ S := hx
      rw [Set.indicator_of_mem hs]
      have hg : returnedGoodSharp V M (X::h) := by
        intro Y hy
        rcases List.mem_cons.mp hy with hY | hY
        · simpa only [hY] using hx
        · exact hh Y hY
      have hi := ih (X::h) hg
      have he : (X::h).length+n=h.length+(n+1) := by simp only [List.length_cons]; omega
      rw [he] at hi
      exact hi
    · have hs : X::h ∉ S := hx
      exact Set.indicator_of_notMem hs _

theorem full_returned_sharp_success (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) (policy : ReturnedHistory M → Intervention)
    (hscale : 50000000000 ≤ V) (hM : 0 < (M:ℝ)) (hcapacity : params.capacity=M)
    (hd : params.cleavage=1/50) (hN : Restart V N.1) (n : ℕ) :
    ENNReal.ofReal (1-(n:ℝ)*sharpBothError V) ≤
      fullHistoryKernel (returnedHistoryStep M N V params hV policy) n [] (returnedFinalSharp V M n) := by
  have hs := physical_history_sharp_linear (returnedPhysicalHistory M N V params hV policy)
    hscale hM hcapacity hd n [] hN
  apply hs.trans
  apply successful_history_event_lower _ _ _ n [] (returnedFinalSharp V M n)
    (Set.to_countable _).measurableSet
  simpa only [List.length_nil,Nat.zero_add] using
    returned_sharp_support M N V params hV policy n [] (by simp [returnedGoodSharp])

theorem returned_sharp_gross (V M n : ℕ) (h : ReturnedHistory M)
    (hh : h ∈ returnedFinalSharp V M n) :
    returnedTotal h 4 ≤ (n:ℝ)*(Nat.floor ((V:ℝ)/10):ℝ) := by
  obtain ⟨hlen,hgood⟩ := hh
  simpa only [hlen] using returned_total_upper h 4 _ (fun X hx => (hgood X hx).2)

/-- Halved per-cycle service allowance and the resulting reservoir size. -/
def grossAllowanceSharp (V n : ℕ) : ℝ := (n:ℝ)*(Nat.floor ((V:ℝ)/10):ℝ)
def reservoirSizeSharp (V n : ℕ) (rho : ℝ) : ℕ := max 1 ⌈grossAllowanceSharp V n/rho⌉₊

theorem reservoirSizeSharp_positive (V n : ℕ) (rho : ℝ) : 0 < reservoirSizeSharp V n rho := by
  unfold reservoirSizeSharp
  have := le_max_left 1 (⌈grossAllowanceSharp V n/rho⌉₊)
  omega

theorem reservoirSizeSharp_budget (V n : ℕ) (rho : ℝ) (hr : 0 < rho) :
    grossAllowanceSharp V n ≤ rho*(reservoirSizeSharp V n rho:ℝ) := by
  have hc : grossAllowanceSharp V n/rho ≤ (reservoirSizeSharp V n rho:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (⌈grossAllowanceSharp V n/rho⌉₊)))
  have := (div_le_iff₀ hr).mp hc
  linarith

theorem pure_prefix_tolerance_sharp {R N V policy h} (tr : HistoryTrace R N V policy h)
    (hR : 0 < R) (hinit : N.2=pureFuel R) (n : ℕ) (hh : h ∈ returnedFinalSharp V R n)
    (rho : ℝ) (hs : grossAllowanceSharp V n ≤ rho*(R:ℝ))
    (b : FuelState R) (hb : b ∈ tr.visitedBath) :
    1-rho ≤ (b.val:ℝ)/R ∧ (b.val:ℝ)/R ≤ 1 ∧ ((bathOf b).waste:ℝ)/R ≤ rho := by
  have hf := (tr.prefix_fuel_abs b hb).trans (returned_sharp_gross V R n h hh)
  rw [hinit] at hf
  change |(b.val:ℝ)-(R:ℝ)| ≤ grossAllowanceSharp V n at hf
  have hr : (0:ℝ) < R := by exact_mod_cast hR
  have hle : (b.val:ℝ) ≤ R := by exact_mod_cast (Nat.le_of_lt_succ b.isLt)
  obtain ⟨hl,_⟩ := abs_le.mp hf
  have hw : ((bathOf b).waste:ℝ)=(R:ℝ)-(b.val:ℝ) := by
    simp only [bathOf,Nat.cast_sub (Nat.le_of_lt_succ b.isLt)]
  refine ⟨(le_div_iff₀ hr).mpr (by nlinarith),(div_le_iff₀ hr).mpr (by linarith),?_⟩
  rw [div_le_iff₀ hr,hw]
  nlinarith

def certifiedSharpHistory (R : ℕ) (N : CountState R) (V n : ℕ)
    (policy : ReturnedHistory R → Intervention) : Set (ReturnedHistory R) :=
  {h | h ∈ returnedFinalSharp V R n ∧ Nonempty (HistoryTrace R N V policy h)}

/-- The sharper mission event: the original operational targets, the halved
per-cycle service allowance, and every-prefix fuel tolerance in the smaller bath. -/
def SharpDesignedSuccess (R : ℕ) (N : CountState R) (V m : ℕ)
    (policy : ReturnedHistory R → Intervention) (rho : ℝ) : Set (ReturnedHistory R) :=
  {h | h ∈ OperationalSuccess R N V m policy ∧
    returnedTotal h 4 ≤ grossAllowanceSharp V m ∧
    ∀ tr : HistoryTrace R N V policy h,∀ b ∈ tr.visitedBath,
      1-rho ≤ (b.val:ℝ)/R ∧ (b.val:ℝ)/R ≤ 1 ∧ ((bathOf b).waste:ℝ)/R ≤ rho}

theorem sharp_mission_bound (R : ℕ) (N : CountState R) (V : ℕ) (params : Parameters R)
    (hV : 0 < (V:ℝ)) (policy : ReturnedHistory R → Intervention)
    (hscale : 50000000000 ≤ V) (hR : 0 < R) (hcapacity : params.capacity=R)
    (hd : params.cleavage=1/50) (hinit : N.2=pureFuel R) (hN : Restart V N.1)
    (m : ℕ) (rho : ℝ) (hrho : grossAllowanceSharp V m ≤ rho*(R:ℝ)) (δ : ℝ)
    (hb : (m:ℝ)*sharpBothError V ≤ δ) :
    ENNReal.ofReal (1-δ) ≤
      fullHistoryKernel (returnedHistoryStep R N V params hV policy) m []
        (SharpDesignedSuccess R N V m policy rho) := by
  have hRr : (0:ℝ) < R := by exact_mod_cast hR
  have hfull := full_returned_sharp_success R N V params hV policy hscale hRr hcapacity hd hN m
  have hlow := (ENNReal.ofReal_le_ofReal (by linarith : 1-δ ≤ 1-(m:ℝ)*sharpBothError V)).trans hfull
  have ht := full_history_has_trace R N V params hV policy m [] ⟨HistoryTrace.nil⟩
  have hae : certifiedSharpHistory R N V m policy =ᵐ[
      fullHistoryKernel (returnedHistoryStep R N V params hV policy) m []]
      returnedFinalSharp V R m := by
    filter_upwards [ht] with h hh
    change (h ∈ returnedFinalSharp V R m ∧ Nonempty (HistoryTrace R N V policy h))=
      (h ∈ returnedFinalSharp V R m)
    simp only [hh,and_true]
  rw [← measure_congr hae] at hlow
  apply hlow.trans
  apply measure_mono
  rintro h ⟨hh,htr⟩
  have hplain : h ∈ returnedFinal V R m := returnedFinalSharp_subset V R m hh
  have hop : h ∈ OperationalSuccess R N V m policy :=
    certified_history_operational R N V m policy hN ⟨hplain,htr⟩
  exact ⟨hop,returned_sharp_gross V R m h hh,
    fun tr b hb => pure_prefix_tolerance_sharp tr hR hinit m hh rho hrho b hb⟩

/-- Improved certified instance: the original hundred-cycle confidence and
every-prefix tolerance, at 48% of the copy scale and 24% of the fuel inventory. -/
theorem sharp_example_mission
    (policy : ReturnedHistory 9600000000000 → Intervention) :
    let V : ℕ := 96000000000
    let R : ℕ := 9600000000000
    let N : CountState R := (![0,0,V,0,0,0],pureFuel R)
    let params := pureParameters R (by norm_num) 20 (1/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ENNReal.ofReal (999979/1000000:ℝ) ≤
      fullHistoryKernel (returnedHistoryStep R N V params (by norm_num) policy) 100 []
        (SharpDesignedSuccess R N V 100 policy (1/10)) := by
  dsimp only
  have hN : Restart 96000000000 ![0,0,96000000000,0,0,0] := all_free_restart _
  have hfl : ⌊((96000000000:ℕ):ℝ)/10⌋₊ = 9600000000 := by
    rw [show ((96000000000:ℕ):ℝ)/10 = ((9600000000:ℕ):ℝ) by push_cast; norm_num]
    exact Nat.floor_natCast _
  have hg : grossAllowanceSharp 96000000000 100 ≤ (1/10)*(9600000000000:ℝ) := by
    unfold grossAllowanceSharp
    rw [hfl]
    norm_num
  convert sharp_mission_bound 9600000000000 (![0,0,96000000000,0,0,0],pureFuel 9600000000000)
    96000000000
    (pureParameters 9600000000000 (by norm_num) 20 (1/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) policy (by norm_num) (by norm_num) rfl rfl rfl hN 100 (1/10) hg
    (21/1000000) sharp_hundred_budget using 1
  norm_num

end
end FiniteReservoir
