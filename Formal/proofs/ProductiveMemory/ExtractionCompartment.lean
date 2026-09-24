import proofs.ProductiveMemory.ExtractionGrowing
import proofs.ProductiveMemory.ExtractionCountSource

namespace ProductiveMemory
open FiniteCopy HeritableCompositions
noncomputable section
set_option Elab.async false

abbrev GrowingChannel := HeritableCompositions.Channel ⊕ Unit

def growingNext (c : Compartment) : GrowingChannel → Compartment :=
  Sum.elim (nextCompartment c) (fun _ => (channelNext c.1 (.inr ()),c.2))

def growingRate (rho γ : ℝ) (c : Compartment) : GrowingChannel → ℝ :=
  Sum.elim (propensity γ c) (fun _ => rho*(c.1 2:ℝ))

def growingCollection : GrowingChannel → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

theorem growing_rate_nonneg (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (c : Compartment) (r : GrowingChannel) : 0 ≤ growingRate rho γ c r := by
  cases r with
  | inl r => exact propensity_nonneg γ hg c r
  | inr r => dsimp [growingRate]; positivity

def growingCompartmentGenerator (rho γ : ℝ) (f : Compartment → ℝ) (c : Compartment) : ℝ :=
  ∑ r : GrowingChannel, growingRate rho γ c r*(f (growingNext c r)-f c)

theorem growing_generator_split (rho γ : ℝ) (f : Compartment → ℝ) (c : Compartment) :
    growingCompartmentGenerator rho γ f c = compartmentGenerator γ f c+
      rho*(c.1 2:ℝ)*(f (channelNext c.1 (.inr ()),c.2)-f c) := by
  simp only [growingCompartmentGenerator,Fintype.sum_sum_type,growingRate,growingNext,
    Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,compartmentGenerator]

theorem count_generator_split (rho : ℝ) (m : ℕ) (f : Point → ℝ) (x : Point) :
    countGenerator rho m f x = generator (1/100000) m f x+
      (m:ℝ)*(rho*x 2)*(f (fun i => x i+channelJump (.inr ()) i/(m:ℝ))-f x) := by
  simp only [countGenerator,Fintype.sum_sum_type,channelDensity,channelJump,
    Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,generator]
  ring

theorem growing_compartment_binding (rho γ : ℝ) (m : ℕ) (hm : 0 < m)
    (n : Counts) (f : Point → ℝ) :
    growingCompartmentGenerator rho γ (fun c => f (concentration c.2 c.1)) (n,m) =
      extractGrowthGenerator rho γ m f (concentration m n) := by
  rw [growing_generator_split,compartment_generator_binding γ m hm n]
  have hext : rho*(n 2:ℝ)*(f (concentration m (channelNext n (.inr ())))-f (concentration m n)) =
      (m:ℝ)*(rho*concentration m n 2)*
        (f (fun i => concentration m n i+channelJump (.inr ()) i/(m:ℝ))-f (concentration m n)) := by
    by_cases hn : 1 ≤ n 2
    · rw [channel_concentration_next m n (.inr ()) hn]
      have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
      unfold concentration
      field_simp
    · have hn0 : n 2 = 0 := by omega
      simp [hn0,concentration]
  change growthGenerator γ m f (concentration m n)+_ = _
  rw [hext]
  unfold extractGrowthGenerator growthGenerator
  rw [count_generator_split]
  ring

theorem extraction_preserves_size (c : Compartment) : (growingNext c (.inr ())).2 = c.2 := rfl

theorem extraction_mark_balance (c : Compartment) (hc : 1 ≤ c.1 2) :
    (growingNext c (.inr ())).1 2+growingCollection (.inr ()) = c.1 2 := by
  simp [growingNext,channelNext,growingCollection,Matrix.cons_val_two]
  omega

end
end ProductiveMemory
