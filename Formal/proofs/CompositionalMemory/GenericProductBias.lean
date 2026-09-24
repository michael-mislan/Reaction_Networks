import Mathlib

namespace CompositionalMemory

theorem ordered_product_gap {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (U eps : ℝ) (hU : 0 ≤ U) (heps : 0 ≤ eps)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (hg : ∀ i ∈ s, g i ≤ U) (hgap : ∀ i ∈ s, g i-f i ≤ eps) :
    (∏ i ∈ s, g i)-(∏ i ∈ s, f i) ≤ (s.card:ℝ)*eps*(U+1)^s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self a s)
    have hga := hg a (Finset.mem_insert_self a s)
    have hfg_a := hfg a (Finset.mem_insert_self a s)
    have hgap_a := hgap a (Finset.mem_insert_self a s)
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfg' := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hgap' := fun i hi => hgap i (Finset.mem_insert_of_mem hi)
    have hprod0 : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg fun i hi => (hf' i hi).trans (hfg' i hi)
    have hprod : (∏ i ∈ s, g i) ≤ (U+1)^s.card := by
      calc
        _ ≤ ∏ _i ∈ s, (U+1) := Finset.prod_le_prod
          (fun i hi => (hf' i hi).trans (hfg' i hi)) (fun i hi => by linarith [hg' i hi])
        _ = _ := by simp
    have hd := ih hf' hfg' hg' hgap'
    rw [Finset.prod_insert ha,Finset.prod_insert ha]
    calc
      _ = f a*((∏ i ∈ s, g i)-(∏ i ∈ s, f i))+(g a-f a)*(∏ i ∈ s, g i) := by ring
      _ ≤ f a*((s.card:ℝ)*eps*(U+1)^s.card)+eps*(U+1)^s.card := add_le_add
        (mul_le_mul_of_nonneg_left hd hfa) (mul_le_mul hgap_a hprod hprod0 heps)
      _ ≤ U*((s.card:ℝ)*eps*(U+1)^s.card)+eps*(U+1)^s.card :=
        add_le_add (mul_le_mul_of_nonneg_right (hfg_a.trans hga) (by positivity)) le_rfl
      _ = (U*(s.card:ℝ)+1)*eps*(U+1)^s.card := by ring
      _ ≤ (((s.card:ℝ)+1)*(U+1))*eps*(U+1)^s.card := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ heps
        have hc : (0:ℝ) ≤ s.card := Nat.cast_nonneg _
        nlinarith only [hc,hU]
      _ = _ := by rw [Finset.card_insert_of_notMem ha,pow_succ]; push_cast; ring

end CompositionalMemory
