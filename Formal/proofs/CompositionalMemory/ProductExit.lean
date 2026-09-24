import proofs.CompositionalMemory.RetainedModular

namespace CompositionalMemory
open FiniteCopy

theorem modular_generator_sum {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (F : Fin k → ModularCountState k → ℝ) (s : ModularCountState k) :
    modularGenerator γ w (fun t => ∑ i, F i t) s =
      ∑ i, modularGenerator γ w (F i) s := by
  unfold modularGenerator
  simp_rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A product-face exit controls the sum of local exponentials without a
dimension factor in the exponent. Valid division states are retained. -/
theorem product_exit_bound {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (γ : ℝ) (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (center : Fin k → Point) (hc : ∀ j a, center j a ≤ 34)
    (E : Fin k → Point → ℝ) (hE : ∀ j y, (1/200)*normSq y ≤ E j y)
    (b : ℝ) (hb : b ≤ 1/32000000) (α a C : ℝ) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hgen : ∀ s ∈ productDomain N center E b, s.2 < 2*(k*N) → ∀ i,
      modularGenerator γ w (fun t => Real.exp (α*(N : ℝ)*
        E i (fun j => modularConcentration t i j-center i j))) s ≤ C)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (retainedModularModel γ w hγ hw N (productDomain N center E b)).total s ≤ q)
    (s : {s : ModularCountState k // s ∈ productDomain N center E b})
    (hstart : ∀ i, E i (fun j => modularConcentration s.val i j-center i j) ≤ a) :
    Real.exp (α*(N : ℝ)*b)*
      ((retainedModularModel γ w hγ hw N (productDomain N center E b)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator {none}) (some s) ≤
      (k : ℝ)*(Real.exp (α*(N : ℝ)*a)+(t : ℝ)*C) := by
  classical
  let F : Fin k → ModularCountState k → ℝ := fun i s =>
    Real.exp (α*(N : ℝ)*E i (fun j => modularConcentration s i j-center i j))
  have hsum (x) : 0 ≤ ∑ i, F i x := Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  have hboundary (x) (hx : x ∈ productDomain N center E b) (hm : x.2 < 2*(k*N))
      (r) (hr : modularNext x r ∉ productDomain N center E b) :
      Real.exp (α*(N : ℝ)*b) ≤ ∑ i, F i (modularNext x r) := by
    obtain ⟨i,hi⟩ := product_departure_energy hk N hN center hc E hE b hb x hx hm r hr
    have he : Real.exp (α*(N : ℝ)*b) ≤ F i (modularNext x r) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi (mul_nonneg hα (Nat.cast_nonneg N)))
    exact he.trans (Finset.single_le_sum
      (fun j _ => (show 0 ≤ F j (modularNext x r) from (Real.exp_pos _).le)) (Finset.mem_univ i))
  have hg (x) (hx : x ∈ productDomain N center E b) (hm : x.2 < 2*(k*N)) :
      modularGenerator γ w (fun y => ∑ i, F i y) x ≤ (k : ℝ)*C := by
    rw [modular_generator_sum]
    calc
      _ ≤ ∑ _i : Fin k, C := Finset.sum_le_sum (fun i _ => hgen x hx hm i)
      _ = _ := by simp
  have h := retained_modular_event_bound γ w hγ hw N (productDomain N center E b)
    (fun y => ∑ i, F i y) (Real.exp (α*(N : ℝ)*b)) ((k : ℝ)*C)
    (Real.exp_pos _).le (mul_nonneg (Nat.cast_nonneg _) hC) (fun y _ => hsum y)
    hboundary hg q t hq hclock s
  have hs : ∑ i, F i s.val ≤ (k : ℝ)*Real.exp (α*(N : ℝ)*a) := by
    calc
      _ ≤ ∑ _i : Fin k, Real.exp (α*(N : ℝ)*a) := Finset.sum_le_sum (fun i _ =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hstart i) (mul_nonneg hα (Nat.cast_nonneg N))))
      _ = _ := by simp
  nlinarith only [h,hs]

end CompositionalMemory
