import proofs.FiniteReservoir.BathPrefixes

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor RandomViability.Binding CommonPhysicalRealization

def grossAllowance (V n : ℕ) : ℝ := (n:ℝ)*(Nat.floor ((V:ℝ)/5):ℝ)
def reservoirSize (V n : ℕ) (rho : ℝ) : ℕ := max 1 ⌈grossAllowance V n/rho⌉₊

theorem reservoir_size_positive (V n : ℕ) (rho : ℝ) : 0 < reservoirSize V n rho := by
  unfold reservoirSize
  have := le_max_left 1 (⌈grossAllowance V n/rho⌉₊)
  omega

theorem reservoir_size_budget (V n : ℕ) (rho : ℝ) (hr : 0 < rho) :
    grossAllowance V n ≤ rho*(reservoirSize V n rho:ℝ) := by
  have hc : grossAllowance V n/rho ≤ (reservoirSize V n rho:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (⌈grossAllowance V n/rho⌉₊)))
  have := (div_le_iff₀ hr).mp hc
  linarith

theorem pure_prefix_tolerance {R N V policy h} (tr : HistoryTrace R N V policy h)
    (hR : 0 < R) (hinit : N.2=pureFuel R) (n : ℕ) (hh : h ∈ returnedFinal V R n)
    (rho : ℝ) (hs : grossAllowance V n ≤ rho*(R:ℝ))
    (b : FuelState R) (hb : b ∈ tr.visitedBath) :
    1-rho ≤ (b.val:ℝ)/R ∧ (b.val:ℝ)/R ≤ 1 ∧ ((bathOf b).waste:ℝ)/R ≤ rho := by
  have hf := (tr.successful_prefix_bound n hh b hb).1
  rw [hinit] at hf
  change |(b.val:ℝ)-(R:ℝ)| ≤ grossAllowance V n at hf
  have hr : (0:ℝ) < R := by exact_mod_cast hR
  have hle : (b.val:ℝ) ≤ R := by exact_mod_cast (Nat.le_of_lt_succ b.isLt)
  obtain ⟨hl,_⟩ := abs_le.mp hf
  have hw : ((bathOf b).waste:ℝ)=(R:ℝ)-(b.val:ℝ) := by
    simp only [bathOf,Nat.cast_sub (Nat.le_of_lt_succ b.isLt)]
  refine ⟨(le_div_iff₀ hr).mpr (by nlinarith), (div_le_iff₀ hr).mpr (by linarith),?_⟩
  rw [div_le_iff₀ hr,hw]
  nlinarith

theorem loaded_prefix_tolerance {R N V policy h} (tr : HistoryTrace (2*R) N V policy h)
    (hR : 0 < R) (hinit : N.2=loadedFuel R) (n : ℕ) (hh : h ∈ returnedFinal V (2*R) n)
    (rho : ℝ) (hs : grossAllowance V n ≤ rho*(R:ℝ))
    (b : FuelState (2*R)) (hb : b ∈ tr.visitedBath) :
    (1-rho ≤ (b.val:ℝ)/R ∧ (b.val:ℝ)/R ≤ 1+rho) ∧
    (1-rho ≤ ((bathOf b).waste:ℝ)/R ∧ ((bathOf b).waste:ℝ)/R ≤ 1+rho) := by
  obtain ⟨hf,hp⟩ := tr.successful_prefix_bound n hh b hb
  rw [hinit] at hf hp
  rw [loaded_bath] at hp
  have hr : (0:ℝ) < R := by exact_mod_cast hR
  exact ⟨stock_tolerance R b.val (grossAllowance V n) rho hr hf hs,
    stock_tolerance R (bathOf b).waste (grossAllowance V n) rho hr hp hs⟩

theorem loaded_prefix_force {R N V policy h} (tr : HistoryTrace (2*R) N V policy h)
    (hR : 0 < R) (hinit : N.2=loadedFuel R) (n : ℕ) (hh : h ∈ returnedFinal V (2*R) n)
    (rho : ℝ) (hr : 0 < rho) (hr1 : rho < 1) (hs : grossAllowance V n ≤ rho*(R:ℝ))
    (b : FuelState (2*R)) (hb : b ∈ tr.visitedBath) :
    |Real.log (((b.val:ℝ)/R)/(((bathOf b).waste:ℝ)/R))| ≤ Real.log ((1+rho)/(1-rho)) := by
  obtain ⟨hf,hp⟩ := loaded_prefix_tolerance tr hR hinit n hh rho hs b hb
  exact activity_force_bound rho _ _ hr hr1 hf.1 hf.2 hp.1 hp.2

end
end FiniteReservoir
