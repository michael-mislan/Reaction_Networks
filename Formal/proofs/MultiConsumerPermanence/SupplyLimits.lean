import proofs.MultiConsumerPermanence.ReservoirBounds

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal Filter Topology Set
open scoped BigOperators

theorem nonnegative_no_negative_slope (f v : ℝ → ℝ) (T c : ℝ) (hc : 0 < c)
    (hf : ∀ t, T ≤ t → 0 ≤ f t) (hd : ∀ t, T ≤ t → HasDerivAt f (v t) t)
    (hv : ∀ t, T ≤ t → v t ≤ -c) : False := by
  let t := T+(f T+1)/c
  have ht : T ≤ t := by dsimp [t]; exact le_add_of_nonneg_right (div_nonneg (by linarith [hf T le_rfl]) hc.le)
  have hh := (convex_Ici T).image_sub_le_mul_sub_of_deriv_le (f := f) (C := -c)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(hd s (interior_subset hs)).deriv]; exact hv s (interior_subset hs))
    T (Set.mem_Ici.mpr (le_refl T)) t ht ht
  have hid : c*(t-T) = f T+1 := by dsimp [t]; field_simp; ring
  have hp := hf t ht
  nlinarith only [hh,hid,hp]

theorem zero_supply_total_extinction {n : ℕ} (e : ℝ) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirTrajectory n e 0 0 Y x R) :
    Tendsto (fun t => total (x t)) atTop (𝓝 0) := by
  have hRanti : AntitoneOn R (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      exact (h.dR t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (h.dR t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have h0 : 0 ≤ t := interior_subset ht
      rw [(h.dR t h0).deriv]
      have hp := mul_nonneg (mul_nonneg (h.reservoir_positive t h0).le (h.positive t h0).2.2.1.le)
        (total_nonneg (x t) (fun i => (h.consumer_positive t h0 i).le))
      nlinarith only [hp]
  let K := R '' Ici (0:ℝ)
  have hK : K.Nonempty := ⟨R 0,0,Set.mem_Ici.mpr (le_refl (0:ℝ)),rfl⟩
  have hKb : BddBelow K := by
    refine ⟨0,?_⟩
    rintro y ⟨t,ht,rfl⟩
    exact (h.reservoir_positive t ht).le
  let L := sInf K
  have hL : ∀ t, 0 ≤ t → L ≤ R t := fun t ht => csInf_le hKb ⟨t,ht,rfl⟩
  have hupper : ∀ eps : ℝ, 0 < eps → ∀ᶠ t in atTop, total (x t) < eps := by
    intro eps heps
    obtain ⟨v,⟨a,ha,rfl⟩,hav⟩ := exists_lt_of_csInf_lt hK (show L < L+eps/2 by linarith)
    have hRtail : ∀ t, a ≤ t → R t-L ≤ eps/2 := by
      intro t ht
      have hh := hRanti ha (ha.trans ht) ht
      linarith only [hh,hav]
    have hh : ∀ᶠ t in atTop, R t+total (x t)-L < eps := by
      apply eventual_upper_of_linear_drift (fun t => R t+total (x t)-L)
        (fun t => -(1/2)*total (x t)-(n:ℝ)*squares (x t))
        a (eps/4) (1/2) eps (by norm_num) (by linarith)
      · intro t ht
        convert (reservoir_supply_balance e 0 0 Y x R h t (ha.trans ht)).sub_const L using 1
        ring
      · intro t ht
        have hr := hRtail t ht
        have hq : 0 ≤ (n:ℝ)*squares (x t) :=
          mul_nonneg (Nat.cast_nonneg n) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
        nlinarith only [hr,hq]
    filter_upwards [hh,eventually_ge_atTop (0:ℝ)] with t ht h0
    linarith only [ht,hL t h0]
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact ha.trans_le (total_nonneg (x t) (fun i => (h.consumer_positive t ht i).le))
  · exact hupper

theorem zero_supply_every_consumer_extinction {n : ℕ} (e : ℝ) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirTrajectory n e 0 0 Y x R) :
    ∀ i, Tendsto (fun t => x t i) atTop (𝓝 0) := by
  have hs := zero_supply_total_extinction e Y x R h
  intro i
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact ha.trans (h.consumer_positive t ht i)
  · intro b hb
    filter_upwards [hs.eventually_lt_const hb,eventually_ge_atTop (0:ℝ)] with t ht h0
    exact (show x t i ≤ total (x t) from
      Finset.single_le_sum (fun j _ => (h.consumer_positive t h0 j).le) (Finset.mem_univ i)).trans_lt ht

theorem necessary_supply_for_species_floor {n : ℕ} (e d eta : ℝ) (hd : 0 ≤ d) (heta : 0 ≤ eta)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirTrajectory n e d d Y x R)
    (hfloor : ∀ᶠ t in atTop, ∀ i, eta ≤ x t i) :
    ((n:ℝ)*eta)/2+(n:ℝ)^2*eta^2 ≤ d := by
  by_contra hbad
  have hc : 0 < ((n:ℝ)*eta)/2+(n:ℝ)^2*eta^2-d := by linarith
  obtain ⟨T,hT⟩ := eventually_atTop.1 (hfloor.and (eventually_ge_atTop (0:ℝ)))
  apply nonnegative_no_negative_slope (fun t => R t+total (x t))
    (fun t => d-d*R t-(1/2)*total (x t)-(n:ℝ)*squares (x t)) T
    (((n:ℝ)*eta)/2+(n:ℝ)^2*eta^2-d) hc
  · intro t ht
    exact add_nonneg (h.reservoir_positive t (hT t ht).2).le
      (total_nonneg (x t) (fun i => (h.consumer_positive t (hT t ht).2 i).le))
  · intro t ht
    exact reservoir_supply_balance e d d Y x R h t (hT t ht).2
  · intro t ht
    have hx := (hT t ht).1
    have hS : (n:ℝ)*eta ≤ total (x t) := by
      simpa [total] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hx i)
    have hQ : (n:ℝ)*eta^2 ≤ squares (x t) := by
      have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
        sq_le_sq₀ heta (heta.trans (hx i)) |>.2 (hx i))
      simpa [squares] using hh
    have hnQ := mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have hdR := mul_nonneg hd (h.reservoir_positive t (hT t ht).2).le
    nlinarith only [hS,hnQ,hdR]

end MultiConsumerPermanence
