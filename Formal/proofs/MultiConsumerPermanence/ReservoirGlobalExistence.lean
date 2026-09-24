import proofs.MultiConsumerPermanence.ReservoirFlowBounds

namespace MultiConsumerPermanence
open CoreCouplingGlobal CoreCouplingCAC RobustPermanence

theorem reservoir_positive_global_vector (n : ℕ) (e d : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hd : 0 < d)
    (x₀ : ReservoirVector n) (hx₀ : ∀ i, 0 < x₀ i) :
    ∃ X : ℝ → ReservoirVector n, X 0 = x₀ ∧
      (∀ t, 0 ≤ t → ∀ i, 0 < X t i) ∧
      ∀ t, 0 ≤ t → HasDerivAt X (reservoirField e d d (X t)) t := by
  let S := max (x₀ (.inl 0)+x₀ (.inl 1)) 34
  let W := max (x₀ (.inl 2)+(7/4:ℝ)*x₀ (.inl 3)) ((7/2)*(S+76))
  let c := min d (1/2)
  have hc : 0 < c := lt_min hd (by norm_num)
  let Q := max (x₀ (.inl 4)+total (fun i => x₀ (.inr i))) (d/c)
  let R := max S (max W Q)+1
  have hS : 34 ≤ S := le_max_right _ _
  have hR : 1 ≤ R := by
    have hh : S ≤ max S (max W Q) := le_max_left _ _
    dsimp [R]
    linarith
  have hSR : S ≤ R := by dsimp [R]; linarith [le_max_left S (max W Q)]
  have hWR : W ≤ R := by
    have hh := (le_max_left W Q).trans (le_max_right S (max W Q))
    dsimp [R]
    linarith
  have hQR : Q ≤ R := by
    have hh := (le_max_right W Q).trans (le_max_right S (max W Q))
    dsimp [R]
    linarith
  obtain ⟨b,X,hb,hbone,hX0,hXd⟩ := reservoir_extension_solution n e d d R (by linarith) x₀
  have hinit : ∀ i, 0 < X 0 i := by simpa only [hX0] using hx₀
  have hnonneg := reservoir_extension_nonnegative e d d he hd.le b (fun x => (hb x).1) X
    (fun i => (hinit i).le) hXd
  have hpart : ∀ t, 0 ≤ t → reservoirPart (X t) = X t := by
    intro t ht
    funext i
    exact max_eq_right (hnonneg t ht i)
  have hscaled : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • reservoirField e d d (X t)) t := by
    intro t ht
    simpa only [hpart t ht] using hXd t
  have hs := reservoir_extension_total_bound e d d S he he' hS b (fun x => (hb x).1) X hnonneg
    (by simpa only [hX0] using le_max_left (x₀ (.inl 0)+x₀ (.inl 1)) 34) hscaled
  have hw := reservoir_extension_weighted_bound e d d S W (le_max_right _ _) b (fun x => (hb x).1)
    X hnonneg hs (by simpa only [hX0] using
      (le_max_left (x₀ (.inl 2)+(7/4:ℝ)*x₀ (.inl 3)) ((7/2)*(S+76)))) hscaled
  have hq := reservoir_extension_supply_bound e d c Q hc (min_le_left _ _) (min_le_right _ _)
    (le_max_right _ _) b (fun x => (hb x).1) X hnonneg
    (by simpa only [hX0] using le_max_left (x₀ (.inl 4)+total (fun i => x₀ (.inr i))) (d/c)) hscaled
  have htotal : ∀ t, 0 ≤ t → total (fun i => X t (.inr i)) ≤ R := by
    intro t ht
    have hh := hq t ht
    have hp := hnonneg t ht (.inl 4)
    linarith
  have hupper : ∀ t, 0 ≤ t → ∀ i, X t i ≤ R := by
    intro t ht i
    have h₀ := hnonneg t ht (.inl 0)
    have h₁ := hnonneg t ht (.inl 1)
    have h₂ := hnonneg t ht (.inl 2)
    have h₃ := hnonneg t ht (.inl 3)
    have hs' := hs t ht
    have hw' := hw t ht
    have hq' := hq t ht
    have htot := total_nonneg (fun i => X t (.inr i)) (fun i => hnonneg t ht (.inr i))
    cases i with
    | inl i => fin_cases i <;> dsimp <;> linarith
    | inr i => exact (reservoir_coordinate_le_total _ (hnonneg t ht) i).trans (htotal t ht)
  have hnorm : ∀ t, 0 ≤ t → ‖X t‖ ≤ R := by
    intro t ht
    apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R)).2
    intro i
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hnonneg t ht i)] using hupper t ht i
  have hdX : ∀ t, 0 ≤ t → HasDerivAt X (reservoirField e d d (X t)) t := by
    intro t ht
    simpa only [hbone _ (hnorm t ht),one_smul] using hscaled t ht
  have hpos : ∀ t, 0 ≤ t → ∀ i, 0 < X t i := by
    intro t ht i
    exact positive_of_linear_lower (fun t => X t i) (fun t => reservoirField e d d (X t) i)
      (31+d+((n:ℝ)+11)*R^2) (fun s hs => hasDerivAt_pi.1 (hdX s hs) i) (hinit i)
      (fun s hs => reservoir_field_linear_lower e d R he he' hd.le hR (X s)
        (hnonneg s hs) (hupper s hs) (htotal s hs) i) t ht
  exact ⟨X,hX0,hpos,hdX⟩

theorem reservoir_positive_global_solution (n : ℕ) (e d : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hd : 0 < d)
    (s₀ : State) (x₀ : Fin n → ℝ) (r₀ : ℝ)
    (hs₀ : s₀.Positive) (hx₀ : ∀ i, 0 < x₀ i) (hr₀ : 0 < r₀) :
    ∃ Y : ℝ → State, ∃ x : ℝ → Fin n → ℝ, ∃ R : ℝ → ℝ,
      Y 0 = s₀ ∧ x 0 = x₀ ∧ R 0 = r₀ ∧ IsReservoirTrajectory n e d d Y x R := by
  let y₀ : ReservoirVector n := Sum.elim ![s₀.A,s₀.B,s₀.z,s₀.H,r₀] x₀
  have hy₀ : ∀ i, 0 < y₀ i := by
    intro i
    cases i with
    | inl i =>
      fin_cases i
      · exact hs₀.1
      · exact hs₀.2.1
      · exact hs₀.2.2.1
      · exact hs₀.2.2.2
      · exact hr₀
    | inr i => exact hx₀ i
  obtain ⟨Z,hZ0,hZp,hZd⟩ := reservoir_positive_global_vector n e d he he' hd y₀ hy₀
  let Y : ℝ → State := fun t => ⟨Z t (.inl 0),Z t (.inl 1),Z t (.inl 2),Z t (.inl 3)⟩
  let x : ℝ → Fin n → ℝ := fun t i => Z t (.inr i)
  let R : ℝ → ℝ := fun t => Z t (.inl 4)
  refine ⟨Y,x,R,?_,?_,?_,?_⟩
  · simp only [Y,hZ0,y₀]
    rfl
  · funext i
    change Z 0 (.inr i) = x₀ i
    rw [hZ0]
    rfl
  · change Z 0 (.inl 4) = r₀
    rw [hZ0]
    rfl
  · refine {
      positive := ?_
      load_nonnegative := ?_
      dA := ?_
      dB := ?_
      dz := ?_
      dH := ?_
      consumer_positive := ?_
      reservoir_positive := ?_
      dx := ?_
      dR := ?_ }
    · intro t ht
      exact ⟨hZp t ht (.inl 0),hZp t ht (.inl 1),hZp t ht (.inl 2),hZp t ht (.inl 3)⟩
    · intro t ht
      exact mul_nonneg (hZp t ht (.inl 4)).le (total_nonneg _ (fun i => (hZp t ht (.inr i)).le))
    · intro t ht
      exact hasDerivAt_pi.1 (hZd t ht) (.inl 0)
    · intro t ht
      exact hasDerivAt_pi.1 (hZd t ht) (.inl 1)
    · intro t ht
      exact hasDerivAt_pi.1 (hZd t ht) (.inl 2)
    · intro t ht
      exact hasDerivAt_pi.1 (hZd t ht) (.inl 3)
    · intro t ht i
      exact hZp t ht (.inr i)
    · intro t ht
      exact hZp t ht (.inl 4)
    · intro t ht i
      exact hasDerivAt_pi.1 (hZd t ht) (.inr i)
    · intro t ht
      exact hasDerivAt_pi.1 (hZd t ht) (.inl 4)

end MultiConsumerPermanence
