import proofs.MultiConsumerPermanence.FlowBounds

namespace MultiConsumerPermanence
open CoreCouplingGlobal CoreCouplingCAC

theorem positive_global_vector (n : ℕ) (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (x₀ : Vector n) (hx₀ : ∀ i, 0 < x₀ i) :
    ∃ X : ℝ → Vector n, X 0 = x₀ ∧
      (∀ t, 0 ≤ t → ∀ i, 0 < X t i) ∧
      ∀ t, 0 ≤ t → HasDerivAt X (field e (X t)) t := by
  let S := max (x₀ (.inl 0)+x₀ (.inl 1)) 34
  let W := max (x₀ (.inl 2)+(7/4:ℝ)*x₀ (.inl 3)) ((7/2)*(S+76))
  let Q := max (total (fun i => x₀ (.inr i))) W
  let R := max S Q+1
  have hS : 34 ≤ S := le_max_right _ _
  have hR : 1 ≤ R := by
    have hh : S ≤ max S Q := le_max_left _ _
    dsimp [R]
    linarith
  obtain ⟨b,X,hb,hbone,hX0,hXd⟩ := extension_solution n e R (by linarith) x₀
  have hinit : ∀ i, 0 < X 0 i := by simpa only [hX0] using hx₀
  have hnonneg := extension_nonnegative e he b (fun x => (hb x).1) X
    (fun i => (hinit i).le) hXd
  have hpart : ∀ t, 0 ≤ t → positivePart (X t) = X t := by
    intro t ht
    funext i
    exact max_eq_right (hnonneg t ht i)
  have hscaled : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • field e (X t)) t := by
    intro t ht
    simpa only [hpart t ht] using hXd t
  have hs := extension_total_bound e S he he' hS b (fun x => (hb x).1) X hnonneg
    (by simpa only [hX0] using (le_max_left (x₀ (.inl 0)+x₀ (.inl 1)) 34)) hscaled
  have hw := extension_weighted_bound e S W (le_max_right _ _) b (fun x => (hb x).1)
    X hnonneg hs (by simpa only [hX0] using
      (le_max_left (x₀ (.inl 2)+(7/4:ℝ)*x₀ (.inl 3)) ((7/2)*(S+76)))) hscaled
  have hq := extension_abundance_bound e Q b (fun x => (hb x).1) X hnonneg
    (fun t ht => by
      have hh := hw t ht
      have hn := hnonneg t ht (.inl 3)
      have hWQ : W ≤ Q := le_max_right _ _
      linarith)
    (by simpa only [hX0] using le_max_left (total (fun i => x₀ (.inr i))) W) hscaled
  have hQR : Q ≤ R := by dsimp [R]; linarith [le_max_right S Q]
  have hupper : ∀ t, 0 ≤ t → ∀ i, X t i ≤ R := by
    intro t ht i
    have h₀ := hnonneg t ht (.inl 0)
    have h₁ := hnonneg t ht (.inl 1)
    have h₂ := hnonneg t ht (.inl 2)
    have h₃ := hnonneg t ht (.inl 3)
    have hs' := hs t ht
    have hw' := hw t ht
    have hSR : S ≤ R := by dsimp [R]; linarith [le_max_left S Q]
    have hWR : W ≤ R := (le_max_right _ _).trans hQR
    cases i with
    | inl i => fin_cases i <;> dsimp <;> linarith
    | inr i => exact (coordinate_le_total _ (hnonneg t ht) i).trans ((hq t ht).trans hQR)
  have hnorm : ∀ t, 0 ≤ t → ‖X t‖ ≤ R := by
    intro t ht
    apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R)).2
    intro i
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hnonneg t ht i)] using hupper t ht i
  have hd : ∀ t, 0 ≤ t → HasDerivAt X (field e (X t)) t := by
    intro t ht
    simpa only [hbone _ (hnorm t ht),one_smul] using hscaled t ht
  have hpos : ∀ t, 0 ≤ t → ∀ i, 0 < X t i := by
    intro t ht i
    exact positive_of_linear_lower (fun t => X t i) (fun t => field e (X t) i)
      (20+(7+(n:ℝ))*R) (fun s hs => hasDerivAt_pi.1 (hd s hs) i) (hinit i)
      (fun s hs => field_linear_lower e R he he' hR (X s) (hnonneg s hs) (hupper s hs)
        ((hq s hs).trans hQR) i) t ht
  exact ⟨X,hX0,hpos,hd⟩

theorem positive_global_solution (n : ℕ) (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (s₀ : State) (x₀ : Fin n → ℝ) (hs₀ : s₀.Positive) (hx₀ : ∀ i, 0 < x₀ i) :
    ∃ Y : ℝ → State, ∃ x : ℝ → Fin n → ℝ,
      Y 0 = s₀ ∧ x 0 = x₀ ∧ IsMultiTrajectory n e Y x := by
  let y₀ : Vector n := Sum.elim ![s₀.A,s₀.B,s₀.z,s₀.H] x₀
  have hy₀ : ∀ i, 0 < y₀ i := by
    intro i
    cases i with
    | inl i =>
      fin_cases i
      · exact hs₀.1
      · exact hs₀.2.1
      · exact hs₀.2.2.1
      · exact hs₀.2.2.2
    | inr i => exact hx₀ i
  obtain ⟨Z,hZ0,hZp,hZd⟩ := positive_global_vector n e he he' y₀ hy₀
  let Y : ℝ → State := fun t => ⟨Z t (.inl 0),Z t (.inl 1),Z t (.inl 2),Z t (.inl 3)⟩
  let x : ℝ → Fin n → ℝ := fun t i => Z t (.inr i)
  refine ⟨Y,x,?_,?_,?_⟩
  · simp only [Y,hZ0,y₀]
    rfl
  · funext i
    change Z 0 (.inr i) = x₀ i
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
      dx := ?_ }
    · intro t ht
      exact ⟨hZp t ht (.inl 0),hZp t ht (.inl 1),hZp t ht (.inl 2),hZp t ht (.inl 3)⟩
    · intro t ht
      exact total_nonneg _ (fun i => (hZp t ht (.inr i)).le)
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
    · intro t ht i
      exact hasDerivAt_pi.1 (hZd t ht) (.inr i)

end MultiConsumerPermanence
