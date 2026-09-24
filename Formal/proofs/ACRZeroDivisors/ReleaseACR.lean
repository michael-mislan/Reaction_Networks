import proofs.ACRZeroDivisors.ReleasePositive

namespace ACRZeroDivisors

def ReleaseOldState {σ : Type*} (f : (σ → ℝ) → σ → ℝ) (x : σ → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ ∀ i, f x i = 0

def ReleaseNewState {σ : Type*} {n : ℕ} (f : (σ → ℝ) → σ → ℝ)
    (F : (σ → ℝ) → ℝ) (rates : Fin (n+1) → ℝ)
    (w : σ → Fin (n+1) → ℝ) (x : σ → ℝ) (y : Fin (n+1) → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ (∀ j, 0 < y j) ∧
    (∀ i, f x i - ∑ j, w i j * (F x-rates j*y j) = 0) ∧
    ∀ j, triangularDifferences (fun j => F x-rates j*y j) j = 0

theorem release_positive_state_iff {σ : Type*} {n : ℕ}
    (f : (σ → ℝ) → σ → ℝ) (F : (σ → ℝ) → ℝ)
    (hF : ∀ x, (∀ i, 0 < x i) → 0 < F x) (rates : Fin (n+1) → ℝ)
    (hr : ∀ j, 0 < rates j) (w : σ → Fin (n+1) → ℝ)
    (x : σ → ℝ) (y : Fin (n+1) → ℝ) :
    ReleaseNewState f F rates w x y ↔
      ReleaseOldState f x ∧ y = (fun j => F x / rates j) := by
  constructor
  · rintro ⟨hx,_,hs⟩
    obtain ⟨hf,hy⟩ := (release_steady_iff (f x) (F x) rates y
      (fun j => ne_of_gt (hr j)) w).mp hs
    exact ⟨⟨hx,hf⟩,funext hy⟩
  · rintro ⟨⟨hx,hf⟩,rfl⟩
    exact ⟨hx,fun j => div_pos (hF x hx) (hr j),
      (release_steady_iff (f x) (F x) rates _ (fun j => ne_of_gt (hr j)) w).mpr
        ⟨hf,fun _ => rfl⟩⟩

/-- Nonvacuous ACR of every old coordinate is equivalent before and after release. -/
theorem release_acr_iff {σ : Type*} {n : ℕ}
    (f : (σ → ℝ) → σ → ℝ) (F : (σ → ℝ) → ℝ)
    (hF : ∀ x, (∀ i, 0 < x i) → 0 < F x) (rates : Fin (n+1) → ℝ)
    (hr : ∀ j, 0 < rates j) (w : σ → Fin (n+1) → ℝ) (i : σ) (a : ℝ) :
    ((∃ x y, ReleaseNewState f F rates w x y) ∧
      ∀ x y, ReleaseNewState f F rates w x y → x i = a) ↔
    ((∃ x, ReleaseOldState f x) ∧ ∀ x, ReleaseOldState f x → x i = a) := by
  simp only [release_positive_state_iff f F hF rates hr w]
  constructor
  · rintro ⟨⟨x,y,hx,_⟩,ha⟩
    exact ⟨⟨x,hx⟩,fun x hx => ha x _ ⟨hx,rfl⟩⟩
  · rintro ⟨⟨x,hx⟩,ha⟩
    exact ⟨⟨x,_,hx,rfl⟩,fun x _ hx => ha x hx.1⟩

end ACRZeroDivisors
