import proofs.DiagnosticWindows.Robustness

noncomputable section
namespace AssayInformation
open DiagnosticWindows FiniteCopy

structure ErrorBand where
  blankLower : ℝ
  blankUpper : ℝ
  missLower : ℝ
  missUpper : ℝ

def ErrorBand.Covers (B : ErrorBand) (fp miss : ℝ) : Prop :=
  B.blankLower ≤ fp ∧ fp ≤ B.blankUpper ∧ B.missLower ≤ miss ∧ miss ≤ B.missUpper
def ErrorBand.Usable (B : ErrorBand) (α β : ℝ) : Prop :=
  B.blankUpper ≤ α ∧ B.missUpper ≤ β
def ErrorBand.Excluded (B : ErrorBand) (α β : ℝ) : Prop :=
  α < B.blankLower ∨ β < B.missLower
def ErrorBand.Unresolved (B : ErrorBand) (α β : ℝ) : Prop :=
  ¬ B.Usable α β ∧ ¬ B.Excluded α β

theorem usable_sound (B : ErrorBand) (fp miss α β : ℝ)
    (hc : B.Covers fp miss) (hu : B.Usable α β) : fp ≤ α ∧ miss ≤ β :=
  ⟨hc.2.1.trans hu.1,hc.2.2.2.trans hu.2⟩

theorem excluded_sound (B : ErrorBand) (fp miss α β : ℝ)
    (hc : B.Covers fp miss) (he : B.Excluded α β) : ¬(fp ≤ α ∧ miss ≤ β) := by
  intro h
  rcases he with he | he
  · linarith [hc.1,h.1]
  · linarith [hc.2.2.1,h.2]

theorem classification_complete (B : ErrorBand) (α β : ℝ) :
    B.Usable α β ∨ B.Excluded α β ∨ B.Unresolved α β := by
  by_cases hu : B.Usable α β
  · exact Or.inl hu
  · by_cases he : B.Excluded α β
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr ⟨hu,he⟩)

/-- Selection from simultaneous valid bands preserves their deterministic guarantee. -/
theorem selected_time_sound {ι : Type*} (bands : ι → ErrorBand) (fp miss : ι → ℝ)
    (α β : ℝ) (hc : ∀ i, (bands i).Covers (fp i) (miss i))
    (chosen : ι) (hu : (bands chosen).Usable α β) :
    fp chosen ≤ α ∧ miss chosen ≤ β :=
  usable_sound _ _ _ _ _ (hc chosen) hu

/-- For worst-case timing error, the endpoints are necessary as well as sufficient. -/
theorem jitter_endpoints (fp miss : ℝ → ℝ) (hf : Monotone fp) (hm : Antitone miss)
    (a b α β : ℝ) (hab : a ≤ b) :
    (∀ t ∈ Set.Icc a b, fp t ≤ α ∧ miss t ≤ β) ↔ (fp b ≤ α ∧ miss a ≤ β) := by
  constructor
  · intro h
    exact ⟨(h b ⟨hab,le_rfl⟩).1,(h a ⟨le_rfl,hab⟩).2⟩
  · intro h t ht
    exact ⟨(hf ht.2).trans h.1,(hm ht.1).trans h.2⟩

def coarseBand : ErrorBand := ⟨0,1/50,0,1/10⟩

theorem coarse_unresolved : coarseBand.Unresolved (1/100) (1/20) := by
  norm_num [ErrorBand.Unresolved,ErrorBand.Usable,ErrorBand.Excluded,coarseBand]

theorem uncertain_source_application (r : Fin 6 → ℝ)
    (h : ∀ z, (49/50:ℝ)*rates10 z ≤ r z ∧ r z ≤ (51/50:ℝ)*rates10 z)
    (load t : NNReal) (hl : 399/100 ≤ load)
    (ht0 : 319/100 ≤ t) (ht1 : t ≤ 321/100) :
    (1-(birthKernel r (uncertainty_valid r h)).poissonized ((5/2)*t) uncalled 0 ≤ 1/100) ∧
    loadedSurvival (birthKernel r (uncertainty_valid r h)) load ((5/2)*t) ≤ 1/20 :=
  robust_guarantee r h load t hl ht0 ht1

end AssayInformation
