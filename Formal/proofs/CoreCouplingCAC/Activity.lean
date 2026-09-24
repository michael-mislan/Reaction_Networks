import proofs.CoreCouplingCAC.Main

namespace CoreCouplingCAC

noncomputable def coreAB (p : Rates) (x : State) : ℝ × ℝ :=
  (-(x.A-x.B*x.z)+2*p.e*(x.B-x.A^2),
    (x.A-x.B*x.z)-p.e*(x.B-x.A^2))

theorem productivity_balance (p : Rates) (x : State) :
    (coreAB p x).1+2*(coreAB p x).2+(coreZH p x).1 = fZ p x.A x.B x.z x.H := by
  simp [coreAB,coreZH,fZ]
  ring

theorem stationary_core_exclusion (p : Rates) (x : State) (hs : Stationary p x) :
    ¬ (0 < (coreAB p x).1 ∧ 0 < (coreAB p x).2 ∧ 0 < (coreZH p x).1) := by
  have h := productivity_balance p x
  rw [hs.2.2.1] at h
  rintro ⟨ha,hb,hz⟩
  linarith

theorem uniform_productivity_z_growth (p : Rates) (x : State) (η : ℝ)
    (ha : η ≤ (coreAB p x).1) (hb : η ≤ (coreAB p x).2)
    (hz : η ≤ (coreZH p x).1) : 4*η ≤ fZ p x.A x.B x.z x.H := by
  have h := productivity_balance p x
  linarith

theorem stationary_AB_margins (p : Rates) (x : State) (hs : Stationary p x) :
    (coreAB p x).1 = x.A-p.a ∧ (coreAB p x).2 = x.B-p.b := by
  have ha := hs.1
  have hb := hs.2.1
  dsimp [fA] at ha
  dsimp [fB] at hb
  dsimp [coreAB]
  constructor <;> linarith

theorem stationary_z_margin (p : Rates) (x : State) (hs : Stationary p x)
    (hd : 2+p.d ≠ 0) :
    (coreZH p x).1 = (p.u*(1-p.d)*x.z-p.v*(1+2*p.d)*x.z^2)/(2+p.d) := by
  have hh := hs.2.2.2
  dsimp [fH] at hh
  apply (eq_div_iff hd).2
  dsimp [coreZH]
  linear_combination -3*hh

theorem stationary_ZH_criterion (p : Rates) (hp : p.Positive) (x : State)
    (hx : x.Positive) (hs : Stationary p x) :
    (0 < (coreZH p x).1 ∧ 0 < (coreZH p x).2) ↔
      p.d < 1 ∧ x.z < p.u*(1-p.d)/(p.v*(1+2*p.d)) := by
  have hu := hp.2.2.1
  have hv := hp.2.2.2.1
  have hd := hp.2.2.2.2.2
  have hz := hx.2.2.1
  have hden : 0 < 2+p.d := by positivity
  have hcoef : 0 < p.v*(1+2*p.d) := by positivity
  rw [stationary_z_margin p x hs (ne_of_gt hden)]
  have hh := stationary_H_margin_pos p x hp hx hs
  have hfac : p.u*(1-p.d)*x.z-p.v*(1+2*p.d)*x.z^2 =
      x.z*(p.u*(1-p.d)-p.v*(1+2*p.d)*x.z) := by ring
  rw [hfac,div_pos_iff_of_pos_right hden,mul_pos_iff_of_pos_left hz]
  constructor
  · rintro ⟨h,_⟩
    have hprod : 0 < p.v*(1+2*p.d)*x.z := mul_pos hcoef hz
    have hless : p.d < 1 := by
      have hpos : 0 < p.u*(1-p.d) := by linarith only [h,hprod]
      have := (mul_pos_iff_of_pos_left hu).1 hpos
      linarith only [this]
    exact ⟨hless,(lt_div_iff₀ hcoef).2 (by linarith)⟩
  · rintro ⟨_,h⟩
    exact ⟨by have := (lt_div_iff₀ hcoef).1 h; linarith,hh⟩

theorem selected_same_signature : ∃ c₁ c₂ : State,
    c₁.z < c₂.z ∧ Stationary witnessRates c₁ ∧ Stationary witnessRates c₂ ∧
    (∀ c ∈ ({c₁,c₂} : Set State),
      ¬ (0 < (coreAB witnessRates c).1 ∧ 0 < (coreAB witnessRates c).2) ∧
      0 < (coreZH witnessRates c).1 ∧ 0 < (coreZH witnessRates c).2) ∧
    SourceSelected lowLeft lowRight c₁ ∧ SourceSelected highLeft highRight c₂ := by
  obtain ⟨c₁,c₂,hp₁,hp₂,hs₁,hs₂,hlt,hsel₁,hsel₂⟩ := two_selected_active_equilibria
  have hactive : ∀ L R c, Selected L R c →
      0 < (coreZH witnessRates c).1 ∧ 0 < (coreZH witnessRates c).2 := by
    intro L R c h
    obtain ⟨X,hX,hall⟩ := h c (near_self c)
    have hh := hall 0 le_rfl
    rw [hX] at hh
    exact ⟨by linarith only [hh.2.2.2.1],by linarith only [hh.2.2.2.2]⟩
  have ha₁ := hactive _ _ _ hsel₁
  have ha₂ := hactive _ _ _ hsel₂
  refine ⟨c₁,c₂,hlt,hs₁,hs₂,?_,selected_source _ _ _ low_weight_lower hsel₁,
    selected_source _ _ _ high_weight_lower hsel₂⟩
  intro c hc
  rcases hc with rfl | hc
  · exact ⟨fun h => stationary_core_exclusion _ _ hs₁ ⟨h.1,h.2,ha₁.1⟩,ha₁⟩
  · have he : c = c₂ := hc
    subst c
    exact ⟨fun h => stationary_core_exclusion _ _ hs₂ ⟨h.1,h.2,ha₂.1⟩,ha₂⟩

end CoreCouplingCAC
