import proofs.OverlappingSiphonInvasion.ProductFloor

noncomputable section
namespace OverlappingSiphonInvasion
open Filter Topology

theorem private_forcing (s a b c m : ℝ)
    (hs : 1/6 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hI : a+b+c ≤ 5) (hu : m ≤ a+c) (hv : m ≤ b+2*c) :
    m/60-3*a ≤ a*(2*s-b/10-c/10-1)+s*c/10 ∧
    m/12-3*b ≤ b*(s-a/10-c/10-1)+s*c := by
  have hs0 : 0 ≤ s := by linarith
  have hsc := mul_nonneg (show 0 ≤ s-1/6 by linarith) hc
  have hsa := mul_nonneg hs0 ha
  have hsb := mul_nonneg hs0 hb
  have hal := mul_nonneg ha (show 0 ≤ 1-(b+c)/10 by linarith)
  have hbl := mul_nonneg hb (show 0 ≤ 1-(a+c)/10 by linarith)
  constructor <;> nlinarith only [hsc,hsa,hsb,hal,hbl,hu,hv,ha,hb]

theorem eventually_private_floors (X : ℝ → State) (h : IsTrajectory (witness 1) X) :
    ∀ᶠ t in atTop, massFloor/360 ≤ X t 1 ∧ massFloor/72 ≤ X t 2 := by
  obtain ⟨T,hT⟩ := eventually_atTop.1
    ((eventually_susceptible_floor X h).and ((eventually_siphon_masses X h).and
      ((eventually_infected_bounds X h).and (eventually_ge_atTop (0:ℝ)))))
  have hforce (t : ℝ) (ht : T ≤ t) :
      massFloor/60-3*X t 1 ≤ field (witness 1) (X t) 1 ∧
      massFloor/12-3*X t 2 ≤ field (witness 1) (X t) 2 := by
    have hp := h.positive t (hT t ht).2.2.2
    have hh := private_forcing (X t 0) (X t 1) (X t 2) (X t 3) massFloor
      (hT t ht).1 (hp 1).le (hp 2).le (hp 3).le
      (hT t ht).2.2.1.2 (hT t ht).2.1.1 (hT t ht).2.1.2
    simpa [field,witness,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
  have ha := lower_of_linear (fun t => X t 1) (fun t => field (witness 1) (X t) 1)
    T (massFloor/60) 3 (massFloor/360) (by norm_num)
    (by have hp := massFloor_pos; linarith)
    (fun t ht => h.derivative t (hT t ht).2.2.2 1) (fun t ht => (hforce t ht).1)
  have hb := lower_of_linear (fun t => X t 2) (fun t => field (witness 1) (X t) 2)
    T (massFloor/12) 3 (massFloor/72) (by norm_num)
    (by have hp := massFloor_pos; linarith)
    (fun t ht => h.derivative t (hT t ht).2.2.2 2) (fun t ht => (hforce t ht).2)
  filter_upwards [ha,hb] with t ht ht'
  exact ⟨ht.le,ht'.le⟩

theorem eventually_shared_floor (X : ℝ → State) (h : IsTrajectory (witness 1) X) :
    ∀ᶠ t in atTop, massFloor^2/259200 ≤ X t 3 := by
  obtain ⟨T,hT⟩ := eventually_atTop.1
    ((eventually_private_floors X h).and (eventually_ge_atTop (0:ℝ)))
  have hl := lower_of_linear (fun t => X t 3) (fun t => field (witness 1) (X t) 3)
    T (massFloor^2/129600) 1 (massFloor^2/259200) (by norm_num)
    (by have hp := sq_pos_of_pos massFloor_pos; nlinarith)
    (fun t ht => h.derivative t (hT t ht).2 3) (by
      intro t ht
      have hp := h.positive t (hT t ht).2
      have hs := (hp 0).le
      have ha := (hp 1).le
      have hb := (hp 2).le
      have hc := (hp 3).le
      have hm := mul_le_mul (hT t ht).1.1 (hT t ht).1.2
        (by have hh := massFloor_pos; positivity : 0 ≤ massFloor/72) ha
      have hp1 := mul_nonneg hc ha
      have hp2 := mul_nonneg hc hb
      have hp0 := mul_nonneg hc hs
      simp [field,witness]
      nlinarith only [hm,hp1,hp2,hp0])
  filter_upwards [hl] with t ht
  exact ht.le

def speciesFloor : ℝ := min (1/6) (min (massFloor/360)
  (min (massFloor/72) (massFloor^2/259200)))

theorem speciesFloor_pos : 0 < speciesFloor := by
  have hp := massFloor_pos
  unfold speciesFloor
  positivity

/-- Uniform physical concentration bounds for every positive global solution
of the literal invading witness, independent of its initial condition. -/
theorem witness_trajectory_permanence (X : ℝ → State) (h : IsTrajectory (witness 1) X) :
    ∀ᶠ t in atTop, ∀ i, speciesFloor ≤ X t i ∧ X t i ≤ 5 := by
  filter_upwards [eventually_susceptible_floor X h,eventually_private_floors X h,
    eventually_shared_floor X h,eventually_total_close X h,eventually_ge_atTop (0:ℝ)]
    with t hs hp hc hn ht
  intro i
  have h0 := h.positive t ht 0
  have h1 := h.positive t ht 1
  have h2 := h.positive t ht 2
  have h3 := h.positive t ht 3
  have hn' := (abs_le.mp hn).2
  have hmin0 : speciesFloor ≤ 1/6 := min_le_left _ _
  have hmin1 : speciesFloor ≤ massFloor/360 := (min_le_right _ _).trans (min_le_left _ _)
  have hmin2 : speciesFloor ≤ massFloor/72 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmin3 : speciesFloor ≤ massFloor^2/259200 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  dsimp [total] at hn'
  fin_cases i <;> dsimp <;> constructor <;> linarith

end OverlappingSiphonInvasion
