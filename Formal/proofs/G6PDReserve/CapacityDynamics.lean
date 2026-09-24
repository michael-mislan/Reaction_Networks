import proofs.G6PDReserve.SourceExistence
import proofs.G6PDReserve.SourceRate

namespace G6PDReserve.Population
noncomputable section
open Set

def rate (V g : ℝ) : ℝ := V * ((56-g)/(2*(56-g)+(3/56)*g+3))
def Admitted (V : ℝ) : Prop := V ∈ Icc (5/8) (9/14) ∨ V ∈ Icc 1 (11/8)
def Solution (V : ℝ) (g : ℝ → ℝ) : Prop :=
  g 0 = 10 ∧ (∀ t ∈ Icc 0 120, g t ∈ Icc 0 56) ∧
    ∀ t ∈ Icc 0 120, HasDerivAt g (rate V (g t)-3/10) t
def Hits (g : ℝ → ℝ) : Prop := ∃ t ∈ Icc (0:ℝ) 120, 28 ≤ g t

theorem literal_rate (V g : ℝ) :
    shimoRate V 3 7 56 125 520 (56-g) 7 g 0 0 = rate V g := by
  unfold shimoRate rate
  have he : 1 + ((56-g)/3)*(1+(7:ℝ)/7)+g/56+0/125+0/520 =
      (2*(56-g)+(3/56)*g+3)/3 := by ring
  rw [he, div_div_eq_mul_div]
  ring

theorem rate_scalar (V g : ℝ) (hV : 0 < V) :
    scalarRate (2/V) ((3/56)/V) (3/V) 56 g = rate V g := by
  unfold scalarRate rate
  field_simp [ne_of_gt hV]

theorem admitted_lower {V : ℝ} (hV : Admitted V) : 5/8 ≤ V := by
  rcases hV with h | h
  · exact h.1
  · linarith [h.1]

theorem rate_zero (V : ℝ) : rate V 0 = 56*V/115 := by unfold rate; ring
theorem rate_target (V : ℝ) : rate V 28 = 56*V/121 := by unfold rate; ring

theorem solution_exists (V : ℝ) (hV : 5/8 ≤ V) : ∃ g, Solution V g := by
  have hp : 0 < V := by linarith
  obtain ⟨g,h0,hpool,hd⟩ := scalar_solution_exists (2/V) ((3/56)/V) (3/V)
    56 (3/10) 10 120 (by positivity) (by positivity) (by positivity)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
      rw [rate_scalar V 0 hp, rate_zero]; linarith)
  refine ⟨g,h0,hpool,?_⟩
  intro t ht
  simpa only [rate_scalar V (g t) hp] using hd t ht

theorem rate_anti (V : ℝ) (hV : 0 < V) : StrictAntiOn (rate V) (Icc 0 56) := by
  have h := scalar_rate_strictAnti (2/V) ((3/56)/V) (3/V) 56
    (by positivity) (by positivity) (by positivity) (by norm_num)
  intro x hx y hy hxy
  simpa only [rate_scalar V x hV, rate_scalar V y hV] using h hx hy hxy

theorem high_hits {V : ℝ} (hV : 1 ≤ V) {g : ℝ → ℝ} (hg : Solution V g) : Hits g := by
  have hp : 0 < V := by linarith
  have he : (28-g 0)/(197/1210) = (21780/197:ℝ) := by rw [hg.1]; norm_num
  have hsub : Icc (0:ℝ) ((28-g 0)/(197/1210)) ⊆ Icc (0:ℝ) 120 := by
    rw [he]; intro t ht; constructor; exact ht.1; linarith [ht.2]
  obtain ⟨t,ht,hh⟩ := positive_drift_reaches g 28 (197/1210) (by norm_num)
    (by rw [hg.1]; norm_num)
    (fun t ht => by simpa only [(hg.2.2 t (hsub ht)).deriv] using hg.2.2 t (hsub ht))
    (by
      intro t ht hbelow
      rw [(hg.2.2 t (hsub ht)).deriv]
      have h := (rate_anti V hp).antitoneOn (hg.2.1 t (hsub ht))
        (show (28:ℝ) ∈ Icc 0 56 by norm_num) hbelow.le
      rw [rate_target] at h
      linarith)
  exact ⟨t,hsub ht,hh⟩

theorem low_not_hits {V : ℝ} (hV : V ∈ Icc (5/8) (9/14))
    {g : ℝ → ℝ} (hg : Solution V g) : ¬ Hits g := by
  have hp : 0 < V := by linarith [hV.1]
  rintro ⟨t,ht,hh⟩
  have hbad : rate V 28 < 3/10 := by rw [rate_target]; linarith [hV.2]
  -- Use the inherited strict nonarrival theorem, including equality at the target.
  have hn := decreasing_rate_no_finite_arrival (rate V) g 56 28 (3/10)
    ((((3/56)/V)*56+3/V)/(3/V)^2) t ht.1 (by norm_num)
    (by rw [hg.1]; norm_num)
    (fun s hs => hg.2.1 s ⟨hs.1,le_trans hs.2 ht.2⟩)
    (fun s hs => hg.2.2 s ⟨hs.1,le_trans hs.2 ht.2⟩)
    (rate_anti V hp) hbad.le (by
      intro x hx
      simpa only [rate_scalar V _ hp] using scalar_secant_bound
        (2/V) ((3/56)/V) (3/V) 56 28 x
        (by positivity) (by positivity) (by positivity) (by norm_num) (by norm_num) hx)
  linarith

theorem hits_iff {V : ℝ} (hV : Admitted V) {g : ℝ → ℝ} (hg : Solution V g) :
    Hits g ↔ 1 ≤ V := by
  rcases hV with h | h
  · constructor
    · intro hh; exact False.elim (low_not_hits h hg hh)
    · intro hh; linarith [h.2]
  · exact ⟨fun _ => h.1, fun _ => high_hits h.1 hg⟩

end
end G6PDReserve.Population
