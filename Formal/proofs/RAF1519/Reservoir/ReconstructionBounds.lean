import proofs.RAF1519.Reservoir.Scalar

namespace RAF1519.Reservoir
noncomputable section
open Set

theorem uptake_mono {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) : uptake l ≤ uptake u := by
  unfold uptake
  nlinarith [mul_nonneg (sub_nonneg.mpr hlu) (show 0 ≤ u+l+1/2 by linarith)]

theorem reservoir_anti {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) : reservoir u ≤ reservoir l := by
  have h := uptake_mono hl hlu
  unfold reservoir
  linarith

theorem resource_mono {l u : ℝ} (hl : l ∈ Icc (0:ℝ) (3/40))
    (hu : u ∈ Icc (0:ℝ) (3/40)) (hlu : l ≤ u) : resource l ≤ resource u := by
  exact div_le_div₀ (by linarith [hu.1]) (by linarith)
    (reservoir_positive u hu) (reservoir_anti hl.1 hlu)

theorem substrate_anti {l u : ℝ} (hl : l ∈ Icc (0:ℝ) (3/40))
    (hu : u ∈ Icc (0:ℝ) (3/40)) (hlu : l ≤ u) : substrate u ≤ substrate l := by
  have h := resource_mono hl hu hlu
  exact div_le_div₀ (by norm_num) le_rfl
    (by have := (resource_bounds l hl).1; linarith) (by linarith)

theorem catalyst_mono {l u : ℝ} (hl : l ∈ Icc (0:ℝ) (3/40))
    (hu : u ∈ Icc (0:ℝ) (3/40)) (hlu : l ≤ u) : catalyst l ≤ catalyst u := by
  have h := resource_mono hl hu hlu
  have hz := (resource_bounds l hl).1
  have hs := mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ resource u+resource l by linarith)
  unfold catalyst
  nlinarith

def reconstructionLower (l u : ℝ) : Fin 6 → ℝ :=
  ![substrate u*resource l+16*resource l+4*(resource l)^2-3*catalyst u+uptake l,
    substrate u,resource l,catalyst l,reservoir u,l]
def reconstructionUpper (l u : ℝ) : Fin 6 → ℝ :=
  ![substrate l*resource u+16*resource u+4*(resource u)^2-3*catalyst l+uptake u,
    substrate l,resource u,catalyst u,reservoir l,u]

theorem reconstruction_bounds (l u s : ℝ) (hl : l ∈ Icc (0:ℝ) (3/40))
    (hu : u ∈ Icc (0:ℝ) (3/40)) (hs : s ∈ Icc l u) :
    ∀ i, reconstructionLower l u i ≤ state s i ∧ state s i ≤ reconstructionUpper l u i := by
  have hsI : s ∈ Icc (0:ℝ) (3/40) := ⟨hl.1.trans hs.1,hs.2.trans hu.2⟩
  have hzL := resource_mono hl hsI hs.1
  have hzU := resource_mono hsI hu hs.2
  have hbL := substrate_anti hsI hu hs.2
  have hbU := substrate_anti hl hsI hs.1
  have hhL := catalyst_mono hl hsI hs.1
  have hhU := catalyst_mono hsI hu hs.2
  have hJ : uptake l ≤ uptake s ∧ uptake s ≤ uptake u :=
    ⟨uptake_mono hl.1 hs.1,uptake_mono hsI.1 hs.2⟩
  have hR : reservoir u ≤ reservoir s ∧ reservoir s ≤ reservoir l :=
    ⟨reservoir_anti hsI.1 hs.2,reservoir_anti hl.1 hs.1⟩
  have hz0 := (resource_bounds l hl).1
  have hzs0 := (resource_bounds s hsI).1
  have hb0 : 0 ≤ substrate u := (by norm_num : (0:ℝ) ≤ 8).trans (substrate_bound u hu).le
  have hbS : 0 ≤ substrate s := hb0.trans hbL
  have hprodL := mul_le_mul hbL hzL hz0.le hbS
  have hprodU := mul_le_mul hbU hzU hzs0.le (hbS.trans hbU)
  have hsqL := mul_nonneg (sub_nonneg.mpr hzL) (show 0 ≤ resource s+resource l by linarith)
  have hsqU := mul_nonneg (sub_nonneg.mpr hzU) (show 0 ≤ resource u+resource s by linarith)
  intro i
  fin_cases i
  · change substrate u*resource l+16*resource l+4*(resource l)^2-3*catalyst u+uptake l ≤ precursor s ∧
      precursor s ≤ substrate l*resource u+16*resource u+4*(resource u)^2-3*catalyst l+uptake u
    unfold precursor
    constructor <;> nlinarith [hJ.1,hJ.2]
  · exact ⟨hbL,hbU⟩
  · exact ⟨hzL,hzU⟩
  · exact ⟨hhL,hhU⟩
  · exact hR
  · exact hs

end
end RAF1519.Reservoir
