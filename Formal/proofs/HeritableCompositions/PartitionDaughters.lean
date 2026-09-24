import proofs.HeritableCompositions.PartitionReturn
import proofs.HeritableCompositions.PartitionProduct
import proofs.HeritableCompositions.GrowthDrift
import proofs.FiniteCopy.CountSource

namespace HeritableCompositions
open FiniteCopy

theorem daughter_draw_le (n d : Counts) (hd : d ∈ daughterDraws n) (i : Fin 4) : d i ≤ n i := by
  have h := (Fintype.mem_piFinset.mp hd) i
  simpa only [Finset.mem_range,Nat.lt_succ_iff] using h

theorem daughter_concentration_noise (n d : Counts) (N : ℕ) (hN : 0 < N) (i : Fin 4) :
    concentration N d i-concentration (2*N) n i = ((d i : ℝ)-(n i : ℝ)/2)/(N : ℝ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [concentration,Nat.cast_mul,Nat.cast_ofNat]
  field_simp

theorem sibling_concentration_noise (n d : Counts) (hd : d ∈ daughterDraws n) (N : ℕ) (i : Fin 4) :
    concentration N (fun j => n j-d j) i-concentration (2*N) n i =
      -(concentration N d i-concentration (2*N) n i) := by
  simp only [concentration,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (daughter_draw_le n d hd i)]
  exact complementary_deviation (n i) (d i) N

theorem both_daughters_return (E : Point → ℝ)
    (hreturn : ∀ (y v : Point), E y ≤ 2*innerEnergy → (∀ i, |v i| ≤ 1/1000000) →
      E (fun i => y i+v i) < 4*innerEnergy)
    (n d : Counts) (hd : d ∈ daughterDraws n) (N : ℕ) (hN : 0 < N) (s : Point)
    (hparent : E (fun i => concentration (2*N) n i-s i) ≤ 2*innerEnergy)
    (hgood : ∀ i, |(d i : ℝ)-(n i : ℝ)/2| < (N : ℝ)*(1/1000000)) :
    E (fun i => concentration N d i-s i) < 4*innerEnergy ∧
    E (fun i => concentration N (fun j => n j-d j) i-s i) < 4*innerEnergy := by
  let y : Point := fun i => concentration (2*N) n i-s i
  let v : Point := fun i => concentration N d i-concentration (2*N) n i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hv (i) : |v i| ≤ 1/1000000 := by
    dsimp [v]
    rw [daughter_concentration_noise n d N hN i,abs_div,abs_of_pos hNr]
    exact ((div_lt_iff₀ hNr).mpr (by linarith only [hgood i])).le
  have hv' (i) : |-v i| ≤ 1/1000000 := by simpa only [abs_neg] using hv i
  have hfirst := hreturn y v hparent hv
  have hsecond := hreturn y (fun i => -v i) hparent hv'
  constructor
  · convert hfirst using 1
    congr 1
    funext i
    dsimp [y,v]
    ring
  · convert hsecond using 1
    congr 1
    funext i
    have hs := sibling_concentration_noise n d hd N i
    dsimp [y,v]
    linarith only [hs]

end HeritableCompositions
