import proofs.FiniteCopy.LocalSourceBounds

namespace FiniteCopy

noncomputable def countBox (N : ℕ) : Finset Counts := by
  classical
  exact Finset.univ.image (fun f : Fin 4 → Fin (35*N+1) => fun i => (f i).val)

theorem mem_countBox (N : ℕ) (n : Counts) :
    n ∈ countBox N ↔ ∀ i, n i ≤ 35*N := by
  classical
  constructor
  · intro hn
    obtain ⟨f,_,hf⟩ := Finset.mem_image.mp hn
    intro i
    have hi := (f i).isLt
    have he := congrFun hf i
    omega
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨fun i => ⟨n i,by have h := hn i; omega⟩,Finset.mem_univ _,?_⟩
    rfl

noncomputable def energyDomain (N : ℕ) (s : Point) (E : Point → ℝ) (b : ℝ) :
    Finset Counts := by
  classical
  exact (countBox N).filter (fun n => E (fun i => concentration N n i-s i) < b)

theorem small_energy_coordinates (E : Point → ℝ)
    (hE : ∀ y, (1/200)*normSq y ≤ E y) (y : Point)
    (hy : E y < 1/32000000) (i : Fin 4) : |y i| ≤ 1/400 := by
  have h := hE y
  have hi := coordinate_sq_le_normSq y i
  apply abs_le.mpr
  constructor <;> nlinarith only [h,hi,hy,sq_nonneg (y i+1/400),sq_nonneg (y i-1/400)]

theorem small_energy_in_countBox (N : ℕ) (hN : 1 ≤ N) (n : Counts)
    (s : Point) (hs : ∀ i, s i ≤ 34) (E : Point → ℝ)
    (hE : ∀ y, (1/200)*normSq y ≤ E y)
    (hy : E (fun i => concentration N n i-s i) < 1/32000000) : n ∈ countBox N := by
  apply (mem_countBox N n).mpr
  intro i
  have hi := (abs_le.mp (small_energy_coordinates E hE _ hy i)).2
  have hx : concentration N n i ≤ 35 := by linarith [hs i]
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : (n i : ℝ) ≤ 35*(N : ℝ) := (div_le_iff₀ hNr).mp hx
  exact_mod_cast hn

theorem mem_energyDomain (N : ℕ) (hN : 1 ≤ N) (n : Counts)
    (s : Point) (hs : ∀ i, s i ≤ 34) (E : Point → ℝ)
    (hE : ∀ y, (1/200)*normSq y ≤ E y) (b : ℝ) (hb : b ≤ 1/32000000) :
    n ∈ energyDomain N s E b ↔ E (fun i => concentration N n i-s i) < b := by
  classical
  rw [energyDomain,Finset.mem_filter]
  constructor
  · exact And.right
  · intro hn
    exact ⟨small_energy_in_countBox N hN n s hs E hE (hn.trans_le hb),hn⟩

end FiniteCopy

