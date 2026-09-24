import proofs.IrrRAFEnumeration.BipartiteBalanceObstruction

namespace IrrRAFEnumeration

def leftCliqueEdge {k : Nat} (i j : Fin k) : Finset (Bool × Fin k) :=
  {(false, i), (false, j)}

def leftCliqueFamily (k : Nat) : Finset (Finset (Bool × Fin k)) :=
  ((Finset.univ ×ˢ Finset.univ).filter fun ij => ij.1 ≠ ij.2).image
    fun ij => leftCliqueEdge ij.1 ij.2

def diagonalFamily (k : Nat) : Finset (Finset (Bool × Fin k)) :=
  Finset.univ.image fun i => bipEdge i i

def cliqueMatchingFamily (k : Nat) : Finset (Finset (Bool × Fin k)) :=
  leftCliqueFamily k ∪ diagonalFamily k

def leftSwap {k : Nat} (i : Fin k) : Finset (Bool × Fin k) :=
  insert (true, i) ((bipLeft k).erase (false, i))

def leftSwapFamily (k : Nat) : Finset (Finset (Bool × Fin k)) :=
  Finset.univ.image leftSwap

def cliqueMatchingBlocker (k : Nat) : Finset (Finset (Bool × Fin k)) :=
  insert (bipLeft k) (leftSwapFamily k)

theorem leftCliqueEdge_mem {k : Nat} (i j : Fin k) (hij : i ≠ j) :
    leftCliqueEdge i j ∈ leftCliqueFamily k := by
  apply Finset.mem_image.mpr
  exact ⟨(i, j), by simp [hij], rfl⟩

theorem diagonalEdge_mem {k : Nat} (i : Fin k) :
    bipEdge i i ∈ diagonalFamily k := by
  exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

@[simp] theorem mem_leftSwap_left {k : Nat} (i j : Fin k) :
    (false, j) ∈ leftSwap i ↔ j ≠ i := by
  simp [leftSwap]

@[simp] theorem mem_leftSwap_right {k : Nat} (i j : Fin k) :
    (true, j) ∈ leftSwap i ↔ j = i := by
  simp [leftSwap]

theorem bipLeft_hits_cliqueMatching {k : Nat} :
    Hits (cliqueMatchingFamily k) (bipLeft k) := by
  intro E hE
  simp only [cliqueMatchingFamily, Finset.mem_union] at hE
  rcases hE with hE | hE
  · obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp hE
    exact Finset.not_disjoint_iff.mpr
      ⟨(false, i), by simp, by simp [leftCliqueEdge]⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hE
    exact Finset.not_disjoint_iff.mpr
      ⟨(false, i), by simp, by simp [bipEdge]⟩

theorem leftSwap_hits_cliqueMatching {k : Nat} (i : Fin k) :
    Hits (cliqueMatchingFamily k) (leftSwap i) := by
  intro E hE
  simp only [cliqueMatchingFamily, Finset.mem_union] at hE
  rcases hE with hE | hE
  · obtain ⟨⟨j, l⟩, hjl, rfl⟩ := Finset.mem_image.mp hE
    have hne : j ≠ l := by simpa using (Finset.mem_filter.mp hjl).2
    by_cases hji : j = i
    · have hli : l ≠ i := by
        intro hli
        exact hne (hji.trans hli.symm)
      exact Finset.not_disjoint_iff.mpr
        ⟨(false, l), by simp [hli], by simp [leftCliqueEdge]⟩
    · exact Finset.not_disjoint_iff.mpr
        ⟨(false, j), by simp [hji], by simp [leftCliqueEdge]⟩
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hE
    by_cases hji : j = i
    · subst j
      exact Finset.not_disjoint_iff.mpr
        ⟨(true, i), by simp, by simp [bipEdge]⟩
    · exact Finset.not_disjoint_iff.mpr
        ⟨(false, j), by simp [hji], by simp [bipEdge]⟩

theorem bipLeft_minimal_cliqueMatching {k : Nat} :
    Minimal (Hits (cliqueMatchingFamily k)) (bipLeft k) := by
  refine ⟨bipLeft_hits_cliqueMatching, ?_⟩
  intro B hB hsub x hx
  have hxfalse : x.1 = false := (mem_bipLeft x).mp hx
  have hxrepr : x = (false, x.2) := by
    apply Prod.ext
    · exact hxfalse
    · rfl
  rw [hxrepr]
  have hhit := hB (bipEdge x.2 x.2)
    (by simp [cliqueMatchingFamily, diagonalEdge_mem])
  obtain ⟨y, hyB, hyEdge⟩ := Finset.not_disjoint_iff.mp hhit
  have hySub := hsub hyB
  simp only [bipEdge, Finset.mem_insert, Finset.mem_singleton] at hyEdge
  rcases hyEdge with rfl | rfl
  · exact hyB
  · simp at hySub

theorem leftSwap_minimal_cliqueMatching {k : Nat} (i : Fin k) :
    Minimal (Hits (cliqueMatchingFamily k)) (leftSwap i) := by
  refine ⟨leftSwap_hits_cliqueMatching i, ?_⟩
  intro B hB hsub x hx
  by_cases hxright : x = (true, i)
  · subst x
    have hhit := hB (bipEdge i i)
      (by simp [cliqueMatchingFamily, diagonalEdge_mem])
    obtain ⟨y, hyB, hyEdge⟩ := Finset.not_disjoint_iff.mp hhit
    simp only [bipEdge, Finset.mem_insert, Finset.mem_singleton] at hyEdge
    rcases hyEdge with rfl | rfl
    · have := hsub hyB
      simp at this
    · exact hyB
  · have hxErase : x ∈ (bipLeft k).erase (false, i) := by
      simpa [leftSwap, hxright] using hx
    have hxLeft : x ∈ bipLeft k := (Finset.mem_erase.mp hxErase).2
    have hxfalse : x.1 = false := (mem_bipLeft x).mp hxLeft
    have hxrepr : x = (false, x.2) := by
      apply Prod.ext
      · exact hxfalse
      · rfl
    rw [hxrepr]
    have hhit := hB (bipEdge x.2 x.2)
      (by simp [cliqueMatchingFamily, diagonalEdge_mem])
    obtain ⟨y, hyB, hyEdge⟩ := Finset.not_disjoint_iff.mp hhit
    have hySub := hsub hyB
    simp only [bipEdge, Finset.mem_insert, Finset.mem_singleton] at hyEdge
    rcases hyEdge with rfl | rfl
    · exact hyB
    · have heq : x.2 = i := by simpa using hySub
      have hxeq : x = (false, i) := hxrepr.trans (congrArg (fun j => (false, j)) heq)
      exact ((Finset.mem_erase.mp hxErase).1 hxeq).elim

theorem cliqueMatching_blocker_eq {k : Nat} :
    blocker (cliqueMatchingFamily k) = cliqueMatchingBlocker k := by
  classical
  ext T
  rw [mem_blocker]
  constructor
  · intro hT
    by_cases hall : bipLeft k ⊆ T
    · have hsub := hT.2 bipLeft_hits_cliqueMatching hall
      have hEq : T = bipLeft k := Finset.Subset.antisymm hsub hall
      simp [cliqueMatchingBlocker, hEq]
    · obtain ⟨x, hxLeft, hxT⟩ := Finset.not_subset.mp hall
      have hxfalse : x.1 = false := (mem_bipLeft x).mp hxLeft
      let i : Fin k := x.2
      have hxrepr : x = (false, i) := by
        apply Prod.ext
        · exact hxfalse
        · rfl
      have hswap : leftSwap i ⊆ T := by
        intro y hy
        by_cases hyright : y = (true, i)
        · subst y
          have hhit := hT.1 (bipEdge i i)
            (by simp [cliqueMatchingFamily, diagonalEdge_mem])
          obtain ⟨z, hzT, hzEdge⟩ := Finset.not_disjoint_iff.mp hhit
          simp only [bipEdge, Finset.mem_insert, Finset.mem_singleton] at hzEdge
          rcases hzEdge with rfl | rfl
          · exact (hxT (hxrepr.symm ▸ hzT)).elim
          · exact hzT
        · have hyErase : y ∈ (bipLeft k).erase (false, i) := by
            simpa [leftSwap, hyright] using hy
          have hyLeft := (Finset.mem_erase.mp hyErase).2
          have hyfalse : y.1 = false := (mem_bipLeft y).mp hyLeft
          have hyrepr : y = (false, y.2) := by
            apply Prod.ext
            · exact hyfalse
            · rfl
          have hne : y.2 ≠ i := by
            intro heq
            apply (Finset.mem_erase.mp hyErase).1
            rw [hyrepr, heq]
          have hhit := hT.1 (leftCliqueEdge i y.2)
            (by simp [cliqueMatchingFamily, leftCliqueEdge_mem i y.2 hne.symm])
          obtain ⟨z, hzT, hzEdge⟩ := Finset.not_disjoint_iff.mp hhit
          simp only [leftCliqueEdge, Finset.mem_insert,
            Finset.mem_singleton] at hzEdge
          rcases hzEdge with rfl | rfl
          · exact (hxT (hxrepr.symm ▸ hzT)).elim
          · exact hyrepr.symm ▸ hzT
      have hsub := hT.2 (leftSwap_hits_cliqueMatching i) hswap
      have hEq : T = leftSwap i := Finset.Subset.antisymm hsub hswap
      subst T
      simp [cliqueMatchingBlocker, leftSwapFamily]
  · intro hT
    simp only [cliqueMatchingBlocker, Finset.mem_insert] at hT
    rcases hT with rfl | hT
    · exact bipLeft_minimal_cliqueMatching
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hT
      exact leftSwap_minimal_cliqueMatching i

/-- The all-left transversal has pairwise disjoint singleton repairs. -/
theorem cliqueMatching_private_repair {k : Nat} (i : Fin k) :
    bipEdge i i ∈ cliqueMatchingFamily k ∧
      bipEdge i i ∩ bipLeft k = {(false, i)} ∧
      bipEdge i i \ bipLeft k = {(true, i)} := by
  refine ⟨by simp [cliqueMatchingFamily, diagonalEdge_mem],
    (bipDiagonal_private_repair i).2.1, ?_⟩
  ext x
  rcases x with ⟨b, j⟩
  cases b <;> simp [bipEdge]

theorem leftSwap_injective {k : Nat} :
    Function.Injective (leftSwap (k := k)) := by
  intro i j hij
  have hi := Finset.ext_iff.mp hij (true, i)
  simpa using hi

theorem leftSwapFamily_card (k : Nat) :
    (leftSwapFamily k).card = k := by
  classical
  rw [leftSwapFamily,
    Finset.card_image_iff.mpr fun i _ j _ h => leftSwap_injective h]
  simp

theorem cliqueMatchingBlocker_card (k : Nat) :
    (cliqueMatchingBlocker k).card = k + 1 := by
  classical
  have hnot : bipLeft k ∉ leftSwapFamily k := by
    intro hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    have hright : (true, i) ∈ leftSwap i := by simp
    rw [hi] at hright
    simp at hright
  simp [cliqueMatchingBlocker, hnot, leftSwapFamily_card]

theorem cliqueMatching_blocker_card (k : Nat) :
    (blocker (cliqueMatchingFamily k)).card = k + 1 := by
  rw [cliqueMatching_blocker_eq, cliqueMatchingBlocker_card]

theorem cliqueMatchingFamily_card_le (k : Nat) :
    (cliqueMatchingFamily k).card ≤ k * k + k := by
  classical
  have hclique : (leftCliqueFamily k).card ≤ k * k := by
    rw [leftCliqueFamily]
    calc
      ((Finset.filter (fun ij : Fin k × Fin k => ij.1 ≠ ij.2)
          (Finset.univ ×ˢ Finset.univ)).image
          fun ij => leftCliqueEdge ij.1 ij.2).card ≤
          (Finset.filter (fun ij : Fin k × Fin k => ij.1 ≠ ij.2)
            (Finset.univ ×ˢ Finset.univ)).card := Finset.card_image_le
      _ ≤ (Finset.univ ×ˢ (Finset.univ : Finset (Fin k))).card :=
        Finset.card_filter_le _ _
      _ = k * k := by simp
  have hdiag : (diagonalFamily k).card ≤ k := by
    rw [diagonalFamily]
    simpa using (Finset.card_image_le :
      (Finset.univ.image fun i : Fin k => bipEdge i i).card ≤ Finset.univ.card)
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hclique hdiag)

/-- Any set meeting every private repair singleton contains the whole right
shore, so the private-repair cover number is exactly `k`. -/
theorem bipRight_subset_of_hits_private_repairs {k : Nat}
    (C : Finset (Bool × Fin k))
    (hC : ∀ i : Fin k, ¬ Disjoint C (bipEdge i i \ bipLeft k)) :
    bipRight k ⊆ C := by
  intro x hx
  have hxtrue : x.1 = true := (mem_bipRight x).mp hx
  have hxrepr : x = (true, x.2) := by
    apply Prod.ext
    · exact hxtrue
    · rfl
  obtain ⟨y, hyC, hyRepair⟩ := Finset.not_disjoint_iff.mp (hC x.2)
  rw [(cliqueMatching_private_repair x.2).2.2] at hyRepair
  have hyEq : y = (true, x.2) := by simpa using hyRepair
  rw [hyEq] at hyC
  rw [hxrepr]
  exact hyC

theorem bipRight_card (k : Nat) : (bipRight k).card = k := by
  classical
  rw [bipRight, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    exact congrArg Prod.snd hij

end IrrRAFEnumeration
