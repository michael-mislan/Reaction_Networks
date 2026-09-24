import proofs.MinRAFApprox.Irreducible

namespace MinRAFApprox.SetCoverSource

open RAF MinRAFApprox.Reaction

/-- Set `0` is universal; set `i+1` is the singleton containing `i`. -/
def universalSingletonInstance (q : Nat) :
    MinRAFApprox.SetCoverInstance (Fin q) (Fin (q + 1)) where
  sets j :=
    if hj : j.val = 0 then Finset.univ
    else {⟨j.val - 1, by omega⟩}
  coverable i := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp

def universalCover (q : Nat) : Finset (Fin (q + 1)) := {⟨0, by omega⟩}

def singletonCover (q : Nat) : Finset (Fin (q + 1)) :=
  Finset.univ.erase ⟨0, by omega⟩

theorem universalCover_minimal (hq : 0 < q) :
    InclusionMinimalCover (universalSingletonInstance q) (universalCover q) := by
  constructor
  · intro i
    exact ⟨⟨0, by omega⟩, by simp [universalCover], by simp [universalSingletonInstance]⟩
  · intro D hD hsub j hj
    let hzero : Fin q := ⟨0, hq⟩
    obtain ⟨k, hkD, _hkset⟩ := hD hzero
    have hk0 : k = ⟨0, by omega⟩ := by
      have := hsub hkD
      simpa [universalCover] using this
    subst k
    have hj0 : j = ⟨0, by omega⟩ := by simpa [universalCover] using hj
    simpa [hj0] using hkD

theorem singletonCover_covers (q : Nat) :
    (universalSingletonInstance q).Covers (singletonCover q) := by
  intro i
  let j : Fin (q + 1) := ⟨i.val + 1, by omega⟩
  refine ⟨j, ?_, ?_⟩
  · simp [singletonCover, j]
  · simp [universalSingletonInstance, j]

theorem singletonCover_minimal (hq : 0 < q) :
    InclusionMinimalCover (universalSingletonInstance q) (singletonCover q) := by
  refine ⟨singletonCover_covers q, ?_⟩
  intro D hD hsub j hj
  have hjne : j.val ≠ 0 := by
    simpa [singletonCover] using hj
  let i : Fin q := ⟨j.val - 1, by omega⟩
  obtain ⟨k, hkD, hik⟩ := hD i
  have hkbad := hsub hkD
  have hkne : k.val ≠ 0 := by
    simpa [singletonCover] using hkbad
  have hkne' : k ≠ (0 : Fin (q + 1)) := by
    intro hk
    apply hkne
    simp [hk]
  have hik' : i = (⟨k.val - 1, by omega⟩ : Fin q) := by
    simpa [universalSingletonInstance, hkne, hkne'] using hik
  have hki : k.val - 1 = i.val := by
    exact (congrArg Fin.val hik').symm
  have hkj : k = j := by
    apply Fin.ext
    dsimp [i] at hki
    omega
  simpa [hkj] using hkD

@[simp] theorem universalCover_card (q : Nat) :
    (universalCover q).card = 1 := by simp [universalCover]

@[simp] theorem singletonCover_card (q : Nat) :
    (singletonCover q).card = q := by
  rw [singletonCover, Finset.card_erase_of_mem]
  · simp
  · simp

/-- Irreducible RAFs have no universal size ratio: for every factor `c`, one
literal source contains a small and a large iRAF whose sizes differ by more
than `c`. -/
theorem irreducibleRAF_size_ratio_unbounded (c : Nat) :
    let q := 2 * c + 2
    let I := universalSingletonInstance q
    let small := MinRAFApprox.canonicalRAF
      (U := Fin q) (K := Fin q) (universalCover q)
    let large := MinRAFApprox.canonicalRAF
      (U := Fin q) (K := Fin q) (singletonCover q)
    IsIrreducibleRAF (crs q (q + 1) q) (catalysis I) small ∧
      IsIrreducibleRAF (crs q (q + 1) q) (catalysis I) large ∧
      c * small.card < large.card := by
  dsimp
  let q := 2 * c + 2
  have hq : 0 < q := by dsimp [q]; omega
  have hsmall :=
    (irreducibleRAF_iff_inclusionMinimalCover
      (universalSingletonInstance q) hq hq (universalCover q)).2
      (universalCover_minimal hq)
  have hlarge :=
    (irreducibleRAF_iff_inclusionMinimalCover
      (universalSingletonInstance q) hq hq (singletonCover q)).2
      (singletonCover_minimal hq)
  refine ⟨hsmall, hlarge, ?_⟩
  rw [canonicalRAF_card, canonicalRAF_card]
  simp only [universalCover_card, singletonCover_card]
  nlinarith

end MinRAFApprox.SetCoverSource
