import proofs.IrrRAFEnumeration.CountPostlude

namespace IrrRAFEnumeration.PlacedCountPostlude
open Complexity Complexity.TM HeaderComparison ExpectedBaseline CountPostlude

def placedPostlude (n : Nat) : TM (n+3) := placeWorkTM n 0 postludeTM

theorem placed_postlude_correct (n length actual : Nat) (success : Bool)
    (inp out : Tape) (work : Fin (n+3) → Tape)
    (hi : Parked inp) (hw : ∀ i, Parked (work i)) (ho : Parked out)
    (hInv : out.StartInvariant)
    (hlen : work (placeWorkIdx n 0 (0 : Fin 3)) = regTape length)
    (hclock : (work (placeWorkIdx n 0 (2 : Fin 3))).read = Γ.ofBool success)
    (hO : success = true → UnaryPrefix (parkOutput out) actual Γ.zero) :
    ∃ c t, t ≤ 3*out.head+6*length+25 ∧
      (placedPostlude n).reachesIn t ⟨(placedPostlude n).qstart,inp,work,out⟩ c ∧
      (placedPostlude n).halted c ∧
      c.output.cells 1 = Γ.ofBool (!(success && decide (actual = length+2))) := by
  let flag := work (placeWorkIdx n 0 (1 : Fin 3))
  let clock := work (placeWorkIdx n 0 (2 : Fin 3))
  obtain ⟨c,t,ht,hr,hh,hv⟩ := postlude_correct length actual success inp flag clock out
    hi (hw _) (hw _) ho hInv hclock hO
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal postludeTM n 0 work hr
    (fun i _ => (hw i).read_ne_start)
  have hl : ∀ j : Fin 3, work (placeWorkIdx n 0 j) = baselineWork length flag clock j := by
    intro j
    fin_cases j
    · exact hlen
    · rfl
    · rfl
  have heq : placeWorkCfg postludeTM n 0 work
      ⟨postludeTM.qstart,inp,baselineWork length flag clock,out⟩ =
      (⟨(placedPostlude n).qstart,inp,work,out⟩ : Cfg (n+3) (placedPostlude n).Q) := by
    refine Cfg.ext rfl rfl ?_ rfl
    funext i
    simp only [placeWorkCfg]
    split
    · rename_i hm
      rw [← hl,placeWorkIdx_placeWorkCoord i hm]
    · rfl
  rw [heq] at hp
  exact ⟨_,t,ht,hp,hh,hv⟩

end IrrRAFEnumeration.PlacedCountPostlude
