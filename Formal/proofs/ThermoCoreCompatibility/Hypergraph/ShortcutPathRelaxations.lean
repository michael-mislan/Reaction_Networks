import proofs.ThermoCoreCompatibility.Hypergraph.ShortcutPathSource
import proofs.ThermoCoreCompatibility.Toric

namespace ThermoCoreCompatibility.Hypergraph.Shortcut

noncomputable def delta (L : ℕ) : ℝ := 1/(1000*((L:ℝ)-1))
noncomputable def activity (L : ℕ) (i : Fin (L+1)) : ℝ :=
  if i.val=0 then 19/20 else 941/1000-((i.val:ℝ)-1)*delta L
noncomputable def doubled (L : ℕ) (i : Fin (L+1)) : ℝ :=
  if i.val=0 then 467/500 else activity L i-(7/4)*delta L

theorem delta_facts (L : ℕ) (hL : 2 ≤ L) :
    0 < delta L ∧ delta L ≤ 1/1000 ∧ ((L:ℝ)-1)*delta L=1/1000 := by
  have hl : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hd : 0 < 1000*((L:ℝ)-1) := by linarith
  have he : (1000*((L:ℝ)-1))*delta L=1 := by
    unfold delta
    exact mul_one_div_cancel (ne_of_gt hd)
  exact ⟨by unfold delta; positivity,by nlinarith,by nlinarith⟩

theorem activity_bounds (L : ℕ) (hL : 2 ≤ L) (i : Fin (L+1)) :
    47/50 ≤ activity L i ∧ activity L i ≤ 19/20 := by
  obtain ⟨hd,_,he⟩ := delta_facts L hL
  have hi : (i.val:ℝ) ≤ L := by exact_mod_cast (show i.val ≤ L by omega)
  unfold activity
  split_ifs with hh
  · norm_num
  · have hi' : (1:ℝ) ≤ i.val := by exact_mod_cast (show 1 ≤ i.val by omega)
    constructor <;> nlinarith

theorem activity_last (L : ℕ) (hL : 2 ≤ L) :
    activity L ⟨L,by omega⟩ = 47/50 := by
  have he := (delta_facts L hL).2.2
  simp only [activity,show L ≠ 0 by omega,if_false]
  linarith

theorem activity_step (L : ℕ) (i : Fin (L+1)) (hi : i.val < L) (hz : i.val ≠ 0) :
    activity L i-activity L ⟨i.val+1,by omega⟩=delta L := by
  simp [activity,hz,Nat.cast_add,Nat.cast_one]
  ring

/-- One global singleton/doubled-complex assignment, with induced box bounds. -/
theorem scalar_relaxations (L : ℕ) (hL : 2 ≤ L) :
    (∀ i, 9/10 ≤ activity L i ∧ activity L i ≤ 1) ∧
    (∀ i, 81/100 ≤ doubled L i ∧ doubled L i ≤ 1) ∧
    ∀ e, let s := (assembly L hL).src e; let t := (assembly L hL).dst e
      activity L t < activity L s ∧ activity L s^2 < activity L t ∧
      0 < activity L t-doubled L s ∧
      activity L s-activity L t < 2*(activity L t-doubled L s) ∧
      activity L t-doubled L s < activity L s-activity L t := by
  obtain ⟨hd,hdu,hde⟩ := delta_facts L hL
  refine ⟨?_,?_,?_⟩
  · intro i; obtain ⟨hl,hu⟩ := activity_bounds L hL i; constructor <;> linarith
  · intro i; obtain ⟨hl,hu⟩ := activity_bounds L hL i
    unfold doubled; split_ifs <;> constructor <;> linarith
  · intro e
    dsimp only
    have hs := activity_bounds L hL ((assembly L hL).src e)
    have ht := activity_bounds L hL ((assembly L hL).dst e)
    have hsq : activity L ((assembly L hL).src e)^2 < activity L ((assembly L hL).dst e) := by
      have hp := mul_nonneg (show 0 ≤ 19/20-activity L ((assembly L hL).src e) by linarith)
        (show 0 ≤ 19/20+activity L ((assembly L hL).src e) by linarith)
      nlinarith
    refine ⟨?_,hsq,?_,?_,?_⟩ <;>
      simp only [assembly] <;> split_ifs with he
    all_goals
      solve
      | (simp [activity,doubled,show L ≠ 0 by omega,hde]
         norm_num)
      | (by_cases hz : e.val=0
         · simp [activity,doubled,hz]
           norm_num
         · have hh := activity_step L e he hz
           try simp only [doubled,hz,if_false]
           linarith)

end ThermoCoreCompatibility.Hypergraph.Shortcut
