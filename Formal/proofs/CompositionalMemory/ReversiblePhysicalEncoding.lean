import proofs.CompositionalMemory.ReversiblePhysicalSource

namespace CompositionalMemory
open FiniteCopy

theorem reversiblePhysical_first_next (N : Nat) (s : CoupledLiveState N)
    (k : Fin 2) (r : Fin 13) :
    reversiblePhysicalClip N (reversiblePhysicalReactionNext N (reversiblePhysicalEmbed N s)
      (k,r.castSucc))=reversibleNext N (some s) (k,r) := by
  simp only [reversiblePhysicalEmbed,reversiblePhysicalReactionNext,Fin.val_castSucc,
    r.isLt,dif_pos,reversiblePhysicalClip]
  exact reversibleCountReactionNext_embed N s (k,r)

theorem reversiblePhysical_first_rate (N : Nat) (hN : 0 < N) (ε ρ : ℝ)
    (s : CoupledLiveState N) (k : Fin 2) (r : Fin 13) :
    reversiblePhysicalReactionRate N ε ρ (reversiblePhysicalEmbed N s) (k,r.castSucc)=
      reversibleRate N ε (some s) (k,r) := by
  rcases s with ⟨j,a⟩
  have hx (i : Fin 2) : ¬((a i).1.val : Int)<0 := not_lt_of_ge (Int.natCast_nonneg _)
  have hy (i : Fin 2) : ¬((a i).2.val : Int)<0 := not_lt_of_ge (Int.natCast_nonneg _)
  have hn : N≠0 := Nat.ne_of_gt hN
  have he : N+j.val=2*N ↔ j.val=N := by omega
  by_cases hj : j.val=N
  · simp [reversiblePhysicalReactionRate,reversibleRawRate,reversiblePhysicalCounts,
      reversiblePhysicalEmbed,coupledCountEmbed,reversibleRate,hj,two_mul]
  · fin_cases r <;>
      norm_num [reversiblePhysicalReactionRate,reversibleRawRate,reversiblePhysicalCounts,
        reversiblePhysicalEmbed,coupledCountEmbed,reversibleRate,hj,hn,he,hx,hy,Nat.cast_add]

theorem reversiblePhysical_reverse_rate (N : Nat) (hN : 0 < N) (ε ρ : ℝ)
    (s : CoupledLiveState N) (k : Fin 2) :
    reversiblePhysicalReactionRate N ε ρ (reversiblePhysicalEmbed N s) (k,Fin.last 13)=
      if s.1.val=N then 0 else ρ*((N : ℝ)+s.1.val) := by
  rcases s with ⟨j,a⟩
  have hx (i : Fin 2) : ¬((a i).1.val : Int)<0 := not_lt_of_ge (Int.natCast_nonneg _)
  have hy (i : Fin 2) : ¬((a i).2.val : Int)<0 := not_lt_of_ge (Int.natCast_nonneg _)
  have hn : N≠0 := Nat.ne_of_gt hN
  have he : N+j.val=2*N ↔ j.val=N := by omega
  simp [reversiblePhysicalReactionRate,reversibleRawRate,reversiblePhysicalCounts,
    reversiblePhysicalEmbed,coupledCountEmbed,hn,he,hx,hy,Nat.cast_add]

theorem reversiblePhysical_reverse_next (N : Nat) (s : CoupledLiveState N)
    (hs : s.1.val≠N) (k : Fin 2) :
    reversiblePhysicalClip N (reversiblePhysicalReactionNext N (reversiblePhysicalEmbed N s)
      (k,Fin.last 13))=none := by
  rcases s with ⟨j,a⟩
  simp [reversiblePhysicalReactionNext,reversiblePhysicalEmbed,coupledCountEmbed,
    reversiblePhysicalClip,hs]

theorem reversiblePhysical_encoded_generator (N : Nat) (hN : 0 < N) (ε ρ : ℝ)
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (f : CoupledFiniteState N → ℝ) (s : CoupledFiniteState N) :
    (reversiblePhysicalEncodedModel N ε ρ hε hρ).generator f s=
      (reversibleMonitoredModel N ε ρ hε hρ).generator f s := by
  rw [reversibleMonitoredModel,withExtraExit_generator]
  cases s with
  | none =>
    simp [FiniteJumpModel.generator,reversiblePhysicalEncodedModel,encodedFiniteModel,
      reversibleFiniteModel,reversibleRate,reversibleReverseHazard]
  | some s =>
    have hsum (k : Fin 2) :
        (∑ r : Fin 14,reversiblePhysicalReactionRate N ε ρ (reversiblePhysicalEmbed N s) (k,r)*
          (f (reversiblePhysicalClip N (reversiblePhysicalReactionNext N
            (reversiblePhysicalEmbed N s) (k,r)))-f (some s)))=
        (∑ r : Fin 13,reversibleRate N ε (some s) (k,r)*
          (f (reversibleNext N (some s) (k,r))-f (some s)))+
        (if s.1.val=N then 0 else ρ*((N : ℝ)+s.1.val)*(f none-f (some s))) := by
      rw [Fin.sum_univ_castSucc]
      simp_rw [reversiblePhysical_first_rate N hN ε ρ s k,
        reversiblePhysical_first_next,reversiblePhysical_reverse_rate N hN]
      by_cases hs : s.1.val=N
      · simp [hs]
      · rw [if_neg hs,reversiblePhysical_reverse_next N s hs k,if_neg hs]
    simp only [FiniteJumpModel.generator,reversiblePhysicalEncodedModel,encodedFiniteModel,
      Fintype.sum_option,reversiblePhysicalRate,reversiblePhysicalNext,reversiblePhysical_clip_embed,
      sub_self,mul_zero,zero_add,Fintype.sum_prod_type]
    simp_rw [hsum]
    simp only [reversibleFiniteModel,Finset.sum_add_distrib]
    rcases s with ⟨j,a⟩
    by_cases hj : j.val=N
    · simp [reversibleReverseHazard,hj,Fin.sum_univ_two]
    · simp [reversibleReverseHazard,hj,Fin.sum_univ_two]
      ring

end CompositionalMemory
