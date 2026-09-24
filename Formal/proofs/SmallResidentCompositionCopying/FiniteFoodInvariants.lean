import proofs.SmallResidentCompositionCopying.FiniteFoodSource

namespace SmallResidentCompositionCopying.FiniteFood
noncomputable section

def molecularNext (v : Fin 2 → Bool → ℕ) (r : Fin 4) (s : Bool) (i : Fin 2) (b : Bool) : ℕ :=
  if i=target r ∧ b=s then if r=0 ∨ r=2 then v i b+1 else v i b-1 else v i b

theorem literal_next (p : Rates) {K : ℕ} (word : Word) (z : Counts K)
    (r : Fin 4) (s : Bool) (c : Option Bool)
    (h : 0<literalRate p (resident word z) (food z) r s c) (i : Fin 2) (b : Bool) :
    resident word ((model p K).next z r) i b=molecularNext (resident word z) r s i b := by
  have hw : word (target r)=s := by
    by_contra hn
    simp [literalRate,literalBase,resident,hn] at h
  have ha : r=0 ∨ r=2 → (count z (target r)).val<K-1 := by
    intro hr
    by_contra hn
    have hz : food z (target r)=0 := by dsimp [food]; omega
    simp [literalRate,literalBase,hr,hz] at h
  have hd : ¬(r=0 ∨ r=2) → 0<(count z (target r)).val := by
    intro hr
    by_contra hn
    have hz : (count z (target r)).val=0 := by omega
    simp [literalRate,literalBase,hr,resident,hw,hz] at h
  have h0 := z.1.isLt
  have h1 := z.2.isLt
  clear h c
  fin_cases r <;> norm_num [target,count,Fin.ext_iff] at hw ha hd
  all_goals
    fin_cases i <;> cases s <;> cases b <;>
      simp [resident,count,target,molecularNext,model,up,down,hw] <;> omega

theorem food_transition (p : Rates) {K : ℕ} (word : Word) (z : Counts K)
    (r : Fin 4) (s : Bool) (c : Option Bool)
    (h : 0<literalRate p (resident word z) (food z) r s c) :
    (count ((model p K).next z r) (target r)).val+1+
      food ((model p K).next z r) (target r)=K ∧
    resident word ((model p K).next z r) (target r) s=
      (if r=0 ∨ r=2 then resident word z (target r) s+1
       else resident word z (target r) s-1) := by
  constructor
  · exact conserved _ _
  · simpa only [molecularNext,eq_self, and_self,ite_true] using literal_next p word z r s c h (target r) s

theorem absent_stays_absent {K : ℕ} (word : Word) (z : Counts K) (i : Fin 2) (s : Bool)
    (h : word i≠s) : resident word z i s=0 := by simp [resident,h]

theorem resident_never_zero {K : ℕ} (word : Word) (z : Counts K) (i : Fin 2) :
    1≤resident word z i (word i) := by simp [resident]

end
end SmallResidentCompositionCopying.FiniteFood
