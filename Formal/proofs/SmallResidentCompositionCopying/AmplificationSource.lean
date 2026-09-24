import proofs.CompositionalMemory.FiniteKilledEventBudget

namespace SmallResidentCompositionCopying.Amplification
open FiniteCopy CompositionalMemory
noncomputable section

abbrev Counts := Fin 20 × Fin 20
abbrev State := Option Counts

def up (a : Fin 20) : Fin 20 := ⟨min (a.val+1) 19, by omega⟩
def down (a : Fin 20) : Fin 20 := ⟨a.val-1, by omega⟩

def factor (b : Fin 20) : ℝ := 1+((b.val:ℝ)+1)/10
def birth (a b : Fin 20) : ℝ := if a.val < 19 then 1000*((a.val:ℝ)+1)*factor b else 0
def death (a b : Fin 20) : ℝ := if a.val < 19 then ((a.val:ℝ)+1)*(a.val:ℝ)*factor b else 0

theorem factor_bounds (b : Fin 20) : 1 ≤ factor b ∧ factor b ≤ 3 := by
  have h : (b.val:ℝ) ≤ 19 := by exact_mod_cast (show b.val ≤ 19 by omega)
  have h' : (0:ℝ) ≤ b.val := Nat.cast_nonneg _
  dsimp [factor]
  constructor <;> linarith

def model : FiniteJumpModel State (Fin 4) where
  next s r := s.map fun z =>
    if r=0 then (up z.1,z.2) else if r=1 then (down z.1,z.2)
    else if r=2 then (z.1,up z.2) else (z.1,down z.2)
  rate s r := s.elim 0 fun z =>
    if r=0 then birth z.1 z.2 else if r=1 then death z.1 z.2
    else if r=2 then birth z.2 z.1 else death z.2 z.1
  nonneg s r := by
    cases s with
    | none => exact le_rfl
    | some z =>
      simp only [Option.elim]
      have h₁ := (factor_bounds z.1).1
      have h₂ := (factor_bounds z.2).1
      split_ifs <;> simp only [birth,death] <;> split_ifs <;> positivity

def remaining : State → ℝ
  | none => 0
  | some z => 38-(z.1.val:ℝ)-(z.2.val:ℝ)

theorem remaining_bounds (z : Counts) : 0 ≤ remaining (some z) ∧ remaining (some z) ≤ 38 := by
  have ha : (z.1.val:ℝ) ≤ 19 := by exact_mod_cast (show z.1.val ≤ 19 by omega)
  have hb : (z.2.val:ℝ) ≤ 19 := by exact_mod_cast (show z.2.val ≤ 19 by omega)
  have ha' : (0:ℝ) ≤ z.1.val := Nat.cast_nonneg _
  have hb' : (0:ℝ) ≤ z.2.val := Nat.cast_nonneg _
  dsimp [remaining]
  constructor <;> linarith

theorem local_drift (a b : Fin 20) :
    birth a b * ((a.val:ℝ)-(up a).val) +
      death a b * ((a.val:ℝ)-(down a).val) ≤ -50*(19-(a.val:ℝ)) := by
  have ha := a.isLt
  have hf := factor_bounds b
  generalize hn : a.val = n at *
  interval_cases n <;> norm_num [birth,death,up,down,hn] <;> nlinarith

theorem generator_remaining (s : State) :
    model.generator remaining s ≤ -50*remaining s := by
  cases s with
  | none => simp [FiniteJumpModel.generator,model,remaining]
  | some z =>
    have h₁ := local_drift z.1 z.2
    have h₂ := local_drift z.2 z.1
    simp [FiniteJumpModel.generator,model,Fin.sum_univ_succ,remaining]
    linarith

theorem local_total (a b : Fin 20) : birth a b + death a b ≤ 60000 := by
  have ha := a.isLt
  have hf := factor_bounds b
  generalize hn : a.val = n at *
  interval_cases n <;> norm_num [birth,death,hn] <;> nlinarith

theorem rate_bound (s : State) : model.total s ≤ 120000 := by
  cases s with
  | none => norm_num [FiniteJumpModel.total,model]
  | some z =>
    have h₁ := local_total z.1 z.2
    have h₂ := local_total z.2 z.1
    simp [FiniteJumpModel.total,model,Fin.sum_univ_succ]
    linarith

end
end SmallResidentCompositionCopying.Amplification
