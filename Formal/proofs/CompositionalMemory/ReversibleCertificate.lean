import proofs.CompositionalMemory.ReversibleLineageLaw
import proofs.CompositionalMemory.ReversibleEncoding
import proofs.CompositionalMemory.ReversibleLayer53
import proofs.CompositionalMemory.ReversibleLayer54
import proofs.CompositionalMemory.ReversibleLayer55
import proofs.CompositionalMemory.ReversibleLayer56
import proofs.CompositionalMemory.ReversibleLayer57
import proofs.CompositionalMemory.ReversibleLayer58
import proofs.CompositionalMemory.ReversibleLayer59
import proofs.CompositionalMemory.ReversibleLayer60
import proofs.CompositionalMemory.ReversibleLayer61
import proofs.CompositionalMemory.ReversibleLayer62
import proofs.CompositionalMemory.ReversibleLayer63
import proofs.CompositionalMemory.ReversibleLayer64
import proofs.CompositionalMemory.ReversibleLayer65
import proofs.CompositionalMemory.ReversibleLayer66
import proofs.CompositionalMemory.ReversibleLayer67
import proofs.CompositionalMemory.ReversibleLayer68
import proofs.CompositionalMemory.ReversibleLayer69
import proofs.CompositionalMemory.ReversibleLayer70
import proofs.CompositionalMemory.ReversibleLayer71
import proofs.CompositionalMemory.ReversibleLayer72
import proofs.CompositionalMemory.ReversibleLayer73
import proofs.CompositionalMemory.ReversibleLayer74
import proofs.CompositionalMemory.ReversibleLayer75
import proofs.CompositionalMemory.ReversibleLayer76
import proofs.CompositionalMemory.ReversibleLayer77
import proofs.CompositionalMemory.ReversibleLayer78
import proofs.CompositionalMemory.ReversibleLayer79
import proofs.CompositionalMemory.ReversibleLayer80
import proofs.CompositionalMemory.ReversibleLayer81
import proofs.CompositionalMemory.ReversibleLayer82
import proofs.CompositionalMemory.ReversibleLayer83
import proofs.CompositionalMemory.ReversibleLayer84
import proofs.CompositionalMemory.ReversibleLayer85
import proofs.CompositionalMemory.ReversibleLayer86
import proofs.CompositionalMemory.ReversibleLayer87
import proofs.CompositionalMemory.ReversibleLayer88
import proofs.CompositionalMemory.ReversibleLayer89
import proofs.CompositionalMemory.ReversibleLayer90
import proofs.CompositionalMemory.ReversibleLayer91
import proofs.CompositionalMemory.ReversibleLayer92
import proofs.CompositionalMemory.ReversibleLayer93
import proofs.CompositionalMemory.ReversibleLayer94
import proofs.CompositionalMemory.ReversibleLayer95
import proofs.CompositionalMemory.ReversibleLayer96
import proofs.CompositionalMemory.ReversibleLayer97
import proofs.CompositionalMemory.ReversibleLayer98
import proofs.CompositionalMemory.ReversibleLayer99
import proofs.CompositionalMemory.ReversibleLayer100
import proofs.CompositionalMemory.ReversibleLayer101
import proofs.CompositionalMemory.ReversibleLayer102
import proofs.CompositionalMemory.ReversibleLayer103
import proofs.CompositionalMemory.ReversibleLayer104
import proofs.CompositionalMemory.ReversibleLayer105
import proofs.CompositionalMemory.ReversibleTerminal

namespace CompositionalMemory.ReversibleCertificate
open ControlledRows
open scoped ENNReal
set_option maxHeartbeats 180000
set_option profiler true

def data : Nat → Array Int
  | 53 => ReversibleLayer53.current
  | 54 => ReversibleLayer54.current
  | 55 => ReversibleLayer55.current
  | 56 => ReversibleLayer56.current
  | 57 => ReversibleLayer57.current
  | 58 => ReversibleLayer58.current
  | 59 => ReversibleLayer59.current
  | 60 => ReversibleLayer60.current
  | 61 => ReversibleLayer61.current
  | 62 => ReversibleLayer62.current
  | 63 => ReversibleLayer63.current
  | 64 => ReversibleLayer64.current
  | 65 => ReversibleLayer65.current
  | 66 => ReversibleLayer66.current
  | 67 => ReversibleLayer67.current
  | 68 => ReversibleLayer68.current
  | 69 => ReversibleLayer69.current
  | 70 => ReversibleLayer70.current
  | 71 => ReversibleLayer71.current
  | 72 => ReversibleLayer72.current
  | 73 => ReversibleLayer73.current
  | 74 => ReversibleLayer74.current
  | 75 => ReversibleLayer75.current
  | 76 => ReversibleLayer76.current
  | 77 => ReversibleLayer77.current
  | 78 => ReversibleLayer78.current
  | 79 => ReversibleLayer79.current
  | 80 => ReversibleLayer80.current
  | 81 => ReversibleLayer81.current
  | 82 => ReversibleLayer82.current
  | 83 => ReversibleLayer83.current
  | 84 => ReversibleLayer84.current
  | 85 => ReversibleLayer85.current
  | 86 => ReversibleLayer86.current
  | 87 => ReversibleLayer87.current
  | 88 => ReversibleLayer88.current
  | 89 => ReversibleLayer89.current
  | 90 => ReversibleLayer90.current
  | 91 => ReversibleLayer91.current
  | 92 => ReversibleLayer92.current
  | 93 => ReversibleLayer93.current
  | 94 => ReversibleLayer94.current
  | 95 => ReversibleLayer95.current
  | 96 => ReversibleLayer96.current
  | 97 => ReversibleLayer97.current
  | 98 => ReversibleLayer98.current
  | 99 => ReversibleLayer99.current
  | 100 => ReversibleLayer100.current
  | 101 => ReversibleLayer101.current
  | 102 => ReversibleLayer102.current
  | 103 => ReversibleLayer103.current
  | 104 => ReversibleLayer104.current
  | 105 => ReversibleLayer105.current
  | 106 => ReversibleTerminal.current
  | _ => #[]

theorem all_rows (m : Nat) (hm : 53 ≤ m) (hM : m < 106) :
    ReversibleRows.checkLayer m (data m) (data (m+1))=true := by
  interval_cases m
  · change ReversibleRows.checkLayer 53 ReversibleLayer53.current ReversibleLayer53.following=true
    exact ReversibleLayer53.rows_checked
  · change ReversibleRows.checkLayer 54 ReversibleLayer54.current ReversibleLayer54.following=true
    exact ReversibleLayer54.rows_checked
  · change ReversibleRows.checkLayer 55 ReversibleLayer55.current ReversibleLayer55.following=true
    exact ReversibleLayer55.rows_checked
  · change ReversibleRows.checkLayer 56 ReversibleLayer56.current ReversibleLayer56.following=true
    exact ReversibleLayer56.rows_checked
  · change ReversibleRows.checkLayer 57 ReversibleLayer57.current ReversibleLayer57.following=true
    exact ReversibleLayer57.rows_checked
  · change ReversibleRows.checkLayer 58 ReversibleLayer58.current ReversibleLayer58.following=true
    exact ReversibleLayer58.rows_checked
  · change ReversibleRows.checkLayer 59 ReversibleLayer59.current ReversibleLayer59.following=true
    exact ReversibleLayer59.rows_checked
  · change ReversibleRows.checkLayer 60 ReversibleLayer60.current ReversibleLayer60.following=true
    exact ReversibleLayer60.rows_checked
  · change ReversibleRows.checkLayer 61 ReversibleLayer61.current ReversibleLayer61.following=true
    exact ReversibleLayer61.rows_checked
  · change ReversibleRows.checkLayer 62 ReversibleLayer62.current ReversibleLayer62.following=true
    exact ReversibleLayer62.rows_checked
  · change ReversibleRows.checkLayer 63 ReversibleLayer63.current ReversibleLayer63.following=true
    exact ReversibleLayer63.rows_checked
  · change ReversibleRows.checkLayer 64 ReversibleLayer64.current ReversibleLayer64.following=true
    exact ReversibleLayer64.rows_checked
  · change ReversibleRows.checkLayer 65 ReversibleLayer65.current ReversibleLayer65.following=true
    exact ReversibleLayer65.rows_checked
  · change ReversibleRows.checkLayer 66 ReversibleLayer66.current ReversibleLayer66.following=true
    exact ReversibleLayer66.rows_checked
  · change ReversibleRows.checkLayer 67 ReversibleLayer67.current ReversibleLayer67.following=true
    exact ReversibleLayer67.rows_checked
  · change ReversibleRows.checkLayer 68 ReversibleLayer68.current ReversibleLayer68.following=true
    exact ReversibleLayer68.rows_checked
  · change ReversibleRows.checkLayer 69 ReversibleLayer69.current ReversibleLayer69.following=true
    exact ReversibleLayer69.rows_checked
  · change ReversibleRows.checkLayer 70 ReversibleLayer70.current ReversibleLayer70.following=true
    exact ReversibleLayer70.rows_checked
  · change ReversibleRows.checkLayer 71 ReversibleLayer71.current ReversibleLayer71.following=true
    exact ReversibleLayer71.rows_checked
  · change ReversibleRows.checkLayer 72 ReversibleLayer72.current ReversibleLayer72.following=true
    exact ReversibleLayer72.rows_checked
  · change ReversibleRows.checkLayer 73 ReversibleLayer73.current ReversibleLayer73.following=true
    exact ReversibleLayer73.rows_checked
  · change ReversibleRows.checkLayer 74 ReversibleLayer74.current ReversibleLayer74.following=true
    exact ReversibleLayer74.rows_checked
  · change ReversibleRows.checkLayer 75 ReversibleLayer75.current ReversibleLayer75.following=true
    exact ReversibleLayer75.rows_checked
  · change ReversibleRows.checkLayer 76 ReversibleLayer76.current ReversibleLayer76.following=true
    exact ReversibleLayer76.rows_checked
  · change ReversibleRows.checkLayer 77 ReversibleLayer77.current ReversibleLayer77.following=true
    exact ReversibleLayer77.rows_checked
  · change ReversibleRows.checkLayer 78 ReversibleLayer78.current ReversibleLayer78.following=true
    exact ReversibleLayer78.rows_checked
  · change ReversibleRows.checkLayer 79 ReversibleLayer79.current ReversibleLayer79.following=true
    exact ReversibleLayer79.rows_checked
  · change ReversibleRows.checkLayer 80 ReversibleLayer80.current ReversibleLayer80.following=true
    exact ReversibleLayer80.rows_checked
  · change ReversibleRows.checkLayer 81 ReversibleLayer81.current ReversibleLayer81.following=true
    exact ReversibleLayer81.rows_checked
  · change ReversibleRows.checkLayer 82 ReversibleLayer82.current ReversibleLayer82.following=true
    exact ReversibleLayer82.rows_checked
  · change ReversibleRows.checkLayer 83 ReversibleLayer83.current ReversibleLayer83.following=true
    exact ReversibleLayer83.rows_checked
  · change ReversibleRows.checkLayer 84 ReversibleLayer84.current ReversibleLayer84.following=true
    exact ReversibleLayer84.rows_checked
  · change ReversibleRows.checkLayer 85 ReversibleLayer85.current ReversibleLayer85.following=true
    exact ReversibleLayer85.rows_checked
  · change ReversibleRows.checkLayer 86 ReversibleLayer86.current ReversibleLayer86.following=true
    exact ReversibleLayer86.rows_checked
  · change ReversibleRows.checkLayer 87 ReversibleLayer87.current ReversibleLayer87.following=true
    exact ReversibleLayer87.rows_checked
  · change ReversibleRows.checkLayer 88 ReversibleLayer88.current ReversibleLayer88.following=true
    exact ReversibleLayer88.rows_checked
  · change ReversibleRows.checkLayer 89 ReversibleLayer89.current ReversibleLayer89.following=true
    exact ReversibleLayer89.rows_checked
  · change ReversibleRows.checkLayer 90 ReversibleLayer90.current ReversibleLayer90.following=true
    exact ReversibleLayer90.rows_checked
  · change ReversibleRows.checkLayer 91 ReversibleLayer91.current ReversibleLayer91.following=true
    exact ReversibleLayer91.rows_checked
  · change ReversibleRows.checkLayer 92 ReversibleLayer92.current ReversibleLayer92.following=true
    exact ReversibleLayer92.rows_checked
  · change ReversibleRows.checkLayer 93 ReversibleLayer93.current ReversibleLayer93.following=true
    exact ReversibleLayer93.rows_checked
  · change ReversibleRows.checkLayer 94 ReversibleLayer94.current ReversibleLayer94.following=true
    exact ReversibleLayer94.rows_checked
  · change ReversibleRows.checkLayer 95 ReversibleLayer95.current ReversibleLayer95.following=true
    exact ReversibleLayer95.rows_checked
  · change ReversibleRows.checkLayer 96 ReversibleLayer96.current ReversibleLayer96.following=true
    exact ReversibleLayer96.rows_checked
  · change ReversibleRows.checkLayer 97 ReversibleLayer97.current ReversibleLayer97.following=true
    exact ReversibleLayer97.rows_checked
  · change ReversibleRows.checkLayer 98 ReversibleLayer98.current ReversibleLayer98.following=true
    exact ReversibleLayer98.rows_checked
  · change ReversibleRows.checkLayer 99 ReversibleLayer99.current ReversibleLayer99.following=true
    exact ReversibleLayer99.rows_checked
  · change ReversibleRows.checkLayer 100 ReversibleLayer100.current ReversibleLayer100.following=true
    exact ReversibleLayer100.rows_checked
  · change ReversibleRows.checkLayer 101 ReversibleLayer101.current ReversibleLayer101.following=true
    exact ReversibleLayer101.rows_checked
  · change ReversibleRows.checkLayer 102 ReversibleLayer102.current ReversibleLayer102.following=true
    exact ReversibleLayer102.rows_checked
  · change ReversibleRows.checkLayer 103 ReversibleLayer103.current ReversibleLayer103.following=true
    exact ReversibleLayer103.rows_checked
  · change ReversibleRows.checkLayer 104 ReversibleLayer104.current ReversibleLayer104.following=true
    exact ReversibleLayer104.rows_checked
  · change ReversibleRows.checkLayer 105 ReversibleLayer105.current ReversibleLayer105.following=true
    exact ReversibleLayer105.rows_checked

theorem terminal_checked : ReversibleRows.terminalCheck 53 (data 106)=true :=
  ReversibleTerminal.terminal_checked

theorem birth_checked : ReversibleRows.birthOK 53 (data 53)=true := ReversibleLayer53.birth_checked

/-- Actual first division, including reverse-growth and finite-event monitors. -/
theorem actual_first_division (ε ρ : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10)
    (hρ : 0 ≤ ρ) (hρu : ρ ≤ 2/10000000)
    (word : Fin 2 → Fin 2) (a : Fin 2 → Fin 849 × Fin 213)
    (ha : ∀ k, newborn 53 (word k).val (a k).1.val (a k).2.val) :
    ENNReal.ofReal (9901/10000 : ℝ) ≤
      reversibleFirstDivisionReturn 53 100000000 ε ρ hε hρ word
        (reversibleBudgetEmbed 53 100000000 (⟨0,a⟩,0)) :=
  reversible_actual_first_division_from_checks ε ρ hε hε1 hρ hρu data all_rows
    terminal_checked birth_checked word a ha

/-- Ten actual state-dependent cycles with a fresh finite event quota per cycle. -/
theorem ten_cycles (ε ρ : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10)
    (hρ : 0 ≤ ρ) (hρu : ρ ≤ 2/10000000)
    (word : Fin 2 → Fin 2) (a : ReversibleWordNewborn word) :
    (9/10 : ℝ≥0∞) ≤ (reversibleCycleKernel ε ρ hε hρ word).survival 10 a :=
  reversible_ten_cycles_from_checks ε ρ hε hε1 hρ hρu data all_rows
    terminal_checked birth_checked word a

/-- A nonzero interaction and strictly positive reverse-growth region,
with an explicit admitted input for every word. -/
theorem positive_window (ε ρ : ℝ) (hεlo : 1/10000 ≤ ε) (hεhi : ε ≤ 1/10)
    (hρlo : 1/10000000 ≤ ρ) (hρhi : ρ ≤ 2/10000000)
    (word : Fin 2 → Fin 2) :
    ∃ (hε : 0 ≤ ε) (hρ : 0 ≤ ρ),
      (9/10 : ℝ≥0∞) ≤ (reversibleCycleKernel ε ρ hε hρ word).survival 10
        (reversibleEncodeWord word) := by
  have hε : 0 ≤ ε := by linarith
  have hρ : 0 ≤ ρ := by linarith
  exact ⟨hε,hρ,ten_cycles ε ρ hε hεhi hρ hρhi word (reversibleEncodeWord word)⟩

end CompositionalMemory.ReversibleCertificate
