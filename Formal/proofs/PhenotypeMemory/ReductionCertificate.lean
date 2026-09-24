import proofs.PhenotypeMemory.Source

namespace PhenotypeMemory
@[simp] theorem cons_five {alpha : Type*} {m : Nat} (x : alpha)
    (u : Fin m.succ.succ.succ.succ.succ → alpha) :
    Matrix.vecCons x u 5 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))) := rfl

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

def eventInverse : Fin 6 → Fin 6 → ℚ :=
![![(65987950/28996311),(1469125/28996311),(3567875/57992622),(2369575/28996311),(41725/28996311),(3098675/9665437)],![(1469125/57992622),(32131925/28996311),(78034675/57992622),(188825/28996311),(702625/57992622),(246925/9665437)],![(209875/173977866),(4590275/86988933),(425380825/173977866),(26975/86988933),(100375/173977866),(35275/28996311)],![(2369575/57992622),(188825/28996311),(458575/57992622),(51941825/28996311),(1133275/57992622),(67923925/9665437)],![(542425/28996311),(9134125/28996311),(22182875/57992622),(14732575/28996311),(31777150/28996311),(19265675/9665437)],![(182275/28996311),(29050/28996311),(35275/28996311),(7991050/28996311),(87175/28996311),(84799350/9665437)]]

def eventH (f : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  (1/10+death i)*f i-molecular (1/100) f i

theorem event_inverse_identity (i j : Fin 6) :
    eventH (fun k => eventInverse k j) i = if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [eventH, eventInverse, death, molecular]

theorem event_inverse_nonnegative (i j : Fin 6) : 0 ≤ eventInverse i j := by
  fin_cases i <;> fin_cases j <;> norm_num [eventInverse]

def independentNext (z : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  ∑ j : Fin 6, eventInverse i j*(death j+(daughter z j)^2/10)

def lowerRow : ℕ → Fin 6 → ℚ
  | 0 => ![(0),(0),(0),(0),(0),(0)]
  | 1 => ![(11263/15625),(29907/40000),(749889/1000000),(55317/500000),(142163/250000),(93943/1000000)]
  | 2 => ![(424399/500000),(176671/200000),(443633/500000),(48053/250000),(66139/100000),(158099/1000000)]
  | 3 => ![(44973/50000),(468399/500000),(37659/40000),(62261/250000),(353319/500000),(208303/1000000)]
  | 4 => ![(461227/500000),(120049/125000),(482671/500000),(144229/500000),(731977/1000000),(1533/6250)]
  | 5 => ![(933717/1000000),(194279/200000),(195279/200000),(31579/100000),(747119/1000000),(135921/500000)]
  | 6 => ![(469787/500000),(976737/1000000),(490851/500000),(66951/200000),(756571/1000000),(290687/1000000)]
  | 7 => ![(942789/1000000),(244859/250000),(984343/1000000),(34793/100000),(152533/200000),(151983/500000)]
  | 8 => ![(188929/200000),(980859/1000000),(98571/100000),(178547/500000),(766691/1000000),(313291/1000000)]
  | _ => fun _ => 0

set_option maxHeartbeats 2000000 in
theorem lower_iteration_certificate (n : Fin 8) (i : Fin 6) :
    lowerRow (n.val+1) i ≤ independentNext (lowerRow n.val) i := by
  fin_cases n <;> fin_cases i <;>
    norm_num [lowerRow, independentNext, eventInverse, death, daughter, Fin.sum_univ_succ]

theorem independent_lower_exceeds : lowerRow 8 5 > 31/100 := by
  norm_num [lowerRow]

theorem source_gap_arithmetic : (31/100:ℚ)-47/200 = 3/40 := by norm_num

end PhenotypeMemory
