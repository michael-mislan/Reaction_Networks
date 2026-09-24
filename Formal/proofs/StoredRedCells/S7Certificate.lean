import proofs.StoredRedCells.S7Data.Part0
import proofs.StoredRedCells.S7Data.Part1
import proofs.StoredRedCells.S7Data.Part2
import proofs.StoredRedCells.S7Data.Part3
import proofs.StoredRedCells.S7Data.Part4
import proofs.StoredRedCells.S7Data.Part5
import proofs.StoredRedCells.S7Data.Part6
import proofs.StoredRedCells.S7Data.Part7
import proofs.StoredRedCells.S7Data.Part8
import proofs.StoredRedCells.S7Data.Part9
import proofs.StoredRedCells.S7Data.Part10
import proofs.StoredRedCells.S7Data.Part11
import proofs.StoredRedCells.S7Data.Part12
import proofs.StoredRedCells.S7Data.Part13
import proofs.StoredRedCells.S7Data.Part14
import proofs.StoredRedCells.S7Data.Part15
import proofs.StoredRedCells.S7Data.Part16
import proofs.StoredRedCells.S7Data.Part17
import proofs.StoredRedCells.S7Data.Part18
import proofs.StoredRedCells.S7Data.Part19
/-! 19620 explicitly represented source columns. Biological applicability remains separate. -/
namespace StoredRedCells.S7Certificate
def sourceChunks : List (List Column) := Part0.chunks ++ Part1.chunks ++ Part2.chunks ++ Part3.chunks ++ Part4.chunks ++ Part5.chunks ++ Part6.chunks ++ Part7.chunks ++ Part8.chunks ++ Part9.chunks ++ Part10.chunks ++ Part11.chunks ++ Part12.chunks ++ Part13.chunks ++ Part14.chunks ++ Part15.chunks ++ Part16.chunks ++ Part17.chunks ++ Part18.chunks ++ Part19.chunks
def sourceTotal : ℤ := (sourceChunks.map (fun rs => (rs.map cost).sum)).sum
theorem source_indices_valid : sourceChunks.all (fun rs => rs.all (fun r => r.terms.all (fun p => decide (p.1 < 10411)))) = true := by
  simp only [sourceChunks, List.all_append, Part0.indices_valid, Part1.indices_valid, Part2.indices_valid, Part3.indices_valid, Part4.indices_valid, Part5.indices_valid, Part6.indices_valid, Part7.indices_valid, Part8.indices_valid, Part9.indices_valid, Part10.indices_valid, Part11.indices_valid, Part12.indices_valid, Part13.indices_valid, Part14.indices_valid, Part15.indices_valid, Part16.indices_valid, Part17.indices_valid, Part18.indices_valid, Part19.indices_valid, Bool.and_self]
theorem source_supplies_nonnegative : sourceChunks.all (fun rs => rs.all (fun r => decide (0 ≤ r.supply))) = true := by
  simp only [sourceChunks, List.all_append, Part0.supplies_nonnegative, Part1.supplies_nonnegative, Part2.supplies_nonnegative, Part3.supplies_nonnegative, Part4.supplies_nonnegative, Part5.supplies_nonnegative, Part6.supplies_nonnegative, Part7.supplies_nonnegative, Part8.supplies_nonnegative, Part9.supplies_nonnegative, Part10.supplies_nonnegative, Part11.supplies_nonnegative, Part12.supplies_nonnegative, Part13.supplies_nonnegative, Part14.supplies_nonnegative, Part15.supplies_nonnegative, Part16.supplies_nonnegative, Part17.supplies_nonnegative, Part18.supplies_nonnegative, Part19.supplies_nonnegative, Bool.and_self]
theorem source_column_count : (sourceChunks.map List.length).sum = 19620 := by
  norm_num only [sourceChunks, List.map_append, List.sum_append, Part0.column_count, Part1.column_count, Part2.column_count, Part3.column_count, Part4.column_count, Part5.column_count, Part6.column_count, Part7.column_count, Part8.column_count, Part9.column_count, Part10.column_count, Part11.column_count, Part12.column_count, Part13.column_count, Part14.column_count, Part15.column_count, Part16.column_count, Part17.column_count, Part18.column_count, Part19.column_count]
theorem source_cost_exact : (sourceTotal : ℚ) / 20180975000000000000000000000000000000000000000 = (1283461673726143619667945455169487587 / 50452437500000000000000000000000000 : ℚ) := by
  norm_num only [sourceTotal, sourceChunks, List.map_append, List.sum_append, Part0.cost_exact, Part1.cost_exact, Part2.cost_exact, Part3.cost_exact, Part4.cost_exact, Part5.cost_exact, Part6.cost_exact, Part7.cost_exact, Part8.cost_exact, Part9.cost_exact, Part10.cost_exact, Part11.cost_exact, Part12.cost_exact, Part13.cost_exact, Part14.cost_exact, Part15.cost_exact, Part16.cost_exact, Part17.cost_exact, Part18.cost_exact, Part19.cost_exact]
end StoredRedCells.S7Certificate
