import proofs.SerialTransferSelection.CycleMaterial
import proofs.SerialTransferSelection.DiscardAccounting

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

/-- K+1 batches, with the first charge from newborn founders. There is no
double counting of a terminal refill as both a batch charge and terminal stock. -/
theorem mission_start_size_sum (K N M : ℕ) (W : Fin (K+1) → ℕ)
    (h0 : W 0=N*M) (hW : ∀ j : Fin K, W j.succ ≤ 2*N*M) :
    (∑ j, W j) ≤ (2*K+1)*N*M := by
  rw [Fin.sum_univ_succ,h0]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hW j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  nlinarith only [h]

theorem mission_precursor_accounts (K N M : ℕ) (W : Fin (K+1) → ℕ)
    (h0 : W 0=N*M) (hW : ∀ j : Fin K, W j.succ ≤ 2*N*M) :
    (∑ j, 4*W j) ≤ (8*K+4)*N*M ∧
    (∑ j, 3*W j) ≤ (6*K+3)*N*M ∧
    (∑ j, W j) ≤ (2*K+1)*N*M := by
  have h := mission_start_size_sum K N M W h0 hW
  rw [← Finset.mul_sum,← Finset.mul_sum]
  constructor
  · nlinarith only [h]
  constructor
  · nlinarith only [h]
  · exact h

/-- Molecular discard, using the exact intact transfer balance and the retained
population's lower size bound. Individual molecular coordinates retain the exact
balance in actual_transfer_material_balance. -/
theorem mission_discard_bound (K N M : ℕ) (W D R : Fin (K+1) → ℕ)
    (h0 : W 0=N*M) (hW : ∀ j : Fin K, W j.succ ≤ 2*N*M)
    (hbalance : ∀ j, D j+R j=4*W j) (hretained : ∀ j, N*M ≤ R j) :
    (∑ j, D j) ≤ (7*K+3)*N*M := by
  have hb := (mission_precursor_accounts K N M W h0 hW).1
  have he : (∑ j, D j)+(∑ j, R j)=∑ j, 4*W j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hbalance j)
  have hr := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hretained j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hr
  nlinarith only [hb,he,hr]

theorem mission_service_allowance (K M JB JR : ℕ) (B : Fin K → ℕ) (R : Fin K → Fin M → ℕ)
    (hb : ∀ j, B j < JB) (hr : ∀ j i, R j i < JR) :
    (∑ j, (B j+∑ i, R j i)) ≤ K*(JB+M*JR) := by
  have hR (j : Fin K) : (∑ i, R j i) ≤ M*JR := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hr j i).le)
    simpa using h
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => Nat.add_le_add (hb j).le (hR j))
  simpa using h

theorem mission_duration (K : ℕ) (T : ℝ) (d : Fin K → ℝ)
    (hd : ∀ j, d j ≤ T+5376) : (∑ j, d j) ≤ (K : ℝ)*(T+5376) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hd j)
  simpa [mul_add] using h

/-- The literal returned ready state includes one terminal refill. -/
theorem mission_precursor_with_terminal (K N M F : ℕ) (W : Fin (K+1) → ℕ)
    (h0 : W 0=N*M) (hW : ∀ j : Fin K, W j.succ ≤ 2*N*M) (hF : F ≤ 8*N*M) :
    (∑ j, 4*W j)+F ≤ (8*K+12)*N*M := by
  have h := (mission_precursor_accounts K N M W h0 hW).1
  nlinarith only [h,hF]

end SerialTransferSelection
