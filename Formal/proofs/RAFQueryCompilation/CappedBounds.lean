import proofs.RAFQueryCompilation.BudgetPruning

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

theorem terminalCap_mono (e' e i o p' p : ℕ) (he : e' ≤ e) (hp : p' ≤ p) :
    terminalCap e' i o p' ≤ terminalCap e i o p := by
  have h1 := Nat.mul_le_mul he (Nat.mul_le_mul_left (i+1) (Nat.add_le_add_right hp 1))
  have h2 := Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.add_le_add hp (Nat.mul_le_mul_right o he)) 1) 2
  exact Nat.add_le_add (Nat.add_le_add_left h1 1) (Nat.mul_le_mul_left 2 h2)

theorem supportCap_mono (e' e i c p' p : ℕ) (he : e' ≤ e) (hp : p' ≤ p) :
    supportCap e' i c p' ≤ supportCap e i c p := by
  have h1 := Nat.mul_le_mul he (Nat.mul_le_mul_left (i+c+2) (Nat.add_le_add_right hp 1))
  have h2 := Nat.pow_le_pow_left (Nat.add_le_add_right he 1) 2
  exact Nat.add_le_add (Nat.add_le_add_left h1 1) (Nat.mul_le_mul_left 2 h2)

theorem cappedClosure_bound (Q : CRS M R) (A : Finset R) (H : Finset M)
    (e i o : ℕ) (he : A.card ≤ e)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o)
    (hout : ∀ r ∈ A, Q.outputs r ⊆ H) (hf : Q.food ⊆ H) (order : List R) :
    (cappedClosure Q A order i o).2 ≤ H.card +
      order.length*replayCap e i o H.card + terminalCap e i o H.card := by
  have hpool : (chargedReplayFrom Q A order Q.food).1 ⊆ H := by
    rw [chargedReplay_refines]
    change replaySchedule Q A order ⊆ H
    apply (replaySchedule_subset_envelope Q A A (Finset.Subset.refl _) order).trans
    apply Finset.union_subset hf
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨r,hr,hx⟩
    exact hout r hr hx
  have hr := chargedReplay_bound Q Q.food H A e i o he hi ho hout hf order
  have hc := terminalCap_mono A.card e i o _ H.card he (Finset.card_le_card hpool)
  have hfood := Finset.card_le_card hf
  dsimp only [cappedClosure, replayCap]
  omega

theorem cappedPruning_bound (Q : CRS M R) (cats : R → Finset M)
    (H : Finset M) (e i o c : ℕ) (hf : Q.food ⊆ H)
    (cert : List (List R)) (A : Finset R) (he : A.card ≤ e)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o)
    (hout : ∀ r ∈ A, Q.outputs r ⊆ H) :
    (cappedPruning Q cats i o c A cert).2 ≤
      cert.flatten.length * replayCap e i o H.card +
      pruningRounds Q (fun x r => x ∈ cats r) A cert * pruningRoundCap e i o c H.card := by
  induction cert generalizing A with
  | nil => simp [cappedPruning, pruningRounds]
  | cons order rest ihcert =>
    have hclcost := cappedClosure_bound Q A H e i o he hi ho hout hf order
    cases hcl : checkClosure Q A order with
    | none =>
      have hb : (cappedClosure Q A order i o).2 ≤
          order.length * replayCap e i o H.card + pruningRoundCap e i o c H.card := by
        unfold terminalCap pruningRoundCap at *
        omega
      simp only [cappedPruning, cappedClosure_refines, hcl, pruningRounds,
        List.flatten_cons, List.length_append]
      nlinarith
    | some pool =>
      have hp := Finset.card_le_card (checkedClosure_pool_subset Q A H hf hout order hcl)
      have hs := supportCap_mono A.card e i c pool.card H.card he hp
      have hb : (cappedClosure Q A order i o).2 + supportCap A.card i c pool.card ≤
          order.length * replayCap e i o H.card + pruningRoundCap e i o c H.card := by
        unfold terminalCap supportCap pruningRoundCap at *
        omega
      by_cases ht : pruneWithPool Q (fun x r => x ∈ cats r) A pool = A
      · simp only [cappedPruning, cappedClosure_refines, hcl, pruningRounds, if_pos ht,
          List.flatten_cons, List.length_append]
        nlinarith
      · have hsub : pruneWithPool Q (fun x r => x ∈ cats r) A pool ⊆ A :=
          Finset.filter_subset _ _
        have htail := ihcert _ ((Finset.card_le_card hsub).trans he)
          (fun r hr => hi r (hsub hr)) (fun r hr => ho r (hsub hr))
          (fun r hr => hout r (hsub hr))
        simp only [cappedPruning, cappedClosure_refines, hcl, pruningRounds, if_neg ht,
          List.flatten_cons, List.length_append]
        nlinarith

theorem cappedPruning_source_bound (Q : CRS M R) (cats : R → Finset M)
    (H : Finset M) (e i o c : ℕ) (hf : Q.food ⊆ H)
    (cert : List (List R)) (A : Finset R) (he : A.card ≤ e)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o)
    (hout : ∀ r ∈ A, Q.outputs r ⊆ H) :
    (cappedPruning Q cats i o c A cert).2 ≤ cert.flatten.length * replayCap e i o H.card +
      (e+1) * pruningRoundCap e i o c H.card := by
  have hr := pruningRounds_le Q (fun x r => x ∈ cats r) cert A
  exact (cappedPruning_bound Q cats H e i o c hf cert A he hi ho hout).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega :
      pruningRounds Q (fun x r => x ∈ cats r) A cert ≤ e+1)) _)

theorem budgetPruning_source_complete (Q : CRS M R) (cats : R → Finset M)
    (H : Finset M) (e i o c : ℕ) (hf : Q.food ⊆ H)
    (cert : List (List R)) (A : Finset R) (he : A.card ≤ e)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o)
    (hout : ∀ r ∈ A, Q.outputs r ⊆ H) (budget : ℕ)
    (hb : cert.flatten.length*replayCap e i o H.card+(e+1)*pruningRoundCap e i o c H.card ≤ budget) :
    budgetPruning Q cats i o c A cert budget = cappedPruning Q cats i o c A cert :=
  budgetPruning_complete Q cats i o c A cert budget
    ((cappedPruning_source_bound Q cats H e i o c hf cert A he hi ho hout).trans hb)

end RAFQueryCompilation
