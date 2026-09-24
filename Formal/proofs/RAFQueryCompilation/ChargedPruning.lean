import proofs.RAFQueryCompilation.ChargedClosure
import proofs.RAFQueryCompilation.PruningWork

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def supportCharge (Q : CRS M R) (cats : R → Finset M)
    (A : Finset R) (pool : Finset M) : ℕ :=
  1 + (∑ r ∈ A, ((Q.inputs r).card + (cats r).card + 2)*(pool.card+1)) +
    2*(A.card+1)^2

omit [DecidableEq R] in
theorem supportCharge_le (Q : CRS M R) (cats : R → Finset M)
    (A : Finset R) (pool : Finset M) (e i c p : ℕ)
    (he : A.card ≤ e) (hp : pool.card ≤ p)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i)
    (hc : ∀ r ∈ A, (cats r).card ≤ c) :
    supportCharge Q cats A pool ≤ 1+e*((i+c+2)*(p+1))+2*(e+1)^2 := by
  have hs : (∑ r ∈ A, ((Q.inputs r).card+(cats r).card+2)*(pool.card+1)) ≤
      e*((i+c+2)*(p+1)) := by
    calc
      _ ≤ ∑ _r ∈ A, (i+c+2)*(p+1) := Finset.sum_le_sum fun r hr =>
        Nat.mul_le_mul (Nat.add_le_add_right (Nat.add_le_add (hi r hr) (hc r hr)) 2)
          (Nat.add_le_add_right hp 1)
      _ = A.card*((i+c+2)*(p+1)) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ he
  have hh := Nat.pow_le_pow_left (Nat.add_le_add_right he 1) 2
  unfold supportCharge
  omega

/-- Charge semantics composed with the same branching decisions as the checker.
The cost interpretation is the declared finite-set model, not native timing. -/
def chargedPruning (Q : CRS M R) (cats : R → Finset M) :
    Finset R → List (List R) → Option (Finset R) × ℕ
  | _, [] => (none, 0)
  | A, order :: rest =>
    let cl := chargedClosure Q A order
    match cl.1 with
    | none => (none, cl.2)
    | some pool =>
      let T := pruneWithPool Q (fun x r => x ∈ cats r) A pool
      let charge := cl.2 + supportCharge Q cats A pool
      if T = A then (some A, charge) else
        let tail := chargedPruning Q cats T rest
        (tail.1, charge + tail.2)

theorem chargedPruning_refines (Q : CRS M R) (cats : R → Finset M)
    (cert : List (List R)) (A : Finset R) :
    (chargedPruning Q cats A cert).1 = checkPruning Q (fun x r => x ∈ cats r) A cert := by
  induction cert generalizing A with
  | nil => rfl
  | cons order rest ih =>
    simp only [chargedPruning, chargedClosure_refines, checkPruning]
    cases hc : checkClosure Q A order with
    | none => rfl
    | some pool =>
      by_cases he : pruneWithPool Q (fun x r => x ∈ cats r) A pool = A
      · simp [he]
      · simp [he, ih]

def replayCap (e i o p : ℕ) : ℕ := 1+e+(i+1)*(p+1)+(p+o+1)^2

def pruningRoundCap (e i o c p : ℕ) : ℕ :=
  p + (1+e*((i+1)*(p+1))+2*(p+e*o+1)^2) +
    (1+e*((i+c+2)*(p+1))+2*(e+1)^2)

/-- Full replay/closure/pruning charge composition. Region construction,
parsing, state maintenance and machine representation costs are separate. -/
theorem chargedPruning_bound (Q : CRS M R) (cats : R → Finset M)
    (H : Finset M) (e i o c : ℕ) (hf : Q.food ⊆ H)
    (cert : List (List R)) (A : Finset R) (he : A.card ≤ e)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o)
    (hc : ∀ r ∈ A, (cats r).card ≤ c)
    (hout : ∀ r ∈ A, Q.outputs r ⊆ H) :
    (chargedPruning Q cats A cert).2 ≤
      cert.flatten.length * replayCap e i o H.card +
      pruningRounds Q (fun x r => x ∈ cats r) A cert * pruningRoundCap e i o c H.card := by
  induction cert generalizing A with
  | nil => simp [chargedPruning, pruningRounds]
  | cons order rest ihcert =>
    have hclcost := chargedClosure_bound Q A H e i o he hi ho hout hf order
    cases hcl : checkClosure Q A order with
    | none =>
      have hb : (chargedClosure Q A order).2 ≤
          order.length * replayCap e i o H.card + pruningRoundCap e i o c H.card := by
        unfold replayCap pruningRoundCap
        omega
      simp only [chargedPruning, chargedClosure_refines, hcl, pruningRounds,
        List.flatten_cons, List.length_append]
      nlinarith
    | some pool =>
      have hp := Finset.card_le_card (checkedClosure_pool_subset Q A H hf hout order hcl)
      have hs := supportCharge_le Q cats A pool e i c H.card he hp hi hc
      have hb : (chargedClosure Q A order).2 + supportCharge Q cats A pool ≤
          order.length * replayCap e i o H.card + pruningRoundCap e i o c H.card := by
        unfold replayCap pruningRoundCap
        omega
      by_cases ht : pruneWithPool Q (fun x r => x ∈ cats r) A pool = A
      · simp only [chargedPruning, chargedClosure_refines, hcl, pruningRounds, if_pos ht,
          List.flatten_cons, List.length_append]
        nlinarith
      · have hsub : pruneWithPool Q (fun x r => x ∈ cats r) A pool ⊆ A :=
          Finset.filter_subset _ _
        have htail := ihcert _ ((Finset.card_le_card hsub).trans he)
          (fun r hr => hi r (hsub hr)) (fun r hr => ho r (hsub hr))
          (fun r hr => hc r (hsub hr)) (fun r hr => hout r (hsub hr))
        simp only [chargedPruning, chargedClosure_refines, hcl, pruningRounds, if_neg ht,
          List.flatten_cons, List.length_append]
        nlinarith

theorem chargedPruning_source_bound (Q : CRS M R) (cats : R → Finset M)
    (H : Finset M) (e i o c : ℕ) (hf : Q.food ⊆ H)
    (cert : List (List R)) (A : Finset R) (he : A.card ≤ e)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o)
    (hc : ∀ r ∈ A, (cats r).card ≤ c)
    (hout : ∀ r ∈ A, Q.outputs r ⊆ H) :
    (chargedPruning Q cats A cert).2 ≤ cert.flatten.length * replayCap e i o H.card +
      (e+1) * pruningRoundCap e i o c H.card := by
  have hr := pruningRounds_le Q (fun x r => x ∈ cats r) cert A
  exact (chargedPruning_bound Q cats H e i o c hf cert A he hi ho hc hout).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega :
      pruningRounds Q (fun x r => x ∈ cats r) A cert ≤ e+1)) _)

end RAFQueryCompilation
