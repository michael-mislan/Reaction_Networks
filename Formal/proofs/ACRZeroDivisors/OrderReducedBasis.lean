import proofs.ACRZeroDivisors.OrderOutput

namespace ACRZeroDivisors.OrderWitness
open MvPolynomial

theorem standard_no_divisor (e : Exponent) (he : Standard e) :
    ¬ L1 ≤ e ∧ ¬ L2 ≤ e ∧ ¬ L3 ≤ e := by
  refine ⟨?_,?_,?_⟩
  · intro h
    have h0 := h 0
    norm_num [L1] at h0
    exact (not_le_of_gt he.1) h0
  · intro h
    have h0 := h 0
    have h2 := h 2
    norm_num [L2] at h0 h2
    dsimp [Standard,zDegree] at he
    omega
  · intro h
    have h1 := h 1
    have h2 := h 2
    norm_num [L3] at h1 h2
    dsimp [Standard,zDegree] at he
    omega

theorem basis_leaders_monic : coeff L1 b1 = 1 ∧ coeff L2 b2 = 1 ∧ coeff L3 b3 = 1 := by
  have h1 : (Finsupp.single 1 2 : Exponent) ≠ L1 := by
    intro h
    have hh := congrArg (fun e : Exponent => e 0) h
    norm_num [L1] at hh
  have h2 : (Finsupp.single 1 1 : Exponent) ≠ L2 := by
    intro h
    have hh := congrArg (fun e : Exponent => e 0) h
    norm_num [L2] at hh
  have h3 : (Finsupp.single 0 1 : Exponent) ≠ L3 := by
    intro h
    have hh := congrArg (fun e : Exponent => e 0) h
    norm_num [L3] at hh
  constructor
  · change coeff L1 (monomial L1 1-monomial (Finsupp.single 1 2) 1) = 1
    simp [coeff_monomial,h1]
  constructor
  · change coeff L2 (monomial L2 1-monomial (Finsupp.single 1 1) 1) = 1
    simp [coeff_monomial,h2]
  · change coeff L3 (monomial L3 1-monomial (Finsupp.single 0 1) 1) = 1
    simp [coeff_monomial,h3]

theorem basis_tails_standard :
    (∀ e ∈ b1.support, e ≠ L1 → Standard e) ∧
    (∀ e ∈ b2.support, e ≠ L2 → Standard e) ∧
    (∀ e ∈ b3.support, e ≠ L3 → Standard e) := by
  refine ⟨?_,?_,?_⟩
  · intro e he hne
    have hr := (support_binomial he).resolve_left hne
    rw [hr]
    norm_num [Standard,zDegree]
  · intro e he hne
    have hr := (support_binomial he).resolve_left hne
    rw [hr]
    norm_num [Standard,zDegree]
  · intro e he hne
    have hr := (support_binomial he).resolve_left hne
    rw [hr]
    norm_num [Standard,zDegree]

theorem basis_leaders_antichain :
    ¬ L1 ≤ L2 ∧ ¬ L1 ≤ L3 ∧ ¬ L2 ≤ L1 ∧
    ¬ L2 ≤ L3 ∧ ¬ L3 ≤ L1 ∧ ¬ L3 ≤ L2 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro h; have hh := h 0; norm_num [L1,L2] at hh
  · intro h; have hh := h 0; norm_num [L1,L3] at hh
  · intro h; have hh := h 2; norm_num [L1,L2] at hh
  · intro h; have hh := h 0; norm_num [L2,L3] at hh
  · intro h; have hh := h 2; norm_num [L1,L3] at hh
  · intro h; have hh := h 1; norm_num [L2,L3] at hh

theorem order_elimination_property (p : P) (e : Exponent)
    (he : IsLeading e p) (hz : zDegree e = 0) : PureT p := by
  intro d hd
  by_contra hdz
  have hed : MixedLT e d := mixed_elimination e d hz (Nat.pos_of_ne_zero hdz)
  rcases he.2 d hd with h | h
  · subst d
    exact mixed_irrefl e hed
  · exact mixed_irrefl e (mixed_trans hed h)

end ACRZeroDivisors.OrderWitness
