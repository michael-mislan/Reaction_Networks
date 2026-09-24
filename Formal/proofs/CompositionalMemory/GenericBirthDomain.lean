import proofs.CompositionalMemory.GenericCountDomain

namespace CompositionalMemory

noncomputable def generalBirthCounts {k d : ℕ} (N C : ℕ)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ) (birth : ℝ) :
    Finset (Fin k → Fin d → ℕ) := by
  classical
  exact (generalCountBox k d (C*N)).filter (fun n => ∀ i,
    E i (fun a => (n i a:ℝ)/(N:ℝ)-center i a) < birth)

abbrev GeneralBirthCount {k d : ℕ} (N C : ℕ)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ) (birth : ℝ) :=
  {n : Fin k → Fin d → ℕ // n ∈ generalBirthCounts N C center E birth}

abbrev GeneralBirthOutcome {k d : ℕ} (N C : ℕ)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ) (birth : ℝ) :=
  Option (GeneralBirthCount N C center E birth × GeneralBirthCount N C center E birth)

theorem mem_generalBirthCounts {k d : ℕ} (N C : ℕ) (hN : 0 < N)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ)
    (c radius birth : ℝ) (hc : 0 < c) (hr : 0 ≤ radius) (hb : birth ≤ c*radius^2)
    (hcenter : ∀ i a, center i a ≤ (C:ℝ)-radius)
    (hE : ∀ i y a, c*(y a)^2 ≤ E i y) (n : Fin k → Fin d → ℕ) :
    n ∈ generalBirthCounts N C center E birth ↔
      ∀ i, E i (fun a => (n i a:ℝ)/(N:ℝ)-center i a) < birth := by
  classical
  rw [generalBirthCounts,Finset.mem_filter]
  constructor
  · exact And.right
  · intro he
    refine ⟨(mem_generalCountBox k d (C*N) n).mpr ?_,he⟩
    intro i a
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    have hcap := energy_coordinate_cap C c radius birth center E hc hr hb hcenter hE i
      (fun a => (n i a:ℝ)/(N:ℝ)) (he i) a
    have hh : (n i a:ℝ) ≤ (C:ℝ)*(N:ℝ) := (div_le_iff₀ hNr).mp hcap
    exact_mod_cast hh

theorem general_lattice_concentration {k d : ℕ} (hk : 1 ≤ k) (N : ℕ)
    (n : Fin k → Fin d → ℕ) (i : Fin k) :
    generalConcentration (n,k*N) i=(fun a => (n i a:ℝ)/(N:ℝ)) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  funext a
  simp only [generalConcentration,Nat.cast_mul]
  congr 1
  field_simp

theorem general_birth_in_growth_domain {k d : ℕ} (hk : 1 ≤ k) (N C : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ)
    (c radius birth outer : ℝ) (hc : 0 < c) (hr : 0 ≤ radius)
    (hb : birth ≤ outer) (ho : outer ≤ c*radius^2)
    (hcenter : ∀ i a, center i a ≤ (C:ℝ)-radius)
    (hE : ∀ i y a, c*(y a)^2 ≤ E i y)
    (n : GeneralBirthCount N C center E birth) :
    (n.val,k*N) ∈ generalProductDomain N C center E outer := by
  have he := (mem_generalBirthCounts N C (by omega) center E c radius birth hc hr
    (hb.trans ho) hcenter hE n.val).mp n.property
  apply (mem_generalProductDomain hk N C hN center E c radius outer hc hr ho hcenter hE _).mpr
  refine ⟨le_rfl,by omega,?_⟩
  intro i
  rw [general_lattice_concentration hk]
  exact (he i).trans_le hb

end CompositionalMemory
