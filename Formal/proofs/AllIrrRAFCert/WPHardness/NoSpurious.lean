import proofs.AllIrrRAFCert.WPHardness.Omissions
namespace AllIrrRAFCert.WPHardness
open RAF RAF.Frankl
variable {k n q : Nat}

theorem decoder_choice (A : System n q) (S : Finset (Rxn k n q))
    (hS : IsRAF (crs A) cat S) (a : Fin k → Fin (n+2))
    (ha : ∀ i u, Rxn.selector (i,u) ∈ S ↔ u ≠ a i)
    {v : Vertex k n} (hv : Rxn.colorGate v ∈ S) : v.2 = a v.1 := by
  by_contra hn
  obtain ⟨t,ht⟩ := hS.2.1 _ hv
  have hx : Mol.signal (v.1,a v.1) ∈ (crs A).inputs (.colorGate v) := by
    simp [crs,Ne.symm hn]
  have hs := signal_origin A S (ht hx)
  exact ((ha v.1 (a v.1)).mp hs) rfl

theorem statement_sound (A : System n q) (S : Finset (Rxn k n q))
    (hS : IsRAF (crs A) cat S) (a : Fin k → Fin (n+2))
    (ha : ∀ i u, Rxn.selector (i,u) ∈ S ↔ u ≠ a i) :
    ∀ t u, Mol.statement u ∈ closureAt (crs A) S t → Derives A (seeds a) u := by
  intro t
  induction t with
  | zero => intro u hu; simp [closureAt,crs] at hu
  | succ t ih =>
    intro u hu
    simp only [closureAt,closureStep,Finset.mem_union,Finset.mem_biUnion] at hu
    rcases hu with hu | ⟨r,hr,ho⟩
    · exact ih u hu
    · by_cases he : Enabled (crs A) (closureAt (crs A) S t) r
      · have hout : Mol.statement u ∈ (crs A).outputs r := by simpa [he] using ho
        cases r with
        | selector v => simp [crs] at hout
        | colorGate v =>
          have hu : u = v.2 := by simpa [crs] using hout
          apply Derives.seed
          rw [hu,decoder_choice A S hS a ha hr]
          exact Finset.mem_image.mpr ⟨v.1,Finset.mem_univ _,rfl⟩
        | rule j =>
          have hu : u = A.result j := by simpa [crs] using hout
          rw [hu]
          apply Derives.rule j
          intro v hv
          apply ih v
          exact he (by simp [crs,hv])
        | close => simp [crs] at hout
      · simp [he] at ho

theorem extra_implies_generating (A : System n q) :
    Extra (k := k) A → ∃ a : Fin k → Fin (n+2), Generates A a := by
  rintro ⟨S,hS,hu⟩
  obtain ⟨a,ha⟩ := extra_omission_pattern A S hS hu
  obtain ⟨t,ht⟩ := hS.1.2.1 _ (extra_contains_close A S hS hu)
  refine ⟨a,fun u => statement_sound A S hS.1 a ha t u (ht ?_)⟩
  simp [crs]

theorem seeds_card_le (a : Fin k → Fin (n+2)) : (seeds a).card ≤ k := by
  exact Finset.card_image_le.trans (by simp)
end AllIrrRAFCert.WPHardness
