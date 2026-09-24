import proofs.RAFQueryCompilation.PruningCertificate

namespace RAFQueryCompilation.CertificateFixtures
open RAF

def q0 : CRS (Fin 5) (Fin 5) :=
  { inputs := ![{2, 4}, {2, 4}, {3, 4}, {2, 4}, {0}], outputs := ![{4}, {0, 2}, {3, 4}, {3}, {0, 3}], food := {0} }
def c0 (x r : Fin 5) : Prop := x ∈ (![{1, 3, 4}, {0}, {2, 3, 4}, ∅, {0}] : Fin 5 → Finset (Fin 5)) r
instance dec0 : ∀ x r, Decidable (c0 x r) :=
  fun x r => inferInstanceAs (Decidable (x ∈ (![{1, 3, 4}, {0}, {2, 3, 4}, ∅, {0}] : Fin 5 → Finset (Fin 5)) r))
theorem accepted0 : checkPruning q0 c0 {1, 3} [[], []] =
    some ∅ := by decide

def q1 : CRS (Fin 5) (Fin 5) :=
  { inputs := ![{1, 2}, {3}, {0, 2}, {1}, ∅], outputs := ![{2}, {2, 3}, {0, 1}, {1, 2}, {3}], food := {0} }
def c1 (x r : Fin 5) : Prop := x ∈ (![{3}, {0, 2, 4}, ∅, {2}, {0}] : Fin 5 → Finset (Fin 5)) r
instance dec1 : ∀ x r, Decidable (c1 x r) :=
  fun x r => inferInstanceAs (Decidable (x ∈ (![{3}, {0, 2, 4}, ∅, {2}, {0}] : Fin 5 → Finset (Fin 5)) r))
theorem accepted1 : checkPruning q1 c1 {0, 3, 4} [[4], [4]] =
    some {4} := by decide

def q2 : CRS (Fin 5) (Fin 5) :=
  { inputs := ![∅, ∅, {3}, {1}, {1, 3}], outputs := ![∅, {1, 4}, ∅, {3, 4}, {0, 3}], food := {0} }
def c2 (x r : Fin 5) : Prop := x ∈ (![{4}, ∅, {3, 4}, {0, 1}, {0, 3}] : Fin 5 → Finset (Fin 5)) r
instance dec2 : ∀ x r, Decidable (c2 x r) :=
  fun x r => inferInstanceAs (Decidable (x ∈ (![{4}, ∅, {3, 4}, {0, 1}, {0, 3}] : Fin 5 → Finset (Fin 5)) r))
theorem accepted2 : checkPruning q2 c2 {0, 1, 4} [[0, 1], [0], []] =
    some ∅ := by decide

def q3 : CRS (Fin 5) (Fin 5) :=
  { inputs := ![{0, 2}, {1, 4}, {2}, ∅, {0, 3}], outputs := ![∅, ∅, {1, 3}, ∅, {3}], food := {0} }
def c3 (x r : Fin 5) : Prop := x ∈ (![{1}, {2}, {1, 2}, ∅, {2}] : Fin 5 → Finset (Fin 5)) r
instance dec3 : ∀ x r, Decidable (c3 x r) :=
  fun x r => inferInstanceAs (Decidable (x ∈ (![{1}, {2}, {1, 2}, ∅, {2}] : Fin 5 → Finset (Fin 5)) r))
theorem accepted3 : checkPruning q3 c3 {0, 1, 4} [[], []] =
    some ∅ := by decide

def q4 : CRS (Fin 5) (Fin 5) :=
  { inputs := ![∅, {1, 2}, ∅, {2}, {4}], outputs := ![∅, {3}, {2, 4}, {1}, ∅], food := {0} }
def c4 (x r : Fin 5) : Prop := x ∈ (![{1}, {2, 4}, {1}, {0}, {1}] : Fin 5 → Finset (Fin 5)) r
instance dec4 : ∀ x r, Decidable (c4 x r) :=
  fun x r => inferInstanceAs (Decidable (x ∈ (![{1}, {2, 4}, {1}, {0}, {1}] : Fin 5 → Finset (Fin 5)) r))
theorem accepted4 : checkPruning q4 c4 {0, 2} [[0, 2], []] =
    some ∅ := by decide

def q5 : CRS (Fin 5) (Fin 5) :=
  { inputs := ![∅, ∅, {3}, {1, 2}, ∅], outputs := ![∅, {1}, {1, 4}, {0, 1}, {1, 4}], food := {0} }
def c5 (x r : Fin 5) : Prop := x ∈ (![{3}, ∅, {3}, {0, 4}, {0}] : Fin 5 → Finset (Fin 5)) r
instance dec5 : ∀ x r, Decidable (c5 x r) :=
  fun x r => inferInstanceAs (Decidable (x ∈ (![{3}, ∅, {3}, {0, 4}, {0}] : Fin 5 → Finset (Fin 5)) r))
theorem accepted5 : checkPruning q5 c5 {1} [[1], []] =
    some ∅ := by decide

def q6 : CRS (Fin 5) (Fin 5) :=
  { inputs := ![∅, ∅, ∅, {0, 2}, {2, 4}], outputs := ![{1, 2}, {2}, {1, 4}, {0}, {1}], food := {0} }
def c6 (x r : Fin 5) : Prop := x ∈ (![{0, 1, 3}, {1, 3, 4}, {3}, {1, 3, 4}, ∅] : Fin 5 → Finset (Fin 5)) r
instance dec6 : ∀ x r, Decidable (c6 x r) :=
  fun x r => inferInstanceAs (Decidable (x ∈ (![{0, 1, 3}, {1, 3, 4}, {3}, {1, 3, 4}, ∅] : Fin 5 → Finset (Fin 5)) r))
theorem accepted6 : checkPruning q6 c6 {0, 3, 4} [[0, 3], [0, 3]] =
    some {0, 3} := by decide

def q7 : CRS (Fin 5) (Fin 5) :=
  { inputs := ![∅, {1, 4}, ∅, {3}, ∅], outputs := ![∅, ∅, {0, 4}, ∅, ∅], food := {0} }
def c7 (x r : Fin 5) : Prop := x ∈ (![{1}, {2, 3}, {4}, {2}, {0, 4}] : Fin 5 → Finset (Fin 5)) r
instance dec7 : ∀ x r, Decidable (c7 x r) :=
  fun x r => inferInstanceAs (Decidable (x ∈ (![{1}, {2, 3}, {4}, {2}, {0, 4}] : Fin 5 → Finset (Fin 5)) r))
theorem accepted7 : checkPruning q7 c7 {0, 1, 3, 4} [[0, 4], [4]] =
    some {4} := by decide

end RAFQueryCompilation.CertificateFixtures
