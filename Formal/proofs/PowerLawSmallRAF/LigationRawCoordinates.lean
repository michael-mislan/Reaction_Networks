import proofs.PowerLawSmallRAF.LigationStaticHistoryLaw

namespace PowerLawSmallRAF
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 100000

def LigationRawCoordinate : List LigationWord → Type
  | [] => Empty
  | w :: rest => Sum (ligationCuts w) (LigationRawCoordinate rest)

instance ligationRawCoordinateDecidableEq : (words : List LigationWord) → DecidableEq (LigationRawCoordinate words)
  | [] => inferInstanceAs (DecidableEq Empty)
  | _ :: rest =>
      letI := ligationRawCoordinateDecidableEq rest
      inferInstanceAs (DecidableEq (Sum _ (LigationRawCoordinate rest)))

instance ligationRawCoordinateFintype : (words : List LigationWord) → Fintype (LigationRawCoordinate words)
  | [] => inferInstanceAs (Fintype Empty)
  | _ :: rest =>
      letI := ligationRawCoordinateFintype rest
      inferInstanceAs (Fintype (Sum _ (LigationRawCoordinate rest)))

def ligationRawDecode : (words : List LigationWord) →
    (LigationRawCoordinate words → Bool) → LigationRawConfiguration words
  | [], _ => ()
  | _ :: rest, B => ((fun i => B (.inl i)), ligationRawDecode rest (fun i => B (.inr i)))

def ligationRawRead : (words : List LigationWord) →
    LigationRawConfiguration words → LigationRawCoordinate words → Bool
  | [], _, i => nomatch i
  | _ :: _, cfg, .inl i => cfg.1 i
  | _ :: rest, cfg, .inr i => ligationRawRead rest cfg.2 i

theorem ligationRawDecode_read (words : List LigationWord) (cfg : LigationRawConfiguration words) :
    ligationRawDecode words (ligationRawRead words cfg) = cfg := by
  induction words with
  | nil => cases cfg; rfl
  | cons w rest ih =>
      rcases cfg with ⟨A,B⟩
      change (A, ligationRawDecode rest (ligationRawRead rest B)) = (A,B)
      rw [ih]

theorem ligationRawRead_decode (words : List LigationWord) (B : LigationRawCoordinate words → Bool) :
    ligationRawRead words (ligationRawDecode words B) = B := by
  induction words with
  | nil => funext i; exact Empty.elim i
  | cons w rest ih =>
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact congrFun (ih (fun j => B (.inr j))) i

def ligationRawCoordinateEquiv (words : List LigationWord) :
    (LigationRawCoordinate words → Bool) ≃ LigationRawConfiguration words where
  toFun := ligationRawDecode words
  invFun := ligationRawRead words
  left_inv := ligationRawRead_decode words
  right_inv := ligationRawDecode_read words

theorem ligationRawDecode_weight (p : ℝ) (words : List LigationWord)
    (B : LigationRawCoordinate words → Bool) :
    bernoulliFullRowWeight p B = ligationRawWeight p words (ligationRawDecode words B) := by
  induction words with
  | nil => simp [bernoulliFullRowWeight, LigationRawCoordinate, ligationRawWeight]
  | cons w rest ih =>
      change (∏ i : Sum (ligationCuts w) (LigationRawCoordinate rest), bernoulliBitWeight p (B i)) =
        bernoulliFullRowWeight p (fun i => B (.inl i)) *
          ligationRawWeight p rest (ligationRawDecode rest (fun i => B (.inr i)))
      rw [Fintype.prod_sum_type]
      rw [← ih]
      rfl

theorem ligationRawDecode_expectation (p : ℝ) (words : List LigationWord)
    (F : LigationRawConfiguration words → ℝ) :
    (∑ B : LigationRawCoordinate words → Bool,
      bernoulliFullRowWeight p B * F (ligationRawDecode words B)) =
      ∑ cfg : LigationRawConfiguration words, ligationRawWeight p words cfg * F cfg := by
  apply Fintype.sum_equiv (ligationRawCoordinateEquiv words)
  intro B
  rw [ligationRawDecode_weight]
  rfl

def ligationRawCoordinateWord : (words : List LigationWord) → LigationRawCoordinate words → LigationWord
  | [], i => nomatch i
  | w :: _, .inl _ => w
  | _ :: rest, .inr i => ligationRawCoordinateWord rest i

def ligationRawCoordinateCut : (words : List LigationWord) → (i : LigationRawCoordinate words) →
    ligationCuts (ligationRawCoordinateWord words i)
  | [], i => nomatch i
  | _ :: _, .inl i => i
  | _ :: rest, .inr i => ligationRawCoordinateCut rest i

theorem ligationRawCoordinateWord_mem (words : List LigationWord) (i : LigationRawCoordinate words) :
    ligationRawCoordinateWord words i ∈ words := by
  induction words with
  | nil => exact Empty.elim i
  | cons w rest ih =>
      cases i with
      | inl i => exact List.mem_cons_self ..
      | inr i => exact List.mem_cons_of_mem w (ih i)

theorem ligationRawCoordinate_ext (words : List LigationWord) (hnd : words.Nodup)
    (i j : LigationRawCoordinate words)
    (hw : ligationRawCoordinateWord words i = ligationRawCoordinateWord words j)
    (hc : (ligationRawCoordinateCut words i).val = (ligationRawCoordinateCut words j).val) : i = j := by
  induction words with
  | nil => exact Empty.elim i
  | cons w rest ih =>
      obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hnd
      cases i with
      | inl i =>
          cases j with
          | inl j => exact congrArg Sum.inl (Subtype.ext hc)
          | inr j =>
              exfalso
              apply hnot
              change w = ligationRawCoordinateWord rest j at hw
              rw [hw]
              exact ligationRawCoordinateWord_mem rest j
      | inr i =>
          cases j with
          | inl j =>
              exfalso
              apply hnot
              change ligationRawCoordinateWord rest i = w at hw
              rw [← hw]
              exact ligationRawCoordinateWord_mem rest i
          | inr j => exact congrArg Sum.inr (ih hrest i j hw hc)

end
end PowerLawSmallRAF
