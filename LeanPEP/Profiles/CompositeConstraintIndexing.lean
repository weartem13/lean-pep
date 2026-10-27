import LeanPEP.Profiles.Composite

/-!
# Row-major lookup for component-local constraint lists

The lemmas expose actual list elements. They do not reconstruct a second
model, assume an ordering convention, or silently default out-of-range indices.
The optional lookup is used only in the proof; public certificate indices
remain the original bounded `Fin` indices.
-/

namespace LeanPEP.Profiles.Composite

/-- A generic rectangular row-major list, exactly the compiler's traversal. -/
def rowMajorList {α : Type*} (r c : ℕ) (f : Fin r → Fin c → α) : List α :=
  (List.finRange r).flatMap fun i => (List.finRange c).map (f i)

@[simp] theorem rowMajorList_zero {α : Type*} (c : ℕ) (f : Fin 0 → Fin c → α) :
    rowMajorList 0 c f = [] := by simp [rowMajorList]

theorem rowMajorList_succ {α : Type*} (r c : ℕ) (f : Fin (r + 1) → Fin c → α) :
    rowMajorList (r + 1) c f =
      (List.finRange c).map (f 0) ++ rowMajorList r c (fun i => f i.succ) := by
  simp only [rowMajorList, List.finRange_succ, List.flatMap_cons, List.flatMap_map]

@[simp] theorem length_rowMajorList {α : Type*} :
    ∀ (r c : ℕ) (f : Fin r → Fin c → α), (rowMajorList r c f).length = r * c := by
  intro r
  induction r with
  | zero => intro c f; simp
  | succ r ih =>
      intro c f
      rw [rowMajorList_succ, List.length_append, List.length_map, List.length_finRange, ih]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

/-- Every bounded pair is found at i*c+j, even when the two dimensions differ. -/
theorem rowMajorList_getElem? {α : Type*} :
    ∀ (r c : ℕ) (f : Fin r → Fin c → α) (i : Fin r) (j : Fin c),
      (rowMajorList r c f)[i.val * c + j.val]? = some (f i j) := by
  intro r
  induction r with
  | zero => intro c f i j; exact Fin.elim0 i
  | succ r ih =>
      intro c f i j
      refine Fin.cases ?_ (fun k => ?_) i
      · rw [rowMajorList_succ]
        simp only [Fin.val_zero, zero_mul, zero_add]
        rw [List.getElem?_append_left (by simpa using j.isLt)]
        simp [j.isLt]
      · rw [rowMajorList_succ]
        have hge : ((List.finRange c).map (f 0)).length ≤ k.succ.val * c + j.val := by
          simp only [List.length_map, List.length_finRange, Fin.val_succ, Nat.add_mul,
            Nat.one_mul]
          omega
        rw [List.getElem?_append_right hge]
        simp only [List.length_map, List.length_finRange, Fin.val_succ, Nat.add_mul,
          Nat.one_mul]
        have he : k.val * c + c + j.val - c = k.val * c + j.val := by omega
        rw [he]
        exact ih c (fun i => f i.succ) k j

end LeanPEP.Profiles.Composite
