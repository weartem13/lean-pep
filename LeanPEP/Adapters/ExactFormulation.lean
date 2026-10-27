import LeanPEP.GramPEP.ExternalBundle

/-!
# Exact source-list comparison and transport of certificates

A source candidate is not allowed to define its own expected formulation.
These small helpers compare full ordered lists (including their lengths) and
transport an existing certificate only after equality of models is proved.
The PSD, coefficient and upper certificate checkers are unchanged.
-/

namespace LeanPEP.Adapters.ExactFormulation

/-- Unlike zip-based comparisons, unequal lengths are always rejected. -/
def checkListQ {α : Type*} (cmp : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => cmp x y && checkListQ cmp xs ys
  | _, _ => false

theorem checkListQ_eq_true_iff {α : Type*} (cmp : α → α → Bool)
    (hcmp : ∀ a b, cmp a b = true ↔ a = b) (xs ys : List α) :
    checkListQ cmp xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [checkListQ]
  | cons x xs ih =>
      cases ys with
      | nil => simp [checkListQ]
      | cons y ys => simp [checkListQ, hcmp, ih]

end LeanPEP.Adapters.ExactFormulation

namespace LeanPEP.GramPEP

/-- Equality transport, not recompilation, reindexing, or certificate repair. -/
def UpperCertQ.rebind {p m : ℕ} {source target : ModelQ p m}
    (c : UpperCertQ source) (h : source = target) : UpperCertQ target :=
  h ▸ c

@[simp] theorem UpperCertQ.rebind_bound {p m : ℕ} {source target : ModelQ p m}
    (c : UpperCertQ source) (h : source = target) : (c.rebind h).bound = c.bound := by
  subst target
  rfl

@[simp] theorem UpperCertQ.rebind_objective {p m : ℕ} {source target : ModelQ p m}
    (c : UpperCertQ source) (h : source = target) : (c.rebind h).objective = c.objective := by
  subst target
  rfl

@[simp] theorem UpperCertQ.rebind_interpTerms {p m : ℕ} {source target : ModelQ p m}
    (c : UpperCertQ source) (h : source = target) : (c.rebind h).interpTerms = c.interpTerms := by
  subst target
  rfl

@[simp] theorem UpperCertQ.rebind_dualMatrix {p m : ℕ} {source target : ModelQ p m}
    (c : UpperCertQ source) (h : source = target) : (c.rebind h).dualMatrix = c.dualMatrix := by
  subst target
  rfl

/-- Original checker acceptance is preserved by proved model equality. -/
theorem checkUpperCertQ_rebind {p m : ℕ} {source target : ModelQ p m}
    (c : UpperCertQ source) (h : source = target) :
    checkUpperCertQ (c.rebind h) = checkUpperCertQ c := by
  subst target
  rfl

end LeanPEP.GramPEP
