import LeanPEP.GramPEP.UpperCertificateChecker

/-!
# D7: exact coverage of a full row family by a shorter submitted family

The omitted rows must be identically zero coefficient objects, not zero at a
particular primal point and not merely unused by one dual certificate. Both
maps are submitted: the inverse is partial and `none` explicitly declares an
omission. No default array access and no inferred completion.
-/
namespace LeanPEP.GramPEP.ZeroRowCoverage

@[ext] structure MapQ (small full : ℕ) where
  toFull : Fin small → Fin full
  fromFull : Fin full → Option (Fin small)

def checkMapQ {small full : ℕ} (a : MapQ small full) : Bool :=
  (List.finRange small).all (fun i => decide (a.fromFull (a.toFull i) = some i)) &&
    (List.finRange full).all (fun j => (List.finRange small).all
      (fun i => decide (a.fromFull j = some i → a.toFull i = j)))

theorem checkMapQ_eq_true_iff {small full : ℕ} (a : MapQ small full) :
    checkMapQ a = true ↔
      (∀ i, a.fromFull (a.toFull i) = some i) ∧
      (∀ j i, a.fromFull j = some i → a.toFull i = j) := by
  simp [checkMapQ, List.all_eq_true]
  intro _
  exact forall_congr' (fun _ =>
    forall_congr' (fun _ => Decidable.imp_iff_not_or.symm))

theorem toFull_injective {small full : ℕ} (a : MapQ small full)
    (ha : checkMapQ a = true) : Function.Injective a.toFull := by
  have h := ((checkMapQ_eq_true_iff a).mp ha).1
  intro i j hij
  have he := congrArg a.fromFull hij
  rw [h i, h j] at he
  exact Option.some.inj he

theorem omitted_iff {small full : ℕ} (a : MapQ small full)
    (ha : checkMapQ a = true) (j : Fin full) :
    a.fromFull j = none ↔ ¬ ∃ i, a.toFull i = j := by
  obtain ⟨hf, hb⟩ := (checkMapQ_eq_true_iff a).mp ha
  constructor
  · intro hn ⟨i, hi⟩
    have he := hf i
    rw [hi, hn] at he
    cases he
  · intro h
    cases he : a.fromFull j with
    | none => rfl
    | some i => exact False.elim (h ⟨i, hb j i he⟩)

/-- Every retained raw row is checked before any later coordinate/auxiliary
projection; omitted full rows must be complete zero polynomials. -/
def checkRowsQ {p m small full : ℕ} (a : MapQ small full)
    (xs : Fin small → LinearExprQ p m) (ys : Fin full → LinearExprQ p m) : Bool :=
  checkMapQ a &&
    ((List.finRange small).all (fun i => checkLinearExprEqQ (xs i) (ys (a.toFull i))) &&
      (List.finRange full).all (fun j =>
        if a.fromFull j = none then checkLinearExprEqQ (ys j) (LinearExprQ.zero p m) else true))

theorem checkRowsQ_eq_true_iff {p m small full : ℕ} (a : MapQ small full)
    (xs : Fin small → LinearExprQ p m) (ys : Fin full → LinearExprQ p m) :
    checkRowsQ a xs ys = true ↔ checkMapQ a = true ∧
      (∀ i, xs i = ys (a.toFull i)) ∧
      (∀ j, a.fromFull j = none → ys j = LinearExprQ.zero p m) := by
  simp [checkRowsQ, List.all_eq_true, checkLinearExprEqQ_eq_true_iff]
  intro _ _
  exact forall_congr' (fun _ => Decidable.imp_iff_not_or.symm)

/-- Pointwise equivalence, without PSD or any primal realizability assumption. -/
theorem feasible_iff {p m small full : ℕ} (a : MapQ small full)
    (xs : Fin small → LinearExprQ p m) (ys : Fin full → LinearExprQ p m)
    (ha : checkRowsQ a xs ys = true) (d : DataR (Fin p) m) :
    (∀ i, 0 ≤ (xs i).evalR d) ↔ ∀ j, 0 ≤ (ys j).evalR d := by
  obtain ⟨hm, he, hz⟩ := (checkRowsQ_eq_true_iff a xs ys).mp ha
  have hb := ((checkMapQ_eq_true_iff a).mp hm).2
  constructor
  · intro h j
    cases hj : a.fromFull j with
    | none => simp only [hz j hj, LinearExprQ.evalR_zero, le_refl]
    | some i =>
        rw [← hb j i hj, ← he i]
        exact h i
  · intro h i
    rw [he i]
    exact h (a.toFull i)

/-- ALL finite scalar upper-bound statements are equivalent. No attainment,
objective value, dual weights, or nonempty feasible set is assumed. -/
theorem finite_upper_equivalence {p m small full : ℕ} (a : MapQ small full)
    (xs : Fin small → LinearExprQ p m) (ys : Fin full → LinearExprQ p m)
    (ha : checkRowsQ a xs ys = true) (o : LinearExprQ p m) (B : ℝ) :
    (∀ d : DataR (Fin p) m, IsGramPosSemidef d.gram →
      (∀ i, 0 ≤ (xs i).evalR d) → o.evalR d ≤ B) ↔
    (∀ d : DataR (Fin p) m, IsGramPosSemidef d.gram →
      (∀ j, 0 ≤ (ys j).evalR d) → o.evalR d ≤ B) := by
  constructor
  · intro h d hG hy
    exact h d hG ((feasible_iff a xs ys ha d).mpr hy)
  · intro h d hG hx
    exact h d hG ((feasible_iff a xs ys ha d).mp hx)

end LeanPEP.GramPEP.ZeroRowCoverage
