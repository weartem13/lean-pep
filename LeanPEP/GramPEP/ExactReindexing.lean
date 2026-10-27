import LeanPEP.Profiles.Composite
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# D4: explicitly checked finite reindexings

`toSource i` is the source storage index of canonical index `i`;
`toCanonical j` is the canonical index of source storage index `j`.
Both arrays are untrusted functions until `checkQ` has verified both inverse
laws. No default lookup, deletion, sorting, matrix symmetrization, or solver
computation is involved. Zero-dimensional arrays are allowed in this layer.
-/

namespace LeanPEP.GramPEP.ExactReindexing

open scoped BigOperators

@[ext] structure IndexMapQ (k : ℕ) where
  toSource : Fin k → Fin k
  toCanonical : Fin k → Fin k

def IndexMapQ.symm {k : ℕ} (p : IndexMapQ k) : IndexMapQ k :=
  { toSource := p.toCanonical, toCanonical := p.toSource }

def IndexMapQ.identity (k : ℕ) : IndexMapQ k :=
  { toSource := id, toCanonical := id }

def checkQ {k : ℕ} (p : IndexMapQ k) : Bool :=
  (List.finRange k).all (fun i => decide (p.toCanonical (p.toSource i) = i)) &&
    (List.finRange k).all (fun j => decide (p.toSource (p.toCanonical j) = j))

theorem checkQ_eq_true_iff {k : ℕ} (p : IndexMapQ k) :
    checkQ p = true ↔
      (∀ i, p.toCanonical (p.toSource i) = i) ∧
      (∀ j, p.toSource (p.toCanonical j) = j) := by
  simp [checkQ, List.all_eq_true]

theorem checkQ_identity (k : ℕ) : checkQ (IndexMapQ.identity k) = true :=
  (checkQ_eq_true_iff _).mpr ⟨fun _ => rfl, fun _ => rfl⟩

theorem checkQ_symm {k : ℕ} (p : IndexMapQ k) (hp : checkQ p = true) :
    checkQ p.symm = true := by
  rcases (checkQ_eq_true_iff p).mp hp with ⟨hl, hr⟩
  exact (checkQ_eq_true_iff p.symm).mpr ⟨hr, hl⟩

/-- Bijection is derived from the two checked inverse arrays, not postulated. -/
def checkedEquiv {k : ℕ} (p : IndexMapQ k) (hp : checkQ p = true) : Fin k ≃ Fin k :=
  { toFun := p.toSource
    invFun := p.toCanonical
    left_inv := ((checkQ_eq_true_iff p).mp hp).1
    right_inv := ((checkQ_eq_true_iff p).mp hp).2 }

def vec {k : ℕ} {α : Type*} (p : IndexMapQ k) (v : Fin k → α) : Fin k → α :=
  fun i => v (p.toSource i)

def matrix {k : ℕ} {α : Type*} (p : IndexMapQ k) (A : Fin k → Fin k → α) :
    Fin k → Fin k → α := fun i j => A (p.toSource i) (p.toSource j)

theorem vec_roundtrip {k : ℕ} {α : Type*} (p : IndexMapQ k) (hp : checkQ p = true)
    (v : Fin k → α) : vec p.symm (vec p v) = v := by
  funext i
  exact congrArg v (((checkQ_eq_true_iff p).mp hp).2 i)

theorem matrix_roundtrip {k : ℕ} {α : Type*} (p : IndexMapQ k) (hp : checkQ p = true)
    (A : Fin k → Fin k → α) : matrix p.symm (matrix p A) = A := by
  have hi := ((checkQ_eq_true_iff p).mp hp).2
  funext i j
  change A (p.toSource (p.toCanonical i)) (p.toSource (p.toCanonical j)) = A i j
  rw [hi i, hi j]

/-- Scalar coefficients gather at canonical-to-source indices. -/
def expr {p m : ℕ} (pv : IndexMapQ p) (pb : IndexMapQ m) (e : LinearExprQ p m) :
    LinearExprQ p m :=
  { constCoeff := e.constCoeff
    valueCoeff := vec pv e.valueCoeff
    gramCoeff := matrix pb e.gramCoeff }

/-- Value references, unlike coefficient arrays, use source-to-canonical indices. -/
def sample {p m : ℕ} (pv : IndexMapQ p) (pb : IndexMapQ m)
    (s : Profiles.Composite.SampleQ p m) : Profiles.Composite.SampleQ p m :=
  { valueIndex := pv.toCanonical s.valueIndex
    position := vec pb s.position
    oracle := vec pb s.oracle }

theorem expr_roundtrip {p m : ℕ} (pv : IndexMapQ p) (pb : IndexMapQ m)
    (hv : checkQ pv = true) (hb : checkQ pb = true) (e : LinearExprQ p m) :
    expr pv.symm pb.symm (expr pv pb e) = e := by
  cases e with
  | mk c v G =>
      change LinearExprQ.mk c (vec pv.symm (vec pv v)) (matrix pb.symm (matrix pb G)) =
        LinearExprQ.mk c v G
      rw [vec_roundtrip pv hv, matrix_roundtrip pb hb]

theorem sample_roundtrip {p m : ℕ} (pv : IndexMapQ p) (pb : IndexMapQ m)
    (hv : checkQ pv = true) (hb : checkQ pb = true) (s : Profiles.Composite.SampleQ p m) :
    sample pv.symm pb.symm (sample pv pb s) = s := by
  have hi := ((checkQ_eq_true_iff pv).mp hv).2
  cases s with
  | mk vi pos ora =>
      change Profiles.Composite.SampleQ.mk (pv.toSource (pv.toCanonical vi))
        (vec pb.symm (vec pb pos)) (vec pb.symm (vec pb ora)) =
        Profiles.Composite.SampleQ.mk vi pos ora
      rw [hi vi, vec_roundtrip pb hb pos, vec_roundtrip pb hb ora]

def factor {m : ℕ} (pb : IndexMapQ m) (t : RankOneFactorQ m) : RankOneFactorQ m :=
  { weight := t.weight, vector := vec pb t.vector }

def psdFactor {m : ℕ} (pb : IndexMapQ m) (f : PSDFactorCertQ m) : PSDFactorCertQ m :=
  { factors := f.factors.map (factor pb) }

/-- No invertibility assumption is needed for this entrywise identity. -/
theorem factorGram_entry {m : ℕ} (pb : IndexMapQ m) (fs : List (RankOneFactorQ m))
    (i j : Fin m) :
    factorGramQ (fs.map (factor pb)) i j =
      factorGramQ fs (pb.toSource i) (pb.toSource j) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      change f.weight * f.vector (pb.toSource i) * f.vector (pb.toSource j) +
        factorGramQ (fs.map (factor pb)) i j =
        f.weight * f.vector (pb.toSource i) * f.vector (pb.toSource j) +
        factorGramQ fs (pb.toSource i) (pb.toSource j)
      rw [ih]

theorem factorGram_reindex {m : ℕ} (pb : IndexMapQ m) (fs : List (RankOneFactorQ m)) :
    factorGramQ (fs.map (factor pb)) = matrix pb (factorGramQ fs) := by
  funext i j
  exact factorGram_entry pb fs i j

theorem sum_reindex {k : ℕ} {α : Type*} [AddCommMonoid α]
    (p : IndexMapQ k) (hp : checkQ p = true) (v : Fin k → α) :
    (∑ i, v (p.toSource i)) = ∑ i, v i :=
  (checkedEquiv p hp).sum_comp v

/-- Reindex BOTH the coefficient expression and its data for semantic transport.
This is permutation-only, not D3's rectangular origin elimination. -/
noncomputable def dataR {p m : ℕ} (pv : IndexMapQ p) (pb : IndexMapQ m)
    (d : DataR (Fin p) m) : DataR (Fin p) m :=
  { value := vec pv d.value
    gram := matrix pb d.gram
    position := fun i => vec pb (d.position (pv.toSource i))
    gradient := fun i => vec pb (d.gradient (pv.toSource i)) }

theorem evalR_reindex {p m : ℕ} (pv : IndexMapQ p) (pb : IndexMapQ m)
    (hv : checkQ pv = true) (hb : checkQ pb = true)
    (e : LinearExprQ p m) (d : DataR (Fin p) m) :
    (expr pv pb e).evalR (dataR pv pb d) = e.evalR d := by
  have hvalue := sum_reindex pv hv (fun i => (e.valueCoeff i : ℝ) * d.value i)
  have hgram :
      (∑ i, ∑ j, (e.gramCoeff (pb.toSource i) (pb.toSource j) : ℝ) *
        d.gram (pb.toSource i) (pb.toSource j)) =
      ∑ i, ∑ j, (e.gramCoeff i j : ℝ) * d.gram i j := by
    calc
      _ = ∑ i, ∑ j, (e.gramCoeff (pb.toSource i) j : ℝ) * d.gram (pb.toSource i) j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact sum_reindex pb hb (fun j => (e.gramCoeff (pb.toSource i) j : ℝ) *
          d.gram (pb.toSource i) j)
      _ = _ := sum_reindex pb hb (fun i => ∑ j, (e.gramCoeff i j : ℝ) * d.gram i j)
  change (e.constCoeff : ℝ) +
      (∑ i, (e.valueCoeff (pv.toSource i) : ℝ) * d.value (pv.toSource i)) +
      (∑ i, ∑ j, (e.gramCoeff (pb.toSource i) (pb.toSource j) : ℝ) *
        d.gram (pb.toSource i) (pb.toSource j)) =
      (e.constCoeff : ℝ) + (∑ i, (e.valueCoeff i : ℝ) * d.value i) +
        (∑ i, ∑ j, (e.gramCoeff i j : ℝ) * d.gram i j)
  rw [hvalue, hgram]

end LeanPEP.GramPEP.ExactReindexing
