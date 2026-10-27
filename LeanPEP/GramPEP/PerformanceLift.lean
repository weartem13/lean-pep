import LeanPEP.GramPEP.RowNormalization

/-!
# D6: one auxiliary scalar performance variable

Values are [tau, old values...]; the vector/Gram basis does NOT change.
The maximized variable satisfies tau <= objective. This is a hypograph
constraint, not objective <= tau. Substitution sets tau=objective, NOT tau=0.
The identities hold for every coefficient, including nonsymmetric Gram terms.
-/
namespace LeanPEP.GramPEP.PerformanceLift

open scoped BigOperators

/-- Shift only scalar value slots. No new Gram vector is introduced. -/
def embedExprQ {p m : ℕ} (e : LinearExprQ p m) : LinearExprQ (p+1) m :=
  { constCoeff := e.constCoeff
    valueCoeff := Fin.cons 0 e.valueCoeff
    gramCoeff := e.gramCoeff }

def tauExprQ (p m : ℕ) : LinearExprQ (p+1) m :=
  { constCoeff := 0
    valueCoeff := Fin.cons 1 (fun _ => 0)
    gramCoeff := 0 }

def tailExprQ {p m : ℕ} (e : LinearExprQ (p+1) m) : LinearExprQ p m :=
  { constCoeff := e.constCoeff
    valueCoeff := fun i => e.valueCoeff i.succ
    gramCoeff := e.gramCoeff }

/-- Complete affine substitution, including the auxiliary coefficient's
contribution to the constant and EVERY Gram entry of the metric. -/
def substituteQ {p m : ℕ} (o : LinearExprQ p m) (e : LinearExprQ (p+1) m) :
    LinearExprQ p m :=
  LinearExprQ.add (tailExprQ e) (LinearExprQ.scale (e.valueCoeff 0) o)

def linkExprQ {p m : ℕ} (o : LinearExprQ p m) : LinearExprQ (p+1) m :=
  LinearExprQ.sub (embedExprQ o) (tauExprQ p m)

@[simp] theorem substitute_embed {p m : ℕ} (o e : LinearExprQ p m) :
    substituteQ o (embedExprQ e) = e := by
  apply LinearExprQ.ext
  · simp [substituteQ, embedExprQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]
  · funext i; simp [substituteQ, embedExprQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]
  · funext i j; simp [substituteQ, embedExprQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]

@[simp] theorem substitute_tau {p m : ℕ} (o : LinearExprQ p m) :
    substituteQ o (tauExprQ p m) = o := by
  apply LinearExprQ.ext
  · simp [substituteQ, tauExprQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]
  · funext i; simp [substituteQ, tauExprQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]
  · funext i j; simp [substituteQ, tauExprQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]

@[simp] theorem substitute_add {p m : ℕ} (o : LinearExprQ p m) (e f : LinearExprQ (p+1) m) :
    substituteQ o (LinearExprQ.add e f) = LinearExprQ.add (substituteQ o e) (substituteQ o f) := by
  apply LinearExprQ.ext
  · dsimp [substituteQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]; ring
  · funext i; dsimp [substituteQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]; ring
  · funext i j; dsimp [substituteQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]; ring

@[simp] theorem substitute_scale {p m : ℕ} (o : LinearExprQ p m) (a : ℚ) (e : LinearExprQ (p+1) m) :
    substituteQ o (LinearExprQ.scale a e) = LinearExprQ.scale a (substituteQ o e) := by
  apply LinearExprQ.ext
  · dsimp [substituteQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]; ring
  · funext i; dsimp [substituteQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]; ring
  · funext i j; dsimp [substituteQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale]; ring

@[simp] theorem substitute_neg {p m : ℕ} (o : LinearExprQ p m) (e : LinearExprQ (p+1) m) :
    substituteQ o (LinearExprQ.neg e) = LinearExprQ.neg (substituteQ o e) := by
  apply LinearExprQ.ext
  · dsimp [substituteQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale, LinearExprQ.neg]; ring
  · funext i; dsimp [substituteQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale, LinearExprQ.neg]; ring
  · funext i j; dsimp [substituteQ, tailExprQ, LinearExprQ.add, LinearExprQ.scale, LinearExprQ.neg]; ring

@[simp] theorem substitute_zero {p m : ℕ} (o : LinearExprQ p m) :
    substituteQ o (LinearExprQ.zero (p+1) m) = LinearExprQ.zero p m := by
  apply LinearExprQ.ext
  · simp [substituteQ, tailExprQ, LinearExprQ.zero, LinearExprQ.add, LinearExprQ.scale]
  · funext i; simp [substituteQ, tailExprQ, LinearExprQ.zero, LinearExprQ.add, LinearExprQ.scale]
  · funext i j; simp [substituteQ, tailExprQ, LinearExprQ.zero, LinearExprQ.add, LinearExprQ.scale]

@[simp] theorem substitute_const {p m : ℕ} (o : LinearExprQ p m) (b : ℚ) :
    substituteQ o (LinearExprQ.const (p+1) m b) = LinearExprQ.const p m b := by
  apply LinearExprQ.ext
  · simp [substituteQ, tailExprQ, LinearExprQ.const, LinearExprQ.add, LinearExprQ.scale]
  · funext i; simp [substituteQ, tailExprQ, LinearExprQ.const, LinearExprQ.add, LinearExprQ.scale]
  · funext i j; simp [substituteQ, tailExprQ, LinearExprQ.const, LinearExprQ.add, LinearExprQ.scale]

@[simp] theorem substitute_gramPairing {p m : ℕ} (o : LinearExprQ p m) (G : Gram m ℚ) :
    substituteQ o (LinearExprQ.gramPairing G) = LinearExprQ.gramPairing G := by
  apply LinearExprQ.ext
  · simp [substituteQ, tailExprQ, LinearExprQ.gramPairing, LinearExprQ.add, LinearExprQ.scale]
  · funext i; simp [substituteQ, tailExprQ, LinearExprQ.gramPairing, LinearExprQ.add, LinearExprQ.scale]
  · funext i j; simp [substituteQ, tailExprQ, LinearExprQ.gramPairing, LinearExprQ.add, LinearExprQ.scale]

@[simp] theorem substitute_link {p m : ℕ} (o : LinearExprQ p m) :
    substituteQ o (linkExprQ o) = LinearExprQ.zero p m := by
  simp only [linkExprQ, LinearExprQ.sub, substitute_add, substitute_embed, substitute_neg, substitute_tau]
  apply LinearExprQ.ext
  · simp [LinearExprQ.add, LinearExprQ.neg, LinearExprQ.zero]
  · funext i; simp [LinearExprQ.add, LinearExprQ.neg, LinearExprQ.zero]
  · funext i j; simp [LinearExprQ.add, LinearExprQ.neg, LinearExprQ.zero]

theorem substitute_orient {p m : ℕ} (o : LinearExprQ p m) (sense : RowNormalization.SenseQ)
    (e : LinearExprQ (p+1) m) :
    substituteQ o (RowNormalization.orientExprQ sense e) =
      RowNormalization.orientExprQ sense (substituteQ o e) := by
  cases sense <;> simp [RowNormalization.orientExprQ]

theorem embed_orient {p m : ℕ} (sense : RowNormalization.SenseQ) (e : LinearExprQ p m) :
    embedExprQ (RowNormalization.orientExprQ sense e) =
      RowNormalization.orientExprQ sense (embedExprQ e) := by
  cases sense with
  | geZero => rfl
  | leZero =>
      apply LinearExprQ.ext
      · rfl
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [embedExprQ, RowNormalization.orientExprQ, LinearExprQ.neg]
      · rfl

@[simp] theorem expr_scale_zero {p m : ℕ} (a : ℚ) :
    LinearExprQ.scale a (LinearExprQ.zero p m) = LinearExprQ.zero p m := by
  apply LinearExprQ.ext
  · simp [LinearExprQ.scale, LinearExprQ.zero]
  · funext i; simp [LinearExprQ.scale, LinearExprQ.zero]
  · funext i j; simp [LinearExprQ.scale, LinearExprQ.zero]

@[simp] theorem expr_zero_add {p m : ℕ} (e : LinearExprQ p m) :
    LinearExprQ.add (LinearExprQ.zero p m) e = e := by
  apply LinearExprQ.ext
  · simp [LinearExprQ.add, LinearExprQ.zero]
  · funext i; simp [LinearExprQ.add, LinearExprQ.zero]
  · funext i j; simp [LinearExprQ.add, LinearExprQ.zero]

noncomputable def extendDataR {p m : ℕ} (d : DataR (Fin p) m) (t : ℝ) : DataR (Fin (p+1)) m :=
  { gram := d.gram
    position := Fin.cons 0 d.position
    gradient := Fin.cons 0 d.gradient
    value := Fin.cons t d.value }

@[simp] theorem eval_embed {p m : ℕ} (e : LinearExprQ p m) (d : DataR (Fin p) m) (t : ℝ) :
    (embedExprQ e).evalR (extendDataR d t) = e.evalR d := by
  simp [LinearExprQ.evalR, embedExprQ, extendDataR, Fin.sum_univ_succ]

@[simp] theorem eval_tau {p m : ℕ} (d : DataR (Fin p) m) (t : ℝ) :
    (tauExprQ p m).evalR (extendDataR d t) = t := by
  simp [LinearExprQ.evalR, tauExprQ, extendDataR, Fin.sum_univ_succ]

/-- Exact substitution semantics; d need not be symmetric, PSD or feasible. -/
theorem eval_substitute {p m : ℕ} (o : LinearExprQ p m) (e : LinearExprQ (p+1) m)
    (d : DataR (Fin p) m) :
    (substituteQ o e).evalR d = e.evalR (extendDataR d (o.evalR d)) := by
  rw [substituteQ, LinearExprQ.evalR_add, LinearExprQ.evalR_scale]
  simp only [LinearExprQ.evalR, tailExprQ, extendDataR, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  ring

@[simp] theorem eval_link {p m : ℕ} (o : LinearExprQ p m) (d : DataR (Fin p) m) (t : ℝ) :
    (linkExprQ o).evalR (extendDataR d t) = o.evalR d - t := by
  simp [linkExprQ]

end LeanPEP.GramPEP.PerformanceLift
