import LeanPEP.Profiles.Composite
import LeanPEP.GramPEP.Coordinate

/-!
# D3: exact removal and restoration of a translation-origin coordinate

Native basis: `[origin, initialPoint, remainingVectors...]`.
Centered basis: `[initialPoint-origin, remainingVectors...]`.
The maps are rectangular: setting the origin to zero is a section, NOT an
invertible change of basis on the whole native vector space. Coefficient
round trips are therefore an essential guard in the source adapter.
-/

namespace LeanPEP.GramPEP.OriginCoordinates

open scoped BigOperators

/-- Coefficients after evaluating the native origin vector at zero. -/
def restrictVec {m : ℕ} {K : Type*} (v : VecExpr (m+1) K) : VecExpr m K :=
  fun i => v i.succ

/-- A centered vector in native coordinates; `a` is the displacement slot. -/
def liftVecQ {m : ℕ} (a : Fin m) (v : VecExpr m ℚ) : VecExpr (m+1) ℚ :=
  Fin.cons (-v a) v

/-- A POINT, unlike an oracle vector, includes one copy of the origin. -/
def liftPositionQ {m : ℕ} (a : Fin m) (v : VecExpr m ℚ) : VecExpr (m+1) ℚ :=
  Fin.cons (1-v a) v

@[simp] theorem restrict_liftVecQ {m : ℕ} (a : Fin m) (v : VecExpr m ℚ) :
    restrictVec (liftVecQ a v) = v := rfl

@[simp] theorem restrict_liftPositionQ {m : ℕ} (a : Fin m) (v : VecExpr m ℚ) :
    restrictVec (liftPositionQ a v) = v := rfl

/-- Principal block, for either a primal Gram or a dual coefficient matrix.
The distinction between these two roles is maintained by the caller. -/
def restrictGram {m : ℕ} {K : Type*} (G : Gram (m+1) K) : Gram m K :=
  fun i j => G i.succ j.succ

/-- Exact coefficient congruence `C^T S C`, including BOTH cross blocks. -/
def liftGramQ {m : ℕ} (a : Fin m) (S : Gram m ℚ) : Gram (m+1) ℚ :=
  Fin.cons (Fin.cons (S a a) (fun j => -S a j))
    (fun i => Fin.cons (-S i a) (S i))

@[simp] theorem restrict_liftGramQ {m : ℕ} (a : Fin m) (S : Gram m ℚ) :
    restrictGram (liftGramQ a S) = S := rfl

def restrictExprQ {p m : ℕ} (e : LinearExprQ p (m+1)) : LinearExprQ p m :=
  { constCoeff := e.constCoeff
    valueCoeff := e.valueCoeff
    gramCoeff := restrictGram e.gramCoeff }

def liftExprQ {p m : ℕ} (a : Fin m) (e : LinearExprQ p m) : LinearExprQ p (m+1) :=
  { constCoeff := e.constCoeff
    valueCoeff := e.valueCoeff
    gramCoeff := liftGramQ a e.gramCoeff }

@[simp] theorem restrict_liftExprQ {p m : ℕ} (a : Fin m) (e : LinearExprQ p m) :
    restrictExprQ (liftExprQ a e) = e := by cases e; rfl

def restrictSampleQ {p m : ℕ} (s : Profiles.Composite.SampleQ p (m+1)) :
    Profiles.Composite.SampleQ p m :=
  { valueIndex := s.valueIndex
    position := restrictVec s.position
    oracle := restrictVec s.oracle }

def liftSampleQ {p m : ℕ} (a : Fin m) (s : Profiles.Composite.SampleQ p m) :
    Profiles.Composite.SampleQ p (m+1) :=
  { valueIndex := s.valueIndex
    position := liftPositionQ a s.position
    oracle := liftVecQ a s.oracle }

@[simp] theorem restrict_liftSampleQ {p m : ℕ} (a : Fin m)
    (s : Profiles.Composite.SampleQ p m) :
    restrictSampleQ (liftSampleQ a s) = s := by cases s; rfl

/-- `centerMapQ * nativeBasis = centeredBasis`. -/
def centerMapQ {m : ℕ} (a : Fin m) : Matrix (Fin m) (Fin (m+1)) ℚ :=
  fun i => liftVecQ a (standardBasisExpr i)

/-- `sectionMapQ * centeredBasis = [0, centeredBasis...]`. -/
def sectionMapQ (m : ℕ) : Matrix (Fin (m+1)) (Fin m) ℚ :=
  Fin.cons (fun _ => 0) (fun i => standardBasisExpr i)

theorem center_section_entry {m : ℕ} (a : Fin m) (i j : Fin m) :
    (∑ k, centerMapQ a i k * sectionMapQ m k j) = if i = j then 1 else 0 := by
  classical
  simp [centerMapQ, sectionMapQ, liftVecQ, standardBasisExpr, Fin.sum_univ_succ,
    eq_comm]

/-- The specialized native lift is exactly multiplication by the center map. -/
theorem liftVecQ_eq_center_combination {m : ℕ} (a : Fin m) (v : VecExpr m ℚ)
    (k : Fin (m+1)) :
    liftVecQ a v k = ∑ i, v i * centerMapQ a i k := by
  classical
  refine Fin.cases ?_ (fun k => ?_) k <;>
    simp [centerMapQ, liftVecQ, standardBasisExpr, mul_ite, mul_neg, Finset.sum_neg_distrib, eq_comm]

/-- Restriction is multiplication by the fixed zero-origin section. -/
theorem restrictVec_eq_section_combination {m : ℕ} (v : VecExpr (m+1) ℚ)
    (k : Fin m) :
    restrictVec v k = ∑ i, v i * sectionMapQ m i k := by
  classical
  simp [restrictVec, sectionMapQ, standardBasisExpr, Fin.sum_univ_succ, mul_ite, eq_comm]

/-- Full coefficient congruence, not a symmetric-part or diagonal-only test. -/
theorem liftGramQ_eq_congruence {m : ℕ} (a : Fin m) (S : Gram m ℚ)
    (i j : Fin (m+1)) :
    liftGramQ a S i j = ∑ r, ∑ t, centerMapQ a r i * S r t * centerMapQ a t j := by
  classical
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [liftGramQ, centerMapQ, liftVecQ, standardBasisExpr,
        ite_mul, mul_ite, neg_mul, mul_neg, Finset.sum_neg_distrib, eq_comm]
  · refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [liftGramQ, centerMapQ, liftVecQ, standardBasisExpr,
        ite_mul, mul_ite, neg_mul, mul_neg, Finset.sum_neg_distrib, eq_comm]

theorem restrictGram_eq_congruence {m : ℕ} (S : Gram (m+1) ℚ) (i j : Fin m) :
    restrictGram S i j = ∑ r, ∑ t, sectionMapQ m r i * S r t * sectionMapQ m t j := by
  classical
  simp [restrictGram, sectionMapQ, standardBasisExpr, Fin.sum_univ_succ,
    ite_mul, mul_ite, eq_comm]

/-- The reverse product is NOT the identity: the origin direction is removed. -/
theorem section_center_origin {m : ℕ} (a : Fin m) :
    (∑ i, sectionMapQ m 0 i * centerMapQ a i 0) = 0 := by
  simp [sectionMapQ]

def restrictFactorQ {m : ℕ} (f : RankOneFactorQ (m+1)) : RankOneFactorQ m :=
  { weight := f.weight, vector := restrictVec f.vector }

def restrictPSDFactorQ {m : ℕ} (f : PSDFactorCertQ (m+1)) : PSDFactorCertQ m :=
  { factors := f.factors.map restrictFactorQ }

theorem restrict_factorGram_entry {m : ℕ} (fs : List (RankOneFactorQ (m+1)))
    (i j : Fin m) :
    factorGramQ (fs.map restrictFactorQ) i j = factorGramQ fs i.succ j.succ := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      change f.weight * f.vector i.succ * f.vector j.succ +
        factorGramQ (fs.map restrictFactorQ) i j =
        f.weight * f.vector i.succ * f.vector j.succ + factorGramQ fs i.succ j.succ
      rw [ih]

theorem restrict_factorGram {m : ℕ} (fs : List (RankOneFactorQ (m+1))) :
    factorGramQ (fs.map restrictFactorQ) = restrictGram (factorGramQ fs) := by
  funext i j
  exact restrict_factorGram_entry fs i j

/-- A centered Gram matrix realized in the zero-origin section. -/
def zeroOriginGramR {m : ℕ} (G : Gram m ℝ) : Gram (m+1) ℝ :=
  Fin.cons (fun _ => 0) (fun i => Fin.cons 0 (G i))

noncomputable def zeroOriginDataR {p m : ℕ} (d : DataR (Fin p) m) :
    DataR (Fin p) (m+1) :=
  { gram := zeroOriginGramR d.gram
    value := d.value
    position := fun i => Fin.cons 0 (d.position i)
    gradient := fun i => Fin.cons 0 (d.gradient i) }

/-- No symmetry/PSD hypothesis is needed for exact coefficient evaluation. -/
theorem evalR_restrictExprQ {p m : ℕ} (e : LinearExprQ p (m+1))
    (d : DataR (Fin p) m) :
    (restrictExprQ e).evalR d = e.evalR (zeroOriginDataR d) := by
  simp [LinearExprQ.evalR, restrictExprQ, restrictGram, zeroOriginDataR,
    zeroOriginGramR, Fin.sum_univ_succ]

theorem gramNormSq_zeroOriginGramR {m : ℕ} (G : Gram m ℝ)
    (v : VecExpr (m+1) ℝ) :
    gramNormSq (zeroOriginGramR G) v = gramNormSq G (restrictVec v) := by
  simp [gramNormSq, gramInner, zeroOriginGramR, restrictVec, Fin.sum_univ_succ]

theorem zeroOriginGramR_psd {m : ℕ} (G : Gram m ℝ) (hG : IsGramPosSemidef G) :
    IsGramPosSemidef (zeroOriginGramR G) := by
  constructor
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · exact hG.1 i j
  · intro v
    rw [gramNormSq_zeroOriginGramR]
    exact hG.2 (restrictVec v)

end LeanPEP.GramPEP.OriginCoordinates
