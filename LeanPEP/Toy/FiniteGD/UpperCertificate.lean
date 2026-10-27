import LeanPEP.Toy.FiniteGD.RationalBridge

/-!
# Generic exact upper-certificate syntax for finite gradient-descent PEPs

For every trajectory length `N`, an upper certificate consists of

* nonnegative multipliers on scalar interpolation slacks; and
* nonnegative weights on squares of affine forms in the sampled gradients.

The certificate identity is checked in a parameterized quadratic-polynomial
representation.  Its variables are the gradient samples `g₀, ..., g_N` and the
function values `f₀, ..., f_N`.  The representation is executable over `ℚ` and
has a proved real evaluation semantics.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD

open scoped BigOperators

/-- Every gradient/value index `0, ..., N`. -/
def indices (N : ℕ) : List (Fin (N + 1)) :=
  List.finRange (N + 1)

/-- Every ordered pair of gradient indices. -/
def indexPairs (N : ℕ) : List (Fin (N + 1) × Fin (N + 1)) :=
  (indices N).flatMap (fun i =>
    (indices N).map (fun j => (i, j)))

@[simp] theorem mem_indices {N : ℕ} (i : Fin (N + 1)) :
    i ∈ indices N := by
  simp [indices]

@[simp] theorem mem_indexPairs {N : ℕ} (i j : Fin (N + 1)) :
    (i, j) ∈ indexPairs N := by
  simp [indexPairs]

/-- A rational coefficient vector with a single `1` at `i`. -/
def unitCoeff {N : ℕ} (i : Fin (N + 1)) : Fin (N + 1) → ℚ :=
  fun j => if j = i then 1 else 0

/-- Rational coefficients paired with a real vector. -/
noncomputable def dotR
    {N : ℕ}
    (a : Fin (N + 1) → ℚ)
    (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ i, (a i : ℝ) * x i

/-- A rational quadratic coefficient matrix evaluated on a real vector. -/
noncomputable def quadR
    {N : ℕ}
    (q : Fin (N + 1) → Fin (N + 1) → ℚ)
    (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ i, ∑ j, (q i j : ℝ) * x i * x j

@[simp] theorem dotR_zero
    {N : ℕ} (x : Fin (N + 1) → ℝ) :
    dotR (fun _ => 0) x = 0 := by
  simp [dotR]

@[simp] theorem dotR_unitCoeff
    {N : ℕ} (i : Fin (N + 1)) (x : Fin (N + 1) → ℝ) :
    dotR (unitCoeff i) x = x i := by
  classical
  unfold dotR
  rw [Fintype.sum_eq_single i (by
    intro j hji
    simp [unitCoeff, hji])]
  simp [unitCoeff]

@[simp] theorem dotR_add
    {N : ℕ}
    (a b : Fin (N + 1) → ℚ)
    (x : Fin (N + 1) → ℝ) :
    dotR (fun i => a i + b i) x = dotR a x + dotR b x := by
  simp [dotR, add_mul, Finset.sum_add_distrib]

@[simp] theorem dotR_neg
    {N : ℕ}
    (a : Fin (N + 1) → ℚ)
    (x : Fin (N + 1) → ℝ) :
    dotR (fun i => -a i) x = -dotR a x := by
  simp [dotR]

@[simp] theorem dotR_scale
    {N : ℕ}
    (c : ℚ)
    (a : Fin (N + 1) → ℚ)
    (x : Fin (N + 1) → ℝ) :
    dotR (fun i => c * a i) x = (c : ℝ) * dotR a x := by
  simp [dotR, Finset.mul_sum, mul_assoc]

@[simp] theorem quadR_zero
    {N : ℕ} (x : Fin (N + 1) → ℝ) :
    quadR (fun _ _ => 0) x = 0 := by
  simp [quadR]

@[simp] theorem quadR_add
    {N : ℕ}
    (q r : Fin (N + 1) → Fin (N + 1) → ℚ)
    (x : Fin (N + 1) → ℝ) :
    quadR (fun i j => q i j + r i j) x = quadR q x + quadR r x := by
  simp [quadR, add_mul, Finset.sum_add_distrib]

@[simp] theorem quadR_neg
    {N : ℕ}
    (q : Fin (N + 1) → Fin (N + 1) → ℚ)
    (x : Fin (N + 1) → ℝ) :
    quadR (fun i j => -q i j) x = -quadR q x := by
  simp [quadR]

@[simp] theorem quadR_scale
    {N : ℕ}
    (c : ℚ)
    (q : Fin (N + 1) → Fin (N + 1) → ℚ)
    (x : Fin (N + 1) → ℝ) :
    quadR (fun i j => c * q i j) x = (c : ℝ) * quadR q x := by
  simp [quadR, Finset.mul_sum, mul_assoc]

/-- Ordered outer product of two rational coefficient vectors. -/
def outerQ
    {N : ℕ}
    (a b : Fin (N + 1) → ℚ) :
    Fin (N + 1) → Fin (N + 1) → ℚ :=
  fun i j => a i * b j

/-- Symmetrized outer product.  It evaluates to the product of the two linear
forms while giving a canonical symmetric quadratic coefficient matrix. -/
def symOuterQ
    {N : ℕ}
    (a b : Fin (N + 1) → ℚ) :
    Fin (N + 1) → Fin (N + 1) → ℚ :=
  fun i j => (a i * b j + b i * a j) / 2

/-- Evaluation of an ordered outer product factors into two dot products. -/
theorem quadR_outerQ
    {N : ℕ}
    (a b : Fin (N + 1) → ℚ)
    (x : Fin (N + 1) → ℝ) :
    quadR (outerQ a b) x = dotR a x * dotR b x := by
  calc
    quadR (outerQ a b) x =
        ∑ i, ((a i : ℝ) * x i) *
          (∑ j, (b j : ℝ) * x j) := by
      unfold quadR outerQ
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Rat.cast_mul]
      ring
    _ = dotR a x * dotR b x := by
      simp [dotR, Finset.sum_mul]

/-- Evaluation of the symmetrized outer product. -/
theorem quadR_symOuterQ
    {N : ℕ}
    (a b : Fin (N + 1) → ℚ)
    (x : Fin (N + 1) → ℝ) :
    quadR (symOuterQ a b) x = dotR a x * dotR b x := by
  have hrewrite :
      symOuterQ a b =
        fun i j => ((1 : ℚ) / 2) *
          (outerQ a b i j + outerQ b a i j) := by
    funext i j
    simp [symOuterQ, outerQ]
    ring
  rw [hrewrite, quadR_scale, quadR_add, quadR_outerQ, quadR_outerQ]
  ring

/-- An affine form in the sampled gradients. -/
@[ext]
structure GradAffineQ (N : ℕ) where
  constCoeff : ℚ
  gradCoeff : Fin (N + 1) → ℚ

namespace GradAffineQ

/-- Zero affine form. -/
def zero (N : ℕ) : GradAffineQ N :=
  { constCoeff := 0
    gradCoeff := fun _ => 0 }

/-- Constant affine form. -/
def const (N : ℕ) (c : ℚ) : GradAffineQ N :=
  { constCoeff := c
    gradCoeff := fun _ => 0 }

/-- The gradient variable `g_i`. -/
def basis {N : ℕ} (i : Fin (N + 1)) : GradAffineQ N :=
  { constCoeff := 0
    gradCoeff := unitCoeff i }

/-- Addition of affine forms. -/
def add {N : ℕ} (a b : GradAffineQ N) : GradAffineQ N :=
  { constCoeff := a.constCoeff + b.constCoeff
    gradCoeff := fun i => a.gradCoeff i + b.gradCoeff i }

/-- Negation of an affine form. -/
def neg {N : ℕ} (a : GradAffineQ N) : GradAffineQ N :=
  { constCoeff := -a.constCoeff
    gradCoeff := fun i => -a.gradCoeff i }

/-- Subtraction of affine forms. -/
def sub {N : ℕ} (a b : GradAffineQ N) : GradAffineQ N :=
  add a (neg b)

/-- Rational scaling of an affine form. -/
def scale {N : ℕ} (c : ℚ) (a : GradAffineQ N) : GradAffineQ N :=
  { constCoeff := c * a.constCoeff
    gradCoeff := fun i => c * a.gradCoeff i }

/-- Real evaluation of a rational affine form. -/
noncomputable def evalR
    {N : ℕ}
    (a : GradAffineQ N)
    (d : DataR N) : ℝ :=
  (a.constCoeff : ℝ) + dotR a.gradCoeff d.grad

@[simp] theorem evalR_zero {N : ℕ} (d : DataR N) :
    (zero N).evalR d = 0 := by
  simp [evalR, zero]

@[simp] theorem evalR_const {N : ℕ} (c : ℚ) (d : DataR N) :
    (const N c).evalR d = (c : ℝ) := by
  simp [evalR, const]

@[simp] theorem evalR_basis
    {N : ℕ} (i : Fin (N + 1)) (d : DataR N) :
    (basis i).evalR d = d.grad i := by
  simp [evalR, basis]

@[simp] theorem evalR_add
    {N : ℕ} (a b : GradAffineQ N) (d : DataR N) :
    (add a b).evalR d = a.evalR d + b.evalR d := by
  simp [evalR, add]
  ring

@[simp] theorem evalR_neg
    {N : ℕ} (a : GradAffineQ N) (d : DataR N) :
    (neg a).evalR d = -a.evalR d := by
  simp [evalR, neg]
  ring

@[simp] theorem evalR_sub
    {N : ℕ} (a b : GradAffineQ N) (d : DataR N) :
    (sub a b).evalR d = a.evalR d - b.evalR d := by
  simp [sub]
  ring

@[simp] theorem evalR_scale
    {N : ℕ} (c : ℚ) (a : GradAffineQ N) (d : DataR N) :
    (scale c a).evalR d = (c : ℝ) * a.evalR d := by
  simp [evalR, scale]
  ring

/-- Symbolic sum of the first `k` gradient variables. -/
def prefixAffine
    {N : ℕ} :
    (k : ℕ) → k ≤ N + 1 → GradAffineQ N
  | 0, _ => zero N
  | k + 1, hk =>
      add
        (prefixAffine k (Nat.le_trans (Nat.le_succ k) hk))
        (basis ⟨k, Nat.lt_of_succ_le hk⟩)

/-- The symbolic prefix has the same real semantics as `FiniteGD.prefixSum`. -/
theorem evalR_prefixAffine
    {N : ℕ} (d : DataR N) :
    ∀ (k : ℕ) (hk : k ≤ N + 1),
      (prefixAffine k hk).evalR d = prefixSum d.grad k hk := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [prefixAffine, prefixSum]
  | succ k ih =>
      intro hk
      simp [prefixAffine, prefixSum, ih]

end GradAffineQ

/-- Symbolic normalized position attached to a finite point. -/
def xAffineQ {N : ℕ} : Point N → GradAffineQ N
  | Point.star => GradAffineQ.zero N
  | Point.iter k =>
      GradAffineQ.sub
        (GradAffineQ.const N 1)
        (GradAffineQ.prefixAffine k.val (Nat.le_of_lt k.isLt))

/-- Symbolic gradient attached to a finite point. -/
def gradAffineQ {N : ℕ} : Point N → GradAffineQ N
  | Point.star => GradAffineQ.zero N
  | Point.iter k => GradAffineQ.basis k

@[simp] theorem evalR_xAffineQ
    {N : ℕ} (d : DataR N) (i : Point N) :
    (xAffineQ i).evalR d = x d i := by
  cases i with
  | star =>
      simp [xAffineQ, x]
  | iter k =>
      simp [xAffineQ, x, iterX, GradAffineQ.evalR_prefixAffine]

@[simp] theorem evalR_gradAffineQ
    {N : ℕ} (d : DataR N) (i : Point N) :
    (gradAffineQ i).evalR d = gradAt d i := by
  cases i <;> simp [gradAffineQ, gradAt]

/-- Executable quadratic-polynomial coefficients for arbitrary trajectory
length.  The quadratic matrix is kept symmetric by all constructors below. -/
@[ext]
structure QuadPolyQ (N : ℕ) where
  constCoeff : ℚ
  gradCoeff : Fin (N + 1) → ℚ
  valueCoeff : Fin (N + 1) → ℚ
  quadCoeff : Fin (N + 1) → Fin (N + 1) → ℚ

namespace QuadPolyQ

/-- Zero quadratic polynomial. -/
def zero (N : ℕ) : QuadPolyQ N :=
  { constCoeff := 0
    gradCoeff := fun _ => 0
    valueCoeff := fun _ => 0
    quadCoeff := fun _ _ => 0 }

/-- Addition of quadratic polynomials. -/
def add {N : ℕ} (p q : QuadPolyQ N) : QuadPolyQ N :=
  { constCoeff := p.constCoeff + q.constCoeff
    gradCoeff := fun i => p.gradCoeff i + q.gradCoeff i
    valueCoeff := fun i => p.valueCoeff i + q.valueCoeff i
    quadCoeff := fun i j => p.quadCoeff i j + q.quadCoeff i j }

/-- Negation of a quadratic polynomial. -/
def neg {N : ℕ} (p : QuadPolyQ N) : QuadPolyQ N :=
  { constCoeff := -p.constCoeff
    gradCoeff := fun i => -p.gradCoeff i
    valueCoeff := fun i => -p.valueCoeff i
    quadCoeff := fun i j => -p.quadCoeff i j }

/-- Subtraction of quadratic polynomials. -/
def sub {N : ℕ} (p q : QuadPolyQ N) : QuadPolyQ N :=
  add p (neg q)

/-- Rational scaling of a quadratic polynomial. -/
def scale {N : ℕ} (c : ℚ) (p : QuadPolyQ N) : QuadPolyQ N :=
  { constCoeff := c * p.constCoeff
    gradCoeff := fun i => c * p.gradCoeff i
    valueCoeff := fun i => c * p.valueCoeff i
    quadCoeff := fun i j => c * p.quadCoeff i j }

/-- Embed an affine gradient form as a quadratic polynomial. -/
def ofAffine {N : ℕ} (a : GradAffineQ N) : QuadPolyQ N :=
  { constCoeff := a.constCoeff
    gradCoeff := a.gradCoeff
    valueCoeff := fun _ => 0
    quadCoeff := fun _ _ => 0 }

/-- The function-value variable `f_i`. -/
def valueVar {N : ℕ} (i : Fin (N + 1)) : QuadPolyQ N :=
  { constCoeff := 0
    gradCoeff := fun _ => 0
    valueCoeff := unitCoeff i
    quadCoeff := fun _ _ => 0 }

/-- Product of two affine gradient forms, represented with a symmetric matrix. -/
def mulAffine {N : ℕ} (a b : GradAffineQ N) : QuadPolyQ N :=
  { constCoeff := a.constCoeff * b.constCoeff
    gradCoeff := fun i =>
      a.constCoeff * b.gradCoeff i +
        b.constCoeff * a.gradCoeff i
    valueCoeff := fun _ => 0
    quadCoeff := symOuterQ a.gradCoeff b.gradCoeff }

/-- Square of one affine gradient form. -/
def square {N : ℕ} (a : GradAffineQ N) : QuadPolyQ N :=
  mulAffine a a

/-- Real evaluation of the executable coefficient representation. -/
noncomputable def evalR
    {N : ℕ} (p : QuadPolyQ N) (d : DataR N) : ℝ :=
  (p.constCoeff : ℝ)
    + dotR p.gradCoeff d.grad
    + dotR p.valueCoeff d.value
    + quadR p.quadCoeff d.grad

@[simp] theorem evalR_zero {N : ℕ} (d : DataR N) :
    (zero N).evalR d = 0 := by
  simp [evalR, zero]

@[simp] theorem evalR_add
    {N : ℕ} (p q : QuadPolyQ N) (d : DataR N) :
    (add p q).evalR d = p.evalR d + q.evalR d := by
  simp [evalR, add]
  ring

@[simp] theorem evalR_neg
    {N : ℕ} (p : QuadPolyQ N) (d : DataR N) :
    (neg p).evalR d = -p.evalR d := by
  simp [evalR, neg]
  ring

@[simp] theorem evalR_sub
    {N : ℕ} (p q : QuadPolyQ N) (d : DataR N) :
    (sub p q).evalR d = p.evalR d - q.evalR d := by
  simp [sub]
  ring

@[simp] theorem evalR_scale
    {N : ℕ} (c : ℚ) (p : QuadPolyQ N) (d : DataR N) :
    (scale c p).evalR d = (c : ℝ) * p.evalR d := by
  simp [evalR, scale]
  ring

@[simp] theorem evalR_ofAffine
    {N : ℕ} (a : GradAffineQ N) (d : DataR N) :
    (ofAffine a).evalR d = a.evalR d := by
  simp [evalR, ofAffine, GradAffineQ.evalR]

@[simp] theorem evalR_valueVar
    {N : ℕ} (i : Fin (N + 1)) (d : DataR N) :
    (valueVar i).evalR d = d.value i := by
  simp [evalR, valueVar]

@[simp] theorem evalR_mulAffine
    {N : ℕ} (a b : GradAffineQ N) (d : DataR N) :
    (mulAffine a b).evalR d = a.evalR d * b.evalR d := by
  simp [evalR, mulAffine, GradAffineQ.evalR, quadR_symOuterQ]
  ring

@[simp] theorem evalR_square
    {N : ℕ} (a : GradAffineQ N) (d : DataR N) :
    (square a).evalR d = (a.evalR d)^2 := by
  simp [square, pow_two]

end QuadPolyQ

/-- Symbolic function value attached to a point. -/
def pointValuePolyQ {N : ℕ} : Point N → QuadPolyQ N
  | Point.star => QuadPolyQ.zero N
  | Point.iter k => QuadPolyQ.valueVar k

@[simp] theorem evalR_pointValuePolyQ
    {N : ℕ} (d : DataR N) (i : Point N) :
    (pointValuePolyQ i).evalR d = valueAt d i := by
  cases i <;> simp [pointValuePolyQ, valueAt]

/-- Symbolic polynomial for one scalar interpolation slack. -/
def slackPolyQ {N : ℕ} (i j : Point N) : QuadPolyQ N :=
  QuadPolyQ.sub
    (QuadPolyQ.sub
      (QuadPolyQ.sub
        (pointValuePolyQ i)
        (pointValuePolyQ j))
      (QuadPolyQ.mulAffine
        (gradAffineQ j)
        (GradAffineQ.sub (xAffineQ i) (xAffineQ j))))
    (QuadPolyQ.scale ((1 : ℚ) / 2)
      (QuadPolyQ.square
        (GradAffineQ.sub (gradAffineQ i) (gradAffineQ j))))

/-- The symbolic slack polynomial has exactly the finite PEP slack semantics. -/
@[simp] theorem evalR_slackPolyQ
    {N : ℕ} (d : DataR N) (i j : Point N) :
    (slackPolyQ i j).evalR d = slack d i j := by
  simp [slackPolyQ, slack]

/-- One nonnegative multiplier on an interpolation inequality. -/
structure InterpTermQ (N : ℕ) where
  weight : ℚ
  i : Point N
  j : Point N
  deriving DecidableEq, Repr

/-- One nonnegative weighted affine square. -/
structure SquareTermQ (N : ℕ) where
  weight : ℚ
  form : GradAffineQ N

/-- Generic exact upper certificate. -/
structure UpperCertQ (N : ℕ) where
  bound : ℚ
  objective : Fin (N + 1)
  interpTerms : List (InterpTermQ N)
  squareTerms : List (SquareTermQ N)

/-- Symbolic sum of all weighted interpolation terms. -/
def interpPolySumQ {N : ℕ} :
    List (InterpTermQ N) → QuadPolyQ N
  | [] => QuadPolyQ.zero N
  | t :: ts =>
      QuadPolyQ.add
        (QuadPolyQ.scale t.weight (slackPolyQ t.i t.j))
        (interpPolySumQ ts)

/-- Symbolic sum of all weighted affine-square terms. -/
def squarePolySumQ {N : ℕ} :
    List (SquareTermQ N) → QuadPolyQ N
  | [] => QuadPolyQ.zero N
  | t :: ts =>
      QuadPolyQ.add
        (QuadPolyQ.scale t.weight (QuadPolyQ.square t.form))
        (squarePolySumQ ts)

/-- Complete symbolic right-hand side represented by a certificate. -/
def certificateRhsPolyQ {N : ℕ} (c : UpperCertQ N) : QuadPolyQ N :=
  QuadPolyQ.add
    (interpPolySumQ c.interpTerms)
    (squarePolySumQ c.squareTerms)

/-- Symbolic target `bound - f_objective`. -/
def upperTargetPolyQ {N : ℕ}
    (bound : ℚ) (objective : Fin (N + 1)) : QuadPolyQ N :=
  QuadPolyQ.sub
    (QuadPolyQ.ofAffine (GradAffineQ.const N bound))
    (QuadPolyQ.valueVar objective)

/-- Exact coefficient residual: target minus certificate right-hand side. -/
def upperCertDifferenceQ {N : ℕ} (c : UpperCertQ N) : QuadPolyQ N :=
  QuadPolyQ.sub
    (upperTargetPolyQ c.bound c.objective)
    (certificateRhsPolyQ c)

/-- Real numerical value of all weighted interpolation terms. -/
noncomputable def interpTermsValueR
    {N : ℕ} (d : DataR N) :
    List (InterpTermQ N) → ℝ
  | [] => 0
  | t :: ts =>
      (t.weight : ℝ) * slack d t.i t.j + interpTermsValueR d ts

/-- Real numerical value of all weighted square terms. -/
noncomputable def squareTermsValueR
    {N : ℕ} (d : DataR N) :
    List (SquareTermQ N) → ℝ
  | [] => 0
  | t :: ts =>
      (t.weight : ℝ) * (t.form.evalR d)^2 + squareTermsValueR d ts

@[simp] theorem evalR_interpPolySumQ
    {N : ℕ} (d : DataR N) (terms : List (InterpTermQ N)) :
    (interpPolySumQ terms).evalR d = interpTermsValueR d terms := by
  induction terms with
  | nil =>
      simp [interpPolySumQ, interpTermsValueR]
  | cons t ts ih =>
      simp [interpPolySumQ, interpTermsValueR, ih]

@[simp] theorem evalR_squarePolySumQ
    {N : ℕ} (d : DataR N) (terms : List (SquareTermQ N)) :
    (squarePolySumQ terms).evalR d = squareTermsValueR d terms := by
  induction terms with
  | nil =>
      simp [squarePolySumQ, squareTermsValueR]
  | cons t ts ih =>
      simp [squarePolySumQ, squareTermsValueR, ih]

@[simp] theorem evalR_certificateRhsPolyQ
    {N : ℕ} (d : DataR N) (c : UpperCertQ N) :
    (certificateRhsPolyQ c).evalR d =
      interpTermsValueR d c.interpTerms +
        squareTermsValueR d c.squareTerms := by
  simp [certificateRhsPolyQ]

@[simp] theorem evalR_upperTargetPolyQ
    {N : ℕ} (d : DataR N)
    (bound : ℚ) (objective : Fin (N + 1)) :
    (upperTargetPolyQ bound objective).evalR d =
      (bound : ℝ) - d.value objective := by
  simp [upperTargetPolyQ]

end FiniteGD
end Toy
end LeanPEP
