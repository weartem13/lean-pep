import LeanPEP.Toy.OneStep.Data

/-!
# Exact rational data for executable one-step PEP auditing

The main mathematical theorems of this project live over `ℝ`.  This file adds a
parallel, fully computable representation over `ℚ`.  Its purpose is certificate
checking: externally supplied decimal data can later be converted to exact
rationals and audited without floating-point tolerances.
-/

namespace LeanPEP
namespace Toy
namespace OneStep

/-- Computable rational version of the normalized one-step finite PEP data. -/
structure OneStepDataQ where
  g0 : ℚ
  g1 : ℚ
  f0 : ℚ
  f1 : ℚ
  deriving DecidableEq, Repr

/-- The complete point list used by the generated checker. -/
def pts : List Pt := [Pt.star, Pt.p0, Pt.p1]

/-- Rational position of each finite point. -/
def xQ (d : OneStepDataQ) : Pt → ℚ
  | Pt.star => 0
  | Pt.p0 => 1
  | Pt.p1 => 1 - d.g0

/-- Rational gradient value attached to each finite point. -/
def gradQ (d : OneStepDataQ) : Pt → ℚ
  | Pt.star => 0
  | Pt.p0 => d.g0
  | Pt.p1 => d.g1

/-- Rational function value attached to each finite point. -/
def valQ (d : OneStepDataQ) : Pt → ℚ
  | Pt.star => 0
  | Pt.p0 => d.f0
  | Pt.p1 => d.f1

/-- Exact rational pairwise interpolation slack. -/
def slackQ (d : OneStepDataQ) (i j : Pt) : ℚ :=
  valQ d i - valQ d j
    - gradQ d j * (xQ d i - xQ d j)
    - ((1 : ℚ) / 2) * (gradQ d i - gradQ d j)^2

/-- Proposition-level rational feasibility, mirroring `OneStepFeasible`. -/
structure OneStepFeasibleQ (d : OneStepDataQ) : Prop where
  interp : ∀ i j : Pt, 0 ≤ slackQ d i j

/-- Rational copy of the exact optimal witness. -/
def exactWitnessQ : OneStepDataQ :=
  { g0 := (1 : ℚ) / 3
    g1 := (1 : ℚ) / 3
    f0 := (5 : ℚ) / 18
    f1 := (1 : ℚ) / 6 }

/-- Rational copy of the intentionally invalid pseudo-certificate. -/
def pseudoCertQ : OneStepDataQ :=
  { g0 := (1 : ℚ) / 2
    g1 := 0
    f0 := (1 : ℚ) / 8
    f1 := (1 : ℚ) / 4 }

end OneStep
end Toy
end LeanPEP
