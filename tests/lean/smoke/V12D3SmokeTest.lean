import LeanPEP.ActualFunction.HuberWitnessAnalytic

open LeanPEP
open LeanPEP.ActualFunction
open LeanPEP.ActualFunction.HuberWitness

#check huberFunction_hasDerivAt
#check deriv_huberFunction
#check huberFunction_differentiable
#check huberGradient_monotone
#check huberFunction_convexOn
#check huberGradient_lipschitz
#check huberFunction_hasGradientAt
#check analytic

#check witnessFunction_hasDerivAt
#check witnessFunction_hasGradientAt
#check witnessGradient_lipschitz
#check witness_analytic
#check normalized_analytic_lower_witness

example (a x : ℝ) :
    HasDerivAt (huberFunction a) (huberGradient a x) x := by
  exact huberFunction_hasDerivAt a x

example (N : ℕ) :
    IsOneSmoothConvexAnalytic (witnessFunction N) (witnessGradient N) := by
  exact witness_analytic N

example (N : ℕ) :
    witnessFunction N
          (ParametricGDActual.unitGDIterate (witnessGradient N) 1 N) -
        witnessFunction N 0 =
      (LeanPEP.Toy.FiniteGD.ParametricUpper.gdBoundQ N : ℝ) := by
  exact (normalized_analytic_lower_witness N).2.2.2.2
