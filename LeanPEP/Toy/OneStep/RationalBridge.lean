import LeanPEP.Toy.OneStep.RationalChecker
import LeanPEP.Toy.OneStep.Upper
import LeanPEP.Toy.OneStep.Lower
import LeanPEP.Toy.OneStep.PseudoCertificate

/-!
# Bridge from executable rational auditing to real finite PEP semantics

The checker runs over `ℚ`, while the main mathematical theorem is stated over
`ℝ`.  This file proves that rational data cast to real data preserve every
position, gradient, value, and interpolation slack.  Consequently, a successful
Boolean rational check yields a proof of real finite PEP feasibility.
-/

namespace LeanPEP
namespace Toy
namespace OneStep

/-- Cast computable rational data into the real finite PEP representation. -/
noncomputable def toRealData (d : OneStepDataQ) : OneStepData :=
  { g0 := (d.g0 : ℝ)
    g1 := (d.g1 : ℝ)
    f0 := (d.f0 : ℝ)
    f1 := (d.f1 : ℝ) }

@[simp] theorem x_toRealData (d : OneStepDataQ) (i : Pt) :
    x (toRealData d) i = (xQ d i : ℝ) := by
  cases i <;> simp [x, xQ, toRealData]

@[simp] theorem grad_toRealData (d : OneStepDataQ) (i : Pt) :
    grad (toRealData d) i = (gradQ d i : ℝ) := by
  cases i <;> simp [grad, gradQ, toRealData]

@[simp] theorem val_toRealData (d : OneStepDataQ) (i : Pt) :
    val (toRealData d) i = (valQ d i : ℝ) := by
  cases i <;> simp [val, valQ, toRealData]

/-- Casting rational data to reals preserves the exact interpolation slack. -/
@[simp] theorem slack_toRealData
    (d : OneStepDataQ) (i j : Pt) :
    slack (toRealData d) i j = (slackQ d i j : ℝ) := by
  simp [slack, slackQ]

/-- Rational feasibility implies feasibility of the cast real data. -/
theorem feasibleQ_toReal
    (d : OneStepDataQ)
    (h : OneStepFeasibleQ d) :
    OneStepFeasible (toRealData d) := by
  constructor
  intro i j
  rw [slack_toRealData]
  exact Rat.cast_nonneg.mpr (h.interp i j)

/-- A successful executable check produces a real finite PEP feasibility proof. -/
theorem checkFeasibleQ_sound_real
    (d : OneStepDataQ)
    (h : checkFeasibleQ d = true) :
    OneStepFeasible (toRealData d) :=
  feasibleQ_toReal d (checkFeasibleQ_sound d h)

/-- Any rational datum accepted by the checker obeys the real one-step bound. -/
theorem checkFeasibleQ_upper
    (d : OneStepDataQ)
    (h : checkFeasibleQ d = true) :
    (d.f1 : ℝ) ≤ (1 : ℝ) / 6 := by
  simpa [toRealData] using
    oneStep_upper (toRealData d) (checkFeasibleQ_sound_real d h)

/-- The rational exact witness casts to the original real exact witness. -/
theorem exactWitnessQ_toReal :
    toRealData exactWitnessQ = exactWitness := by
  apply OneStepData.ext <;>
    norm_num [toRealData, exactWitnessQ, exactWitness]

/-- The rational pseudo-certificate casts to the original real datum. -/
theorem pseudoCertQ_toReal :
    toRealData pseudoCertQ = pseudoCert := by
  apply OneStepData.ext <;>
    norm_num [toRealData, pseudoCertQ, pseudoCert]

/-- The executable checker reconstructs real feasibility of the exact witness. -/
theorem exactWitness_feasible_from_checker :
    OneStepFeasible exactWitness := by
  rw [← exactWitnessQ_toReal]
  exact checkFeasibleQ_sound_real exactWitnessQ exactWitnessQ_check

end OneStep
end Toy
end LeanPEP
