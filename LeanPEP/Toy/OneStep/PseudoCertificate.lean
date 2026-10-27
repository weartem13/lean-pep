import LeanPEP.Toy.OneStep.Data

/-!
# Exact rejection of an invalid pseudo-certificate

This file demonstrates Level 1 certificate auditing: Lean rejects a
numerical-looking datum by identifying an exact violated scalar interpolation
constraint.  This is not a theorem-level counterexample to any published rate.
-/

namespace LeanPEP
namespace Toy
namespace OneStep

/-- An intentionally invalid PEP-style datum. -/
noncomputable def pseudoCert : OneStepData :=
  { g0 := (1 : ℝ) / 2
    g1 := 0
    f0 := (1 : ℝ) / 8
    f1 := (1 : ℝ) / 4 }

/-- The `p0, p1` interpolation slack of the pseudo-certificate is exactly
negative. -/
theorem pseudo_slack_negative :
    slack pseudoCert Pt.p0 Pt.p1 = -((1 : ℝ) / 4) := by
  norm_num [slack, x, grad, val, pseudoCert]

/-- The pseudo-certificate is not feasible. -/
theorem pseudoCert_not_feasible :
    ¬ OneStepFeasible pseudoCert := by
  intro h
  have hp : 0 ≤ slack pseudoCert Pt.p0 Pt.p1 := h.interp Pt.p0 Pt.p1
  rw [pseudo_slack_negative] at hp
  norm_num at hp

end OneStep
end Toy
end LeanPEP
