import LeanPEP

open LeanPEP.Profiles.Momentum
open LeanPEP.Profiles.NesterovPilot
open LeanPEP.Profiles.GramCompilation
open LeanPEP.GramPEP

#check ScheduleQ
#check coefficientStateQ
#check stateCoeffQ_succ
#check queryCoeffQ_succ
#check coefficientStateQ_causal
#check stateAffineQ_succ
#check queryAffineQ_succ
#check evalR_stateAffineQ_succ
#check evalR_queryAffineQ_succ
#check queryProfileQ
#check outputProfileQ
#check outputProfileQ_before_final
#check outputProfileQ_final
#check iterateAffineQ_queryProfileQ
#check iterateAffineQ_outputProfileQ_before_final
#check iterateAffineQ_outputProfileQ_final
#check outputModelQ_position_before_final
#check outputModelQ_position_final
#check outputModelQ_causal
#check outputModelQ_terminal_gradient_unused
#check outputObjectiveQ_evalR
#check nesterovScheduleQ
#check nesterovModelQ
#check nesterovObjectiveQ
#check pilot_positions
#check pilot_historical_gradient_mix
#check pilot_terminal_state_not_query
#check pilotUpperCertQ_check
#check pilotUpperCertQ_valid
#check pilot_certificate_identity
#check pilot_upper
#check pilotPrimalQ_psd_check
#check pilotPrimalQ_interpolation_check
#check pilotPrimalQ_assumptions_check
#check pilotPrimalQ_value
#check pilotPrimalQ_feasible_real
#check pilotPrimalQ_value_real
#check pilot_finite_tight
#check wrongBoundCertQ_rejected
#check wrongObjectiveCertQ_rejected
#check negativeInterpCertQ_rejected
#check missingDualFactorsCertQ_rejected

example (N : ℕ) (s : ScheduleQ) (i j : Fin (N + 1)) (h : i.val ≤ j.val) :
    (outputProfileQ N s).stepCoeff i j = 0 :=
  (outputProfileQ N s).causal i j h

example : (outputProfileQ 0 nesterovScheduleQ).stepCoeff 0 0 = 0 := by decide +kernel
example : pilotModelQ.position 4 2 = -(27/20 : ℚ) := by decide +kernel
example : pilotModelQ.position 5 4 = -(1 : ℚ) := by decide +kernel
example : checkUpperCertQ pilotUpperCertQ = true := pilotUpperCertQ_check
example : IsGreatest pilotFiniteValues ((1 : ℝ) / 21) := pilot_finite_tight

-- Expose dependencies of the structural proof and the finite tight result.
#print axioms coefficientStateQ_causal
#print axioms pilotUpperCertQ_check
#print axioms pilot_finite_tight
