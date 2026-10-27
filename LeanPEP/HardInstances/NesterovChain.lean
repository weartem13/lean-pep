import LeanPEP.HardInstances.NesterovChain.Matrix
import LeanPEP.HardInstances.NesterovChain.Function
import LeanPEP.HardInstances.NesterovChain.Minimizer
import LeanPEP.HardInstances.NesterovChain.SmallTrajectory

/-!
# Nesterov chain hard instance

This aggregate exposes the exact structure matrix, explicit quadratic function,
closed-form minimizer, and small exact gradient-descent trajectories developed
in the independent hard-instance branch.
The space-dimension parameter used here is distinct from the finite-GD step
parameter in `LeanPEP.Toy.FiniteGD`.
-/
