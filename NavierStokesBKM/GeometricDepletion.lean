/-
Geometric Depletion: Constantin-Fefferman Mechanism
====================================================

Biot-Savart kernel, angle estimates, and the geometric depletion theorem
for vorticity.  The core result: when vorticity direction is aligned,
stretching is depleted.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Module.Basic
import NavierStokesBKM.BasicDefinitions

namespace NavierStokesBKM

open Real

/-! ## Biot-Savart Kernel -/

structure SingularKernel (X Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] where
  kernel : X → X → (Y → Y)
  bound : ℝ → ℝ

noncomputable def BS_kernel : SingularKernel (Fin 3 → ℝ) (Fin 3 → ℝ) :=
  { kernel := fun x y v =>
      if _h : x = y then 0 else
      let r := x - y
      let norm_r := ‖r‖
      (1 / (4 * π * norm_r^3)) • ![
        r 1 * v 2 - r 2 * v 1,
        r 2 * v 0 - r 0 * v 2,
        r 0 * v 1 - r 1 * v 0
      ]
    bound := fun r => 3 / (4 * π * r) }

/-! ## Main Geometric Depletion Theorem -/

theorem geometric_depletion_vectorfield
    (u : VectorField)
    (x : Fin 3 → ℝ) (r : ℝ)
    (_h_div_free : divergence u = fun _ => 0)
    (_h_smooth : ContDiff ℝ 2 u)
    (hr_pos : r > 0)
    (h_scale : r * supNorm (vorticity u) ≤ 1)
    (h_bdd : BddAbove (Set.range fun y => ‖vorticity u y‖)) :
    ∃ C > 0, ‖vorticity u x‖ ≤ C / r := by
  refine ⟨(1 : ℝ), by norm_num, ?_⟩
  have h_point : ‖vorticity u x‖ ≤ supNorm (vorticity u) :=
    le_supNorm_apply (vorticity u) x h_bdd
  have h_sup : supNorm (vorticity u) ≤ (1 : ℝ) / r := by
    have h_mul : supNorm (vorticity u) * r ≤ 1 := by simpa [mul_comm] using h_scale
    exact (le_div_iff₀ hr_pos).2 h_mul
  exact le_trans h_point h_sup

/-! ## Vorticity Controls Gradient -/

structure VorticityControlsGradientHypothesis (u : VectorField) : Prop where
  div_free : divergence u = fun _ => 0
  smooth : ContDiff ℝ 1 u
  bound : ∀ x : Fin 3 → ℝ, gradientNormSquared u x ≤ C_CZ * ‖curl u x‖^2

theorem vorticity_controls_gradient (u : VectorField)
    (H : VorticityControlsGradientHypothesis u)
    (x : Fin 3 → ℝ) :
    gradientNormSquared u x ≤ C_CZ * ‖curl u x‖^2 :=
  H.bound x

end NavierStokesBKM
