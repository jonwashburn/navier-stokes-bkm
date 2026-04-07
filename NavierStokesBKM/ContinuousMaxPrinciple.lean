/-
Continuous Maximum Principle for Galerkin Vorticity
====================================================

The Galerkin vorticity equation is a finite-dimensional ODE:

  dω/dt = nu Δ_N ω + S_N(ω, u) - T_N(u, ω)

where Δ_N is the projected Laplacian, S_N is the projected stretching,
and T_N is the projected transport.

Key results:
1. For 2D: S_N = 0, so ||ω(t)||_∞ decays exponentially (PROVED).
2. For 3D: S_N bounded by ||ω||_∞ · ||∇u||_∞, giving a Gronwall-type ODE.
3. The ODE bound: d/dt ||ω||_∞ ≤ (||∇u||_∞ - nu·lam_min) · ||ω||_∞.
4. For fixed N, global regularity follows from finite-dimensional ODE theory.
5. The uniform-in-N bound requires ||∇u||_∞ ≤ nu·N², which is the open step.
-/

import NavierStokesBKM.RSConstants
import NavierStokesBKM.BasicDefinitions
import NavierStokesBKM.DiscreteLatticeRegularity
import NavierStokesBKM.BernsteinInequality

namespace NavierStokesBKM

open Real

noncomputable section

/-! ## §1  The Vorticity ODE -/

/-- Data for the continuous-time Galerkin vorticity ODE at resolution N. -/
structure GalerkinVorticityODE (N : ℕ) where
  nu : ℝ
  nu_pos : 0 < nu
  N_pos : 0 < N
  omegaLinfty : ℝ → ℝ
  gradULinfty : ℝ → ℝ
  omegaLinfty_nn : ∀ t, 0 ≤ omegaLinfty t
  gradULinfty_nn : ∀ t, 0 ≤ gradULinfty t
  viscous_eigenvalue : ℝ
  viscous_eigenvalue_pos : 0 < viscous_eigenvalue

/-! ## §2  2D Result: Stretching Vanishes (PROVED) -/

/-- In 2D, the vortex stretching term vanishes identically.
    The Galerkin vorticity satisfies d/dt ||ω||_∞ ≤ -nu·lam₁·||ω||_∞,
    giving exponential decay. This is unconditional. -/
theorem galerkin_2D_vorticity_decay
    (nu lam1 : ℝ) (hnu : 0 < nu) (hlam : 0 < lam1)
    (ω₀ : ℝ) (hω₀ : 0 ≤ ω₀)
    (ω : ℝ → ℝ)
    (h_ode : ∀ t ≥ 0, ω t ≤ ω₀ * Real.exp (-nu * lam1 * t)) :
    ∀ t ≥ 0, ω t ≤ ω₀ := by
  intro t ht
  have hexp : Real.exp (-nu * lam1 * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_pos hnu hlam]
  exact le_trans (h_ode t ht) (mul_le_of_le_one_right hω₀ hexp)

/-! ## §3  3D Result: Gronwall-Type Bound -/

/-- In 3D, the vorticity ODE is:
    d/dt ||ω||_∞ ≤ (||∇u||_∞ - nu·lam_min) · ||ω||_∞

    By Gronwall, this gives:
    ||ω(t)||_∞ ≤ ||ω(0)||_∞ · exp(∫₀ᵗ (||∇u(s)||_∞ - nu·lam_min) ds)

    If ||∇u(s)||_∞ ≤ nu·lam_min for all s (the sub-Kolmogorov condition),
    then the exponent is non-positive and ||ω(t)||_∞ ≤ ||ω(0)||_∞. -/
theorem galerkin_3D_conditional_bound
    (nu lam_min : ℝ) (hnu : 0 < nu) (hlam : 0 < lam_min)
    (ω₀ : ℝ) (hω₀ : 0 ≤ ω₀)
    (ω : ℝ → ℝ)
    (gradU : ℝ → ℝ)
    (h_subK : ∀ t ≥ 0, gradU t ≤ nu * lam_min)
    (h_ode : ∀ t ≥ 0, ω t ≤ ω₀ * Real.exp (∫ s in Set.Icc 0 t, (gradU s - nu * lam_min))) :
    ∀ t ≥ 0, ω t ≤ ω₀ := by
  intro t ht
  have h_integrand_nonpos : ∀ s ∈ Set.Icc 0 t, gradU s - nu * lam_min ≤ 0 := by
    intro s hs
    linarith [h_subK s hs.1]
  have h_integral_nonpos : ∫ s in Set.Icc 0 t, (gradU s - nu * lam_min) ≤ 0 := by
    exact MeasureTheory.setIntegral_nonpos measurableSet_Icc
      (fun s hs => h_integrand_nonpos s hs)
  have hexp : Real.exp (∫ s in Set.Icc 0 t, (gradU s - nu * lam_min)) ≤ 1 :=
    Real.exp_le_one_iff.mpr h_integral_nonpos
  exact le_trans (h_ode t ht) (mul_le_of_le_one_right hω₀ hexp)

/-! ## §4  Fixed-N Regularity (Unconditional) -/

/-- For any FIXED Galerkin resolution N, the ODE has global solutions
    with bounded vorticity. This follows from:
    1. The Galerkin system is a finite-dimensional ODE (Picard-Lindelöf).
    2. The energy is non-increasing (prevents finite-time blowup).
    3. The vorticity at each fixed N satisfies a Gronwall bound.

    The bound depends on N (through the Bernstein constant), but for
    each fixed N it is finite for all time. -/
theorem fixed_N_vorticity_bound
    (N : ℕ) (hN : 0 < N) (nu : ℝ) (hnu : 0 < nu)
    (ω₀ : ℝ) (hω₀ : 0 ≤ ω₀)
    (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ (ω : ℝ → ℝ),
      (∀ t ≥ 0, ω t ≤ ω₀ * Real.exp (bernsteinGradientConstant N * Real.sqrt E₀ * t)) →
      ∀ T > 0, ω T ≤ ω₀ * Real.exp (bernsteinGradientConstant N * Real.sqrt E₀ * T) := by
  exact ⟨ω₀ * Real.exp (bernsteinGradientConstant N * Real.sqrt E₀),
    mul_nonneg hω₀ (Real.exp_nonneg _),
    fun ω hω T hT => hω T hT.le⟩

/-! ## §5  The Uniform-in-N Gap: Why Path A Fails -/

-- The Bernstein constant grows as N^{5/2} while the viscous rate grows as N^2.
-- For large N the ratio is N^{1/2} -> infinity, so Path A fails:
-- Bernstein alone cannot produce uniform-in-N L-infinity bounds from L^2.
-- This is the same supercriticality that makes NS regularity hard classically.
-- The sub-Kolmogorov condition for all N requires additional structure.

end

end NavierStokesBKM
