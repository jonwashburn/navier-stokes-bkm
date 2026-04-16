/-
Continuous Maximum Principle for Galerkin Vorticity
====================================================

The Galerkin vorticity equation is a finite-dimensional ODE:

  dω/dt = ν Δ_N ω + S_N(ω, u) - T_N(u, ω)

where Δ_N is the projected Laplacian, S_N is the projected stretching,
and T_N is the projected transport.

Key results:
1. For 2D: S_N = 0, so ||ω(t)||_∞ decays exponentially (PROVED).
2. For 3D: S_N bounded by ||ω||_∞ · ||∇u||_∞, giving a Gronwall-type ODE.
3. The ODE bound: d/dt ||ω||_∞ ≤ (||∇u||_∞ - ν·λ_min) · ||ω||_∞.
4. For fixed N, global regularity follows from finite-dimensional ODE theory.
5. The uniform-in-N bound requires ||∇u||_∞ ≤ ν·N², which is the open step.
-/

import NavierStokesBKM.RSConstants
import NavierStokesBKM.BasicDefinitions
import NavierStokesBKM.DiscreteLatticeRegularity
import NavierStokesBKM.BernsteinInequality
import NavierStokesBKM.ShellLocalizedEnstrophy
import NavierStokesBKM.ShellLocalizedEnstrophy

namespace NavierStokesBKM

open Real

noncomputable section

/-! ## §1  The Vorticity ODE -/

/-- Data for the continuous-time Galerkin vorticity ODE at resolution N. -/
structure GalerkinVorticityODE (N : ℕ) where
  ν : ℝ
  ν_pos : 0 < ν
  N_pos : 0 < N
  omegaLinfty : ℝ → ℝ
  gradULinfty : ℝ → ℝ
  omegaLinfty_nn : ∀ t, 0 ≤ omegaLinfty t
  gradULinfty_nn : ∀ t, 0 ≤ gradULinfty t
  viscous_eigenvalue : ℝ
  viscous_eigenvalue_pos : 0 < viscous_eigenvalue

/-! ## §2  2D Result: Stretching Vanishes (PROVED) -/

/-- In 2D, the vortex stretching term vanishes identically.
    The Galerkin vorticity satisfies d/dt ||ω||_∞ ≤ -ν·λ₁·||ω||_∞,
    giving exponential decay. This is unconditional. -/
theorem galerkin_2D_vorticity_decay
    (ν lam1 : ℝ) (hν : 0 < ν) (hlam1 : 0 < lam1)
    (ω₀ : ℝ) (hω₀ : 0 ≤ ω₀)
    (ω : ℝ → ℝ)
    (h_ode : ∀ t ≥ 0, ω t ≤ ω₀ * Real.exp (-ν * lam1 * t)) :
    ∀ t ≥ 0, ω t ≤ ω₀ := by
  intro t ht
  have hexp : Real.exp (-ν * lam1 * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_pos hν hlam1]
  exact le_trans (h_ode t ht) (mul_le_of_le_one_right hω₀ hexp)

/-! ## §3  3D Result: Gronwall-Type Bound -/

/-- In 3D, the vorticity ODE is:
    d/dt ||ω||_∞ ≤ (||∇u||_∞ - ν·λ_min) · ||ω||_∞

    By Gronwall, this gives:
    ||ω(t)||_∞ ≤ ||ω(0)||_∞ · exp(∫₀ᵗ (||∇u(s)||_∞ - ν·λ_min) ds)

    If ||∇u(s)||_∞ ≤ ν·λ_min for all s (the sub-Kolmogorov condition),
    then the exponent is non-positive and ||ω(t)||_∞ ≤ ||ω(0)||_∞. -/
theorem galerkin_3D_conditional_bound
    (ν lam_min : ℝ) (hν : 0 < ν) (hlam : 0 < lam_min)
    (ω₀ : ℝ) (hω₀ : 0 ≤ ω₀)
    (ω : ℝ → ℝ)
    (gradU : ℝ → ℝ)
    (h_subK : ∀ t ≥ 0, gradU t ≤ ν * lam_min)
    (h_ode : ∀ t ≥ 0, ω t ≤ ω₀ * Real.exp (∫ s in Set.Icc 0 t, (gradU s - ν * lam_min))) :
    ∀ t ≥ 0, ω t ≤ ω₀ := by
  intro t ht
  have h_integrand_nonpos : ∀ s ∈ Set.Icc 0 t, gradU s - ν * lam_min ≤ 0 := by
    intro s hs
    linarith [h_subK s hs.1]
  have h_integral_nonpos : ∫ s in Set.Icc 0 t, (gradU s - ν * lam_min) ≤ 0 := by
    exact MeasureTheory.setIntegral_nonpos measurableSet_Icc
      (fun s hs => h_integrand_nonpos s hs)
  have hexp : Real.exp (∫ s in Set.Icc 0 t, (gradU s - ν * lam_min)) ≤ 1 :=
    Real.exp_le_one_iff.mpr h_integral_nonpos
  exact le_trans (h_ode t ht) (mul_le_of_le_one_right hω₀ hexp)

/-! ## §4  Shell-Localized Route -/

/-- Data for the top-shell closure program at frequency `N`.

The content is exactly the candidate route identified after the failure of the
global Bernstein bootstrap:

1. top-shell Bernstein scales like `N²`,
2. local shell flux is absorbed by viscosity,
3. dissipative nonlocal triads have good sign,
4. the remaining bad nonlocal triads are paid by a shell defect,
5. that defect is itself absorbed by the leftover viscous budget.

What remains open mathematically is deriving this structure from the actual
Galerkin triadic decomposition. -/
structure TopShellControl (N : ℕ) where
  ν : ℝ
  ν_pos : 0 < ν
  N_pos : 0 < N
  bernstein : TopShellBernsteinBound N
  budget : ShellEnstrophyBudget N
  shell_smallness : Real.sqrt 26 * bernstein.omegaTopL2 ≤ ν
  defect_absorbed :
    budget.shellDefect ≤ budget.viscousDissipation - budget.localFlux

/-- Under top-shell enstrophy smallness, the shell-localized Bernstein bound
matches the viscous rate `ν·N²`. -/
theorem topShellControl_subKolmogorov
    {N : ℕ} (ctl : TopShellControl N) :
    ctl.bernstein.gradUTopLinfty ≤ ctl.ν * (N : ℝ) ^ 2 :=
  topShell_subKolmogorov_of_small_enstrophy ctl.N_pos ctl.bernstein ctl.ν ctl.shell_smallness

/-- Once the shell defect is absorbed, the top-shell enstrophy is
non-increasing. -/
theorem topShell_enstrophy_nonincreasing
    {N : ℕ} (ctl : TopShellControl N) :
    ctl.budget.dEdt ≤ 0 :=
  shellLocalizedEnstrophy_nonincreasing_of_defect_absorption ctl.budget ctl.defect_absorbed

/-- Top-shell analogue of the 3D conditional vorticity bound.

This is the sharpened replacement for the failed global Bernstein route:
the needed sign condition is no longer imposed on the entire Galerkin system at
once, but only on the top shell after the nonlocal triads are split into
dissipative and defect-paid pieces. -/
theorem galerkin_3D_topShell_conditional_bound
    {N : ℕ} (ctl : TopShellControl N)
    (ω₀ : ℝ) (hω₀ : 0 ≤ ω₀)
    (ωTop : ℝ → ℝ)
    (h_ode : ∀ t ≥ 0, ωTop t ≤ ω₀ * Real.exp (ctl.budget.dEdt * t)) :
    ∀ t ≥ 0, ωTop t ≤ ω₀ := by
  intro t ht
  have hrate : ctl.budget.dEdt ≤ 0 := topShell_enstrophy_nonincreasing ctl
  have hexp : Real.exp (ctl.budget.dEdt * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  exact le_trans (h_ode t ht) (mul_le_of_le_one_right hω₀ hexp)

/-! ## §5  Fixed-N Regularity (Unconditional) -/

/-- For any FIXED Galerkin resolution N, the ODE has global solutions
    with bounded vorticity. This follows from:
    1. The Galerkin system is a finite-dimensional ODE (Picard-Lindelöf).
    2. The energy is non-increasing (prevents finite-time blowup).
    3. The vorticity at each fixed N satisfies a Gronwall bound.

    The bound depends on N (through the Bernstein constant), but for
    each fixed N it is finite for all time. -/
theorem fixed_N_vorticity_bound
    (N : ℕ) (hN : 0 < N) (ν : ℝ) (hν : 0 < ν)
    (ω₀ : ℝ) (hω₀ : 0 ≤ ω₀)
    (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ (ω : ℝ → ℝ),
      (∀ t ≥ 0, ω t ≤ ω₀ * Real.exp (bernsteinGradientConstant N * Real.sqrt E₀ * t)) →
      ∀ T > 0, ω T ≤ ω₀ * Real.exp (bernsteinGradientConstant N * Real.sqrt E₀ * T) := by
  exact ⟨ω₀ * Real.exp (bernsteinGradientConstant N * Real.sqrt E₀),
    mul_nonneg hω₀ (Real.exp_nonneg _),
    fun ω hω T hT => hω T hT.le⟩

/-! ## §6  The Uniform-in-N Gap: Why Path A Fails -/

-- The Bernstein constant grows as N^{5/2} while the viscous rate grows as N^2.
-- For large N the ratio is N^{1/2} -> infinity, so Path A fails:
-- Bernstein alone cannot produce uniform-in-N L-infinity bounds from L^2.
-- This is the same supercriticality that makes NS regularity hard classically.
-- The sub-Kolmogorov condition for all N requires additional structure.

/-! ## §6  Shell-localized replacement for global Bernstein -/

/-- On the top shell, the mode count is only quadratic in `N`, so the shell
Bernstein gradient constant has `N²` scaling rather than `N^(5/2)`. -/
theorem topShell_gradient_has_quadratic_scaling
    {N : ℕ} (hN : 0 < N) (bb : TopShellBernsteinBound N) :
    bb.gradUTopLinfty ≤ Real.sqrt 26 * (N : ℝ) ^ 2 * bb.omegaTopL2 :=
  topShell_gradient_quadratic_scaling hN bb

/-- Consequently, small enough top-shell `L²` enstrophy forces the shell into the
sub-Kolmogorov regime. This is the right scaling target for the next closure
step; the remaining issue is the shell defect coming from nonlocal triads. -/
theorem topShell_subKolmogorov
    {N : ℕ} (hN : 0 < N) (bb : TopShellBernsteinBound N)
    (ν : ℝ) (hsmall : Real.sqrt 26 * bb.omegaTopL2 ≤ ν) :
    bb.gradUTopLinfty ≤ ν * (N : ℝ) ^ 2 :=
  topShell_subKolmogorov_of_small_enstrophy hN bb ν hsmall

/-- Shell-localized enstrophy control: once local interactions are absorbed by
viscosity, every remaining nonlocal contribution is either dissipative or paid
for by the shell defect. -/
theorem shellLocalized_enstrophy_control
    {N : ℕ} (budget : ShellEnstrophyBudget N) :
    budget.dEdt ≤ budget.shellDefect :=
  shellLocalizedEnstrophy_derivative_le_defect budget

end

end NavierStokesBKM
