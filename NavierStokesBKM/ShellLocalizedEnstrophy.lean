/- 
Shell-Localized Enstrophy Control for Galerkin Vorticity
========================================================

The global Bernstein route fails because counting all modes in `[-N, N]^3`
costs `(2N+1)^3 ~ N^3` modes, whose square root produces the extra `N^(1/2)`
gap after differentiating.

This file records the first shell-localized replacement:

1. The top shell only contains `O(N^2)` modes.
2. The corresponding shell Bernstein gradient constant scales like `N^2`,
   which matches the viscous scale.
3. Once the top-shell triadic budget is split into:
     - local flux (absorbed by viscosity),
     - dissipative nonlocal flux,
     - dangerous nonlocal flux paid by a shell defect,
   the shell enstrophy derivative is bounded by the shell defect alone.

This does not yet close the 3D problem, but it isolates the remaining task in
the right scaling regime.
-/

import NavierStokesBKM.BernsteinInequality

namespace NavierStokesBKM

open Real

noncomputable section

/-! ## §1  Top-shell counting -/

/-- Number of modes newly added when passing from truncation `N-1` to `N`.
For `N = 0` this is the single zero mode. -/
def topShellModeCount : ℕ → ℕ
  | 0 => modeCount 0
  | N + 1 => modeCount (N + 1) - modeCount N

theorem topShellModeCount_zero : topShellModeCount 0 = 1 := by
  simp [topShellModeCount, modeCount]

/-- Exact cardinality of the boundary shell added at level `N + 1`. -/
theorem topShellModeCount_succ_formula (N : ℕ) :
    topShellModeCount (N + 1) = 24 * N ^ 2 + 48 * N + 26 := by
  have hexpand :
      modeCount (N + 1) = modeCount N + (24 * N ^ 2 + 48 * N + 26) := by
    unfold modeCount
    ring
  calc
    topShellModeCount (N + 1)
        = modeCount (N + 1) - modeCount N := by
            simp [topShellModeCount]
    _ = (modeCount N + (24 * N ^ 2 + 48 * N + 26)) - modeCount N := by
          rw [hexpand]
    _ = 24 * N ^ 2 + 48 * N + 26 := by
          simpa [add_comm, add_left_comm, add_assoc] using
            Nat.add_sub_cancel_left (modeCount N) (24 * N ^ 2 + 48 * N + 26)

/-- Exact quadratic mode count for the top shell at truncation `N > 0`. -/
theorem topShellModeCount_formula {N : ℕ} (hN : 0 < N) :
    topShellModeCount N = 24 * N ^ 2 + 2 := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN) with ⟨n, rfl⟩
  calc
    topShellModeCount (n + 1) = 24 * n ^ 2 + 48 * n + 26 := topShellModeCount_succ_formula n
    _ = 24 * (n + 1) ^ 2 + 2 := by ring

/-- Real-valued version of the top-shell mode count. -/
def topShellModeCountReal (N : ℕ) : ℝ := topShellModeCount N

theorem topShellModeCountReal_pos {N : ℕ} (hN : 0 < N) :
    0 < topShellModeCountReal N := by
  unfold topShellModeCountReal
  rw [topShellModeCount_formula hN]
  positivity

/-- The top shell has only quadratic size in `N`. -/
theorem topShellModeCountReal_le_quadratic {N : ℕ} (hN : 0 < N) :
    topShellModeCountReal N ≤ 26 * (N : ℝ) ^ 2 := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hN
  have hNsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith
  unfold topShellModeCountReal
  rw [topShellModeCount_formula hN]
  norm_num
  nlinarith

/-! ## §2  Shell-localized Bernstein constants -/

/-- Shell Bernstein constant: only the newest shell at frequency `N` is counted. -/
def topShellBernsteinConstant (N : ℕ) : ℝ :=
  Real.sqrt (topShellModeCountReal N)

/-- Shell Bernstein gradient constant.
The extra derivative contributes one factor of `N`. -/
def topShellBernsteinGradientConstant (N : ℕ) : ℝ :=
  (N : ℝ) * topShellBernsteinConstant N

/-- The shell-localized gradient constant has the correct quadratic scaling. -/
theorem topShellBernsteinGradientConstant_le {N : ℕ} (hN : 0 < N) :
    topShellBernsteinGradientConstant N ≤ Real.sqrt 26 * (N : ℝ) ^ 2 := by
  unfold topShellBernsteinGradientConstant topShellBernsteinConstant
  have hcount : topShellModeCountReal N ≤ 26 * (N : ℝ) ^ 2 :=
    topShellModeCountReal_le_quadratic hN
  have hsqrt :
      Real.sqrt (topShellModeCountReal N) ≤ Real.sqrt (26 * (N : ℝ) ^ 2) := by
    exact Real.sqrt_le_sqrt hcount
  have hNnn : 0 ≤ (N : ℝ) := by positivity
  have hmul :
      (N : ℝ) * Real.sqrt (topShellModeCountReal N) ≤
        (N : ℝ) * Real.sqrt (26 * (N : ℝ) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hsqrt hNnn
  have hsqrt_prod :
      Real.sqrt (26 * (N : ℝ) ^ 2) = Real.sqrt 26 * (N : ℝ) := by
    have hsq :
        (Real.sqrt (26 * (N : ℝ) ^ 2)) ^ 2 = (Real.sqrt 26 * (N : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    have hleft_nonneg : 0 ≤ Real.sqrt (26 * (N : ℝ) ^ 2) := Real.sqrt_nonneg _
    have hright_nonneg : 0 ≤ Real.sqrt 26 * (N : ℝ) := by positivity
    apply le_antisymm
    · nlinarith
    · nlinarith
  have hscale :
      (N : ℝ) * Real.sqrt (26 * (N : ℝ) ^ 2) = Real.sqrt 26 * (N : ℝ) ^ 2 := by
    calc
      (N : ℝ) * Real.sqrt (26 * (N : ℝ) ^ 2)
          = (N : ℝ) * (Real.sqrt 26 * (N : ℝ)) := by
              rw [hsqrt_prod]
      _ = Real.sqrt 26 * (N : ℝ) ^ 2 := by ring
  rw [hscale] at hmul
  exact hmul

/-- Shell-localized Bernstein data for the vorticity concentrated on the top shell. -/
structure TopShellBernsteinBound (N : ℕ) where
  omegaTopLinfty : ℝ
  omegaTopL2 : ℝ
  gradUTopLinfty : ℝ
  omegaTopLinfty_nn : 0 ≤ omegaTopLinfty
  omegaTopL2_nn : 0 ≤ omegaTopL2
  gradUTopLinfty_nn : 0 ≤ gradUTopLinfty
  bernstein_omega_top :
    omegaTopLinfty ≤ topShellBernsteinConstant N * omegaTopL2
  bernstein_gradU_top :
    gradUTopLinfty ≤ topShellBernsteinGradientConstant N * omegaTopL2

/-- The shell-localized gradient estimate scales like `N²`, not `N^(5/2)`. -/
theorem topShell_gradient_quadratic_scaling {N : ℕ} (hN : 0 < N)
    (bb : TopShellBernsteinBound N) :
    bb.gradUTopLinfty ≤ Real.sqrt 26 * (N : ℝ) ^ 2 * bb.omegaTopL2 := by
  have hconst :
      topShellBernsteinGradientConstant N * bb.omegaTopL2 ≤
        (Real.sqrt 26 * (N : ℝ) ^ 2) * bb.omegaTopL2 := by
    exact mul_le_mul_of_nonneg_right
      (topShellBernsteinGradientConstant_le hN) bb.omegaTopL2_nn
  exact le_trans bb.bernstein_gradU_top hconst

/-- If the top-shell `L²` enstrophy is small relative to `ν`, then the shell is
sub-Kolmogorov at frequency `N`. -/
theorem topShell_subKolmogorov_of_small_enstrophy {N : ℕ} (hN : 0 < N)
    (bb : TopShellBernsteinBound N) (ν : ℝ)
    (hsmall : Real.sqrt 26 * bb.omegaTopL2 ≤ ν) :
    bb.gradUTopLinfty ≤ ν * (N : ℝ) ^ 2 := by
  calc
    bb.gradUTopLinfty ≤ Real.sqrt 26 * (N : ℝ) ^ 2 * bb.omegaTopL2 :=
      topShell_gradient_quadratic_scaling hN bb
    _ = (Real.sqrt 26 * bb.omegaTopL2) * (N : ℝ) ^ 2 := by ring
    _ ≤ ν * (N : ℝ) ^ 2 := by
          exact mul_le_mul_of_nonneg_right hsmall (sq_nonneg ((N : ℝ)))

/-! ## §3  Shell-localized triadic budget -/

/-- Total triadic contribution to the top shell, split into the three pieces
relevant to the closure program. -/
structure ShellTriadBudget where
  localFlux : ℝ
  dissipativeNonlocalFlux : ℝ
  defectPaidNonlocalFlux : ℝ
  shellDefect : ℝ
  shellDefect_nonneg : 0 ≤ shellDefect
  dissipative_nonpos : dissipativeNonlocalFlux ≤ 0
  defect_paid : defectPaidNonlocalFlux ≤ shellDefect

/-- Total nonlocal transfer hitting the top shell. -/
def totalNonlocalFlux (b : ShellTriadBudget) : ℝ :=
  b.dissipativeNonlocalFlux + b.defectPaidNonlocalFlux

/-- Dangerous nonlocal triads are harmless once they are either dissipative or
paid for by the shell defect. -/
theorem totalNonlocalFlux_le_shellDefect (b : ShellTriadBudget) :
    totalNonlocalFlux b ≤ b.shellDefect := by
  unfold totalNonlocalFlux
  linarith [b.dissipative_nonpos, b.defect_paid]

/-- Shell-localized enstrophy balance for the top band. -/
structure ShellEnstrophyBudget (N : ℕ) extends ShellTriadBudget where
  shellEnstrophy : ℝ
  shellEnstrophy_nonneg : 0 ≤ shellEnstrophy
  viscousDissipation : ℝ
  viscousDissipation_nonneg : 0 ≤ viscousDissipation
  dEdt : ℝ
  split :
    dEdt =
      -viscousDissipation + localFlux +
        dissipativeNonlocalFlux + defectPaidNonlocalFlux
  local_absorbed_by_viscous : localFlux ≤ viscousDissipation

/-- Once local shell interactions are absorbed by viscosity, the entire top-shell
growth rate is controlled by the shell defect alone. -/
theorem shellLocalizedEnstrophy_derivative_le_defect {N : ℕ}
    (b : ShellEnstrophyBudget N) :
    b.dEdt ≤ b.shellDefect := by
  rw [b.split]
  linarith [b.local_absorbed_by_viscous, b.dissipative_nonpos, b.defect_paid]

/-- If the shell defect vanishes, the top-shell enstrophy is non-increasing. -/
theorem shellLocalizedEnstrophy_nonincreasing_of_zero_defect {N : ℕ}
    (b : ShellEnstrophyBudget N) (hdef : b.shellDefect = 0) :
    b.dEdt ≤ 0 := by
  have h := shellLocalizedEnstrophy_derivative_le_defect b
  simpa [hdef] using h

/-- More generally, if the defect itself is absorbed by the leftover viscous
budget, then the top shell is dissipative. -/
theorem shellLocalizedEnstrophy_nonincreasing_of_defect_absorption {N : ℕ}
    (b : ShellEnstrophyBudget N)
    (hdef : b.shellDefect ≤ b.viscousDissipation - b.localFlux) :
    b.dEdt ≤ 0 := by
  rw [b.split]
  linarith [b.dissipative_nonpos, b.defect_paid, hdef]

/-- The shell defect is the only remaining rate after the triadic split. -/
theorem shellLocalizedEnstrophy_gated_by_rate {N : ℕ}
    (b : ShellEnstrophyBudget N) (κ : ℝ)
    (hdef : b.shellDefect ≤ κ * b.shellEnstrophy) :
    b.dEdt ≤ κ * b.shellEnstrophy := by
  exact le_trans (shellLocalizedEnstrophy_derivative_le_defect b) hdef

end

end NavierStokesBKM
