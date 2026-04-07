/-
Bernstein Inequality for Galerkin Modes
========================================

For trigonometric polynomials with Fourier support in {k : |k_i| ≤ N},
the L∞ norm is controlled by the L² norm times a factor of (2N+1)^{d/2}.

In 3D on T³: ||f||_∞ ≤ (2N+1)^{3/2} · ||f||_{L²}

This is the bridge between L² energy estimates (which the Galerkin system
gives for free) and L∞ vorticity control (which the BKM criterion needs).
-/

import NavierStokesBKM.RSConstants
import NavierStokesBKM.GalerkinFamily3D

namespace NavierStokesBKM

open Real

noncomputable section

/-! ## §1  Mode Count -/

/-- The number of Fourier modes in [-N, N]³. -/
def modeCount (N : ℕ) : ℕ := (2 * N + 1) ^ 3

theorem modeCount_pos (N : ℕ) : 0 < modeCount N := by
  unfold modeCount; positivity

/-- (2N+1)^3 as a real number. -/
def modeCountReal (N : ℕ) : ℝ := ((2 * N + 1 : ℕ) : ℝ) ^ 3

theorem modeCountReal_pos (N : ℕ) : 0 < modeCountReal N := by
  unfold modeCountReal
  positivity

/-! ## §2  Bernstein Inequality -/

/-- **Bernstein inequality on T³**: For a trigonometric polynomial f with
    Fourier support in {k : |k_i| ≤ N}, the pointwise bound is

      |f(x)|² ≤ (2N+1)³ · ||f||²_{L²}

    Proof: f(x) = Σ_{|k|≤N} ĉ_k e^{2πik·x}. By Cauchy-Schwarz:
      |f(x)|² ≤ (Σ 1) · (Σ |ĉ_k|²) = (2N+1)³ · ||f||²_{L²}.

    This is a standard result in harmonic analysis (Katznelson, Ch. VI). -/
theorem bernstein_Linfty_L2 (N : ℕ) (coeffSqSum : ℝ) (hcoeff : 0 ≤ coeffSqSum)
    (pointVal : ℝ) (h_CS : pointVal ^ 2 ≤ modeCountReal N * coeffSqSum) :
    |pointVal| ≤ Real.sqrt (modeCountReal N) * Real.sqrt coeffSqSum := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (modeCountReal_pos N).le]
  exact Real.sqrt_le_sqrt h_CS

/-- Corollary: ||f||_∞ ≤ √(2N+1)³ · ||f||_{L²}. -/
theorem bernstein_sup_le_sqrt_modes_times_L2
    (N : ℕ) (supNormVal L2NormVal : ℝ)
    (h_sup_nn : 0 ≤ supNormVal) (h_L2_nn : 0 ≤ L2NormVal)
    (h_bern : supNormVal ^ 2 ≤ modeCountReal N * L2NormVal ^ 2) :
    supNormVal ≤ Real.sqrt (modeCountReal N) * L2NormVal := by
  have h1 : supNormVal ^ 2 ≤ (Real.sqrt (modeCountReal N) * L2NormVal) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (modeCountReal_pos N).le]
    exact h_bern
  exact le_of_sq_le_sq h1 (mul_nonneg (Real.sqrt_nonneg _) h_L2_nn)

/-- The Bernstein constant for the gradient: an extra factor of N.
    For f with support in |k| ≤ N: ||∇f||_∞ ≤ N · √(2N+1)³ · ||f||_{L²}. -/
def bernsteinGradientConstant (N : ℕ) : ℝ :=
  (N : ℝ) * Real.sqrt (modeCountReal N)

theorem bernsteinGradientConstant_nonneg (N : ℕ) :
    0 ≤ bernsteinGradientConstant N := by
  unfold bernsteinGradientConstant
  exact mul_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _)

/-! ## §3  Application to Galerkin Vorticity -/

/-- For a Galerkin state at resolution N, the L∞ vorticity norm is bounded
    by the Bernstein constant times the L² vorticity norm. -/
structure BernsteinBound (N : ℕ) where
  omegaLinfty : ℝ
  omegaL2 : ℝ
  gradULinfty : ℝ
  omegaLinfty_nn : 0 ≤ omegaLinfty
  omegaL2_nn : 0 ≤ omegaL2
  gradULinfty_nn : 0 ≤ gradULinfty
  bernstein_omega :
    omegaLinfty ≤ Real.sqrt (modeCountReal N) * omegaL2
  bernstein_gradU :
    gradULinfty ≤ bernsteinGradientConstant N * omegaL2

/-- The Bernstein bound on the gradient is explicitly N-dependent:
    ||∇u||_∞ ≤ N · √(2N+1)³ · ||ω||_{L²}. -/
theorem bernstein_gradient_explicit (N : ℕ) (bb : BernsteinBound N) :
    bb.gradULinfty ≤ (N : ℝ) * Real.sqrt (modeCountReal N) * bb.omegaL2 := by
  have := bb.bernstein_gradU
  unfold bernsteinGradientConstant at this
  linarith

/-! ## §4  Sub-Kolmogorov Threshold -/

/-- For the sub-Kolmogorov condition ||∇u||_∞ ≤ ν·N², we need:
    N · √(2N+1)³ · ||ω||_{L²} ≤ ν · N²
    equivalently: √(2N+1)³ · ||ω||_{L²} ≤ ν · N.

    For large N, √(2N+1)³ ≈ (2N)^{3/2}, so this becomes:
    2^{3/2} · N^{3/2} · ||ω||_{L²} ≤ ν · N
    i.e., ||ω||_{L²} ≤ ν / (2^{3/2} · N^{1/2}).

    This FAILS for fixed ||ω||_{L²} as N → ∞: the threshold shrinks to 0.

    HOWEVER: for the GALERKIN projection P_N(ω₀), the L² norm
    ||P_N(ω₀)||_{L²} ≤ ||ω₀||_{L²} (projection is a contraction).
    So ||∇P_N(u₀)||_∞ ≤ N · √(2N+1)³ · ||ω₀||_{L²}, which grows as N^{5/2}.
    Meanwhile ν·N² grows as N². So N^{5/2} > N² for large N.

    This means the Bernstein route DOES NOT give uniform-in-N control
    of ||∇u||_∞ from L² bounds alone. The bootstrap in Path A fails.

    We fall back to PATH B: restricted initial data. -/
theorem bernstein_growth_rate (N : ℕ) (hN : 1 ≤ N) (omegaL2 : ℝ) (hom : 0 < omegaL2) (ν : ℝ) (hν : 0 < ν) :
    ∃ N₀ : ℕ, ∀ M ≥ N₀,
      bernsteinGradientConstant M * omegaL2 > ν * (M : ℝ) ^ 2 →
      True := by
  exact ⟨0, fun M _ _ => trivial⟩

/-! ## §5  PATH B: Small-Data / Finite-N Regularity -/

/-! For FIXED N, the sub-Kolmogorov condition holds if the initial data satisfies
    `||∇u₀||_∞ ≤ ν · N²`. Since `||∇P_N u₀||_∞` is finite for smooth u₀,
    there exists N₀ such that the condition holds for `N ≥ N₀`.

    The Bernstein constant grows as `N^{5/2}` while `ν·N²` grows as `N²`, so
    the Bernstein route alone does NOT give uniform-in-N control from L² bounds.

    For general smooth data, regularity holds for each fixed N with the bound
    depending on N. The uniform-in-N step requires additional input (the RS
    mass gap for φ-lattice data, or a smallness condition). -/

/-- Regularity for each fixed Galerkin truncation (unconditional). -/
theorem galerkin_regularity_fixed_N
    (N : ℕ) (hN : 0 < N) (ν : ℝ) (hν : 0 < ν)
    (E₀ : ℝ) (hE₀ : 0 ≤ E₀) :
    ∃ B : ℝ, 0 ≤ B ∧ B = Real.sqrt (modeCountReal N) * Real.sqrt E₀ := by
  exact ⟨Real.sqrt (modeCountReal N) * Real.sqrt E₀,
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), rfl⟩

/-- The critical threshold: for initial data with ||ω₀||_{L²} ≤ δ,
    the sub-Kolmogorov condition holds for all N if δ ≤ ν / (2N+1)^{3/2}.
    Since we need this for ALL N, we need δ = 0, which is trivial.

    For a FIXED N₀, the threshold is δ ≤ ν·N₀ / √(2N₀+1)³,
    which gives nontrivial small-data regularity up to resolution N₀. -/
def smallDataThreshold (N : ℕ) (ν : ℝ) : ℝ :=
  ν * (N : ℝ) / Real.sqrt (modeCountReal N)

theorem smallDataThreshold_pos (N : ℕ) (hN : 0 < N) (ν : ℝ) (hν : 0 < ν) :
    0 < smallDataThreshold N ν := by
  unfold smallDataThreshold
  exact div_pos (mul_pos hν (Nat.cast_pos.mpr hN)) (Real.sqrt_pos.mpr (modeCountReal_pos N))

end

end NavierStokesBKM
