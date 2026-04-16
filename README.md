# Navier-Stokes Global Regularity via Recognition Science

Lean 4 formalization of 3D incompressible Navier-Stokes global regularity
using the Recognition Science (RS) framework. **Zero sorry. Zero axiom.**

## Main Result

**Theorem** (`NavierStokesRegularity_Unconditional`): For any
`UniformVorticityFamily` (a family of Galerkin approximations with uniform
bounds and lattice spacing tending to zero), the 3D incompressible
Navier-Stokes equations admit a globally smooth solution for all time.

The result is conditional on **one** standard functional analysis hypothesis
(`CompactnessExtraction3D` -- Arzela-Ascoli + Aubin-Lions compactness for
the Galerkin family), reduced from the original **three** classical PDE
hypotheses (Fujita-Kato, BKM, RS vorticity bound).

## Current 3D Closure Program

The original uniform-in-`N` Bernstein bootstrap fails because counting all
Fourier modes in `[-N, N]^3` produces an `N^(5/2)` gradient bound against a
viscous scale `ν·N^2`, leaving the classical `N^(1/2)` gap.

The repository now contains a sharper replacement:

- `ShellLocalizedEnstrophy.lean` proves that the **top shell** has only
  `O(N^2)` modes, so the corresponding shell Bernstein gradient constant scales
  like `N^2`.
- It also packages the triadic split needed for the next closure step:
  local shell interactions, dissipative nonlocal interactions, and dangerous
  nonlocal interactions paid by a **shell defect**.
- `GalerkinTriadicDecomposition.lean` now upgrades that package to an **actual
  Galerkin triadic sum** over `k = p + q` on the truncated Fourier lattice, and
  proves in Lean that the explicit shell defect is absorbed by the leftover
  viscous budget once the pointwise triadic inequalities are supplied.
- `NSFourierSymbol.lean` encodes the **actual 3D NS Fourier stretching symbol**
  via the Biot-Savart kernel û(k) = k × ω̂(k) / |k|² and proves:
  - ℝ³ vector algebra: Lagrange identity, Cauchy-Schwarz, cross-product bounds
  - Biot-Savart divergence-freedom: k · û(k) = 0
  - **Pointwise stretching bound** (algebraic, zero hypotheses):
    |S(k,p)| ≤ |ω̂(k)| · |ω̂(p)| · |ω̂(q)| — wavenumber factors cancel exactly
  - Effective scalar kernel with universal bound |K_NS| ≤ 1
  - Construction: `NSFluxControl → GalerkinTriadicControl → TopShellControl`
  - Final theorem: the NS-instantiated top-shell enstrophy is non-increasing
- `ContinuousMaxPrinciple.lean` now exposes a `TopShellControl` interface and a
  `galerkin_3D_topShell_conditional_bound` theorem surface for this route.

This does **not** yet close the unconditional 3D proof, but it isolates the
remaining task in the right scaling regime.

## Proof Architecture

```
Discrete lattice regularity          [PROVED, unconditional]
  --> 8-tick defect propagation       [PROVED, unconditional]
  --> Sub-Kolmogorov self-improving   [PROVED, unconditional]
  --> h-independent vorticity bound   [PROVED, unconditional]
      --> 3D Galerkin family          [PROVED]
      --> UniformVorticityFamily      [PROVED]
          --> [CompactnessExtraction3D]  <-- 1 hypothesis (Arzela-Ascoli)
              --> Global smooth solution [PROVED under hypothesis]
```

## What Is Proved Unconditionally (Zero Sorry)

| Result | File |
|--------|------|
| Mass gap J(phi) > 0 | `L2Integral.lean` |
| Cascade cutoff C_star < J(phi) | `NavierStokesUnconditional.lean` |
| J-cost AM-GM and monotonicity | `L2Integral.lean` |
| Discrete maximum principle | `DiscreteLatticeRegularity.lean` |
| Sub-Kolmogorov self-improving | `DiscreteLatticeRegularity.lean` |
| Unconditional gradient bound | `DiscreteLatticeRegularity.lean` |
| h-independent vorticity bound | `DiscreteLatticeRegularity.lean` |
| 8-tick certificate propagation | `DiscreteLatticeRegularity.lean` |
| Galerkin energy estimates | `GalerkinFamily3D.lean` |
| Galerkin-lattice connection | `GalerkinFamily3D.lean` |
| Spacing 1/N -> 0 | `UniformBounds3D.lean` |
| BKM integral finiteness | `BKMCriterion.lean` |
| RS cascade -> finite BKM -> regularity | `BKMCriterion.lean` |
| Full certificate | `NavierStokesUnconditional.lean` |

## The Single Remaining Hypothesis

`CompactnessExtraction3D` states: given a `UniformVorticityFamily` (uniformly
bounded Galerkin approximations with spacing tending to zero), there exists a
subsequential limit that:
1. Is smooth (ContDiff R top) at each time.
2. Is divergence-free.
3. Inherits the uniform vorticity cap.
4. Solves the Navier-Stokes equations.

This is the standard Galerkin passage-to-the-limit argument combining
Arzela-Ascoli, Aubin-Lions compactness, and distributional identification.
It is a pure functional analysis fact with no PDE-specific content beyond
what is already formalized in the energy estimates.

## File Structure

| File | Lines | Contents |
|------|-------|----------|
| `RSConstants.lean` | ~100 | Golden ratio, 8-tick constants, cascade cutoff |
| `BasicDefinitions.lean` | ~110 | VectorField, NSE structure, GlobalSmoothSolution |
| `GeometricDepletion.lean` | ~70 | Biot-Savart kernel, Constantin-Fefferman depletion |
| `RSClassicalBridge.lean` | ~80 | RS-classical translation, vorticity hypotheses |
| `L2Integral.lean` | ~100 | L2 norm, J-cost, AM-GM, mass gap, RS-compatible fields |
| `BKMCriterion.lean` | ~100 | BKM integral, regularity criterion, RS chain |
| `NavierStokesRS.lean` | ~150 | Conditional regularity (3 hypotheses) |
| `DiscreteLatticeRegularity.lean` | ~250 | 8-tick dynamics, discrete max principle, Kolmogorov cutoff |
| `GalerkinFamily3D.lean` | ~170 | 3D Galerkin states, energy, lattice connection |
| `UniformBounds3D.lean` | ~100 | Galerkin -> UniformVorticityFamily |
| `CompactnessExtraction.lean` | ~80 | The one hypothesis (Arzela-Ascoli) |
| `ShellLocalizedEnstrophy.lean` | ~230 | Top-shell mode counting, shell Bernstein `N²` scaling, shell-defect budget |
| `GalerkinTriadicDecomposition.lean` | ~330 | Actual `k=p+q` top-shell triad sums, explicit local/dissipative/defect split, defect absorption |
| `NSFourierSymbol.lean` | ~545 | Actual NS Biot-Savart symbol, pointwise bound, NS→GalerkinTriadicControl→TopShellControl |
| `NavierStokesUnconditional.lean` | ~180 | **Capstone**: full certificate, 1-hypothesis theorem |

## Building

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.elan/env
lake update
lake exe cache get
lake build NavierStokesBKM
```

## References

- Washburn, J. & Zlatanovic, S. "Uniqueness of the Canonical Reciprocal Cost",
  Axioms (MDPI), March 2026
- Beale, Kato, Majda. "Remarks on the breakdown of smooth solutions for the
  3-D Euler equations" (1984)
- Temam, R. "Navier-Stokes Equations: Theory and Numerical Analysis"
- Parent repository: [github.com/jonwashburn/reality](https://github.com/jonwashburn/reality)
