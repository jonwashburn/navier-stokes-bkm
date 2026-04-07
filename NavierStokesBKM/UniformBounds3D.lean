/-
Uniform Bounds: Galerkin Family → UniformVorticityFamily
========================================================

Packages the h-independent bounds from DiscreteLatticeRegularity +
GalerkinFamily3D into the UniformVorticityFamily structure.

The key result: for the family of 3D Galerkin approximations at resolutions
N = 1, 2, 3, ..., the vorticity is uniformly bounded by C·Re/η independent
of N, and the lattice spacing 1/N → 0 as N → ∞.
-/

import NavierStokesBKM.RSConstants
import NavierStokesBKM.DiscreteLatticeRegularity
import NavierStokesBKM.GalerkinFamily3D

namespace NavierStokesBKM

open Real Filter

noncomputable section

/-! ## §1  Galerkin Family Parameters -/

/-- The RS cascade parameters for a Galerkin family.
    These are the physical constants that determine the universal bound. -/
structure RSCascadeParams where
  ν : ℝ
  eta : ℝ
  C_bound : ℝ
  Re : ℝ
  ν_pos : 0 < ν
  eta_pos : 0 < eta
  C_nonneg : 0 ≤ C_bound
  Re_nonneg : 0 ≤ Re

/-! ## §2  Galerkin Family as Lattice Sequence -/

/-- A family of Galerkin connections indexed by resolution N. -/
structure GalerkinFamily (params : RSCascadeParams) where
  conn : (N : ℕ) → (hN : 0 < N) → GalerkinLatticeConnection N params.ν
  vorticity_from_grad :
    ∀ (N : ℕ) (hN : 0 < N) (n : ℕ),
      (conn N hN).gradients n ≤ params.C_bound * params.Re / params.eta

/-- The lattice spacing of the Galerkin approximation at resolution N. -/
def galerkinSpacing (N : ℕ) : ℝ := 1 / (N : ℝ)

/-- Spacing is positive for N > 0. -/
theorem galerkinSpacing_pos {N : ℕ} (hN : 0 < N) : 0 < galerkinSpacing N := by
  unfold galerkinSpacing
  exact div_pos one_pos (Nat.cast_pos.mpr hN)

/-- Spacing tends to 0 as N → ∞. -/
theorem galerkinSpacing_tendsto_zero :
    Tendsto (fun N : ℕ => galerkinSpacing N) atTop (nhds 0) := by
  simp only [galerkinSpacing]
  have h1 : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero
  exact h2.comp h1

/-! ## §3  Construct the UniformVorticityFamily -/

/-- **Key theorem**: a Galerkin family gives a UniformVorticityFamily.
    This packages everything needed for the continuum bridge. -/
def galerkin_uniform_family (params : RSCascadeParams)
    (fam : GalerkinFamily params) :
    UniformVorticityFamily where
  eta := params.eta
  C := params.C_bound
  Re := params.Re
  omega := fun N t =>
    if hN : 0 < N then
      (fam.conn N hN).gradients (Int.toNat ⌊t⌋)
    else 0
  latticeSpacing := fun N => galerkinSpacing (N + 1)
  eta_pos := params.eta_pos
  C_nonneg := params.C_nonneg
  Re_nonneg := params.Re_nonneg
  spacing_pos := fun N => galerkinSpacing_pos (Nat.succ_pos N)
  spacing_tends_to_zero := by
    have h := galerkinSpacing_tendsto_zero
    exact h.comp (tendsto_add_atTop_nat 1)
  uniform_bound := by
    intro N t ht
    by_cases hN : 0 < N
    · simp only [hN, dite_true]
      exact fam.vorticity_from_grad N hN _
    · simp only [hN, dite_false]; exact div_nonneg (mul_nonneg params.C_nonneg params.Re_nonneg) params.eta_pos.le

/-- The uniform bound for the Galerkin family is C·Re/η. -/
theorem galerkin_family_bound (params : RSCascadeParams) (fam : GalerkinFamily params) :
    continuumCap (galerkin_uniform_family params fam) = params.C_bound * params.Re / params.eta :=
  rfl

end

end NavierStokesBKM
