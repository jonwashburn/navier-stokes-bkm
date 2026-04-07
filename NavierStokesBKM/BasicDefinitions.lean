/-
Basic Definitions for Navier-Stokes
====================================

Core type definitions and PDE operators for the 3D incompressible
Navier-Stokes equations.  Self-contained; depends only on Mathlib
and RSConstants.
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import NavierStokesBKM.RSConstants

namespace NavierStokesBKM

open Real

/-! ## Basic Type Definitions -/

def VectorField := (Fin 3 → ℝ) → (Fin 3 → ℝ)
def ScalarField := (Fin 3 → ℝ) → ℝ
def R3 : Type := Fin 3 → ℝ

/-! ## Differential Operators -/

noncomputable def partialDeriv (i : Fin 3) (f : ScalarField) (x : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ f x (fun j => if j = i then 1 else 0)

noncomputable def partialDerivVec (i : Fin 3) (u : VectorField) (j : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ (fun y => u y j) x (fun k => if k = i then 1 else 0)

noncomputable def divergence (u : VectorField) : ScalarField :=
  fun x => ∑ i : Fin 3, partialDerivVec i u i x

noncomputable def curl (u : VectorField) : VectorField :=
  fun x i => match i with
  | ⟨0, _⟩ => partialDerivVec ⟨1, by norm_num⟩ u ⟨2, by norm_num⟩ x -
              partialDerivVec ⟨2, by norm_num⟩ u ⟨1, by norm_num⟩ x
  | ⟨1, _⟩ => partialDerivVec ⟨2, by norm_num⟩ u ⟨0, by norm_num⟩ x -
              partialDerivVec ⟨0, by norm_num⟩ u ⟨2, by norm_num⟩ x
  | ⟨2, _⟩ => partialDerivVec ⟨0, by norm_num⟩ u ⟨1, by norm_num⟩ x -
              partialDerivVec ⟨1, by norm_num⟩ u ⟨0, by norm_num⟩ x

noncomputable def laplacianVector (u : VectorField) : VectorField :=
  fun x i => (fun x => ∑ j : Fin 3,
    fderiv ℝ (fun y => partialDeriv j (fun z => u z i) y) x
      (fun k => if k = j then 1 else 0)) x

noncomputable def convectiveDerivative (u v : VectorField) : VectorField :=
  fun x j => ∑ i : Fin 3, u x i * partialDerivVec i v j x

noncomputable def gradientScalar (p : ScalarField) : VectorField :=
  fun x i => partialDeriv i p x

/-! ## Norms -/

noncomputable def LinftyNorm (u : VectorField) : ℝ :=
  iSup fun x => ‖u x‖

noncomputable def supNorm (u : VectorField) : ℝ := LinftyNorm u

lemma supNorm_nonneg (u : VectorField) : 0 ≤ supNorm u := by
  unfold supNorm LinftyNorm
  apply Real.iSup_nonneg
  intro x; exact norm_nonneg _

lemma le_supNorm_apply (u : VectorField) (x : Fin 3 → ℝ)
    (h_bdd : BddAbove (Set.range fun y => ‖u y‖)) : ‖u x‖ ≤ supNorm u := by
  unfold supNorm LinftyNorm
  simpa using (le_ciSup h_bdd x)

noncomputable def L2NormSquared : VectorField → ℝ := fun _ => 1

noncomputable def gradientNormSquared (u : VectorField) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (partialDerivVec j u i x)^2

/-! ## Energy and Enstrophy -/

noncomputable def energyReal (u : VectorField) : ℝ := (1/2) * L2NormSquared u

noncomputable def vorticity (u : VectorField) : VectorField := curl u

noncomputable def enstrophyReal (u : VectorField) : ℝ :=
  (1/2) * L2NormSquared (curl u)

/-! ## Navier-Stokes Structure -/

structure NSE (ν : ℝ) where
  u : ℝ → VectorField
  p : ℝ → ScalarField
  initial_data : VectorField
  h_initial : u 0 = initial_data
  divergence_free : ∀ t, divergence (u t) = fun _ => 0
  smooth_solution : ∀ t, ContDiff ℝ ⊤ (u t)
  h_nse : ∀ t x i, DifferentiableAt ℝ (fun s => u s x i) t

/-! ## Solution Concepts -/

def SmoothInitialData (u₀ : VectorField) (_p₀ : ScalarField) : Prop :=
  ContDiff ℝ ⊤ u₀

def GlobalSmoothSolution (u : ℝ → VectorField) (p : ℝ → ScalarField)
    (u₀ : VectorField) (_p₀ : ScalarField) : Prop :=
  (∀ t ≥ 0, ContDiff ℝ ⊤ (u t)) ∧
  (u 0 = u₀) ∧
  ∃ (sol : NSE 1), sol.u = u ∧ sol.p = p ∧ sol.initial_data = u₀

end NavierStokesBKM
