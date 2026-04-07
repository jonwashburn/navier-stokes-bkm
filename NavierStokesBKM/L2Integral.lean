/-
L2 Integral: Measure-Theoretic Norms and J-Cost
================================================

1. Proper L² norm via Bochner integral over ℝ³.
2. J-cost function J(x) = ½(x + x⁻¹) − 1 with AM-GM property.
3. RS-compatible fields and the φ-lattice energy bound.
-/

import NavierStokesBKM.BasicDefinitions
import NavierStokesBKM.RSConstants

namespace NavierStokesBKM

open Real MeasureTheory

noncomputable section

/-! ## §1  Product Lebesgue Measure on ℝ³ -/

def volumeR3 : Measure (Fin 3 → ℝ) :=
  Measure.pi (fun _ : Fin 3 => MeasureTheory.volume)

/-! ## §2  Proper L² Norm -/

def L2NormSqReal (u : VectorField) : ℝ :=
  ∫ x : Fin 3 → ℝ, ‖u x‖ ^ 2 ∂volumeR3

lemma L2NormSqReal_nonneg (u : VectorField) : 0 ≤ L2NormSqReal u := by
  unfold L2NormSqReal; exact integral_nonneg (fun x => by positivity)

def energyRS (u : VectorField) : ℝ := (1 / 2) * L2NormSqReal u

lemma energyRS_nonneg (u : VectorField) : 0 ≤ energyRS u :=
  mul_nonneg (by norm_num) (L2NormSqReal_nonneg u)

end

/-! ## §3  The J-Cost Function -/

noncomputable def J_cost (x : ℝ) : ℝ := (1 / 2) * (x + x⁻¹) - 1

theorem J_cost_nonneg (x : ℝ) (hx : 0 < x) : 0 ≤ J_cost x := by
  unfold J_cost
  suffices h : 2 ≤ x + x⁻¹ by linarith
  have key : 0 ≤ (x - 1) ^ 2 / x := div_nonneg (sq_nonneg _) hx.le
  have expand : (x - 1) ^ 2 / x = x + x⁻¹ - 2 := by field_simp; ring
  linarith [expand ▸ key]

theorem J_cost_zero_iff (x : ℝ) (hx : 0 < x) : J_cost x = 0 ↔ x = 1 := by
  constructor
  · intro h
    unfold J_cost at h
    have hx2 : x + x⁻¹ = 2 := by linarith
    have hdiff : (x - 1) ^ 2 / x = 0 := by
      have expand : (x - 1) ^ 2 / x = x + x⁻¹ - 2 := by field_simp; ring
      linarith [expand]
    have hnum : (x - 1) ^ 2 = 0 :=
      (div_eq_zero_iff.mp hdiff).resolve_right (ne_of_gt hx)
    linarith [sq_eq_zero_iff.mp hnum]
  · intro h; subst h; norm_num [J_cost]

theorem J_cost_phi_pos : 0 < J_cost φ := by
  have hφp : 0 < φ := lt_trans one_pos φ_gt_one
  have hge : 0 ≤ J_cost φ := J_cost_nonneg φ hφp
  rcases hge.lt_or_eq with h | h
  · exact h
  · exfalso
    have heq1 : φ = 1 := (J_cost_zero_iff φ hφp).mp h.symm
    linarith [φ_gt_one]

theorem J_cost_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : J_cost x ≤ J_cost y := by
  unfold J_cost
  have hxp : 0 < x := lt_of_lt_of_le one_pos hx
  have hyp : 0 < y := lt_of_lt_of_le one_pos (le_trans hx hxy)
  suffices h : x + x⁻¹ ≤ y + y⁻¹ by linarith
  have key : 0 ≤ (y - x) * (1 - 1 / (x * y)) := by
    apply mul_nonneg
    · linarith
    · rw [sub_nonneg, div_le_one (mul_pos hxp hyp)]
      exact le_trans hx (le_mul_of_one_le_right hxp.le (le_trans hx hxy))
  linarith [show (y - x) * (1 - 1 / (x * y)) = y + y⁻¹ - (x + x⁻¹) by field_simp; ring, key]

/-! ## §4  RS-Compatible Fields -/

structure RSCompatibleField (u : VectorField) : Prop where
  compact_support : ∃ R : ℝ, R > 0 ∧ ∀ x : Fin 3 → ℝ, R ≤ ‖x‖ → u x = 0
  phi_bound : ∃ n : ℕ, ∀ x : Fin 3 → ℝ, ‖u x‖ ≤ φ ^ n
  measurable : Measurable u

theorem j_cost_pointwise_bound (u : VectorField) (hRS : RSCompatibleField u) :
    ∃ n : ℕ, ∀ x : Fin 3 → ℝ, ‖u x‖ ^ 2 ≤ (φ ^ n) ^ 2 := by
  obtain ⟨n, h_bound⟩ := hRS.phi_bound
  exact ⟨n, fun x => by
    have hnn : 0 ≤ ‖u x‖ := norm_nonneg _
    have hpn : 0 ≤ φ ^ n := pow_nonneg (le_of_lt (lt_trans one_pos φ_gt_one)) n
    exact sq_le_sq' (by linarith [h_bound x]) (h_bound x)⟩

theorem rs_mass_gap_positive : 0 < J_cost φ := J_cost_phi_pos

end NavierStokesBKM
