/-
BKM Criterion: Beale-Kato-Majda in the RS Framework
=====================================================

§1  BKM integral (interval integral formulation).
§2  BKM regularity criterion (hypothesis structure).
§3  RS cascade cutoff → uniform vorticity bound → finite BKM.
§4  Chain: RS → finite BKM → global regularity.
-/

import NavierStokesBKM.RSConstants
import NavierStokesBKM.BasicDefinitions
import NavierStokesBKM.RSClassicalBridge

namespace NavierStokesBKM.BKM

open Real MeasureTheory Set intervalIntegral
open NavierStokesBKM
open NavierStokesBKM.RSClassical

/-! ## §1  The BKM Integral -/

noncomputable def bkmIntegral (ω_max : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, ω_max t

theorem bounded_implies_bkm_finite
    (ω_max : ℝ → ℝ) (T C : ℝ) (hT : 0 < T) (_hC : 0 ≤ C)
    (h_bound : ∀ t ∈ Set.uIcc 0 T, ω_max t ≤ C)
    (_h_nn : ∀ t, 0 ≤ ω_max t)
    (h_int : IntervalIntegrable ω_max MeasureTheory.volume 0 T) :
    bkmIntegral ω_max T ≤ C * T := by
  unfold bkmIntegral
  have hT' : (0 : ℝ) ≤ T := le_of_lt hT
  calc ∫ t in (0:ℝ)..T, ω_max t
      ≤ ∫ _ in (0:ℝ)..T, C := by
        apply intervalIntegral.integral_mono_on hT' h_int
          (_root_.intervalIntegrable_const)
        intro t ht
        exact h_bound t (Set.uIcc_of_le hT' ▸ ht)
    _ = C * T := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-! ## §2  BKM Regularity Criterion -/

/-- BKM Regularity Hypothesis (Beale-Kato-Majda 1984).
    Bounded vorticity on every [0, T] → global smoothness. -/
structure BKMRegularityHypothesis (ν : ℝ) (nse : NSE ν) : Prop where
  regularity :
    (∀ T > 0, ∃ C_T > 0, ∀ t ∈ Set.Icc 0 T,
        supNorm (vorticity (nse.u t)) ≤ C_T) →
    ∀ t ≥ 0, ContDiff ℝ ⊤ (nse.u t)

theorem bkm_finite_implies_regularity
    (ν : ℝ) (nse : NSE ν)
    (H_bkm : BKMRegularityHypothesis ν nse)
    (h_bound : ∀ T > 0, ∃ C_T > 0, ∀ t ∈ Set.Icc 0 T,
        supNorm (vorticity (nse.u t)) ≤ C_T) :
    ∀ t ≥ 0, ContDiff ℝ ⊤ (nse.u t) :=
  H_bkm.regularity h_bound

/-! ## §3  RS Cascade → Bounded BKM -/

theorem rs_cascade_vorticity_bound (ν : ℝ) (hν : 0 < ν) (nse : NSE ν)
    (H : VorticityBoundDirectHypothesis ν nse) :
    ∀ T > 0, ∃ C_T > 0, ∀ t ∈ Set.Icc 0 T,
        supNorm (vorticity (nse.u t)) ≤ C_T := by
  intro T _hT
  exact ⟨C_star / Real.sqrt ν,
    div_pos C_star_pos (Real.sqrt_pos.mpr hν),
    fun t ht => H.bound t ht.1⟩

/-! ## §4  Chain: RS → Finite BKM → Global Regularity -/

theorem rs_cascade_implies_global_regularity
    (ν : ℝ) (hν : 0 < ν) (nse : NSE ν)
    (H_vort : VorticityBoundDirectHypothesis ν nse)
    (H_bkm  : BKMRegularityHypothesis ν nse) :
    ∀ t ≥ 0, ContDiff ℝ ⊤ (nse.u t) :=
  bkm_finite_implies_regularity ν nse H_bkm
    (rs_cascade_vorticity_bound ν hν nse H_vort)

theorem rs_bootstrap_implies_global_regularity
    (ν : ℝ) (hν : 0 < ν) (nse : NSE ν)
    (H_vort : VorticityBoundDirectHypothesis ν nse)
    (H_boot : VorticityBootstrapHypothesis ν nse)
    (H_bkm  : BKMRegularityHypothesis ν nse) :
    ∀ t ≥ 0, ContDiff ℝ ⊤ (nse.u t) :=
  bkm_finite_implies_regularity ν nse H_bkm (fun T hT =>
    ⟨K_star / Real.sqrt ν,
      div_pos K_star_pos (Real.sqrt_pos.mpr hν),
      fun t ht => H_boot.bootstrap H_vort.bound t ht.1⟩)

end NavierStokesBKM.BKM
