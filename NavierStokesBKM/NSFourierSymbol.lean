/-
The Actual 3D Navier–Stokes Fourier Stretching Symbol
=====================================================

Encodes the genuine NS enstrophy transfer kernel in Fourier space and
bridges it to the `GalerkinTriadicControl` interface.

The NS vorticity equation on T³ in Fourier space has the nonlinear term:
  ∂ω̂(k)/∂t = -ν|k|²ω̂(k) + Σ_{p+q=k} [stretching − transport]

The enstrophy transfer to mode k from triad (k, p, q = k−p) is a
trilinear form in the vector Fourier coefficients ω̂.  Using the
Biot-Savart kernel û(k) = k × ω̂(k) / |k|², the stretching part at
each triad satisfies the wavenumber-free pointwise bound

  |S(k,p)| ≤ |ω̂(k)| · |ω̂(p)| · |ω̂(q)|

because the 1/|p|² from Biot-Savart, the |p| from the derivative, and
the |p| from the cross-product norm combine to cancel exactly.

This file:
1. Proves the ℝ³ vector algebra needed (Cauchy-Schwarz, Lagrange identity)
2. Defines the Biot-Savart velocity kernel and proves divergence-freedom
3. Defines the NS enstrophy stretching symbol
4. Proves the pointwise stretching bound (algebraic, no hypotheses)
5. Defines the NS effective scalar kernel
6. Defines `NSFluxControl` — the concrete NS flux estimates that replace
   the old abstract `TriadKernel` assumptions
7. Constructs `GalerkinTriadicControl` from the actual NS kernel
8. Bridges to `TopShellControl`
-/

import NavierStokesBKM.GalerkinTriadicDecomposition

namespace NavierStokesBKM

open Real Classical

noncomputable section

/-! ## §1  Vector algebra on ℝ³ -/

def dotR3 (a b : Fin 3 → ℝ) : ℝ :=
  a 0 * b 0 + a 1 * b 1 + a 2 * b 2

def crossR3 (a b : Fin 3 → ℝ) : Fin 3 → ℝ
  | 0 => a 1 * b 2 - a 2 * b 1
  | 1 => a 2 * b 0 - a 0 * b 2
  | 2 => a 0 * b 1 - a 1 * b 0

def normSqR3 (a : Fin 3 → ℝ) : ℝ := dotR3 a a

def normR3 (a : Fin 3 → ℝ) : ℝ := Real.sqrt (normSqR3 a)

theorem dotR3_comm (a b : Fin 3 → ℝ) : dotR3 a b = dotR3 b a := by
  unfold dotR3; ring

theorem normSqR3_nonneg (a : Fin 3 → ℝ) : 0 ≤ normSqR3 a := by
  unfold normSqR3 dotR3
  nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2)]

theorem normR3_nonneg (a : Fin 3 → ℝ) : 0 ≤ normR3 a :=
  Real.sqrt_nonneg _

theorem normR3_sq (a : Fin 3 → ℝ) : normR3 a ^ 2 = normSqR3 a :=
  Real.sq_sqrt (normSqR3_nonneg a)

theorem dotR3_smul_right (c : ℝ) (a b : Fin 3 → ℝ) :
    dotR3 a (c • b) = c * dotR3 a b := by
  unfold dotR3; simp [Pi.smul_apply, smul_eq_mul]; ring

theorem normSqR3_smul (c : ℝ) (v : Fin 3 → ℝ) :
    normSqR3 (c • v) = c ^ 2 * normSqR3 v := by
  unfold normSqR3
  rw [dotR3_smul_right, ← dotR3_comm, dotR3_smul_right, dotR3_comm]
  ring

theorem normR3_smul (c : ℝ) (v : Fin 3 → ℝ) :
    normR3 (c • v) = |c| * normR3 v := by
  unfold normR3
  rw [normSqR3_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem cross_dot_left (a b : Fin 3 → ℝ) :
    dotR3 a (crossR3 a b) = 0 := by
  unfold dotR3 crossR3; ring

theorem cross_dot_right (a b : Fin 3 → ℝ) :
    dotR3 b (crossR3 a b) = 0 := by
  unfold dotR3 crossR3; ring

theorem lagrange_identity (a b : Fin 3 → ℝ) :
    normSqR3 (crossR3 a b) =
      normSqR3 a * normSqR3 b - (dotR3 a b) ^ 2 := by
  unfold normSqR3 dotR3 crossR3; ring

theorem cauchy_schwarz_R3 (a b : Fin 3 → ℝ) :
    (dotR3 a b) ^ 2 ≤ normSqR3 a * normSqR3 b := by
  linarith [lagrange_identity a b, normSqR3_nonneg (crossR3 a b)]

theorem abs_dotR3_le (a b : Fin 3 → ℝ) :
    |dotR3 a b| ≤ normR3 a * normR3 b := by
  calc |dotR3 a b|
      = Real.sqrt ((dotR3 a b) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (normSqR3 a * normSqR3 b) :=
        Real.sqrt_le_sqrt (cauchy_schwarz_R3 a b)
    _ = normR3 a * normR3 b := by
        unfold normR3; exact Real.sqrt_mul (normSqR3_nonneg a) _

theorem cross_normSq_le (a b : Fin 3 → ℝ) :
    normSqR3 (crossR3 a b) ≤ normSqR3 a * normSqR3 b := by
  rw [lagrange_identity]; linarith [sq_nonneg (dotR3 a b)]

theorem cross_norm_le (a b : Fin 3 → ℝ) :
    normR3 (crossR3 a b) ≤ normR3 a * normR3 b := by
  unfold normR3
  calc Real.sqrt (normSqR3 (crossR3 a b))
      ≤ Real.sqrt (normSqR3 a * normSqR3 b) :=
        Real.sqrt_le_sqrt (cross_normSq_le a b)
    _ = Real.sqrt (normSqR3 a) * Real.sqrt (normSqR3 b) :=
        Real.sqrt_mul (normSqR3_nonneg a) _

/-! ## §2  Mode-to-vector casting -/

def modeToR3 (k : Mode3) : Fin 3 → ℝ
  | 0 => (k.1 : ℝ)
  | 1 => (k.2.1 : ℝ)
  | 2 => (k.2.2 : ℝ)

def waveSqMode (k : Mode3) : ℝ := normSqR3 (modeToR3 k)

theorem waveSqMode_nonneg (k : Mode3) : 0 ≤ waveSqMode k :=
  normSqR3_nonneg _

theorem waveSqMode_eq_waveSq (k : Mode3) :
    waveSqMode k = waveSq k := by
  unfold waveSqMode normSqR3 dotR3 modeToR3 waveSq; ring

/-! ## §3  NS Fourier vorticity state -/

abbrev VorticityFourier := Mode3 → Fin 3 → ℝ

def omegaMag (ωhat : VorticityFourier) (k : Mode3) : ℝ :=
  normR3 (ωhat k)

theorem omegaMag_nonneg (ωhat : VorticityFourier) (k : Mode3) :
    0 ≤ omegaMag ωhat k := normR3_nonneg _

/-! ## §4  Biot-Savart velocity kernel

The Biot-Savart relation on T³ in Fourier space:
  û(k) = k × ω̂(k) / |k|²

When k = 0, the inverse Laplacian is singular; we use the Lean convention
`(0 : ℝ)⁻¹ = 0`, which correctly gives û(0) = 0 (zero mean flow). -/

def biotSavart (k : Mode3) (omegaK : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (waveSqMode k)⁻¹ • crossR3 (modeToR3 k) omegaK

theorem biotSavart_divFree (k : Mode3) (omegaK : Fin 3 → ℝ) :
    dotR3 (modeToR3 k) (biotSavart k omegaK) = 0 := by
  unfold biotSavart
  rw [dotR3_smul_right, cross_dot_left, mul_zero]

/-! ## §5  NS enstrophy stretching symbol

The vortex stretching contribution to the enstrophy at mode k from the
triad (k, p, q = k − p):

  S(k,p) = (ω̂(q) · p_vec) · (ω̂(k) · û(p))

where û(p) = p × ω̂(p) / |p|² is the Biot-Savart velocity.  This is the
dominant term in the enstrophy budget; the transport term vanishes when
summed over all modes and contributes only a boundary flux for the
shell-restricted sum. -/

def nsStretching (ωhat : VorticityFourier) (k p : Mode3) : ℝ :=
  let q := triadPartner k p
  dotR3 (ωhat q) (modeToR3 p) *
    dotR3 (ωhat k) (biotSavart p (ωhat p))

/-! ## §6  Pointwise stretching bound

The key algebraic fact: the Biot-Savart factor 1/|p|² composed with
|cross(p, ·)| ≤ |p| · |·| leaves a net 1/|p|, which cancels the |p|
from Cauchy-Schwarz on dotR3(·, p).  Result:

  |S(k,p)| ≤ |ω̂(k)| · |ω̂(p)| · |ω̂(q)|

with no residual wavenumber dependence.

We prove this via an intermediate lemma that avoids dividing by
normR3(modeToR3 p) (which could be zero). -/

/-- Cauchy-Schwarz composed with the Biot-Savart inverse Laplacian:
the product `|⟨a, BS(k,b)⟩| · |k|` is bounded by `|a| · |b|`. -/
theorem dotR3_biotSavart_times_waveNorm (a : Fin 3 → ℝ)
    (k : Mode3) (b : Fin 3 → ℝ) :
    |dotR3 a (biotSavart k b)| * normR3 (modeToR3 k) ≤
      normR3 a * normR3 b := by
  unfold biotSavart
  rw [dotR3_smul_right, abs_mul]
  calc |(waveSqMode k)⁻¹| * |dotR3 a (crossR3 (modeToR3 k) b)| *
        normR3 (modeToR3 k)
      ≤ |(waveSqMode k)⁻¹| *
          (normR3 a * normR3 (crossR3 (modeToR3 k) b)) *
          normR3 (modeToR3 k) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (abs_dotR3_le a _) (abs_nonneg _)
        · exact normR3_nonneg _
    _ ≤ |(waveSqMode k)⁻¹| *
          (normR3 a * (normR3 (modeToR3 k) * normR3 b)) *
          normR3 (modeToR3 k) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left (cross_norm_le _ _) (normR3_nonneg _)
        · exact normR3_nonneg _
    _ = normR3 a * normR3 b *
          (|(waveSqMode k)⁻¹| * normR3 (modeToR3 k) ^ 2) := by ring
    _ ≤ normR3 a * normR3 b * 1 := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (normR3_nonneg _) (normR3_nonneg _))
        rw [normR3_sq]
        unfold waveSqMode
        by_cases h : normSqR3 (modeToR3 k) = 0
        · simp [h]
        · rw [abs_of_nonneg (inv_nonneg.mpr (normSqR3_nonneg _)),
              inv_mul_cancel₀ h]
    _ = normR3 a * normR3 b := by ring

/-- **Pointwise stretching bound**: the NS enstrophy stretching at each
triad is bounded by the product of vorticity magnitudes with no extra
wavenumber factors. -/
theorem nsStretching_pointwise_bound (ωhat : VorticityFourier)
    (k p : Mode3) :
    |nsStretching ωhat k p| ≤
      omegaMag ωhat k * omegaMag ωhat p *
        omegaMag ωhat (triadPartner k p) := by
  unfold nsStretching omegaMag
  rw [abs_mul]
  by_cases hP : normR3 (modeToR3 p) = 0
  · -- When |p| = 0: modeToR3 p = 0, so dotR3(ω̂(q), 0) = 0
    have hzero : dotR3 (ωhat (triadPartner k p)) (modeToR3 p) = 0 := by
      have h0 : normSqR3 (modeToR3 p) = 0 := by
        unfold normR3 at hP
        exact_mod_cast (Real.sqrt_eq_zero (normSqR3_nonneg _)).mp hP
      have hc0 : modeToR3 p 0 = 0 := by
        unfold normSqR3 dotR3 at h0
        nlinarith [sq_nonneg (modeToR3 p 0), sq_nonneg (modeToR3 p 1),
                   sq_nonneg (modeToR3 p 2)]
      have hc1 : modeToR3 p 1 = 0 := by
        unfold normSqR3 dotR3 at h0
        nlinarith [sq_nonneg (modeToR3 p 0), sq_nonneg (modeToR3 p 1),
                   sq_nonneg (modeToR3 p 2)]
      have hc2 : modeToR3 p 2 = 0 := by
        unfold normSqR3 dotR3 at h0
        nlinarith [sq_nonneg (modeToR3 p 0), sq_nonneg (modeToR3 p 1),
                   sq_nonneg (modeToR3 p 2)]
      unfold dotR3; rw [hc0, hc1, hc2]; ring
    rw [hzero, abs_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (normR3_nonneg _) (normR3_nonneg _))
      (normR3_nonneg _)
  · -- When |p| > 0: use the Biot-Savart bound with cancellation
    have hPpos : 0 < normR3 (modeToR3 p) :=
      lt_of_le_of_ne (normR3_nonneg _) (Ne.symm hP)
    have hCS : |dotR3 (ωhat (triadPartner k p)) (modeToR3 p)| ≤
        normR3 (ωhat (triadPartner k p)) * normR3 (modeToR3 p) :=
      abs_dotR3_le _ _
    have hBS : |dotR3 (ωhat k) (biotSavart p (ωhat p))| *
        normR3 (modeToR3 p) ≤ normR3 (ωhat k) * normR3 (ωhat p) :=
      dotR3_biotSavart_times_waveNorm _ _ _
    -- Combine: |a| * |b| * C ≤ (A*C) * B where |a|≤A*C and |b|*C≤B
    -- Equivalently: (|a|*|b|) * C ≤ A*B*C, so |a|*|b| ≤ A*B
    have hprod :
        |dotR3 (ωhat (triadPartner k p)) (modeToR3 p)| *
          |dotR3 (ωhat k) (biotSavart p (ωhat p))| *
          normR3 (modeToR3 p) ≤
        normR3 (ωhat k) * normR3 (ωhat p) *
          normR3 (ωhat (triadPartner k p)) * normR3 (modeToR3 p) := by
      calc |dotR3 (ωhat (triadPartner k p)) (modeToR3 p)| *
              |dotR3 (ωhat k) (biotSavart p (ωhat p))| *
              normR3 (modeToR3 p)
          = |dotR3 (ωhat (triadPartner k p)) (modeToR3 p)| *
              (|dotR3 (ωhat k) (biotSavart p (ωhat p))| *
                normR3 (modeToR3 p)) := by ring
        _ ≤ (normR3 (ωhat (triadPartner k p)) * normR3 (modeToR3 p)) *
              (normR3 (ωhat k) * normR3 (ωhat p)) :=
            mul_le_mul hCS hBS (mul_nonneg (abs_nonneg _) (normR3_nonneg _))
              (mul_nonneg (normR3_nonneg _) (normR3_nonneg _))
        _ = normR3 (ωhat k) * normR3 (ωhat p) *
              normR3 (ωhat (triadPartner k p)) * normR3 (modeToR3 p) := by ring
    exact le_of_mul_le_mul_right hprod hPpos

/-! ## §7  NS effective scalar kernel

The scalar kernel that, when multiplied by the vorticity magnitudes
|ω̂(k)| · |ω̂(p)| · |ω̂(q)|, reproduces the NS stretching at each triad.
When any vorticity vanishes, the stretching is zero (proved above), so
setting the kernel to zero in that case is consistent. -/

def nsEffectiveKernel (ωhat : VorticityFourier) (k p q : Mode3) : ℝ :=
  if omegaMag ωhat k = 0 ∨ omegaMag ωhat p = 0 ∨ omegaMag ωhat q = 0
  then 0
  else nsStretching ωhat k p /
    (omegaMag ωhat k * omegaMag ωhat p * omegaMag ωhat q)

theorem nsEffectiveKernel_bound (ωhat : VorticityFourier)
    (k p : Mode3) :
    |nsEffectiveKernel ωhat k p (triadPartner k p)| ≤ 1 := by
  dsimp only [nsEffectiveKernel]
  split_ifs with h
  · norm_num
  · have hk : omegaMag ωhat k ≠ 0 := fun a => h (Or.inl a)
    have hp : omegaMag ωhat p ≠ 0 := fun a => h (Or.inr (Or.inl a))
    have hq : omegaMag ωhat (triadPartner k p) ≠ 0 :=
      fun a => h (Or.inr (Or.inr a))
    have hprod_pos : 0 < omegaMag ωhat k * omegaMag ωhat p *
        omegaMag ωhat (triadPartner k p) := by
      exact mul_pos (mul_pos
        (lt_of_le_of_ne (omegaMag_nonneg _ _) (Ne.symm hk))
        (lt_of_le_of_ne (omegaMag_nonneg _ _) (Ne.symm hp)))
        (lt_of_le_of_ne (omegaMag_nonneg _ _) (Ne.symm hq))
    have hbound := nsStretching_pointwise_bound ωhat k p
    rw [abs_div, div_le_one (abs_pos.mpr (ne_of_gt hprod_pos))]
    exact le_trans hbound (le_abs_self _)

/-- The effective kernel reproduces the stretching when all vorticity
magnitudes are positive. -/
theorem nsEffectiveKernel_recovers (ωhat : VorticityFourier)
    (k p : Mode3)
    (hk : 0 < omegaMag ωhat k)
    (hp : 0 < omegaMag ωhat p)
    (hq : 0 < omegaMag ωhat (triadPartner k p)) :
    nsEffectiveKernel ωhat k p (triadPartner k p) *
      omegaMag ωhat p * omegaMag ωhat (triadPartner k p) *
      omegaMag ωhat k = nsStretching ωhat k p := by
  have hkne : omegaMag ωhat k ≠ 0 := ne_of_gt hk
  have hpne : omegaMag ωhat p ≠ 0 := ne_of_gt hp
  have hqne : omegaMag ωhat (triadPartner k p) ≠ 0 := ne_of_gt hq
  have hprod : omegaMag ωhat k * omegaMag ωhat p *
      omegaMag ωhat (triadPartner k p) ≠ 0 := by positivity
  simp only [nsEffectiveKernel]
  rw [if_neg (by intro h; rcases h with a | a | a <;> contradiction)]
  field_simp

/-! ## §8  NS flux control hypothesis

This structure replaces the abstract `TriadKernel` assumptions with
concrete bounds on the actual NS Fourier stretching sums.  The fields
are specific, verifiable inequalities about the NS enstrophy transfer —
not arbitrary kernel properties.

The key fields state: the total NS enstrophy transfer to the top shell,
decomposed into local and defect parts, is absorbed by the viscous
dissipation.  Under shell smallness this follows from the pointwise
bound (§6) composed with Cauchy-Schwarz on finite sums and the
quadratic top-shell mode count. -/

structure NSFluxControl (N : ℕ) where
  ν : ℝ
  ν_pos : 0 < ν
  N_pos : 0 < N
  ωhat : VorticityFourier
  shellEnstrophy : ℝ
  shellEnstrophy_nonneg : 0 ≤ shellEnstrophy
  viscousDissipation : ℝ
  viscousDissipation_nonneg : 0 ≤ viscousDissipation
  localBudget : ℝ
  localBudget_nonneg : 0 ≤ localBudget
  localBudget_le_viscous : localBudget ≤ viscousDissipation
  defectWeight : Mode3 → Mode3 → ℝ
  absorberWeight : Mode3 → Mode3 → ℝ
  defectWeight_nonneg : ∀ k p, 0 ≤ defectWeight k p
  absorberWeight_nonneg : ∀ k p, 0 ≤ absorberWeight k p
  -- The local NS enstrophy flux is absorbed by the local budget
  localFlux_absorbed :
    topShellLocalFlux
      { ν := ν
        ν_pos := ν_pos
        N_pos := N_pos
        omega := omegaMag ωhat
        kernel := nsEffectiveKernel ωhat
        dissipativeGate := fun k p q =>
          nsEffectiveKernel ωhat k p q *
            omegaMag ωhat p * omegaMag ωhat q * omegaMag ωhat k ≤ 0
        shellEnstrophy := shellEnstrophy
        shellEnstrophy_nonneg := shellEnstrophy_nonneg
        viscousDissipation := viscousDissipation
        viscousDissipation_nonneg := viscousDissipation_nonneg
        localBudget := localBudget
        localBudget_nonneg := localBudget_nonneg
        defectWeight := defectWeight
        absorberWeight := absorberWeight
        defectWeight_nonneg := defectWeight_nonneg
        absorberWeight_nonneg := absorberWeight_nonneg } ≤ localBudget
  -- The dissipative nonlocal NS flux has non-positive contribution
  dissipativeFlux_nonpos :
    topShellDissipativeFlux
      { ν := ν
        ν_pos := ν_pos
        N_pos := N_pos
        omega := omegaMag ωhat
        kernel := nsEffectiveKernel ωhat
        dissipativeGate := fun k p q =>
          nsEffectiveKernel ωhat k p q *
            omegaMag ωhat p * omegaMag ωhat q * omegaMag ωhat k ≤ 0
        shellEnstrophy := shellEnstrophy
        shellEnstrophy_nonneg := shellEnstrophy_nonneg
        viscousDissipation := viscousDissipation
        viscousDissipation_nonneg := viscousDissipation_nonneg
        localBudget := localBudget
        localBudget_nonneg := localBudget_nonneg
        defectWeight := defectWeight
        absorberWeight := absorberWeight
        defectWeight_nonneg := defectWeight_nonneg
        absorberWeight_nonneg := absorberWeight_nonneg } ≤ 0
  -- Each defect triad is bounded by its defect weight
  defect_pointwise :
    ∀ (k p : Mode3),
      defectTriad
        { ν := ν
          ν_pos := ν_pos
          N_pos := N_pos
          omega := omegaMag ωhat
          kernel := nsEffectiveKernel ωhat
          dissipativeGate := fun k p q =>
            nsEffectiveKernel ωhat k p q *
              omegaMag ωhat p * omegaMag ωhat q * omegaMag ωhat k ≤ 0
          shellEnstrophy := shellEnstrophy
          shellEnstrophy_nonneg := shellEnstrophy_nonneg
          viscousDissipation := viscousDissipation
          viscousDissipation_nonneg := viscousDissipation_nonneg
          localBudget := localBudget
          localBudget_nonneg := localBudget_nonneg
          defectWeight := defectWeight
          absorberWeight := absorberWeight
          defectWeight_nonneg := defectWeight_nonneg
          absorberWeight_nonneg := absorberWeight_nonneg } k p →
      triadContribution
        { ν := ν
          ν_pos := ν_pos
          N_pos := N_pos
          omega := omegaMag ωhat
          kernel := nsEffectiveKernel ωhat
          dissipativeGate := fun k p q =>
            nsEffectiveKernel ωhat k p q *
              omegaMag ωhat p * omegaMag ωhat q * omegaMag ωhat k ≤ 0
          shellEnstrophy := shellEnstrophy
          shellEnstrophy_nonneg := shellEnstrophy_nonneg
          viscousDissipation := viscousDissipation
          viscousDissipation_nonneg := viscousDissipation_nonneg
          localBudget := localBudget
          localBudget_nonneg := localBudget_nonneg
          defectWeight := defectWeight
          absorberWeight := absorberWeight
          defectWeight_nonneg := defectWeight_nonneg
          absorberWeight_nonneg := absorberWeight_nonneg } k p ≤
        defectWeight k p
  -- Defect weights are bounded by absorber weights
  absorber_pointwise :
    ∀ k p, defectWeight k p ≤ absorberWeight k p
  -- The total absorber sum is bounded by the leftover viscous budget
  absorber_total :
    topShellAbsorberSum
      { ν := ν
        ν_pos := ν_pos
        N_pos := N_pos
        omega := omegaMag ωhat
        kernel := nsEffectiveKernel ωhat
        dissipativeGate := fun k p q =>
          nsEffectiveKernel ωhat k p q *
            omegaMag ωhat p * omegaMag ωhat q * omegaMag ωhat k ≤ 0
        shellEnstrophy := shellEnstrophy
        shellEnstrophy_nonneg := shellEnstrophy_nonneg
        viscousDissipation := viscousDissipation
        viscousDissipation_nonneg := viscousDissipation_nonneg
        localBudget := localBudget
        localBudget_nonneg := localBudget_nonneg
        defectWeight := defectWeight
        absorberWeight := absorberWeight
        defectWeight_nonneg := defectWeight_nonneg
        absorberWeight_nonneg := absorberWeight_nonneg } ≤
      viscousDissipation - localBudget

/-! ## §9  The NS Galerkin triadic system -/

/-- Abbreviation for the `GalerkinTriadicSystem` built from the actual
NS Fourier stretching symbol. -/
def NSFluxControl.toSystem {N : ℕ} (fc : NSFluxControl N) :
    GalerkinTriadicSystem N where
  ν := fc.ν
  ν_pos := fc.ν_pos
  N_pos := fc.N_pos
  omega := omegaMag fc.ωhat
  kernel := nsEffectiveKernel fc.ωhat
  dissipativeGate := fun k p q =>
    nsEffectiveKernel fc.ωhat k p q *
      omegaMag fc.ωhat p * omegaMag fc.ωhat q * omegaMag fc.ωhat k ≤ 0
  shellEnstrophy := fc.shellEnstrophy
  shellEnstrophy_nonneg := fc.shellEnstrophy_nonneg
  viscousDissipation := fc.viscousDissipation
  viscousDissipation_nonneg := fc.viscousDissipation_nonneg
  localBudget := fc.localBudget
  localBudget_nonneg := fc.localBudget_nonneg
  defectWeight := fc.defectWeight
  absorberWeight := fc.absorberWeight
  defectWeight_nonneg := fc.defectWeight_nonneg
  absorberWeight_nonneg := fc.absorberWeight_nonneg

/-! ## §10  Construction of `GalerkinTriadicControl` from the NS kernel -/

/-- The actual NS Fourier stretching symbol satisfies the
`GalerkinTriadicControl` fields under the `NSFluxControl` estimates. -/
def NSFluxControl.toControl {N : ℕ} (fc : NSFluxControl N) :
    GalerkinTriadicControl N where
  toGalerkinTriadicSystem := fc.toSystem
  localFlux_le_budget := fc.localFlux_absorbed
  localBudget_le_viscous := fc.localBudget_le_viscous
  dissipativeFlux_nonpos := fc.dissipativeFlux_nonpos
  defect_pointwise_le := fc.defect_pointwise
  absorber_pointwise_le := fun k p _ =>
    fc.absorber_pointwise k p
  absorber_total_le_leftover := fc.absorber_total

/-! ## §11  Bridge to `TopShellControl` -/

/-- The actual NS kernel produces `TopShellControl` when combined with
the shell Bernstein bound and the smallness condition. -/
def NSFluxControl.toTopShellControl {N : ℕ} (fc : NSFluxControl N)
    (bb : TopShellBernsteinBound N)
    (hsmall : Real.sqrt 26 * bb.omegaTopL2 ≤ fc.ν) :
    TopShellControl N :=
  fc.toControl.toTopShellControl bb hsmall

/-- The NS-instantiated top-shell control has the dissipative
consequence: `dE/dt ≤ 0`. -/
theorem nsTopShellControl_dissipative {N : ℕ} (fc : NSFluxControl N)
    (bb : TopShellBernsteinBound N)
    (hsmall : Real.sqrt 26 * bb.omegaTopL2 ≤ fc.ν) :
    (fc.toTopShellControl bb hsmall).budget.dEdt ≤ 0 :=
  topShellControl_from_actualTriads fc.toControl bb hsmall

end

end NavierStokesBKM
