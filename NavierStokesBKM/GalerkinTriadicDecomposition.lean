/- 
Actual Galerkin Triadic Decomposition for the Top Shell
======================================================

This file upgrades the shell-localized interface to an actual Fourier-triad
decomposition on the Galerkin mode set:

  k = p + q,  with q = k - p.

For the top shell `|k|_∞ = N`, we define the exact finite triadic sum, split it
into:

1. local shell interactions,
2. dissipative nonlocal interactions,
3. defect-paid nonlocal interactions,

and then prove that the shell defect is absorbed by the leftover viscous budget
whenever the corresponding pointwise / summed triadic inequalities hold.

This is still an abstract kernel-level theorem: the remaining mathematical work
is to instantiate the kernel inequalities for the actual 3D Navier-Stokes
Fourier symbol. But the decomposition and the absorption step are now exact
finite sums in Lean, not budget placeholders.
-/

import NavierStokesBKM.ContinuousMaxPrinciple

namespace NavierStokesBKM

open Real Classical

noncomputable section

/-! ## §1  Mode geometry -/

/-- The shell radius `|k|_∞ = max(|k₁|, |k₂|, |k₃|)` as a natural number. -/
def modeRadius (k : Mode3) : ℕ :=
  max k.1.natAbs (max k.2.1.natAbs k.2.2.natAbs)

/-- The top shell at truncation `N`: modes with `|k|_∞ = N`. -/
def isTopShell (N : ℕ) (k : Mode3) : Prop :=
  modeRadius k = N

/-- Explicit top-shell finset inside `[-N, N]^3`. -/
def topShellFinset (N : ℕ) : Finset Mode3 :=
  (modesFinset N).filter (fun k => isTopShell N k)

/-- The triadic partner `q = k - p`. -/
def triadPartner (k p : Mode3) : Mode3 :=
  (k.1 - p.1, (k.2.1 - p.2.1, k.2.2 - p.2.2))

/-- Admissible triadic inputs `p` for a fixed output mode `k`: the partner
`q = k - p` must also lie in the Galerkin truncation. -/
def triadPairs (N : ℕ) (k : Mode3) : Finset Mode3 :=
  (modesFinset N).filter (fun p => triadPartner k p ∈ modesFinset N)

/-- The scalar Fourier interaction coefficient for a vorticity triad. -/
abbrev TriadKernel := Mode3 → Mode3 → Mode3 → ℝ

/-! ## §2  Exact triadic stretching sum -/

/-- Data for an actual top-shell Galerkin triadic system. -/
structure GalerkinTriadicSystem (N : ℕ) where
  ν : ℝ
  ν_pos : 0 < ν
  N_pos : 0 < N
  omega : Mode3 → ℝ
  kernel : TriadKernel
  dissipativeGate : Mode3 → Mode3 → Mode3 → Prop
  shellEnstrophy : ℝ
  shellEnstrophy_nonneg : 0 ≤ shellEnstrophy
  viscousDissipation : ℝ
  viscousDissipation_nonneg : 0 ≤ viscousDissipation
  localBudget : ℝ
  localBudget_nonneg : 0 ≤ localBudget
  defectWeight : Mode3 → Mode3 → ℝ
  absorberWeight : Mode3 → Mode3 → ℝ
  defectWeight_nonneg : ∀ k p, 0 ≤ defectWeight k p
  absorberWeight_nonneg : ∀ k p, 0 ≤ absorberWeight k p

/-- Signed contribution of a single triad `p + q = k` to the top-shell
stretching budget. -/
def triadContribution {N : ℕ} (sys : GalerkinTriadicSystem N)
    (k p : Mode3) : ℝ :=
  sys.kernel k p (triadPartner k p) *
    sys.omega p * sys.omega (triadPartner k p) * sys.omega k

/-- A top-shell triad is local if one of its inputs also lies on the top shell. -/
def localTriad {N : ℕ} (_sys : GalerkinTriadicSystem N) (k p : Mode3) : Prop :=
  isTopShell N p ∨ isTopShell N (triadPartner k p)

/-- Dissipative nonlocal triads are the nonlocal interactions admitted by the
chosen dissipative gate. -/
def dissipativeNonlocalTriad {N : ℕ} (sys : GalerkinTriadicSystem N)
    (k p : Mode3) : Prop :=
  ¬ localTriad sys k p ∧ sys.dissipativeGate k p (triadPartner k p)

/-- Defect triads are the remaining nonlocal interactions. -/
def defectTriad {N : ℕ} (sys : GalerkinTriadicSystem N) (k p : Mode3) : Prop :=
  ¬ localTriad sys k p ∧ ¬ sys.dissipativeGate k p (triadPartner k p)

/-- Local part of a single triad contribution. -/
def localContribution {N : ℕ} (sys : GalerkinTriadicSystem N)
    (k p : Mode3) : ℝ :=
  if localTriad sys k p then triadContribution sys k p else 0

/-- Dissipative nonlocal part of a single triad contribution. -/
def dissipativeContribution {N : ℕ} (sys : GalerkinTriadicSystem N)
    (k p : Mode3) : ℝ :=
  if dissipativeNonlocalTriad sys k p then triadContribution sys k p else 0

/-- Defect-paid nonlocal part of a single triad contribution. -/
def defectContribution {N : ℕ} (sys : GalerkinTriadicSystem N)
    (k p : Mode3) : ℝ :=
  if defectTriad sys k p then triadContribution sys k p else 0

/-- Pointwise defect budget attached to a dangerous triad. -/
def defectWeightContribution {N : ℕ} (sys : GalerkinTriadicSystem N)
    (k p : Mode3) : ℝ :=
  if defectTriad sys k p then sys.defectWeight k p else 0

/-- Pointwise viscous absorber attached to a dangerous triad. -/
def absorberContribution {N : ℕ} (sys : GalerkinTriadicSystem N)
    (k p : Mode3) : ℝ :=
  if defectTriad sys k p then sys.absorberWeight k p else 0

/-- Exact top-shell triadic stretching sum. -/
def topShellTriadicStretching {N : ℕ} (sys : GalerkinTriadicSystem N) : ℝ :=
  Finset.sum (topShellFinset N) (fun k =>
    Finset.sum (triadPairs N k) (fun p => triadContribution sys k p))

/-- Local top-shell flux. -/
def topShellLocalFlux {N : ℕ} (sys : GalerkinTriadicSystem N) : ℝ :=
  Finset.sum (topShellFinset N) (fun k =>
    Finset.sum (triadPairs N k) (fun p => localContribution sys k p))

/-- Dissipative nonlocal top-shell flux. -/
def topShellDissipativeFlux {N : ℕ} (sys : GalerkinTriadicSystem N) : ℝ :=
  Finset.sum (topShellFinset N) (fun k =>
    Finset.sum (triadPairs N k) (fun p => dissipativeContribution sys k p))

/-- Defect-paid nonlocal top-shell flux. -/
def topShellDefectFlux {N : ℕ} (sys : GalerkinTriadicSystem N) : ℝ :=
  Finset.sum (topShellFinset N) (fun k =>
    Finset.sum (triadPairs N k) (fun p => defectContribution sys k p))

/-- Total shell defect attached to dangerous nonlocal triads. -/
def topShellDefectWeightSum {N : ℕ} (sys : GalerkinTriadicSystem N) : ℝ :=
  Finset.sum (topShellFinset N) (fun k =>
    Finset.sum (triadPairs N k) (fun p => defectWeightContribution sys k p))

/-- Total viscous absorber attached to dangerous nonlocal triads. -/
def topShellAbsorberSum {N : ℕ} (sys : GalerkinTriadicSystem N) : ℝ :=
  Finset.sum (topShellFinset N) (fun k =>
    Finset.sum (triadPairs N k) (fun p => absorberContribution sys k p))

/-- The exact top-shell derivative: viscous dissipation plus explicit triadic
stretching. -/
def topShellDerivative {N : ℕ} (sys : GalerkinTriadicSystem N) : ℝ :=
  -sys.viscousDissipation + topShellTriadicStretching sys

/-! ## §3  Exact algebraic split -/

theorem triadContribution_split {N : ℕ} (sys : GalerkinTriadicSystem N)
    (k p : Mode3) :
    triadContribution sys k p =
      localContribution sys k p +
        dissipativeContribution sys k p +
        defectContribution sys k p := by
  by_cases hlocal : localTriad sys k p
  · simp [localContribution, dissipativeContribution, defectContribution,
      dissipativeNonlocalTriad, defectTriad, hlocal]
  · by_cases hgate : sys.dissipativeGate k p (triadPartner k p)
    · simp [localContribution, dissipativeContribution, defectContribution,
        dissipativeNonlocalTriad, defectTriad, hlocal, hgate]
    · simp [localContribution, dissipativeContribution, defectContribution,
        dissipativeNonlocalTriad, defectTriad, hlocal, hgate]

theorem topShellTriadicStretching_split {N : ℕ} (sys : GalerkinTriadicSystem N) :
    topShellTriadicStretching sys =
      topShellLocalFlux sys +
        topShellDissipativeFlux sys +
        topShellDefectFlux sys := by
  unfold topShellTriadicStretching topShellLocalFlux
    topShellDissipativeFlux topShellDefectFlux
  simp_rw [triadContribution_split]
  calc
    Finset.sum (topShellFinset N) (fun k =>
        Finset.sum (triadPairs N k) (fun p =>
          localContribution sys k p + dissipativeContribution sys k p + defectContribution sys k p))
      =
        Finset.sum (topShellFinset N) (fun k =>
          Finset.sum (triadPairs N k) (fun p => localContribution sys k p) +
            Finset.sum (triadPairs N k) (fun p =>
              dissipativeContribution sys k p + defectContribution sys k p)) := by
          apply Finset.sum_congr rfl
          intro k hk
          simpa [add_assoc] using
            (Finset.sum_add_distrib
              (s := triadPairs N k)
              (f := fun p => localContribution sys k p)
              (g := fun p => dissipativeContribution sys k p + defectContribution sys k p))
    _ =
        Finset.sum (topShellFinset N) (fun k =>
          Finset.sum (triadPairs N k) (fun p => localContribution sys k p) +
            (Finset.sum (triadPairs N k) (fun p => dissipativeContribution sys k p) +
              Finset.sum (triadPairs N k) (fun p => defectContribution sys k p))) := by
          apply Finset.sum_congr rfl
          intro k hk
          congr 1
          simpa [add_assoc] using
            (Finset.sum_add_distrib
              (s := triadPairs N k)
              (f := fun p => dissipativeContribution sys k p)
              (g := fun p => defectContribution sys k p))
    _ =
        Finset.sum (topShellFinset N) (fun k =>
          Finset.sum (triadPairs N k) (fun p => localContribution sys k p)) +
          (Finset.sum (topShellFinset N) (fun k =>
            Finset.sum (triadPairs N k) (fun p => dissipativeContribution sys k p)) +
            Finset.sum (topShellFinset N) (fun k =>
              Finset.sum (triadPairs N k) (fun p => defectContribution sys k p))) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ =
        Finset.sum (topShellFinset N) (fun k =>
          Finset.sum (triadPairs N k) (fun p => localContribution sys k p)) +
          Finset.sum (topShellFinset N) (fun k =>
            Finset.sum (triadPairs N k) (fun p => dissipativeContribution sys k p)) +
          Finset.sum (topShellFinset N) (fun k =>
            Finset.sum (triadPairs N k) (fun p => defectContribution sys k p)) := by
          ring

/-! ## §4  Control assumptions on the explicit triadic sums -/

structure GalerkinTriadicControl (N : ℕ) extends GalerkinTriadicSystem N where
  localFlux_le_budget :
    topShellLocalFlux toGalerkinTriadicSystem ≤ localBudget
  localBudget_le_viscous :
    localBudget ≤ viscousDissipation
  dissipativeFlux_nonpos :
    topShellDissipativeFlux toGalerkinTriadicSystem ≤ 0
  defect_pointwise_le :
    ∀ k p, defectTriad toGalerkinTriadicSystem k p →
      triadContribution toGalerkinTriadicSystem k p ≤ defectWeight k p
  absorber_pointwise_le :
    ∀ k p, defectTriad toGalerkinTriadicSystem k p →
      defectWeight k p ≤ absorberWeight k p
  absorber_total_le_leftover :
    topShellAbsorberSum toGalerkinTriadicSystem ≤
      viscousDissipation - localBudget

theorem defectWeightSum_nonneg {N : ℕ} (sys : GalerkinTriadicSystem N) :
    0 ≤ topShellDefectWeightSum sys := by
  unfold topShellDefectWeightSum
  refine Finset.sum_nonneg ?_
  intro k hk
  refine Finset.sum_nonneg ?_
  intro p hp
  by_cases hdef : defectTriad sys k p
  · simp [defectWeightContribution, hdef, sys.defectWeight_nonneg]
  · simp [defectWeightContribution, hdef]

theorem absorberSum_nonneg {N : ℕ} (sys : GalerkinTriadicSystem N) :
    0 ≤ topShellAbsorberSum sys := by
  unfold topShellAbsorberSum
  refine Finset.sum_nonneg ?_
  intro k hk
  refine Finset.sum_nonneg ?_
  intro p hp
  by_cases hdef : defectTriad sys k p
  · simp [absorberContribution, hdef, sys.absorberWeight_nonneg]
  · simp [absorberContribution, hdef]

theorem defectFlux_le_defectWeightSum {N : ℕ} (ctl : GalerkinTriadicControl N) :
    topShellDefectFlux ctl.toGalerkinTriadicSystem ≤
      topShellDefectWeightSum ctl.toGalerkinTriadicSystem := by
  unfold topShellDefectFlux topShellDefectWeightSum
  refine Finset.sum_le_sum ?_
  intro k hk
  refine Finset.sum_le_sum ?_
  intro p hp
  by_cases hdef : defectTriad ctl.toGalerkinTriadicSystem k p
  · simp [defectContribution, defectWeightContribution, hdef]
    exact ctl.defect_pointwise_le k p hdef
  · simp [defectContribution, defectWeightContribution, hdef]

theorem defectWeightSum_le_absorberSum {N : ℕ} (ctl : GalerkinTriadicControl N) :
    topShellDefectWeightSum ctl.toGalerkinTriadicSystem ≤
      topShellAbsorberSum ctl.toGalerkinTriadicSystem := by
  unfold topShellDefectWeightSum topShellAbsorberSum
  refine Finset.sum_le_sum ?_
  intro k hk
  refine Finset.sum_le_sum ?_
  intro p hp
  by_cases hdef : defectTriad ctl.toGalerkinTriadicSystem k p
  · simp [defectWeightContribution, absorberContribution, hdef]
    exact ctl.absorber_pointwise_le k p hdef
  · simp [defectWeightContribution, absorberContribution, hdef]

/-- The explicit shell defect is absorbed by the leftover viscous budget. -/
theorem shellDefect_absorbed_by_leftoverViscous {N : ℕ}
    (ctl : GalerkinTriadicControl N) :
    topShellDefectWeightSum ctl.toGalerkinTriadicSystem ≤
      ctl.viscousDissipation - topShellLocalFlux ctl.toGalerkinTriadicSystem := by
  have h1 :
      topShellDefectWeightSum ctl.toGalerkinTriadicSystem ≤
        topShellAbsorberSum ctl.toGalerkinTriadicSystem :=
    defectWeightSum_le_absorberSum ctl
  have h2 :
      topShellAbsorberSum ctl.toGalerkinTriadicSystem ≤
        ctl.viscousDissipation - ctl.localBudget :=
    ctl.absorber_total_le_leftover
  have h3 :
      ctl.viscousDissipation - ctl.localBudget ≤
        ctl.viscousDissipation - topShellLocalFlux ctl.toGalerkinTriadicSystem := by
    linarith [ctl.localFlux_le_budget]
  exact le_trans h1 (le_trans h2 h3)

/-! ## §5  Producing the shell budget and `TopShellControl` -/

/-- The explicit triadic system produces the shell-enstrophy budget used by the
top-shell route. -/
def GalerkinTriadicControl.toShellEnstrophyBudget {N : ℕ}
    (ctl : GalerkinTriadicControl N) : ShellEnstrophyBudget N where
  localFlux := topShellLocalFlux ctl.toGalerkinTriadicSystem
  dissipativeNonlocalFlux := topShellDissipativeFlux ctl.toGalerkinTriadicSystem
  defectPaidNonlocalFlux := topShellDefectFlux ctl.toGalerkinTriadicSystem
  shellDefect := topShellDefectWeightSum ctl.toGalerkinTriadicSystem
  shellDefect_nonneg := defectWeightSum_nonneg ctl.toGalerkinTriadicSystem
  dissipative_nonpos := ctl.dissipativeFlux_nonpos
  defect_paid := defectFlux_le_defectWeightSum ctl
  shellEnstrophy := ctl.shellEnstrophy
  shellEnstrophy_nonneg := ctl.shellEnstrophy_nonneg
  viscousDissipation := ctl.viscousDissipation
  viscousDissipation_nonneg := ctl.viscousDissipation_nonneg
  dEdt := topShellDerivative ctl.toGalerkinTriadicSystem
  split := by
    unfold topShellDerivative
    rw [topShellTriadicStretching_split]
    ring
  local_absorbed_by_viscous := le_trans ctl.localFlux_le_budget ctl.localBudget_le_viscous

/-- The actual Galerkin triadic decomposition produces `TopShellControl`. -/
def GalerkinTriadicControl.toTopShellControl {N : ℕ}
    (ctl : GalerkinTriadicControl N) (bb : TopShellBernsteinBound N)
    (hsmall : Real.sqrt 26 * bb.omegaTopL2 ≤ ctl.ν) :
    TopShellControl N where
  ν := ctl.ν
  ν_pos := ctl.ν_pos
  N_pos := ctl.N_pos
  bernstein := bb
  budget := ctl.toShellEnstrophyBudget
  shell_smallness := hsmall
  defect_absorbed := shellDefect_absorbed_by_leftoverViscous ctl

/-- The constructed control object has the desired dissipative consequence. -/
theorem topShellControl_from_actualTriads {N : ℕ}
    (ctl : GalerkinTriadicControl N) (bb : TopShellBernsteinBound N)
    (hsmall : Real.sqrt 26 * bb.omegaTopL2 ≤ ctl.ν) :
    let topCtl := ctl.toTopShellControl bb hsmall
    topCtl.budget.dEdt ≤ 0 := by
  intro topCtl
  exact topShell_enstrophy_nonincreasing topCtl

end

end NavierStokesBKM
