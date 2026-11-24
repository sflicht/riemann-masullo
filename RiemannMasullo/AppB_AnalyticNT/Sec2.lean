module

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import RiemannMasullo.ForMathlib.Analysis.Calculus.IteratedDeriv.ExponentialWeight
import RiemannMasullo.ForMathlib.Analysis.Complex.PhragmenLindelof
import RiemannMasullo.ForMathlib.Analysis.MellinTransform
import RiemannMasullo.ForMathlib.Analysis.Complex.VerticalCauchyIntegral

/-!
# Mellin transforms and asymptotic Cauchy integrals

Masullo, §B.2, pp. 591–604. A Schwartz–Bruhat function on the positive reals is
represented by its real-line Schwartz map in the coordinate `x = log t`.
Other functions on the positive reals are represented by functions on ℝ whose
values outside the positive reals are immaterial.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped Asymptotics ContDiff ENNReal FourierTransform NNReal SchwartzMap Topology

namespace RiemannMasullo

local notation "verticalPoint" =>
  (fun (σ y : ℝ) ↦ (σ : ℂ) + (y : ℂ) * Complex.I)
local notation "verticalTrace" =>
  (fun (Φ : ℂ → ℂ) (σ : ℝ) (y : ℝ) ↦ Φ (verticalPoint σ y))
local notation "atAbsInfty" => (comap abs atTop)
local notation "openStrip" => (fun a b : ℝ ↦ Complex.re ⁻¹' Ioo a b)
local notation "closedStrip" => (fun a b : ℝ ↦ Complex.re ⁻¹' Icc a b)
set_option quotPrecheck false in
local notation "stripWithTop" =>
  (fun (a : ℝ) (b : WithTop ℝ) ↦ {s : ℂ | a < s.re ∧ (s.re : WithTop ℝ) < b})
set_option quotPrecheck false in
local notation "heightBound" =>
  (fun (Φ : ℂ → ℂ) (J : Set ℝ) (N : ℕ) (C : ℝ) ↦
    ∀ σ ∈ J, ∀ y : ℝ, y ≠ 0 → ‖Φ (verticalPoint σ y)‖ ≤ C / |y| ^ N)
set_option quotPrecheck false in
local notation "eventualHeightBound" =>
  (fun (Φ : ℂ → ℂ) (J : Set ℝ) (N : ℕ) ↦
    ∃ C > (0 : ℝ), ∀ᶠ y : ℝ in atAbsInfty, ∀ σ ∈ J,
      ‖Φ (verticalPoint σ y)‖ ≤ C / |y| ^ N)
set_option quotPrecheck false in
local notation "lpTail" =>
  (fun (p : ℝ) (N : ℕ) ↦ ∫ y : ℝ in {y | 1 / 2 ≤ |y|}, 1 / |y| ^ (p * (N : ℝ)))
local notation "logWeight" =>
  (fun (σ x : ℝ) ↦ (Real.exp (σ * x) : ℂ))
local notation "fromLog" => (fun (f : ℝ → ℂ) (t : ℝ) ↦ f (Real.log t))

/-- Paper: §B.2.1, p. 592. The half-plane Hardy condition is holomorphy
and a finite uniform bound on the vertical Lᵖ norms. -/
def MemLeftHardy (Φ : ℂ → ℂ) (b p : ℝ) : Prop :=
  0 < p ∧ DifferentiableOn ℂ Φ (Complex.re ⁻¹' Iio b) ∧
    ∃ C : ℝ≥0, ∀ σ < b, eLpNorm (verticalTrace Φ σ) (ENNReal.ofReal p) volume ≤ C

/-- Paper: §B.2.1, p. 592. At exponent one, the half-plane Hardy bound is
equivalent to a common finite bound on the integrals of the vertical absolute values.
Deviation: Sanity check for the extended-norm formulation. -/
theorem memLeftHardy_one_iff (Φ : ℂ → ℂ) (b : ℝ) :
    MemLeftHardy Φ b 1 ↔ DifferentiableOn ℂ Φ (Complex.re ⁻¹' Iio b) ∧
      ∃ C : ℝ, ∀ σ < b, Complex.VerticalIntegrable Φ σ ∧
        (∫ y : ℝ, ‖Φ (verticalPoint σ y)‖) ≤ C := by
  simp only [MemLeftHardy, zero_lt_one, true_and, ENNReal.ofReal_one,
    Complex.VerticalIntegrable]
  constructor
  · rintro ⟨hΦ, C, hC⟩
    refine ⟨hΦ, C, fun σ hσ ↦ ?_⟩
    have hLp := hC σ hσ
    have hInt : Integrable (verticalTrace Φ σ) :=
      memLp_one_iff_integrable.mp (memLp_iff.mpr (hLp.trans_lt ENNReal.coe_lt_top))
    refine ⟨hInt, ?_⟩
    rw [integral_norm_eq_lintegral_eNorm hInt.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_eNorm hInt.aestronglyMeasurable]
    exact ENNReal.toReal_mono ENNReal.coe_ne_top hLp
  · rintro ⟨hΦ, C, hC⟩
    refine ⟨hΦ, C.toNNReal, fun σ hσ ↦ ?_⟩
    obtain ⟨hInt, hBound⟩ := hC σ hσ
    rw [eLpNorm_one_eq_lintegral_eNorm hInt.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_eNorm hInt, ENNReal.ofNNReal_toNNReal]
    exact ENNReal.ofReal_le_ofReal hBound

-- TODO(paper-gap): Footnotes 5 and 6 ask how the cited Hardy-space results
-- apply on the left half-plane. Footnote 7 asks how far the decay is uniform.

/-- Paper: Definition B.2.1.1(1), p. 593. Every derivative of the logarithmic
profile decays faster than every exponential as the log coordinate tends to positive infinity.
Deviation: Uses logarithmic differentiation as allowed in Remark B.2.1.2. -/
def ForwardSemiExponentialDecay (f : 𝓢(ℝ, ℂ)) : Prop :=
  ∀ (j : ℕ) (A : ℝ), 0 < A →
    (iteratedDeriv j (f : ℝ → ℂ)) =O[atTop] fun x ↦ Real.exp (-A * x)

/-- Paper: Definition B.2.1.1(1), p. 593. Every derivative of the logarithmic
profile decays faster than every exponential as the log coordinate tends to negative infinity.
Deviation: Uses logarithmic differentiation as allowed in Remark B.2.1.2. -/
def BackwardSemiExponentialDecay (f : 𝓢(ℝ, ℂ)) : Prop :=
  ∀ (j : ℕ) (A : ℝ), 0 < A →
    (iteratedDeriv j (f : ℝ → ℂ)) =O[atBot] fun x ↦ Real.exp (A * x)

/-- Paper: Definition B.2.1.1(2), p. 593. Exponential decay requires
the two semi-exponential decay conditions on the logarithmic profile. -/
def ExponentialDecay (f : 𝓢(ℝ, ℂ)) : Prop :=
  ForwardSemiExponentialDecay f ∧ BackwardSemiExponentialDecay f

/-- Paper: Definition B.2.1.1, p. 593. The ordinary real Gaussian
satisfies all three decay conditions as a logarithmic profile.
Deviation: Sanity check for the three definitions. -/
theorem exists_gaussian_logProfile_exponentialDecay :
    ∃ f : 𝓢(ℝ, ℂ), (∀ x : ℝ, f x = Real.exp (-(x ^ 2))) ∧
      ForwardSemiExponentialDecay f ∧ BackwardSemiExponentialDecay f ∧
      ExponentialDecay f := by
  let G : ℝ → ℂ := fun x ↦ (Real.exp (-(x ^ 2)) : ℂ)
  -- Differentiating p(x) exp(-x²) replaces p by p' - 2Xp.
  have hderiv (j : ℕ) : ∃ p : Polynomial ℝ,
      iteratedDeriv j G = fun x ↦ (↑(p.eval x * Real.exp (-(x ^ 2))) : ℂ) := by
    induction j with
    | zero => exact ⟨1, by simp [G]⟩
    | succ j ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p.derivative - Polynomial.C 2 * Polynomial.X * p, ?_⟩
      rw [iteratedDeriv_succ, hp]
      funext x
      have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp (-(y ^ 2)))
          (Real.exp (-(x ^ 2)) * -(2 * x)) x := by
        simpa using! (((hasDerivAt_id x).pow 2).neg).exp
      apply (((p.hasDerivAt x).mul hexp).ofReal_comp.deriv).trans
      congr 1
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
  -- A Gaussian absorbs polynomial weights and any fixed exponential weight.
  have hbound (k j : ℕ) (A : ℝ) : ∃ C : ℝ, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedDeriv j G x‖ ≤ C * Real.exp (-A * |x|) := by
    obtain ⟨p, hp⟩ := hderiv j
    let M : ℝ := ∑ i ∈ p.support, ‖p.coeff i‖ * ((k + i).factorial : ℝ)
    have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ by positivity
    refine ⟨M * Real.exp ((A + 1) ^ 2 / 4), fun x ↦ ?_⟩
    have hpoly : ‖x‖ ^ k * ‖p.eval x‖ ≤ M * Real.exp |x| := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, norm_pow, ← mul_left_comm, ← pow_add, Real.norm_eq_abs x, mul_assoc]
      have hfact : (0 : ℝ) < (k + i).factorial := by positivity
      have hpow := (div_le_iff₀ hfact).mp
        (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) (k + i))
      exact mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using hpow) (norm_nonneg _)
    have hsquare : |x| + -(x ^ 2) ≤ (A + 1) ^ 2 / 4 + -A * |x| := by
      rw [← sq_abs x]
      nlinarith [sq_nonneg (|x| - (A + 1) / 2)]
    rw [hp, Complex.norm_real, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc]
    calc
      _ ≤ (M * Real.exp |x|) * Real.exp (-(x ^ 2)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = M * Real.exp (|x| + -(x ^ 2)) := by rw [mul_assoc, ← Real.exp_add]
      _ ≤ M * Real.exp ((A + 1) ^ 2 / 4 + -A * |x|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsquare) hM
      _ = _ := by rw [Real.exp_add, mul_assoc]
  have hsmooth : ContDiff ℝ ∞ G :=
    Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ ∞ fun x : ℝ ↦ Real.exp (-(x ^ 2)))
  let f : 𝓢(ℝ, ℂ) := ⟨G, hsmooth, fun k j ↦ by
    obtain ⟨C, hC⟩ := hbound k j 0
    exact ⟨C, fun x ↦ by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, neg_zero, zero_mul,
        Real.exp_zero, mul_one] using hC x⟩⟩
  have hforward : ForwardSemiExponentialDecay f := by
    intro j A _
    change iteratedDeriv j G =O[atTop] _
    obtain ⟨C, hC⟩ := hbound 0 j A
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simpa only [pow_zero, one_mul, abs_of_nonneg hx, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using hC x
  have hbackward : BackwardSemiExponentialDecay f := by
    intro j A _
    change iteratedDeriv j G =O[atBot] _
    obtain ⟨C, hC⟩ := hbound 0 j A
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    simpa only [pow_zero, one_mul, abs_of_nonpos hx, neg_mul_neg, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using hC x
  exact ⟨f, fun _ ↦ rfl, hforward, hbackward, ⟨hforward, hbackward⟩⟩

/-- An extra exponential factor absorbs any prescribed polynomial weight at positive infinity. -/
private theorem forward_weighted_deriv_bound {f : 𝓢(ℝ, ℂ)} (hf : ForwardSemiExponentialDecay f)
    {A : ℝ} (hA : 0 ≤ A) (k j : ℕ) : ∃ B : ℝ, ∀ x : ℝ,
      |x| ^ k * Real.exp (A * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖ ≤ B := by
  obtain ⟨C, hC, hdec⟩ := (hf j (A + 1) (by linarith)).exists_pos
  obtain ⟨R, hR⟩ := eventually_atTop.mp hdec.bound
  let G (x : ℝ) := |x| ^ k * Real.exp (A * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖
  have hG : Continuous G := ((continuous_abs.pow _).mul (by fun_prop)).mul
    (f.smooth ⊤ |>.continuous_iteratedDeriv j (by simp)).norm
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).bddAbove_image hG.continuousOn
  let S := SchwartzMap.seminorm ℂ k j f
  refine ⟨max (max D S) (C * k.factorial), fun x ↦ ?_⟩
  by_cases hx : x ≤ 0
  · have e : Real.exp (A * x) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hA hx)
    calc |x| ^ k * Real.exp (A * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖
      _ ≤ |x| ^ k * ‖iteratedDeriv j (f : ℝ → ℂ) x‖ := by
        grw [e]; rw [mul_one]
      _ ≤ S := f.le_seminorm' ℂ k j x
      _ ≤ _ := (le_max_right _ _).trans (le_max_left _ _)
  by_cases hr : x ≤ R
  · exact (hD (mem_image_of_mem _ ⟨le_of_not_ge hx, hr⟩)).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hx0 : 0 ≤ x := le_of_not_ge hx
  have hd := hR x (le_of_not_ge hr)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hd
  have hpow := (div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mp (Real.pow_div_factorial_le_exp x hx0 k)
  rw [abs_of_nonneg hx0]
  calc x ^ k * Real.exp (A * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖
    _ ≤ (Real.exp x * k.factorial) * Real.exp (A * x) * (C * Real.exp (-(A + 1) * x)) := by gcongr
    _ = C * k.factorial := by
      calc _ = (C * k.factorial) * (Real.exp x * Real.exp (A * x) * Real.exp (-(A + 1) * x)) := by ring
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, show x + A * x + -(A + 1) * x = 0 by ring]; simp
    _ ≤ _ := le_max_right _ _

/-- Paper: Remark B.2.1.2, p. 593. Forward decay is equivalent to the
Schwartz condition on every nonnegatively weighted logarithmic profile. -/
theorem forwardSemiExponentialDecay_iff_weighted_schwartz (f : 𝓢(ℝ, ℂ)) :
    ForwardSemiExponentialDecay f ↔ ∀ A : ℝ, 0 ≤ A →
      ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = logWeight A x * f x := by
  constructor
  · intro hf A hA
    let G : ℝ → ℂ := (fun y ↦ Real.exp (A * y)) • ⇑f
    have hG : ContDiff ℝ ∞ G := ContDiff.smul (by fun_prop) (f.smooth _)
    have bound (k n : ℕ) : ∃ B, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n G x‖ ≤ B := by
      choose C hC using forward_weighted_deriv_bound hf hA k
      refine ⟨∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * |A| ^ i) * C (n - i), fun x ↦ ?_⟩
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      apply (norm_iteratedDeriv_exp_smul_le A x k n f (f.smooth n)).trans
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hC (n - i) x) (by positivity)
    refine ⟨⟨G, hG, bound⟩, fun x ↦ ?_⟩
    change Real.exp (A * x) • f x = _
    rw [Complex.real_smul]
  · intro hf j A hA
    obtain ⟨g, hg⟩ := hf A hA.le
    have hfg : (f : ℝ → ℂ) = (fun y ↦ Real.exp (-A * y)) • ⇑g := by
      funext x
      change f x = Real.exp (-A * x) • g x
      simp only [Complex.real_smul, hg, ← mul_assoc, ← Complex.ofReal_mul,
        ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]
    let B := ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℝ) * |-A| ^ i) * SchwartzMap.seminorm ℂ 0 (j - i) g
    apply Asymptotics.IsBigO.of_bound B
    filter_upwards with x
    rw [hfg, Real.norm_of_nonneg (Real.exp_pos _).le]
    have upper := norm_iteratedDeriv_exp_smul_le (-A) x 0 j g (g.smooth j)
    simp only [pow_zero, one_mul] at upper
    apply upper.trans
    rw [show B * Real.exp (-A * x) = ∑ i ∈ Finset.range (j + 1),
      ((j.choose i : ℝ) * |-A| ^ i) * (Real.exp (-A * x) * SchwartzMap.seminorm ℂ 0 (j - i) g) from by
        unfold B
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring]
    apply Finset.sum_le_sum
    intro i _
    gcongr
    simpa using g.le_seminorm' ℂ 0 (j - i) x

-- TODO(paper-gap): The single rate O(e⁻ˣ) in the last assertion of Remark B.2.1.2
-- does not imply the family of bounds required by Definition B.2.1.1(1).
-- TODO(paper-gap): Remark B.2.1.3 quantifies over every exponent and over all t.
-- The exponent zero forces boundedness and the bound at t = 1 forces vanishing there.
-- TODO(paper-gap): Lemma B.2.1.4(1) claims that the zero extension is Schwartz.
-- A smooth function supported away from zero and equal to 1/t for large t
-- has backward semi-exponential decay but fails the ordinary Schwartz bounds.

/-- Paper: Lemma B.2.1.4(1), p. 593. Backward semi-exponential decay makes the
zero extension smooth across the origin.
Deviation: The ordinary Schwartz assertion is false without forward decay. -/
theorem contDiff_zeroExtension_of_backwardSemiExponentialDecay (f : 𝓢(ℝ, ℂ))
    (hf : BackwardSemiExponentialDecay f) :
    ContDiff ℝ ∞ ((Ioi (0 : ℝ)).indicator (fromLog f)) := by
  let G (a : ℝ) (j : ℕ) : ℝ → ℂ :=
    (Ioi (0 : ℝ)).indicator fun t ↦ t ^ a • iteratedDeriv j (f : ℝ → ℂ) (Real.log t)
  have G_eq (a : ℝ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
      G a j t = t ^ a • iteratedDeriv j (f : ℝ → ℂ) (Real.log t) :=
    indicator_of_mem ht _
  have G_zero (a : ℝ) (j : ℕ) {t : ℝ} (ht : t ≤ 0) : G a j t = 0 :=
    indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht.not_gt) _
  -- The extra two powers of t give a zero derivative at the origin.
  have hdecay (a : ℝ) (j : ℕ) (ha : a ≤ 0) : G a j =O[𝓝 0] (fun t : ℝ ↦ t ^ 2) := by
    rw [← nhdsLE_sup_nhdsGT, Asymptotics.isBigO_sup]
    constructor
    · apply (Asymptotics.isBigO_zero _ _).congr' _ EventuallyEq.rfl
      filter_upwards [self_mem_nhdsWithin (s := Iic (0 : ℝ))] with t ht
      exact (G_zero a j ht).symm
    · have hlog := isBigO_comp_log_rpow_of_isBigO_exp (hf j (2 - a) (by linarith))
        Real.tendsto_log_nhdsGT_zero self_mem_nhdsWithin
      apply ((Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ a) _).smul hlog).congr'
      · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
        exact (G_eq a j ht).symm
      · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
        rw [smul_eq_mul, ← Real.rpow_add ht, show a + (2 - a) = 2 by ring, Real.rpow_two]
  have hderiv (a : ℝ) (j : ℕ) (ha : a ≤ 0) (t : ℝ) :
      HasDerivAt (G a j) (G (a - 1) (j + 1) t + a • G (a - 1) j t) t := by
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · rw [G_zero _ _ ht.le, G_zero _ _ ht.le, smul_zero, add_zero]
      exact (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq
        ((eventually_lt_nhds ht).mono fun u hu ↦ G_zero a j hu.le)
    · simp only [G_zero _ _ le_rfl, smul_zero, add_zero, hasDerivAt_iff_isLittleO,
        sub_zero]
      exact (hdecay a j ha).trans_isLittleO (by
        simpa only [pow_one] using
          (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (m := 1) (n := 2) (by decide)))
    · have hlog : HasDerivAt (fromLog (iteratedDeriv j (f : ℝ → ℂ)))
          (t⁻¹ • iteratedDeriv (j + 1) (f : ℝ → ℂ) (Real.log t)) t := by
        rw [iteratedDeriv_succ]
        exact ((f.smooth ⊤).differentiable_iteratedDeriv j
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)
          (Real.log t)).hasDerivAt.scomp t (Real.hasDerivAt_log ht.ne')
      have h := (Real.hasDerivAt_rpow_const (p := a) (Or.inl ht.ne')).smul hlog
      rw [G_eq _ _ ht, G_eq _ _ ht, smul_smul]
      rw [smul_smul, mul_comm (t ^ a) t⁻¹, ← div_eq_inv_mul, ← Real.rpow_sub_one ht.ne'] at h
      exact h.congr_of_eventuallyEq ((eventually_gt_nhds ht).mono fun u hu ↦ G_eq a j hu)
  have hsmooth (n : ℕ) (a : ℝ) (j : ℕ) (ha : a ≤ 0) : ContDiff ℝ n (G a j) := by
    induction n generalizing a j with
    | zero =>
      exact contDiff_zero.mpr (Differentiable.continuous fun t ↦ (hderiv a j ha t).differentiableAt)
    | succ n ih =>
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun t ↦ (hderiv a j ha t).differentiableAt, by simp, ?_⟩
      rw [show deriv (G a j) = G (a - 1) (j + 1) + a • G (a - 1) j from
        funext fun t ↦ (hderiv a j ha t).deriv]
      have ha' : a - 1 ≤ 0 := by linarith
      exact (ih (a - 1) (j + 1) ha').add ((ih (a - 1) j ha').const_smul a)
  rw [contDiff_infty]
  intro n
  simpa only [G, Real.rpow_zero, one_smul, iteratedDeriv_zero] using hsmooth n 0 0 le_rfl

/-- Paper: Lemma B.2.1.4(2), p. 593. Inversion on the positive reals is
the continuous linear involution given by reflection of the logarithmic profile. -/
theorem exists_schwartzLogReflection :
    ∃ R : 𝓢(ℝ, ℂ) ≃L[ℂ] 𝓢(ℝ, ℂ), (∀ (f : 𝓢(ℝ, ℂ)) (x : ℝ), R f x = f (-x)) ∧
      Involutive R := by
  let T := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (ContinuousLinearEquiv.neg ℝ (M := ℝ))
  have hT (f : 𝓢(ℝ, ℂ)) (x : ℝ) : T f x = f (-x) := rfl
  have hinv (f : 𝓢(ℝ, ℂ)) : T (T f) = f := by ext x; simp only [hT, neg_neg]
  exact ⟨ContinuousLinearEquiv.equivOfInverse T T hinv hinv, hT, hinv⟩

/-- Paper: Lemma B.2.1.4(2), p. 593. Reflection interchanges forward
and backward semi-exponential decay. -/
theorem backwardSemiExponentialDecay_iff_forward_reflected
    (f g : 𝓢(ℝ, ℂ)) (hg : ∀ x : ℝ, g x = f (-x)) :
    BackwardSemiExponentialDecay g ↔ ForwardSemiExponentialDecay f := by
  have normEq (n : ℕ) (x : ℝ) : ‖iteratedDeriv n (g : ℝ → ℂ) x‖ = ‖iteratedDeriv n (f : ℝ → ℂ) (-x)‖ := by
    rw [show (g : ℝ → ℂ) = fun y ↦ f (-y) from funext hg, iteratedDeriv_comp_neg]
    simp [norm_pow]
  constructor
  · intro h j A hA
    obtain ⟨C, hC⟩ := (h j A hA).bound
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [tendsto_neg_atTop_atBot.eventually hC] with x hx
    simpa only [normEq, neg_neg, mul_neg, neg_mul] using hx
  · intro h j A hA
    obtain ⟨C, hC⟩ := (h j A hA).bound
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [tendsto_neg_atBot_atTop.eventually hC] with x hx
    rw [normEq]
    simpa only [neg_mul_neg] using hx

/-- Paper: Lemma B.2.1.4(2), p. 593. Exponential decay is invariant under
reflection of the logarithmic profile. -/
theorem exponentialDecay_iff_reflected (f g : 𝓢(ℝ, ℂ)) (hg : ∀ x : ℝ, g x = f (-x)) :
    ExponentialDecay g ↔ ExponentialDecay f := by
  have hgf (x : ℝ) : f x = g (-x) := by simp [hg]
  have h₁ := backwardSemiExponentialDecay_iff_forward_reflected f g hg
  have h₂ := backwardSemiExponentialDecay_iff_forward_reflected g f hgf
  exact ⟨fun h ↦ ⟨h₁.mp h.2, h₂.mpr h.1⟩, fun h ↦ ⟨h₂.mp h.2, h₁.mpr h.1⟩⟩

/-- Signed Stirling numbers of the first kind, so that
`t^{-n} \sum_j s(n,j) f^{(j)}(\log t)` is the `n`-th derivative of `f \circ \log`. -/
private def sStir (n k : ℕ) : ℤ := (-1) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

private lemma sStir_succ_succ (n k : ℕ) :
    sStir (n + 1) (k + 1) = sStir n k - (n : ℤ) * sStir n (k + 1) := by
  dsimp only [sStir]
  have hsub : (n + 1) - (k + 1) = n - k := Nat.succ_sub_succ n k
  rw [hsub, Nat.stirlingFirst_succ_succ]
  push_cast
  by_cases hkn : n ≤ k
  · have hS2 : Nat.stirlingFirst n (k + 1) = 0 :=
      Nat.stirlingFirst_eq_zero_of_lt (by omega)
    have hnk : n - k = 0 := Nat.sub_eq_zero_of_le hkn
    simp [hS2, hnk]
  · have hsub' : n - (k + 1) + 1 = n - k := by omega
    have hsign : (-1 : ℤ) ^ (n - k) = - (-1 : ℤ) ^ (n - (k + 1)) := by
      rw [← hsub', pow_succ]
      ring
    rw [hsign]
    ring

private lemma sStir_rec (n k : ℕ) :
    sStir (n + 1) k =
      (if k = 0 then 0 else sStir n (k - 1)) - (n : ℤ) * sStir n k := by
  cases k with
  | zero =>
    have hL : sStir (n + 1) 0 = 0 := by
      dsimp only [sStir]
      rw [Nat.sub_zero, Nat.stirlingFirst_succ_zero, Nat.cast_zero, mul_zero]
    have hR : (n : ℤ) * sStir n 0 = 0 := by
      dsimp only [sStir, Nat.sub_zero]
      cases n with
      | zero => simp [Nat.stirlingFirst_zero]
      | succ n => rw [Nat.stirlingFirst_succ_zero, Nat.cast_zero, mul_zero, mul_zero]
    simp [hL, hR]
  | succ k =>
    simpa using sStir_succ_succ n k

private lemma sStir_sum_identity (n : ℕ) (d : ℕ → ℂ) :
    (∑ j ∈ Finset.range (n + 1),
        (((sStir n j : ℂ) * (-(n : ℂ))) * d j + (sStir n j : ℂ) * d (j + 1))) =
      ∑ k ∈ Finset.range (n + 2), (sStir (n + 1) k : ℂ) * d k := by
  have hzero : sStir n (n + 1) = 0 := by
    dsimp only [sStir]
    rw [Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero, mul_zero]
  have hfirst :
      (∑ j ∈ Finset.range (n + 1), ((sStir n j : ℂ) * (-(n : ℂ))) * d j) =
        ∑ k ∈ Finset.range (n + 2), ((sStir n k : ℂ) * (-(n : ℂ))) * d k := by
    conv_rhs => rw [Finset.sum_range_succ]
    simp [hzero]
  have hsecond :
      (∑ j ∈ Finset.range (n + 1), (sStir n j : ℂ) * d (j + 1)) =
        ∑ k ∈ Finset.range (n + 2),
          (if k = 0 then (0 : ℂ) else (sStir n (k - 1) : ℂ)) * d k := by
    have hIcc :
        (∑ j ∈ Finset.range (n + 1), (sStir n j : ℂ) * d (j + 1)) =
          ∑ k ∈ Finset.Icc 1 (n + 1), (sStir n (k - 1) : ℂ) * d k := by
      refine Finset.sum_nbij' (fun j => j + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
        omega
      · intro k hk
        simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢
        omega
      · intro j _hj; simp
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        exact Nat.sub_add_cancel hk.1
      · intro j _hj; simp
    have hsub : Finset.Icc 1 (n + 1) ⊆ Finset.range (n + 2) := by
      intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    rw [hIcc]
    have hIf :
        (∑ k ∈ Finset.Icc 1 (n + 1), (sStir n (k - 1) : ℂ) * d k) =
          ∑ k ∈ Finset.Icc 1 (n + 1),
            (if k = 0 then (0 : ℂ) else (sStir n (k - 1) : ℂ)) * d k := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hk0 : k ≠ 0 := by omega
      simp [hk0]
    rw [hIf]
    refine Finset.sum_subset hsub ?_
    intro k hk hk'
    simp only [Finset.mem_range, Finset.mem_Icc] at hk hk'
    have hk0 : k = 0 := by omega
    simp [hk0]
  rw [Finset.sum_add_distrib, hfirst, hsecond, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  have hrec : (sStir (n + 1) k : ℂ) =
      (if k = 0 then (0 : ℂ) else (sStir n (k - 1) : ℂ)) - (n : ℂ) * (sStir n k : ℂ) := by
    rw [sStir_rec]
    push_cast
    split_ifs <;> simp
  rw [hrec]
  ring

/-- The `n`-th derivative, on `(0, \infty)`, of `t \mapsto f(\log t)`. -/
private def prof (f : ℝ → ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (sStir n j : ℂ) * ((s ^ (-(n : ℤ)) : ℝ) : ℂ) * iteratedDeriv j f (Real.log s)

private lemma norm_sStir (n k : ℕ) : ‖(sStir n k : ℂ)‖ = (Nat.stirlingFirst n k : ℝ) := by
  have hnat : (sStir n k).natAbs = Nat.stirlingFirst n k := by
    dsimp [sStir]
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul,
      Int.natAbs_natCast]
  rw [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs, hnat]
  simp

private lemma hasDerivAt_prof (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (prof f n) (prof f (n + 1) t) t := by
  have hiter (j : ℕ) (y : ℝ) :
      HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f y) y := by
    have hdj : ContDiff ℝ (j + 1) f := hf.of_le (by simp)
    simpa [iteratedDeriv_succ] using (hdj.differentiable_iteratedDeriv' j y).hasDerivAt
  let term (j : ℕ) (s : ℝ) : ℂ :=
    (sStir n j : ℂ) * ((s ^ (-(n : ℤ)) : ℝ) : ℂ) * iteratedDeriv j f (Real.log s)
  have hterm (j : ℕ) :
      HasDerivAt (term j)
        ((sStir n j : ℂ) * ((t ^ (-((n + 1) : ℤ)) : ℝ) : ℂ) *
          ((-(n : ℂ)) * iteratedDeriv j f (Real.log t) +
            iteratedDeriv (j + 1) f (Real.log t))) t := by
    let c : ℂ := (sStir n j : ℂ)
    let u : ℝ → ℂ := fun s => ((s ^ (-(n : ℤ)) : ℝ) : ℂ)
    let v : ℝ → ℂ := fun s => iteratedDeriv j f (Real.log s)
    have hu := (hasDerivAt_zpow (-(n : ℤ)) t (Or.inl ht.ne')).ofReal_comp
    have hv : HasDerivAt v ((t⁻¹ : ℝ) • iteratedDeriv (j + 1) f (Real.log t)) t :=
      (hiter j (Real.log t)).scomp t (Real.hasDerivAt_log ht.ne')
    have hmul := ((hasDerivAt_const t c).mul hu).mul hv
    refine hmul.congr_deriv ?_
    have hpow : (↑((↑(-(n : ℤ)) : ℝ) * t ^ (-(n : ℤ) - 1)) : ℂ) =
        (-(n : ℂ)) * ↑(t ^ (-((n : ℤ) + 1))) := by
      rw [show (↑(-(n : ℤ)) : ℝ) = -(n : ℝ) by simp [Int.cast_neg, Int.cast_natCast]]
      rw [show -(n : ℤ) - 1 = -((n : ℤ) + 1) by ring]
      rw [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_natCast]
    have hinv : (t ^ (-(n : ℤ)) : ℝ) * t⁻¹ = t ^ (-((n + 1) : ℤ)) := by
      rw [← zpow_neg_one, ← zpow_add₀ ht.ne']
      congr 1
      ring
    have hsmul : (t⁻¹ : ℝ) • iteratedDeriv (j + 1) f (Real.log t) =
        ((t⁻¹ : ℝ) : ℂ) * iteratedDeriv (j + 1) f (Real.log t) := by
      simp [Complex.real_smul]
    set dj := iteratedDeriv j f (Real.log t)
    set djs := iteratedDeriv (j + 1) f (Real.log t)
    set pn := ((t ^ (-(n : ℤ)) : ℝ) : ℂ)
    set pn1 := ((t ^ (-((n + 1) : ℤ)) : ℝ) : ℂ)
    have hpn : pn * ((t⁻¹ : ℝ) : ℂ) = pn1 := by
      simpa [pn, pn1, Complex.ofReal_mul] using congrArg Complex.ofReal hinv
    simp only [c, v, zero_mul, zero_add, Pi.mul_apply]
    rw [hpow, hsmul]
    conv_lhs =>
      rhs
      rw [mul_assoc]
      arg 2
      rw [← mul_assoc]
    rw [hpn]
    ring
  have hsum := HasDerivAt.fun_sum (u := Finset.range (n + 1)) (fun j _hj => hterm j)
  change HasDerivAt (fun s => prof f n s) _ t
  simp only [prof] at hsum ⊢
  refine hsum.congr_deriv ?_
  have hfactor :
      (∑ j ∈ Finset.range (n + 1),
          (sStir n j : ℂ) * ((t ^ (-((n + 1) : ℤ)) : ℝ) : ℂ) *
            ((-(n : ℂ)) * iteratedDeriv j f (Real.log t) +
              iteratedDeriv (j + 1) f (Real.log t))) =
        ((t ^ (-((n + 1) : ℤ)) : ℝ) : ℂ) *
          ∑ j ∈ Finset.range (n + 1),
            ((sStir n j : ℂ) * (-(n : ℂ)) * iteratedDeriv j f (Real.log t) +
              (sStir n j : ℂ) * iteratedDeriv (j + 1) f (Real.log t)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    ring
  rw [hfactor]
  have hid := sStir_sum_identity n (fun j => iteratedDeriv j f (Real.log t))
  rw [hid, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by push_cast; rfl]
  ring

private lemma prof_zero (f : ℝ → ℂ) (t : ℝ) : prof f 0 t = f (Real.log t) := by
  simp [prof, sStir, Nat.stirlingFirst_zero, iteratedDeriv_zero]

/-- Exponential decay in both directions bounds every derivative against every exponential weight. -/
private theorem exp_mul_iteratedDeriv_bounded {f : 𝓢(ℝ, ℂ)} (hf : ExponentialDecay f)
    (j : ℕ) (c : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ,
      Real.exp (c * y) * ‖iteratedDeriv j (f : ℝ → ℂ) y‖ ≤ B := by
  let A := |c| + 1
  have hA : 0 < A := by positivity
  obtain ⟨Cf, Cf_pos, hfwd⟩ := (hf.1 j A hA).exists_pos
  obtain ⟨R, hR⟩ := eventually_atTop.mp hfwd.bound
  obtain ⟨Cb, Cb_pos, hbwd⟩ := (hf.2 j A hA).exists_pos
  obtain ⟨S, hS⟩ := eventually_atBot.mp hbwd.bound
  let R' := max R (0 : ℝ)
  let S' := min S (0 : ℝ)
  have hS'R' : S' ≤ R' := (min_le_right S 0).trans (le_max_right R 0)
  have : (Icc S' R').Nonempty := nonempty_Icc.mpr hS'R'
  let G (y : ℝ) := Real.exp (c * y) * ‖iteratedDeriv j (f : ℝ → ℂ) y‖
  have hGc : Continuous G := by
    have hcont : Continuous (iteratedDeriv j (f : ℝ → ℂ)) :=
      (f.smooth ⊤).continuous_iteratedDeriv j (by simp)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id')).mul hcont.norm
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := S') (b := R')).bddAbove_image hGc.continuousOn
  refine ⟨max (max Cf Cb) (max M 0), by positivity, fun y => ?_⟩
  by_cases hyR : R' ≤ y
  · have hy0 : 0 ≤ y := (le_max_right R 0).trans hyR
    have hyb := hR y ((le_max_left R 0).trans hyR)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at hyb
    have htail : G y ≤ Cf := by
      calc
        G y ≤ Real.exp (c * y) * (Cf * Real.exp (-A * y)) :=
          mul_le_mul_of_nonneg_left hyb (Real.exp_nonneg _)
        _ = Cf * Real.exp ((c - A) * y) := by
          rw [mul_left_comm (Real.exp (c * y)) Cf, ← Real.exp_add]
          congr 1
          ring
        _ ≤ Cf := by
          rw [mul_le_iff_le_one_right Cf_pos, Real.exp_le_one_iff]
          have hcA : c - A ≤ 0 := by
            dsimp [A]
            linarith [le_abs_self c]
          exact mul_nonpos_of_nonpos_of_nonneg hcA hy0
    exact htail.trans ((le_max_left Cf Cb).trans (le_max_left _ _))
  · by_cases hyS : y ≤ S'
    · have hy0 : y ≤ 0 := hyS.trans (min_le_right S 0)
      have hyb := hS y (hyS.trans (min_le_left S 0))
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at hyb
      have htail : G y ≤ Cb := by
        calc
          G y ≤ Real.exp (c * y) * (Cb * Real.exp (A * y)) :=
            mul_le_mul_of_nonneg_left hyb (Real.exp_nonneg _)
          _ = Cb * Real.exp ((c + A) * y) := by
            rw [mul_left_comm (Real.exp (c * y)) Cb, ← Real.exp_add]
            congr 1
            ring
          _ ≤ Cb := by
            rw [mul_le_iff_le_one_right Cb_pos, Real.exp_le_one_iff]
            have hcA : 0 ≤ c + A := by
              dsimp [A]
              linarith [neg_le_abs c]
            exact mul_nonpos_of_nonneg_of_nonpos hcA hy0
      exact htail.trans ((le_max_right Cf Cb).trans (le_max_left _ _))
    · have hyI : y ∈ Icc S' R' := ⟨le_of_not_ge hyS, le_of_not_ge hyR⟩
      exact (hM (mem_image_of_mem G hyI)).trans ((le_max_left M 0).trans (le_max_right _ _))

/-- Paper: Lemma B.2.1.4(3), p. 593. The zero extension of a function with
exponential decay is an ordinary Schwartz function on the real line. -/
theorem exists_schwartz_zeroExtension_of_exponentialDecay (f : 𝓢(ℝ, ℂ))
    (hf : ExponentialDecay f) :
    ∃ g : 𝓢(ℝ, ℂ), (g : ℝ → ℂ) = (Ioi (0 : ℝ)).indicator (fromLog f) := by
  let D (n : ℕ) (s : ℝ) : ℂ := if 0 < s then prof (⇑f) n s else 0
  have hAway (n : ℕ) {s : ℝ} (hs : s ≠ 0) : HasDerivAt (D n) (D (n + 1) s) s := by
    by_cases hs0 : 0 < s
    · have hprof := hasDerivAt_prof (⇑f) f.smooth' n hs0
      have heq : D n =ᶠ[𝓝 s] prof (⇑f) n := by
        filter_upwards [Ioi_mem_nhds hs0] with y hy
        have hy0 : 0 < y := hy
        simp [D, hy0]
      have hval : D (n + 1) s = prof (⇑f) (n + 1) s := by simp [D, hs0]
      rw [hval]
      exact hprof.congr_of_eventuallyEq heq
    · have hsneg : s < 0 := lt_of_le_of_ne (le_of_not_gt hs0) hs
      have heq : D n =ᶠ[𝓝 s] fun _ => (0 : ℂ) := by
        filter_upwards [Iio_mem_nhds hsneg] with y hy
        simp [D, not_lt.mpr hy.le]
      have hval : D (n + 1) s = 0 := by simp [D, not_lt.mpr hsneg.le]
      rw [hval]
      exact (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq heq
  have hNear (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ t, 0 < t → ‖prof (⇑f) n t‖ ≤ K * t := by
    have hB : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ,
        Real.exp ((-((n + 1 : ℕ) : ℝ)) * y) * ‖iteratedDeriv j (f : ℝ → ℂ) y‖ ≤ B :=
      fun j => exp_mul_iteratedDeriv_bounded hf j (-(n + 1 : ℕ))
    choose B hB0 hBy using hB
    refine ⟨∑ j ∈ Finset.range (n + 1), (Nat.stirlingFirst n j : ℝ) * B j,
      Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hB0 j), fun t ht => ?_⟩
    have hzpos : 0 < t ^ (-(n : ℤ)) := zpow_pos ht _
    have hsplit : (t ^ (-(n : ℤ)) : ℝ) =
        t * Real.exp ((-((n + 1 : ℕ) : ℝ)) * Real.log t) := by
      have hexp : (t ^ (-(n : ℤ)) : ℝ) =
          Real.exp ((-(n : ℤ) : ℝ) * Real.log t) := by
        rw [← Real.exp_log hzpos, Real.log_zpow]
        simp [Int.cast_neg, Int.cast_natCast]
      rw [hexp]
      have hcoef : ((-(n : ℤ) : ℝ) * Real.log t) =
          Real.log t + (-((n + 1 : ℕ) : ℝ)) * Real.log t := by
        push_cast
        ring
      rw [hcoef, Real.exp_add, Real.exp_log ht]
    calc
      ‖prof (⇑f) n t‖
        ≤ ∑ j ∈ Finset.range (n + 1),
            ‖(sStir n j : ℂ)‖ * ‖((t ^ (-(n : ℤ)) : ℝ) : ℂ)‖ *
              ‖iteratedDeriv j (f : ℝ → ℂ) (Real.log t)‖ := by
            simpa [prof, norm_mul] using norm_sum_le (Finset.range (n + 1))
              (fun j => (sStir n j : ℂ) * ((t ^ (-(n : ℤ)) : ℝ) : ℂ) *
                iteratedDeriv j (f : ℝ → ℂ) (Real.log t))
      _ = ∑ j ∈ Finset.range (n + 1),
            (Nat.stirlingFirst n j : ℝ) * (t ^ (-(n : ℤ))) *
              ‖iteratedDeriv j (f : ℝ → ℂ) (Real.log t)‖ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_sStir, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzpos]
      _ = ∑ j ∈ Finset.range (n + 1),
            (Nat.stirlingFirst n j : ℝ) * t *
              (Real.exp ((-((n + 1 : ℕ) : ℝ)) * Real.log t) *
                ‖iteratedDeriv j (f : ℝ → ℂ) (Real.log t)‖) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hsplit]
            ring
      _ ≤ ∑ j ∈ Finset.range (n + 1), (Nat.stirlingFirst n j : ℝ) * t * B j := by
            refine Finset.sum_le_sum fun j _ => ?_
            have hnn : 0 ≤ (Nat.stirlingFirst n j : ℝ) * t := by positivity
            exact mul_le_mul_of_nonneg_left (hBy j (Real.log t)) hnn
      _ = (∑ j ∈ Finset.range (n + 1), (Nat.stirlingFirst n j : ℝ) * B j) * t := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
  have hCont (n : ℕ) : Continuous (D n) := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs0 : 0 < s
    · have hprof := (hasDerivAt_prof (⇑f) f.smooth' n hs0).continuousAt
      have heq : prof (⇑f) n =ᶠ[𝓝 s] D n := by
        filter_upwards [Ioi_mem_nhds hs0] with y hy
        have hy0 : 0 < y := hy
        simp [D, hy0]
      exact hprof.congr heq
    · by_cases hs : s = 0
      · subst hs
        obtain ⟨K, _hK0, hK⟩ := hNear n
        refine (Metric.continuousAt_iff).2 fun ε hε => ?_
        refine ⟨ε / (K + 1), by positivity, fun y hy => ?_⟩
        have hyabs : |y| < ε / (K + 1) := by simpa [Real.dist_eq] using hy
        have hzero : D n 0 = 0 := by simp [D]
        rw [hzero, dist_zero_right]
        by_cases hy0 : 0 < y
        · have hle : ‖D n y‖ ≤ K * y := by simpa [D, hy0] using hK y hy0
          calc
            ‖D n y‖ ≤ K * |y| := by simpa [abs_of_pos hy0] using hle
            _ ≤ (K + 1) * |y| :=
              mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
            _ < (K + 1) * (ε / (K + 1)) :=
              mul_lt_mul_of_pos_left hyabs (by positivity)
            _ = ε := by field_simp
        · have : D n y = 0 := by simp [D, hy0]
          simpa [this] using hε
      · have hsneg : s < 0 := lt_of_le_of_ne (le_of_not_gt hs0) hs
        have heq : D n =ᶠ[𝓝 s] fun _ => (0 : ℂ) := by
          filter_upwards [Iio_mem_nhds hsneg] with y hy
          simp [D, not_lt.mpr hy.le]
        exact continuousAt_const.congr heq.symm
  have hHas (n : ℕ) (s : ℝ) : HasDerivAt (D n) (D (n + 1) s) s := by
    by_cases hs : s = 0
    · subst hs
      exact hasDerivAt_of_hasDerivAt_of_ne (fun y hy => hAway n hy)
        (hCont n).continuousAt (hCont (n + 1)).continuousAt
    · exact hAway n hs
  have hIter : ∀ m, iteratedDeriv m (D 0) = D m := by
    intro m
    induction m with
    | zero => simp [iteratedDeriv_zero]
    | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      ext s
      exact (hHas m s).deriv
  have hsmooth : ContDiff ℝ ∞ (D 0) := by
    refine contDiff_of_differentiable_iteratedDeriv (n := ⊤) ?_
    intro m _hm
    simpa [hIter m] using (show Differentiable ℝ (D m) from fun s => (hHas m s).differentiableAt)
  have hdecay : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (D 0) x‖ ≤ C := by
    intro k n
    have hB : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ,
        Real.exp ((((k : ℝ) - n) * y)) * ‖iteratedDeriv j (f : ℝ → ℂ) y‖ ≤ B :=
      fun j => exp_mul_iteratedDeriv_bounded hf j ((k : ℝ) - n)
    choose B hB0 hBy using hB
    refine ⟨∑ j ∈ Finset.range (n + 1), (Nat.stirlingFirst n j : ℝ) * B j, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hIter n]
    by_cases hx : 0 < x
    · have hzpos : 0 < x ^ (-(n : ℤ)) := zpow_pos hx _
      have hpow : (x ^ k : ℝ) * (x ^ (-(n : ℤ)) : ℝ) =
          Real.exp ((((k : ℝ) - n) * Real.log x)) := by
        have hxk : (x ^ k : ℝ) = Real.exp ((k : ℝ) * Real.log x) := by
          rw [← Real.exp_log (pow_pos hx k), Real.log_pow]
        have hxn : (x ^ (-(n : ℤ)) : ℝ) =
            Real.exp ((-(n : ℤ) : ℝ) * Real.log x) := by
          rw [← Real.exp_log hzpos, Real.log_zpow]
          simp [Int.cast_neg, Int.cast_natCast]
        rw [hxk, hxn, ← Real.exp_add]
        congr 1
        push_cast
        ring
      have hnormx : ‖x‖ = x := by simp [Real.norm_eq_abs, abs_of_pos hx]
      rw [hnormx]
      calc
        x ^ k * ‖D n x‖
          = x ^ k * ‖prof (⇑f) n x‖ := by simp [D, hx]
        _ ≤ x ^ k * ∑ j ∈ Finset.range (n + 1),
              ‖(sStir n j : ℂ)‖ * ‖((x ^ (-(n : ℤ)) : ℝ) : ℂ)‖ *
                ‖iteratedDeriv j (f : ℝ → ℂ) (Real.log x)‖ := by
              gcongr
              simpa [prof, norm_mul] using norm_sum_le (Finset.range (n + 1))
                (fun j => (sStir n j : ℂ) * ((x ^ (-(n : ℤ)) : ℝ) : ℂ) *
                  iteratedDeriv j (f : ℝ → ℂ) (Real.log x))
        _ = ∑ j ∈ Finset.range (n + 1),
              (Nat.stirlingFirst n j : ℝ) *
                (x ^ k * (x ^ (-(n : ℤ))) * ‖iteratedDeriv j (f : ℝ → ℂ) (Real.log x)‖) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [norm_sStir, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzpos]
              ring
        _ ≤ ∑ j ∈ Finset.range (n + 1), (Nat.stirlingFirst n j : ℝ) * B j := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [hpow]
              exact mul_le_mul_of_nonneg_left (hBy j (Real.log x)) (by positivity)
    · have hzero : D n x = 0 := by simp [D, hx]
      rw [hzero, norm_zero, mul_zero]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hB0 j)
  let g : 𝓢(ℝ, ℂ) := ⟨D 0, hsmooth, hdecay⟩
  refine ⟨g, ?_⟩
  ext t
  change D 0 t = (Ioi (0 : ℝ)).indicator (fromLog (⇑f)) t
  by_cases ht : 0 < t
  · simp [D, ht, prof_zero, mem_Ioi]
  · simp [D, ht, mem_Ioi]

/-- Paper: Lemma B.2.1.4(4), p. 593. Logarithmic differentiation preserves
forward semi-exponential decay. -/
theorem ForwardSemiExponentialDecay.deriv (f : 𝓢(ℝ, ℂ)) (hf : ForwardSemiExponentialDecay f) :
    ForwardSemiExponentialDecay (SchwartzMap.derivCLM ℂ ℂ f) := by
  intro j A hA
  rw [show (⇑(SchwartzMap.derivCLM ℂ ℂ f) : ℝ → ℂ) = _root_.deriv f from
    funext (SchwartzMap.derivCLM_apply ℂ f), ← iteratedDeriv_succ']
  exact hf (j + 1) A hA

/-- Paper: Lemma B.2.1.4(4), p. 593. Logarithmic differentiation preserves
backward semi-exponential decay. -/
theorem BackwardSemiExponentialDecay.deriv (f : 𝓢(ℝ, ℂ)) (hf : BackwardSemiExponentialDecay f) :
    BackwardSemiExponentialDecay (SchwartzMap.derivCLM ℂ ℂ f) := by
  intro j A hA
  rw [show (⇑(SchwartzMap.derivCLM ℂ ℂ f) : ℝ → ℂ) = _root_.deriv f from
    funext (SchwartzMap.derivCLM_apply ℂ f), ← iteratedDeriv_succ']
  exact hf (j + 1) A hA

/-- Paper: Lemma B.2.1.4(4), p. 593. Logarithmic differentiation preserves
exponential decay. -/
theorem ExponentialDecay.deriv (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) :
    ExponentialDecay (SchwartzMap.derivCLM ℂ ℂ f) := by
  exact ⟨hf.1.deriv f, hf.2.deriv f⟩

private theorem fromLog_locallyIntegrable (f : 𝓢(ℝ, ℂ)) :
    LocallyIntegrableOn (fromLog f) (Ioi 0) volume :=
  (f.continuous.comp_continuousOn (Real.continuousOn_log.mono
    (fun _ hx ↦ ne_of_gt hx))).locallyIntegrableOn measurableSet_Ioi

private theorem isBigO_fromLog_atTop (f : 𝓢(ℝ, ℂ)) (hf : ForwardSemiExponentialDecay f)
    {A : ℝ} (hA : 0 < A) : (fromLog f) =O[atTop] (fun t ↦ t ^ (-A)) :=
  isBigO_comp_log_rpow_of_isBigO_exp (by simpa only [iteratedDeriv_zero] using hf 0 A hA)
    Real.tendsto_log_atTop (eventually_gt_atTop 0)

-- Equation (B.2.1.2) is Mathlib's `mellin`, with `MellinConvergent`
-- for absolute convergence and `HasMellin` for a convergent integral with a specified value.

/-- The Mellin integral of a logarithmic profile after the substitution `t = exp x`. -/
private theorem mellin_fromLog_eq_integral_exp (g : ℝ → ℂ) (s : ℂ) :
    mellin (fromLog g) s = ∫ x : ℝ, Complex.exp (s * x) * g x := by
  rw [mellin, ← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- `|y| ^ (-q)` is integrable away from the origin when `q ≥ 2`. -/
private theorem integrableOn_one_div_abs_rpow_large {q : ℝ} (hq : 2 ≤ q) :
    IntegrableOn (fun y : ℝ ↦ 1 / |y| ^ q) {y | (1 / 2 : ℝ) ≤ |y|} := by
  let mid : Set ℝ := {y | (1 / 2 : ℝ) ≤ |y| ∧ |y| ≤ 1}
  let outer : Set ℝ := {y | (1 : ℝ) ≤ |y|}
  have hmid_eq : mid = Icc (-1) (-(1 / 2)) ∪ Icc (1 / 2) 1 := by
    ext y
    simp only [mid, Set.mem_ofPred, mem_union, mem_Icc]
    constructor
    · intro ⟨h1, h2⟩
      rcases le_total y 0 with hy | hy
      · left
        rw [abs_of_nonpos hy] at h1 h2
        exact ⟨by linarith, by linarith⟩
      · right
        rw [abs_of_nonneg hy] at h1 h2
        exact ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have hy : y ≤ 0 := h2.trans (by norm_num)
        rw [abs_of_nonpos hy]
        exact ⟨by linarith, by linarith⟩
      · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y)]
        exact ⟨h1, h2⟩
  have hunion : {y | (1 / 2 : ℝ) ≤ |y|} = mid ∪ outer := by
    ext y
    simp only [mid, outer, Set.mem_ofPred, mem_union]
    constructor
    · intro hy
      exact (le_or_gt |y| 1).elim (fun h ↦ Or.inl ⟨hy, h⟩) (fun h ↦ Or.inr h.le)
    · rintro (⟨hy, _⟩ | hy)
      · exact hy
      · exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans hy
  have hmid : IntegrableOn (fun y : ℝ ↦ 1 / |y| ^ q) mid := by
    have hbase : Continuous fun y : ℝ ↦ |y| ^ q :=
      (Real.continuous_rpow_const (by linarith : 0 ≤ q)).comp continuous_abs
    have hcont : ContinuousOn (fun y : ℝ ↦ 1 / |y| ^ q) mid :=
      continuousOn_const.div hbase.continuousOn fun y hy ↦
        (Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hy.1) q).ne'
    exact hcont.integrableOn_compact (by rw [hmid_eq]; exact isCompact_Icc.union isCompact_Icc)
  have houter : IntegrableOn (fun y : ℝ ↦ 1 / |y| ^ q) outer := by
    have hmeas : MeasurableSet outer := measurableSet_Ici.preimage continuous_abs.measurable
    rw [← integrable_indicator_iff hmeas]
    have hfun : Measurable fun y : ℝ ↦ 1 / |y| ^ q :=
      Measurable.div measurable_const
        (((Real.continuous_rpow_const (q := q) (by linarith : 0 ≤ q)).comp continuous_abs).measurable)
    apply Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 : ℝ))
      (hfun.indicator hmeas).aestronglyMeasurable
    refine Eventually.of_forall fun y ↦ ?_
    by_cases hy : y ∈ outer
    · rw [indicator_of_mem hy, Real.norm_eq_abs]
      have hy1 : (1 : ℝ) ≤ |y| := hy
      have hval : 0 ≤ 1 / |y| ^ q := by positivity
      rw [abs_of_nonneg hval]
      have hpow : |y| ^ (2 : ℝ) ≤ |y| ^ q := Real.rpow_le_rpow_of_exponent_le hy1 hq
      have hinv : 1 / |y| ^ q ≤ 1 / |y| ^ (2 : ℝ) :=
        div_le_div_of_nonneg_left zero_le_one
          (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < |y|) 2) hpow
      have hy2 : (1 : ℝ) ≤ y ^ 2 := by
        have := pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1) hy1 2
        simpa using this
      have hsq : 1 / |y| ^ (2 : ℝ) ≤ 2 * (1 + y ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, Real.rpow_two, sq_abs]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hy2]
      exact hinv.trans hsq
    · rw [indicator_of_notMem hy, norm_zero]
      positivity
  rw [hunion, integrableOn_union]
  exact ⟨hmid, houter⟩


section ForwardMellin

variable (f : 𝓢(ℝ, ℂ)) (hf : ForwardSemiExponentialDecay f)

include hf

/-- Paper: Proposition B.2.1.5, p. 594. The Mellin integral converges
absolutely in the open right half-plane. -/
theorem mellinConvergent_of_forwardSemiExponentialDecay (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fromLog f) s := by
  obtain ⟨g, hg⟩ := (forwardSemiExponentialDecay_iff_weighted_schwartz f).mp hf s.re hs.le
  exact mellinConvergent_of_integrable_logWeight f s
    ((g.integrable (μ := volume)).congr (Eventually.of_forall hg))

/-- Paper: Proposition B.2.1.5(1), p. 594. The Mellin transform is
holomorphic in the open right half-plane. -/
theorem differentiableOn_mellin_of_forwardSemiExponentialDecay :
    DifferentiableOn ℂ (mellin (fromLog f)) (Complex.re ⁻¹' Ioi 0) := by
  intro s hs
  have hs' : 0 < s.re := hs
  apply DifferentiableAt.differentiableWithinAt
  apply mellin_differentiableAt_of_isBigO_rpow (b := 0) (fromLog_locallyIntegrable f)
    (isBigO_fromLog_atTop f hf (A := s.re + 1) (by linarith)) (lt_add_one _) _ hs'
  apply Asymptotics.IsBigO.of_bound (SchwartzMap.seminorm ℂ 0 0 f)
  filter_upwards with t
  simpa using f.norm_le_seminorm ℂ (Real.log t)

/-- The weighted derivatives have uniform polynomial bounds as the weight varies in a compact
interval of nonnegative exponents. -/
private theorem forward_uniform_weighted_deriv_bound (a b : ℝ) (ha : 0 ≤ a)
    (k j : ℕ) : ∃ B : ℝ, ∀ σ ∈ Icc a b, ∀ x : ℝ,
      |x| ^ k * Real.exp (σ * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖ ≤ B := by
  obtain ⟨A, hA⟩ := forward_weighted_deriv_bound hf ha k j
  by_cases hab : a ≤ b
  · obtain ⟨D, hD⟩ := forward_weighted_deriv_bound hf (ha.trans hab) k j
    refine ⟨max A D, fun σ hσ x ↦ ?_⟩
    by_cases hx : 0 ≤ x
    · calc
        _ ≤ |x| ^ k * Real.exp (b * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσ.2 hx)) (by positivity))
            (norm_nonneg _)
        _ ≤ D := hD x
        _ ≤ _ := le_max_right _ _
    · calc
        _ ≤ |x| ^ k * Real.exp (a * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hσ.1 (le_of_not_ge hx)))
              (by positivity)) (norm_nonneg _)
        _ ≤ A := hA x
        _ ≤ _ := le_max_left _ _
  · exact ⟨A, fun σ hσ ↦ (hab (hσ.1.trans hσ.2)).elim⟩

omit hf in
private theorem verticalPoint_re (σ y : ℝ) : (verticalPoint σ y).re = σ := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

omit hf in
private theorem verticalPoint_im (σ y : ℝ) : (verticalPoint σ y).im = y := by
  rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

omit hf in
private theorem norm_exp_verticalPoint_mul (σ y x : ℝ) :
    ‖Complex.exp ((verticalPoint σ y) * ↑x)‖ = Real.exp (σ * x) := by
  rw [Complex.norm_exp, Complex.mul_re, verticalPoint_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

omit hf in
/-- In logarithmic coordinates the Mellin integral is the Laplace transform of the profile. -/
private theorem mellin_fromLog_eq_integral_cexp (s : ℂ) :
    mellin (fromLog f) s = ∫ x : ℝ, (f : ℝ → ℂ) x * Complex.exp (s * ↑x) := by
  have hsub := integral_comp_exp (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • f (Real.log t))
  rw [mellin, ← hsub]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp]
  rw [← mul_assoc, ← Complex.exp_add, mul_comm]
  congr 1
  ring_nf

/-- A uniform multiple of `(1 + x ^ 2)⁻¹` dominates every nonnegative weight in the interval. -/
private theorem weighted_iteratedDeriv_le_inv_one_add_sq (a b : ℝ) (ha : 0 ≤ a) (j : ℕ) :
    ∃ C : ℝ, ∀ σ ∈ Icc a b, ∀ x : ℝ,
      Real.exp (σ * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖ ≤ C * (1 + x ^ 2)⁻¹ := by
  obtain ⟨B0, hB0⟩ := forward_uniform_weighted_deriv_bound f hf a b ha (0 : ℕ) j
  obtain ⟨B2, hB2⟩ := forward_uniform_weighted_deriv_bound f hf a b ha 2 j
  refine ⟨B0 + B2, fun σ hσ x ↦ ?_⟩
  rw [← div_eq_mul_inv]
  refine (le_div_iff₀ (by positivity)).mpr ?_
  have h0 : Real.exp (σ * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖ ≤ B0 := by
    simpa using hB0 σ hσ x
  have h2 : x ^ 2 * (Real.exp (σ * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖) ≤ B2 := by
    simpa [sq_abs, mul_assoc] using hB2 σ hσ x
  calc
    Real.exp (σ * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖ * (1 + x ^ 2)
      = Real.exp (σ * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖ +
          x ^ 2 * (Real.exp (σ * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖) := by ring
    _ ≤ B0 + B2 := add_le_add h0 h2

private theorem integrable_weighted_iteratedDeriv_norm (a b : ℝ) (ha : 0 ≤ a) (j : ℕ)
    {σ : ℝ} (hσ : σ ∈ Icc a b) :
    Integrable (fun x : ℝ ↦ Real.exp (σ * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖) := by
  obtain ⟨C, hC⟩ := weighted_iteratedDeriv_le_inv_one_add_sq f hf a b ha j
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ ↦ Real.exp (σ * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖) volume :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (((f.smooth ⊤).continuous_iteratedDeriv j (by simp)).norm)).aestronglyMeasurable
  exact (integrable_inv_one_add_sq.const_mul C).mono_nonneg hmeas
    (Eventually.of_forall fun _ ↦ by positivity)
    (Eventually.of_forall fun x ↦ hC σ hσ x)

private theorem integral_norm_weighted_iteratedDeriv_bound (a b : ℝ) (ha : 0 ≤ a) (j : ℕ) :
    ∃ C : ℝ, ∀ σ ∈ Icc a b,
      ∫ x : ℝ, Real.exp (σ * x) * ‖iteratedDeriv j (f : ℝ → ℂ) x‖ ≤ C := by
  obtain ⟨B, hB⟩ := weighted_iteratedDeriv_le_inv_one_add_sq f hf a b ha j
  refine ⟨B * Real.pi, fun σ hσ ↦ ?_⟩
  have hdom : Integrable (fun x : ℝ ↦ B * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul B
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity) hdom
    (Eventually.of_forall fun x ↦ hB σ hσ x)).trans ?_
  rw [integral_const_mul, integral_univ_inv_one_add_sq]

private theorem integrable_cexp_mul_iteratedDeriv (a b : ℝ) (ha : 0 ≤ a)
    (σ y : ℝ) (hσ : σ ∈ Icc a b) (j : ℕ) :
    Integrable (fun x : ℝ ↦
      iteratedDeriv j (f : ℝ → ℂ) x * Complex.exp ((verticalPoint σ y) * ↑x)) := by
  refine (integrable_weighted_iteratedDeriv_norm f hf a b ha j hσ).mono ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    refine (((f.smooth ⊤).continuous_iteratedDeriv j (by simp))).mul ?_
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.ofRealCLM.continuous.comp continuous_id))
  · filter_upwards with x
    rw [norm_mul, norm_exp_verticalPoint_mul, mul_comm, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]

/-- One integration by parts against the exponential, with vanishing boundary terms. -/
private theorem integral_cexp_mul_iteratedDeriv_succ (a b : ℝ) (ha : 0 < a)
    (σ y : ℝ) (hσ : σ ∈ Icc a b) (j : ℕ) :
    ∫ x : ℝ, iteratedDeriv j (f : ℝ → ℂ) x * Complex.exp ((verticalPoint σ y) * ↑x) =
      (-(verticalPoint σ y))⁻¹ *
        ∫ x : ℝ, iteratedDeriv (j + 1) (f : ℝ → ℂ) x *
          Complex.exp ((verticalPoint σ y) * ↑x) := by
  let s := verticalPoint σ y
  let u := fun t : ℝ ↦ iteratedDeriv j (f : ℝ → ℂ) t
  let u' := fun t : ℝ ↦ iteratedDeriv (j + 1) (f : ℝ → ℂ) t
  let v := fun t : ℝ ↦ Complex.exp (s * ↑t)
  let v' := fun t : ℝ ↦ s * Complex.exp (s * ↑t)
  have hs0 : s ≠ 0 := by
    have hσpos : (0 : ℝ) < σ := lt_of_lt_of_le ha hσ.1
    intro hs
    have : σ = 0 := by simpa [s, hs] using (verticalPoint_re σ y).symm
    exact hσpos.ne' this
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    dsimp [u, u']
    rw [iteratedDeriv_succ]
    exact (((f.smooth ⊤).differentiable_iteratedDeriv j
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)) x).hasDerivAt
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    dsimp [v, v']
    have hlin : HasDerivAt (fun t : ℝ ↦ s * ↑t) s x := by
      simpa [mul_one] using ((hasDerivAt_id x).ofReal_comp.const_mul s)
    simpa [mul_comm] using hlin.cexp
  have huv : Integrable (u * v) :=
    integrable_cexp_mul_iteratedDeriv f hf a b ha.le σ y hσ j
  have hu'v : Integrable (u' * v) :=
    integrable_cexp_mul_iteratedDeriv f hf a b ha.le σ y hσ (j + 1)
  have huv' : Integrable (u * v') := by
    have hfun : u * v' = fun x ↦ s * (u x * v x) := by
      funext x; simp only [Pi.mul_apply, v']; ring
    rw [hfun]
    exact huv.const_mul s
  have hparts : ∫ x, u x * v' x = -∫ x, u' x * v x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ ↦ hu x) (fun x _ ↦ hv x) huv' hu'v huv
  have hsmul : ∫ x, u x * v' x = s * ∫ x, u x * v x := by
    have hfun : (fun x ↦ u x * v' x) = fun x ↦ s * (u x * v x) := by
      funext x; simp only [v']; ring
    rw [hfun]
    exact integral_const_mul s fun x ↦ u x * v x
  rw [hsmul] at hparts
  calc
    ∫ x, u x * v x = s⁻¹ * (s * ∫ x, u x * v x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
    _ = s⁻¹ * (-∫ x, u' x * v x) := by rw [hparts]
    _ = (-s)⁻¹ * ∫ x, u' x * v x := by rw [mul_neg, ← neg_mul, ← inv_neg]

private theorem integral_cexp_mul_eq_inv_pow_iteratedDeriv (a b : ℝ) (ha : 0 < a)
    (σ y : ℝ) (hσ : σ ∈ Icc a b) (n : ℕ) :
    ∫ x : ℝ, (f : ℝ → ℂ) x * Complex.exp ((verticalPoint σ y) * ↑x) =
      (-(verticalPoint σ y))⁻¹ ^ n *
        ∫ x : ℝ, iteratedDeriv n (f : ℝ → ℂ) x * Complex.exp ((verticalPoint σ y) * ↑x) := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [ih, integral_cexp_mul_iteratedDeriv_succ f hf a b ha σ y hσ n, ← mul_assoc, ← pow_succ]

/-- Paper: Proposition B.2.1.5(2), p. 594. For each positive integer
power, one constant gives the vertical decay bound throughout the prescribed closed strip. -/
theorem mellin_heightBound_of_forwardSemiExponentialDecay
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C > (0 : ℝ), heightBound (mellin (fromLog f)) (Icc a b) N C := by
  -- The estimate does not use `a < b` or `1 ≤ N` beyond the stated range.
  have _ := hab
  have _ := hN
  obtain ⟨B, hB⟩ := integral_norm_weighted_iteratedDeriv_bound f hf a b ha.le N
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun σ hσ y hy ↦ ?_⟩
  let s := verticalPoint σ y
  have hmeq := mellin_fromLog_eq_integral_cexp f s
  have hiter := integral_cexp_mul_eq_inv_pow_iteratedDeriv f hf a b ha σ y hσ N
  have hreal : ∫ x : ℝ, ‖iteratedDeriv N (f : ℝ → ℂ) x * Complex.exp (s * ↑x)‖ ≤ max B 1 := by
    have hpoint (x : ℝ) : ‖iteratedDeriv N (f : ℝ → ℂ) x * Complex.exp (s * ↑x)‖ =
        Real.exp (σ * x) * ‖iteratedDeriv N (f : ℝ → ℂ) x‖ := by
      rw [norm_mul, norm_exp_verticalPoint_mul, mul_comm]
    rw [integral_congr_ae (Eventually.of_forall hpoint)]
    exact (hB σ hσ).trans (le_max_left _ _)
  have hdecay : ‖s‖⁻¹ ^ N ≤ (|y| ^ N)⁻¹ := by
    have him : |y| ≤ ‖s‖ := by
      rw [← verticalPoint_im σ y]
      exact Complex.abs_im_le_norm s
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
      (inv_anti₀ (abs_pos.mpr hy) him) N
  calc
    ‖mellin (fromLog f) s‖
      = ‖(-s)⁻¹‖ ^ N * ‖∫ x : ℝ, iteratedDeriv N (f : ℝ → ℂ) x * Complex.exp (s * ↑x)‖ := by
        rw [hmeq, hiter, norm_mul, norm_pow]
    _ = ‖s‖⁻¹ ^ N * ‖∫ x : ℝ, iteratedDeriv N (f : ℝ → ℂ) x * Complex.exp (s * ↑x)‖ := by
        rw [norm_inv, norm_neg]
    _ ≤ ‖s‖⁻¹ ^ N * ∫ x : ℝ, ‖iteratedDeriv N (f : ℝ → ℂ) x * Complex.exp (s * ↑x)‖ := by
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
          (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
    _ ≤ (|y| ^ N)⁻¹ * ∫ x : ℝ, ‖iteratedDeriv N (f : ℝ → ℂ) x * Complex.exp (s * ↑x)‖ := by
        exact mul_le_mul_of_nonneg_right hdecay (integral_nonneg fun _ ↦ norm_nonneg _)
    _ ≤ (|y| ^ N)⁻¹ * max B 1 := by
        exact mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr (pow_nonneg (abs_nonneg _) _))
    _ = max B 1 / |y| ^ N := by rw [inv_mul_eq_div]

/-- Paper: Proposition B.2.1.5(3), p. 594. The Lᵖ norms on the vertical
lines admit the displayed central and tail bound, uniformly in the abscissa.
Deviation: The constant from part (2) is supplied with its bound. -/
theorem mellin_verticalLp_of_forwardSemiExponentialDecay
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (p : ℝ) (hp : 1 ≤ p)
    (N : ℕ) (hN : 1 < N) (C : ℝ) (hC : heightBound (mellin (fromLog f)) (Icc a b) N C) :
    ∃ B > (0 : ℝ), ∀ σ ∈ Icc a b,
      eLpNorm (verticalTrace (mellin (fromLog f)) σ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((B ^ p + C ^ p * lpTail p N) ^ (1 / p)) := by
  by_cases hC0 : 0 ≤ C
  · obtain ⟨ga, hga⟩ := (forwardSemiExponentialDecay_iff_weighted_schwartz f).mp hf a ha.le
    obtain ⟨gb, hgb⟩ := (forwardSemiExponentialDecay_iff_weighted_schwartz f).mp hf b
      (ha.le.trans hab.le)
    have hdom : Integrable fun x : ℝ ↦ ‖ga x‖ + ‖gb x‖ :=
      ((ga.integrable (μ := volume)).norm.add (gb.integrable (μ := volume)).norm)
    let M : ℝ := ∫ x : ℝ, ‖ga x‖ + ‖gb x‖
    have hM0 : 0 ≤ M := integral_nonneg fun _ ↦ add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hga_norm (x : ℝ) : ‖ga x‖ = Real.exp (a * x) * ‖f x‖ := by
      rw [hga, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hgb_norm (x : ℝ) : ‖gb x‖ = Real.exp (b * x) * ‖f x‖ := by
      rw [hgb, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hpoint (σ : ℝ) (hσ : σ ∈ Icc a b) (y : ℝ) :
        ‖mellin (fromLog f) (verticalPoint σ y)‖ ≤ M := by
      rw [mellin_fromLog_eq_integral_exp (⇑f)]
      refine norm_integral_le_of_norm_le hdom (Eventually.of_forall fun x ↦ ?_)
      rw [norm_mul, Complex.norm_exp]
      have hre : (((σ : ℂ) + (y : ℂ) * Complex.I) * (x : ℂ)).re = σ * x := by
        simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          sub_zero, add_zero, mul_one]
      rw [hre]
      rcases le_total x 0 with hx | hx
      · exact (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hσ.1 hx)) (norm_nonneg _)).trans
          (by rw [← hga_norm]; exact le_add_of_nonneg_right (norm_nonneg _))
      · exact (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσ.2 hx)) (norm_nonneg _)).trans
          (by rw [← hgb_norm]; exact le_add_of_nonneg_left (norm_nonneg _))
    refine ⟨M + 1, by linarith, fun σ hσ ↦ ?_⟩
    let φ : ℝ → ℂ := verticalTrace (mellin (fromLog f)) σ
    have hcont : Continuous φ := by
      refine (differentiableOn_mellin_of_forwardSemiExponentialDecay f hf).continuousOn.comp_continuous
        (continuous_const.add (Continuous.mul Complex.continuous_ofReal continuous_const)) ?_
      intro y
      rw [Set.mem_preimage, Set.mem_Ioi]
      have hre : ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      rw [hre]
      exact ha.trans_le hσ.1
    let center : Set ℝ := Icc (-(1 / 2 : ℝ)) (1 / 2)
    let tailSet : Set ℝ := {y | 1 / 2 ≤ |y|}
    let bound : ℝ → ℝ := fun y ↦
      center.indicator (fun _ ↦ M ^ p) y +
        tailSet.indicator (fun y ↦ C ^ p * (1 / |y| ^ (p * (N : ℝ)))) y
    have hpointwise (y : ℝ) : ‖φ y‖ ^ p ≤ bound y := by
      by_cases hy : |y| ≤ 1 / 2
      · have hmemc : y ∈ center := (abs_le.mp hy)
        have htailnn : 0 ≤ tailSet.indicator (fun y ↦ C ^ p * (1 / |y| ^ (p * (N : ℝ)))) y := by
          by_cases hyt : y ∈ tailSet
          · rw [indicator_of_mem hyt]
            positivity
          · rw [indicator_of_notMem hyt]
        calc ‖φ y‖ ^ p
          _ ≤ M ^ p := Real.rpow_le_rpow (norm_nonneg _) (hpoint σ hσ y) (by linarith)
          _ ≤ bound y := by
            have hb : bound y = M ^ p +
                tailSet.indicator (fun y ↦ C ^ p * (1 / |y| ^ (p * (N : ℝ)))) y := by
              simp [bound, indicator_of_mem hmemc]
            rw [hb]
            exact le_add_of_nonneg_right htailnn
      · have hy0 : y ≠ 0 := by
          intro hy0
          simp [hy0, abs_zero] at hy
        have hmemt : y ∈ tailSet := (lt_of_not_ge hy).le
        have hnot : y ∉ center := by
          intro hc
          exact hy (abs_le.mpr hc)
        have hrepr : (C / |y| ^ N) ^ p = C ^ p * (1 / |y| ^ (p * (N : ℝ))) := by
          have hyabs : 0 ≤ |y| := abs_nonneg y
          calc (C / |y| ^ N) ^ p
            _ = C ^ p / (|y| ^ N) ^ p := Real.div_rpow hC0 (pow_nonneg hyabs N) p
            _ = C ^ p / (|y| ^ (N : ℝ)) ^ p := by rw [← Real.rpow_natCast]
            _ = C ^ p / |y| ^ ((N : ℝ) * p) := by rw [← Real.rpow_mul hyabs]
            _ = C ^ p / |y| ^ (p * (N : ℝ)) := by rw [mul_comm]
            _ = C ^ p * (1 / |y| ^ (p * (N : ℝ))) := by rw [div_eq_mul_one_div]
        calc ‖φ y‖ ^ p
          _ ≤ (C / |y| ^ N) ^ p :=
            Real.rpow_le_rpow (norm_nonneg _) (hC σ hσ y hy0) (by linarith)
          _ = C ^ p * (1 / |y| ^ (p * (N : ℝ))) := hrepr
          _ = bound y := by simp [bound, indicator_of_notMem hnot, indicator_of_mem hmemt]
    have hcenterMeas : MeasurableSet center := measurableSet_Icc
    have htailMeas : MeasurableSet tailSet := measurableSet_Ici.preimage continuous_abs.measurable
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
    have hq : 2 ≤ p * (N : ℝ) := by
      simpa using (mul_le_mul hp hN2 zero_le_two (by linarith : (0 : ℝ) ≤ p))
    have htailOn : IntegrableOn (fun y : ℝ ↦ 1 / |y| ^ (p * (N : ℝ))) tailSet :=
      integrableOn_one_div_abs_rpow_large hq
    have htailScaled : IntegrableOn (fun y : ℝ ↦ C ^ p * (1 / |y| ^ (p * (N : ℝ)))) tailSet := by
      rw [IntegrableOn] at htailOn ⊢
      exact htailOn.const_mul (C ^ p)
    have hintCenter : Integrable (center.indicator fun _ : ℝ ↦ M ^ p) := by
      rw [integrable_indicator_iff hcenterMeas]
      exact integrableOn_const (by simp [center, Real.volume_Icc, ENNReal.ofReal_ne_top])
    have hintTail : Integrable (tailSet.indicator fun y : ℝ ↦
        C ^ p * (1 / |y| ^ (p * (N : ℝ)))) :=
      htailScaled.integrable_indicator htailMeas
    have hintBound : Integrable bound := hintCenter.add hintTail
    have hboundInt : ∫ y, bound y = M ^ p + C ^ p * lpTail p N := by
      have hsum : ∀ y, bound y = center.indicator (fun _ : ℝ ↦ M ^ p) y +
          tailSet.indicator (fun y : ℝ ↦ C ^ p * (1 / |y| ^ (p * (N : ℝ)))) y :=
        fun _ ↦ rfl
      rw [integral_congr_ae (Eventually.of_forall hsum), integral_add hintCenter hintTail]
      congr 1
      · rw [integral_indicator hcenterMeas, setIntegral_const,
          Real.volume_real_Icc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2), smul_eq_mul]
        norm_num
      · rw [integral_indicator htailMeas, integral_const_mul]
    have hintφ : Integrable fun y : ℝ ↦ ‖φ y‖ ^ p := by
      apply Integrable.mono' hintBound
        (((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp hcont.norm).aestronglyMeasurable)
      refine Eventually.of_forall fun y ↦ ?_
      simp only [Function.comp_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
      exact hpointwise y
    have hppos : 0 < p := by linarith
    have hmem : MemLp φ (ENNReal.ofReal p) := by
      rw [← integrable_norm_rpow_iff hcont.aestronglyMeasurable
        (ne_of_gt (ENNReal.ofReal_pos.mpr hppos)) ENNReal.ofReal_ne_top]
      simpa [ENNReal.toReal_ofReal hppos.le] using hintφ
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (ne_of_gt (ENNReal.ofReal_pos.mpr hppos))
      ENNReal.ofReal_ne_top hmem]
    simp only [ENNReal.toReal_ofReal hppos.le, inv_eq_one_div]
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
      (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) ?_ (by positivity))
    calc ∫ y, ‖φ y‖ ^ p
      _ ≤ ∫ y, bound y := integral_mono_of_nonneg
        (Eventually.of_forall fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) hintBound
        (Eventually.of_forall hpointwise)
      _ = M ^ p + C ^ p * lpTail p N := hboundInt
      _ ≤ (M + 1) ^ p + C ^ p * lpTail p N :=
        add_le_add_left (Real.rpow_le_rpow hM0 (le_add_of_nonneg_right zero_le_one)
          (le_trans zero_le_one hp)) _
  · have hCneg : C < 0 := lt_of_not_ge hC0
    refine ⟨1, one_pos, fun σ hσ ↦ ?_⟩
    rw [eLpNorm_zero_of_ae_eNorm_zero (μ := volume)]
    · exact zero_le
    · have hne : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
        rw [ae_iff]
        simp [measure_singleton]
      filter_upwards [hne] with y hy
      have hnorm0 : ‖mellin (fromLog f) (verticalPoint σ y)‖ = 0 := by
        have hlt : C / |y| ^ N < 0 :=
          div_neg_of_neg_of_pos hCneg (pow_pos (abs_pos.mpr hy) N)
        linarith [norm_nonneg (mellin (fromLog f) (verticalPoint σ y)), hC σ hσ y hy]
      rw [← ofReal_norm, hnorm0, ENNReal.ofReal_zero]

end ForwardMellin

/-- Paper: Lemma B.2.1.6, p. 594. Iterating the Euler derivative
before the exponential change of variables gives the ordinary iterated derivative afterwards. -/
theorem iterate_eulerDeriv_comp_exp (φ : ℝ → ℂ) (hφ : ContDiffOn ℝ ∞ φ (Ioi 0))
    (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    ((fun g : ℝ → ℂ ↦ fun t ↦ (t : ℂ) * deriv g t)^[N]) φ (Real.exp x) =
      iteratedDeriv N (fun u : ℝ ↦ φ (Real.exp u)) x := by
  clear hN
  induction N generalizing φ x with
  | zero => simp
  | succ N ih =>
    have hderiv : ContDiffOn ℝ ∞ (fun t : ℝ ↦ (t : ℂ) * deriv φ t) (Ioi 0) :=
      (Complex.ofRealCLM.contDiff.contDiffOn).mul
        ((hφ.derivWithin (uniqueDiffOn_Ioi 0) le_rfl).congr
          fun t ht ↦ (derivWithin_of_isOpen isOpen_Ioi ht).symm)
    have hchain : (fun u : ℝ ↦ ((Real.exp u : ℝ) : ℂ) * deriv φ (Real.exp u)) =
        deriv (fun u : ℝ ↦ φ (Real.exp u)) := by
      funext u
      have hφu : HasDerivAt φ (deriv φ (Real.exp u)) (Real.exp u) :=
        ((hφ.differentiableOn (by simp)).differentiableAt
          (isOpen_Ioi.mem_nhds (Real.exp_pos u))).hasDerivAt
      have h := HasDerivAt.scomp u hφu (Real.hasDerivAt_exp u)
      exact (Complex.real_smul.symm.trans h.deriv.symm)
    rw [Function.iterate_succ_apply, ih _ hderiv, hchain, ← iteratedDeriv_succ']

-- TODO(paper-gap): Theorem B.2.1.7(1)(c) places a uniform bound on a strip
-- containing the prescribed poles. Even on the punctured strip it rules out
-- every nonzero pole. The statement needs a specified exclusion or height restriction.

section AsymptoticMellin

open Complex

private def cpowLog (a : ℂ) (n : ℕ) : ℝ → ℂ :=
  fun t => (t : ℂ) ^ a * (Real.log t : ℂ) ^ n

private def cpowLogInd (a : ℂ) (n : ℕ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (cpowLog a n)

private theorem continuousOn_cpowLog (a : ℂ) (n : ℕ) :
    ContinuousOn (cpowLog a n) (Ioi 0) := by
  refine ContinuousOn.mul ?_ ?_
  · intro t ht
    exact (continuousAt_ofReal_cpow_const t a (Or.inr ht.ne')).continuousWithinAt
  · refine ContinuousOn.pow ?_ _
    exact continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun t ht => ht.ne')

private theorem isBigO_cpowLog_nhdsGT (a : ℂ) (n : ℕ) {b : ℝ} (hb : -a.re < b) :
    cpowLog a n =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  have hlim : Tendsto (fun t : ℝ => |Real.log t| ^ (n : ℝ) * t ^ (a.re + b)) (𝓝[>] 0) (𝓝 0) := by
    have hs : -(a.re + b) < 0 := by linarith
    refine (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (n : ℝ) hs).tendsto_div_nhds_zero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [div_eq_mul_inv, Real.rpow_neg ht.le, inv_inv]
  have hratio : (fun t : ℝ => ‖cpowLog a n t‖ / t ^ (-b)) =ᶠ[𝓝[>] 0]
      fun t => |Real.log t| ^ (n : ℝ) * t ^ (a.re + b) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [cpowLog, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_pow, norm_real,
      Real.norm_eq_abs]
    rw [div_eq_mul_inv, ← Real.rpow_natCast |Real.log t| n, Real.rpow_neg ht.le, inv_inv,
      mul_right_comm, ← Real.rpow_add ht]
    ac_rfl
  have hlim' := hlim.congr' hratio.symm
  filter_upwards [hlim'.eventually (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with t ht (hpos : 0 < t)
  have hden : 0 < t ^ (-b) := Real.rpow_pos_of_pos hpos _
  have hlt : ‖cpowLog a n t‖ / t ^ (-b) < 1 := ht
  rw [div_lt_one hden] at hlt
  have hnorm : ‖(t : ℝ) ^ (-b)‖ = t ^ (-b) :=
    Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)
  simpa [hnorm, one_mul] using hlt.le

private theorem isBigO_cpowLogInd_nhdsGT (a : ℂ) (n : ℕ) {b : ℝ} (hb : -a.re < b) :
    cpowLogInd a n =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  have hEq : cpowLogInd a n =ᶠ[𝓝[>] (0 : ℝ)] cpowLog a n := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    simp [cpowLogInd, indicator_of_mem ht']
  exact (isBigO_cpowLog_nhdsGT a n hb).congr' hEq.symm .rfl

private theorem isBigO_cpowLogInd_atTop (a : ℂ) (n : ℕ) (c : ℝ) :
    cpowLogInd a n =O[atTop] (fun t : ℝ => t ^ c) := by
  refine Asymptotics.IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have hnot : t ∉ Ioc (0 : ℝ) 1 := fun h => lt_irrefl (1 : ℝ) (ht.trans_le h.2)
  simp [cpowLogInd, indicator_of_notMem hnot]

private theorem locallyIntegrableOn_indicator_Ioc {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0)) :
    LocallyIntegrableOn ((Ioc (0 : ℝ) 1).indicator g) (Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  refine ⟨Ioo (x / 2) (x + 1), mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)),
    ?_⟩
  have hIcc : Icc (x / 2) (x + 1) ⊆ Ioi 0 := by
    intro t ht
    exact lt_of_lt_of_le (half_pos hx0) ht.1
  have hgcont : ContinuousOn g (Icc (x / 2) (x + 1)) := hg.mono hIcc
  have hint : IntegrableOn g (Icc (x / 2) (x + 1)) :=
    hgcont.integrableOn_compact isCompact_Icc
  have hsub : Ioc (0 : ℝ) 1 ∩ Ioo (x / 2) (x + 1) ⊆ Icc (x / 2) (x + 1) := by
    intro t ht
    exact ⟨le_of_lt ht.2.1, le_of_lt ht.2.2⟩
  simpa using (integrableOn_indicator_iff measurableSet_Ioc.nullMeasurableSet).2 (hint.mono_set hsub)

private theorem locallyIntegrableOn_cpowLogInd (a : ℂ) (n : ℕ) :
    LocallyIntegrableOn (cpowLogInd a n) (Ioi 0) :=
  locallyIntegrableOn_indicator_Ioc (continuousOn_cpowLog a n)

private theorem log_mul_cpowLogInd (a : ℂ) (n : ℕ) :
    (fun t : ℝ => (Real.log t : ℂ) * cpowLogInd a n t) = cpowLogInd a (n + 1) := by
  funext t
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · simp only [cpowLogInd, indicator_of_mem ht, cpowLog]
    calc
      (Real.log t : ℂ) * ((t : ℂ) ^ a * (Real.log t : ℂ) ^ n)
          = (t : ℂ) ^ a * ((Real.log t : ℂ) * (Real.log t : ℂ) ^ n) := by ring
      _ = (t : ℂ) ^ a * (Real.log t : ℂ) ^ (n + 1) := by rw [← pow_succ']
  · simp [cpowLogInd, indicator_of_notMem ht]

private theorem hasMellin_cpowLogInd (a : ℂ) (n : ℕ) {s : ℂ} (hs : 0 < s.re + a.re) :
    HasMellin (cpowLogInd a n) s
      ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (s + a) ^ (-(n : ℤ) - 1)) := by
  have hhalf : IsOpen {z : ℂ | 0 < z.re + a.re} := by
    have hEq : {z : ℂ | 0 < z.re + a.re} = (fun z : ℂ => z.re + a.re) ⁻¹' Ioi 0 := by
      ext z; rfl
    rw [hEq]
    exact isOpen_Ioi.preimage (continuous_re.add continuous_const)
  have key : ∀ n : ℕ, ∀ s : ℂ, 0 < s.re + a.re →
      HasMellin (cpowLogInd a n) s (iteratedDeriv n (fun z : ℂ => (z + a)⁻¹) s) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have h0 := hasMellin_cpow_Ioc a hs
      have hfun : cpowLogInd a 0 = (Ioc (0 : ℝ) 1).indicator (fun t : ℝ => (t : ℂ) ^ a) := by
        funext t
        by_cases ht : t ∈ Ioc (0 : ℝ) 1
        · rw [cpowLogInd, indicator_of_mem ht, indicator_of_mem ht, cpowLog, pow_zero, mul_one]
        · rw [cpowLogInd, indicator_of_notMem ht, indicator_of_notMem ht]
      refine ⟨?_, ?_⟩
      · rw [hfun]; exact h0.1
      · rw [hfun, iteratedDeriv_zero, inv_eq_one_div]; exact h0.2
    | succ n ih =>
      intro s hs
      have hloc := locallyIntegrableOn_cpowLogInd a n
      have htop := isBigO_cpowLogInd_atTop a n (-(s.re + 1))
      set b0 : ℝ := (-a.re + s.re) / 2
      have hb0_lt : b0 < s.re := by dsimp [b0]; linarith
      have hb0_gt : -a.re < b0 := by dsimp [b0]; linarith
      have hbot := isBigO_cpowLogInd_nhdsGT a n hb0_gt
      have hder := mellin_hasDerivAt_of_isBigO_rpow (a := s.re + 1) (b := b0)
        hloc htop (by linarith) hbot hb0_lt
      have hsmul := log_mul_cpowLogInd a n
      have hHas : HasDerivAt (mellin (cpowLogInd a n)) (mellin (cpowLogInd a (n + 1)) s) s := by
        simpa [hsmul, real_smul] using hder.2
      have hconv : MellinConvergent (cpowLogInd a (n + 1)) s := by
        simpa [hsmul, real_smul] using hder.1
      have hagree : mellin (cpowLogInd a n) =ᶠ[𝓝 s]
          iteratedDeriv n (fun z : ℂ => (z + a)⁻¹) := by
        filter_upwards [hhalf.mem_nhds hs] with z hz
        exact (ih z hz).2
      refine ⟨hconv, ?_⟩
      rw [← hHas.deriv, hagree.deriv_eq, ← iteratedDeriv_succ]
  have hkey := key n s hs
  have hform : iteratedDeriv n (fun z : ℂ => (z + a)⁻¹) s =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * (s + a) ^ (-(n : ℤ) - 1) := by
    rw [iteratedDeriv_eq_iterate]
    have hlin := congr_fun (iter_deriv_inv_linear n (1 : ℂ) a) s
    simpa [show (-1 - (n : ℤ) = -(n : ℤ) - 1) by ring] using hlin
  simpa [hform] using hkey

private theorem hasMellin_finset_sum {ι : Type*} (p : Finset ι) (f : ι → ℝ → ℂ) (v : ι → ℂ)
    (s : ℂ) (h : ∀ i ∈ p, HasMellin (f i) s (v i)) :
    HasMellin (fun t => ∑ i ∈ p, f i t) s (∑ i ∈ p, v i) := by
  classical
  induction p using Finset.induction with
  | empty =>
    refine ⟨?_, ?_⟩
    · simp only [Finset.sum_empty, MellinConvergent, smul_zero]
      exact integrableOn_zero
    · simp [mellin, Finset.sum_empty]
  | insert i p hi ih =>
    have hfun : (fun t => ∑ j ∈ insert i p, f j t) = fun t => f i t + ∑ j ∈ p, f j t := by
      funext t
      rw [Finset.sum_insert hi]
    have hval : (∑ j ∈ insert i p, v j) = v i + ∑ j ∈ p, v j := Finset.sum_insert hi
    rw [hfun, hval]
    have hi' := h i (Finset.mem_insert_self i p)
    have hp := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have Hadd := hasMellin_add hi'.1 hp.1
    rw [hi'.2, hp.2] at Hadd
    exact Hadd

private theorem exists_lt_withTop {x : ℝ} {b : WithTop ℝ} (hx : (x : WithTop ℝ) < b) :
    ∃ σ : ℝ, x < σ ∧ (σ : WithTop ℝ) < b := by
  cases b with
  | top =>
    exact ⟨x + 1, by linarith, WithTop.coe_lt_top _⟩
  | coe B =>
    have hxB : x < B := by simpa [WithTop.coe_lt_coe] using hx
    refine ⟨(x + B) / 2, by linarith, ?_⟩
    simpa [WithTop.coe_lt_coe] using (by linarith : (x + B) / 2 < B)

private theorem isOpen_reStrip (A : ℝ) (b : WithTop ℝ) :
    IsOpen {s : ℂ | A < s.re ∧ (s.re : WithTop ℝ) < b} := by
  have hset : IsOpen {x : ℝ | A < x ∧ (x : WithTop ℝ) < b} := by
    cases b with
    | top =>
      have hEq : {x : ℝ | A < x ∧ (x : WithTop ℝ) < ⊤} = Ioi A := by
        ext x
        simp [WithTop.coe_lt_top]
      rw [hEq]
      exact isOpen_Ioi
    | coe B =>
      have hEq : {x : ℝ | A < x ∧ (x : WithTop ℝ) < B} = Ioo A B := by
        ext x
        simp [WithTop.coe_lt_coe]
      rw [hEq]
      exact isOpen_Ioo
  convert hset.preimage continuous_re using 1
  ext s
  simp

/-- Paper: Theorem B.2.1.7(2), p. 596. A finite power-log expansion at zero
gives a meromorphic continuation, with poles of the prescribed orders.
Deviation: Meromorphic continuation is in normal form. The coefficients are
indexed by their logarithm degree, starting at zero. -/
theorem exists_meromorphic_mellin_of_asymptoticExpansion
    (a A : ℝ) (b : WithTop ℝ) (ha : 0 < a) (hA : A < 0) (hab : (a : WithTop ℝ) < b)
    (φ : ℝ → ℂ) (hφ : ContDiffOn ℝ ∞ φ (Ioi 0))
    (hWeighted : ∀ σ : ℝ, a < σ → (σ : WithTop ℝ) < b →
      ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = logWeight σ x * φ (Real.exp x))
    (poles : Finset ℂ) (m : ℂ → ℕ) (hm : ∀ α ∈ poles, 1 ≤ m α)
    (hpoles : ∀ α ∈ poles, (-α).re ∈ Ioc A a) (c : ℂ → ℕ → ℂ)
    (hc : ∀ α ∈ poles, c α (m α - 1) ≠ 0)
    (hAsymptotic : (fun t : ℝ ↦ φ t -
      ∑ α ∈ poles, ∑ j ∈ Finset.range (m α), c α j * (t : ℂ) ^ α * (Real.log t : ℂ) ^ j)
      =O[𝓝[>] (0 : ℝ)] fun t ↦ t ^ (-A)) :
    ∃ F : ℂ → ℂ, MeromorphicNFOn F (stripWithTop A b) ∧
      (∀ s ∈ stripWithTop a b, HasMellin φ s (F s)) ∧
      (∀ α ∈ poles, meromorphicOrderAt F (-α) = -((m α : ℕ) : ℤ)) ∧
      ∀ s ∈ stripWithTop A b, -s ∉ poles → 0 ≤ meromorphicOrderAt F s := by
  classical
  -- Cut the power-log expansion off at 1. Its Mellin transform is an explicit
  -- rational function, and the remainder is holomorphic on the wider strip.
  let E : ℝ → ℂ := fun t =>
    ∑ α ∈ poles, ∑ j ∈ Finset.range (m α),
      c α j * (t : ℂ) ^ α * (Real.log t : ℂ) ^ j
  let cutoff : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator E
  let ψ : ℝ → ℂ := fun t => φ t - cutoff t
  let coeff (β : ℂ) (j : ℕ) : ℂ :=
    c β j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ)
  let P : ℂ → ℂ := fun z =>
    ∑ α ∈ poles, ∑ j ∈ Finset.range (m α),
      coeff α j * (z + α) ^ (-(j : ℤ) - 1)
  let F : ℂ → ℂ := fun z => if -z ∈ poles then 0 else mellin ψ z + P z
  have hEfun : E = ∑ α ∈ poles, ∑ j ∈ Finset.range (m α),
      fun t : ℝ => c α j * cpowLog α j t := by
    funext t
    simp only [E, cpowLog, Finset.sum_apply, mul_assoc]
  have hEcont : ContinuousOn E (Ioi 0) := by
    rw [hEfun]
    refine Finset.sum_induction _ (fun g => ContinuousOn g (Ioi 0))
      (fun _ _ hf hg => hf.add hg) continuousOn_const ?_
    intro α _hα
    refine Finset.sum_induction _ (fun g => ContinuousOn g (Ioi 0))
      (fun _ _ hf hg => hf.add hg) continuousOn_const ?_
    intro j _hj
    exact continuousOn_const.mul (continuousOn_cpowLog α j)
  have hψloc : LocallyIntegrableOn ψ (Ioi 0) :=
    (hφ.continuousOn.locallyIntegrableOn measurableSet_Ioi).sub
      (locallyIntegrableOn_indicator_Ioc hEcont)
  have hψφ : ψ =ᶠ[atTop] φ := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    have hnot : t ∉ Ioc (0 : ℝ) 1 := fun h => lt_irrefl (1 : ℝ) (ht.trans_le h.2)
    simp [ψ, cutoff, indicator_of_notMem hnot]
  have hψE : ψ =ᶠ[𝓝[>] (0 : ℝ)] (fun t => φ t - E t) := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    simp [ψ, cutoff, indicator_of_mem ht']
  have hφtop : ∀ {σ : ℝ}, a < σ → (σ : WithTop ℝ) < b →
      φ =O[atTop] (fun t : ℝ => t ^ (-σ)) := by
    intro σ hσa hσb
    obtain ⟨g, hg⟩ := hWeighted σ hσa hσb
    have hprof : (fun x : ℝ => φ (Real.exp x)) =O[atTop] (fun x => Real.exp (-σ * x)) := by
      refine Asymptotics.IsBigO.of_bound (SchwartzMap.seminorm ℂ 0 0 g) ?_
      filter_upwards with x
      have hmul : φ (Real.exp x) = (Real.exp (-σ * x) : ℂ) * g x := by
        have hne : (Real.exp (σ * x) : ℂ) ≠ 0 := by
          exact_mod_cast Real.exp_ne_zero (σ * x)
        apply mul_left_cancel₀ hne
        calc
          (Real.exp (σ * x) : ℂ) * φ (Real.exp x) = g x := (hg x).symm
          _ = (Real.exp (σ * x) : ℂ) * ((Real.exp (-σ * x) : ℂ) * g x) := by
            rw [← mul_assoc, ← ofReal_mul, ← Real.exp_add]
            have hzero : σ * x + -σ * x = 0 := by ring
            rw [hzero, Real.exp_zero, ofReal_one, one_mul]
      rw [hmul]
      calc
        ‖(Real.exp (-σ * x) : ℂ) * g x‖ = Real.exp (-σ * x) * ‖g x‖ := by
          rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
        _ ≤ Real.exp (-σ * x) * SchwartzMap.seminorm ℂ 0 0 g :=
          mul_le_mul_of_nonneg_left (g.norm_le_seminorm ℂ x) (Real.exp_nonneg _)
        _ = SchwartzMap.seminorm ℂ 0 0 g * ‖Real.exp (-σ * x)‖ := by
          rw [mul_comm, Real.norm_of_nonneg (Real.exp_nonneg _)]
    refine (isBigO_comp_log_rpow_of_isBigO_exp hprof Real.tendsto_log_atTop
      (eventually_gt_atTop 0)).congr' ?_ .rfl
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [Real.exp_log ht]
  have hpow : ∀ {p q : ℝ}, q ≤ p →
      (fun t : ℝ => t ^ p) =O[𝓝[>] (0 : ℝ)] (fun t => t ^ q) := by
    intro p q hpq
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    have ht0 : 0 < t := ht.1
    have hle1 : t ≤ 1 := ht.2.le
    have hcmp : t ^ p ≤ t ^ q := by
      have happ : p = q + (p - q) := by ring
      rw [happ, Real.rpow_add ht0]
      have hsmall : t ^ (p - q) ≤ 1 := Real.rpow_le_one ht0.le hle1 (by linarith)
      calc
        t ^ q * t ^ (p - q) ≤ t ^ q * 1 :=
          mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg ht0.le _)
        _ = t ^ q := mul_one _
    simpa [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), one_mul] using hcmp
  have hψbot : ∀ {s : ℂ}, A < s.re →
      ψ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-((A + s.re) / 2))) := by
    intro s hsA
    have hrem := hAsymptotic.trans
      (hpow (p := -A) (q := -((A + s.re) / 2)) (by linarith))
    exact hrem.congr' hψE.symm .rfl
  have hψdecay : ∀ s : ℂ, A < s.re → (s.re : WithTop ℝ) < b →
      ∃ σ : ℝ, s.re < σ ∧ ψ =O[atTop] (fun t : ℝ => t ^ (-σ)) ∧
        ψ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-((A + s.re) / 2))) ∧
        (A + s.re) / 2 < s.re := by
    intro s hsA hsb
    have hx : ((max a s.re : ℝ) : WithTop ℝ) < b := by
      by_cases hsa : s.re ≤ a
      · rw [max_eq_left hsa]; exact hab
      · rw [max_eq_right (le_of_not_ge hsa)]; exact hsb
    obtain ⟨σ, hσgt, hσb⟩ := exists_lt_withTop hx
    have hσa : a < σ := lt_of_le_of_lt (le_max_left a s.re) hσgt
    have hσs : s.re < σ := lt_of_le_of_lt (le_max_right a s.re) hσgt
    refine ⟨σ, hσs, (hφtop hσa hσb).congr' hψφ.symm .rfl, hψbot hsA, by linarith⟩
  have hstrip : IsOpen (stripWithTop A b) := isOpen_reStrip A b
  have hHdiff : DifferentiableOn ℂ (mellin ψ) (stripWithTop A b) := by
    intro s hs
    obtain ⟨σ, hσs, htop, hbot, hb0⟩ := hψdecay s hs.1 hs.2
    exact (mellin_differentiableAt_of_isBigO_rpow hψloc htop hσs hbot hb0).differentiableWithinAt
  have hHanal : ∀ s ∈ stripWithTop A b, AnalyticAt ℂ (mellin ψ) s :=
    fun s hs => hHdiff.analyticAt (hstrip.mem_nhds hs)
  have hterm : ∀ β ∈ poles, ∀ j ∈ Finset.range (m β), ∀ s : ℂ, a < s.re →
      HasMellin ((Ioc (0 : ℝ) 1).indicator
        (fun t => c β j * (t : ℂ) ^ β * (Real.log t : ℂ) ^ j)) s
        (coeff β j * (s + β) ^ (-(j : ℤ) - 1)) := by
    intro β hβ j _hj s hs
    have hre : 0 < s.re + β.re := by
      have : -β.re ≤ a := by simpa [neg_re] using (hpoles β hβ).2
      linarith
    have hbase := hasMellin_cpowLogInd β j hre
    have hsm := hasMellin_const_smul hbase.1 (c β j)
    rw [hbase.2] at hsm
    have hfun : (fun t => (c β j) • cpowLogInd β j t) =
        (Ioc (0 : ℝ) 1).indicator
          (fun t => c β j * (t : ℂ) ^ β * (Real.log t : ℂ) ^ j) := by
      funext t
      by_cases ht : t ∈ Ioc (0 : ℝ) 1
      · simp [cpowLogInd, cpowLog, ht, indicator_of_mem, smul_eq_mul, mul_assoc]
      · simp [cpowLogInd, ht, indicator_of_notMem, smul_eq_mul]
    have hval : (c β j) • ((-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) *
        (s + β) ^ (-(j : ℤ) - 1)) = coeff β j * (s + β) ^ (-(j : ℤ) - 1) := by
      simp [coeff, smul_eq_mul, mul_assoc]
    rw [hfun, hval] at hsm
    exact hsm
  have hcutFun : cutoff = fun t =>
      ∑ α ∈ poles, ∑ j ∈ Finset.range (m α),
        (Ioc (0 : ℝ) 1).indicator
          (fun u => c α j * (u : ℂ) ^ α * (Real.log u : ℂ) ^ j) t := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · simp [cutoff, E, indicator_of_mem ht]
    · simp [cutoff, E, indicator_of_notMem ht]
  have hcut : ∀ s : ℂ, a < s.re → HasMellin cutoff s (P s) := by
    intro s hs
    have hsum := hasMellin_finset_sum poles
      (fun α t => ∑ j ∈ Finset.range (m α),
        (Ioc (0 : ℝ) 1).indicator
          (fun u => c α j * (u : ℂ) ^ α * (Real.log u : ℂ) ^ j) t)
      (fun α => ∑ j ∈ Finset.range (m α), coeff α j * (s + α) ^ (-(j : ℤ) - 1)) s
      ?_
    · rw [hcutFun]
      simpa [P, Finset.sum_apply] using hsum
    · intro α hα
      refine hasMellin_finset_sum (Finset.range (m α))
        (fun j t => (Ioc (0 : ℝ) 1).indicator
          (fun u => c α j * (u : ℂ) ^ α * (Real.log u : ℂ) ^ j) t)
        (fun j => coeff α j * (s + α) ^ (-(j : ℤ) - 1)) s ?_
      intro j hj
      simpa using hterm α hα j hj s hs
  have hsplit : ∀ s : ℂ, s ∈ stripWithTop a b → HasMellin φ s (mellin ψ s + P s) := by
    intro s hs
    obtain ⟨σ, hσs, hσb⟩ := exists_lt_withTop hs.2
    have htop : ψ =O[atTop] (fun t => t ^ (-σ)) :=
      (hφtop (hs.1.trans hσs) hσb).congr' hψφ.symm .rfl
    have hbot : ψ =O[𝓝[>] 0] (fun t => t ^ (-((A + s.re) / 2))) :=
      hψbot (lt_trans hA (lt_trans ha hs.1))
    have hψc : MellinConvergent ψ s :=
      mellinConvergent_of_isBigO_rpow hψloc htop hσs hbot (by linarith [hs.1, hA, ha])
    have hcu := hcut s hs.1
    have Hadd := hasMellin_add hψc hcu.1
    have hsum : (fun t => ψ t + cutoff t) = φ := by
      funext t; simp [ψ]
    rw [hsum, hcu.2] at Hadd
    exact Hadd
  have hPanal : ∀ {s : ℂ}, -s ∉ poles → AnalyticAt ℂ P s := by
    intro s hs
    have hPfun : P = ∑ α ∈ poles, ∑ j ∈ Finset.range (m α),
        fun z : ℂ => coeff α j * (z + α) ^ (-(j : ℤ) - 1) := by
      funext z
      simp [P, Finset.sum_apply]
    rw [hPfun]
    refine Finset.sum_induction _ (fun g => AnalyticAt ℂ g s)
      (fun _ _ hf hg => hf.add hg) analyticAt_const ?_
    intro α hα
    refine Finset.sum_induction _ (fun g => AnalyticAt ℂ g s)
      (fun _ _ hf hg => hf.add hg) analyticAt_const ?_
    intro j _hj
    refine analyticAt_const.mul ?_
    have hne : s + α ≠ 0 := by
      intro hzero
      apply hs
      have : s = -α := add_eq_zero_iff_eq_neg.mp hzero
      simpa [this] using hα
    exact ((analyticAt_id.add analyticAt_const).zpow hne)
  have hpoleClosed : IsClosed {z : ℂ | -z ∈ poles} := by
    have hEq : {z : ℂ | -z ∈ poles} = Neg.neg '' (poles : Set ℂ) := by
      ext z
      constructor
      · intro hz
        refine ⟨-z, by simpa using hz, by simp⟩
      · rintro ⟨α, hα, rfl⟩
        simpa using hα
    rw [hEq]
    exact (poles.finite_toSet.image Neg.neg).isClosed
  have hdecomp : ∀ α ∈ poles, ∃ G : ℂ → ℂ, AnalyticAt ℂ G (-α) ∧ G (-α) ≠ 0 ∧
      F =ᶠ[𝓝 (-α)] fun z => (z - (-α)) ^ (-(m α : ℤ)) • G z := by
    intro α hα
    have hk : (1 : ℕ) ≤ m α := hm α hα
    let x : ℂ := -α
    have hxstrip : x ∈ stripWithTop A b := by
      have hI := hpoles α hα
      refine ⟨by simpa [x, neg_re] using hI.1, ?_⟩
      exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr (by simpa [x, neg_re] using hI.2)) hab
    let regular : ℂ → ℂ := fun z =>
      mellin ψ z + ∑ β ∈ poles.erase α, ∑ j ∈ Finset.range (m β),
        coeff β j * (z + β) ^ (-(j : ℤ) - 1)
    let singular : ℂ → ℂ := fun z =>
      ∑ j ∈ Finset.range (m α),
        c α j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) * (z + α) ^ (m α - (j + 1))
    let G : ℂ → ℂ := fun z => (z + α) ^ (m α) * regular z + singular z
    have hreg : AnalyticAt ℂ regular x := by
      have hfun : regular = (fun z : ℂ => mellin ψ z) +
          ∑ β ∈ poles.erase α, ∑ j ∈ Finset.range (m β),
            fun z : ℂ => coeff β j * (z + β) ^ (-(j : ℤ) - 1) := by
        funext z
        simp [regular, Finset.sum_apply]
      rw [hfun]
      refine (hHanal x hxstrip).add ?_
      refine Finset.analyticAt_sum (poles.erase α) ?_
      intro β hβ
      have hβne : β ≠ α := (Finset.mem_erase.mp hβ).1
      refine Finset.analyticAt_sum (Finset.range (m β)) ?_
      intro j _hj
      refine analyticAt_const.mul ?_
      have hne : x + β ≠ 0 := by
        intro hzero
        apply hβne
        have h' : β + (-α) = 0 := by simpa [x, add_comm] using hzero
        exact (add_eq_zero_iff_eq_neg.mp h').trans (neg_neg α)
      exact ((analyticAt_id.add analyticAt_const).zpow hne)
    have hsingA : AnalyticAt ℂ singular x := by
      have hfun : singular = ∑ j ∈ Finset.range (m α),
          fun z : ℂ => c α j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) *
            (z + α) ^ (m α - (j + 1)) := by
        funext z
        simp [singular, Finset.sum_apply]
      rw [hfun]
      refine Finset.analyticAt_sum (Finset.range (m α)) ?_
      intro j _hj
      exact analyticAt_const.mul ((analyticAt_id.add analyticAt_const).pow _)
    have hGanal : AnalyticAt ℂ G x :=
      (((analyticAt_id.add analyticAt_const).pow (m α)).mul hreg).add hsingA
    have hsingx : singular x = coeff α (m α - 1) := by
      have hmemj : m α - 1 ∈ Finset.range (m α) :=
        Finset.mem_range.mpr (Nat.sub_lt (Nat.lt_of_lt_of_le zero_lt_one hk) zero_lt_one)
      rw [show singular x = ∑ j ∈ Finset.range (m α),
          c α j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) *
            (x + α) ^ (m α - (j + 1)) from rfl]
      rw [Finset.sum_eq_single_of_mem (m α - 1) hmemj]
      · rw [show m α - (m α - 1 + 1) = 0 by rw [Nat.sub_add_cancel hk, Nat.sub_self],
          pow_zero, mul_one]
      · intro j hj hjne
        have hjk : j < m α := Finset.mem_range.mp hj
        have hjl : j ≤ m α - 1 := Nat.le_sub_one_of_lt hjk
        have hjs : j < m α - 1 := lt_of_le_of_ne hjl hjne
        have hsucc : j + 1 < m α := by
          have hcancel : (m α - 1) + 1 = m α := Nat.sub_add_cancel hk
          simpa [hcancel] using Nat.add_lt_add_right hjs 1
        rw [show x + α = 0 by simp [x], zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hsucc)),
          mul_zero]
    have hGne : G x ≠ 0 := by
      have hzero : (x + α) ^ (m α) * regular x = 0 := by
        simp [x, zero_pow (Nat.one_le_iff_ne_zero.mp hk)]
      rw [show G x = (x + α) ^ (m α) * regular x + singular x from rfl, hzero, zero_add, hsingx]
      unfold coeff
      apply mul_ne_zero
      · apply mul_ne_zero
        · simpa using hc α hα
        · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
      · exact_mod_cast (Nat.factorial_pos (m α - 1)).ne'
    have hiden : ∀ z, z ≠ x →
        mellin ψ z + P z = (z - x) ^ (-(m α : ℤ)) * G z := by
      intro z hz
      have hzα : z + α ≠ 0 := by
        intro hzero
        exact hz ((add_eq_zero_iff_eq_neg.mp hzero).trans (by simp [x]))
      have hshift : z - x = z + α := by simp [x]
      have hcancel : (z + α) ^ (-(m α : ℤ)) * ((z + α) ^ (m α) * regular z) = regular z := by
        have hmul : (z + α) ^ (-(m α : ℤ)) * (z + α) ^ ((m α : ℕ) : ℤ) = 1 := by
          rw [← zpow_add₀ hzα, neg_add_cancel, zpow_zero]
        calc
          (z + α) ^ (-(m α : ℤ)) * ((z + α) ^ (m α) * regular z)
              = ((z + α) ^ (-(m α : ℤ)) * (z + α) ^ ((m α : ℕ) : ℤ)) * regular z := by
                rw [← mul_assoc, ← zpow_natCast]
          _ = regular z := by rw [hmul, one_mul]
      have hsingmul : (z + α) ^ (-(m α : ℤ)) * singular z =
          ∑ j ∈ Finset.range (m α), coeff α j * (z + α) ^ (-(j : ℤ) - 1) := by
        simp only [singular, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hle : j + 1 ≤ m α := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
        have hexp : (z + α) ^ (-(m α : ℤ)) * (z + α) ^ (m α - (j + 1)) =
            (z + α) ^ (-(j : ℤ) - 1) := by
          rw [← zpow_natCast, ← zpow_add₀ hzα]
          congr 1
          rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
          ring
        calc
          (z + α) ^ (-(m α : ℤ)) *
              (c α j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) *
                (z + α) ^ (m α - (j + 1)))
            = c α j * (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) *
                ((z + α) ^ (-(m α : ℤ)) * (z + α) ^ (m α - (j + 1))) := by ring
          _ = coeff α j * (z + α) ^ (-(j : ℤ) - 1) := by rw [hexp]
      have hsplitP : P z =
          (∑ β ∈ poles.erase α, ∑ j ∈ Finset.range (m β),
            coeff β j * (z + β) ^ (-(j : ℤ) - 1)) +
          ∑ j ∈ Finset.range (m α), coeff α j * (z + α) ^ (-(j : ℤ) - 1) := by
        have hsum := Finset.sum_erase_add
          (f := fun β => ∑ j ∈ Finset.range (m β),
            coeff β j * (z + β) ^ (-(j : ℤ) - 1)) (s := poles) hα
        simpa [P, add_comm] using hsum.symm
      calc
        mellin ψ z + P z
            = regular z + ∑ j ∈ Finset.range (m α),
                coeff α j * (z + α) ^ (-(j : ℤ) - 1) := by
              simp only [regular, hsplitP, add_assoc]
        _ = regular z + (z + α) ^ (-(m α : ℤ)) * singular z := by rw [← hsingmul]
        _ = (z + α) ^ (-(m α : ℤ)) * ((z + α) ^ (m α) * regular z) +
              (z + α) ^ (-(m α : ℤ)) * singular z := by rw [hcancel]
        _ = (z - x) ^ (-(m α : ℤ)) * G z := by rw [← mul_add, hshift]
    let bad : Finset ℂ := (poles.erase α).image fun β => -β
    have hxbad : x ∉ (bad : Set ℂ) := by
      intro hx
      obtain ⟨β, hβ, hβx⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_erase.mp hβ).1 (by simpa [x] using hβx)
    have havoid : {z : ℂ | z ∉ (bad : Set ℂ)} ∈ 𝓝 x :=
      (isOpen_compl_iff.mpr bad.finite_toSet.isClosed).mem_nhds hxbad
    have hEq : F =ᶠ[𝓝 x] fun z => (z - x) ^ (-(m α : ℤ)) • G z := by
      filter_upwards [havoid] with z hz
      by_cases hzx : z = x
      · subst hzx
        have hk0 : (-(m α : ℤ)) ≠ 0 := by
          intro hk0
          exact Nat.one_le_iff_ne_zero.mp hk (by exact_mod_cast neg_eq_zero.mp hk0)
        rw [sub_self, zero_zpow (-(m α : ℤ)) hk0, zero_smul]
        simp [F, x, hα]
      · have hnot : -z ∉ poles := by
          intro hzmem
          by_cases hαeq : -z = α
          · exact hzx (by simpa [x] using neg_eq_iff_eq_neg.mp hαeq)
          · exact hz (Finset.mem_image.mpr ⟨-z, Finset.mem_erase.mpr ⟨hαeq, hzmem⟩, by simp⟩)
        simp [F, hnot, smul_eq_mul, hiden z hzx]
    exact ⟨G, hGanal, hGne, hEq⟩
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro s hs
    by_cases hmem : -s ∈ poles
    · obtain ⟨α, hα, hsα⟩ : ∃ α ∈ poles, s = -α := ⟨-s, hmem, by simp⟩
      obtain ⟨G, hGan, hGne, hEq⟩ := hdecomp α hα
      rw [hsα]
      exact Or.inr ⟨(-(m α : ℤ)), G, hGan, hGne, hEq⟩
    · have hFeq : F =ᶠ[𝓝 s] fun z => mellin ψ z + P z := by
        filter_upwards [(isOpen_compl_iff.mpr hpoleClosed).mem_nhds (by simpa using hmem)] with z hz
        simp [F, show -z ∉ poles from by simpa using hz]
      exact (((hHanal s hs).add (hPanal hmem)).congr hFeq.symm).meromorphicNFAt
  · intro s hs
    have hnot : -s ∉ poles := by
      intro hmem
      have : s.re ≤ a := by simpa [neg_neg, neg_re] using (hpoles (-s) hmem).2
      exact (not_lt_of_ge this) hs.1
    simpa [F, hnot] using hsplit s hs
  · intro α hα
    obtain ⟨G, hGan, hGne, hEq⟩ := hdecomp α hα
    have hNF : MeromorphicNFAt F (-α) := Or.inr ⟨(-(m α : ℤ)), G, hGan, hGne, hEq⟩
    have hcast : (((-(m α : ℤ)) : ℤ) : WithTop ℤ) = -((m α : ℕ) : ℤ) := by
      simp
    rw [← hcast, meromorphicOrderAt_eq_int_iff hNF.meromorphicAt]
    exact ⟨G, hGan, hGne, hEq.filter_mono nhdsWithin_le_nhds⟩
  · intro s hs hnot
    have hFeq : F =ᶠ[𝓝 s] fun z => mellin ψ z + P z := by
      filter_upwards [(isOpen_compl_iff.mpr hpoleClosed).mem_nhds (by simpa using hnot)] with z hz
      simp [F, show -z ∉ poles from by simpa using hz]
    exact (((hHanal s hs).add (hPanal hnot)).congr hFeq.symm).meromorphicOrderAt_nonneg


end AsymptoticMellin

/-- Paper: Equation (B.2.1.19), p. 597. The logarithmic profile is
m-times continuously differentiable and its derivatives through order m vanish at infinity. -/
def MemLogContDiffZero (m : ℕ) (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ (m : ℕ∞) f ∧
    ∀ j ≤ m, Tendsto (iteratedDeriv j f) (cocompact ℝ) (𝓝 0)

/-- Paper: Equation (B.2.1.19), p. 597. At order zero the condition
means that the logarithmic profile is a continuous map vanishing at infinity.
Deviation: Sanity check using Mathlib's bundled space. -/
theorem memLogContDiffZero_zero_iff (f : ℝ → ℂ) :
    MemLogContDiffZero 0 f ↔
      ∃ g : ZeroAtInftyContinuousMap ℝ ℂ, (g : ℝ → ℂ) = f := by
  constructor
  · rintro ⟨hc, ht⟩
    have hc' : Continuous f := by simpa using hc
    refine ⟨⟨⟨f, hc'⟩, ?_⟩, rfl⟩
    simpa using ht 0 le_rfl
  · rintro ⟨g, rfl⟩
    refine ⟨by simpa using g.continuous, ?_⟩
    intro j hj
    obtain rfl := Nat.le_zero.mp hj
    simpa using g.zero_at_infty'

/-- Paper: Equation (B.2.1.19), p. 597. The norm is the sum of the
supremum norms of the logarithmic derivatives through order m. -/
def logContDiffZeroNorm (m : ℕ) (f : {f : ℝ → ℂ // MemLogContDiffZero m f}) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), sSup (range fun x : ℝ ↦ ‖iteratedDeriv j f.val x‖)

/-- Paper: Equation (B.2.1.19), p. 597. At order zero the norm is the
supremum of the absolute value on the positive reals.
Deviation: Sanity check for the logarithmic norm. -/
theorem logContDiffZeroNorm_zero (f : {f : ℝ → ℂ // MemLogContDiffZero 0 f}) :
    logContDiffZeroNorm 0 f = sSup (range fun x : ℝ ↦ ‖f.val x‖) := by
  simp [logContDiffZeroNorm]

/-- Paper: Equation (B.2.2.4), p. 601. An upward vertical line integral uses
the parameter y ↦ σ + iy and its differential i dy. -/
def verticalLineIntegral (Φ : ℂ → ℂ) (σ : ℝ) : ℂ :=
  Complex.I * ∫ y : ℝ, Φ (verticalPoint σ y)

open scoped Interval in
/-- Cauchy–Goursat on expanding rectangles allows a vertical contour to be shifted
across a strip of holomorphy when its horizontal boundary integrals tend to zero. -/
private theorem verticalIntegral_eq_of_contour_shift {K : ℂ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hK : DifferentiableOn ℂ K (Complex.re ⁻¹' Icc c d))
    (hc : Complex.VerticalIntegrable K c) (hd : Complex.VerticalIntegrable K d)
    (hh : Tendsto (fun y : ℝ ↦ ∫ x in c..d, K (verticalPoint x y)) atAbsInfty (𝓝 0)) :
    verticalLineIntegral K d = verticalLineIntegral K c := by
  have hrect (t : ℝ) :
      (∫ x in c..d, K (verticalPoint x (-t))) - (∫ x in c..d, K (verticalPoint x t)) +
      Complex.I • (∫ y in -t..t, K (verticalPoint d y)) -
      Complex.I • (∫ y in -t..t, K (verticalPoint c y)) = 0 := by
    apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn K (⟨c, -t⟩ : ℂ) (⟨d, t⟩ : ℂ)
    apply hK.mono
    intro w hw
    simpa only [uIcc_of_le hcd] using hw.1
  have ht : Tendsto (fun t : ℝ ↦ t) atTop atAbsInfty := by
    apply tendsto_comap_iff.mpr
    exact tendsto_abs_atTop_atTop
  have hn : Tendsto (fun t : ℝ ↦ -t) atTop atAbsInfty := by
    apply tendsto_comap_iff.mpr
    simpa [Function.comp_def] using tendsto_abs_atTop_atTop
  have hv (x : ℝ) (hi : Complex.VerticalIntegrable K x) :=
    intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot (tendsto_id : Tendsto id atTop (atTop : Filter ℝ))
  have hlim := (((hh.comp hn).sub (hh.comp ht)).add ((hv d hd).const_smul Complex.I)).sub
    ((hv c hc).const_smul Complex.I)
  have heq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun t ↦ (hrect t).symm)
  simpa [verticalLineIntegral, sub_eq_zero] using heq

/-- A weighted bound on a positive closed strip gives uniform decay in the height. -/
private theorem verticalTrace_polynomialDecay {F : ℂ → ℂ} {c d N : ℝ} (hc : 0 < c)
    (hN : 0 ≤ N)
    (hBound : BddAbove ((fun s : ℂ ↦ ‖s‖ ^ N * ‖F s‖) '' closedStrip c d)) :
    ∃ C ≥ (0 : ℝ), ∀ σ ∈ Icc c d, ∀ y : ℝ,
      ‖verticalTrace F σ y‖ ≤ C * (1 + ‖y‖) ^ (-N) := by
  obtain ⟨B, hB⟩ := hBound
  let A := 1 + c⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A ^ N * max B 0, by positivity, ?_⟩
  intro σ hσ y
  let z := verticalPoint σ y
  have hre : c ≤ ‖z‖ := hσ.1.trans (by
    simpa [z, abs_of_pos (hc.trans_le hσ.1)] using Complex.abs_re_le_norm z)
  have him : ‖y‖ ≤ ‖z‖ := by simpa [z, Real.norm_eq_abs] using Complex.abs_im_le_norm z
  have hone : 1 ≤ c⁻¹ * ‖z‖ := (one_le_inv_mul₀ hc).mpr hre
  have hle : 1 + ‖y‖ ≤ A * ‖z‖ := by
    calc
      1 + ‖y‖ ≤ c⁻¹ * ‖z‖ + ‖z‖ := add_le_add hone him
      _ = A * ‖z‖ := by dsimp only [A]; ring
  have hz : z ∈ closedStrip c d := by simpa [z] using hσ
  have hF := (hB (mem_image_of_mem _ hz)).trans (le_max_left B 0)
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    ‖F z‖ * (1 + ‖y‖) ^ N ≤ ‖F z‖ * (A * ‖z‖) ^ N := by
      gcongr
    _ = A ^ N * (‖z‖ ^ N * ‖F z‖) := by rw [Real.mul_rpow hA.le (norm_nonneg _)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hF (by positivity)

/-- An integrable power envelope controls every moment whose remaining decay has exponent
greater than one. -/
private theorem integrable_verticalTrace_moment {f : ℝ → ℂ} (hf : Continuous f)
    {C N : ℝ} (hbound : ∀ y, ‖f y‖ ≤ C * (1 + ‖y‖) ^ (-N))
    (j : ℕ) (hj : (j : ℝ) < N - 1) :
    Integrable (fun y : ℝ ↦ y ^ j • f y) := by
  have hmodel : Integrable (fun y : ℝ ↦ (1 + ‖y‖) ^ (-(N - (j : ℝ)))) :=
    integrable_one_add_norm (by simpa using (show 1 < N - (j : ℝ) by linarith))
  apply (hmodel.const_mul C).mono' (by fun_prop)
  filter_upwards with y
  rw [norm_smul]
  calc
    ‖y ^ j‖ * ‖f y‖ ≤ (1 + ‖y‖) ^ j * (C * (1 + ‖y‖) ^ (-N)) := by
      rw [norm_pow]
      gcongr
      · exact le_add_of_nonneg_left zero_le_one
      · exact hbound y
    _ = C * (1 + ‖y‖) ^ (-(N - (j : ℝ))) := by
      rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add (by positivity)]
      congr 2
      ring

/-- The inverse Mellin integral agrees on either side of a closed strip when the
vertical traces are integrable and have uniform power decay with exponent at least one. -/
theorem mellinInv_eq_of_verticalTrace_decay {F : ℂ → ℂ} {c d C N : ℝ}
    (hcd : c ≤ d) (hF : DifferentiableOn ℂ F (closedStrip c d))
    (hc : Complex.VerticalIntegrable F c) (hd : Complex.VerticalIntegrable F d)
    (hC : 0 ≤ C) (hN : 1 ≤ N)
    (hdecay : ∀ σ ∈ Icc c d, ∀ y : ℝ, ‖verticalTrace F σ y‖ ≤ C * (1 + ‖y‖) ^ (-N))
    {t : ℝ} (ht : 0 < t) : mellinInv c F t = mellinInv d F t := by
  let P (s : ℂ) := (t : ℂ) ^ (-s)
  let K (s : ℂ) := P s * F s
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hP : Differentiable ℂ P := differentiable_id.neg.const_cpow (.inl ht0)
  have hnorm (σ y : ℝ) : ‖P (verticalPoint σ y)‖ = t ^ (-σ) := by
    simp [P, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hi (σ : ℝ) (h : Complex.VerticalIntegrable F σ) : Complex.VerticalIntegrable K σ := by
    have hcont : Continuous (verticalTrace P σ) := hP.continuous.comp (by fun_prop)
    exact h.bdd_mul hcont.aestronglyMeasurable (Eventually.of_forall fun y ↦ (hnorm σ y).le)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := c) (b := d)).bddAbove_image
    ((Real.continuous_const_rpow ht.ne').comp continuous_neg).continuousOn
  have hh : Tendsto (fun y : ℝ ↦ ∫ x in c..d, K (verticalPoint x y)) atAbsInfty (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards with y
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro σ hσ
      have hσ' := Ioc_subset_Icc_self ((uIoc_of_le hcd) ▸ hσ)
      have hb : t ^ (-σ) ≤ B := hB (mem_image_of_mem _ hσ')
      have hpow : (1 + ‖y‖) ^ (-N) ≤ (1 + ‖y‖)⁻¹ := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le (by simp) (by linarith)
      change ‖P (verticalPoint σ y) * F (verticalPoint σ y)‖ ≤ _
      rw [norm_mul, hnorm, mul_comm (t ^ (-σ))]
      calc
        _ ≤ (C * (1 + ‖y‖) ^ (-N)) * t ^ (-σ) :=
          mul_le_mul_of_nonneg_right (hdecay σ hσ' y) (by positivity)
        _ ≤ (C * (1 + ‖y‖)⁻¹) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) hb (by positivity) (by positivity)
        _ = C * B / (1 + ‖y‖) := by ring
    · have hy : Tendsto (fun y : ℝ ↦ 1 + ‖y‖) atAbsInfty atTop := by
        simpa only [Real.norm_eq_abs] using
          tendsto_atTop_add_const_left atAbsInfty (1 : ℝ) (tendsto_comap :
            Tendsto (abs : ℝ → ℝ) atAbsInfty atTop)
      simpa only [zero_mul] using
        (((tendsto_const_nhds (x := C * B)).div_atTop hy).mul_const |d - c|)
  have heq := verticalIntegral_eq_of_contour_shift hcd (hP.differentiableOn.mul hF)
    (hi c hc) (hi d hd) hh
  unfold verticalLineIntegral at heq
  exact congrArg ((1 / (2 * Real.pi)) • ·) (mul_left_cancel₀ Complex.I_ne_zero heq).symm

/-- In logarithmic coordinates the normalized inverse Mellin integral is the
Fourier transform of the appropriately rescaled vertical trace. -/
private theorem mellinInv_exp_eq_fourier (F : ℂ → ℂ) (σ x : ℝ) :
    mellinInv σ F (Real.exp x) =
      logWeight (-σ) x * 𝓕 (fun y : ℝ ↦ verticalTrace F σ (2 * Real.pi * y)) x := by
  rw [mellinInv_eq_fourierInv _ _ (Real.exp_pos x), Real.log_exp, Real.fourierInv_eq_fourier_neg,
    neg_neg, smul_eq_mul, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    mul_comm (x : ℂ) (-(σ : ℂ))]

-- TODO(paper-gap): In the proof of Proposition B.2.1.8, the integrals in dτ
-- need the factor 1/(2π). The boundary term of (B.2.1.22) uses f, since it
-- comes from integrating the derivative of f(s)t⁻ˢ.

/-- Paper: Proposition B.2.1.8, p. 597. Polynomial decay of a holomorphic
function on closed interior strips gives a Mellin inverse with the stated differentiability,
vanishing and square-integrability properties.
Deviation: Square integrability for dt/t is written in logarithmic coordinates. -/
theorem exists_mellin_of_holomorphicOn_isPolynomialDecay
    (a : ℝ) (b : WithTop ℝ) (ha : 0 < a) (hab : (a : WithTop ℝ) < b)
    (N : ℝ) (hN : 2 < N) (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (stripWithTop a b))
    (hBound : ∀ c d : ℝ, a < c → c ≤ d → (d : WithTop ℝ) < b →
      BddAbove ((fun s : ℂ ↦ ‖s‖ ^ N * ‖F s‖) '' closedStrip c d))
    (m : ℕ) (hm : (m : ℝ) < N - 1) :
    ∃ φ : ℝ → ℂ, ContDiffOn ℝ (m : ℕ∞) φ (Ioi 0) ∧
      (∀ σ : ℝ, a < σ → (σ : WithTop ℝ) < b →
        MemLogContDiffZero m (fun x : ℝ ↦ logWeight σ x * φ (Real.exp x)) ∧
        MemLp (fun x : ℝ ↦ logWeight σ x * φ (Real.exp x)) 2 volume) ∧
      ∀ s ∈ stripWithTop a b, HasMellin φ s (F s) := by
  let trace (σ : ℝ) := fun y : ℝ ↦ verticalTrace F σ (2 * Real.pi * y)
  let g (σ : ℝ) : ℝ → ℂ := 𝓕 (trace σ)
  have between {σ : ℝ} (hσ : (σ : WithTop ℝ) < b) :
      ∃ d : ℝ, σ < d ∧ (d : WithTop ℝ) < b := by
    obtain ⟨d, hd₁, hd₂⟩ := exists_between hσ
    lift d to ℝ using ne_of_lt (hd₂.trans_le le_top)
    exact ⟨d, WithTop.coe_lt_coe.mp hd₁, hd₂⟩
  obtain ⟨σ₀, hσ₀a, hσ₀b⟩ := between hab
  have hcont (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      Continuous (verticalTrace F σ) :=
    hF.continuousOn.comp_continuous (by fun_prop) fun y ↦ by simpa using And.intro hσa hσb
  have hverticalMoment (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b)
      (j : ℕ) (hj : (j : ℝ) < N - 1) : Integrable (fun y : ℝ ↦ y ^ j • verticalTrace F σ y) := by
    obtain ⟨C, _, hdecay⟩ := verticalTrace_polynomialDecay (ha.trans hσa)
      (by linarith : 0 ≤ N) (hBound σ σ hσa le_rfl hσb)
    exact integrable_verticalTrace_moment (hcont σ hσa hσb) (hdecay σ ⟨le_rfl, le_rfl⟩) j hj
  have hline (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      Complex.VerticalIntegrable F σ := by
    simpa [Complex.VerticalIntegrable] using hverticalMoment σ hσa hσb 0 (by simp; linarith)
  have hmoment (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) (j : ℕ) (hj : j ≤ m) :
      Integrable (fun y : ℝ ↦ y ^ j • trace σ y) := by
    have hscale : 2 * Real.pi ≠ 0 := by positivity
    have hi := hverticalMoment σ hσa hσb j ((Nat.cast_le.mpr hj).trans_lt hm)
    convert (hi.comp_mul_left' hscale).smul ((2 * Real.pi)⁻¹ ^ j) using 1
    funext y
    simp only [trace, Pi.smul_apply, smul_smul, ← mul_pow, ← mul_assoc,
      inv_mul_cancel₀ hscale, one_mul]
  have hsmooth (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      MemLogContDiffZero m (g σ) := by
    have hmom (j : ℕ) (hj : (j : ℕ∞) ≤ m) := hmoment σ hσa hσb j (by exact_mod_cast hj)
    refine ⟨Real.contDiff_fourier (fun j hj ↦ ?_), fun j hj ↦ ?_⟩
    · simpa only [norm_smul, norm_pow] using (hmom j hj).norm
    · change Tendsto (iteratedDeriv j (𝓕 (trace σ))) _ _
      rw [Real.iteratedDeriv_fourier (N := (m : ℕ∞)) hmom (by exact_mod_cast hj)]
      exact Real.zero_at_infty_fourier _
  have hordered (c d : ℝ) (hca : a < c) (hcd : c ≤ d) (hdb : (d : WithTop ℝ) < b)
      {t : ℝ} (ht : 0 < t) : mellinInv c F t = mellinInv d F t := by
    have hcb : (c : WithTop ℝ) < b := (WithTop.coe_le_coe.mpr hcd).trans_lt hdb
    obtain ⟨C, hC, hdecay⟩ := verticalTrace_polynomialDecay (ha.trans hca)
      (by linarith : 0 ≤ N) (hBound c d hca hcd hdb)
    refine mellinInv_eq_of_verticalTrace_decay hcd (hF.mono ?_) (hline c hca hcb)
      (hline d (hca.trans_le hcd) hdb) hC (by linarith) hdecay ht
    intro z hz
    exact ⟨hca.trans_le hz.1, (WithTop.coe_le_coe.mpr hz.2).trans_lt hdb⟩
  let p (x : ℝ) := logWeight (-σ₀) x * g σ₀ x
  have hp : ContDiff ℝ (m : ℕ∞) p := by
    have hw : ContDiff ℝ (m : ℕ∞) (logWeight (-σ₀)) :=
      Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ (m : ℕ∞)
        (fun x : ℝ ↦ Real.exp (-σ₀ * x)))
    exact hw.mul (hsmooth σ₀ hσ₀a hσ₀b).1
  have hweight (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) :
      (fun x ↦ logWeight σ x * p x) = g σ := by
    funext x
    have hshift : mellinInv σ₀ F (Real.exp x) = mellinInv σ F (Real.exp x) := by
      rcases le_total σ₀ σ with h | h
      · exact hordered σ₀ σ hσ₀a h hσb (Real.exp_pos x)
      · exact (hordered σ σ₀ hσa h hσ₀b (Real.exp_pos x)).symm
    rw [mellinInv_exp_eq_fourier, mellinInv_exp_eq_fourier] at hshift
    change logWeight σ x * p x = g σ x
    rw [show p x = logWeight (-σ) x * g σ x from hshift, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add]
    simp
  have htransition (σ τ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b)
      (hτa : a < τ) (hτb : (τ : WithTop ℝ) < b) (x : ℝ) :
      g σ x = logWeight (σ - τ) x * g τ x := by
    have he : logWeight σ x = logWeight (σ - τ) x * logWeight τ x := by
      change (Real.exp (σ * x) : ℂ) = (Real.exp ((σ - τ) * x) : ℂ) * (Real.exp (τ * x) : ℂ)
      rw [← Complex.ofReal_mul, ← Real.exp_add, sub_mul, sub_add_cancel]
    calc
      g σ x = logWeight σ x * p x := (congrFun (hweight σ hσa hσb) x).symm
      _ = (logWeight (σ - τ) x * logWeight τ x) * p x := congrArg (· * p x) he
      _ = logWeight (σ - τ) x * (logWeight τ x * p x) := mul_assoc _ _ _
      _ = _ := congrArg (logWeight (σ - τ) x * ·) (congrFun (hweight τ hτa hτb) x)
  let K (σ : ℝ) := ∫ y, ‖trace σ y‖
  have hK (σ : ℝ) (x : ℝ) : ‖g σ x‖ ≤ K σ := Real.norm_fourier_le_integral_norm _ _
  -- Shifting left for negative log coordinates and right for positive ones gives integrable tails.
  have hgInt (σ : ℝ) (hσa : a < σ) (hσb : (σ : WithTop ℝ) < b) : Integrable (g σ) := by
    obtain ⟨c, hca, hcσ⟩ := exists_between hσa
    obtain ⟨d, hσd, hdb⟩ := between hσb
    have hcb : (c : WithTop ℝ) < b := (WithTop.coe_lt_coe.mpr hcσ).trans hσb
    have hda := hσa.trans hσd
    have hmeas : AEStronglyMeasurable (g σ) volume :=
      (hsmooth σ hσa hσb).1.continuous.aestronglyMeasurable
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    constructor
    · apply ((integrableOn_exp_mul_Iic (sub_pos.mpr hcσ) 0).const_mul (K c)).mono'
        hmeas.restrict
      filter_upwards with x
      rw [htransition σ c hσa hσb hca hcb x, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      exact mul_le_mul_of_nonneg_right (hK c x) (Real.exp_pos _).le
    · apply ((integrableOn_exp_mul_Ioi (sub_neg.mpr hσd) 0).const_mul (K d)).mono'
        hmeas.restrict
      filter_upwards with x
      rw [htransition σ d hσa hσb hda hdb x, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      exact mul_le_mul_of_nonneg_right (hK d x) (Real.exp_pos _).le
  refine ⟨fromLog p, hp.contDiffOn.comp (Real.contDiffOn_log.mono ?_) (mapsTo_univ _ _), ?_, ?_⟩
  · intro x hx
    exact ne_of_gt hx
  · intro σ hσa hσb
    simp only [Real.log_exp, hweight σ hσa hσb]
    refine ⟨hsmooth σ hσa hσb, ?_⟩
    apply (integrable_norm_rpow_iff (hgInt σ hσa hσb).aestronglyMeasurable
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)).mp
    apply ((hgInt σ hσa hσb).norm.const_mul (K σ)).mono' (by fun_prop)
    filter_upwards with x
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _)]
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hK σ x) (norm_nonneg _)
  · intro s hs
    have hi := hgInt s.re hs.1 hs.2
    refine ⟨mellinConvergent_of_integrable_logWeight p s (by rwa [hweight s.re hs.1 hs.2]), ?_⟩
    rw [mellin_eq_fourier]
    have hEq : (fun u : ℝ ↦ Real.exp (-s.re * u) • p (Real.log (Real.exp (-u)))) =
        𝓕⁻ (trace s.re) := by
      funext u
      rw [Real.log_exp, Complex.real_smul, neg_mul, ← mul_neg, Real.fourierInv_eq_fourier_neg]
      exact congrFun (hweight s.re hs.1 hs.2) (-u)
    have hct : Continuous (trace s.re) := (hcont s.re hs.1 hs.2).comp (by fun_prop)
    have hit : Integrable (trace s.re) := by simpa using hmoment s.re hs.1 hs.2 0 (Nat.zero_le m)
    rw [hEq, hct.fourier_fourierInv_eq hit hi]
    change F (verticalPoint s.re (2 * Real.pi * (s.im / (2 * Real.pi)))) = F s
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (show 2 * Real.pi ≠ 0 by positivity)]
    exact congrArg F (Complex.re_add_im s)

/-- Two-sided decay gives Schwartz profiles for weights of either sign. -/
private theorem exponentialDecay_weighted_schwartz (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) (c : ℝ) :
    ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = logWeight c x * f x := by
  by_cases hc : 0 ≤ c
  · exact (forwardSemiExponentialDecay_iff_weighted_schwartz f).mp hf.1 c hc
  obtain ⟨R, hR, _⟩ := exists_schwartzLogReflection
  have hr : ForwardSemiExponentialDecay (R f) :=
    (backwardSemiExponentialDecay_iff_forward_reflected (R f) f
      (fun x ↦ by rw [hR, neg_neg])).mp hf.2
  obtain ⟨g, hg⟩ := (forwardSemiExponentialDecay_iff_weighted_schwartz (R f)).mp hr (-c) (by linarith)
  exact ⟨R g, fun x ↦ by simp only [hR, hg, neg_neg, neg_mul_neg]⟩

section ExponentialMellin

variable (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)

include hf

/-- Paper: Equation (B.2.1.26), p. 598. The Mellin integral of an
exponentially decaying function converges absolutely at every complex exponent. -/
theorem mellinConvergent_of_exponentialDecay (s : ℂ) :
    MellinConvergent (fromLog f) s := by
  obtain ⟨g, hg⟩ := exponentialDecay_weighted_schwartz f hf s.re
  exact mellinConvergent_of_integrable_logWeight f s
    ((g.integrable (μ := volume)).congr (Eventually.of_forall hg))

/-- Paper: Proposition B.2.1.9(1), p. 598. The Mellin transform of an
exponentially decaying function is entire. -/
theorem differentiable_mellin_of_exponentialDecay :
    Differentiable ℂ (mellin (fromLog f)) := by
  intro s
  let A : ℝ := |s.re| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine mellin_differentiableAt_of_isBigO_rpow (a := A) (b := -A)
    (fromLog_locallyIntegrable f) (isBigO_fromLog_atTop f hf.1 hA) ?_ ?_ ?_
  · dsimp [A]
    linarith [le_abs_self s.re]
  · apply isBigO_comp_log_rpow_of_isBigO_exp _ Real.tendsto_log_nhdsGT_zero
      self_mem_nhdsWithin
    simpa only [neg_neg, iteratedDeriv_zero] using hf.2 0 A hA
  · dsimp [A]
    linarith [neg_abs_le s.re]

/-- Paper: Proposition B.2.1.9(2), p. 598. The Mellin transform satisfies
every inverse-power height bound uniformly on each bounded closed strip. -/
theorem mellin_heightBound_of_exponentialDecay (a b : ℝ) (hab : a < b) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C > (0 : ℝ), heightBound (mellin (fromLog f)) (Icc a b) N C := by
  -- Weight the profile so that the translated strip lies in the right half-plane.
  let c := a - 1
  obtain ⟨g, hg⟩ := exponentialDecay_weighted_schwartz f hf c
  have hgForward : ForwardSemiExponentialDecay g := by
    apply (forwardSemiExponentialDecay_iff_weighted_schwartz g).mpr
    intro A _
    obtain ⟨k, hk⟩ := exponentialDecay_weighted_schwartz f hf (A + c)
    refine ⟨k, fun x ↦ ?_⟩
    simp only [hk, hg, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_mul]
  obtain ⟨C, hC, hbound⟩ := mellin_heightBound_of_forwardSemiExponentialDecay g hgForward
    (a - c) (b - c) (by dsimp [c]; linarith) (sub_lt_sub_right hab c) N hN
  refine ⟨C, hC, fun σ hσ y hy ↦ ?_⟩
  have hshift : mellin (fromLog g) (verticalPoint (σ - c) y) =
      mellin (fromLog f) (verticalPoint σ y) := by
    rw [mellin_fromLog_eq_integral_cexp, mellin_fromLog_eq_integral_cexp]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [hg, Complex.ofReal_exp, Complex.ofReal_mul]
    rw [mul_comm _ (f x), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [← hshift]
  exact hbound (σ - c) ⟨sub_le_sub_right hσ.1 c, sub_le_sub_right hσ.2 c⟩ y hy

omit hf in
/-- A function on the line with a uniform bound and an inverse-power bound away from zero
satisfies the vertical `Lᵖ` bound of (B.2.1.28): the uniform bound is used where
`|y| < 1 / 2`, a set of measure one, and the inverse-power bound on the rest. -/
private theorem eLpNorm_le_of_bound_of_heightBound {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {p : ℝ} (hp : 1 ≤ p) {N : ℕ} (hN : 1 < N)
    {S C : ℝ} (hS : 0 ≤ S) (hC : 0 ≤ C) (hsup : ∀ y, ‖g y‖ ≤ S)
    (hdecay : ∀ y, y ≠ 0 → ‖g y‖ ≤ C / |y| ^ N) :
    eLpNorm g (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((S ^ p + C ^ p * lpTail p N) ^ (1 / p)) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = p * (N : ℝ) := ⟨_, rfl⟩
  have he2 : 2 ≤ e := by
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    rw [he]
    nlinarith
  have hT : MeasurableSet {y : ℝ | 1 / 2 ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  -- The tail is integrable: it is dominated by a multiple of `(1 + y ^ 2)⁻¹`.
  have htail : Integrable ({y : ℝ | 1 / 2 ≤ |y|}.indicator fun y : ℝ ↦ 1 / |y| ^ e) := by
    refine (integrable_inv_one_add_sq.const_mul ((2 : ℝ) ^ (e + 1))).mono'
      ((measurable_const.div (continuous_abs.measurable.pow_const e)).indicator
        hT).aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
    have hy2 : (0 : ℝ) < 1 + y ^ 2 := by positivity
    by_cases hy : 1 / 2 ≤ |y|
    · have hypos : 0 < |y| := lt_of_lt_of_le (by norm_num) hy
      have hpow : 0 < |y| ^ e := Real.rpow_pos_of_pos hypos e
      have hkey : 1 + y ^ 2 ≤ (2 : ℝ) ^ (e + 1) * |y| ^ e := by
        have h1 : (2 * |y|) ^ (2 : ℝ) ≤ (2 * |y|) ^ e :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) he2
        rw [Real.rpow_two, Real.mul_rpow (by norm_num) (abs_nonneg y)] at h1
        rw [Real.rpow_add (by norm_num), Real.rpow_one, ← sq_abs y]
        nlinarith [mul_le_mul hy hy (by norm_num) (abs_nonneg y)]
      rw [indicator_of_mem (show y ∈ {y : ℝ | 1 / 2 ≤ |y|} from hy),
        Real.norm_of_nonneg (one_div_nonneg.mpr hpow.le), ← div_eq_mul_inv,
        div_le_div_iff₀ hpow hy2, one_mul]
      exact hkey
    · rw [indicator_of_notMem (show y ∉ {y : ℝ | 1 / 2 ≤ |y|} from hy), norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (inv_nonneg.mpr hy2.le)
  have hu : IntegrableOn (fun y : ℝ ↦ 1 / |y| ^ e) {y : ℝ | 1 / 2 ≤ |y|} :=
    (integrable_indicator_iff hT).mp htail
  have hvol : volume {y : ℝ | 1 / 2 ≤ |y|}ᶜ = 1 := by
    have hset : {y : ℝ | 1 / 2 ≤ |y|}ᶜ = Ioo (-(1 / 2)) (1 / 2) := by
      ext y
      simp only [mem_compl_iff, mem_ofPred_eq, not_le, mem_Ioo, abs_lt]
    rw [hset, Real.volume_Ioo]
    norm_num
  have hpt_in (y : ℝ) (hy : y ∈ {y : ℝ | 1 / 2 ≤ |y|}) :
      ‖g y‖ₑ ^ p ≤ ENNReal.ofReal (C ^ p * (1 / |y| ^ e)) := by
    have hypos : 0 < |y| := lt_of_lt_of_le (by norm_num) hy
    have hy0 : y ≠ 0 := abs_pos.mp hypos
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖g y‖ ^ p ≤ (C / |y| ^ N) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) (hdecay y hy0) hp0.le
      _ = C ^ p * (1 / |y| ^ e) := by
          rw [Real.div_rpow hC (pow_nonneg hypos.le _), he, mul_comm p,
            Real.rpow_natCast_mul hypos.le, mul_one_div]
  have hpt_out (y : ℝ) : ‖g y‖ₑ ^ p ≤ ENNReal.ofReal (S ^ p) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) (hsup y) hp0.le)
  have hSp : 0 ≤ S ^ p := Real.rpow_nonneg hS p
  have hCt : 0 ≤ C ^ p * lpTail p N :=
    mul_nonneg (Real.rpow_nonneg hC p) (integral_nonneg fun y ↦
      one_div_nonneg.mpr (Real.rpow_nonneg (abs_nonneg y) _))
  have hlin : ∫⁻ y, ‖g y‖ₑ ^ p ≤ ENNReal.ofReal (S ^ p + C ^ p * lpTail p N) := by
    have h1 : ∫⁻ y in {y : ℝ | 1 / 2 ≤ |y|}, ‖g y‖ₑ ^ p ≤
        ENNReal.ofReal (C ^ p * lpTail p N) := by
      refine (setLIntegral_mono' hT hpt_in).trans_eq ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.const_mul hu _)
        (Eventually.of_forall fun y ↦ mul_nonneg (Real.rpow_nonneg hC p)
          (one_div_nonneg.mpr (Real.rpow_nonneg (abs_nonneg y) _))),
        integral_const_mul, he]
    have h2 : ∫⁻ y in {y : ℝ | 1 / 2 ≤ |y|}ᶜ, ‖g y‖ₑ ^ p ≤ ENNReal.ofReal (S ^ p) := by
      refine (setLIntegral_mono' hT.compl fun y _ ↦ hpt_out y).trans_eq ?_
      rw [setLIntegral_const, hvol, mul_one]
    rw [← lintegral_add_compl _ hT, add_comm (S ^ p), ENNReal.ofReal_add hCt hSp]
    exact add_le_add h1 h2
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
    ENNReal.ofReal_ne_top hg, ENNReal.toReal_ofReal hp0.le,
    ← ENNReal.ofReal_rpow_of_nonneg (add_nonneg hSp hCt) (one_div_nonneg.mpr hp0.le)]
  exact ENNReal.rpow_le_rpow hlin (one_div_nonneg.mpr hp0.le)

omit hf in
/-- Two-sided exponential decay makes every symmetric exponential weight integrable. -/
private theorem integrable_exp_mul_abs_mul_norm_of_exponentialDecay (g : 𝓢(ℝ, ℂ))
    (hg : ExponentialDecay g) (c : ℝ) :
    Integrable fun x : ℝ ↦ Real.exp (c * |x|) * ‖g x‖ := by
  obtain ⟨G₁, hG₁⟩ := exponentialDecay_weighted_schwartz g hg c
  obtain ⟨G₂, hG₂⟩ := exponentialDecay_weighted_schwartz g hg (-c)
  refine ((G₁.integrable (μ := volume)).norm.add (G₂.integrable (μ := volume)).norm).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      g.continuous.norm).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  have e1 : ‖G₁ x‖ = Real.exp (c * x) * ‖g x‖ := by
    rw [hG₁, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have e2 : ‖G₂ x‖ = Real.exp (-c * x) * ‖g x‖ := by
    rw [hG₂, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  change ‖Real.exp (c * |x|) * ‖g x‖‖ ≤ ‖G₁ x‖ + ‖G₂ x‖
  rw [e1, e2, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)), ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩
  · rw [hx]
    linarith [Real.exp_pos (-c * x)]
  · rw [hx, mul_neg, ← neg_mul]
    linarith [Real.exp_pos (c * x)]

/-- Paper: Proposition B.2.1.9(3), p. 599. On a closed strip, the vertical
Lᵖ norms satisfy the bound with the exponentially weighted L¹ term.
Deviation: The L¹ term uses the logarithmic coordinate, and the constant from
part (2) is supplied with its bound. -/
theorem mellin_verticalLp_of_exponentialDecay
    (a b : ℝ) (hab : a < b) (p : ℝ) (hp : 1 ≤ p)
    (N : ℕ) (hN : 1 < N) (C : ℝ) (hC : heightBound (mellin (fromLog f)) (Icc a b) N C) :
    ∀ σ ∈ Icc a b,
      eLpNorm (verticalTrace (mellin (fromLog f)) σ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal
          (((∫ x : ℝ, Real.exp ((max |a| |b| + (N : ℝ)) * |x|) * ‖f x‖) ^ p +
            C ^ p * lpTail p N) ^ (1 / p)) := by
  intro σ hσ
  have hC0 : 0 ≤ C := by
    have h := hC σ hσ 1 one_ne_zero
    rw [abs_one, one_pow, div_one] at h
    exact (norm_nonneg _).trans h
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max |a| |b| + (N : ℝ) := ⟨_, rfl⟩
  have hInt : Integrable (fun x : ℝ ↦ Real.exp (c * |x|) * ‖f x‖) :=
    integrable_exp_mul_abs_mul_norm_of_exponentialDecay f hf c
  -- The Mellin integral is bounded by the weighted `L¹` norm at every height.
  have hsup (y : ℝ) : ‖mellin (fromLog f) ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      ∫ x : ℝ, Real.exp (c * |x|) * ‖f x‖ := by
    rw [mellin_fromLog_eq_integral_exp]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun x ↦ norm_nonneg _) hInt (Eventually.of_forall fun x ↦ ?_))
    change ‖Complex.exp (((σ : ℂ) + (y : ℂ) * Complex.I) * (x : ℂ)) * f x‖ ≤
      Real.exp (c * |x|) * ‖f x‖
    have h1 : (((σ : ℂ) + (y : ℂ) * Complex.I) * (x : ℂ)).re = σ * x := by simp
    rw [norm_mul, Complex.norm_exp, h1]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hσM : |σ| ≤ max |a| |b| := abs_le_max_abs_abs hσ.1 hσ.2
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc σ * x ≤ |σ * x| := le_abs_self _
      _ = |σ| * |x| := abs_mul σ x
      _ ≤ c * |x| := by
          rw [hc]
          exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg x)
  have hline : Continuous (fun y : ℝ ↦ (σ : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
  have hres := eLpNorm_le_of_bound_of_heightBound
    (g := fun y : ℝ ↦ mellin (fromLog f) ((σ : ℂ) + (y : ℂ) * Complex.I))
    ((differentiable_mellin_of_exponentialDecay f hf).continuous.comp
      hline).aestronglyMeasurable hp hN
    (integral_nonneg fun x ↦ mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hC0 hsup
    (hC σ hσ)
  rw [hc] at hres
  exact hres

omit hf in
/-- The exponential twist of an exponentially decaying profile is integrable at every
complex exponent. -/
private theorem integrable_cexp_mul_of_exponentialDecay (g : 𝓢(ℝ, ℂ)) (hg : ExponentialDecay g)
    (s : ℂ) : Integrable fun x : ℝ ↦ Complex.exp (s * x) * g x := by
  obtain ⟨G, hG⟩ := exponentialDecay_weighted_schwartz g hg s.re
  refine (G.integrable (μ := volume)).mono
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      g.continuous).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  have hexp : ‖Complex.exp (s * x)‖ = Real.exp (s.re * x) := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  rw [hG, norm_mul, norm_mul, hexp, Complex.norm_of_nonneg (Real.exp_pos _).le]

omit hf in
/-- One integration by parts against the exponential at an arbitrary complex exponent. Two-sided
decay makes both boundary terms vanish. -/
private theorem integral_cexp_mul_derivCLM_of_exponentialDecay (g : 𝓢(ℝ, ℂ))
    (hg : ExponentialDecay g) (s : ℂ) :
    ∫ x : ℝ, Complex.exp (s * x) * SchwartzMap.derivCLM ℂ ℂ g x =
      -s * ∫ x : ℝ, Complex.exp (s * x) * g x := by
  let u := fun x : ℝ ↦ Complex.exp (s * x)
  let u' := fun x : ℝ ↦ s * Complex.exp (s * x)
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    have hlin : HasDerivAt (fun t : ℝ ↦ s * ↑t) s x := by
      simpa [mul_one] using ((hasDerivAt_id x).ofReal_comp.const_mul s)
    simpa [u, u', mul_comm] using hlin.cexp
  have hv (x : ℝ) : HasDerivAt (g : ℝ → ℂ) (SchwartzMap.derivCLM ℂ ℂ g x) x := by
    rw [SchwartzMap.derivCLM_apply]
    exact g.differentiableAt.hasDerivAt
  have huv : Integrable (u * (g : ℝ → ℂ)) := integrable_cexp_mul_of_exponentialDecay g hg s
  have huv' : Integrable (u * ⇑(SchwartzMap.derivCLM ℂ ℂ g)) :=
    integrable_cexp_mul_of_exponentialDecay _ (hg.deriv g) s
  have hu'v : Integrable (u' * (g : ℝ → ℂ)) := by
    have hfun : u' * (g : ℝ → ℂ) = fun x ↦ s * (u x * g x) := by
      funext x
      simp only [Pi.mul_apply, u, u']
      ring
    rw [hfun]
    exact huv.const_mul s
  have hparts : ∫ x, u x * SchwartzMap.derivCLM ℂ ℂ g x = -∫ x, u' x * g x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ ↦ hu x) (fun x _ ↦ hv x) huv' hu'v huv
  have hsmul : ∫ x, u' x * g x = s * ∫ x, u x * g x := by
    have hfun : (fun x ↦ u' x * g x) = fun x ↦ s * (u x * g x) := by
      funext x
      simp only [u, u']
      ring
    rw [hfun]
    exact integral_const_mul s fun x ↦ u x * g x
  rw [hsmul] at hparts
  rw [neg_mul]
  exact hparts

omit hf in
/-- Iterating the integration by parts: the `N`th logarithmic derivative is again an
exponentially decaying profile, with no larger support, whose exponential twist integrates to
`(-s) ^ N` times that of the original profile. -/
private theorem exists_derivProfile_of_exponentialDecay (g : 𝓢(ℝ, ℂ))
    (hg : ExponentialDecay g) (N : ℕ) :
    ∃ h : 𝓢(ℝ, ℂ), ExponentialDecay h ∧ tsupport (h : ℝ → ℂ) ⊆ tsupport (g : ℝ → ℂ) ∧
      ∀ s : ℂ, ∫ x : ℝ, Complex.exp (s * x) * h x =
        (-s) ^ N * ∫ x : ℝ, Complex.exp (s * x) * g x := by
  induction N with
  | zero => exact ⟨g, hg, subset_rfl, fun s ↦ by rw [pow_zero, one_mul]⟩
  | succ N ih =>
    obtain ⟨h, hh, hsupp, hint⟩ := ih
    refine ⟨SchwartzMap.derivCLM ℂ ℂ h, hh.deriv h, ?_, fun s ↦ ?_⟩
    · rw [show (⇑(SchwartzMap.derivCLM ℂ ℂ h) : ℝ → ℂ) = _root_.deriv h from
        funext (SchwartzMap.derivCLM_apply ℂ h)]
      exact (tsupport_deriv_subset (f := (h : ℝ → ℂ))).trans hsupp
    · rw [integral_cexp_mul_derivCLM_of_exponentialDecay h hh s, hint s, pow_succ]
      ring

/-- Paper: Proposition B.2.1.9(4), p. 599. Support in t > 1 permits the
choice of one height-decay constant for the whole left half-plane.
Deviation: The cited estimate is (B.2.1.27). The support is tested in x = log t. -/
theorem mellin_heightBound_left_of_exponentialDecay
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Ioi 0) (b : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C > (0 : ℝ), heightBound (mellin (fromLog f)) (Iic b) N C := by
  -- Integrate by parts `N` times: `(-s) ^ N * M(s)` is the twisted integral of the `N`th
  -- logarithmic derivative `h`, which still vanishes on the nonpositive half-line.
  obtain ⟨h, hh, hsupp, hint⟩ := exists_derivProfile_of_exponentialDecay f hf N
  obtain ⟨G, hG⟩ := exponentialDecay_weighted_schwartz h hh (max b 0)
  have hGint : Integrable (fun x : ℝ ↦ ‖G x‖) := (G.integrable (μ := volume)).norm
  refine ⟨(∫ x : ℝ, ‖G x‖) + 1,
    add_pos_of_nonneg_of_pos (integral_nonneg fun _ ↦ norm_nonneg _) one_pos, fun σ hσ y hy ↦ ?_⟩
  have hσb : σ ≤ b := hσ
  set s : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I with hs
  have hre : s.re = σ := by simp [s]
  have him : s.im = y := by simp [s]
  -- On the support, `x > 0` and `σ ≤ b`, so the weight `exp (σ x)` is at most `exp (max b 0 * x)`.
  have hpoint (x : ℝ) : ‖Complex.exp (s * x) * h x‖ ≤ ‖G x‖ := by
    by_cases hx : 0 < x
    · have hexp : ‖Complex.exp (s * x)‖ = Real.exp (σ * x) := by
        rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
          sub_zero, hre]
      rw [hG, norm_mul, norm_mul, hexp, Complex.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (hσb.trans (le_max_left b 0)) hx.le)) (norm_nonneg _)
    · have hx0 : h x = 0 :=
        image_eq_zero_of_notMem_tsupport fun hmem ↦ hx (hSupport (hsupp hmem))
      rw [hx0, mul_zero, norm_zero]
      exact norm_nonneg _
  have hbound : ‖∫ x : ℝ, Complex.exp (s * x) * h x‖ ≤ ∫ x : ℝ, ‖G x‖ :=
    norm_integral_le_of_norm_le hGint (Eventually.of_forall hpoint)
  rw [hint s, ← mellin_fromLog_eq_integral_exp, norm_mul, norm_pow, norm_neg] at hbound
  have hy0 : 0 < |y| ^ N := pow_pos (abs_pos.mpr hy) N
  have hys : |y| ^ N ≤ ‖s‖ ^ N :=
    pow_le_pow_left₀ (abs_nonneg y) (him ▸ Complex.abs_im_le_norm s) N
  rw [le_div_iff₀ hy0]
  calc ‖mellin (fromLog f) s‖ * |y| ^ N
      ≤ ‖mellin (fromLog f) s‖ * ‖s‖ ^ N := mul_le_mul_of_nonneg_left hys (norm_nonneg _)
    _ = ‖s‖ ^ N * ‖mellin (fromLog f) s‖ := mul_comm _ _
    _ ≤ ∫ x : ℝ, ‖G x‖ := hbound
    _ ≤ (∫ x : ℝ, ‖G x‖) + 1 := le_add_of_nonneg_right zero_le_one

/-- Paper: Proposition B.2.1.9(4), p. 599. If the function is supported in
t > 1, its Mellin transform belongs to each left half-plane Hardy class with p ≥ 1. -/
theorem memLeftHardy_mellin_of_exponentialDecay
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Ioi 0) (b p : ℝ) (hp : 1 ≤ p) :
    MemLeftHardy (mellin (fromLog f)) b p := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hcont : Continuous (mellin (fromLog f)) :=
    (differentiable_mellin_of_exponentialDecay f hf).continuous
  refine ⟨hp0, (differentiable_mellin_of_exponentialDecay f hf).differentiableOn, ?_⟩
  -- A bound at every height: on the support the weight `exp (b x)` dominates `exp (σ x)`.
  have hInt : Integrable (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x) * f x) :=
    integrable_cexp_mul_of_exponentialDecay f hf b
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∫ x : ℝ, ‖Complex.exp ((b : ℂ) * x) * f x‖ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact integral_nonneg fun x ↦ norm_nonneg _
  have hsup (σ : ℝ) (hσ : σ ≤ b) (y : ℝ) :
      ‖mellin (fromLog f) ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K := by
    rw [mellin_fromLog_eq_integral_exp, hK]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun x ↦ norm_nonneg _) hInt.norm (Eventually.of_forall fun x ↦ ?_))
    change ‖Complex.exp (((σ : ℂ) + (y : ℂ) * Complex.I) * (x : ℂ)) * f x‖ ≤
      ‖Complex.exp ((b : ℂ) * (x : ℂ)) * f x‖
    have h1 : (((σ : ℂ) + (y : ℂ) * Complex.I) * (x : ℂ)).re = σ * x := by simp
    have h2 : ((b : ℂ) * (x : ℂ)).re = b * x := by simp
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, h1, h2]
    by_cases hx : f x = 0
    · rw [hx, norm_zero, mul_zero, mul_zero]
    · have hxpos : 0 < x := hSupport (subset_tsupport _ hx)
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσ hxpos.le)) (norm_nonneg _)
  -- Together with the inverse-square height bound this gives one integrable majorant.
  obtain ⟨C, hC, hBound⟩ :=
    mellin_heightBound_left_of_exponentialDecay f hf hSupport b 2 one_le_two
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * K + 2 * C := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    rw [hD]
    linarith
  have hpt (σ : ℝ) (hσ : σ ≤ b) (y : ℝ) :
      ‖mellin (fromLog f) ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ D * (1 + y ^ 2)⁻¹ := by
    have hy2 : (0 : ℝ) < 1 + y ^ 2 := by positivity
    obtain ⟨N, hN⟩ :
        ∃ N : ℝ, N = ‖mellin (fromLog f) ((σ : ℂ) + (y : ℂ) * Complex.I)‖ := ⟨_, rfl⟩
    have hN0 : 0 ≤ N := by
      rw [hN]
      exact norm_nonneg _
    rw [← hN, ← div_eq_mul_inv, le_div_iff₀ hy2, hD]
    by_cases hy : |y| ≤ 1
    · have h1 : y ^ 2 ≤ 1 := by
        rw [← sq_abs]
        exact pow_le_one₀ (abs_nonneg y) hy
      have h2 : N ≤ K := by
        rw [hN]
        exact hsup σ hσ y
      nlinarith [mul_nonneg hN0 (sub_nonneg.mpr h1)]
    · have hy1 : 1 < |y| := not_le.mp hy
      have hy0 : y ≠ 0 := by
        intro h
        rw [h, abs_zero] at hy1
        linarith
      have h1 : 1 ≤ y ^ 2 := by
        rw [← sq_abs]
        exact one_le_pow₀ hy1.le
      have hysq : (0 : ℝ) < y ^ 2 := by positivity
      have h2 : N * y ^ 2 ≤ C := by
        have h := hBound σ hσ y hy0
        rw [sq_abs] at h
        rw [hN]
        exact (le_div_iff₀ hysq).mp h
      nlinarith [mul_nonneg hN0 (sub_nonneg.mpr h1)]
  -- The majorant lies in every `Lᵖ` with `p ≥ 1`, since it is at most `D ^ p / (1 + y ^ 2)`.
  have hGcont : Continuous (fun y : ℝ ↦ D * (1 + y ^ 2)⁻¹) :=
    continuous_const.mul ((continuous_const.add (continuous_pow 2)).inv₀
      fun y ↦ (by positivity : (0 : ℝ) < 1 + y ^ 2).ne')
  have hGmem : MemLp (fun y : ℝ ↦ D * (1 + y ^ 2)⁻¹) (ENNReal.ofReal p) volume := by
    refine (integrable_norm_rpow_iff hGcont.aestronglyMeasurable
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top).mp ?_
    rw [ENNReal.toReal_ofReal hp0.le]
    refine (integrable_inv_one_add_sq.const_mul (D ^ p)).mono'
      (hGcont.norm.rpow_const fun y ↦ Or.inr hp0.le).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    have hy2 : (0 : ℝ) < 1 + y ^ 2 := by positivity
    have hinv0 : 0 ≤ (1 + y ^ 2)⁻¹ := inv_nonneg.mpr hy2.le
    have hinv1 : (1 + y ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [sq_nonneg y])
    change ‖‖D * (1 + y ^ 2)⁻¹‖ ^ p‖ ≤ D ^ p * (1 + y ^ 2)⁻¹
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Real.norm_of_nonneg (mul_nonneg hD0.le hinv0), Real.mul_rpow hD0.le hinv0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_le_one hinv0 hinv1 hp)
      (Real.rpow_nonneg hD0.le _)
  refine ⟨(eLpNorm (fun y : ℝ ↦ D * (1 + y ^ 2)⁻¹) (ENNReal.ofReal p) volume).toNNReal,
    fun σ hσ ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hGmem.eLpNorm_ne_top]
  have hline : Continuous (fun y : ℝ ↦ (σ : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
  exact eLpNorm_mono_real (hcont.comp hline).aestronglyMeasurable fun y ↦ hpt σ hσ.le y

local notation "shiftedMellin" =>
  (fun (n : ℕ) (δ : ℝ) (s : ℂ) ↦ mellin (fromLog f) ((n : ℂ) + (δ : ℂ) * s))

variable (n : ℕ) (δ : ℝ) (hδ : δ = 1 ∨ δ = -1)

include hδ

/-- Paper: Corollary B.2.1.10(1), p. 600. The two shifts of the Mellin
variable, with and without reflection, give entire functions. -/
theorem differentiable_shiftedMellin_of_exponentialDecay :
    Differentiable ℂ (shiftedMellin n δ) := by
  have h : Differentiable ℂ (fun s : ℂ ↦ (n : ℂ) + (δ : ℂ) * s) := by fun_prop
  exact (differentiable_mellin_of_exponentialDecay f hf).comp h

/-- Paper: Corollary B.2.1.10(1), p. 600. Both shifted transforms are
bounded on each vertical strip of bounded width. -/
theorem bddAbove_norm_shiftedMellin_of_exponentialDecay (a b : ℝ) (hab : a < b) :
    BddAbove ((fun s : ℂ ↦ ‖shiftedMellin n δ s‖) '' closedStrip a b) := by
  have hcont : Continuous (mellin (fromLog f)) :=
    (differentiable_mellin_of_exponentialDecay f hf).continuous
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max |a| |b| := ⟨_, rfl⟩
  have hM0 : 0 < M := by
    rw [hM, lt_max_iff, abs_pos, abs_pos]
    by_contra h
    rw [not_or, not_not, not_not] at h
    rw [h.1, h.2] at hab
    exact lt_irrefl _ hab
  -- Away from the real axis the height bound applies; near it the strip is compact.
  obtain ⟨C, hC, hBound⟩ := mellin_heightBound_of_exponentialDecay f hf
    ((n : ℝ) - M) ((n : ℝ) + M) (by linarith) 1 le_rfl
  obtain ⟨D, hD⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_bound_of_continuousOn
    (s := Complex.reProdIm (Icc ((n : ℝ) - M) ((n : ℝ) + M)) (Icc (-1 : ℝ) 1))
    hcont.continuousOn
  refine ⟨max C D, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  change ‖mellin (fromLog f) ((n : ℂ) + (δ : ℂ) * s)‖ ≤ max C D
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (n : ℂ) + (δ : ℂ) * s := ⟨_, rfl⟩
  rw [← hw]
  have hsre : |s.re| ≤ M := by
    rw [hM]
    exact abs_le_max_abs_abs hs.1 hs.2
  have hδs : |δ * s.re| ≤ M := by
    rcases hδ with rfl | rfl <;> simpa using hsre
  have hwre : w.re = (n : ℝ) + δ * s.re := by
    rw [hw]
    simp
  have hre : w.re ∈ Icc ((n : ℝ) - M) ((n : ℝ) + M) := by
    rw [hwre]
    have h := abs_le.mp hδs
    constructor <;> linarith
  by_cases him : |w.im| ≤ 1
  · exact (hD w (Complex.mem_reProdIm.mpr ⟨hre, abs_le.mp him⟩)).trans (le_max_right _ _)
  · have him' : 1 < |w.im| := not_le.mp him
    have hne : w.im ≠ 0 := by
      intro h
      rw [h, abs_zero] at him'
      linarith
    have h : ‖mellin (fromLog f) w‖ ≤ C / |w.im| ^ 1 := by
      simpa only [Complex.re_add_im] using hBound w.re hre w.im hne
    rw [pow_one] at h
    exact (h.trans (div_le_self hC.le him'.le)).trans (le_max_left _ _)

omit hδ hf in
/-- Two-sided exponential decay makes every tilted symmetric exponential weight integrable. -/
private theorem integrable_exp_add_mul_abs_mul_norm_of_exponentialDecay (g : 𝓢(ℝ, ℂ))
    (hg : ExponentialDecay g) (d c : ℝ) :
    Integrable fun x : ℝ ↦ Real.exp (d * x + c * |x|) * ‖g x‖ := by
  obtain ⟨G₁, hG₁⟩ := exponentialDecay_weighted_schwartz g hg (d + c)
  obtain ⟨G₂, hG₂⟩ := exponentialDecay_weighted_schwartz g hg (d - c)
  refine ((G₁.integrable (μ := volume)).norm.add (G₂.integrable (μ := volume)).norm).mono'
    ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).add
      (continuous_const.mul continuous_abs))).mul g.continuous.norm).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  have e1 : ‖G₁ x‖ = Real.exp ((d + c) * x) * ‖g x‖ := by
    rw [hG₁, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have e2 : ‖G₂ x‖ = Real.exp ((d - c) * x) * ‖g x‖ := by
    rw [hG₂, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  change ‖Real.exp (d * x + c * |x|) * ‖g x‖‖ ≤ ‖G₁ x‖ + ‖G₂ x‖
  rw [e1, e2, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)), ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩
  · rw [hx, show d * x + c * x = (d + c) * x by ring]
    linarith [Real.exp_pos ((d - c) * x)]
  · rw [hx, show d * x + c * -x = (d - c) * x by ring]
    linarith [Real.exp_pos ((d + c) * x)]

/-- Paper: Corollary B.2.1.10(1), p. 600. The inequality (B.2.1.28)
applies to both shifts with the weighted, possibly reflected input.
Deviation: The sign encodes both shifts. The L¹ term uses the logarithmic
profile exp(nδx) f(δx) of the shifted transform. -/
theorem shiftedMellin_verticalLp_of_exponentialDecay
    (a b : ℝ) (hab : a < b) (N : ℕ) (hN : 1 < N) :
    ∃ C > (0 : ℝ), heightBound (shiftedMellin n δ) (Icc a b) N C ∧
      ∀ p : ℝ, 1 ≤ p → ∀ σ ∈ Icc a b,
        eLpNorm (verticalTrace (shiftedMellin n δ) σ) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal
            (((∫ x : ℝ, Real.exp (((n : ℝ) * δ) * x + (max |a| |b| + (N : ℝ)) * |x|) *
                  ‖f (δ * x)‖) ^ p + C ^ p * lpTail p N) ^ (1 / p)) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max |a| |b| := ⟨_, rfl⟩
  have hM0 : 0 < M := by
    rw [hM, lt_max_iff, abs_pos, abs_pos]
    by_contra h
    rw [not_or, not_not, not_not] at h
    rw [h.1, h.2] at hab
    exact lt_irrefl _ hab
  obtain ⟨C, hC, hBound⟩ := mellin_heightBound_of_exponentialDecay f hf
    ((n : ℝ) - M) ((n : ℝ) + M) (by linarith) N (by omega)
  have hpt (σ y : ℝ) : (n : ℂ) + (δ : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I) =
      (((n : ℝ) + δ * σ : ℝ) : ℂ) + ((δ * y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hδσ (σ : ℝ) (hσ : σ ∈ Icc a b) : |δ * σ| ≤ M := by
    have h : |σ| ≤ M := by
      rw [hM]
      exact abs_le_max_abs_abs hσ.1 hσ.2
    rcases hδ with rfl | rfl <;> simpa using h
  have hmem (σ : ℝ) (hσ : σ ∈ Icc a b) :
      (n : ℝ) + δ * σ ∈ Icc ((n : ℝ) - M) ((n : ℝ) + M) := by
    have h := abs_le.mp (hδσ σ hσ)
    constructor <;> linarith
  -- The height of `n + δ s` is `δ y`, of the same absolute value as the height of `s`.
  have hheight : ∀ σ ∈ Icc a b, ∀ y : ℝ, y ≠ 0 →
      ‖mellin (fromLog f) ((n : ℂ) + (δ : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        C / |y| ^ N := by
    intro σ hσ y hy
    have hδy : δ * y ≠ 0 := mul_ne_zero (by rcases hδ with rfl | rfl <;> norm_num) hy
    have habs : |δ * y| = |y| := by rcases hδ with rfl | rfl <;> simp
    rw [hpt, ← habs]
    exact hBound _ (hmem σ hσ) (δ * y) hδy
  refine ⟨C, hC, hheight, fun p hp σ hσ ↦ ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = M + (N : ℝ) := ⟨_, rfl⟩
  have hH : Integrable (fun u : ℝ ↦ Real.exp ((n : ℝ) * u + c * |u|) * ‖f u‖) :=
    integrable_exp_add_mul_abs_mul_norm_of_exponentialDecay f hf n c
  -- The weighted `L¹` term of the statement is the integral of this majorant.
  have hS : (∫ x : ℝ, Real.exp (((n : ℝ) * δ) * x + c * |x|) * ‖f (δ * x)‖) =
      ∫ u : ℝ, Real.exp ((n : ℝ) * u + c * |u|) * ‖f u‖ := by
    rcases hδ with rfl | rfl
    · simp only [mul_one, one_mul]
    · rw [← integral_neg_eq_self (fun u : ℝ ↦ Real.exp ((n : ℝ) * u + c * |u|) * ‖f u‖)]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [mul_neg, mul_one, neg_mul, one_mul, abs_neg]
  have hsup (y : ℝ) :
      ‖mellin (fromLog f) ((n : ℂ) + (δ : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        ∫ u : ℝ, Real.exp ((n : ℝ) * u + c * |u|) * ‖f u‖ := by
    rw [mellin_fromLog_eq_integral_exp]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun x ↦ norm_nonneg _) hH (Eventually.of_forall fun x ↦ ?_))
    change ‖Complex.exp (((n : ℂ) + (δ : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)) * (x : ℂ)) *
      f x‖ ≤ Real.exp ((n : ℝ) * x + c * |x|) * ‖f x‖
    have h1 : (((n : ℂ) + (δ : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)) * (x : ℂ)).re =
        ((n : ℝ) + δ * σ) * x := by
      rw [hpt]
      simp
    rw [norm_mul, Complex.norm_exp, h1]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h2 : δ * σ * x ≤ c * |x| :=
      calc δ * σ * x ≤ |δ * σ * x| := le_abs_self _
        _ = |δ * σ| * |x| := abs_mul _ _
        _ ≤ c * |x| := by
            rw [hc]
            exact mul_le_mul_of_nonneg_right (by linarith [hδσ σ hσ]) (abs_nonneg x)
    rw [add_mul]
    linarith
  have hline : Continuous (fun y : ℝ ↦
      (n : ℂ) + (δ : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
  have hres := eLpNorm_le_of_bound_of_heightBound
    (g := fun y : ℝ ↦ mellin (fromLog f)
      ((n : ℂ) + (δ : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)))
    ((differentiable_mellin_of_exponentialDecay f hf).continuous.comp
      hline).aestronglyMeasurable hp hN
    (integral_nonneg fun x ↦ mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hC.le hsup
    (hheight σ hσ)
  rw [← hS, hc, hM] at hres
  exact hres

/-- Paper: Corollary B.2.1.10(2), p. 600. Multiplying either shifted Mellin
transform by a meromorphic function of polynomial growth gives rapid vertical decay.
Deviation: The proof identifies the intended estimate as (B.2.1.27). -/
theorem mul_shiftedMellin_eventualHeightBound (hn : 1 ≤ n)
    (a b : ℝ) (hab : a < b) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (openStrip a b))
    (hPoles : {s : ℂ | s ∈ openStrip a b ∧ meromorphicOrderAt F s < 0}.Finite)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hGrowth : ∀ᶠ y : ℝ in atAbsInfty, ∀ σ ∈ Ioo a b, ‖F (verticalPoint σ y)‖ ≤ A * |y| ^ B)
    (N : ℕ) (hN : 1 ≤ N) :
    eventualHeightBound (fun s ↦ F s * shiftedMellin n δ s) (Ioo a b) N := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max |a| |b| := ⟨_, rfl⟩
  have hM0 : 0 < M := by
    rw [hM, lt_max_iff, abs_pos, abs_pos]
    by_contra h
    rw [not_or, not_not, not_not] at h
    rw [h.1, h.2] at hab
    exact lt_irrefl _ hab
  -- A height bound of order `N + K` for the Mellin transform absorbs the growth `|y| ^ B`.
  obtain ⟨K, hK⟩ : ∃ K : ℕ, B ≤ K := exists_nat_ge B
  obtain ⟨C, hC, hBound⟩ := mellin_heightBound_of_exponentialDecay f hf
    ((n : ℝ) - M) ((n : ℝ) + M) (by linarith) (N + K) (by omega)
  have hy1 : ∀ᶠ y : ℝ in atAbsInfty, 1 ≤ |y| := tendsto_comap.eventually (eventually_ge_atTop 1)
  refine ⟨A * C, mul_pos hA hC, ?_⟩
  filter_upwards [hGrowth, hy1] with y hFy hy σ hσ
  have hypos : 0 < |y| := zero_lt_one.trans_le hy
  have hy0 : y ≠ 0 := abs_pos.mp hypos
  have hδy : δ * y ≠ 0 := mul_ne_zero (by rcases hδ with rfl | rfl <;> norm_num) hy0
  have habs : |δ * y| = |y| := by rcases hδ with rfl | rfl <;> simp
  have hσM : |δ * σ| ≤ M := by
    have h : |σ| ≤ M := by
      rw [hM]
      exact abs_le_max_abs_abs hσ.1.le hσ.2.le
    rcases hδ with rfl | rfl <;> simpa using h
  have hmem : (n : ℝ) + δ * σ ∈ Icc ((n : ℝ) - M) ((n : ℝ) + M) := by
    have h := abs_le.mp hσM
    constructor <;> linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = ‖F ((σ : ℂ) + (y : ℂ) * Complex.I)‖ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = ‖mellin (fromLog f)
      ((n : ℂ) + (δ : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))‖ := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by
    rw [hw]
    exact norm_nonneg _
  have hpowN : 0 < |y| ^ N := pow_pos hypos _
  have hrpow : |y| ^ B ≤ |y| ^ K := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hy hK
  have hu' : u ≤ A * |y| ^ K := by
    rw [hu]
    exact (hFy σ hσ).trans (mul_le_mul_of_nonneg_left hrpow hA.le)
  have hw' : w * (|y| ^ N * |y| ^ K) ≤ C := by
    have hpt : (n : ℂ) + (δ : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I) =
        (((n : ℝ) + δ * σ : ℝ) : ℂ) + ((δ * y : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have h : w ≤ C / |y| ^ (N + K) := by
      rw [hw, hpt, ← habs]
      exact hBound ((n : ℝ) + δ * σ) hmem (δ * y) hδy
    rw [← pow_add]
    exact (le_div_iff₀ (pow_pos hypos _)).mp h
  change ‖F ((σ : ℂ) + (y : ℂ) * Complex.I) * mellin (fromLog f)
    ((n : ℂ) + (δ : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))‖ ≤ A * C / |y| ^ N
  rw [norm_mul, ← hu, ← hw, le_div_iff₀ hpowN]
  calc u * w * |y| ^ N ≤ A * |y| ^ K * w * |y| ^ N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu' hw0) hpowN.le
    _ = A * (w * (|y| ^ N * |y| ^ K)) := by ring
    _ ≤ A * C := mul_le_mul_of_nonneg_left hw' hA.le

end ExponentialMellin

/-- Paper: Definition B.2.2.1, p. 600. A holomorphic function on an open
strip has uniform rapid decay in height on every closed interior strip. -/
def UniformlySchwartzOnStrip (Φ : ℂ → ℂ) (a b : ℝ) : Prop :=
  a < b ∧ DifferentiableOn ℂ Φ (openStrip a b) ∧
    ∀ ε > (0 : ℝ), a + ε < b - ε → ∀ N : ℕ, 1 ≤ N →
      eventualHeightBound Φ (Icc (a + ε) (b - ε)) N

/-- Paper: Definition B.2.2.1, p. 600. An entire function is Schwartz on
vertical strips if it has uniform rapid decay on every bounded open strip. -/
def SchwartzOnVerticalStrips (Φ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Φ ∧ ∀ a b : ℝ, a < b → UniformlySchwartzOnStrip Φ a b

/-- Paper: Definition B.2.2.1, p. 600. A holomorphic function on a left
half-plane has uniform rapid decay in height on every smaller closed left half-plane. -/
def SchwartzOnLeftHalfPlane (Φ : ℂ → ℂ) (b : ℝ) : Prop :=
  DifferentiableOn ℂ Φ (Complex.re ⁻¹' Iio b) ∧
    ∀ ε > (0 : ℝ), ∀ N : ℕ, 1 ≤ N → eventualHeightBound Φ (Iic (b - ε)) N

/-- Paper: Example B.2.2.2, p. 600. Exponentially decaying functions give
Mellin transforms that are Schwartz on vertical strips. -/
theorem schwartzOnVerticalStrips_mellin_of_exponentialDecay
    (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) :
    SchwartzOnVerticalStrips (mellin (fromLog f)) := by
  refine ⟨differentiable_mellin_of_exponentialDecay f hf, fun a b hab ↦
    ⟨hab, (differentiable_mellin_of_exponentialDecay f hf).differentiableOn,
      fun ε _ hWidth N hN ↦ ?_⟩⟩
  obtain ⟨C, hC, hBound⟩ :=
    mellin_heightBound_of_exponentialDecay f hf (a + ε) (b - ε) hWidth N hN
  have hy : ∀ᶠ y : ℝ in atAbsInfty, 0 < |y| := tendsto_comap.eventually (eventually_gt_atTop 0)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hy] with y hy σ hσ
  exact hBound σ hσ y (abs_pos.mp hy)

/-- Paper: Example B.2.2.2, p. 600. Exponentially decaying functions give
Mellin transforms that are uniformly Schwartz on each prescribed vertical strip. -/
theorem uniformlySchwartzOnStrip_mellin_of_exponentialDecay
    (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) (a b : ℝ) (hab : a < b) :
    UniformlySchwartzOnStrip (mellin (fromLog f)) a b :=
  (schwartzOnVerticalStrips_mellin_of_exponentialDecay f hf).2 a b hab

/-- Paper: Definition B.2.2.1, p. 600. An exponentially decaying function
supported in t > 1 gives a Mellin transform that is Schwartz on each left half-plane.
Deviation: Sanity check using Proposition B.2.1.9(4). -/
theorem schwartzOnLeftHalfPlane_mellin_of_exponentialDecay
    (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Ioi 0) (b : ℝ) :
    SchwartzOnLeftHalfPlane (mellin (fromLog f)) b := by
  refine ⟨(differentiable_mellin_of_exponentialDecay f hf).differentiableOn,
    fun ε _ N hN ↦ ?_⟩
  obtain ⟨C, hC, hBound⟩ :=
    mellin_heightBound_left_of_exponentialDecay f hf hSupport (b - ε) N hN
  have hy : ∀ᶠ y : ℝ in atAbsInfty, 0 < |y| := tendsto_comap.eventually (eventually_gt_atTop 0)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hy] with y hy σ hσ
  exact hBound σ hσ y (abs_pos.mp hy)

/-- The Mellin integral of a logarithmic profile after the substitution `t = exp x`. -/
theorem mellin_logProfile_eq (g : ℝ → ℂ) (s : ℂ) :
    mellin (fromLog g) s = ∫ x : ℝ, Complex.exp (s * x) * g x := by
  rw [mellin, ← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Multiplication by the boundary polynomial preserves the Schwartz class. -/
private theorem weightedBoundaryBound (c : ℝ) (n : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ∃ M : ℝ, ∀ y : ℝ, ‖((c : ℂ) + y * Complex.I) ^ n * g y‖ ≤ M := by
  let W (y : ℝ) := ((c : ℂ) + y * Complex.I) ^ n
  have hW : W.HasTemperateGrowth := by
    dsimp [W]
    fun_prop
  let h := SchwartzMap.smulLeftCLM ℂ W g
  refine ⟨SchwartzMap.seminorm ℂ 0 0 h, fun y ↦ ?_⟩
  simpa only [h, SchwartzMap.smulLeftCLM_apply_apply hW, smul_eq_mul, W] using h.norm_le_seminorm ℂ y

section UniformRiemannLebesgue

variable (f : 𝓢(ℝ, ℂ)) (a b : ℝ) (hab : a < b)
  (hWeighted : ∀ σ ∈ Icc a b, ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = logWeight σ x * f x)

include hab hWeighted

/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin integral converges
absolutely throughout the closed strip of Schwartz weights. -/
theorem mellinConvergent_on_strip_of_weighted_schwartz (s : ℂ) (hs : s ∈ closedStrip a b) :
    MellinConvergent (fromLog f) s := by
  obtain ⟨g, hg⟩ := hWeighted s.re hs
  apply mellinConvergent_of_integrable_logWeight
  exact (g.integrable (μ := volume)).congr (Eventually.of_forall hg)

/-- Paper: Proposition B.2.2.3(1), p. 601. The two endpoint weights give one
integrable majorant for every Mellin integrand in the closed strip. -/
private theorem mellin_logProfile_dominated :
    ∃ B : ℝ → ℝ, Integrable B ∧ ∀ s ∈ closedStrip a b, ∀ x : ℝ,
      ‖Complex.exp (s * x) * f x‖ ≤ B x := by
  obtain ⟨g, hg⟩ := hWeighted a (left_mem_Icc.mpr hab.le)
  obtain ⟨h, hh⟩ := hWeighted b (right_mem_Icc.mpr hab.le)
  refine ⟨fun x ↦ ‖g x‖ + ‖h x‖, (g.integrable (μ := volume)).norm.add
    (h.integrable (μ := volume)).norm, ?_⟩
  intro s hs x
  have hnorm (r : ℝ) : ‖(Real.exp (r * x) : ℂ) * f x‖ = Real.exp (r * x) * ‖f x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖Complex.exp (s * x) * f x‖ ≤ _
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rcases le_total x 0 with hx | hx
  · apply le_add_of_le_of_nonneg _ (norm_nonneg _)
    rw [hg, hnorm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hs.1 hx))
      (norm_nonneg _)
  · apply le_add_of_nonneg_of_le (norm_nonneg _) _
    rw [hh, hnorm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs.2 hx))
      (norm_nonneg _)


/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin transform is continuous
on the closed strip of Schwartz weights. -/
theorem continuousOn_mellin_of_weighted_schwartz :
    ContinuousOn (mellin (fromLog f)) (closedStrip a b) := by
  obtain ⟨B, hB, hbound⟩ := mellin_logProfile_dominated f a b hab hWeighted
  change ContinuousOn (fun s ↦ mellin (fromLog f) s) (closedStrip a b)
  simp_rw [mellin_logProfile_eq]
  apply continuousOn_of_dominated (bound := B)
  · intro s _
    exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      f.continuous).aestronglyMeasurable
  · exact fun s hs ↦ Eventually.of_forall (hbound s hs)
  · exact hB
  · filter_upwards with x
    exact ((Complex.continuous_exp.comp (continuous_id.mul_const (x : ℂ))).mul_const
      (f x)).continuousOn

/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin transform restricts
to a Schwartz function on each vertical line of the closed strip. -/
theorem exists_schwartz_verticalTrace_mellin_of_weighted_schwartz (σ : ℝ) (hσ : σ ∈ Icc a b) :
    ∃ g : 𝓢(ℝ, ℂ), (g : ℝ → ℂ) = verticalTrace (mellin (fromLog f)) σ := by
  obtain ⟨g, hg⟩ := hWeighted σ hσ
  let r := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv g
  let e := (LinearEquiv.smulOfNeZero ℝ ℝ (2 * Real.pi)⁻¹
    (inv_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero))).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (𝓕 r), ?_⟩
  funext y
  change (𝓕 r) ((2 * Real.pi)⁻¹ * y) = mellin (fun t ↦ f (Real.log t)) (σ + y * Complex.I)
  rw [SchwartzMap.fourier_coe, mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add, Real.log_exp,
    div_eq_inv_mul]
  apply congrArg (fun v : ℝ → ℂ ↦ 𝓕 v ((2 * Real.pi)⁻¹ * y))
  funext x
  change g (-x) = _
  simp only [hg, Complex.real_smul, mul_neg, neg_mul]

/-- Paper: Proposition B.2.2.3(1), p. 601. The Mellin transform is holomorphic
in the interior of the strip of Schwartz weights. -/
theorem differentiableOn_mellin_of_weighted_schwartz :
    DifferentiableOn ℂ (mellin (fromLog f)) (openStrip a b) := by
  have hloc : LocallyIntegrableOn (fun t ↦ f (Real.log t)) (Ioi 0) volume :=
    (f.continuous.comp_continuousOn (Real.continuousOn_log.mono
      (fun x hx ↦ ne_of_gt hx))).locallyIntegrableOn measurableSet_Ioi
  have bound {c : ℝ} (hc : c ∈ Icc a b) {l : Filter ℝ} (hl : ∀ᶠ t in l, 0 < t) :
      (fun t ↦ f (Real.log t)) =O[l] (fun t : ℝ ↦ t ^ (-c)) := by
    obtain ⟨g, hg⟩ := hWeighted c hc
    apply Asymptotics.IsBigO.of_bound (SchwartzMap.seminorm ℂ 0 0 g)
    filter_upwards [hl] with t ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), Real.rpow_neg ht.le, ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos ht _), Real.rpow_def_of_pos ht, mul_comm (Real.log t)]
    simpa only [hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      using g.norm_le_seminorm ℂ (Real.log t)
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  exact mellin_differentiableAt_of_isBigO_rpow hloc
    (bound (right_mem_Icc.mpr hab.le) (eventually_gt_atTop 0)) hs.2
    (bound (left_mem_Icc.mpr hab.le) self_mem_nhdsWithin) hs.1

/-- Paper: Proposition B.2.2.3(2), p. 601. The rapid decay bound holds
uniformly across the full closed strip, including the two boundary lines. -/
theorem mellin_eventualHeightBound_of_weighted_schwartz (N : ℕ) (hN : 1 ≤ N) :
    eventualHeightBound (mellin (fromLog f)) (Icc a b) N := by
  let F := mellin (fromLog f)
  have hd : DiffContOnCl ℂ F (Complex.re ⁻¹' Ioo a b) := by
    refine ⟨differentiableOn_mellin_of_weighted_schwartz f a b hab hWeighted, ?_⟩
    rw [Complex.closure_preimage_re, closure_Ioo hab.ne]
    exact continuousOn_mellin_of_weighted_schwartz f a b hab hWeighted
  obtain ⟨B, hB, hbound⟩ := mellin_logProfile_dominated f a b hab hWeighted
  have hM (z : ℂ) (hz : z.re ∈ Icc a b) : ‖F z‖ ≤ ∫ x, B x := by
    rw [show F z = _ from mellin_logProfile_eq f z]
    exact norm_integral_le_of_norm_le hB (Eventually.of_forall (hbound z hz))
  have edge (c : ℝ) (hc : c ∈ Icc a b) : ∃ C : ℝ, ∀ z : ℂ, z.re = c → ‖z ^ N * F z‖ ≤ C := by
    obtain ⟨g, hg⟩ := exists_schwartz_verticalTrace_mellin_of_weighted_schwartz f a b hab hWeighted c hc
    obtain ⟨C, hC⟩ := weightedBoundaryBound c N g
    refine ⟨C, fun z hz ↦ ?_⟩
    have hy : (c : ℂ) + z.im * Complex.I = z := hz ▸ Complex.re_add_im z
    have hg' : g z.im = F ((c : ℂ) + z.im * Complex.I) := congrFun hg z.im
    simpa only [hg', hy] using hC z.im
  obtain ⟨A, hA⟩ := edge a (left_mem_Icc.mpr hab.le)
  obtain ⟨C, hC⟩ := edge b (right_mem_Icc.mpr hab.le)
  let D := max (max A C) 1
  refine ⟨D, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  have hy : ∀ᶠ y : ℝ in atAbsInfty, 0 < |y| := tendsto_comap.eventually (eventually_gt_atTop 0)
  filter_upwards [hy] with y hy σ hσ
  let z : ℂ := (σ : ℂ) + y * Complex.I
  have h := norm_pow_mul_le_on_verticalStrip hab hd hM N
    (fun w hw ↦ (hA w hw).trans (le_max_left A C))
    (fun w hw ↦ (hC w hw).trans (le_max_right A C)) z (by simpa [z] using hσ)
  change ‖F z‖ ≤ D / |y| ^ N
  rw [le_div_iff₀ (pow_pos hy N), mul_comm]
  have him : |y| ≤ ‖z‖ := by simpa [z] using Complex.abs_im_le_norm z
  calc
    |y| ^ N * ‖F z‖ ≤ ‖z‖ ^ N * ‖F z‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) him N) (norm_nonneg _)
    _ = ‖z ^ N * F z‖ := by rw [norm_mul, norm_pow]
    _ ≤ D := h.trans (le_max_left _ _)

end UniformRiemannLebesgue

/-- Paper: Equation (B.2.2.4), p. 601. The normalized line integral is
the inverse Mellin integral evaluated at one.
Deviation: Sanity check for orientation and normalization. -/
theorem verticalLineIntegral_div_eq_mellinInv_one (Φ : ℂ → ℂ) (σ : ℝ)
    (hΦ : Complex.VerticalIntegrable Φ σ) :
    verticalLineIntegral Φ σ / (2 * (Real.pi : ℂ) * Complex.I) = mellinInv σ Φ 1 := by
  unfold verticalLineIntegral mellinInv
  simp only [Complex.ofReal_one, Complex.one_cpow, one_smul]
  rw [Complex.real_smul]
  push_cast
  field_simp

local notation "cauchyKernel" =>
  (fun (Φ : ℂ → ℂ) (N : ℕ) (z s : ℂ) ↦ Φ s / (s - z) ^ (N + 1))
local notation "normalizedCauchyIntegral" =>
  (fun (Φ : ℂ → ℂ) (N : ℕ) (σ : ℝ) (z : ℂ) ↦
    (Nat.factorial N : ℂ) / (2 * (Real.pi : ℂ) * Complex.I) *
      verticalLineIntegral (cauchyKernel Φ N z) σ)

/-- A continuous trace with inverse-square decay at both ends is integrable. -/
private theorem integrable_of_eventual_sq_decay {u : ℝ → ℂ} (hu : Continuous u) {C : ℝ} (hC : 0 < C)
    (h : ∀ᶠ y : ℝ in comap abs atTop, ‖u y‖ ≤ C / |y| ^ 2) : Integrable u := by
  apply hu.locallyIntegrable.integrable_of_isBigO_cocompact _
    (integrable_inv_one_add_sq.integrableAtFilter _)
  apply Asymptotics.IsBigO.of_bound (2 * C)
  have hf : comap (abs : ℝ → ℝ) atTop = cocompact ℝ := by
    rw [show (abs : ℝ → ℝ) = norm from funext fun x ↦ (Real.norm_eq_abs x).symm,
      comap_norm_atTop, Metric.cobounded_eq_cocompact]
  rw [← hf]
  have hlarge : ∀ᶠ y : ℝ in comap abs atTop, 1 ≤ |y| := tendsto_comap.eventually (eventually_ge_atTop 1)
  filter_upwards [h, hlarge] with y hy hy'
  apply hy.trans
  rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, sq_abs]
  have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, sq_nonneg (|y| - 1)]
  apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
  nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hy2)]

/-- Staying away from the real part of the pole gives a bounded Cauchy multiplier. -/
private theorem kernel_integrable_from_trace {Φ : ℂ → ℂ} {σ : ℝ} (h : Complex.VerticalIntegrable Φ σ)
    (N : ℕ) (z : ℂ) (hz : z.re ≠ σ) :
    Complex.VerticalIntegrable (fun s ↦ Φ s / (s - z) ^ (N + 1)) σ := by
  let w (y : ℝ) := (σ : ℂ) + y * Complex.I
  have hw (y : ℝ) : w y - z ≠ 0 := by
    intro h
    have hr := congrArg Complex.re (sub_eq_zero.mp h)
    exact hz (by simpa [w] using hr.symm)
  let K (y : ℝ) := ((w y - z) ^ (N + 1))⁻¹
  have hc : Continuous K := by
    apply Continuous.inv₀ _ fun y ↦ pow_ne_zero _ (hw y)
    dsimp [w]
    fun_prop
  have hbound (y : ℝ) : ‖K y‖ ≤ (|σ - z.re| ^ (N + 1))⁻¹ := by
    have hsep : |σ - z.re| ≤ ‖w y - z‖ := by simpa [w] using Complex.abs_re_le_norm (w y - z)
    rw [show ‖K y‖ = (‖w y - z‖ ^ (N + 1))⁻¹ by simp [K]]
    exact inv_anti₀ (pow_pos (abs_pos.mpr (sub_ne_zero.mpr hz.symm)) _)
      (pow_le_pow_left₀ (abs_nonneg _) hsep _)
  exact (h.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall hbound)).congr
    (Eventually.of_forall fun y ↦ by simp [K, w, div_eq_inv_mul])

/-- Paper: Theorem B.2.2.4(1), p. 602. Every interior vertical trace is
absolutely integrable because it has inverse-square decay at large heights. -/
theorem UniformlySchwartzOnStrip.verticalIntegrable {Φ : ℂ → ℂ} {a b : ℝ} (hΦ : UniformlySchwartzOnStrip Φ a b)
    (σ : ℝ) (hσ : σ ∈ Ioo a b) : Complex.VerticalIntegrable Φ σ := by
  let δ := min (σ - a) (b - σ) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (lt_min (sub_pos.mpr hσ.1) (sub_pos.mpr hσ.2))
  have hleft : a + δ < σ := by dsimp [δ]; linarith [min_le_left (σ - a) (b - σ), hσ.1]
  have hright : σ < b - δ := by dsimp [δ]; linarith [min_le_right (σ - a) (b - σ), hσ.2]
  obtain ⟨C, hC, h⟩ := hΦ.2.2 δ hδ (hleft.trans hright) 2 (by norm_num)
  refine integrable_of_eventual_sq_decay ?_ hC ?_
  · apply hΦ.2.1.continuousOn.comp_continuous
    · fun_prop
    · intro y
      simpa using hσ
  · exact h.mono fun y hy ↦ hy σ ⟨hleft.le, hright.le⟩

section ContourShift

open scoped Interval

/-- The horizontal Cauchy integrals vanish when the numerator decays uniformly in height. -/
private theorem horizontalKernel_tendsto_zero {Φ : ℂ → ℂ} {c d : ℝ} (hcd : c ≤ d) {C : ℝ}
    (hd : ∀ᶠ y : ℝ in atAbsInfty, ∀ x ∈ Icc c d, ‖Φ (verticalPoint x y)‖ ≤ C / |y|) (N : ℕ) (z : ℂ) :
    Tendsto (fun y : ℝ ↦ ∫ x in c..d, Φ (verticalPoint x y) / (verticalPoint x y - z) ^ (N + 1))
      atAbsInfty (𝓝 0) := by
  have hy : Tendsto (abs : ℝ → ℝ) atAbsInfty atTop := tendsto_comap
  apply squeeze_zero_norm'
  · filter_upwards [hd, hy.eventually (eventually_ge_atTop (|z.im| + 1))] with y hφ hlarge
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have im := Complex.abs_im_le_norm (verticalPoint x y - z)
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.ofReal_re, zero_add] at im
    have hsep : 1 ≤ ‖verticalPoint x y - z‖ := by linarith [abs_sub_abs_le_abs_sub y z.im]
    rw [norm_div, norm_pow]
    exact (div_le_self (norm_nonneg _) (one_le_pow₀ hsep)).trans
      (hφ x (Ioc_subset_Icc_self ((uIoc_of_le hcd) ▸ hx)))
  · simpa using ((tendsto_const_nhds (x := C)).div_atTop hy).mul_const |d - c|

end ContourShift

section CauchyStrip

variable {Φ : ℂ → ℂ} {a b : ℝ} (hΦ : UniformlySchwartzOnStrip Φ a b)

include hΦ

/-- Paper: Theorem B.2.2.4(1), p. 602. The Cauchy kernel is absolutely
integrable on each interior line off the real part of the evaluation point. -/
theorem cauchyKernel_verticalIntegrable_on_strip (σ : ℝ) (hσ : σ ∈ Ioo a b)
    (N : ℕ) (z : ℂ) (hz : z.re ≠ σ) :
    Complex.VerticalIntegrable (cauchyKernel Φ N z) σ := by
  exact kernel_integrable_from_trace (hΦ.verticalIntegrable σ hσ) N z hz

variable (ε : ℝ) (hε : 0 < ε) (hWidth : a + ε < b - ε) (N : ℕ) (z : ℂ)

include hε hWidth

/-- Paper: Theorem B.2.2.4(1), p. 601. The normalized right-line integral
minus the normalized left-line integral gives the derivative at a point between the lines. -/
theorem asymptoticCauchy_eq_iteratedDeriv (hz : z.re ∈ Ioo (a + ε) (b - ε)) :
    normalizedCauchyIntegral Φ N (b - ε) z - normalizedCauchyIntegral Φ N (a + ε) z =
      iteratedDeriv N Φ z := by
  let c := a + ε
  let d := b - ε
  have ha : a < c := by dsimp [c]; linarith
  have hb : d < b := by dsimp [d]; linarith
  have hc : c ∈ Ioo a b := ⟨ha, hWidth.trans hb⟩
  have hd : d ∈ Ioo a b := ⟨ha.trans hWidth, hb⟩
  let J (n : ℕ) (σ : ℝ) (w : ℂ) := normalizedCauchyIntegral Φ n σ w
  change J N d z - J N c z = iteratedDeriv N Φ z
  induction N generalizing z with
  | zero =>
    obtain ⟨C, hC, hdecay⟩ := hΦ.2.2 ε hε hWidth 1 le_rfl
    have hk (σ : ℝ) (hσ : σ ∈ Ioo a b) (hne : z.re ≠ σ) :
        Complex.VerticalIntegrable (fun w ↦ Φ w / (w - z)) σ := by
      simpa using cauchyKernel_verticalIntegrable_on_strip hΦ σ hσ 0 z hne
    have h := verticalCauchyIntegral_sub_eq hΦ.2.1 ha hb hz hC.le
      (by simpa only [pow_one] using hdecay) (hk c hc hz.1.ne') (hk d hd hz.2.ne)
    simp only [J, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one, iteratedDeriv_zero,
      verticalLineIntegral]
    rw [← mul_sub, ← mul_sub, h]
    field_simp [Complex.I_ne_zero, Real.pi_ne_zero]
  | succ n ih =>
    have hJ (σ : ℝ) (hσ : σ ∈ Ioo a b) (hne : z.re ≠ σ) :
        HasDerivAt (J n σ) (J (n + 1) σ z) z := by
      have h := hasDerivAt_verticalCauchyIntegral hne (hΦ.verticalIntegrable σ hσ) n
        (cauchyKernel_verticalIntegrable_on_strip hΦ σ hσ n z hne)
      convert (h.const_mul Complex.I).const_mul ((n.factorial : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) using 1
      · rfl
      · simp only [J, verticalLineIntegral, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
    have heq : (fun w ↦ J n d w - J n c w) =ᶠ[𝓝 z] iteratedDeriv n Φ :=
      ((isOpen_Ioo.preimage Complex.continuous_re).eventually_mem hz).mono fun w hw ↦ ih w hw
    rw [iteratedDeriv_succ, ← heq.deriv_eq]
    exact ((hJ d hd hz.2.ne).sub (hJ c hc hz.1.ne')).deriv.symm

/-- Paper: Theorem B.2.2.4(1), p. 602. The two normalized line integrals
agree when the evaluation point is outside the closed strip they bound. -/
theorem asymptoticCauchy_eq_zero (hz : z.re ∉ Icc (a + ε) (b - ε)) :
    normalizedCauchyIntegral Φ N (b - ε) z - normalizedCauchyIntegral Φ N (a + ε) z =
      0 := by
  let c := a + ε
  let d := b - ε
  have ha : a < c := by dsimp [c]; linarith
  have hb : d < b := by dsimp [d]; linarith
  have hcd : c < d := hWidth
  have hzc : z.re ≠ c := fun h ↦ hz (h ▸ left_mem_Icc.mpr hcd.le)
  have hzd : z.re ≠ d := fun h ↦ hz (h ▸ right_mem_Icc.mpr hcd.le)
  let K := cauchyKernel Φ N z
  have hdiff : DifferentiableOn ℂ K (Complex.re ⁻¹' Icc c d) := by
    apply (hΦ.2.1.mono (preimage_mono (Icc_subset_Ioo ha hb))).div
      ((differentiable_id.sub_const z).pow _).differentiableOn
    intro w hw
    exact pow_ne_zero _ (sub_ne_zero.mpr fun h ↦ hz (h ▸ hw))
  obtain ⟨C, _, hC⟩ := hΦ.2.2 ε hε hWidth 1 le_rfl
  have hh := horizontalKernel_tendsto_zero (Φ := Φ) hcd.le (C := C)
    (by simpa only [pow_one] using hC) N z
  have hv := verticalIntegral_eq_of_contour_shift hcd.le hdiff
    (cauchyKernel_verticalIntegrable_on_strip hΦ c ⟨ha, hcd.trans hb⟩ N z hzc)
    (cauchyKernel_verticalIntegrable_on_strip hΦ d ⟨ha.trans hcd, hb⟩ N z hzd) hh
  change _ * verticalLineIntegral K d - _ * verticalLineIntegral K c = 0
  rw [hv, sub_self]

end CauchyStrip

-- TODO(paper-gap): The finite rectangle preceding (B.2.2.10) needs
-- |T| > |Im(z)| for z to lie between the horizontal sides.
-- TODO(paper-gap): Theorem B.2.2.4(2), equations (B.2.2.6) and (B.2.2.7),
-- fail under the large-height condition of Definition B.2.2.1 alone.
-- The hypothesis does not bound the Hardy norm used in (B.2.2.12).

/-- Paper: Theorem B.2.2.4(2), p. 602. The vertical Cauchy integral on the
shifted half-plane boundary converges absolutely off the line.
Deviation: The two identities fail with the printed half-plane hypothesis. -/
theorem cauchyKernel_verticalIntegrable_on_leftHalfPlane
    {Φ : ℂ → ℂ} {b : ℝ} (hΦ : SchwartzOnLeftHalfPlane Φ b)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) (z : ℂ) (hz : z.re ≠ b - ε) :
    Complex.VerticalIntegrable (cauchyKernel Φ N z) (b - ε) := by
  apply kernel_integrable_from_trace _ N z hz
  obtain ⟨C, hC, h⟩ := hΦ.2 ε hε 2 (by norm_num)
  apply integrable_of_eventual_sq_decay _ hC
  · exact h.mono fun y hy ↦ hy (b - ε) le_rfl
  · apply hΦ.1.continuousOn.comp_continuous
    · fun_prop
    · intro y
      simpa using (sub_lt_self b hε)

-- TODO(paper-gap): Remark B.2.2.5 drops the inverse Mellin normalization
-- and does not justify extension by zero from the real-axis Fourier argument.
-- Its final global bound would force the entire function to vanish.

/-- Paper: Remark B.2.2.5, p. 603. The inverse Mellin integrand
on the imaginary axis is absolutely integrable for every positive input. -/
theorem verticalIntegrable_mellinInv_of_schwartzOnVerticalStrips {Φ : ℂ → ℂ}
    (hΦ : SchwartzOnVerticalStrips Φ) (t : ℝ) (ht : 0 < t) :
    Complex.VerticalIntegrable (fun s ↦ Φ s * (t : ℂ) ^ (-s)) 0 := by
  have h := (hΦ.2 (-1) 1 (by norm_num)).verticalIntegrable 0 (by constructor <;> norm_num)
  have hphase : Continuous (fun y : ℝ ↦ (t : ℂ) ^ (-(verticalPoint 0 y))) := by
    apply Continuous.const_cpow (by fun_prop)
    exact Or.inl (by exact_mod_cast ht.ne')
  have bound (y : ℝ) : ‖(t : ℂ) ^ (-(verticalPoint 0 y))‖ ≤ 1 := by
    simp [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  exact (h.bdd_mul hphase.aestronglyMeasurable (Eventually.of_forall bound)).congr
    (Eventually.of_forall fun y ↦ mul_comm _ _)

section InverseContour

open scoped Interval

local notation "invKernel" => (fun (Φ : ℂ → ℂ) (t : ℝ) (s : ℂ) ↦ Φ s * (t : ℂ) ^ (-s))
local notation "invProfile" => (fun (Φ : ℂ → ℂ) ↦ Set.indicator (Ioi (0 : ℝ)) (fun t ↦
  verticalLineIntegral (invKernel Φ t) 0))
local notation "invDeriv" => (fun (Φ : ℂ → ℂ) (s : ℂ) ↦ (1 - s) * Φ (s - 1))

/-- The transform corresponding to differentiation of the inverse Mellin integral. -/
private theorem invDeriv_schwartz {Φ : ℂ → ℂ} (h : SchwartzOnVerticalStrips Φ) :
    SchwartzOnVerticalStrips (invDeriv Φ) := by
  have hd : Differentiable ℂ (invDeriv Φ) :=
    ((differentiable_const (1 : ℂ)).sub differentiable_id).mul (h.1.comp (differentiable_id.sub_const 1))
  refine ⟨hd, fun a b hab ↦ ⟨hab, hd.differentiableOn, ?_⟩⟩
  intro ε hε hw n hn
  obtain ⟨C, hC, hdec⟩ := (h.2 (a - 1) (b - 1) (by linarith)).2.2 ε hε (by linarith)
    (n + 1) (by omega)
  let M := max |a| |b|
  have hM : 0 ≤ M := (abs_nonneg a).trans (le_max_left _ _)
  refine ⟨(M + 2) * C, mul_pos (by linarith) hC, ?_⟩
  have large : ∀ᶠ y : ℝ in atAbsInfty, 1 ≤ |y| := tendsto_comap.eventually (eventually_ge_atTop 1)
  filter_upwards [hdec, large] with y hy hlarge x hx
  have hxM : |x| ≤ M := abs_le.mpr ⟨by linarith [hx.1, neg_abs_le a, le_max_left |a| |b|],
    by linarith [hx.2, le_abs_self b, le_max_right |a| |b|]⟩
  have hle : ‖1 - verticalPoint x y‖ ≤ (M + 2) * |y| := by
    calc ‖1 - verticalPoint x y‖ ≤ ‖(1 : ℂ)‖ + ‖verticalPoint x y‖ := norm_sub_le _ _
      _ ≤ 1 + (|x| + |y|) := by
        rw [norm_one]
        gcongr
        simpa using norm_add_le (x : ℂ) ((y : ℂ) * Complex.I)
      _ ≤ _ := by nlinarith [mul_nonneg hM (sub_nonneg.mpr hlarge)]
  have hshift : verticalPoint x y - 1 = verticalPoint (x - 1) y := by push_cast; ring
  rw [norm_mul, hshift]
  calc ‖1 - verticalPoint x y‖ * ‖Φ (verticalPoint (x - 1) y)‖ ≤ (M + 2) * |y| * (C / |y| ^ (n + 1)) :=
      mul_le_mul hle (hy (x - 1) ⟨by linarith [hx.1], by linarith [hx.2]⟩) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; field_simp [(zero_lt_one.trans_le hlarge).ne']

/-- Every vertical trace of an entire function with rapid strip decay is integrable. -/
private theorem entireTrace_integrable {Φ : ℂ → ℂ} (h : SchwartzOnVerticalStrips Φ) (c : ℝ) :
    Complex.VerticalIntegrable Φ c :=
  (h.2 (c - 1) (c + 1) (by linarith)).verticalIntegrable c ⟨by linarith, by linarith⟩

/-- On a vertical line the inverse Mellin phase has constant norm. -/
private theorem invKernel_integrable {Φ : ℂ → ℂ} (h : SchwartzOnVerticalStrips Φ) {t : ℝ} (ht : 0 < t)
    (c : ℝ) : Complex.VerticalIntegrable (invKernel Φ t) c := by
  have hp : Continuous (fun y : ℝ ↦ (t : ℂ) ^ (-(verticalPoint c y))) :=
    Continuous.const_cpow (by fun_prop) (.inl (by exact_mod_cast ht.ne'))
  have bound (y : ℝ) : ‖(t : ℂ) ^ (-(verticalPoint c y))‖ ≤ t ^ (-c) := by
    simp [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  exact ((entireTrace_integrable h c).bdd_mul hp.aestronglyMeasurable (Eventually.of_forall bound)).congr
    (Eventually.of_forall fun y ↦ mul_comm _ _)

/-- Shift the contour to any negative real part before differentiating or approaching zero. -/
private theorem invProfile_eq_shift {Φ : ℂ → ℂ} (h : SchwartzOnVerticalStrips Φ) {t : ℝ} (ht : 0 < t)
    {c : ℝ} (hc : c < 0) : invProfile Φ t = verticalLineIntegral (invKernel Φ t) c := by
  change (Ioi (0 : ℝ)).indicator _ t = _
  rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
  refine verticalIntegral_eq_of_contour_shift hc.le ?_ (invKernel_integrable h ht c) (invKernel_integrable h ht 0) ?_
  · have hp : Differentiable ℂ (fun s : ℂ ↦ (t : ℂ) ^ (-s)) :=
      differentiable_id.neg.const_cpow (.inl (by exact_mod_cast ht.ne'))
    exact (h.1.mul hp).differentiableOn
  · obtain ⟨C, hC, hdec⟩ := (h.2 (c - 1) 1 (by linarith)).2.2 1 zero_lt_one (by linarith) 1 le_rfl
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := c) (b := 0)).bddAbove_image
      ((Real.continuous_const_rpow ht.ne').comp continuous_neg).continuousOn
    apply squeeze_zero_norm'
    · filter_upwards [hdec] with y hy
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' := Ioc_subset_Icc_self ((uIoc_of_le hc.le) ▸ hx)
      have hx'' := hy x (show x ∈ Icc (c - 1 + 1) (1 - 1) by simpa using hx')
      have hb := hB (mem_image_of_mem _ hx')
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
        neg_zero, add_zero, pow_one] at *
      exact mul_le_mul hx'' hb (Real.rpow_nonneg ht.le _) (by positivity)
    · have hy : Tendsto (abs : ℝ → ℝ) atAbsInfty atTop := tendsto_comap
      simpa using (((tendsto_const_nhds (x := C)).div_atTop hy).mul_const B).mul_const |0 - c|

/-- Differentiation on the line of real part minus one produces the shifted multiplier. -/
private theorem invProfile_hasDerivAt_pos {Φ : ℂ → ℂ} (h : SchwartzOnVerticalStrips Φ)
    {t : ℝ} (ht : 0 < t) : HasDerivAt (invProfile Φ) (invProfile (invDeriv Φ) t) t := by
  let p (y : ℝ) := verticalPoint (-1) y
  let q (y : ℝ) := verticalPoint 0 y
  let F (u y : ℝ) := invKernel Φ u (p y)
  let F' (u y : ℝ) := invKernel (invDeriv Φ) u (q y)
  have hs := invDeriv_schwartz h
  have hpq (y : ℝ) : q y - 1 = p y := by dsimp [p, q]; push_cast; ring
  have hexp (y : ℝ) : -(p y) - 1 = -(q y) := by rw [← hpq]; ring
  have lim : HasDerivAt (fun u ↦ ∫ y, F u y) (∫ y, F' t y) t := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
      (bound := fun y ↦ ‖invDeriv Φ (q y)‖) (Ioi_mem_nhds ht) ?_ (invKernel_integrable h ht (-1))
      (invKernel_integrable hs ht 0).aestronglyMeasurable ?_ (entireTrace_integrable hs 0).norm ?_).2
    · filter_upwards [Ioi_mem_nhds ht] with u hu
      exact (invKernel_integrable h hu (-1)).aestronglyMeasurable
    · filter_upwards with y u hu
      simp [F', Complex.norm_cpow_eq_rpow_re_of_pos hu, q]
    · filter_upwards with y u hu
      have hne : -(p y) ≠ 0 := by
        intro he
        simpa [p] using congrArg Complex.re he
      have hder := (hasDerivAt_ofReal_cpow_const (ne_of_gt hu) hne).const_mul (Φ (p y))
      convert hder using 1
      dsimp only [F']
      rw [hexp, hpq, ← hpq]
      ring
  have hEq : invProfile Φ =ᶠ[𝓝 t] (fun u ↦ Complex.I * ∫ y, F u y) :=
    (eventually_gt_nhds ht).mono fun u hu ↦ invProfile_eq_shift h hu (by norm_num : (-1 : ℝ) < 0)
  change HasDerivAt _ ((Ioi (0 : ℝ)).indicator _ t) t
  rw [indicator_of_mem ht]
  exact (lim.const_mul Complex.I).congr_of_eventuallyEq hEq

/-- A contour at real part minus two bounds the profile by a quadratic at the origin. -/
private theorem invProfile_hasDerivAt_zero {Φ : ℂ → ℂ} (h : SchwartzOnVerticalStrips Φ) :
    HasDerivAt (invProfile Φ) 0 0 := by
  let C := ∫ y : ℝ, ‖Φ (verticalPoint (-2) y)‖
  have hC : 0 ≤ C := integral_nonneg fun _ ↦ norm_nonneg _
  have bound (u : ℝ) : ‖invProfile Φ u‖ ≤ C * |u| ^ 2 := by
    by_cases hu : 0 < u
    · rw [invProfile_eq_shift h hu (by norm_num : (-2 : ℝ) < 0), verticalLineIntegral, norm_mul,
        Complex.norm_I, one_mul, abs_of_pos hu]
      rw [show C * u ^ 2 = ∫ y : ℝ, ‖Φ (verticalPoint (-2) y)‖ * u ^ 2 from (integral_mul_const _ _).symm]
      apply norm_integral_le_of_norm_le ((entireTrace_integrable h (-2)).norm.mul_const _) (Eventually.of_forall _)
      intro y
      simp [Complex.norm_cpow_eq_rpow_re_of_pos hu]
    · change ‖(Ioi (0 : ℝ)).indicator _ u‖ ≤ _
      rw [indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu), norm_zero]
      positivity
  rw [hasDerivAt_iff_tendsto]
  simp only [indicator_of_notMem (show (0 : ℝ) ∉ Ioi 0 by simp), sub_zero, smul_zero]
  apply squeeze_zero (g := fun u : ℝ ↦ C * |u|) (fun u ↦ mul_nonneg (by positivity) (norm_nonneg _))
  · intro u
    by_cases hu : u = 0
    · simp [hu]
    · calc ‖u‖⁻¹ * ‖invProfile Φ u‖ ≤ ‖u‖⁻¹ * (C * |u| ^ 2) := by gcongr; exact bound u
        _ = C * |u| := by rw [Real.norm_eq_abs]; field_simp [abs_ne_zero.mpr hu]
  · have cont : Continuous (fun u : ℝ ↦ C * |u|) := continuous_const.mul continuous_abs
    simpa only [abs_zero, mul_zero] using cont.tendsto 0

/-- The zero-extended inverse Mellin profile differentiates by a shifted multiplier. -/
private theorem invProfile_hasDerivAt {Φ : ℂ → ℂ} (h : SchwartzOnVerticalStrips Φ) (t : ℝ) :
    HasDerivAt (invProfile Φ) (invProfile (invDeriv Φ) t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · change HasDerivAt _ ((Ioi (0 : ℝ)).indicator _ t) t
    rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht.not_gt)]
    exact (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq
      ((eventually_lt_nhds ht).mono fun u hu ↦ indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from (le_of_lt hu).not_gt) _)
  · simpa using invProfile_hasDerivAt_zero h
  · exact invProfile_hasDerivAt_pos h ht

/-- Paper: Remark B.2.2.5, p. 603. The zero extension of the imaginary-axis
contour integral is smooth on the real line. -/
theorem contDiff_zeroExtension_mellinInv_of_schwartzOnVerticalStrips {Φ : ℂ → ℂ}
    (hΦ : SchwartzOnVerticalStrips Φ) :
    ContDiff ℝ ∞ ((Ioi (0 : ℝ)).indicator fun t ↦
      verticalLineIntegral (fun s ↦ Φ s * (t : ℂ) ^ (-s)) 0) := by
  change ContDiff ℝ ∞ (invProfile Φ)
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  induction n generalizing Φ with
  | zero =>
    rw [iteratedDeriv_zero]
    exact fun t ↦ (invProfile_hasDerivAt hΦ t).differentiableAt
  | succ n ih =>
    have he : deriv (invProfile Φ) = invProfile (invDeriv Φ) := funext fun t ↦ (invProfile_hasDerivAt hΦ t).deriv
    rw [iteratedDeriv_succ', he]
    exact ih (invDeriv_schwartz hΦ) le_top

end InverseContour

/-- Apply the strip estimate to a compact interval of arbitrary placement. -/
private theorem closedSubstrip_decay {Φ : ℂ → ℂ} {a b c d : ℝ} (h : UniformlySchwartzOnStrip Φ a b)
    (ha : a < c) (hcd : c ≤ d) (hb : d < b) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C > (0 : ℝ), ∀ᶠ y : ℝ in atAbsInfty, ∀ x ∈ Icc c d, ‖Φ (verticalPoint x y)‖ ≤ C / |y| ^ n := by
  let ε := min (c - a) (b - d) / 2
  have hε : 0 < ε := half_pos (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb))
  have hl : a + ε < c := by dsimp [ε]; linarith [min_le_left (c - a) (b - d)]
  have hr : d < b - ε := by dsimp [ε]; linarith [min_le_right (c - a) (b - d)]
  obtain ⟨C, hC, h'⟩ := h.2.2 ε hε (hl.trans (hcd.trans_lt hr)) n hn
  exact ⟨C, hC, h'.mono fun y hy x hx ↦ hy x ⟨hl.le.trans hx.1, hx.2.trans hr.le⟩⟩

/-- A polynomial weight absorbs the inverse powers of the imaginary part at large heights. -/
private theorem pow_mul_bound_of_heightBound {Φ : ℂ → ℂ} {c d C x y : ℝ} {n : ℕ}
    (hx : x ∈ Icc c d) (hy : 1 ≤ |y|) (h : ‖Φ (verticalPoint x y)‖ ≤ C / |y| ^ n) :
    ‖(verticalPoint x y) ^ n * Φ (verticalPoint x y)‖ ≤ (max |c| |d| + 1) ^ n * C := by
  let M := max |c| |d|
  have hM : 0 ≤ M := (abs_nonneg c).trans (le_max_left _ _)
  have hxM : |x| ≤ M := abs_le.mpr ⟨by linarith [hx.1, neg_abs_le c, le_max_left |c| |d|],
    by linarith [hx.2, le_abs_self d, le_max_right |c| |d|]⟩
  have hb : ‖verticalPoint x y‖ ≤ (M + 1) * |y| := by
    calc ‖verticalPoint x y‖ ≤ |x| + |y| := by simpa using norm_add_le (x : ℂ) ((y : ℂ) * Complex.I)
      _ ≤ (M + 1) * |y| := by nlinarith [mul_nonneg hM (sub_nonneg.mpr hy)]
  rw [norm_mul, norm_pow]
  calc ‖verticalPoint x y‖ ^ n * ‖Φ (verticalPoint x y)‖ ≤ ((M + 1) * |y|) ^ n * (C / |y| ^ n) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hb _) h (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_pow]; dsimp only [M]; field_simp [ne_of_gt (zero_lt_one.trans_le hy)]

/-- A continuous function bounded outside a bounded interval is bounded everywhere. -/
private theorem globally_bounded_of_height_bound {G : ℝ → ℂ} (hG : Continuous G) {C : ℝ}
    (h : ∀ᶠ y : ℝ in atAbsInfty, ‖G y‖ ≤ C) : ∃ D, ∀ y, ‖G y‖ ≤ D := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp h)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -R) (b := R)).bddAbove_image hG.norm.continuousOn
  refine ⟨max B C, fun y ↦ ?_⟩
  by_cases hy : R ≤ |y|
  · exact (hR |y| hy y rfl).trans (le_max_right _ _)
  · exact (hB (mem_image_of_mem _ (abs_le.mp (le_of_not_ge hy)))).trans (le_max_left _ _)

/-- Bounds along selected horizontal lines above and below each point propagate through the strip. -/
private theorem norm_le_of_selected_rectangles {F : ℂ → ℂ} {c d B : ℝ} (hcd : c < d)
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc c d))
    (hedge : ∀ w : ℂ, w.re = c ∨ w.re = d → ‖F w‖ ≤ B)
    (T : ℤ → ℝ) (hMono : Monotone T)
    (hInf : Tendsto (fun k : ℤ ↦ |T k|) (comap abs atTop) atTop)
    (hT : ∀ᶠ k : ℤ in comap abs atTop, ∀ x ∈ Icc c d, ‖F (verticalPoint x (T k))‖ ≤ B)
    (z : ℂ) (hz : z.re ∈ Icc c d) : ‖F z‖ ≤ B := by
  have top : Tendsto (fun k : ℤ ↦ k) atTop (comap abs atTop) :=
    tendsto_comap_iff.mpr tendsto_abs_atTop_atTop
  have bot : Tendsto (fun k : ℤ ↦ k) atBot (comap abs atTop) :=
    tendsto_comap_iff.mpr tendsto_abs_atBot_atTop
  obtain ⟨u, hu, hTu⟩ : ∃ k, z.im < T k ∧ ∀ x ∈ Icc c d, ‖F (verticalPoint x (T k))‖ ≤ B := by
    have eventually := (hInf.comp top).eventually (eventually_gt_atTop (max z.im (-(T 0))))
    obtain ⟨k, hpos, hlarge, hhorizontal⟩ :=
      ((eventually_ge_atTop 0).and (eventually.and (top.eventually hT))).exists
    have h0 := hMono hpos
    refine ⟨k, ?_, hhorizontal⟩
    change max z.im (-(T 0)) < |T k| at hlarge
    rcases lt_abs.mp hlarge with h | h
    · exact (le_max_left _ _).trans_lt h
    · linarith [le_max_right z.im (-(T 0))]
  obtain ⟨l, hl, hTl⟩ : ∃ k, T k < z.im ∧ ∀ x ∈ Icc c d, ‖F (verticalPoint x (T k))‖ ≤ B := by
    have eventually := (hInf.comp bot).eventually (eventually_gt_atTop (max (-z.im) (T 0)))
    obtain ⟨k, hneg, hlarge, hhorizontal⟩ :=
      ((eventually_le_atBot 0).and (eventually.and (bot.eventually hT))).exists
    have h0 := hMono hneg
    refine ⟨k, ?_, hhorizontal⟩
    change max (-z.im) (T 0) < |T k| at hlarge
    rcases lt_abs.mp hlarge with h | h
    · linarith [le_max_right (-z.im) (T 0)]
    · linarith [le_max_left (-z.im) (T 0)]
  have hlu := hl.trans hu
  have cl := Complex.closure_reProdIm (Ioo c d) (Ioo (T l) (T u))
  rw [closure_Ioo hcd.ne, closure_Ioo hlu.ne] at cl
  apply Complex.norm_le_of_forall_mem_frontier_norm_le ((Metric.isBounded_Ioo c d).reProdIm (Metric.isBounded_Ioo (T l) (T u)))
  · apply DifferentiableOn.diffContOnCl
    rw [cl]
    exact hF.mono fun w hw ↦ hw.1
  · intro w hw
    rw [Complex.frontier_reProdIm, frontier_Ioo hcd, frontier_Ioo hlu, closure_Ioo hcd.ne,
      closure_Ioo hlu.ne] at hw
    rcases hw with hw | hw
    · have him : w.im = T l ∨ w.im = T u := hw.2
      have hxy : verticalPoint w.re w.im = w := Complex.re_add_im w
      rcases him with him | him
      · rw [← hxy, him]
        exact hTl _ hw.1
      · rw [← hxy, him]
        exact hTu _ hw.1
    · exact hedge w hw.1
  · rw [cl]
    exact ⟨hz, hl.le, hu.le⟩

/-- Multiplication by a polynomial gives a globally bounded vertical trace. -/
private theorem weighted_trace_bound {Φ : ℂ → ℂ} {x C : ℝ} {n : ℕ}
    (hc : Continuous (fun y : ℝ ↦ Φ (verticalPoint x y)))
    (h : ∀ᶠ y : ℝ in atAbsInfty, ‖Φ (verticalPoint x y)‖ ≤ C / |y| ^ n) :
    ∃ B, ∀ y : ℝ, ‖(verticalPoint x y) ^ n * Φ (verticalPoint x y)‖ ≤ B := by
  apply globally_bounded_of_height_bound (Continuous.mul (by fun_prop) hc)
  have hy : ∀ᶠ y : ℝ in atAbsInfty, 1 ≤ |y| := tendsto_comap.eventually (eventually_ge_atTop 1)
  filter_upwards [h, hy] with y hyφ hy'
  exact pow_mul_bound_of_heightBound (show x ∈ Icc x x from ⟨le_rfl, le_rfl⟩) hy' hyφ

section CauchySelectedHeights

variable {Φ : ℂ → ℂ} {a a' a'' b'' b' b : ℝ}
  (ha₁ : a < a'') (ha₂ : a'' < a') (hab : a' < b') (hb₁ : b' < b'') (hb₂ : b'' < b)
  (hΦ : DifferentiableOn ℂ Φ (openStrip a b))
  (hLeft : UniformlySchwartzOnStrip Φ a a') (hRight : UniformlySchwartzOnStrip Φ b' b)
  (T : ℤ → ℝ) (hMono : StrictMono T)
  (hInf : Tendsto (fun k : ℤ ↦ |T k|) (comap (abs : ℤ → ℤ) atTop) atTop)
  (hHeight : ∀ M : ℕ, 1 ≤ M → ∃ C > (0 : ℝ),
    ∀ᶠ k : ℤ in atAbsInfty, ∀ σ ∈ Icc a'' b'',
      ‖Φ (verticalPoint σ (T k))‖ ≤ C / |T k| ^ M)

include ha₁ ha₂ hab hb₁ hb₂ hΦ hLeft hRight hMono hInf hHeight

/-- Paper: Corollary B.2.2.6, p. 603. Rapid decay along the chosen horizontal
lines and near both vertical edges implies uniform rapid decay on every closed substrip. -/
theorem uniformlySchwartzOnStrip_of_selectedHeights : UniformlySchwartzOnStrip Φ a b := by
  have hmid := ha₂.trans (hab.trans hb₁)
  refine ⟨ha₁.trans (hmid.trans hb₂), hΦ, ?_⟩
  intro ε hε _ n hn
  let l := min (a + ε) a''
  let r := max (b - ε) b''
  obtain ⟨L, hL, left⟩ := closedSubstrip_decay hLeft
    (show a < l from lt_min (by linarith) ha₁) (min_le_right _ _) ha₂ n hn
  obtain ⟨R, hR, right⟩ := closedSubstrip_decay hRight hb₁ (le_max_right _ _)
    (show r < b from max_lt (by linarith) hb₂) n hn
  let F (z : ℂ) := z ^ n * Φ z
  have hcont (x : ℝ) (hx : x ∈ Ioo a b) : Continuous (fun y : ℝ ↦ Φ (verticalPoint x y)) :=
    hΦ.continuousOn.comp_continuous (by fun_prop) fun y ↦ by simpa using hx
  obtain ⟨A, hA⟩ := weighted_trace_bound (hcont a'' ⟨ha₁, hmid.trans hb₂⟩)
    (left.mono fun y hy ↦ hy a'' ⟨min_le_right _ _, le_rfl⟩)
  obtain ⟨B, hB⟩ := weighted_trace_bound (hcont b'' ⟨ha₁.trans hmid, hb₂⟩)
    (right.mono fun y hy ↦ hy b'' ⟨le_rfl, le_max_right _ _⟩)
  obtain ⟨C, _, hC⟩ := hHeight n hn
  let H := (max |a''| |b''| + 1) ^ n * C
  let D := max (max A B) H
  have hbound (z : ℂ) (hz : z.re ∈ Icc a'' b'') : ‖F z‖ ≤ D := by
    apply norm_le_of_selected_rectangles hmid (F := F) _ _ T hMono.monotone hInf _ z hz
    · exact ((differentiable_id.pow n).differentiableOn.mul hΦ).mono (preimage_mono (Icc_subset_Ioo ha₁ hb₂))
    · intro w hw
      rw [← Complex.re_add_im w]
      rcases hw with hw | hw
      · rw [hw]
        exact (hA w.im).trans ((le_max_left A B).trans (le_max_left _ _))
      · rw [hw]
        exact (hB w.im).trans ((le_max_right A B).trans (le_max_left _ _))
    · filter_upwards [hC, hInf.eventually (eventually_ge_atTop 1)] with k hk hy x hx
      exact (pow_mul_bound_of_heightBound hx hy (hk x hx)).trans (le_max_right _ _)
  let M := max (max L R) D
  refine ⟨M, hL.trans_le ((le_max_left L R).trans (le_max_left _ _)), ?_⟩
  have hy : ∀ᶠ y : ℝ in atAbsInfty, 0 < |y| := tendsto_comap.eventually (eventually_gt_atTop 0)
  filter_upwards [left, right, hy] with y hly hry hy x hx
  by_cases hl : x ≤ a''
  · exact (hly x ⟨(min_le_left _ _).trans hx.1, hl⟩).trans
      (div_le_div_of_nonneg_right ((le_max_left L R).trans (le_max_left _ _)) (by positivity))
  by_cases hr : b'' ≤ x
  · exact (hry x ⟨hr, hx.2.trans (le_max_left _ _)⟩).trans
      (div_le_div_of_nonneg_right ((le_max_right L R).trans (le_max_left _ _)) (by positivity))
  have hz : (verticalPoint x y).re ∈ Icc a'' b'' := by simpa using And.intro (le_of_not_ge hl) (le_of_not_ge hr)
  have him : |y| ≤ ‖verticalPoint x y‖ := by simpa using Complex.abs_im_le_norm (verticalPoint x y)
  rw [le_div_iff₀ (pow_pos hy _), mul_comm]
  calc |y| ^ n * ‖Φ (verticalPoint x y)‖ ≤ ‖verticalPoint x y‖ ^ n * ‖Φ (verticalPoint x y)‖ := by gcongr
    _ = ‖F (verticalPoint x y)‖ := by simp only [F, norm_mul, norm_pow]
    _ ≤ M := (hbound _ hz).trans (le_max_right _ _)

/-- Paper: Corollary B.2.2.6, p. 603. With the two edge bounds and the
selected horizontal heights, the vertical Cauchy kernel is absolutely integrable
on each interior line off the real part of the evaluation point. -/
theorem cauchyKernel_verticalIntegrable_of_selectedHeights (σ : ℝ) (hσ : σ ∈ Ioo a b)
    (N : ℕ) (z : ℂ) (hz : z.re ≠ σ) :
    Complex.VerticalIntegrable (cauchyKernel Φ N z) σ := by
  exact cauchyKernel_verticalIntegrable_on_strip
    (uniformlySchwartzOnStrip_of_selectedHeights ha₁ ha₂ hab hb₁ hb₂ hΦ hLeft hRight T hMono hInf hHeight)
    σ hσ N z hz

variable (ε : ℝ) (hε : 0 < ε) (hWidth : a + ε < b - ε) (N : ℕ) (z : ℂ)

include hε hWidth

/-- Paper: Corollary B.2.2.6, p. 603. Rapid decay near both edges and
along the selected horizontal lines gives the Cauchy derivative formula inside. -/
theorem asymptoticCauchy_eq_iteratedDeriv_of_selectedHeights (hz : z.re ∈ Ioo (a + ε) (b - ε)) :
    normalizedCauchyIntegral Φ N (b - ε) z - normalizedCauchyIntegral Φ N (a + ε) z =
      iteratedDeriv N Φ z := by
  exact asymptoticCauchy_eq_iteratedDeriv
    (uniformlySchwartzOnStrip_of_selectedHeights ha₁ ha₂ hab hb₁ hb₂ hΦ hLeft hRight T hMono hInf hHeight)
    ε hε hWidth N z hz

/-- Paper: Corollary B.2.2.6, p. 603. Under the same edge and height
conditions, the difference of the normalized integrals vanishes outside. -/
theorem asymptoticCauchy_eq_zero_of_selectedHeights (hz : z.re ∉ Icc (a + ε) (b - ε)) :
    normalizedCauchyIntegral Φ N (b - ε) z - normalizedCauchyIntegral Φ N (a + ε) z =
      0 := by
  exact asymptoticCauchy_eq_zero
    (uniformlySchwartzOnStrip_of_selectedHeights ha₁ ha₂ hab hb₁ hb₂ hΦ hLeft hRight T hMono hInf hHeight)
    ε hε hWidth N z hz

end CauchySelectedHeights

end RiemannMasullo
