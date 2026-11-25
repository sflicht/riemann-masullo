module

public import RiemannMasullo.Ch13_ZerosHecke.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec6
import RiemannMasullo.External.TauCeti.Analysis.Complex.Conformal.Montel.Basic
import RiemannMasullo.ForMathlib.Analysis.Meromorphic.VerticalStripZeros
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Holomorphic
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.External.Grh.Lemmas.AnalyticGoodHeightDisk
import RiemannMasullo.External.Grh.Lemmas.LogLossGoodHeight
import RiemannMasullo.Ch12_TraceGeometric.Sec5
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.DigammaIntegral
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import RiemannMasullo.External.HardyCriticalLine.DigammaFormula
import RiemannMasullo.External.HardyCriticalLine.CriticalLineStirlingPhase
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Probability.Distributions.Cauchy

import RiemannMasullo.Ch07_SchauderBasesZeta.Sec5
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b
import Mathlib.Analysis.Normed.Group.Tannery
import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
import RiemannMasullo.ForMathlib.Analysis.Distribution.TestFunction.Schwartz
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.Deriv.Shift
import RiemannMasullo.External.TauCeti.Analysis.SpecialFunctions.SmoothTransition
import RiemannMasullo.External.TauCeti.MeasureTheory.Integral.NormRpow
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Holomorphic

/-! # From the trace formula to GRH

Masullo, §1.4, pp. 27–31, repeated in §§1.8.4–1.8.5. The introductory trace
identity recurs as Theorem 12.5.1.1. The centered version is `traceFormula`.
The page 28 display uses an uncentered zero window. Its literal form is
`Printed.introTrace_globalTrace` in the companion file. The passage from the
trace identity to the zero-free region requires limits of the trace terms.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instNormOneIdeleClassMeasurableSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "D𝔽" => BruhatCompactSupport C𝔽
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "q(" v ")" => ((v : V).asIdeal.absNorm : ℝ)
local notation "N(" g ")" => (((ideleClassNorm F) (g : C𝔽)).val : ℝ)
local notation "right(" a ")" => (Complex.re ⁻¹' Ioi (a : ℝ))
local notation "τVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "finiteL(" χ ")" => (finiteHeckeL_exists_continuation (F := F) χ).choose
local notation "zeroOrder(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "windowZeros(" χ ", " a ")" =>
  {s : ℂ // 0 < zeroOrder(χ, s) ∧ |s.re - 1 / 2| < (a : ℝ)}

-- TODO(paper-gap): The “Finish!” footnotes on p. 27 belong to §§1.3.3–1.3.4.
-- The deduction here inherits the unfinished kernel comparisons in those subsections.
-- The centered window in §1.8.4, p. 53, agrees with the shift in §1.4.3.

/-- Paper: §1.4.1, p. 28. A radial profile gives a test of norm-one weight
conjugate to the character by multiplication by that conjugate on the idele classes.
Deviation: The conjugate is required by the stated weight and by the zero Mellin
pairing. The product in the prose of §§1.4.2–1.4.3 uses the character itself. -/
def introTraceTest (χ : U𝔽) (h : ℝ → ℂ) (g : C𝔽) : ℂ :=
  (star (χ g : ℂ)) * h (N(g))

local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "archIntegrand(" χ ", " h ", " w ")" =>
  (fun u : (w : InfinitePlace F).Completionˣ ↦
    introTraceTest χ h (archClass(w) u) * (Real.sqrt (‖u.val‖ ^ InfinitePlace.mult w) : ℂ) /
      ((‖1 - u.val‖ ^ InfinitePlace.mult w : ℝ) : ℂ))

section CharacterTrace

/-- Paper: §1.4.1, p. 28. Right translation by a norm-one class multiplies the
test by the conjugate character value on that class. -/
theorem introTraceTest_mul_normOne (χ : U𝔽) (h : ℝ → ℂ)
    (g : C𝔽) (u : (ideleClassNorm F).ker) :
    introTraceTest χ h (g * u.val) = star (χ u.val : ℂ) * introTraceTest χ h g := by
  have hu : ideleClassNorm F u.val = 1 := u.property
  simp only [introTraceTest, map_mul, hu, mul_one, Circle.coe_mul, star_mul]
  ac_rfl

/-- Paper: §1.4.1, p. 28. Mathlib's Mellin moment of the radial profile uses the
positive norm coordinate with Haar density `dt/t`. -/
def introTraceMellin (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin h s

/-- Paper: §1.4.1, p. 28. In the selected isotype the global Mellin integral
exists and is the radial moment times the norm-one Tamagawa volume. -/
theorem introTraceTest_mellin (χ : U𝔽) (h : ℝ → ℂ) (φ : D𝔽)
    (_hφ : ∀ g, φ.val g = introTraceTest χ h g) (s : ℂ) :
    let f := fun g : C𝔽 ↦ φ.val g * ideleClassNormTwist χ s g
    Integrable f (ideleClassTamagawaMeasure F) ∧
      (∫ g, f g ∂ideleClassTamagawaMeasure F) = τVolume * introTraceMellin h s := by
  let W (g : C𝔽) := φ.val g * ideleClassNormTwist χ s g
  have hc : Continuous φ.val := schwartzBruhat_continuous
    (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hW : Continuous W := hc.mul (ideleClassNormTwist χ s).continuous
  refine ⟨hW.integrable_of_hasCompactSupport
    (show HasCompactSupport φ.val from φ.property.2).mul_right, ?_⟩
  have hrad (g : C𝔽) : W g = h (N(g)) * (N(g) : ℂ) ^ s := by
    change φ.val g * ((χ g : ℂ) * (N(g) : ℂ) ^ s) = _
    rw [_hφ, introTraceTest]
    have hu : star (χ g : ℂ) * (χ g : ℂ) = 1 := by simp [← Circle.coe_inv_eq_conj]
    linear_combination h (N(g)) * (N(g) : ℂ) ^ s * hu
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let σ (x : ℝ) : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F (E x))
  have hσ : Continuous σ :=
    continuous_quotient_mk'.comp ((canonicalIdeleNormSection_continuous F).comp E.continuous)
  have hnorm (x : ℝ) : N(σ x) = Real.exp x :=
    congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (canonicalIdeleNormSection_rightInverse F (E x))
  let l (g : C𝔽) := Real.log (N(g))
  have hl : Measurable l := Real.measurable_log.comp
    ((NNReal.continuous_coe.comp Units.continuous_val).comp
      (isProperMap_ideleClassNorm F).continuous).measurable
  have hsec (g : C𝔽) : W (σ (l g)) = W g := by
    have he : Real.exp (l g) = N(g) := Real.exp_log (Units.zero_lt (ideleClassNorm F g))
    rw [hrad, hrad, hnorm, he]
  have hmellin : (∫ x : ℝ, W (σ x)) = introTraceMellin h s := by
    rw [introTraceMellin, mellin, ← integral_comp_exp]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    beta_reduce
    rw [hrad, hnorm, Complex.real_smul, smul_eq_mul]
    have he : (Real.exp x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'
    rw [show (s : ℂ) = (s - 1) + 1 by ring, Complex.cpow_add _ _ he,
      Complex.cpow_one, add_sub_cancel_right]
    ring
  change (∫ g, W g ∂ideleClassTamagawaMeasure F) = _
  calc
    _ = ∫ x, W (σ x) ∂(ideleClassTamagawaMeasure F).map l := by
      rw [integral_map (f := fun x ↦ W (σ x)) hl.aemeasurable (hW.comp hσ).aestronglyMeasurable]
      exact integral_congr_ae (.of_forall fun g ↦ (hsec g).symm)
    _ = _ := by
      rw [show (ideleClassTamagawaMeasure F).map l = _ from classTamagawa_map_log_norm (F := F),
        integral_smul_nnreal_measure, hmellin]
      rfl

open Classical in
/-- Paper: §1.4.1, p. 28. The archimedean term is the ordinary local integral
on tests vanishing at norm one.
Deviation: As in the corrected `traceFormula`, the denominator uses the normalized
local absolute value of `1 - u`, and the weight is the square root of the
normalized norm of `u`. The displayed real denominator uses the positive sign
even for the negative branch. The displayed complex denominator is unsquared. -/
def introTraceArchimedean (χ : U𝔽) (h : ℝ → ℂ) (w : InfinitePlace F) : ℂ :=
  (if w.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ))) *
    ∫ u, archIntegrand(χ, h, w) u ∂infiniteLocalMultiplicativeTamagawaMeasure F w

private theorem introTraceArchimedean_real_bound (w : InfinitePlace F) (hw : w.IsReal)
    (φ : BruhatCompactSupport w.Completionˣ) (hφ : φ.val 1 = 0) :
    ∃ C : ℝ, ∀ u : w.Completionˣ,
      ‖φ.val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ)‖ ≤ C * ‖u.val‖ := by
  let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let r := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  obtain ⟨A, hA⟩ := exists_infiniteWeilTestMap w
  -- The real Mellin comparison supplies the ordinary Schwartz representative of the weighted test.
  obtain ⟨s, he, _⟩ := realArchimedeanMellin_eq_infiniteLocalIdelicZFunction w hw (A φ)
  have hmult : w.mult = 1 := by simp [InfinitePlace.mult, hw]
  have hval (u : w.Completionˣ) :
      s (e (u.val - 1)) = φ.val u / (Real.sqrt ‖u.val‖ : ℂ) := by
    refine (he _).trans ((hA φ (u.val - 1)).trans ?_)
    change Function.extend Units.val (φ.val : _ → ℂ) (fun _ ↦ 0) (1 + (u.val - 1)) / _ = _
    simp only [show 1 + (u.val - 1) = u.val by ring, Units.val_injective.extend_apply, hmult, pow_one]
  have hz : s 0 = 0 := by
    have h := hval 1
    simpa [show e 0 = 0 from map_zero r, hφ] using h
  -- Vanishing at one becomes vanishing at zero after the weighted translation.
  let C := SchwartzMap.seminorm ℝ 0 1 s
  have hlip (t : ℝ) : ‖s t‖ ≤ C * ‖t‖ := by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := s) (s := univ) (C := C)
      (fun x _ ↦ s.differentiableAt) (fun x _ ↦ ?_) convex_univ (mem_univ 0) (mem_univ t)
    · simpa [hz] using h
    · rw [← norm_iteratedFDeriv_one]
      exact s.norm_iteratedFDeriv_le_seminorm ℝ 1 x
  refine ⟨C, fun u ↦ ?_⟩
  have he_norm (x : w.Completion) : ‖e x‖ = ‖x‖ :=
    e.isometry.norm_map_of_map_zero (map_zero r) x
  have h := hlip (e (u.val - 1))
  rw [hval, he_norm, norm_sub_rev u.val 1] at h
  have hr : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
  have hs : 0 < Real.sqrt ‖u.val‖ := Real.sqrt_pos.mpr hr
  simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.le,
    abs_of_nonneg (norm_nonneg _)] at h ⊢
  by_cases hu : 1 - u.val = 0
  · simp [hu, mul_nonneg (show 0 ≤ C from apply_nonneg _ _) hr.le]
  · refine (div_le_iff₀ (norm_pos_iff.mpr hu)).mpr ?_
    have hh := (div_le_iff₀ hs).mp h
    calc
      ‖φ.val u‖ * Real.sqrt ‖u.val‖ ≤
          (C * ‖1 - u.val‖ * Real.sqrt ‖u.val‖) * Real.sqrt ‖u.val‖ :=
        mul_le_mul_of_nonneg_right hh hs.le
      _ = C * ‖u.val‖ * ‖1 - u.val‖ := by
        rw [mul_assoc (C * ‖1 - u.val‖), Real.mul_self_sqrt hr.le]
        ring

private theorem introTraceArchimedean_real_integrable (w : InfinitePlace F) (hw : w.IsReal)
    (φ : BruhatCompactSupport w.Completionˣ) (hφ : φ.val 1 = 0) :
    Integrable (fun u : w.Completionˣ ↦
      φ.val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ))
      (infiniteLocalMultiplicativeTamagawaMeasure F w) := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
    infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  obtain ⟨C, hC⟩ := introTraceArchimedean_real_bound w hw φ hφ
  have hc : Continuous φ.val := schwartzBruhat_continuous
    (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat w.Completionˣ)
  have hdom : Continuous (fun u : w.Completionˣ ↦ C * ‖u.val‖) := by fun_prop
  have hK : IsCompact (tsupport φ.val) := φ.property.2
  apply Integrable.mono' ((hdom.continuousOn.integrableOn_compact hK).integrable_indicator
    hK.measurableSet)
  · have hn : Measurable (fun u : w.Completionˣ ↦ ((‖1 - u.val‖ : ℝ) : ℂ)) := by fun_prop
    exact ((hc.measurable.mul (by fun_prop)).div hn).aestronglyMeasurable
  · refine .of_forall fun u ↦ ?_
    by_cases hu : u ∈ tsupport φ.val
    · simpa only [indicator_of_mem hu] using hC u
    · simp only [indicator_of_notMem hu, image_eq_zero_of_notMem_tsupport hu,
        zero_mul, zero_div, norm_zero, le_refl]

/-- Paper: §1.4.1, p. 28. At a real place this integral is the local
Connes–Weil term of a compactly supported Bruhat test vanishing at norm one.
Deviation: The denominator on the negative real component is `1 + t` at `u = -t`,
as in the local kernel of the first display on p. 28. The character-by-character
display there prints `|1 - t|` on both components. -/
theorem introTraceArchimedean_eq_realPrincipalValue (χ : U𝔽) (h : ℝ → ℂ)
    (_hh : h 1 = 0) (w : InfinitePlace F) (_hw : w.IsReal)
    (φ : BruhatCompactSupport w.Completionˣ)
    (_hφ : ∀ u, φ.val u = introTraceTest χ h (archClass(w) u)) :
    Integrable archIntegrand(χ, h, w) (infiniteLocalMultiplicativeTamagawaMeasure F w) ∧
      introTraceArchimedean χ h w = infiniteConnesWeilPrincipalValue w φ := by
  have hzero : φ.val 1 = 0 := by simp [_hφ, introTraceTest, _hh]
  have hm : w.mult = 1 := by simp [InfinitePlace.mult, _hw]
  constructor
  · simpa only [_hφ, hm, pow_one] using introTraceArchimedean_real_integrable w _hw φ hzero
  · rw [realConnesWeilPrincipalValue_of_apply_one_zero w _hw φ hzero]
    simp only [introTraceArchimedean, ite_eq_left _hw, hm, pow_one, _hφ]

open Classical in
/-- Paper: §1.4.1, p. 28. The finite term at a place is a sum over the positive
and negative prime-power shells.
Deviation: Averaging over local integer units annihilates ramified characters.
At unramified places the uniformizer value uses the library's Euler convention. -/
def introTracePrimePower (χ : U𝔽) (h : ℝ → ℂ) (v : V) (k : ℕ) : ℂ :=
  let c := ideleClassNormTwist χ 0
  let m := k + 1
  if c.IsUnramifiedAt v then
    (Real.log q(v) : ℂ) *
      (c.localValue v ^ m * h (q(v) ^ m) + star (c.localValue v) ^ m * h ((q(v) ^ m)⁻¹)) /
      (q(v) : ℂ) ^ ((m : ℂ) / 2)
  else 0

/-- Paper: §1.4.1, p. 28. The two shells of exponent one for the trivial
character have coefficient `log(q)/sqrt(q)`. -/
theorem introTracePrimePower_one_first (h : ℝ → ℂ) (v : V) :
    introTracePrimePower (1 : U𝔽) h v 0 =
      (Real.log q(v) : ℂ) * (h q(v) + h (q(v)⁻¹)) / (q(v) : ℂ) ^ (1 / 2 : ℂ) := by
  classical
  have htriv : ideleClassNormTwist (1 : U𝔽) 0 = 1 := by
    ext1 g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hunit (u : (v.adicCompletion F)ˣ) :
      (1 : HeckeCharacter (𝓞 F) F).restrict v u = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hur : (1 : HeckeCharacter (𝓞 F) F).IsUnramifiedAt v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦
      hunit (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x)
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hv : (1 : HeckeCharacter (𝓞 F) F).localValue v = 1 := hunit u
  simp [introTracePrimePower, htriv, hur, hv]

/-- Paper: §1.4.1, p. 28. The spectral side sums the full zero orders in the
selected character and the open window centered at one half. -/
def introTraceSpectralSum (χ : U𝔽) (h : ℝ → ℂ) (a : ℝ) : ℂ :=
  ∑' ρ : windowZeros(χ, a), (zeroOrder(χ, ρ.val) : ℂ) * introTraceMellin h (ρ.val - 1 / 2)

/-- Paper: §1.4.1, p. 28. A window containing exactly one zero gives its
multiplicity times the radial Mellin moment at that zero's shifted parameter. -/
theorem introTraceSpectralSum_eq_single (χ : U𝔽) (h : ℝ → ℂ) (a : ℝ) (ρ : ℂ)
    (_hρ : 0 < zeroOrder(χ, ρ) ∧ |ρ.re - 1 / 2| < a)
    (_honly : ∀ w : windowZeros(χ, a), w.val = ρ) :
    introTraceSpectralSum χ h a =
      (zeroOrder(χ, ρ) : ℂ) * introTraceMellin h (ρ - 1 / 2) := by
  let w : windowZeros(χ, a) := ⟨ρ, _hρ⟩
  unfold introTraceSpectralSum
  exact tsum_eq_single w fun v hv ↦ (hv (Subtype.ext (_honly v))).elim

/-- Compact support along the norm section bounds both the radial variable and its inverse. -/
private theorem introTrace_characterTrace_radial_bound (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (h : ℝ → ℂ) (φ : D𝔽)
    (hφ : ∀ g, φ.val g = introTraceTest χ h g) :
    ∃ B : ℕ, ∀ x : ℝ, 0 < x → h x ≠ 0 → max x x⁻¹ ≤ B := by
  let mag (g : C𝔽) : ℝ := max N(g) N(g⁻¹)
  have hmag : Continuous mag := by
    have hm := (isProperMap_ideleClassNorm F).continuous
    dsimp only [mag]
    fun_prop
  obtain ⟨R, hR⟩ := (φ.property.2.image hmag).bddAbove
  obtain ⟨B, hB⟩ := exists_nat_ge R
  refine ⟨B, fun x hx hn ↦ ?_⟩
  let t : ℝ≥0ˣ := Units.mk0 (⟨x, hx.le⟩ : ℝ≥0) (by intro e; exact hx.ne' (congrArg NNReal.toReal e))
  have ht : N(τ t) = x := by rw [hτ]; rfl
  have hti : N((τ t)⁻¹) = x⁻¹ := by rw [map_inv, hτ]; rfl
  have hs : τ t ∈ tsupport φ.val := subset_tsupport _ (show φ.val (τ t) ≠ 0 by
    rw [hφ, introTraceTest, ht]; exact mul_ne_zero (by simp) hn)
  have hr := hR (mem_image_of_mem mag hs)
  simpa [mag, ht, hti] using hr.trans hB

/-- Only finitely many prime powers can meet the bounded radial support of the adelic test. -/
private theorem introTrace_characterTrace_primes_summable (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (h : ℝ → ℂ) (φ : D𝔽)
    (hφ : ∀ g, φ.val g = introTraceTest χ h g) :
    Summable (fun p : V × ℕ ↦ introTracePrimePower χ h p.1 p.2) := by
  classical
  obtain ⟨B, hB⟩ := introTrace_characterTrace_radial_bound τ hτ χ h φ hφ
  have hfin : {v : V | v.asIdeal.absNorm ≤ B}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) B).preimage
      HeightOneSpectrum.asIdeal_injective.injOn
  apply summable_of_hasFiniteSupport
  refine (hfin.prod (Set.finite_Iic B)).subset ?_
  rintro ⟨v, k⟩ hnon
  let m := k + 1
  let n := v.asIdeal.absNorm
  have hn : 1 < n := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hnm : 0 < q(v) ^ m := pow_pos (by exact_mod_cast hn.pos) _
  have hbound : n ^ m ≤ B := by
    by_contra! hb
    have hb' : (B : ℝ) < q(v) ^ m := by exact_mod_cast hb
    have h₁ : h (q(v)^m) = 0 := by
      by_contra hne
      exact hb'.not_ge ((le_max_left _ _).trans (hB _ hnm hne))
    have h₂ : h ((q(v)^m)⁻¹) = 0 := by
      by_contra hne
      have hh := (le_max_right _ _).trans (hB _ (inv_pos.mpr hnm) hne)
      rw [inv_inv] at hh
      exact hb'.not_ge hh
    apply hnon
    change introTracePrimePower χ h v k = 0
    simp [introTracePrimePower, ← show m = k + 1 from rfl, h₁, h₂]
  have hq : n ≤ n ^ m := by simpa using Nat.pow_le_pow_right hn.le (show 1 ≤ m by dsimp [m]; omega)
  have he : k ≤ n ^ m := by
    have hk : k < 2 ^ k := Nat.lt_two_pow_self
    have ht : 2 ^ k ≤ n ^ m := (Nat.pow_le_pow_left (by omega : 2 ≤ n) _).trans
      (Nat.pow_le_pow_right hn.le (by dsimp [m]; omega))
    omega
  exact ⟨hq.trans hbound, he.trans hbound⟩

/-- The integer-unit translate of an integrand with a nontrivial character
has integral zero under multiplicative Haar measure. -/
private theorem introTrace_characterTrace_integral_zero {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (W : G → ℂ) (a : G) (c : ℂ)
    (hc : c ≠ 1) (hW : ∀ g, W (a * g) = c * W g) : (∫ g, W g ∂μ) = 0 := by
  have hi : (∫ g, W g ∂μ) = c * ∫ g, W g ∂μ := by
    calc
      _ = ∫ g, W (a * g) ∂μ := (integral_mul_left_eq_self (μ := μ) W a).symm
      _ = _ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ hW)
  exact (mul_eq_zero.mp (show (1 - c) * (∫ g, W g ∂μ) = 0 by linear_combination hi)).resolve_left
    (fun he ↦ hc (sub_eq_zero.mp he).symm)

/-- The norm-one Tamagawa volume is finite and nonzero. -/
private theorem introTrace_characterTrace_volume :
    τVolume ≠ 0 := by
  have hvol := normOneIdeleClassTamagawaMeasure_volume (F := F)
  have hc0 : normOneIdeleClassTamagawaMeasure F univ ≠ 0 := by
    rw [hvol, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := NumberField.Units.regulator_pos F
    have := NumberField.classNumber_pos F
    have := NumberField.Units.torsionOrder_pos F
    have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
    positivity
  have hct : normOneIdeleClassTamagawaMeasure F univ ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩)

open Classical in

/-- A norm-one translation annihilates the Mellin integral of the radial test
against every other character trivial on the chosen norm section. In its own
character the integral is the radial Mellin moment times the norm-one volume. -/
private theorem introTrace_characterTrace_mellin (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ η : U𝔽) (hχ : ∀ t, χ (τ t) = 1)
    (hη : ∀ t, η (τ t) = 1) (h : ℝ → ℂ) (φ : D𝔽)
    (hφ : ∀ g, φ.val g = introTraceTest χ h g) (s : ℂ) :
    (∫ g, φ.val g * ideleClassNormTwist η s g ∂(ideleClassTamagawaMeasure F)) =
      if η = χ then τVolume * introTraceMellin h s else 0 := by
  classical
  split_ifs with hsame
  · subst η
    exact (introTraceTest_mellin χ h φ hφ s).2
  · obtain ⟨y, hy⟩ : ∃ y, η y ≠ χ y :=
      not_forall.mp (fun h ↦ hsame (DFunLike.ext _ _ h))
    let u : (ideleClassNorm F).ker := ⟨y * (τ (ideleClassNorm F y))⁻¹, by
      change ideleClassNorm F _ = 1
      rw [map_mul, map_inv, hτ, mul_inv_cancel]⟩
    have huχ : χ u.val = χ y := by simp [u, hχ]
    have huη : η u.val = η y := by simp [u, hη]
    let d : ℂ := star (χ u.val : ℂ) * (η u.val : ℂ)
    have hd : d ≠ 1 := by
      intro hd
      have hunit : (χ u.val : ℂ) * star (χ u.val : ℂ) = 1 := by
        simp [← Circle.coe_inv_eq_conj]
      have he : (η u.val : ℂ) = (χ u.val : ℂ) := by
        dsimp only [d] at hd
        linear_combination (χ u.val : ℂ) * hd - (η u.val : ℂ) * hunit
      exact hy (Subtype.ext (by simpa only [huχ, huη] using he))
    let W (x : C𝔽) := φ.val x * ideleClassNormTwist η s x
    have hW (x : C𝔽) : W (x * u.val) = d * W x := by
      have ht : ideleClassNormTwist η s u.val = (η u.val : ℂ) := by
        change (η u.val : ℂ) * ((N(u.val) : ℂ) ^ s) = _
        simp [show ideleClassNorm F u.val = 1 from u.property]
      simp only [W, d, map_mul, ht, hφ, introTraceTest_mul_normOne]
      ring
    exact introTrace_characterTrace_integral_zero (ideleClassTamagawaMeasure F) W u.val d hd
      (fun x ↦ (congrArg W (mul_comm u.val x)).trans (hW x))

open Classical in

/-- Restrict the global zero sum to the chosen isotype. Orthogonality makes every
term off the embedded single-character window zero, and the same norm-one
volume multiplies all remaining moments. -/
private theorem introTrace_characterTrace_isotype (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1)
    (h : ℝ → ℂ) (φ : D𝔽) (hφ : ∀ g, φ.val g = introTraceTest χ h g) (a : ℝ) (T : ℂ)
    (hS : HasSum (fun z : {p : {η : U𝔽 // ∀ t, η (τ t) = 1} × ℂ //
        0 < zeroOrder(p.1.val, p.2) ∧ |p.2.re - 1 / 2| < a} ↦
      (zeroOrder(z.val.1.val, z.val.2) : ℂ) *
        ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2) g ∂ideleClassTamagawaMeasure F)
      ((∫ g, φ.val g * ideleClassNormTwist (1 : U𝔽) (1 / 2) g ∂ideleClassTamagawaMeasure F) +
       (∫ g, φ.val g * ideleClassNormTwist (1 : U𝔽) (-1 / 2) g ∂ideleClassTamagawaMeasure F) - τVolume * T)) :
    HasSum (fun ρ : windowZeros(χ, a) ↦
      (zeroOrder(χ, ρ.val) : ℂ) * introTraceMellin h (ρ.val - 1 / 2))
      ((if χ = 1 then introTraceMellin h (1 / 2) + introTraceMellin h (-1 / 2) else 0) - T) := by
  classical
  let A := {p : {η : U𝔽 // ∀ t, η (τ t) = 1} × ℂ //
    0 < zeroOrder(p.1.val, p.2) ∧ |p.2.re - 1 / 2| < a}
  let ι (ρ : windowZeros(χ, a)) : A := ⟨(⟨χ, hχ⟩, ρ.val), ρ.property⟩
  have hi : Injective ι := fun _ _ h ↦ Subtype.ext (congrArg (fun z : A ↦ z.val.2) h)
  let mom (η : U𝔽) (s : ℂ) := ∫ g, φ.val g * ideleClassNormTwist η s g ∂ideleClassTamagawaMeasure F
  let term (z : A) := (zeroOrder(z.val.1.val, z.val.2) : ℂ) * mom z.val.1.val (z.val.2 - 1 / 2)
  have hm (η : U𝔽) (hη : ∀ t, η (τ t) = 1) (s : ℂ) :
      mom η s = if η = χ then τVolume * introTraceMellin h s else 0 :=
    introTrace_characterTrace_mellin τ hτ χ η hχ hη h φ hφ s
  have hoff (z : A) (hz : z ∉ range ι) : term z = 0 := by
    have hne : z.val.1.val ≠ χ := by
      rintro he
      refine hz ⟨⟨z.val.2, he ▸ z.property⟩, ?_⟩
      exact Subtype.ext (Prod.ext (Subtype.ext he.symm) rfl)
    simp only [term, hm _ z.val.1.property, ite_eq_right hne, mul_zero]
  have hnorm := (hi.hasSum_iff (f := term) hoff).mpr hS
  have hvol := introTrace_characterTrace_volume (F := F)
  have hscalar := hnorm.mul_left τVolume⁻¹
  have hv : τVolume⁻¹ * (mom 1 (1 / 2) + mom 1 (-1 / 2) - τVolume * T) =
      (if χ = 1 then introTraceMellin h (1 / 2) + introTraceMellin h (-1 / 2) else 0) - T := by
    rw [hm 1 (fun _ ↦ rfl), hm 1 (fun _ ↦ rfl)]
    by_cases h1 : χ = 1
    · subst χ
      simp only [ite_true]
      field_simp
    · simp only [ite_eq_right h1, ite_eq_right (Ne.symm h1)]
      field_simp
      ring
  rw [← hv]
  refine hscalar.congr_fun fun ρ ↦ ?_
  change _ = τVolume⁻¹ * ((zeroOrder(χ, ρ.val) : ℂ) * mom χ (ρ.val - 1 / 2))
  rw [hm χ hχ, ite_eq_left rfl]
  field_simp

/-- A Euclidean presentation transports an additive Bruhat test to an ordinary Schwartz function. -/
private theorem introTrace_characterTrace_euclidean_model
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    [LocallyCompactSpace A] {n : ℕ}
    (v : A ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin n))) (g : SchwartzBruhat A) :
      ∃ s : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ∀ x, s (v x).toAdd = g x := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let P := ElementaryLieGroup n 0 0 PUnit
  let D := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit
  let : Unique D := uniqueOfSubsingleton 0
  let p : Multiplicative E ≃ₜ* Multiplicative P :=
    { toMulEquiv := (AddEquiv.prodUnique (M := E) (N := D)).symm.toMultiplicative
      continuous_toFun := (continuous_id.prodMk continuous_const :
        Continuous (fun x : E ↦ (x, (default : D))))
      continuous_invFun := (continuous_fst : Continuous (Prod.fst : E × D → E)) }
  let e : ElementaryLCAPresentation A :=
    { realDim := n, torusDim := 0, latticeRank := 0, finiteFactor := PUnit, equiv := v.trans p }
  have hA := (lca_elementary_iff (G := A)).mpr ⟨e⟩
  let i : (⊤ : Subgroup A) ≃ₜ* A :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair A := ⟨(⊤, OrderDual.toDual ⊥), by simp,
    isCompactlyGeneratedGroup_of_continuousMulEquiv i.symm hA.1,
    isBruhatGoodSubgroup_bot_iff.mpr hA.2, bot_le⟩
  let q₀ : A →* a.quotient := (QuotientGroup.mk' _).comp i.symm.toMulEquiv.toMonoidHom
  have hq₀ : IsOpenQuotientMap q₀ :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.symm.toHomeomorph.isOpenQuotientMap
  have hinj : Injective q₀ := (MonoidHom.ker_eq_bot_iff q₀).mp (eq_bot_iff.mpr fun x hx ↦ by
    exact (a.quotient_mk_eq_one (i.symm x)).mp hx)
  let q := (MulEquiv.ofBijective q₀ ⟨hinj, hq₀.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hq₀.isQuotientMap.isOpen_preimage)
  let e₀ : ElementaryLCAPresentation a.quotient := { e with equiv := q.symm.trans e.equiv }
  have hreal (s : SchwartzBruhatStage e₀) (x : A) :
      schwartzBruhatStageRealization a e₀ s x = s ((v x).toAdd, 0, 0, PUnit.unit) := by
    have hx : x ∈ a.val.1 := Subgroup.mem_top x
    rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
    change s ((e₀.equiv (q x)).toAdd) = _
    change s ((e.equiv (q.symm (q x))).toAdd) = _
    rw [q.symm_apply_apply]
    rfl
  have hrange : schwartzBruhatSubmodule A ≤ (schwartzBruhatStageRealization a e₀).range := by
    refine iSup_le fun b ↦ iSup_le fun eb ↦ ?_
    rintro _ ⟨sb, rfl⟩
    obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition (show b ≤ a from ⟨le_top, le_top⟩) eb e₀
    exact ⟨j sb, hj sb⟩
  obtain ⟨s, hs⟩ := hrange g.property
  let f : E → ℂ := fun x ↦ s (x, 0, 0, PUnit.unit)
  have hs' (y : P) : f y.1 = s y :=
    congrArg (fun z : P ↦ s z) (Prod.ext rfl (Subsingleton.elim _ _))
  have hf : (fun y : P ↦ f y.1) ∈ elementarySchwartzSubmodule n 0 0 PUnit :=
    (funext hs').symm ▸ s.property
  obtain ⟨S, hS⟩ := (elementarySchwartzSubmodule_real_iff f).mp hf
  refine ⟨S, fun x ↦ ?_⟩
  exact (congrFun hS (v x).toAdd).trans
    ((hreal s x).symm.trans (congrFun hs x))

/-- In the complex coordinate of an infinite place the additive test is a classical Schwartz function. -/
private theorem introTrace_characterTrace_complex_model (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion)) :
    ∃ g : SchwartzMap ℂ ℂ, ∀ z : ℂ,
      g z = f (Multiplicative.ofAdd ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z)) := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let L : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ ℂ)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let v : Multiplicative w.Completion ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin (Module.finrank ℝ ℂ))) :=
    { toMulEquiv := (e.toAddEquiv.trans L.toLinearEquiv.toAddEquiv).toMultiplicative
      continuous_toFun := L.continuous.comp j.continuous
      continuous_invFun := j.symm.continuous.comp L.symm.continuous }
  let : LocallyCompactSpace (Multiplicative w.Completion) := v.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : T2Space (Multiplicative w.Completion) := v.toHomeomorph.isEmbedding.t2Space
  obtain ⟨s, hs⟩ := introTrace_characterTrace_euclidean_model v f
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L s, fun z ↦ ?_⟩
  have hz := hs (Multiplicative.ofAdd (e.symm z))
  change s (L (e (e.symm z))) = _ at hz
  change s (L z) = f (Multiplicative.ofAdd (e.symm z))
  simpa only [RingEquiv.apply_symm_apply] using hz

/-- A Schwartz test vanishing at zero is integrable against the reciprocal squared radius in the plane. -/
private theorem introTrace_characterTrace_schwartz_integrable_div_square (g : SchwartzMap ℂ ℂ)
    (hg : g 0 = 0) : Integrable (fun z : ℂ ↦ g z / ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
  let C := SchwartzMap.seminorm ℝ 0 1 g
  have hlip (z : ℂ) : ‖g z‖ ≤ C * ‖z‖ := by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := g) (s := univ) (C := C)
      (fun z _ ↦ g.differentiableAt) (fun z _ ↦ ?_) convex_univ (mem_univ 0) (mem_univ z)
    · simpa [hg] using h
    · rw [← norm_iteratedFDeriv_one]
      exact g.norm_iteratedFDeriv_le_seminorm ℝ 1 z
  let B := Metric.ball (0 : ℂ) 1
  have hi : IntegrableOn (fun z : ℂ ↦ ‖z‖⁻¹) B := by
    rw [integrableOn_fun_norm_addHaar (μ := volume) (f := fun y : ℝ ↦ y⁻¹), Complex.finrank_real_complex]
    refine (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun (fun y (hy : y ∈ Ioo 0 1) ↦ ?_)
      measurableSet_Ioo
    simp [smul_eq_mul, hy.1.ne']
  have hiB := (integrable_indicator_iff (show MeasurableSet B from measurableSet_ball)).mpr (hi.const_mul C)
  refine (hiB.add g.integrable.norm).mono'
    (g.continuous.measurable.div (by fun_prop)).aestronglyMeasurable (.of_forall fun z ↦ ?_)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  by_cases hz : z ∈ B
  · rw [indicator_of_mem hz]
    refine (le_add_of_nonneg_right (norm_nonneg _)).trans' ?_
    rcases eq_or_ne z 0 with rfl | hn
    · simp
    have hp : 0 < ‖z‖ := norm_pos_iff.mpr hn
    calc ‖g z‖ / ‖z‖ ^ 2 ≤ (C * ‖z‖) / ‖z‖ ^ 2 := by gcongr; exact hlip z
      _ = C * ‖z‖⁻¹ := by field_simp
  · rw [indicator_of_notMem hz, zero_add]
    have h1 : 1 ≤ ‖z‖ := le_of_not_gt fun h ↦ hz (mem_ball_zero_iff.mpr h)
    exact div_le_self (norm_nonneg _) (by nlinarith)

/-- At a complex place, vanishing at zero removes the finite-part cutoff. -/
private theorem introTrace_characterTrace_complex_add (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion)) (hf : f (Multiplicative.ofAdd 0) = 0) :
    letI : MeasurableSpace w.Completion := borel _
    Integrable (fun x ↦ f (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ)) (infiniteLocalAdditiveTamagawaMeasure F w) ∧
    infiniteConnesPrincipalValue w f = (1 / (2 * (Real.pi : ℂ))) *
      ∫ x, f (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂(infiniteLocalAdditiveTamagawaMeasure F w) := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let m := j.symm.toHomeomorph.toMeasurableEquiv
  obtain ⟨g, hg⟩ := introTrace_characterTrace_complex_model w hw f
  have hz : e.symm 0 = 0 := map_zero e.symm
  have hi := introTrace_characterTrace_schwartz_integrable_div_square g
    (by rw [hg, hz]; exact hf)
  have hμ : (infiniteLocalAdditiveTamagawaMeasure F w) = (2 • (volume : Measure ℂ)).map m :=
    dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)
  have hG : Integrable (fun x ↦ f (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ)) (infiniteLocalAdditiveTamagawaMeasure F w) := by
    rw [hμ, integrable_map_equiv]
    have hsc : Integrable (fun z : ℂ ↦ g z / ((‖z‖ ^ 2 : ℝ) : ℂ)) (2 • volume) := by
      simpa only [two_smul] using hi.add_measure hi
    refine hsc.congr (ae_of_all _ fun z ↦ ?_)
    change g z / _ = f (Multiplicative.ofAdd (e.symm z)) / _
    rw [hg, show ‖m z‖ = ‖z‖ from j.symm.isometry.norm_map_of_map_zero (map_zero e.symm) z]
  refine ⟨hG, ?_⟩
  have hT := ((exists_infiniteConnesPrincipalValue w).choose_spec f).2
  change infiniteConnesPrincipalValue w f = _ at hT
  have hL := (complexLogFourier_finitePart w hw f).2.2
  simp only [hf, mul_zero, zero_mul, add_zero] at hL
  have hm (ε : ℝ) : MeasurableSet {x : w.Completion | ε ≤ ‖x‖ ^ 2} :=
    measurableSet_le measurable_const (measurable_norm.pow_const _)
  have hlim : Tendsto (fun ε : ℝ ↦ ∫ x in {x : w.Completion | ε ≤ ‖x‖ ^ 2},
      f (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂(infiniteLocalAdditiveTamagawaMeasure F w)) (𝓝[>] 0)
      (𝓝 (∫ x, f (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂(infiniteLocalAdditiveTamagawaMeasure F w))) := by
    simp_rw [← integral_indicator (hm _)]
    refine tendsto_integral_filter_of_dominated_convergence _
      (.of_forall fun ε ↦ hG.aestronglyMeasurable.indicator (hm ε))
      (.of_forall fun ε ↦ .of_forall fun x ↦ norm_indicator_le_norm_self _ _)
      hG.norm (.of_forall fun x ↦ ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Set.indicator_apply]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (sq_pos_of_pos (norm_pos_iff.mpr hx)))] with ε hε
      rw [indicator_of_mem (show ε ≤ ‖x‖ ^ 2 from hε.le)]
  rw [hT, tendsto_nhds_unique hlim hL]
  push_cast
  field_simp

/-- Multiplicative Haar integration at a complex place uses the inverse squared radius. -/
private theorem introTrace_characterTrace_complex_haar (w : InfinitePlace F) (hw : w.IsComplex)
    (g : w.Completion → ℂ) :
    letI : MeasurableSpace w.Completion := borel _
    (Integrable (fun u : w.Completionˣ ↦ g u.val) (infiniteLocalMultiplicativeTamagawaMeasure F w) ↔
      Integrable (fun y ↦ (‖y‖ ^ 2)⁻¹ • g y) (infiniteLocalAdditiveTamagawaMeasure F w)) ∧
      ∫ u : w.Completionˣ, g u.val ∂(infiniteLocalMultiplicativeTamagawaMeasure F w) = ∫ y, (‖y‖ ^ 2)⁻¹ • g y ∂(infiniteLocalAdditiveTamagawaMeasure F w) := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  let d : w.Completion → ENNReal := fun y ↦ (↑(‖y‖₊ ^ w.mult) : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  have hdlt : ∀ᵐ y ∂((infiniteLocalAdditiveTamagawaMeasure F w).restrict (range (Units.val : w.Completionˣ → w.Completion))), d y < ⊤ := by
    refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    exact ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr (pow_pos (nnNorm_pos.mpr (hu ▸ u.ne_zero)) _))
  have hdy (y : w.Completion) : (d y).toReal = (‖y‖ ^ 2)⁻¹ := by
    simp [d, hw.mult_eq_two]
  have hs : support (fun y ↦ (‖y‖ ^ 2)⁻¹ • g y) ⊆ range (Units.val : w.Completionˣ → w.Completion) := by
    intro y hy
    have hn : y ≠ 0 := by rintro rfl; simp at hy
    exact ⟨Units.mk0 y hn, rfl⟩
  change (Integrable (g ∘ Units.val) (((infiniteLocalAdditiveTamagawaMeasure F w).withDensity d).comap Units.val) ↔ _) ∧
    ∫ u : w.Completionˣ, g u.val ∂(((infiniteLocalAdditiveTamagawaMeasure F w).withDensity d).comap Units.val) = _
  constructor
  · rw [← hval.integrable_map_iff (g := g), hval.map_comap, restrict_withDensity hval.measurableSet_range,
      integrable_withDensity_iff_integrable_smul' hd hdlt,
      ← integrableOn_iff_integrable_of_support_subset hs]
    simp_rw [hdy]
    rfl
  · rw [← hval.integral_map (g := g), hval.map_comap,
      setIntegral_withDensity_eq_setIntegral_toReal_smul hd hdlt _ hval.measurableSet_range,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := range Units.val)
        (fun y hy ↦ Function.notMem_support.mp (fun h ↦ hy (hs h)))]
    simp_rw [hdy]

/-- A test vanishing at one gives the ordinary integrable complex-place kernel, normalized by 1/(2π). -/
private theorem introTrace_characterTrace_complex_place (w : InfinitePlace F) (hw : w.IsComplex)
    (f : BruhatCompactSupport w.Completionˣ) (hf : f.val 1 = 0) :
    Integrable (fun u : w.Completionˣ ↦ f.val u * (Real.sqrt (‖u.val‖ ^ w.mult) : ℂ) /
      ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)) (infiniteLocalMultiplicativeTamagawaMeasure F w) ∧
    infiniteConnesWeilPrincipalValue w f = (1 / (2 * (Real.pi : ℂ))) *
      ∫ u : w.Completionˣ, f.val u * (Real.sqrt (‖u.val‖ ^ w.mult) : ℂ) /
        ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ) ∂(infiniteLocalMultiplicativeTamagawaMeasure F w) := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : ((infiniteLocalAdditiveTamagawaMeasure F w)).IsAddHaarMeasure := infiniteLocalAdditiveTamagawaMeasure_haar F w
  let A := (exists_infiniteWeilTestMap w).choose
  let Fz : w.Completion → ℂ := Function.extend Units.val (f.val : _ → ℂ) (fun _ ↦ 0)
  have hA (x : w.Completion) : (A f) (Multiplicative.ofAdd x) = Fz (1 + x) /
      (Real.sqrt (‖1 + x‖ ^ w.mult) : ℂ) := (exists_infiniteWeilTestMap w).choose_spec f x
  have hFu (u : w.Completionˣ) : Fz u.val = f.val u := Units.val_injective.extend_apply _ _ u
  have h0 : (A f) (Multiplicative.ofAdd 0) = 0 := by
    rw [hA]
    rw [add_zero, ← Units.val_one, hFu, hf, zero_div]
  let Q (y : w.Completion) := Fz y * (‖y‖ : ℂ) / ((‖1 - y‖ ^ 2 : ℝ) : ℂ)
  let H (y : w.Completion) := (‖y‖ ^ 2)⁻¹ • Q y
  have hPH (x : w.Completion) : (A f) (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ) = H (1 + x) := by
    rw [hA]
    change Fz (1 + x) / (Real.sqrt (‖1 + x‖ ^ w.mult) : ℂ) / _ = (‖1 + x‖ ^ 2)⁻¹ •
      (Fz (1 + x) * (‖1 + x‖ : ℂ) / ((‖1 - (1 + x)‖ ^ 2 : ℝ) : ℂ))
    rw [hw.mult_eq_two, Real.sqrt_sq (norm_nonneg _), sub_add_cancel_left, norm_neg, Complex.real_smul]
    push_cast
    by_cases hz : ‖1 + x‖ = 0
    · simp [hz]
    · have hn : (‖1 + x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      field_simp
  have hQ : (fun u : w.Completionˣ ↦ f.val u * (Real.sqrt (‖u.val‖ ^ w.mult) : ℂ) /
      ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)) = fun u : w.Completionˣ ↦ Q u.val := by
    funext u
    dsimp only [Q]
    rw [hw.mult_eq_two, Real.sqrt_sq (norm_nonneg _), hFu]
  obtain ⟨hi, he⟩ := introTrace_characterTrace_complex_add w hw (A f) h0
  rw [show (fun x ↦ (A f) (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ)) = fun x ↦ H (1+x) from funext hPH] at hi he
  have hHI : Integrable H (infiniteLocalAdditiveTamagawaMeasure F w) :=
    (hi.comp_add_left (-1)).congr (ae_of_all _ fun x ↦ congrArg H (add_neg_cancel_left 1 x))
  rw [hQ]
  refine ⟨(introTrace_characterTrace_complex_haar w hw Q).1.mpr hHI, ?_⟩
  change infiniteConnesPrincipalValue w (A f) = _
  rw [he, integral_add_left_eq_self, (introTrace_characterTrace_complex_haar w hw Q).2]

/-- In a sum over the valuation lattice, group the shells of valuations
`k + 1` and `-(k + 1)` when the central shell contributes zero. -/
private theorem introTrace_characterTrace_paired (I : ℤ → ℂ) {z : ℂ} (h : HasSum I z)
    (h0 : I 0 = 0) : HasSum (fun k : ℕ ↦ I (k + 1) + I (-(k + 1))) z := by
  have h' : HasSum (fun n : ℕ ↦ I n + I (-n)) z := by simpa [h0] using h.nat_add_neg
  simpa [h0] using (hasSum_nat_add_iff' 1).mpr h'

/-- The noncentral ultrametric denominator depends only on the norm. -/
private theorem introTrace_characterTrace_ultrametric {K : Type*} [NormedField K]
    [IsUltrametricDist K] (u : K) (hu : ‖u‖ ≠ 1) : ‖1 - u‖ = max 1 ‖u‖ := by
  have hn : ‖(1 : K)‖ ≠ ‖-u‖ := by simpa using hu.symm
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hn

/-- The two noncentral valuations give reciprocal square-root weights, both
with denominator q to the half power. -/
private theorem introTrace_characterTrace_sqrt (q : ℝ) (hq : 0 < q) (m : ℕ) :
    ((Real.sqrt (q ^ m) : ℝ) : ℂ) = (q : ℂ) ^ ((m : ℂ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq.le, Complex.ofReal_cpow hq.le]
  congr 1
  push_cast
  ring

/-- Decompose the finite local Connes–Weil integral into positive and negative
valuation shells. The integral over units vanishes because the radial profile
vanishes at one. At a ramified place, translation by a unit with nontrivial
character annihilates the whole integral. -/
private theorem introTrace_characterTrace_finite (χ : U𝔽) (h : ℝ → ℂ) (h1 : h 1 = 0)
    (v : V) [LocallyCompactSpace (v.adicCompletion F)ˣ] (b : BruhatCompactSupport (v.adicCompletion F)ˣ)
    (hb : ∀ x, b.val x = introTraceTest χ h (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x)) :
    ((Real.log q(v) / ((finiteLocalMultiplicativeTamagawaMeasure F v)
      (v.adicCompletionIntegers F).units).toReal : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v 1 b = ∑' k, introTracePrimePower χ h v k := by
  classical
  let K := v.adicCompletion F
  let : MeasurableSpace K := borel _
  let : BorelSpace K := ⟨rfl⟩
  let : MeasurableSpace Kˣ := borel _
  let : BorelSpace Kˣ := ⟨rfl⟩
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let : μ.IsHaarMeasure := finiteLocalMultiplicative_isHaar F v
  let U : Set Kˣ := (v.adicCompletionIntegers F).units
  let c := finiteUnitary v χ
  let W (u : Kˣ) := b.val u * (Real.sqrt ‖u.val‖ : ℂ) / (‖1 - u.val‖ : ℂ)
  have hb' (u : Kˣ) : b.val u = star (c u : ℂ) * h ‖u.val‖ := by
    rw [hb, introTraceTest, ideleClassNorm_ofAdicCompletion]
    rfl
  have hb1 : b.val 1 = 0 := by simp [hb', h1]
  obtain ⟨hI, hPV⟩ := finiteConnesWeilPrincipalValue_of_apply_one_zero v b hb1
  change Integrable W μ at hI
  change finiteConnesWeilPrincipalValue v 1 b = ∫ x, W x ∂μ at hPV
  rw [hPV]
  by_cases hur : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨p, hp⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    let π := Units.mk0 (p : K) hp.ne_zero
    have hπ : ‖π.val‖ = q(v)⁻¹ := norm_uniformizer_adicCompletion v _ hp
    have hq : 1 < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    have hr : 0 < ‖π.val‖ := norm_pos_iff.mpr π.ne_zero
    have hr1 : ‖π.val‖ < 1 := hπ.trans_lt (inv_lt_one_of_one_lt₀ hq)
    have hloc : (ideleClassNormTwist χ 0).localValue v = (c π : ℂ) := by
      rw [hur.localValue_eq π hp, HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
      change finitePlaceRestriction F v (ideleClassNormTwist χ 0) π = _
      simp [finiteUnitary_eval, c]
    let S (n : ℤ) := (fun u : Kˣ ↦ π ^ (-n) * u) ⁻¹' U
    have hS (n : ℤ) (u : Kˣ) : u ∈ S n ↔ ‖u.val‖ = ‖π.val‖ ^ n := by
      change π ^ (-n) * u ∈ (v.adicCompletionIntegers F).units ↔ _
      rw [finiteUnit_norm, Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, zpow_neg]
      constructor
      · intro hu
        calc
          ‖u.val‖ = (‖π.val‖ ^ n) * ((‖π.val‖ ^ n)⁻¹ * ‖u.val‖) := by field_simp
          _ = _ := by rw [hu, mul_one]
      · intro hu
        rw [hu, inv_mul_cancel₀ (zpow_ne_zero _ hr.ne')]
    have hcover : ⋃ n, S n = univ := by
      apply eq_univ_of_forall
      intro u
      obtain ⟨e, hep, hei⟩ := finitePlace_unitDecomposition v π hπ
      let i := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom
      let n := (e u).1.toAdd
      let t := i (e u).2
      have ht : t ∈ U := ⟨(e u).2.val.property, (e u).2.inv.property⟩
      have hu : u = π ^ n * t := by
        apply e.injective
        rw [map_mul, map_zpow, hep, hei]
        apply Prod.ext <;> simp [n]
        change _ = Multiplicative.ofAdd (Multiplicative.toAdd (e u).1 * 1)
        simp
      exact mem_iUnion.mpr ⟨n, (hS n u).mpr (by
        conv_lhs => rw [hu]
        simp [Units.val_zpow_eq_zpow_val, (finiteUnit_norm v t).mp ht])⟩
    have hmass (n : ℤ) : μ (S n) = μ U := measure_preimage_mul μ _ _
    have hm (n : ℤ) : MeasurableSet (S n) :=
      (Submonoid.isOpen_units (Valued.isOpen_valuationSubring K)).measurableSet.preimage (measurable_const_mul _)
    have hd : Pairwise (Disjoint on S) := by
      intro i j hij
      refine disjoint_left.mpr fun x hi hj ↦ hij ?_
      exact (zpow_right_injective₀ hr hr1.ne) (((hS i x).mp hi).symm.trans ((hS j x).mp hj))
    let I (n : ℤ) := ∫ u in S n, W u ∂μ
    have hs : HasSum I (∫ x, W x ∂μ) := by
      simpa only [hcover, Measure.restrict_univ] using hasSum_integral_iUnion hm hd hI.integrableOn
    have hc (n : ℤ) (u : Kˣ) (hu : u ∈ S n) : c u = c π ^ n := by
      have hunit : c (π ^ (-n) * u) = 1 :=
        (finiteUnitary_unramified v χ).mp hur _ ((finiteUnit_norm v _).mp hu)
      calc
        _ = c (π ^ n * (π ^ (-n) * u)) := by congr 1; group
        _ = _ := by rw [map_mul, map_zpow, hunit, mul_one]
    have int_const (n : ℤ) (d : ℂ) (he : ∀ u ∈ S n, W u = d) : I n = (μ.real U : ℂ) * d := by
      change (∫ u in S n, W u ∂μ) = _
      rw [setIntegral_congr_fun (hm n) he, setIntegral_const, Measure.real, hmass, Complex.real_smul]
      rfl
    have hzero : I 0 = 0 := by
      rw [int_const 0 0 (fun u hu ↦ by
        have hnorm : ‖u.val‖ = 1 := by simpa using (hS 0 u).mp hu
        simp [W, hb', hnorm, h1]), mul_zero]
    have H := (introTrace_characterTrace_paired I hs hzero).mul_left
      ((Real.log q(v) / μ.real U : ℝ) : ℂ)
    symm
    apply HasSum.tsum_eq
    apply H.congr_fun
    intro k
    let m := k + 1
    have hqm : 1 < q(v)^m := one_lt_pow₀ hq (Nat.succ_ne_zero k)
    have hqm0 := zero_lt_one.trans hqm
    have hroot := introTrace_characterTrace_sqrt q(v) (zero_lt_one.trans hq) m
    have hposNorm : ‖π.val‖ ^ (m : ℤ) = (q(v)^m)⁻¹ := by simp [hπ, inv_pow]
    have hnegNorm : ‖π.val‖ ^ (-(m : ℤ)) = q(v)^m := by rw [zpow_neg, hposNorm, inv_inv]
    have hpos := int_const (m : ℤ)
      (star (c π : ℂ) ^ m * h ((q(v)^m)⁻¹) * (Real.sqrt ((q(v)^m)⁻¹) : ℂ)) (by
        intro u hu
        have hnorm := ((hS (m : ℤ) u).mp hu).trans hposNorm
        have hsmall : ‖u.val‖ < 1 := hnorm.trans_lt (inv_lt_one_of_one_lt₀ hqm)
        dsimp only [W]
        rw [hb', introTrace_characterTrace_ultrametric _ hsmall.ne, max_eq_left hsmall.le,
          hnorm, hc (m : ℤ) u hu]
        simp)
    have hneg := int_const (-(m : ℤ))
      ((c π : ℂ) ^ m * h (q(v)^m) * (Real.sqrt (q(v)^m) : ℂ) / ((q(v)^m : ℝ) : ℂ)) (by
        intro u hu
        have hnorm := ((hS (-(m : ℤ)) u).mp hu).trans hnegNorm
        have hlarge : 1 < ‖u.val‖ := hqm.trans_eq hnorm.symm
        dsimp only [W]
        rw [hb', introTrace_characterTrace_ultrametric _ hlarge.ne', max_eq_right hlarge.le,
          hnorm, hc (-(m : ℤ)) u hu]
        simp only [zpow_neg, zpow_natCast, Circle.coe_inv_eq_conj, Complex.star_def,
          Complex.conj_conj, Circle.coe_pow])
    have hmass_ne : (μ.real U : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      change (finiteLocalMultiplicativeTamagawaMeasure F v (v.adicCompletionIntegers F).units).toReal ≠ 0
      rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
      positivity
    have hsq : (Real.sqrt (q(v)^m) : ℂ) ^ 2 = ((q(v)^m : ℝ) : ℂ) := by
      exact_mod_cast Real.sq_sqrt hqm0.le
    have hroot_ne : (Real.sqrt (q(v)^m) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hqm0).ne'
    symm
    change ((Real.log q(v) / μ.real U : ℝ) : ℂ) * (I (m : ℤ) + I (-(m : ℤ))) =
      introTracePrimePower χ h v k
    rw [hpos, hneg, introTracePrimePower, ite_eq_left hur, hloc]
    change _ = (Real.log q(v) : ℂ) * ((c π : ℂ) ^ m * h (q(v)^m) +
      star (c π : ℂ) ^ m * h ((q(v)^m)⁻¹)) / ((q(v) : ℂ) ^ ((m : ℂ) / 2))
    rw [← hroot, Real.sqrt_inv, Complex.ofReal_inv, ← hsq, Complex.ofReal_div]
    field_simp
    ring
  · obtain ⟨t, htu, htc⟩ : ∃ t : Kˣ, ‖t.val‖ = 1 ∧ c t ≠ 1 := by
      simpa only [finiteUnitary_unramified, not_forall, Classical.not_imp, exists_prop, c] using hur
    have hc : star (c t : ℂ) ≠ 1 := by
      intro he
      have hstar := congrArg star he
      apply htc
      exact Subtype.ext (by simpa using hstar)
    have hinv (x : Kˣ) : W (t * x) = star (c t : ℂ) * W x := by
      have hn : ‖(t * x).val‖ = ‖x.val‖ := by simp [Units.val_mul, norm_mul, htu]
      by_cases hx : ‖x.val‖ = 1
      · simp only [W, hb', hn, hx, h1, mul_zero, zero_mul, zero_div]
      · dsimp only [W]
        rw [show ‖1 - (t * x).val‖ = ‖1 - x.val‖ by
          rw [introTrace_characterTrace_ultrametric _ (hn ▸ hx), introTrace_characterTrace_ultrametric _ hx, hn]]
        simp only [hb', hn, map_mul, Circle.coe_mul, star_mul]
        ring
    rw [introTrace_characterTrace_integral_zero μ W t _ hc hinv, mul_zero]
    simp [introTracePrimePower, hur]

end CharacterTrace

section Tests

/-- Paper: §1.4.2, p. 28. The radial power is zero below one, one half at
one, and the inverse complex power above one.
Deviation: The radial profile is extended by zero to the nonpositive real axis
for additive convolution. -/
def introTracePower (z : ℂ) (t : ℝ) : ℂ :=
  if 1 < t then (t : ℂ) ^ (-z) else if t = 1 then 1 / 2 else 0

/-- Paper: §1.4.2, p. 28. On the positive side at parameter two the profile
has value one quarter at two and value one half at the jump. -/
theorem introTracePower_two :
    introTracePower 2 2 = 1 / 4 ∧ introTracePower 2 1 = 1 / 2 := by
  refine ⟨?_, by simp [introTracePower]⟩
  simp only [introTracePower, show (1 : ℝ) < 2 by norm_num, ↓reduceIte, Complex.cpow_neg]
  norm_num

/-- Paper: §1.4.2, p. 28. The radial power is smooth on the two real
intervals separated by its jump at one. -/
theorem introTracePower_contDiffOn (z : ℂ) :
    ContDiffOn ℝ ⊤ (introTracePower z) ({1}ᶜ : Set ℝ) := by
  intro x hx
  refine ContDiffAt.contDiffWithinAt ?_
  rcases lt_or_gt_of_ne (show x ≠ 1 from hx) with h | h
  · have : introTracePower z =ᶠ[nhds x] fun _ ↦ 0 := by
      filter_upwards [eventually_lt_nhds h] with t ht
      simp [introTracePower, ht.not_gt, ht.ne]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have : introTracePower z =ᶠ[nhds x]
        fun t : ℝ ↦ Complex.exp ((Real.log t : ℂ) * (-z)) := by
      filter_upwards [eventually_gt_nhds h] with t ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
      simp only [introTracePower, ht, ↓reduceIte, Complex.cpow_def_of_ne_zero ht0,
        Complex.ofReal_log (by linarith : (0 : ℝ) ≤ t)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ this
    have hlog : ContDiffAt ℝ ⊤ Real.log x := Real.contDiffAt_log.2 (by linarith)
    exact Complex.contDiff_exp.contDiffAt.comp x
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog).mul contDiffAt_const)

/-- Paper: §1.4.2, p. 28. The limiting power depends holomorphically
on the complex parameter at each fixed radial coordinate. -/
theorem introTracePower_differentiable (t : ℝ) :
    Differentiable ℂ (fun z ↦ introTracePower z t) := by
  by_cases ht : 1 < t
  · simp only [introTracePower, ite_eq_left ht]
    exact differentiable_neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (by linarith)))
  · simp only [introTracePower, ite_eq_right ht]
    exact differentiable_const _

/-- Paper: §1.4.2, pp. 28–29. The cutoffs increase pointwise to the indicator
of `(1, ∞)` and the mollifiers have nonnegative unit mass and shrinking support.
Deviation: The paper leaves the mollifier and convolution unspecified. This
uses ordinary additive convolution in the coordinate `t` with Lebesgue measure
and encodes the cofinal approximation by sequences. -/
def IsIntroTraceApproximation (h ρ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, ContDiff ℝ (⊤ : ℕ∞) (h n) ∧ HasCompactSupport (h n) ∧
    tsupport (h n) ⊆ Ioi 1 ∧ ∀ t, h n t ∈ Icc 0 1) ∧
  Monotone h ∧ (∀ t > 1, Tendsto (fun n ↦ h n t) atTop (𝓝 1)) ∧
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ n, 0 < ε n ∧ ContDiff ℝ (⊤ : ℕ∞) (ρ n) ∧ (∀ t, 0 ≤ ρ n t) ∧
      tsupport (ρ n) ⊆ Icc (-ε n) (ε n) ∧ (∫ t, ρ n t) = 1

/-- Paper: §1.4.2, pp. 28–29. Smooth bump cutoffs and ordinary mollifiers
give an approximation sequence with the stated support and convergence. -/
theorem exists_introTraceApproximation :
    ∃ h ρ, IsIntroTraceApproximation h ρ := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  let b (n : ℕ) : ContDiffBump (0 : ℝ) :=
    ⟨ε n / 2, ε n, half_pos (hε n), half_lt_self (hε n)⟩
  let h (n : ℕ) (t : ℝ) := Real.smoothTransition (((n : ℝ) + 1) * (t - 1) - 1) *
    Real.smoothTransition ((n : ℝ) - t)
  have hs (n : ℕ) : tsupport (h n) ⊆ Icc (1 + ε n) (n : ℝ) := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    have hp := mul_ne_zero_iff.mp (show h n t ≠ 0 from ht)
    have hl := lt_of_not_ge (hp.1 ∘ Real.smoothTransition.zero_of_nonpos)
    have hr := lt_of_not_ge (hp.2 ∘ Real.smoothTransition.zero_of_nonpos)
    refine ⟨?_, by linarith⟩
    have : ε n < t - 1 := by
      apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
      rw [mul_comm]
      linarith
    linarith
  refine ⟨h, fun n ↦ (b n).normed volume, ?_, ?_, ?_,
    ε, tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  · intro n
    refine ⟨?_, isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hs n),
      fun t ht ↦ lt_of_lt_of_le (lt_add_of_pos_right 1 (hε n)) (hs n ht).1, fun t ↦ ?_⟩
    · exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
          (Real.smoothTransition.contDiff.comp (by fun_prop))
    · exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
        (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
          (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)⟩
  · intro m n hmn t
    have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmn
    dsimp [h]
    by_cases ht : 1 ≤ t
    · have hl := mul_le_mul_of_nonneg_right (show (m : ℝ) + 1 ≤ (n : ℝ) + 1 by linarith)
        (sub_nonneg.mpr ht)
      exact mul_le_mul (Real.smoothTransition.monotone (sub_le_sub_right hl 1))
        (Real.smoothTransition.monotone (sub_le_sub_right hcast t))
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    · have hz (k : ℕ) : ((k : ℝ) + 1) * (t - 1) - 1 ≤ 0 := by
        have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ (k : ℝ) + 1)
          (sub_nonpos.mpr (le_of_not_ge ht))
        linarith
      simp [Real.smoothTransition.zero_of_nonpos (hz m),
        Real.smoothTransition.zero_of_nonpos (hz n)]
  · intro t ht
    apply tendsto_const_nhds.congr'
    have hg : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hg.eventually_ge_atTop (2 / (t - 1)), hg.eventually_ge_atTop (t + 1)]
      with n hn hn'
    have hmul := (div_le_iff₀ (sub_pos.mpr ht)).mp hn
    have hl : 1 ≤ ((n : ℝ) + 1) * (t - 1) - 1 := by linarith only [hmul, ht]
    simp only [h, Real.smoothTransition.one_of_one_le hl,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ (n : ℝ) - t), mul_one]
  · intro n
    refine ⟨hε n, (b n).contDiff_normed, (b n).nonneg_normed, ?_, (b n).integral_normed⟩
    rw [(b n).tsupport_normed_eq, Real.closedBall_eq_Icc]
    simp [b]

/-- Paper: §1.4.2, p. 28. The approximant is the cutoff times the mollified
radial power in the norm coordinate. -/
def introTraceApprox (h ρ : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (h t : ℂ) * ∫ u : ℝ, (ρ u : ℂ) * introTracePower z (t - u)

/-- Paper: §1.4.2, pp. 28–29. The approximants are supported strictly
above norm one and agree with the limiting power at each fixed norm other
than one in the limit.
Deviation: The support statement uses topological support, so each individual
cutoff vanishes in an open neighborhood of one. -/
theorem introTraceApprox_support (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    tsupport (introTraceApprox (h n) (ρ n) z) ⊆ Ioi 1 := by
  refine (closure_mono (s := Function.support (introTraceApprox (h n) (ρ n) z))
    (t := Function.support (h n)) ?_).trans (_hA.1 n).2.2.1
  intro t ht he
  exact ht (by simp [introTraceApprox, he])

/-- Paper: §1.4.2, p. 29. Every fixed positive norm other than one has
the printed pointwise limit. -/
theorem introTraceApprox_tendsto (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (z : ℂ) (t : ℝ) (_ht : 0 < t) (_ht₁ : t ≠ 1) :
    Tendsto (fun n ↦ introTraceApprox (h n) (ρ n) z t) atTop (𝓝 (introTracePower z t)) := by
  obtain ⟨hh, -, hhlim, ε, hε, hρ⟩ := _hA
  rcases lt_or_gt_of_ne _ht₁ with ht | ht
  · have hzero (n : ℕ) : h n t = 0 := by
      by_contra hn
      exact (not_lt.mpr ht.le) ((hh n).2.2.1 (subset_tsupport _ hn))
    simp [introTraceApprox, hzero, introTracePower, ht.not_gt, ht.ne]
  · have hcont : ContinuousAt (introTracePower z) t := by
      apply (Complex.continuousAt_ofReal_cpow_const t (-z) (Or.inr _ht.ne')).congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds ht] with x hx
      simp [introTracePower, hx]
    have hmeas : Measurable (introTracePower z) :=
      Measurable.ite measurableSet_Ioi (by fun_prop)
        (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
    have hsmall : Tendsto (fun n ↦ support (ρ n)) atTop (𝓝 0).smallSets := by
      rw [Metric.nhds_basis_ball.smallSets.tendsto_right_iff]
      intro r hr
      filter_upwards [hε.eventually_lt_const hr] with n hn
      intro x hx
      have hmem := (hρ n).2.2.2.1 (subset_tsupport _ hx)
      simpa only [Metric.mem_ball, Real.dist_0_eq_abs, abs_lt] using
        (show -r < x ∧ x < r from ⟨lt_of_lt_of_le (neg_lt_neg hn) hmem.1, hmem.2.trans_lt hn⟩)
    have hconv := convolution_tendsto_right (μ := volume)
      (g := fun _ : ℕ ↦ introTracePower z) (k := fun _ ↦ t)
      (Eventually.of_forall fun n ↦ (hρ n).2.2.1)
      (Eventually.of_forall fun n ↦ (hρ n).2.2.2.2) hsmall
      (Eventually.of_forall fun _ ↦ hmeas.aestronglyMeasurable)
      (hcont.tendsto.comp tendsto_snd) tendsto_const_nhds
    have hcut := Complex.continuous_ofReal.continuousAt.tendsto.comp (hhlim t ht)
    simpa only [introTraceApprox, convolution, ContinuousLinearMap.lsmul_apply,
      Complex.real_smul, Complex.ofReal_one, one_mul, Function.comp_def] using hcut.mul hconv

/-- Paper: §1.4.2, pp. 28–29. At any fixed norm, the mollified cutoff
depends holomorphically on the complex parameter. -/
theorem introTraceApprox_differentiable (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (t : ℝ) :
    Differentiable ℂ (fun z ↦ introTraceApprox (h n) (ρ n) z t) := by
  obtain ⟨-, -, -, ε, -, hε⟩ := _hA
  obtain ⟨-, hρc, -, hρs, -⟩ := hε n
  have hρint : Integrable (ρ n) := hρc.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hρs)
  have hρm : Measurable fun u ↦ (ρ n u : ℂ) :=
    Complex.measurable_ofReal.comp hρc.continuous.measurable
  have hPm : ∀ z : ℂ, Measurable (introTracePower z) := fun z ↦
    Measurable.ite measurableSet_Ioi (by fun_prop)
      (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
  have hu : ∀ u, ρ n u ≠ 0 → t - u ≤ t + ε n := fun u hu ↦ by
    have := hρs (subset_tsupport _ hu)
    linarith [this.1]
  intro z₀
  set K : ℝ := |z₀.re| + 1
  set C : ℝ := |Real.log (t + ε n)| * |t + ε n| ^ K
  set M : ℝ := max 1 (|t + ε n| ^ K)
  have hpow : ∀ u, ∀ z ∈ Metric.ball z₀ 1, ρ n u ≠ 0 → 1 < t - u →
      (t - u) ^ (-z.re) ≤ |t + ε n| ^ K := by
    intro u z hz hρ h1
    have hz' : |z.re - z₀.re| < 1 :=
      (Complex.abs_re_le_norm (z - z₀)).trans_lt (by simpa [dist_eq_norm] using hz)
    calc (t - u) ^ (-z.re) ≤ (t - u) ^ K := Real.rpow_le_rpow_of_exponent_le h1.le
          (by linarith [(abs_lt.1 hz').1, neg_abs_le z₀.re])
      _ ≤ |t + ε n| ^ K := Real.rpow_le_rpow (by linarith)
          ((hu u hρ).trans (le_abs_self _)) (by positivity)
  have hF_int : Integrable (fun u ↦ (ρ n u : ℂ) * introTracePower z₀ (t - u)) := by
    refine Integrable.mono' (hρint.norm.mul_const M)
      (hρm.mul ((hPm z₀).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (Eventually.of_forall fun u ↦ ?_)
    by_cases hρ : ρ n u = 0
    · simp [hρ]
    rw [norm_mul, Complex.norm_real]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    unfold introTracePower
    split_ifs with h1 h2
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
      exact (hpow u z₀ (Metric.mem_ball_self one_pos) hρ h1).trans (le_max_right _ _)
    · exact le_trans (by norm_num) (le_max_left _ _)
    · simpa using (zero_le_one.trans (le_max_left _ _) : (0 : ℝ) ≤ M)
  have hF'_meas : AEStronglyMeasurable (fun u : ℝ ↦ (ρ n u : ℂ) *
      if 1 < t - u then ((t - u : ℝ) : ℂ) ^ (-z₀) * Complex.log ((t - u : ℝ) : ℂ) * (-1)
      else 0) volume :=
    (hρm.mul (Measurable.ite (measurableSet_lt measurable_const
      (measurable_const.sub measurable_id)) (by fun_prop) measurable_const)).aestronglyMeasurable
  have h_bound : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1, ‖(ρ n u : ℂ) *
      (if 1 < t - u then ((t - u : ℝ) : ℂ) ^ (-z) * Complex.log ((t - u : ℝ) : ℂ) * (-1)
        else 0)‖ ≤ ‖ρ n u‖ * C := by
    refine Eventually.of_forall fun u z hz ↦ ?_
    rw [norm_mul, Complex.norm_real]
    by_cases hρ : ρ n u = 0
    · simp [hρ]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    split_ifs with h1
    · have hc : 0 < t - u := by linarith
      rw [norm_mul, norm_mul, norm_neg, norm_one, mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos hc, Complex.neg_re, ← Complex.ofReal_log hc.le,
        Complex.norm_real, Real.norm_eq_abs, mul_comm]
      refine mul_le_mul ?_ (hpow u z hz hρ h1) (by positivity) (abs_nonneg _)
      rw [abs_of_nonneg (Real.log_nonneg h1.le)]
      exact (Real.log_le_log hc (hu u hρ)).trans (le_abs_self _)
    · simp only [norm_zero]
      positivity
  have h_diff : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun z ↦ (ρ n u : ℂ) * introTracePower z (t - u)) ((ρ n u : ℂ) *
        (if 1 < t - u then ((t - u : ℝ) : ℂ) ^ (-z) * Complex.log ((t - u : ℝ) : ℂ) * (-1)
          else 0)) z := by
    refine Eventually.of_forall fun u z _ ↦ ?_
    split_ifs with h1
    · have hfun : (fun z ↦ (ρ n u : ℂ) * introTracePower z (t - u)) =
          fun z ↦ (ρ n u : ℂ) * ((t - u : ℝ) : ℂ) ^ (-z) := by
        funext z
        simp [introTracePower, h1]
      rw [hfun]
      exact ((hasDerivAt_neg z).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.2 (by linarith)))).const_mul _
    · have hfun : (fun z ↦ (ρ n u : ℂ) * introTracePower z (t - u)) =
          fun _ ↦ (ρ n u : ℂ) * introTracePower 0 (t - u) := by
        funext z
        simp [introTracePower, h1]
      rw [hfun]
      exact (hasDerivAt_const z _).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z ↦ (hρm.mul
      ((hPm z).comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
    hF_int hF'_meas h_bound (hρint.norm.mul_const C) h_diff
  exact (differentiableAt_const _).mul key.2.differentiableAt

private theorem introTracePower_locallyIntegrable (z : ℂ) :
    LocallyIntegrable (introTracePower z) volume := by
  let P (t : ℝ) := ((max t 1 : ℝ) : ℂ) ^ (-z)
  have hP : Continuous P := continuous_iff_continuousAt.mpr fun t ↦
    (Complex.continuousAt_ofReal_cpow_const (max t 1) (-z)
      (Or.inr (zero_lt_one.trans_le (le_max_right t 1)).ne')).comp
        (f := fun u : ℝ ↦ max u 1) (x := t) (continuous_id.max continuous_const).continuousAt
  have hI : LocallyIntegrable ((Ioi (1 : ℝ)).indicator P) volume :=
    hP.locallyIntegrable.indicator measurableSet_Ioi
  apply hI.congr
  have he : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    simp [ae_iff]
  filter_upwards [he] with x hx
  by_cases h : 1 < x
  · rw [indicator_of_mem h]
    simp [P, introTracePower, h, max_eq_left h.le]
  · rw [indicator_of_notMem h]
    simp [introTracePower, h, hx]

private theorem introTraceApprox_logProfile (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    let f := fun x ↦ introTraceApprox (h n) (ρ n) z (Real.exp x)
    ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f := by
  intro f
  obtain ⟨hh, _, _, _, _, hρ⟩ := hA
  have hc : HasCompactSupport (fun u ↦ (ρ n u : ℂ)) := by
    apply HasCompactSupport.comp_left (g := Complex.ofReal) _ (by simp)
    exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hρ n).2.2.2.1
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun u ↦ (ρ n u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hρ n).2.1
  have hs : ContDiff ℝ (⊤ : ℕ∞) (introTraceApprox (h n) (ρ n) z) := by
    exact (Complex.ofRealCLM.contDiff.comp (hh n).1).mul <|
      hc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hm (introTracePower_locallyIntegrable z)
  refine ⟨hs.comp Real.contDiff_exp, ?_⟩
  have hl : ContinuousOn Real.log (tsupport (h n)) :=
    Real.continuousOn_log.mono fun x hx ↦ (zero_lt_one.trans ((hh n).2.2.1 hx)).ne'
  refine exists_compact_iff_hasCompactSupport.mp
    ⟨Real.log '' tsupport (h n), ((hh n).2.1.image_of_continuousOn hl), fun x hx ↦ ?_⟩
  have hz : h n (Real.exp x) = 0 := by
    by_contra hn
    exact hx ⟨Real.exp x, subset_tsupport _ hn, Real.log_exp x⟩
  simp [f, introTraceApprox, hz]

/-- Paper: §1.4.2, pp. 28–29. After twisting by the conjugate character
the approximant is a compactly supported Bruhat test on the idele classes. -/
theorem introTraceApprox_exists_bruhat (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    ∃ φ : D𝔽, ∀ g, φ.val g = introTraceTest χ (introTraceApprox (h n) (ρ n) z) g := by
  obtain ⟨hs, hc⟩ := introTraceApprox_logProfile h ρ _hA n z
  obtain ⟨φ, hφ⟩ := exists_characterNormTest (F := F) χ⁻¹ _ hs hc
  refine ⟨φ, fun g ↦ ?_⟩
  rw [hφ, introTraceTest]
  have hg : 0 < N(g) := NNReal.coe_pos.mpr (Units.zero_lt _)
  simp [Real.exp_log hg, ← Circle.coe_inv_eq_conj, show χ⁻¹ g = (χ g)⁻¹ from rfl]

/-- Paper: §1.4.2, pp. 28–29. The twisted approximant satisfies the second
standing hypothesis of the trace identity, vanishing at every norm-one class. -/
theorem introTraceApprox_zero_on_normOne (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    ∀ g : (ideleClassNorm F).ker,
      introTraceTest χ (introTraceApprox (h n) (ρ n) z) g.val = 0 := by
  intro g
  have hzero : introTraceApprox (h n) (ρ n) z 1 = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun ht ↦ lt_irrefl (1 : ℝ) (introTraceApprox_support h ρ _hA n z ht)
  have hg : ideleClassNorm F g.val = 1 := g.property
  simp [introTraceTest, hg, hzero]

private theorem introTraceApprox_mellin_tendsto_power_measurable (z : ℂ) :
    Measurable (introTracePower z) :=
  Measurable.ite measurableSet_Ioi (by fun_prop)
    (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)

private theorem introTraceApprox_mellin_tendsto_power_bound {a t x : ℝ} {z : ℂ}
    (ht : 1 < t) (hx : |x - t| ≤ 1) (hz : a ≤ z.re) :
    ‖introTracePower z x‖ ≤ ((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a) := by
  -- On the nonzero branch, the shifted radius lies between t/2 and 2t.
  have hb (hx1 : 1 ≤ x) :
      x ^ (-a) ≤ ((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a) := by
    obtain ⟨hl, hu⟩ := abs_le.mp hx
    rcases le_total 0 a with ha | ha
    · calc
        x ^ (-a) ≤ ((1 / 2) * t) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
        _ = (1 / 2 : ℝ) ^ (-a) * t ^ (-a) := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
    · calc
        x ^ (-a) ≤ (2 * t) ^ (-a) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
        _ = (2 : ℝ) ^ (-a) * t ^ (-a) := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)
  unfold introTracePower
  split_ifs with h h'
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le h.le (neg_le_neg hz)).trans (hb h.le)
  · subst x
    exact le_trans (by norm_num : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) ^ (-a)) (hb le_rfl)
  · rw [norm_zero]
    positivity

private theorem introTraceApprox_mellin_tendsto_radial {h ρ : ℕ → ℝ → ℝ}
    (hA : IsIntroTraceApproximation h ρ) (z : ℂ) {t : ℝ} (ht : 1 < t) :
    Tendsto (fun p : ℕ × ℂ ↦ introTraceApprox (h p.1) (ρ p.1) p.2 t)
      (atTop ×ˢ 𝓝 z) (𝓝 (introTracePower z t)) := by
  obtain ⟨_, _, hlim, ε, hε, hρ⟩ := hA
  have hsmall : Tendsto (fun n ↦ support (ρ n)) atTop (𝓝 0).smallSets := by
    rw [Metric.nhds_basis_ball.smallSets.tendsto_right_iff]
    intro r hr
    filter_upwards [hε.eventually_lt_const hr] with n hn
    intro x hx
    have hm := (hρ n).2.2.2.1 (subset_tsupport _ hx)
    simpa only [Metric.mem_ball, Real.dist_0_eq_abs, abs_lt] using
      (show -r < x ∧ x < r from ⟨by linarith [hm.1], by linarith [hm.2]⟩)
  let l : Filter (ℕ × ℂ) := atTop ×ˢ 𝓝 z
  have hcont : Tendsto (fun p : (ℕ × ℂ) × ℝ ↦ introTracePower p.1.2 p.2)
      (l ×ˢ 𝓝 t) (𝓝 (introTracePower z t)) := by
    have hx : Tendsto (fun p : (ℕ × ℂ) × ℝ ↦ (p.2 : ℂ)) (l ×ˢ 𝓝 t) (𝓝 (t : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_snd
    have hz : Tendsto (fun p : (ℕ × ℂ) × ℝ ↦ -p.1.2) (l ×ˢ 𝓝 t) (𝓝 (-z)) :=
      (tendsto_snd.comp tendsto_fst).neg
    simp only [introTracePower, ht, ↓reduceIte]
    apply (hx.cpow hz (Complex.ofReal_mem_slitPlane.mpr (by linarith))).congr'
    filter_upwards [tendsto_snd.eventually (lt_mem_nhds ht)] with p hp
    simp [hp]
  have hconv := convolution_tendsto_right (μ := volume)
    (φ := fun p : ℕ × ℂ ↦ ρ p.1) (g := fun p : ℕ × ℂ ↦ introTracePower p.2)
    (k := fun _ ↦ t) (l := l)
    (Eventually.of_forall fun p ↦ (hρ p.1).2.2.1)
    (Eventually.of_forall fun p ↦ (hρ p.1).2.2.2.2) (hsmall.comp tendsto_fst)
    (Eventually.of_forall fun p ↦ (introTraceApprox_mellin_tendsto_power_measurable p.2).aestronglyMeasurable)
    hcont tendsto_const_nhds
  have hcut := Complex.continuous_ofReal.continuousAt.tendsto.comp ((hlim t ht).comp
    (show Tendsto Prod.fst l atTop from tendsto_fst))
  simpa only [introTraceApprox, convolution, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul, Complex.ofReal_one, one_mul, Function.comp_def] using hcut.mul hconv

private theorem introTraceApprox_mellin_tendsto_cutoff_bound {h ρ : ℕ → ℝ → ℝ}
    (hA : IsIntroTraceApproximation h ρ) (a : ℝ) :
    ∀ᶠ n in atTop, ∀ (z : ℂ) (t : ℝ), a ≤ z.re → 1 < t →
      ‖introTraceApprox (h n) (ρ n) z t‖ ≤ ((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a) := by
  obtain ⟨hh, _, _, ε, hε, hρ⟩ := hA
  filter_upwards [hε.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)] with n hn
  intro z t hz ht
  let B := ((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a)
  obtain ⟨_, hsm, hpos, hs, hm⟩ := hρ n
  have hi : Integrable (ρ n) volume := hsm.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs)
  have hbound : ‖∫ u : ℝ, (ρ n u : ℂ) * introTracePower z (t - u)‖ ≤ B := by
    calc
      _ ≤ ∫ u, ρ n u * B := norm_integral_le_of_norm_le (hi.mul_const B) (by
        apply Eventually.of_forall
        intro u
        by_cases hu : ρ n u = 0
        · simp [hu]
        obtain ⟨hl, hr⟩ := hs (subset_tsupport _ hu)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hpos u)]
        apply mul_le_mul_of_nonneg_left _ (hpos u)
        exact introTraceApprox_mellin_tendsto_power_bound ht (abs_le.mpr ⟨by linarith, by linarith⟩) hz)
      _ = B := by rw [integral_mul_const, hm, one_mul]
  rw [introTraceApprox, norm_mul, Complex.norm_real, Real.norm_of_nonneg ((hh n).2.2.2 t).1]
  exact mul_le_of_le_one_left (norm_nonneg _) ((hh n).2.2.2 t).2 |>.trans hbound

private theorem introTraceApprox_mellin_tendsto_integral {ι : Type} {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → ℝ → ℂ} {g : ℝ → ℂ} (s : ℂ) {a C : ℝ}
    (ha : s.re < a) (hf : ∀ i, Measurable (f i))
    (hzero : ∀ i t, t < 1 → f i t = 0)
    (hbound : ∀ᶠ i in l, ∀ t, 1 < t → ‖f i t‖ ≤ C * t ^ (-a))
    (hlim : ∀ t, t ≠ 1 → Tendsto (fun i ↦ f i t) l (𝓝 (g t))) :
    Tendsto (fun i ↦ introTraceMellin (f i) s) l (𝓝 (introTraceMellin g s)) := by
  -- The Mellin weight lowers the decay exponent to s.re - 1 - a < -1.
  let B := (Ioi (1 : ℝ)).indicator (fun t : ℝ ↦ C * t ^ (s.re - 1 - a))
  have hi : Integrable B volume := (integrable_indicator_iff measurableSet_Ioi).2
    ((integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 1 - a < -1) zero_lt_one).const_mul C)
  apply tendsto_integral_filter_of_dominated_convergence B _ _ hi.integrableOn _
  · exact Eventually.of_forall fun i ↦
      ((by fun_prop : Measurable (fun t : ℝ ↦ (t : ℂ) ^ (s - 1))).smul (hf i)).aestronglyMeasurable
  · filter_upwards [hbound] with i hbi
    filter_upwards [Measure.ae_ne _ (1 : ℝ)] with t hne
    rcases lt_or_gt_of_ne hne with ht | ht
    · simp [B, hzero i t ht, ht.not_gt, Set.indicator_of_notMem]
    · rw [show B t = C * t ^ (s.re - 1 - a) from indicator_of_mem ht _, smul_eq_mul,
          norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      simp only [Complex.sub_re, Complex.one_re]
      calc
        _ ≤ t ^ (s.re - 1) * (C * t ^ (-a)) :=
          mul_le_mul_of_nonneg_left (hbi t ht) (by positivity)
        _ = C * t ^ (s.re - 1 - a) := by
          rw [sub_eq_add_neg (s.re - 1), Real.rpow_add (by linarith : 0 < t)]
          ring
  · filter_upwards [Measure.ae_ne _ (1 : ℝ)] with t ht
    exact (tendsto_const_nhds (x := (t : ℂ) ^ (s - 1))).smul (hlim t ht)

/-- Paper: §§1.4.2–1.4.3, pp. 28–29. For a fixed Mellin exponent `s`,
the approximant moments converge locally uniformly on `Re z > Re s`
to the Mellin integral of the limiting radial power. -/
theorem introTraceApprox_mellin_tendsto (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (s : ℂ) :
    TendstoLocallyUniformlyOn
      (fun n z ↦ introTraceMellin (introTraceApprox (h n) (ρ n) z) s)
      (fun z ↦ introTraceMellin (introTracePower z) s) atTop right(s.re) := by
  apply (isOpen_Ioi.preimage Complex.continuous_re).tendstoLocallyUniformlyOn_iff_forall_tendsto.2
  intro z hz
  obtain ⟨a, hsa, haz⟩ := exists_between (show s.re < z.re from hz)
  let l : Filter (ℕ × ℂ) := atTop ×ˢ 𝓝 z
  let C := (1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)
  have hnear : ∀ᶠ p : ℕ × ℂ in l, a ≤ p.2.re :=
    (Complex.continuous_re.continuousAt.tendsto.comp tendsto_snd).eventually (le_mem_nhds haz)
  have hpow : Tendsto (fun p : ℕ × ℂ ↦ introTraceMellin (introTracePower p.2) s) l
      (𝓝 (introTraceMellin (introTracePower z) s)) := by
    apply introTraceApprox_mellin_tendsto_integral (a := a) (C := C) s hsa
    · exact fun p ↦ introTraceApprox_mellin_tendsto_power_measurable p.2
    · intro p t ht
      simp [introTracePower, ht.not_gt, ht.ne]
    · filter_upwards [hnear] with p hp
      intro t ht
      exact introTraceApprox_mellin_tendsto_power_bound ht (by simp) hp
    · intro t _
      exact (introTracePower_differentiable t).continuous.continuousAt.tendsto.comp tendsto_snd
  have hzero (n : ℕ) (t : ℝ) (ht : t < 1) : h n t = 0 := by
    by_contra hn
    exact ht.asymm ((_hA.1 n).2.2.1 (subset_tsupport _ hn))
  have happ : Tendsto (fun p : ℕ × ℂ ↦ introTraceMellin (introTraceApprox (h p.1) (ρ p.1) p.2) s) l
      (𝓝 (introTraceMellin (introTracePower z) s)) := by
    apply introTraceApprox_mellin_tendsto_integral (a := a) (C := C) s hsa
    · intro p
      obtain ⟨ε, _, hρ⟩ := _hA.2.2.2
      have hm := (introTraceApprox_mellin_tendsto_power_measurable p.2).comp
        (measurable_fst.sub measurable_snd : Measurable fun q : ℝ × ℝ ↦ q.1 - q.2)
      have hk : Measurable (fun q : ℝ × ℝ ↦ (ρ p.1 q.2 : ℂ)) :=
        Complex.measurable_ofReal.comp ((hρ p.1).2.1.continuous.measurable.comp measurable_snd)
      exact (Complex.measurable_ofReal.comp (_hA.1 p.1).1.continuous.measurable).mul
        ((hk.mul hm).stronglyMeasurable.integral_prod_right'.measurable)
    · intro p t ht
      simp [introTraceApprox, hzero p.1 t ht]
    · filter_upwards [hnear, (show Tendsto Prod.fst l atTop from tendsto_fst).eventually
          (introTraceApprox_mellin_tendsto_cutoff_bound _hA a)] with p hp hb
      exact fun t ht ↦ hb p.2 t hp ht
    · intro t ht
      rcases lt_or_gt_of_ne ht with hlt | hgt
      · simp [introTraceApprox, hzero _ _ hlt, introTracePower, hlt.not_gt, hlt.ne]
      · exact introTraceApprox_mellin_tendsto_radial _hA z hgt
  exact (hpow.prodMk_nhds happ).mono_right (nhds_le_uniformity _)

/-- Paper: §§1.4.2, 1.4.5, pp. 28–29. The Mellin transform of the limiting
radial power exists on the convergence half-plane and equals `1 / (z - s)`. -/
theorem introTracePower_mellin (z s : ℂ) (_hs : s.re < z.re) :
    IntegrableOn (fun t : ℝ ↦ introTracePower z t * (t : ℂ) ^ (s - 1)) (Ioi 0) ∧
      introTraceMellin (introTracePower z) s = 1 / (z - s) := by
  let a := -z + (s - 1)
  have ha : a.re < -1 := by
    change -z.re + (s.re - 1) < -1
    linarith
  have he : (fun t : ℝ ↦ introTracePower z t * (t : ℂ) ^ (s - 1)) =ᵐ[volume]
      (Ioi (1 : ℝ)).indicator (fun t : ℝ ↦ (t : ℂ) ^ a) := by
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t ht
    by_cases hgt : 1 < t
    · rw [indicator_of_mem hgt, introTracePower, ite_eq_left hgt]
      exact (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hgt).ne')).symm
    · simp [introTracePower, ht, hgt]
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  have hI : IntegrableOn ((Ioi (1 : ℝ)).indicator (fun t : ℝ ↦ (t : ℂ) ^ a)) (Ioi 0) := by
    rw [integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet, inter_eq_left.mpr hsub]
    exact integrableOn_Ioi_cpow_of_lt ha zero_lt_one
  refine ⟨hI.congr (ae_restrict_of_ae he.symm), ?_⟩
  unfold introTraceMellin mellin
  simp_rw [smul_eq_mul, mul_comm _ (introTracePower z _)]
  rw [integral_congr_ae (ae_restrict_of_ae he), setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr hsub, integral_Ioi_cpow_of_lt ha zero_lt_one]
  rw [show a + 1 = -(z - s) by dsimp [a]; ring]
  simp only [Complex.ofReal_one, Complex.one_cpow, neg_div_neg_eq]

end Tests

section Limits

local notation "approx(" h ", " ρ ", " n ", " z ")" => introTraceApprox (h n) (ρ n) z
local notation "archSum(" χ ", " h ")" =>
  (∑ w : InfinitePlace F, introTraceArchimedean χ h w)
local notation "primeSum(" χ ", " h ")" =>
  (∑' p : V × ℕ, introTracePrimePower χ h p.1 p.2)

/-- With the radial cutoff fixed, Fubini combines the local integral and the
mollification into a single weighted Mellin integral. -/
private theorem introTraceApprox_archimedean_differentiable_integral
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ] (A : X → ℂ) (t : X → ℝ)
    (ρ : ℝ → ℝ) (hA : Measurable A) (ht : Measurable t) (hρ : Measurable ρ)
    (hAi : Integrable A μ) (hρi : Integrable ρ) (B ε : ℝ)
    (hB : ∀ x, A x ≠ 0 → t x ≤ B) (hε : ∀ u, ρ u ≠ 0 → -ε ≤ u) :
    Differentiable ℂ (fun z ↦ ∫ x, A x * ∫ u, (ρ u : ℂ) *
      introTracePower z (t x - u) ∂volume ∂μ) := by
  let r (p : X × ℝ) := max 1 (t p.1 - p.2)
  let f (p : X × ℝ) := A p.1 * (ρ p.2 : ℂ) * introTracePower 0 (t p.1 - p.2)
  have hr : Measurable r := measurable_const.max (ht.comp measurable_fst |>.sub measurable_snd)
  have hr1 (p : X × ℝ) : 1 ≤ r p := le_max_left _ _
  have hrp (p : X × ℝ) : 0 < r p := zero_lt_one.trans_le (hr1 p)
  have hf : Measurable f := by
    have hp : Measurable (introTracePower 0) := by
      unfold introTracePower
      exact Measurable.ite measurableSet_Ioi (by fun_prop)
        (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
    exact ((hA.comp measurable_fst).mul ((hρ.comp measurable_snd).complex_ofReal)).mul
      (hp.comp ((ht.comp measurable_fst).sub measurable_snd))
  have hI (z : ℂ) : Integrable (fun p ↦ f p * (r p : ℂ) ^ z) (μ.prod volume) := by
    let C := max 1 (B + ε) ^ |z.re|
    have hdom := (hAi.norm.mul_prod hρi.norm).mul_const C
    refine hdom.mono' (hf.mul (hr.complex_ofReal.pow_const _)).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ ?_)
    by_cases ha : A p.1 = 0
    · simp [f, ha]
    by_cases hρ0 : ρ p.2 = 0
    · simp [f, hρ0]
    have hrle : r p ≤ max 1 (B + ε) := by
      exact max_le_max le_rfl (by linarith [hB _ ha, hε _ hρ0])
    have hpow : r p ^ z.re ≤ C :=
      (Real.rpow_le_rpow_of_exponent_le (hr1 p) (le_abs_self _)).trans
        (Real.rpow_le_rpow (hrp p).le hrle (abs_nonneg _))
    have hp : ‖introTracePower 0 (t p.1 - p.2)‖ ≤ 1 := by
      unfold introTracePower
      split_ifs <;> norm_num [norm_div]
    simp only [f, norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos (hrp p)]
    calc
      _ ≤ (‖A p.1‖ * ‖ρ p.2‖ * 1) * C := by gcongr
      _ = _ := by simp
  have han := analyticOnNhd_integral_mul_cpow_of_integrable (μ.prod volume)
    f r hr hrp isOpen_univ (fun z _ ↦ hI z)
  have hd : Differentiable ℂ (fun z : ℂ ↦ ∫ p, f p * (r p : ℂ) ^ z ∂μ.prod volume) :=
    fun z ↦ (han z (mem_univ _)).differentiableAt
  convert hd.comp differentiable_neg using 1
  ext1 z
  change _ = ∫ p, f p * (r p : ℂ) ^ (-z) ∂μ.prod volume
  rw [integral_prod _ (hI (-z))]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ fun u ↦ ?_
  have hp (a : ℝ) : introTracePower z a =
      introTracePower 0 a * ((max 1 a : ℝ) : ℂ) ^ (-z) := by
    by_cases ha : 1 < a
    · simp [introTracePower, ha, max_eq_right ha.le]
    · simp [introTracePower, ha, max_eq_left (le_of_not_gt ha)]
  simp only [f, r, hp (t x - u), mul_assoc]

/-- Paper: §1.4.3, p. 29. Each fixed-cutoff archimedean integral is entire
in the parameter.
Deviation: The archimedean kernels use the corrected trace formula. -/
theorem introTraceApprox_archimedean_differentiable (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (w : InfinitePlace F) :
    Differentiable ℂ (fun z ↦ introTraceArchimedean χ approx(h, ρ, n, z) w) := by
  classical
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology w.Completionˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : LocallyCompactSpace w.Completionˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).locallyCompactSpace
  let μ := infiniteLocalMultiplicativeTamagawaMeasure F w
  let : μ.IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  let localClass := IdeleClassGroup.ofCompletion (𝓞 F) F w
  let t (u : w.Completionˣ) : ℝ := ‖u.val‖ ^ w.mult
  have ht : Continuous t := (continuous_norm.comp Units.continuous_val).pow _
  have ht_norm (u : w.Completionˣ) :
      N(IdeleClassGroup.ofCompletion (𝓞 F) F w u) = t u := by
    rw [ideleClassNorm_ofCompletion, Units.val_pow_eq_pow_val, NNReal.coe_pow]
    rfl
  obtain ⟨hh, -, -, ε, -, hε⟩ := _hA
  obtain ⟨hhc, hhK, hhS, -⟩ := hh n
  obtain ⟨-, hρc, -, hρS, -⟩ := hε n
  obtain ⟨B, hB⟩ := hhK.bddAbove
  let K := t ⁻¹' tsupport (h n)
  have hK_closed : IsClosed K := (isClosed_tsupport _).preimage ht
  have hK_norm (u : w.Completionˣ) (hu : u ∈ K) : 1 < t u := hhS hu
  have hK : IsCompact K := by
    let S : Set w.Completion := (fun u : w.Completion ↦ ‖u‖ ^ w.mult) ⁻¹' tsupport (h n)
    have hS1 {u : w.Completion} (hu : u ∈ S) : 1 < ‖u‖ ^ w.mult := hhS hu
    have hScompact : IsCompact S := by
      have he := InfinitePlace.Completion.isometry_extensionEmbedding w
      have hball : IsCompact (Metric.closedBall (0 : w.Completion) B) := by
        simpa only [← he.preimage_closedBall] using he.isClosedEmbedding.isCompact_preimage
          (isCompact_closedBall (InfinitePlace.Completion.extensionEmbedding w 0) B)
      refine hball.of_isClosed_subset ((isClosed_tsupport _).preimage (continuous_norm.pow _)) ?_
      intro u hu
      rw [mem_closedBall_zero_iff]
      have hnorm : 1 ≤ ‖u‖ := by
        by_contra! h
        exact (not_lt_of_ge (pow_le_one₀ (norm_nonneg _) h.le)) (hS1 hu)
      exact (le_self_pow₀ hnorm w.mult_ne_zero).trans (hB hu)
    refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hScompact ?_
    intro u hu
    have hne : u ≠ 0 := by
      intro hzero
      have h := hS1 hu
      rw [hzero, norm_zero, zero_pow w.mult_ne_zero] at h
      exact (not_lt_of_ge zero_le_one) h
    exact ⟨Units.mk0 u hne, rfl⟩
  let a (u : w.Completionˣ) : ℂ :=
    star (χ (localClass u) : ℂ) * (h n (t u) : ℂ) *
      (Real.sqrt (t u) : ℂ) / ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)
  have hzero (u : w.Completionˣ) (hu : u ∉ K) : a u = 0 := by
    have hh0 : h n (t u) = 0 := image_eq_zero_of_notMem_tsupport hu
    simp [a, hh0]
  have hχ : Continuous (fun u : w.Completionˣ ↦ (χ (localClass u) : ℂ)) :=
    continuous_subtype_val.comp (χ.continuous.comp (continuous_ideleClass_ofCompletion F w))
  have hden : Continuous (fun u : w.Completionˣ ↦ ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_norm.comp (continuous_const.sub Units.continuous_val)).pow _)
  have ha : Measurable a :=
    ((hχ.star.measurable.mul ((hhc.continuous.comp ht).measurable.complex_ofReal)).mul
      ((Real.continuous_sqrt.comp ht).measurable.complex_ofReal)).div hden.measurable
  have hai : Integrable a μ := by
    have hac : ContinuousOn a K := by
      apply ContinuousOn.div
      · exact ((hχ.star.mul (Complex.continuous_ofReal.comp (hhc.continuous.comp ht))).mul
          (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp ht))).continuousOn
      · exact hden.continuousOn
      · intro u hu
        apply Complex.ofReal_ne_zero.mpr
        apply pow_ne_zero
        rw [norm_ne_zero_iff, sub_ne_zero]
        intro he
        have hone : t u = 1 := by simp [t, ← he]
        exact (ne_of_gt (hK_norm u hu)) hone
    refine ((hac.integrableOn_compact hK).integrable_indicator hK_closed.measurableSet).congr ?_
    refine ae_of_all _ fun u ↦ ?_
    by_cases hu : u ∈ K
    · exact indicator_of_mem hu _
    · rw [indicator_of_notMem hu, hzero u hu]
  have hρi : Integrable (ρ n) := hρc.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hρS)
  have hd := introTraceApprox_archimedean_differentiable_integral μ a t (ρ n)
    ha ht.measurable hρc.continuous.measurable hai hρi B (ε n)
    (fun u hu ↦ hB (show u ∈ K from not_not.mp (mt (hzero u) hu)))
    (fun x hx ↦ (hρS (subset_tsupport _ hx)).1)
  unfold introTraceArchimedean
  refine (differentiable_const _).mul ?_
  convert hd using 1
  ext1 z
  apply integral_congr_ae
  refine ae_of_all _ fun u ↦ ?_
  simp only [introTraceTest, introTraceApprox, ht_norm, a, t]
  ring

/-- The local multiplicative measure in either infinite-place coordinate has density
the reciprocal normalized norm against its additive Tamagawa measure. -/
private theorem introTraceApprox_archimedean_sub_shiftTwo_lintegral {E : Type*} [NormedField E] [MeasurableSpace E] [BorelSpace E]
    (v : InfinitePlace F) (e : v.Completion ≃+* E) (hi : Isometry e)
    (ν : Measure E) (hν : ν.restrict {0}ᶜ = ν)
    (hμ : letI := instMeasurableSpaceCompletion_riemannMasullo F v
      infiniteLocalAdditiveTamagawaMeasure F v = ν.map e.symm)
    (Φ : E → ENNReal) (hΦ : Measurable Φ) :
    ∫⁻ u, Φ (e (u : v.Completion)) ∂infiniteLocalMultiplicativeTamagawaMeasure F v =
      ∫⁻ t, Φ t * ENNReal.ofReal (‖t‖ ^ v.mult)⁻¹ ∂ν := by
  let : MeasurableSpace v.Completion := instMeasurableSpaceCompletion_riemannMasullo F v
  let : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace v.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let j : v.Completion ≃ᵢ E := ⟨e.toEquiv, hi⟩
  let m := j.toHomeomorph.toMeasurableEquiv
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.Completion)).measurableEmbedding
  have hd : Measurable (fun x : v.Completion ↦ (↑(‖x‖₊ ^ v.mult) : ENNReal)⁻¹) :=
    (measurable_coe_nnreal_ennreal.comp (measurable_nnNorm.pow_const _)).inv
  let g : v.Completion → ENNReal := fun x ↦ Φ (e x)
  have hg : Measurable g := hΦ.comp m.measurable
  have hee (t : E) : e (m.symm t) = t := e.apply_symm_apply t
  have key := hval.lintegral_map (μ := ((infiniteLocalAdditiveTamagawaMeasure F v).withDensity
    (fun x ↦ (↑(‖x‖₊ ^ v.mult) : ENNReal)⁻¹)).comap Units.val) g
  rw [hval.map_comap, setLIntegral_withDensity_eq_setLIntegral_mul _ hd hg
    hval.measurableSet_range] at key
  unfold infiniteLocalMultiplicativeTamagawaMeasure
  refine key.symm.trans ?_
  rw [hμ]
  change (∫⁻ x in range Units.val, _ ∂ν.map m.symm) = _
  rw [m.symm.restrict_map, m.symm.measurableEmbedding.lintegral_map]
  have he0 : m.symm 0 = 0 := map_zero (e).symm
  have hrange : m.symm ⁻¹' range (Units.val : v.Completionˣ → v.Completion) = {0}ᶜ := by
    ext t
    simp only [mem_preimage, mem_range, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro ⟨x, hx⟩ rfl
      exact x.ne_zero (hx.trans he0)
    · intro ht
      exact ⟨Units.mk0 (m.symm t) fun h0 ↦ ht (m.symm.injective (h0.trans he0.symm)), rfl⟩
  have hnorm (t : E) : ‖m.symm t‖ = ‖t‖ := j.symm.isometry.norm_map_of_map_zero (map_zero e.symm) t
  rw [hrange]
  conv_rhs => rw [← hν]
  refine setLIntegral_congr_fun (measurableSet_singleton (0 : E)).compl fun t ht ↦ ?_
  have ht0 : t ≠ 0 := ht
  change (↑(‖m.symm t‖₊ ^ v.mult) : ENNReal)⁻¹ * g (m.symm t) = _
  simp only [g]
  rw [hee, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow, coe_nnNorm, hnorm, mul_comm,
    ENNReal.ofReal_inv_of_pos (pow_pos (norm_pos_iff.mpr ht0) _)]

/-- At the real place of ℚ, a lower integral against the local multiplicative Tamagawa measure
is the Lebesgue integral with density `|t|⁻¹` in the real coordinate. -/
private theorem introTraceApprox_rat_archimedean_tendsto_atTop_lintegral
    (Φ : ℝ → ENNReal) (hΦ : Measurable Φ) :
    ∫⁻ u, Φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (u : Rat.infinitePlace.Completion))
        ∂infiniteLocalMultiplicativeTamagawaMeasure ℚ Rat.infinitePlace =
      ∫⁻ t, Φ t * ENNReal.ofReal |t|⁻¹ := by
  simpa only [Rat.isReal_infinitePlace.mult_eq_one, pow_one, Real.norm_eq_abs] using
    introTraceApprox_archimedean_sub_shiftTwo_lintegral Rat.infinitePlace
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
      (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).isometry
      volume (restrict_compl_singleton (μ := volume) 0)
      (dite_eq_left Rat.isReal_infinitePlace) Φ hΦ

/-- Paper: §1.4.3, p. 29. For the trivial rational character at parameter two,
the real-place term goes to positive infinity as the cutoffs are removed.
Deviation: This replaces the printed uniform bound. It also applies to the
corrected trace formula, since the positive real branch has the same kernel. -/
theorem introTraceApprox_rat_archimedean_tendsto_atTop (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) :
    Tendsto (fun n ↦ (∑ w : InfinitePlace ℚ,
      introTraceArchimedean (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) w).re) atTop atTop := by
  classical
  obtain ⟨hh, -, hhlim, ε, hε, hρ⟩ := _hA
  have hw : Rat.infinitePlace.IsReal := Rat.isReal_infinitePlace
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  -- The limiting profile at parameter two is real.
  let p : ℝ → ℝ := fun x ↦ if 1 < x then x ^ (-2 : ℝ) else if x = 1 then 1 / 2 else 0
  have hp0 (x : ℝ) : 0 ≤ p x := by
    simp only [p]; split_ifs with h1 <;> first | positivity | norm_num
  have hp1 (x : ℝ) : p x ≤ 1 := by
    simp only [p]; split_ifs with h1
    · exact Real.rpow_le_one_of_one_le_of_nonpos h1.le (by norm_num)
    · norm_num
    · norm_num
  have hpm : Measurable p :=
    Measurable.ite measurableSet_Ioi (by fun_prop)
      (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
  have hpow (x : ℝ) : introTracePower 2 x = (p x : ℂ) := by
    simp only [introTracePower, p]
    split_ifs with h1 h2
    · rw [Complex.ofReal_cpow (zero_lt_one.trans h1).le]; push_cast; rfl
    · push_cast; rfl
    · simp
  -- The real approximants.
  let b : ℕ → ℝ → ℝ := fun n t ↦ h n t * ∫ u, ρ n u * p (t - u)
  have happrox (n : ℕ) (t : ℝ) : introTraceApprox (h n) (ρ n) 2 t = (b n t : ℂ) := by
    simp only [introTraceApprox, hpow, b, Complex.ofReal_mul]
    congr 1
    rw [← integral_complex_ofReal]
    simp only [Complex.ofReal_mul]
  have hρint (n : ℕ) : Integrable (ρ n) volume := (hρ n).2.1.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hρ n).2.2.2.1)
  have hint (n : ℕ) (t : ℝ) : Integrable (fun u ↦ ρ n u * p (t - u)) volume :=
    (hρint n).mono (((hρ n).2.1.continuous.measurable.mul
      (hpm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
      (Eventually.of_forall fun u ↦ by
        rw [norm_mul, Real.norm_of_nonneg (hp0 _)]
        exact mul_le_of_le_one_right (norm_nonneg _) (hp1 _))
  have hI0 (n : ℕ) (t : ℝ) : 0 ≤ ∫ u, ρ n u * p (t - u) :=
    integral_nonneg fun u ↦ mul_nonneg ((hρ n).2.2.1 u) (hp0 _)
  have hb0 (n : ℕ) (t : ℝ) : 0 ≤ b n t := mul_nonneg ((hh n).2.2.2 t).1 (hI0 n t)
  have hb1 (n : ℕ) (t : ℝ) : b n t ≤ 1 := by
    have hI : ∫ u, ρ n u * p (t - u) ≤ 1 := by
      rw [← (hρ n).2.2.2.2]
      exact integral_mono (hint n t) (hρint n) fun u ↦
        mul_le_of_le_one_right ((hρ n).2.2.1 u) (hp1 _)
    exact mul_le_one₀ ((hh n).2.2.2 t).2 (hI0 n t) hI
  have hbm (n : ℕ) : Measurable (b n) := by
    have hk : Measurable (fun q : ℝ × ℝ ↦ ρ n q.2 * p (q.1 - q.2)) :=
      ((hρ n).2.1.continuous.measurable.comp measurable_snd).mul
        (hpm.comp (measurable_fst.sub measurable_snd))
    exact (hh n).1.continuous.measurable.mul hk.stronglyMeasurable.integral_prod_right'.measurable
  have hbsupp (n : ℕ) (t : ℝ) (hbt : b n t ≠ 0) : t ∈ tsupport (h n) :=
    subset_tsupport _ (left_ne_zero_of_mul hbt)
  have hblow (n : ℕ) (t : ℝ) (hεn : ε n ≤ 1) (ht1 : 1 + ε n < t) (ht2 : t < 2) :
      h n t / 9 ≤ b n t := by
    have hI : (1 / 9 : ℝ) ≤ ∫ u, ρ n u * p (t - u) := by
      calc (1 / 9 : ℝ) = ∫ u, ρ n u * (1 / 9) := by rw [integral_mul_const, (hρ n).2.2.2.2, one_mul]
        _ ≤ _ := integral_mono ((hρint n).mul_const _) (hint n t) fun u ↦ by
          by_cases hu : ρ n u = 0
          · simp [hu]
          obtain ⟨hl, hr⟩ := (hρ n).2.2.2.1 (subset_tsupport _ hu)
          refine mul_le_mul_of_nonneg_left ?_ ((hρ n).2.2.1 u)
          have hgt : 1 < t - u := by linarith
          have hlt : t - u ≤ 3 := by linarith
          simp only [p, if_pos hgt]
          rw [Real.rpow_neg (by linarith), Real.rpow_two, show (1 / 9 : ℝ) = (3 ^ 2)⁻¹ by norm_num]
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hlt 2)
    calc h n t / 9 = h n t * (1 / 9) := by ring
      _ ≤ b n t := mul_le_mul_of_nonneg_left hI ((hh n).2.2.2 t).1
  -- The integrand in the real coordinate.
  let Φ : ℕ → ℝ → ℝ := fun n t ↦ b n |t| * √|t| / |1 - t|
  have hΦ0 (n : ℕ) (t : ℝ) : 0 ≤ Φ n t := by
    simp only [Φ]; have := hb0 n |t|; positivity
  have hΦm (n : ℕ) : Measurable (Φ n) :=
    (((hbm n).comp continuous_abs.measurable).mul (Real.continuous_sqrt.measurable.comp continuous_abs.measurable)).div
      (continuous_abs.measurable.comp (measurable_const.sub measurable_id))
  let X : ℕ → ENNReal := fun n ↦ ∫⁻ t, ENNReal.ofReal (Φ n t) * ENNReal.ofReal |t|⁻¹
  have hnorm (x : Rat.infinitePlace.Completion) : ‖x‖ = |e x| :=
    ((InfinitePlace.Completion.isometryEquivRealOfIsReal hw).isometry.norm_map_of_map_zero
      (map_zero e) x).symm.trans (Real.norm_eq_abs _)
  -- The real part of the archimedean term is half of `X n`.
  have hre (n : ℕ) : (∑ w : InfinitePlace ℚ,
      introTraceArchimedean (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) w).re = (X n).toReal / 2 := by
    rw [Fintype.sum_subsingleton _ Rat.infinitePlace, introTraceArchimedean, if_pos hw]
    have hpt (u : Rat.infinitePlace.Completionˣ) :
        introTraceTest (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) approx(h, ρ, n, (2 : ℂ))
            (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace u) *
            (Real.sqrt (‖u.val‖ ^ InfinitePlace.mult Rat.infinitePlace) : ℂ) /
            ((‖1 - u.val‖ ^ InfinitePlace.mult Rat.infinitePlace : ℝ) : ℂ) =
          ((Φ n (e u) : ℝ) : ℂ) := by
      have hN : (((ideleClassNorm ℚ) (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace u)).val : ℝ) =
          ‖(u : Rat.infinitePlace.Completion)‖ := by
        rw [ideleClassNorm_ofCompletion, hw.mult_eq_one, pow_one]
        rfl
      simp only [introTraceTest, PontryaginDual.one_apply, Circle.coe_one, star_one, one_mul,
        hw.mult_eq_one, pow_one, hN, happrox, Φ]
      rw [hnorm, hnorm, map_sub, map_one]
      push_cast
      rfl
    let : MeasurableSpace Rat.infinitePlace.Completion :=
      instMeasurableSpaceCompletion_riemannMasullo ℚ Rat.infinitePlace
    let : BorelSpace Rat.infinitePlace.Completion := ⟨rfl⟩
    let : BorelSpace Rat.infinitePlace.Completionˣ := borelSpace_units_of_continuousInv₀ _
    simp_rw [hpt]
    rw [integral_complex_ofReal]
    have hmeas : Measurable fun u : Rat.infinitePlace.Completionˣ ↦ Φ n (e u) :=
      (hΦm n).comp ((InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous.measurable.comp
        Units.continuous_val.measurable)
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun u ↦ hΦ0 n _)
      hmeas.aestronglyMeasurable,
      introTraceApprox_rat_archimedean_tendsto_atTop_lintegral (fun t ↦ ENNReal.ofReal (Φ n t))
        (ENNReal.measurable_ofReal.comp (hΦm n))]
    simp only [one_div, Complex.re_mul_ofReal, Complex.inv_re, Complex.normSq_ofNat]
    norm_num
    ring
  -- Each `X n` is finite: the cutoff is supported in a compact subset of `(1, ∞)`.
  have hfin (n : ℕ) : X n ≠ ⊤ := by
    have hK : IsCompact (tsupport (h n)) := (hh n).2.1
    have hsub : tsupport (h n) ⊆ Ioi 1 := (hh n).2.2.1
    obtain ⟨c, hc1, hc⟩ : ∃ c, 1 < c ∧ ∀ x ∈ tsupport (h n), c ≤ x := by
      rcases (tsupport (h n)).eq_empty_or_nonempty with he | hne
      · exact ⟨2, by norm_num, by simp [he]⟩
      · obtain ⟨c, hcK, hcmin⟩ := hK.exists_isMinOn hne continuousOn_id
        exact ⟨c, hsub hcK, fun x hx ↦ hcmin hx⟩
    obtain ⟨R, hR⟩ := hK.bddAbove
    let M : ℝ := √R / (c - 1) * c⁻¹
    have hle (t : ℝ) : ENNReal.ofReal (Φ n t) * ENNReal.ofReal |t|⁻¹ ≤
        (Icc (-R) R).indicator (fun _ ↦ ENNReal.ofReal M) t := by
      by_cases hz : b n |t| = 0
      · simp [Φ, hz]
      have hmem := hbsupp n |t| hz
      have hct : c ≤ |t| := hc _ hmem
      have hRt : |t| ≤ R := hR hmem
      rw [indicator_of_mem (abs_le.mp hRt), ← ENNReal.ofReal_mul (hΦ0 n t)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1t : c - 1 ≤ |1 - t| := by
        have := abs_sub_abs_le_abs_sub t 1
        rw [abs_one, abs_sub_comm] at this
        linarith
      have hc0 : 0 < c - 1 := by linarith
      have htpos : 0 < |t| := by linarith
      have hb := hb1 n |t|
      have hb' := hb0 n |t|
      simp only [Φ, M]
      calc b n |t| * √|t| / |1 - t| * |t|⁻¹ ≤ 1 * √R / (c - 1) * c⁻¹ := by
            gcongr
        _ = √R / (c - 1) * c⁻¹ := by rw [one_mul]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- The lower bounds `K n` and Fatou's lemma.
  let K : ℕ → ℝ → ENNReal := fun n ↦
    (Ioo (1 + ε n) 2).indicator fun t ↦ ENNReal.ofReal (h n t / (18 * (t - 1)))
  have hKm (n : ℕ) : Measurable (K n) :=
    (ENNReal.measurable_ofReal.comp ((hh n).1.continuous.measurable.div
      (measurable_const.mul (measurable_id.sub measurable_const)))).indicator measurableSet_Ioo
  have hKle : ∀ᶠ n in atTop, ∀ t, K n t ≤ ENNReal.ofReal (Φ n t) * ENNReal.ofReal |t|⁻¹ := by
    filter_upwards [hε.eventually_le_const (zero_lt_one : (0 : ℝ) < 1)] with n hn t
    simp only [K]
    by_cases ht : t ∈ Ioo (1 + ε n) 2
    · rw [indicator_of_mem ht, ← ENNReal.ofReal_mul (hΦ0 n t)]
      refine ENNReal.ofReal_le_ofReal ?_
      obtain ⟨ht1, ht2⟩ := ht
      have hεpos := (hρ n).1
      have htpos : 0 < t := by linarith
      have ht1' : 0 < t - 1 := by linarith
      have hbt := hblow n t hn ht1 ht2
      have hs0 : 0 < √t := Real.sqrt_pos.mpr htpos
      have hs2 : √t ≤ 2 := by
        calc √t ≤ √4 := Real.sqrt_le_sqrt (by linarith)
          _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hst : √t * t⁻¹ = (√t)⁻¹ := by
        calc √t * t⁻¹ = √t * (√t * √t)⁻¹ := by rw [Real.mul_self_sqrt htpos.le]
          _ = (√t)⁻¹ := by field_simp
      have hsq : 1 / 2 ≤ √t * t⁻¹ := by
        rw [hst, one_div]
        exact inv_anti₀ hs0 hs2
      simp only [Φ]
      rw [abs_of_pos htpos, abs_sub_comm, abs_of_pos ht1']
      have hh0 : 0 ≤ h n t / 9 := div_nonneg ((hh n).2.2.2 t).1 (by norm_num)
      calc h n t / (18 * (t - 1)) = (h n t / 9) * (1 / 2) / (t - 1) := by field_simp; ring
        _ ≤ b n t * (√t * t⁻¹) / (t - 1) :=
          div_le_div_of_nonneg_right (mul_le_mul hbt hsq (by norm_num) (hb0 n t)) ht1'.le
        _ = b n t * √t / (t - 1) * t⁻¹ := by ring
    · rw [indicator_of_notMem ht]
      exact bot_le
  have hliminf : ∀ t, (Ioo 1 2).indicator (fun t ↦ ENNReal.ofReal (1 / (18 * (t - 1)))) t ≤
      liminf (fun n ↦ K n t) atTop := by
    intro t
    by_cases ht : t ∈ Ioo 1 2
    · rw [indicator_of_mem ht]
      have hev : ∀ᶠ n in atTop, K n t = ENNReal.ofReal (h n t / (18 * (t - 1))) := by
        filter_upwards [hε.eventually (gt_mem_nhds (sub_pos.mpr ht.1))] with n hn
        simp only [K]
        exact indicator_of_mem (show t ∈ Ioo (1 + ε n) 2 from ⟨by linarith, ht.2⟩) _
      have hlim : Tendsto (fun n ↦ K n t) atTop (𝓝 (ENNReal.ofReal (1 / (18 * (t - 1))))) :=
        (ENNReal.tendsto_ofReal ((hhlim t ht.1).div_const _)).congr' (hev.mono fun n hn ↦ hn.symm)
      exact hlim.liminf_eq.ge
    · rw [indicator_of_notMem ht]
      exact bot_le
  have hdiv : ∫⁻ t, (Ioo 1 2).indicator (fun t ↦ ENNReal.ofReal (1 / (18 * (t - 1)))) t = ⊤ := by
    rw [lintegral_indicator measurableSet_Ioo]
    by_contra hne
    have hi : IntegrableOn (fun t : ℝ ↦ 1 / (18 * (t - 1))) (Ioo (1 : ℝ) 2) := by
      have := integrable_toReal_of_lintegral_ne_top (μ := volume.restrict (Ioo (1 : ℝ) 2))
        (ENNReal.measurable_ofReal.comp (measurable_const.div
          (measurable_const.mul (measurable_id.sub measurable_const)))).aemeasurable hne
      refine this.congr ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht ↦ ?_))
      have : 0 ≤ 1 / (18 * (t - 1)) := by have := ht.1; positivity
      exact ENNReal.toReal_ofReal this
    have hii : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 1 2 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
      refine IntegrableOn.congr_fun (Integrable.const_mul hi 18) (fun t ht ↦ ?_) measurableSet_Ioo
      have : t - 1 ≠ 0 := by have := ht.1; linarith
      field_simp
    rw [intervalIntegrable_sub_inv_iff] at hii
    rcases hii with h12 | h1
    · norm_num at h12
    · exact h1 (by simp)
  have hX : liminf X atTop = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : ENNReal) = ∫⁻ t, (Ioo 1 2).indicator (fun t ↦ ENNReal.ofReal (1 / (18 * (t - 1)))) t :=
          hdiv.symm
      _ ≤ ∫⁻ t, liminf (fun n ↦ K n t) atTop := lintegral_mono hliminf
      _ ≤ liminf (fun n ↦ ∫⁻ t, K n t) atTop := lintegral_liminf_le hKm
      _ ≤ liminf X atTop := liminf_le_liminf (hKle.mono fun n hn ↦ lintegral_mono hn)
  -- Conclusion.
  simp_rw [hre]
  refine tendsto_atTop.mpr fun M ↦ ?_
  have hlt : ENNReal.ofReal (2 * max M 0) < liminf X atTop := by rw [hX]; exact ENNReal.ofReal_lt_top
  filter_upwards [eventually_lt_of_lt_liminf hlt] with n hn
  have := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (hfin n)).mp hn
  have := le_max_left M 0
  linarith

open Classical in
/-- The additive coordinate retains the value of the local character on every unit. -/
private theorem introTraceArchimedean_coordinate_character (χ : U𝔽) {E : Type*} [NormedField E] [MeasurableSpace E] [BorelSpace E]
    (v : InfinitePlace F) (e : v.Completion ≃+* E) (hi : Isometry e)
    (ν : Measure E) (hν : ν.restrict {0}ᶜ = ν)
    (hμ : letI := instMeasurableSpaceCompletion_riemannMasullo F v
      infiniteLocalAdditiveTamagawaMeasure F v = ν.map e.symm) :
    ∃ m : E → ℂ, (∀ u : v.Completionˣ, m (e u.val) = star (χ (IdeleClassGroup.ofCompletion (𝓞 F) F v u) : ℂ)) ∧
    Measurable m ∧ (∀ t, ‖m t‖ = 1) ∧ (χ = 1 → ∀ t, m t = 1) ∧ ContinuousAt m 1 ∧ m 1 = 1 ∧ ∀ f : ℝ → ℂ, Measurable f →
    (Integrable archIntegrand(χ, f, v) (infiniteLocalMultiplicativeTamagawaMeasure F v) ↔
      Integrable (fun t : E ↦ m t * ((((‖t‖ ^ v.mult)⁻¹ : ℝ) : ℂ) *
        (f (‖t‖ ^ v.mult) * (Real.sqrt (‖t‖ ^ v.mult) : ℂ) / ((‖1 - t‖ ^ v.mult : ℝ) : ℂ)))) ν) ∧
    introTraceArchimedean χ f v =
      (if v.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi:ℂ))) * ∫ t : E, m t * ((((‖t‖ ^ v.mult)⁻¹ : ℝ) : ℂ) *
        (f (‖t‖ ^ v.mult) * (Real.sqrt (‖t‖ ^ v.mult) : ℂ) / ((‖1 - t‖ ^ v.mult : ℝ) : ℂ))) ∂ν := by
  classical
  let j : v.Completion ≃ᵢ E := ⟨e.toEquiv, hi⟩
  let : MeasurableSpace v.Completion := instMeasurableSpaceCompletion_riemannMasullo F v
  let : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace v.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let φ (u : v.Completionˣ) := e (u : v.Completion)
  have hemb : MeasurableEmbedding φ :=
    j.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comp
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.Completion)).measurableEmbedding
  let : MeasurableSpace Circle := borel Circle
  let : BorelSpace Circle := ⟨rfl⟩
  let ch := fun u : v.Completionˣ ↦ χ (IdeleClassGroup.ofCompletion (𝓞 F) F v u)
  have hch : Measurable ch := (χ.continuous.comp (continuous_ideleClass_ofCompletion F v)).measurable
  let m (t : E) := star ((Function.extend φ ch (fun _ ↦ 1) t : Circle) : ℂ)
  have hcirc : Continuous (fun x : Circle ↦ star (x : ℂ)) := continuous_star.comp continuous_subtype_val
  have hm : Measurable m := hcirc.measurable.comp (hemb.measurable_extend hch measurable_const)
  have hopen : Topology.IsOpenEmbedding φ := j.toHomeomorph.isOpenEmbedding.comp
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.Completion))
  have hone : φ 1 = 1 := by simp [φ]
  have hcomp : m ∘ φ = fun u ↦ star (ch u : ℂ) := by
    funext u
    simp only [Function.comp_apply, m, hemb.injective.extend_apply]
  have hnear : ContinuousAt m 1 := by
    rw [← hone, ← hopen.continuousAt_iff, hcomp]
    exact (hcirc.comp (χ.continuous.comp (continuous_ideleClass_ofCompletion F v))).continuousAt
  have hm1 : m 1 = 1 := by
    rw [← hone]
    change (m ∘ φ) 1 = _
    rw [hcomp]
    simp [ch]
  refine ⟨m, fun u ↦ congrFun hcomp u, hm, fun t ↦ by simp [m], ?_, hnear, hm1, ?_⟩
  · rintro rfl t
    by_cases ht : ∃ u, φ u = t
    · obtain ⟨u, rfl⟩ := ht
      simp [m, ch]
    · simp [m, Function.extend_apply' _ _ _ ht]
  intro f hf
  let g (t : E) := m t * (f (‖t‖ ^ v.mult) * (Real.sqrt (‖t‖ ^ v.mult) : ℂ) / ((‖1 - t‖ ^ v.mult : ℝ) : ℂ))
  let D (t : E) := ENNReal.ofReal (‖t‖ ^ v.mult)⁻¹
  have hφ : Measurable φ :=
    j.continuous.measurable.comp
      Units.continuous_val.measurable
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hD : Measurable D := by dsimp [D]; fun_prop
  have hmap : (infiniteLocalMultiplicativeTamagawaMeasure F v).map φ = ν.withDensity D := by
    apply Measure.ext_of_lintegral
    intro Φ hΦ
    rw [lintegral_map hΦ hφ, lintegral_withDensity_eq_lintegral_mul _ hD hΦ]
    simpa [φ, D, mul_comm] using introTraceApprox_archimedean_sub_shiftTwo_lintegral v e hi ν hν hμ Φ hΦ
  have hnorm (x : v.Completion) : ‖x‖ = ‖e x‖ := (hi.norm_map_of_map_zero (map_zero e) x).symm
  have hpoint : archIntegrand(χ, f, v) = g ∘ φ := by
    funext u
    change _ = g (φ u)
    have hN : (((ideleClassNorm F) (IdeleClassGroup.ofCompletion (𝓞 F) F v u)).val : ℝ) =
        ‖(u : v.Completion)‖ ^ v.mult := by
      rw [ideleClassNorm_ofCompletion]
      rfl
    simp only [introTraceTest,
      hN, g, m, hemb.injective.extend_apply, ch, φ, hnorm, map_sub, map_one]
    ring
  constructor
  · rw [hpoint, ← hemb.integrable_map_iff, hmap, integrable_withDensity_iff_integrable_smul' hD
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    apply integrable_congr
    exact .of_forall fun t ↦ by
      simp only [D, ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)), Complex.real_smul, g]
      ring
  rw [introTraceArchimedean, hpoint]
  congr 1
  calc
    _ = ∫ t, g t ∂ν.withDensity D := by
      rw [← hmap, integral_map hφ.aemeasurable hg.aestronglyMeasurable]
      rfl
    _ = _ := by
      rw [integral_withDensity_eq_integral_toReal_smul hD
        (Eventually.of_forall fun t ↦ ENNReal.ofReal_lt_top)]
      simp only [D, ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)), Complex.real_smul, g]
      congr 1
      funext t
      ring

open Classical in
/-- The local character transfers to a measurable unitary multiplier in the archimedean
coordinate. The chart preserves integrability and evaluates the local functional. -/
private theorem introTraceApprox_archimedean_coordinate_continuousAt_one (χ : U𝔽) {E : Type*} [NormedField E] [MeasurableSpace E] [BorelSpace E]
    (v : InfinitePlace F) (e : v.Completion ≃+* E) (hi : Isometry e)
    (ν : Measure E) (hν : ν.restrict {0}ᶜ = ν)
    (hμ : letI := instMeasurableSpaceCompletion_riemannMasullo F v
      infiniteLocalAdditiveTamagawaMeasure F v = ν.map e.symm) :
    ∃ m : E → ℂ, Measurable m ∧ (∀ t, ‖m t‖ = 1) ∧ (χ = 1 → ∀ t, m t = 1) ∧ ContinuousAt m 1 ∧ m 1 = 1 ∧ ∀ f : ℝ → ℂ, Measurable f →
    (Integrable archIntegrand(χ, f, v) (infiniteLocalMultiplicativeTamagawaMeasure F v) ↔
      Integrable (fun t : E ↦ m t * ((((‖t‖ ^ v.mult)⁻¹ : ℝ) : ℂ) *
        (f (‖t‖ ^ v.mult) * (Real.sqrt (‖t‖ ^ v.mult) : ℂ) / ((‖1 - t‖ ^ v.mult : ℝ) : ℂ)))) ν) ∧
    introTraceArchimedean χ f v =
      (if v.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi:ℂ))) * ∫ t : E, m t * ((((‖t‖ ^ v.mult)⁻¹ : ℝ) : ℂ) *
        (f (‖t‖ ^ v.mult) * (Real.sqrt (‖t‖ ^ v.mult) : ℂ) / ((‖1 - t‖ ^ v.mult : ℝ) : ℂ))) ∂ν := by
  obtain ⟨m, _, hm, hn, htriv, hc, h1, he⟩ := introTraceArchimedean_coordinate_character χ v e hi ν hν hμ
  exact ⟨m, hm, hn, htriv, hc, h1, he⟩

open Classical in
/-- The local coordinate formula, with its trivial-character specialization. -/
private theorem introTraceApprox_archimedean_sub_shiftTwo_coordinate (χ : U𝔽) {E : Type*} [NormedField E] [MeasurableSpace E] [BorelSpace E]
    (v : InfinitePlace F) (e : v.Completion ≃+* E) (hi : Isometry e)
    (ν : Measure E) (hν : ν.restrict {0}ᶜ = ν)
    (hμ : letI := instMeasurableSpaceCompletion_riemannMasullo F v
      infiniteLocalAdditiveTamagawaMeasure F v = ν.map e.symm) :
    ∃ m : E → ℂ, Measurable m ∧ (∀ t, ‖m t‖ = 1) ∧ (χ = 1 → ∀ t, m t = 1) ∧ ∀ f : ℝ → ℂ, Measurable f →
    (Integrable archIntegrand(χ, f, v) (infiniteLocalMultiplicativeTamagawaMeasure F v) ↔
      Integrable (fun t : E ↦ m t * ((((‖t‖ ^ v.mult)⁻¹ : ℝ) : ℂ) *
        (f (‖t‖ ^ v.mult) * (Real.sqrt (‖t‖ ^ v.mult) : ℂ) / ((‖1 - t‖ ^ v.mult : ℝ) : ℂ)))) ν) ∧
    introTraceArchimedean χ f v =
      (if v.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi:ℂ))) * ∫ t : E, m t * ((((‖t‖ ^ v.mult)⁻¹ : ℝ) : ℂ) *
        (f (‖t‖ ^ v.mult) * (Real.sqrt (‖t‖ ^ v.mult) : ℂ) / ((‖1 - t‖ ^ v.mult : ℝ) : ℂ))) ∂ν := by
  obtain ⟨m, hm, hn, htriv, _, _, he⟩ :=
    introTraceApprox_archimedean_coordinate_continuousAt_one χ v e hi ν hν hμ
  exact ⟨m, hm, hn, htriv, he⟩

private theorem introTraceApprox_archimedean_sub_shiftTwo_realCoordinate (χ : U𝔽) (v : InfinitePlace F) (hw : v.IsReal) :
    ∃ m : ℝ → ℂ, Measurable m ∧ (∀ t, ‖m t‖ = 1) ∧ (χ = 1 → ∀ t, m t = 1) ∧ ∀ f : ℝ → ℂ, Measurable f →
    (Integrable archIntegrand(χ, f, v) (infiniteLocalMultiplicativeTamagawaMeasure F v) ↔
      Integrable (fun t : ℝ ↦ m t * (((|t|⁻¹ : ℝ) : ℂ) *
        (f |t| * (Real.sqrt |t| : ℂ) / ((|1 - t| : ℝ) : ℂ))))) ∧
    introTraceArchimedean χ f v =
      (1 / 2 : ℂ) * ∫ t : ℝ, m t * (((|t|⁻¹ : ℝ) : ℂ) *
        (f |t| * (Real.sqrt |t| : ℂ) / ((|1 - t| : ℝ) : ℂ))) := by
  simpa only [hw, ite_true, hw.mult_eq_one, pow_one, Real.norm_eq_abs] using
    introTraceApprox_archimedean_sub_shiftTwo_coordinate χ v (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).isometry volume
      (restrict_compl_singleton (μ := volume) 0) (dite_eq_left hw)

/-- In the rational real chart the multiplicative measure is `dt/|t|` and
the two signs of the unit give the denominator `|1-t|`. -/
private theorem introTraceArchimedean_rat_sub_shiftTwo_integral (f : ℝ → ℂ)
    (hf : Measurable f) :
    introTraceArchimedean (F := ℚ) 1 f Rat.infinitePlace =
      (1 / 2 : ℂ) * ∫ t : ℝ, ((|t|⁻¹ : ℝ) : ℂ) *
        (f |t| * (Real.sqrt |t| : ℂ) / ((|1 - t| : ℝ) : ℂ)) := by
  obtain ⟨m, _, _, hm, he⟩ := introTraceApprox_archimedean_sub_shiftTwo_realCoordinate (F := ℚ) 1 Rat.infinitePlace Rat.isReal_infinitePlace
  simpa only [hm rfl, one_mul] using (he f hf).2

/-- Above one the step-two difference cancels the real-place denominator on both
sign branches. Their densities are the sum and difference of two integrable powers. -/
private theorem introTraceArchimedean_rat_sub_shiftTwo_branches (z : ℂ) (t : ℝ) (ht : 1 < t) :
    let p := (t : ℂ) ^ (-z - 3 / 2)
    let q := (t : ℂ) ^ (-z - 3 / 2 - 1)
    let b := ((t⁻¹ : ℝ) : ℂ) * ((introTracePower z t - introTracePower (z + 2) t) * (Real.sqrt t : ℂ))
    b / (t - 1 : ℂ) = p + q ∧ b / (1 + t : ℂ) = p - q := by
  dsimp only
  have ht₀ : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have ht₁ : (t : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ht.ne')
  have htplus : 1 + (t : ℂ) ≠ 0 := by exact_mod_cast (show 1 + t ≠ 0 by linarith)
  have hsqrt : (Real.sqrt t : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by linarith : 0 ≤ t)]
    norm_num
  have hexp : (t : ℂ) ^ (-z - 3 / 2) =
      (t : ℂ) ^ (-z) * (t : ℂ) ^ (1 / 2 : ℂ) / (t : ℂ) ^ 2 := by
    rw [show -z - 3 / 2 = (-z + 1 / 2) - 2 by ring,
      Complex.cpow_sub _ _ ht₀, Complex.cpow_add _ _ ht₀, Complex.cpow_ofNat]
  simp only [introTracePower, ht, ite_true, Complex.ofReal_inv, hsqrt, neg_add_rev]
  rw [show -(2 : ℂ) + -z = -z - 2 by ring, Complex.cpow_sub (-z) 2 ht₀, Complex.cpow_ofNat,
    Complex.cpow_sub _ 1 ht₀, Complex.cpow_one, hexp]
  constructor <;> field_simp <;> ring

/-- Paper: §1.4.3, p. 29. For the trivial rational character, subtract the radial
power at `z+2` from that at `z` before integrating at the real place. The factor
`1-t⁻²` cancels the singularity of the positive branch at one. Adding the two
sign branches gives an integrable power on `(1,∞)`, whose integral is `1/(z+1/2)`.
Deviation: This directly regularizes the limiting radial test on `Re z > -1/2`. -/
theorem introTraceArchimedean_rat_sub_shiftTwo (z : ℂ) (hz : -(1 / 2 : ℝ) < z.re) :
    introTraceArchimedean (F := ℚ) 1
      (fun t ↦ introTracePower z t - introTracePower (z + 2) t) Rat.infinitePlace = 1 / (z + 1 / 2) := by
  let a := -z - 3 / 2
  let p := (Ioi (1 : ℝ)).indicator fun t ↦ (t : ℂ) ^ a
  let q := (Ioi (1 : ℝ)).indicator fun t ↦ (t : ℂ) ^ (a - 1)
  have ha : a.re < -1 := by dsimp [a]; norm_num; linarith
  have ha' : (a - 1).re < -1 := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hp : Integrable p := (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_Ioi_cpow_of_lt ha zero_lt_one)
  have hq : Integrable q := (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_Ioi_cpow_of_lt ha' zero_lt_one)
  have hm (w : ℂ) : Measurable (introTracePower w) := introTraceApprox_mellin_tendsto_power_measurable w
  rw [introTraceArchimedean_rat_sub_shiftTwo_integral (fun t ↦ introTracePower z t -
    introTracePower (z + 2) t) ((hm z).sub (hm (z + 2)))]
  have hbranches (t : ℝ) : ((|t|⁻¹ : ℝ) : ℂ) *
      ((introTracePower z |t| - introTracePower (z + 2) |t|) * (Real.sqrt |t| : ℂ) /
      ((|1 - t| : ℝ) : ℂ)) = (p t + q t) + (p (-t) - q (-t)) := by
    rcases lt_or_ge 1 t with ht | ht
    · have hn : ¬ 1 < -t := by linarith
      have ht0 : 0 < t := by linarith
      simp only [p, q, indicator_of_mem (mem_Ioi.mpr ht),
        indicator_of_notMem (show -t ∉ Ioi 1 from hn), sub_self, add_zero,
        abs_of_pos ht0, abs_of_neg (show 1 - t < 0 by linarith), neg_sub, Complex.ofReal_sub, Complex.ofReal_one]
      rw [← mul_div_assoc]
      exact (introTraceArchimedean_rat_sub_shiftTwo_branches z t ht).1
    · by_cases hn : 1 < -t
      · have ht0 : t < 0 := by linarith
        simp only [p, q, indicator_of_mem (mem_Ioi.mpr hn),
          indicator_of_notMem (show t ∉ Ioi 1 from not_lt.mpr ht), add_zero, zero_add,
          abs_of_neg ht0, abs_of_pos (show 0 < 1 - t by linarith), Complex.ofReal_sub, Complex.ofReal_one]
        rw [← mul_div_assoc]
        simpa only [Complex.ofReal_neg, ← sub_eq_add_neg] using
          (introTraceArchimedean_rat_sub_shiftTwo_branches z (-t) hn).2
      · have hab : ¬ 1 < |t| := not_lt.mpr (abs_le.mpr ⟨by linarith, ht⟩)
        simp [p, q, introTracePower, hab, not_lt.mpr ht, hn]
  simp_rw [hbranches]
  rw [integral_add (f := fun t ↦ p t + q t) (g := fun t ↦ p (-t) - q (-t))
    (hp.add hq) (hp.sub hq).comp_neg, integral_neg_eq_self (fun t ↦ p t - q t),
    integral_add hp hq, integral_sub hp hq]
  have hpval : (∫ t, p t) = 1 / (z + 1 / 2) := by
    rw [show (∫ t, p t) = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ a from integral_indicator measurableSet_Ioi,
      integral_Ioi_cpow_of_lt ha zero_lt_one, Complex.ofReal_one, Complex.one_cpow,
      show a + 1 = -(z + 1 / 2) by dsimp [a]; ring, neg_div_neg_eq]
  rw [hpval]
  ring

/-- Each cutoff is supported a positive distance above one. A cofinal choice
of mollifier indices makes its support radius smaller than this distance. -/
private theorem introTraceApprox_rat_sub_shiftTwo_match (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ IsIntroTraceApproximation h (ρ ∘ k) ∧
      ∀ n t u, h n t ≠ 0 → ρ (k n) u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1 := by
  obtain ⟨hh, hm, hl, ε, hε, hρ⟩ := hA
  have hd (n : ℕ) : ∃ d : ℝ, 0 < d ∧ ∀ t, h n t ≠ 0 → d ≤ t - 1 := by
    rcases (tsupport (h n)).eq_empty_or_nonempty with he | hne
    · exact ⟨1, zero_lt_one, fun t ht ↦ (he ▸ subset_tsupport _ ht : t ∈ (∅ : Set ℝ)).elim⟩
    obtain ⟨x, hx, hmin⟩ := (hh n).2.1.exists_isMinOn hne continuousOn_id
    exact ⟨x - 1, sub_pos.mpr ((hh n).2.2.1 hx), fun t ht ↦
      sub_le_sub_right (isMinOn_iff.mp hmin t (subset_tsupport _ ht)) _⟩
  choose d hd hsep using hd
  have hk (n : ℕ) : ∃ j, n ≤ j ∧ ε j ≤ min 1 (d n) :=
    ((eventually_ge_atTop n).and (hε.eventually_le_const (lt_min zero_lt_one (hd n)))).exists
  choose k hnk hsmall using hk
  have hcof : Tendsto k atTop atTop := tendsto_atTop_mono hnk tendsto_id
  refine ⟨k, hcof, ⟨hh, hm, hl, ε ∘ k, hε.comp hcof, fun n ↦ hρ (k n)⟩, ?_⟩
  intro n t u ht hu
  have hb := abs_le.mpr ((hρ (k n)).2.2.2.1 (subset_tsupport _ hu))
  exact ⟨hb.trans ((hsmall n).trans (min_le_left _ _)),
    hb.trans (((hsmall n).trans (min_le_right _ _)).trans (hsep n t ht))⟩

/-- The shift by two introduces the factor `1-x⁻²`. On a matched mollifier
support this is bounded by a constant times `(t-1)/t`, even as `t` tends to one. -/
private theorem introTraceApprox_rat_sub_shiftTwo_power_bound {a t u : ℝ} {z : ℂ}
    (ht : 1 < t) (hu : |u| ≤ 1) (hsep : |u| ≤ t - 1) (hz : a ≤ z.re) :
    ‖introTracePower z (t - u) - introTracePower (z + 2) (t - u)‖ ≤
      (((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a)) * (8 * (t - 1) / t) := by
  let x := t - u
  have ht0 : 0 < t := by linarith
  have hx1 : 1 ≤ x := by dsimp [x]; linarith [(abs_le.mp hsep).2]
  rcases eq_or_lt_of_le hx1 with he | hx
  · change ‖introTracePower z x - introTracePower (z + 2) x‖ ≤ _
    rw [← he]
    simp only [introTracePower, lt_irrefl, ite_false, ite_true, sub_self, norm_zero]
    positivity
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hxt : t ≤ 2 * x := by dsimp [x] at *; linarith [(abs_le.mp hu).2]
  have hsub : x - 1 ≤ 2 * (t - 1) := by dsimp [x]; linarith [(abs_le.mp hsep).1]
  have hfac : 1 - (x ^ 2)⁻¹ ≤ 8 * (t - 1) / t := by
    have hb : 1 - (x ^ 2)⁻¹ ≤ 2 * (x - 1) / x := by
      field_simp
      nlinarith [sq_nonneg (x - 1)]
    refine hb.trans ((div_le_div_iff₀ hx0 ht0).2 ?_)
    calc 2 * (x - 1) * t ≤ 2 * (2 * (t - 1)) * (2 * x) := by gcongr
      _ = 8 * (t - 1) * x := by ring
  have hcx : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hid : introTracePower z x - introTracePower (z + 2) x =
      introTracePower z x * ((1 - (x ^ 2)⁻¹ : ℝ) : ℂ) := by
    simp only [introTracePower, hx, ite_true]
    rw [show -(z + 2) = -z - 2 by ring, Complex.cpow_sub _ _ hcx, Complex.cpow_ofNat]
    push_cast
    ring
  change ‖introTracePower z x - introTracePower (z + 2) x‖ ≤ _
  have hnn : 0 ≤ 1 - (x ^ 2)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_pow₀ hx.le))
  rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
  exact mul_le_mul (introTraceApprox_mellin_tendsto_power_bound ht (by simpa [x] using hu) hz)
    hfac hnn (by positivity)

/-- A matched convolution inherits the vanishing factor of the shift-two difference,
uniformly on right half-planes. -/
private theorem introTraceApprox_rat_sub_shiftTwo_bound (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ)
    (hmatch : ∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1)
    (n : ℕ) {a t : ℝ} {z : ℂ} (ht : 1 < t) (hz : a ≤ z.re) :
    ‖introTraceApprox (h n) (ρ n) z t - introTraceApprox (h n) (ρ n) (z + 2) t‖ ≤
      (((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a)) * (8 * (t - 1) / t) := by
  let B := (((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a)) * (8 * (t - 1) / t)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  by_cases hzero : h n t = 0
  · simpa [introTraceApprox, hzero, B] using hB
  obtain ⟨ε, _, hρ⟩ := hA.2.2.2
  obtain ⟨_, hsm, hp, hs, hm⟩ := hρ n
  have hc : HasCompactSupport (ρ n) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  have hcast := hc.comp_left (g := Complex.ofReal) (by simp)
  have hi (w : ℂ) : Integrable (fun u : ℝ ↦ (ρ n u : ℂ) * introTracePower w (t - u)) :=
    hcast.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ)
      (Complex.continuous_ofReal.comp hsm.continuous) (introTracePower_locallyIntegrable w) t
  unfold introTraceApprox
  rw [← mul_sub, ← integral_sub (hi z) (hi (z + 2)), norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ((hA.1 n).2.2.2 t).1]
  refine (mul_le_of_le_one_left (norm_nonneg _) ((hA.1 n).2.2.2 t).2).trans ?_
  calc
    _ ≤ ∫ u, ρ n u * B := norm_integral_le_of_norm_le
      ((hsm.continuous.integrable_of_hasCompactSupport hc).mul_const B) (by
        apply Eventually.of_forall
        intro u
        by_cases hu : ρ n u = 0
        · simp [hu]
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp _)]
        obtain ⟨hu1, hsep⟩ := hmatch n t u hzero hu
        exact mul_le_mul_of_nonneg_left (introTraceApprox_rat_sub_shiftTwo_power_bound ht hu1 hsep hz) (hp u))
    _ = B := by rw [integral_mul_const, hm, one_mul]

/-- The fixed-cutoff profiles are continuous and compactly supported. -/
private theorem introTraceApprox_rat_sub_shiftTwo_profile (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    Continuous (introTraceApprox (h n) (ρ n) z) ∧ HasCompactSupport (introTraceApprox (h n) (ρ n) z) := by
  obtain ⟨ε, _, hρ⟩ := hA.2.2.2
  obtain ⟨_, hm, _, hs, _⟩ := hρ n
  have hc : HasCompactSupport (fun u ↦ (ρ n u : ℂ)) :=
    HasCompactSupport.comp_left (g := Complex.ofReal)
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs) (by simp)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun u ↦ (ρ n u : ℂ)) := Complex.ofRealCLM.contDiff.comp hm
  refine ⟨(Complex.continuous_ofReal.comp (hA.1 n).1.continuous).mul ?_,
    ((hA.1 n).2.1.comp_left (g := Complex.ofReal) (by simp)).mul_right⟩
  exact (hc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hg (introTracePower_locallyIntegrable z)).continuous

/-- A continuous compact radial test supported strictly above one has integrable
density on the rational real chart. -/
private theorem introTraceApprox_rat_sub_shiftTwo_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi 1) :
    Integrable (fun t : ℝ ↦ ((|t|⁻¹ : ℝ) : ℂ) * (f |t| * (Real.sqrt |t| : ℂ) / ((|1 - t| : ℝ) : ℂ))) := by
  let W (t : ℝ) := ((|t|⁻¹ : ℝ) : ℂ) * (f |t| * (Real.sqrt |t| : ℂ) / ((|1 - t| : ℝ) : ℂ))
  have hW : Continuous W := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : |x| ≤ 1
    · have he := notMem_tsupport_iff_eventuallyEq.mp (fun ht ↦ (hs ht).not_ge hx)
      apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(continuous_abs.continuousAt (x := x)).tendsto.eventually he] with t ht
      simp [W, show f |t| = 0 from ht]
    · have hab : 0 < |x| := zero_lt_one.trans (lt_of_not_ge hx)
      have hx' : x ≠ 1 := fun he ↦ hx (by simp [he])
      have hden : ((|1 - x| : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (sub_ne_zero.mpr hx'.symm))
      dsimp only [W]
      fun_prop (disch := first | exact hab.ne' | exact hden)
  obtain ⟨R, hR⟩ := hc.bddAbove
  refine hW.integrable_of_hasCompactSupport (exists_compact_iff_hasCompactSupport.mp
    ⟨Icc (-R) R, isCompact_Icc, fun t ht ↦ ?_⟩)
  have hz : f |t| = 0 := by
    by_contra hne
    exact ht (abs_le.mp (hR (subset_tsupport _ hne)))
  simp [W, hz]

/-- The vanishing factor cancels the positive-branch singularity. The remaining
density is integrable at infinity when the lower real bound exceeds minus one half. -/
private theorem introTraceApprox_rat_sub_shiftTwo_density_bound (t a C : ℝ) (hC : 0 ≤ C)
    (ht : 1 < |t|) (v : ℂ) (hv : ‖v‖ ≤ (C * |t| ^ (-a)) * (8 * (|t| - 1) / |t|)) :
    ‖((|t|⁻¹ : ℝ) : ℂ) * (v * (Real.sqrt |t| : ℂ) / ((|1 - t| : ℝ) : ℂ))‖ ≤
      8 * C * |t| ^ (-a - 3 / 2) := by
  let x := |t|
  have hx : 1 < x := ht
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hdiff : x - 1 ≤ |1 - t| := by
    simpa [x, abs_sub_comm t 1] using abs_sub_abs_le_abs_sub t (1 : ℝ)
  have hd : 0 < x - 1 := sub_pos.mpr hx
  rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (abs_nonneg _)),
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_real, Real.norm_of_nonneg (abs_nonneg _)]
  calc
    _ ≤ x⁻¹ * (((C * x ^ (-a)) * (8 * (x - 1) / x)) * Real.sqrt x / (x - 1)) := by
      gcongr
    _ = 8 * C * x ^ (-a - 3 / 2) := by
      rw [Real.sqrt_eq_rpow, show -a - 3 / 2 = (-a + 1 / 2) - 2 by ring,
        Real.rpow_sub hx0, Real.rpow_add hx0, Real.rpow_ofNat]
      field_simp

private theorem introTraceApprox_archimedean_sub_shiftTwo_complexCoordinate (χ : U𝔽) (v : InfinitePlace F) (hw : v.IsComplex) :
    ∃ m : ℂ → ℂ, Measurable m ∧ (∀ t, ‖m t‖ = 1) ∧ ∀ f : ℝ → ℂ, Measurable f →
    (Integrable archIntegrand(χ, f, v) (infiniteLocalMultiplicativeTamagawaMeasure F v) ↔
      Integrable (fun t : ℂ ↦ m t * ((((‖t‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        (f (‖t‖ ^ 2) * (‖t‖ : ℂ) / ((‖1 - t‖ ^ 2 : ℝ) : ℂ)))) (2 • volume)) ∧
    introTraceArchimedean χ f v =
      (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℂ, m t * ((((‖t‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        (f (‖t‖ ^ 2) * (‖t‖ : ℂ) / ((‖1 - t‖ ^ 2 : ℝ) : ℂ))) ∂(2 • volume) := by
  have hν : (2 • (volume : Measure ℂ)).restrict {(0 : ℂ)}ᶜ = 2 • volume := by
    simp [two_smul, Measure.restrict_add, restrict_compl_singleton]
  obtain ⟨m, hm, hnm, _, he⟩ := introTraceApprox_archimedean_sub_shiftTwo_coordinate χ v (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry (2 • volume) hν
    (dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw))
  exact ⟨m, hm, hnm, by
    simpa only [InfinitePlace.not_isReal_iff_isComplex.mpr hw, ite_false, hw.mult_eq_two,
      Real.sqrt_sq (norm_nonneg _)] using he⟩

section

open Complex Metric
open scoped ComplexConjugate ENNReal

private theorem introTraceArchimedean_poisson_nat {r a : ℝ} (ha : |a| < r) (k : ℕ) :
    (2 * Real.pi)⁻¹ • (∫ θ in 0..2 * Real.pi,
      ((r ^ 2 - a ^ 2) / ‖circleMap 0 r θ - (a : ℂ)‖ ^ 2) • (Circle.exp θ : ℂ) ^ k) =
      ((a / r : ℝ) : ℂ) ^ k := by
  have hr : 0 < r := (abs_nonneg a).trans_lt ha
  let f : ℂ → ℂ := fun z ↦ (z / (r : ℂ)) ^ k
  have hf : DiffContOnCl ℂ f (ball 0 r) := Differentiable.diffContOnCl (by dsimp [f]; fun_prop)
  have hw : (a : ℂ) ∈ ball 0 r := by simpa [mem_ball, Complex.norm_real, Real.norm_eq_abs] using ha
  have hp := hf.circleAverage_poissonKernel_smul' hw
  simpa only [Real.circleAverage_def, sub_zero, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr, sq_abs, f, circleMap_zero, ← Circle.coe_exp,
    mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne'), Complex.ofReal_div] using hp

private theorem introTraceArchimedean_poisson_int {r a : ℝ} (ha : |a| < r) (n : ℤ) :
    (2 * Real.pi)⁻¹ • (∫ θ in 0..2 * Real.pi,
      ((r ^ 2 - a ^ 2) / ‖circleMap 0 r θ - (a : ℂ)‖ ^ 2) • (Circle.exp θ : ℂ) ^ n) =
      ((a / r : ℝ) : ℂ) ^ n.natAbs := by
  cases n with
  | ofNat k => exact introTraceArchimedean_poisson_nat ha k
  | negSucc k =>
    have h := congrArg (starRingEnd ℂ) (introTraceArchimedean_poisson_nat ha (k+1))
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, ← intervalIntegral.intervalIntegral_conj,
      map_pow, ← Complex.inv_eq_conj (Circle.norm_coe _), inv_pow] at h
    simpa only [Int.natAbs_negSucc, zpow_negSucc, Complex.real_smul] using h

private theorem introTraceArchimedean_poisson_exterior {r : ℝ} (hr : 1 < r) (n : ℤ) :
    (2 * Real.pi)⁻¹ • (∫ θ in 0..2 * Real.pi,
      (‖(1 : ℂ) - circleMap 0 r θ‖ ^ 2)⁻¹ • (Circle.exp θ : ℂ) ^ n) =
      ((r⁻¹ ^ n.natAbs / (r ^ 2 - 1) : ℝ) : ℂ) := by
  have h := introTraceArchimedean_poisson_int (r := r) (a := 1) (by simpa using hr) n
  let g : ℝ → ℂ := fun θ ↦ (‖(1 : ℂ) - circleMap 0 r θ‖ ^ 2)⁻¹ • (Circle.exp θ : ℂ) ^ n
  have hweighted : (r ^ 2 - 1) • ((2 * Real.pi)⁻¹ • (∫ θ in 0..2 * Real.pi, g θ)) =
      ((r⁻¹ : ℝ) : ℂ) ^ n.natAbs := by
    rw [smul_comm, ← intervalIntegral.integral_smul]
    simpa only [g, smul_smul, ← div_eq_mul_inv, norm_sub_rev (1 : ℂ), Complex.ofReal_one,
      one_pow, one_div] using h
  have hne : r ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (r-1)])
  calc
    _ = (r ^ 2 - 1)⁻¹ • ((r ^ 2 - 1) • ((2 * Real.pi)⁻¹ • (∫ θ in 0..2 * Real.pi, g θ))) :=
      (inv_smul_smul₀ hne _).symm
    _ = _ := by rw [hweighted, Complex.real_smul]; push_cast; ring

open scoped ENNReal

private theorem introTraceArchimedean_plane_average (f : ℂ → ℂ) (hm : Measurable f) (hi : Integrable f) :
    (∫ z, f z) = (2 * Real.pi) • ∫ r in Ioi (0:ℝ), r • Real.circleAverage f 0 r := by
  let F (p : ℝ × ℝ) := p.1 • f (Complex.polarCoord.symm p)
  have hpol : Measurable (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hF : IntegrableOn F polarCoord.target := by
    refine ⟨(measurable_fst.smul (hm.comp hpol)).aestronglyMeasurable, ?_⟩
    apply hasFiniteIntegral_iff_eNorm.mpr
    calc
      (∫⁻ p in polarCoord.target, ‖F p‖ₑ) = ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 • ‖f (Complex.polarCoord.symm p)‖ₑ := by
        apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp
        have hr : 0 < p.1 := hp.1
        have hx : ‖p.1‖ₑ = ENNReal.ofReal p.1 := by
          rw [← ofReal_norm p.1, Real.norm_eq_abs, abs_of_pos hr]
        exact (eNorm_smul p.1 _).trans (congrArg (· * ‖f (Complex.polarCoord.symm p)‖ₑ) hx)
      _ = ∫⁻ z, ‖f z‖ₑ := Complex.lintegral_comp_polarCoord_symm (fun z : ℂ ↦ ‖f z‖ₑ)
      _ < ∞ := hasFiniteIntegral_iff_eNorm.mp hi.hasFiniteIntegral
  have hp (r θ : ℝ) : Complex.polarCoord.symm (r,θ) = circleMap 0 r θ := by
    simp [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I]
  have hcircle (r : ℝ) : (∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) =
      (2 * Real.pi) • Real.circleAverage f 0 r := by
    have he := ((periodic_circleMap 0 r).comp f).intervalIntegral_add_eq 0 (-Real.pi)
    rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      integral_Ioc_eq_integral_Ioo] at he
    rw [Real.circleAverage_def, smul_inv_smul₀ (ne_of_gt Real.two_pi_pos)]
    exact he.symm
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, F p ∂(volume.prod volume)) = _
  rw [setIntegral_prod (μ := volume) (ν := volume) F hF, ← MeasureTheory.integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  simp only [F, hp, MeasureTheory.integral_smul, hcircle, smul_comm r (2 * Real.pi)]

/-- Angular integration of an exterior Fourier mode, with Euclidean area measure. -/
private theorem introTraceArchimedean_plane_exterior (f : ℂ → ℂ) (b : ℝ → ℂ) (n : ℤ)
    (hm : Measurable f) (hi : Integrable f)
    (hb : ∀ r : ℝ, r ≤ 1 → 0 ≤ r → b r = 0)
    (hs : ∀ r : ℝ, 0 < r → ∀ θ : ℝ, f (circleMap 0 r θ) =
      b r * ((‖(1 : ℂ) - circleMap 0 r θ‖ ^ 2)⁻¹ • (Circle.exp θ : ℂ) ^ n)) :
    (∫ z, f z) = (2 * Real.pi) • ∫ r in Ioi (1 : ℝ),
      r • (b r * ((r⁻¹ ^ n.natAbs / (r ^ 2 - 1) : ℝ) : ℂ)) := by
  have hc (r : ℝ) (hr : 0 < r) : Real.circleAverage f 0 r =
      b r * ((r⁻¹ ^ n.natAbs / (r ^ 2 - 1) : ℝ) : ℂ) := by
    rw [Real.circleAverage_def, show (fun θ ↦ f (circleMap 0 r θ)) = _ from funext (hs r hr)]
    rw [intervalIntegral.integral_const_mul, Complex.real_smul, mul_left_comm]
    by_cases h1 : 1 < r
    · rw [← Complex.real_smul, introTraceArchimedean_poisson_exterior h1 n]
    · simp [hb r (le_of_not_gt h1) hr.le]
  rw [introTraceArchimedean_plane_average f hm hi]
  congr 1
  calc
    _ = ∫ r in Ioi (0 : ℝ), r • (b r * ((r⁻¹ ^ n.natAbs / (r ^ 2 - 1) : ℝ) : ℂ)) :=
      setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ congrArg (r • ·) (hc r hr)
    _ = _ := (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi zero_le_one) fun r hr ↦ by
        have hle : r ≤ 1 := le_of_not_gt hr.2
        simp [hb r hle (le_of_lt hr.1)])

/-- At a complex place, angular integration leaves the absolute value of the character's integer frequency. -/
private theorem introTraceArchimedean_complex_radial (χ : U𝔽) (w : InfinitePlace F)
    (hw : w.IsComplex) (f : ℝ → ℂ) (hf : Measurable f) (hz : ∀ x, x ≤ 1 → f x = 0)
    (hi : Integrable archIntegrand(χ, f, w) (infiniteLocalMultiplicativeTamagawaMeasure F w)) :
    let p := (complexHeckeCharacter_parameters χ w hw).exists.choose
    introTraceArchimedean χ f w = 2 * ∫ r in Ioi (1 : ℝ),
      star ((((r ^ 2 : ℝ) : ℂ)) ^ p.1) * f (r ^ 2) *
        ((r⁻¹ ^ p.2.natAbs / (r ^ 2 - 1) : ℝ) : ℂ) := by
  intro p
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  have hν : (2 • (volume : Measure ℂ)).restrict {(0 : ℂ)}ᶜ = 2 • volume := by
    simp [two_smul, Measure.restrict_add, restrict_compl_singleton]
  obtain ⟨m, hmu, hm, -, -, -, -, hchart⟩ := introTraceArchimedean_coordinate_character χ w e
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry (2 • volume) hν
    (dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw))
  let G (z : ℂ) := m z * ((((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
    (f (‖z‖ ^ 2) * (‖z‖ : ℂ) / ((‖1 - z‖ ^ 2 : ℝ) : ℂ)))
  have hGm : Measurable G := by dsimp [G]; fun_prop
  obtain ⟨hGi, hv⟩ := hchart f hf
  rw [if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr hw)] at hv
  simp only [hw.mult_eq_two, Real.sqrt_sq (norm_nonneg _)] at hv hGi hi
  change introTraceArchimedean χ f w = (1 / (2 * (Real.pi : ℂ))) * ∫ z, G z ∂(2 • volume) at hv
  have hG : Integrable G volume := by
    have h : Integrable G (2 • volume) := hGi.mp hi
    simpa only [two_smul, integrable_add_measure, and_self] using h
  let b (r : ℝ) := star (((r ^ 2 : ℝ) : ℂ) ^ p.1) * f (r ^ 2) / (r : ℂ)
  have hunit (r θ : ℝ) (hr : 0 < r) : m (circleMap 0 r θ) =
      star (((r^2 : ℝ) : ℂ) ^ p.1) * (Circle.exp θ : ℂ) ^ (-p.2) := by
    let z := circleMap 0 r θ
    have hn : ‖z‖ = r := (norm_circleMap_zero _ _).trans (abs_of_pos hr)
    have hne : z ≠ 0 := norm_ne_zero_iff.mp (hn.trans_ne hr.ne')
    let u := Units.mk0 z hne
    let v := Units.map e.symm.toMonoidHom u
    have he : e v.val = z := e.apply_symm_apply _
    have hh := hmu v
    rw [he] at hh
    have hp := (complexHeckeCharacter_parameters χ w hw).exists.choose_spec.2 u
    change (χ (IdeleClassGroup.ofCompletion (𝓞 F) F w v) : ℂ) * _ ^ (0 : ℂ) = _ at hp
    rw [Complex.cpow_zero, mul_one] at hp
    change (χ (IdeleClassGroup.ofCompletion (𝓞 F) F w v) : ℂ) =
      ((‖z‖ ^ 2 : ℝ) : ℂ) ^ p.1 * (z / (‖z‖ : ℂ)) ^ p.2 at hp
    rw [hh, hp, hn]
    have ha : z / (r : ℂ) = (Circle.exp θ : ℂ) := by
      rw [show z = (r : ℂ) * (Circle.exp θ : ℂ) by simp [z, circleMap_zero, Circle.coe_exp],
        mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
    rw [ha]
    change conj (_ * _) = conj _ * _
    rw [map_mul, map_zpow₀, ← Complex.inv_eq_conj (Circle.norm_coe _), inv_zpow, zpow_neg]
  have hs (r : ℝ) (hr : 0 < r) (θ : ℝ) : G (circleMap 0 r θ) =
      b r * ((‖(1 : ℂ) - circleMap 0 r θ‖ ^ 2)⁻¹ • (Circle.exp θ : ℂ) ^ (-p.2)) := by
    dsimp only [G, b]
    rw [hunit r θ hr, norm_circleMap_zero, abs_of_pos hr, Complex.real_smul]
    push_cast
    field_simp
  have hvan (r : ℝ) (hr : r ≤ 1) : 0 ≤ r → b r = 0 := by
    intro h0
    have hsq : r ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) (by linarith : 0 ≤ 1+r)]
    simp only [b, hz (r ^ 2) hsq, mul_zero, zero_div]
  have hplane := introTraceArchimedean_plane_exterior G b (-p.2) hGm hG hvan hs
  rw [hv, two_smul, integral_add_measure hG hG, hplane]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, Int.natAbs_neg]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show ∀ x : ℂ, 1 / (2 * (Real.pi : ℂ)) *
        (2 * (Real.pi : ℂ) * x + 2 * (Real.pi : ℂ) * x) = 2 * x by intro x; field_simp; ring]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only [b]
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hr).ne'
  field_simp

private theorem introTraceArchimedean_exp_half_subst (g : ℝ → ℂ) :
    (∫ r in Ioi (1 : ℝ), g r) =
      ∫ t in Ioi (0 : ℝ), (Real.exp (t/2)/2) • g (Real.exp (t/2)) := by
  let h (t : ℝ) := Real.exp (t / 2)
  have him : h '' Ioi 0 = Ioi 1 := by
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Real.one_lt_exp_iff.mpr (by linarith [show 0 < t from ht])
    · intro hr
      refine ⟨2 * Real.log r, mul_pos (by norm_num) (Real.log_pos hr), ?_⟩
      dsimp [h]
      rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.exp_log (zero_lt_one.trans hr)]
  rw [← him]
  apply integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioi
  · intro t _
    simpa only [h, Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using
      (Real.hasDerivAt_exp (t / 2) |>.comp t ((hasDerivAt_id t).div_const 2)).hasDerivWithinAt
  · exact fun x _ y _ hxy ↦ Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hxy (by norm_num))

private theorem introTraceArchimedean_gamma_density (a : ℂ) (ha : a.re = 0) (k : ℕ) (t : ℝ)
    (ht : 0 < t) :
    let r := Real.exp (t / 2)
    (r : ℂ) * star ((((r ^ 2 : ℝ) : ℂ)) ^ a) * ((r⁻¹ ^ k / (r ^ 2 - 1) : ℝ) : ℂ) =
      Complex.exp (-(1/2 + a + (k : ℂ)/2) * (t : ℂ)) / (1 - (Real.exp (-t) : ℝ)) := by
  intro r
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : 1 < r := Real.one_lt_exp_iff.mpr (by linarith)
  have hr2 : r ^ 2 = Real.exp t := by
    dsimp only [r]
    rw [sq, ← Real.exp_add, add_halves]
  have hconj : conj a = -a := by apply Complex.ext <;> simp [ha]
  have hcp : star (((r ^ 2 : ℝ) : ℂ) ^ a) = Complex.exp (-a * (t : ℂ)) := by
    rw [hr2, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
    change conj (Complex.exp _) = _
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, hconj, mul_comm]
  have he : Complex.exp (-((t : ℂ)/2)) = (r : ℂ)⁻¹ := by
    rw [Complex.exp_neg]
    simp only [r, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hk : Complex.exp (-(1/2 + a + (k : ℂ)/2) * (t : ℂ)) =
      (r : ℂ)⁻¹ * Complex.exp (-a * (t : ℂ)) * ((r : ℂ)⁻¹)^k := by
    rw [show -(1/2 + a + (k : ℂ)/2) * (t : ℂ) =
      -((t : ℂ)/2) + -a * (t : ℂ) + (k : ℂ) * -((t : ℂ)/2) by ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, he]
  rw [hcp, hk, Real.exp_neg, ← hr2]
  push_cast
  have hr : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hd : (r : ℂ)^2 - 1 ≠ 0 := by exact_mod_cast ne_of_gt (by nlinarith [sq_nonneg (r-1)] : 0 < r^2-1)
  field_simp

/-- Paper: §1.4.1, p. 28, and Theorem B.4.2.2, p. 616. For a radial test supported
above norm one the complex local trace term equals the negative digamma integral. -/
private theorem introTraceArchimedean_complex_eq_neg_digamma (χ : U𝔽) (w : InfinitePlace F)
    (hw : w.IsComplex) (f : ℝ → ℂ) (hf : Measurable f) (hz : ∀ x, x ≤ 1 → f x = 0)
    (hi : Integrable archIntegrand(χ, f, w) (infiniteLocalMultiplicativeTamagawaMeasure F w)) :
    let p := (complexHeckeCharacter_parameters χ w hw).exists.choose
    introTraceArchimedean χ f w = -(∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
      (1/2 + p.1 + (p.2.natAbs : ℂ)/2) (1/2 - p.1 + (p.2.natAbs : ℂ)/2)
      (fun y ↦ f (Real.exp y)) t) := by
  intro p
  rw [introTraceArchimedean_complex_radial χ w hw f hf hz hi, introTraceArchimedean_exp_half_subst,
    ← integral_const_mul, ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  let r := Real.exp (t/2)
  have hr2 : r ^ 2 = Real.exp t := by dsimp [r]; rw [sq, ← Real.exp_add, add_halves]
  have hφ0 : f (Real.exp 0) = 0 := by rw [Real.exp_zero]; exact hz 1 le_rfl
  have hφn : f (Real.exp (-t)) = 0 := hz _ (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_of_lt ht)))
  have hden := introTraceArchimedean_gamma_density p.1
    (complexHeckeCharacter_parameters χ w hw).exists.choose_spec.1 p.2.natAbs t ht
  change (r : ℂ) * _ * _ = _ at hden
  simp only [heckeArchimedeanDigammaKernel, hφ0, hφn, one_mul, mul_zero, zero_div, zero_mul, add_zero,
    zero_sub, neg_neg, Complex.ofReal_one]
  change 2 * ((r / 2) • (star (((r^2 : ℝ) : ℂ)^p.1) * f (r^2) * _)) = _
  rw [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [show 2 * ((r : ℂ) / 2 * (star (((r^2 : ℝ) : ℂ)^p.1) * f (r^2) *
      ((r⁻¹ ^ p.2.natAbs / (r ^ 2 - 1) : ℝ) : ℂ))) =
      f (r^2) * ((r : ℂ) * star (((r^2 : ℝ) : ℂ)^p.1) *
      ((r⁻¹ ^ p.2.natAbs / (r ^ 2 - 1) : ℝ) : ℂ)) by ring, hden, hr2]
  ring

/-- The even and odd real characters give the two sign averages in the real gamma factor. -/
private theorem introTraceArchimedean_real_radial (χ : U𝔽) (w : InfinitePlace F)
    (hw : w.IsReal) (f : ℝ → ℂ) (hf : Measurable f) (hz : ∀ x, x ≤ 1 → f x = 0)
    (hi : Integrable archIntegrand(χ, f, w) (infiniteLocalMultiplicativeTamagawaMeasure F w)) :
    let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    introTraceArchimedean χ f w = ∫ r in Ioi (1 : ℝ),
      star ((r : ℂ) ^ p.1) * f r * (Real.sqrt r : ℂ) *
        ((r⁻¹ ^ p.2.val / (r ^ 2 - 1) : ℝ) : ℂ) := by
  intro p
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  obtain ⟨m, hmu, -, -, -, -, -, hchart⟩ := introTraceArchimedean_coordinate_character χ w e
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).isometry volume
    (restrict_compl_singleton (μ := volume) 0) (dite_eq_left hw)
  let G (x : ℝ) := m x * (((|x|⁻¹ : ℝ) : ℂ) *
    (f |x| * (Real.sqrt |x| : ℂ) / ((|1 - x| : ℝ) : ℂ)))
  obtain ⟨hGi, hv⟩ := hchart f hf
  have hG : Integrable G := by
    simpa only [G, hw.mult_eq_one, pow_one, Real.norm_eq_abs] using (hGi.mp hi)
  have hval : introTraceArchimedean χ f w = (1 / 2 : ℂ) * ∫ x, G x := by
    simpa only [G, hw, ite_true, hw.mult_eq_one, pow_one, Real.norm_eq_abs] using hv
  have hunit (x : ℝ) (hx : x ≠ 0) : m x = star (((|x| : ℝ) : ℂ) ^ p.1) *
      (if 0 < x then 1 else (-1 : ℂ)) ^ p.2.val := by
    let u := Units.mk0 x hx
    let v := Units.map e.symm.toMonoidHom u
    have hh := hmu v
    rw [show e v.val = x from e.apply_symm_apply _] at hh
    have hp := (realHeckeCharacter_parameters χ w hw).exists.choose_spec.2 u
    change (χ (IdeleClassGroup.ofCompletion (𝓞 F) F w v) : ℂ) * _ ^ (0 : ℂ) = _ at hp
    rw [Complex.cpow_zero, mul_one] at hp
    change (χ (IdeleClassGroup.ofCompletion (𝓞 F) F w v) : ℂ) =
      ((|x| : ℝ) : ℂ) ^ p.1 * (if 0 < x then 1 else (-1 : ℂ)) ^ p.2.val at hp
    rw [hh, hp]
    split <;> simp
  have hneg : (∫ x in Iic (0 : ℝ), G x) = ∫ x in Ioi (0 : ℝ), G (-x) := by
    simpa using (integral_comp_neg_Ioi 0 G).symm
  rw [hval, ← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hG, compl_Ioi, hneg,
    ← integral_add hG.integrableOn hG.comp_neg.integrableOn, ← integral_const_mul]
  have hsmall (r : ℝ) (hr : 0 < r) (hu : r ≤ 1) :
      (1 / 2 : ℂ) * (G r + G (-r)) = 0 := by
    simp only [G, abs_neg, abs_of_pos hr, hz r hu, zero_mul, zero_div, mul_zero, add_zero]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi zero_le_one) (fun r hr ↦ hsmall r hr.1 (le_of_not_gt hr.2))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr1 : 1 < r := hr
  have h0 : 0 < r := zero_lt_one.trans hr1
  have hminus : 0 ≤ 1 + r := by linarith
  have habs : |1 - r| = r - 1 := by rw [abs_of_neg (sub_neg.mpr hr)]; ring
  simp only [G, hunit r h0.ne', hunit (-r) (neg_ne_zero.mpr h0.ne'), h0, ite_true,
    not_lt_of_ge (neg_nonpos.mpr h0.le), ite_false, abs_neg, abs_of_pos h0, habs,
    sub_neg_eq_add, abs_of_nonneg hminus, one_pow, mul_one]
  have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  have hm : (r : ℂ) - 1 ≠ 0 := by exact_mod_cast (sub_pos.mpr hr).ne'
  have hp : 1 + (r : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1:ℝ) + r ≠ 0)
  have hd : (r : ℂ)^2 - 1 ≠ 0 := by exact_mod_cast ne_of_gt (by nlinarith [sq_nonneg (r-1)] : 0 < r^2-1)
  generalize hε : p.2 = ε
  fin_cases ε <;> push_cast <;> norm_num <;> field_simp <;> ring

/-- The parity sign average cancels one factor of the real digamma denominator. -/
private theorem introTraceArchimedean_real_eq_neg_digamma (χ : U𝔽) (w : InfinitePlace F)
    (hw : w.IsReal) (f : ℝ → ℂ) (hf : Measurable f) (hz : ∀ x, x ≤ 1 → f x = 0)
    (hi : Integrable archIntegrand(χ, f, w) (infiniteLocalMultiplicativeTamagawaMeasure F w)) :
    let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    introTraceArchimedean χ f w = -(∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1/2)
      ((1/2 + p.1 + p.2.val)/2) ((1/2 - p.1 + p.2.val)/2)
      (fun y ↦ f (Real.exp y)) t) := by
  intro p
  rw [introTraceArchimedean_real_radial χ w hw f hf hz hi, introTraceArchimedean_exp_half_subst,
    ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  let r := Real.exp (t/2)
  have hr0 : 0 < r := Real.exp_pos _
  have ha : p.1.re = 0 := (realHeckeCharacter_parameters χ w hw).exists.choose_spec.1
  have hden := introTraceArchimedean_gamma_density (p.1/2) (by simp [ha]) p.2.val t ht
  have hpow : (((r ^ 2 : ℝ) : ℂ)) ^ (p.1/2) = (r : ℂ)^p.1 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (pow_pos hr0 2).ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr0.ne'), ← Complex.ofReal_log (sq_nonneg r),
      ← Complex.ofReal_log hr0.le, Real.log_pow]
    congr 1
    push_cast
    ring
  change (r : ℂ) * star ((((r ^ 2 : ℝ) : ℂ)) ^ (p.1/2)) * _ = _ at hden
  rw [hpow] at hden
  have hroot : (Real.sqrt r : ℂ) = Complex.exp ((t : ℂ)/4) := by
    rw [show Real.sqrt r = Real.exp ((t/2)/2) from (Real.exp_half _).symm, Complex.ofReal_exp]
    congr 1; push_cast; ring
  have he : (Real.sqrt r : ℂ) * Complex.exp (-(1/2 + p.1/2 + (p.2.val : ℂ)/2) * (t : ℂ)) =
      Complex.exp (-((1/2 + p.1 + (p.2.val : ℂ))/2) * (t : ℂ)) := by
    rw [hroot, ← Complex.exp_add]; congr 1; ring
  have hφ0 : f (Real.exp 0) = 0 := by rw [Real.exp_zero]; exact hz 1 le_rfl
  have hφn : f (Real.exp (-(1/2*t))) = 0 :=
    hz _ (Real.exp_le_one_iff.mpr (by linarith [show 0 < t from ht]))
  simp only [heckeArchimedeanDigammaKernel, hφ0, hφn, mul_zero, zero_mul, add_zero, zero_div,
    zero_sub, mul_neg, neg_neg]
  rw [show (1/2 : ℝ)*t = t/2 by ring]
  change (r/2) • (star ((r : ℂ)^p.1) * f r * (Real.sqrt r : ℂ) * _) = _
  rw [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [show (r : ℂ)/2 * (star ((r : ℂ)^p.1) * f r * (Real.sqrt r : ℂ) *
      ((r⁻¹ ^ p.2.val / (r^2-1) : ℝ) : ℂ)) = (1/2 : ℂ) * f r * ((Real.sqrt r : ℂ) *
      ((r : ℂ) * star ((r : ℂ)^p.1) * ((r⁻¹ ^ p.2.val / (r^2-1) : ℝ) : ℂ))) by ring,
    hden, ← mul_div_assoc, he]
  push_cast
  ring

open Classical in
/-- Paper: §1.4.1, p. 28; Theorem B.4.2.2, p. 616. On an integrable test supported above
norm one, the local trace integral equals the negative archimedean digamma term of the
explicit formula. At a real place the two signs recover the parity of the local character.
At a complex place the Poisson integral gives its absolute angular frequency. -/
theorem introTraceArchimedean_eq_neg_digamma_of_supported_above_one (χ : U𝔽) (w : InfinitePlace F)
    (f : ℝ → ℂ) (hf : Measurable f) (hz : ∀ x, x ≤ 1 → f x = 0)
    (hi : Integrable archIntegrand(χ, f, w) (infiniteLocalMultiplicativeTamagawaMeasure F w)) :
    introTraceArchimedean χ f w = -(if hw : w.IsReal then
      let p := (realHeckeCharacter_parameters χ w hw).exists.choose
      ∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1/2)
        ((1/2 + p.1 + p.2.val)/2) ((1/2 - p.1 + p.2.val)/2) (fun y ↦ f (Real.exp y)) t
    else
      let p := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
      ∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
        (1/2 + p.1 + (p.2.natAbs : ℂ)/2) (1/2 - p.1 + (p.2.natAbs : ℂ)/2)
        (fun y ↦ f (Real.exp y)) t) := by
  split_ifs with hw
  · exact introTraceArchimedean_real_eq_neg_digamma χ w hw f hf hz hi
  · exact introTraceArchimedean_complex_eq_neg_digamma χ w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) f hf hz hi

/-- Inversion preserves the square-root weight divided by the normalized distance from one. -/
private theorem introTraceArchimedean_inv_weight {K : Type*} [NormedField K] (v : Kˣ) (m : ℕ) :
    Real.sqrt (‖(v⁻¹).val‖ ^ m) / ‖1 - (v⁻¹).val‖ ^ m =
      Real.sqrt (‖v.val‖ ^ m) / ‖1 - v.val‖ ^ m := by
  have h : 1 - (v.val)⁻¹ = (v.val - 1) / v.val := by field_simp
  have hn := norm_pos_iff.mpr v.ne_zero
  have hs := Real.sq_sqrt (pow_nonneg hn.le m)
  have hpos : 0 < Real.sqrt (‖v.val‖ ^ m) := Real.sqrt_pos.2 (pow_pos hn m)
  rw [Units.val_inv_eq_inv_val, h, norm_div, norm_sub_rev v.val 1, norm_inv, inv_pow,
    Real.sqrt_inv, div_pow]
  by_cases he : ‖1 - v.val‖ ^ m = 0
  · simp [he]
  · field_simp [he, ne_of_gt hpos, pow_ne_zero m hn.ne']
    nlinarith

/-- Inverting a local unit exchanges a profile with its conjugate at the reciprocal radius. -/
private theorem introTraceArchimedean_inv_integrand (χ : U𝔽) (w : InfinitePlace F)
    (h : ℝ → ℂ) (u : w.Completionˣ) :
    archIntegrand(χ, (fun x ↦ conj (h x⁻¹)), w) u =
      conj (archIntegrand(χ, h, w) u⁻¹) := by
  have hc : (χ (archClass(w) u⁻¹) : ℂ) = conj (χ (archClass(w) u) : ℂ) := by
    rw [map_inv, map_inv, Circle.coe_inv_eq_conj]
  have hn : (((ideleClassNorm F) (archClass(w) u⁻¹)).val : ℝ) =
      ((((ideleClassNorm F) (archClass(w) u)).val : ℝ))⁻¹ := by simp
  have hw := congrArg (fun r : ℝ ↦ (r : ℂ)) (introTraceArchimedean_inv_weight u w.mult)
  simp only [Complex.ofReal_div] at hw
  simp only [introTraceTest, map_div₀, map_mul, Complex.conj_ofReal, hc, hn,
    ← Complex.star_def, star_star, mul_div_assoc]
  rw [hw]

/-- The normalized Haar integral commutes with conjugation and inversion of the radial profile. -/
private theorem introTraceArchimedean_conj_inv (χ : U𝔽) (w : InfinitePlace F)
    (h : ℝ → ℂ) :
    introTraceArchimedean χ (fun x ↦ conj (h x⁻¹)) w = conj (introTraceArchimedean χ h w) := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology w.Completionˣ :=
    (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
  let μ := infiniteLocalMultiplicativeTamagawaMeasure F w
  let : μ.IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure w
  have hi : (∫ u, archIntegrand(χ, (fun x ↦ conj (h x⁻¹)), w) u ∂μ) =
      conj (∫ u, archIntegrand(χ, h, w) u ∂μ) := by
    simp_rw [introTraceArchimedean_inv_integrand χ w h]
    rw [integral_conj, integral_inv_eq_self (archIntegrand(χ, h, w)) μ]
  unfold introTraceArchimedean
  rw [hi, map_mul]
  congr 1
  have htwo : conj (2 : ℂ) = 2 := by exact_mod_cast Complex.conj_ofReal (2 : ℝ)
  split_ifs <;> simp [htwo]

/-- Restriction of an integrable local term to radii above one preserves integrability. -/
private theorem introTraceArchimedean_above_integrable (χ : U𝔽) (w : InfinitePlace F)
    (h : ℝ → ℂ)
    (hi : Integrable (archIntegrand(χ, h, w)) (infiniteLocalMultiplicativeTamagawaMeasure F w)) :
    Integrable (archIntegrand(χ, ((Ioi (1 : ℝ)).indicator h), w)) (infiniteLocalMultiplicativeTamagawaMeasure F w) := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let N (u : w.Completionˣ) : ℝ := ‖u.val‖ ^ w.mult
  have hN (u : w.Completionˣ) : (((ideleClassNorm F) (archClass(w) u)).val : ℝ) = N u := by
    rw [ideleClassNorm_ofCompletion]
    rfl
  have hm : MeasurableSet (N ⁻¹' Ioi 1) :=
    ((continuous_norm.comp Units.continuous_val).pow w.mult).measurable measurableSet_Ioi
  apply (hi.indicator hm).congr
  apply Eventually.of_forall
  intro u
  by_cases hu : 1 < N u <;> simp only [introTraceTest, Set.indicator, Set.mem_preimage,
    Set.mem_Ioi, hN, hu, ite_true, ite_false, mul_zero, zero_mul, zero_div]

/-- Inversion and conjugation preserve absolute integrability of a local term. -/
private theorem introTraceArchimedean_inv_integrable (χ : U𝔽) (w : InfinitePlace F)
    (h : ℝ → ℂ)
    (hi : Integrable (archIntegrand(χ, h, w)) (infiniteLocalMultiplicativeTamagawaMeasure F w)) :
    Integrable (archIntegrand(χ, (fun x ↦ conj (h x⁻¹)), w)) (infiniteLocalMultiplicativeTamagawaMeasure F w) := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology w.Completionˣ :=
    (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
  let μ := infiniteLocalMultiplicativeTamagawaMeasure F w
  let : μ.IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure w
  change Integrable (archIntegrand(χ, h, w)) μ at hi
  have hstar := memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr hi.comp_inv).star
  refine hstar.congr (Eventually.of_forall fun u ↦ ?_)
  exact (introTraceArchimedean_inv_integrand χ w h u).symm

/-- When the profile vanishes at one, splitting the local integral produces two one-sided profiles. -/
private theorem introTraceArchimedean_two_halves (χ : U𝔽) (w : InfinitePlace F)
    (h : ℝ → ℂ) (h₁ : h 1 = 0)
    (hi : Integrable (archIntegrand(χ, h, w)) (infiniteLocalMultiplicativeTamagawaMeasure F w)) :
    let P := (Ioi (1 : ℝ)).indicator h
    let M := (Ioi (1 : ℝ)).indicator (fun x : ℝ ↦ conj (h x⁻¹))
    introTraceArchimedean χ h w = introTraceArchimedean χ P w + conj (introTraceArchimedean χ M w) := by
  intro P M
  let q (x : ℝ) := conj (M x⁻¹)
  have hP := introTraceArchimedean_above_integrable χ w h hi
  have hM := introTraceArchimedean_above_integrable χ w _ (introTraceArchimedean_inv_integrable χ w h hi)
  have hq := introTraceArchimedean_inv_integrable χ w M hM
  have he (x : ℝ) (hx : 0 < x) : h x = P x + q x := by
    rcases lt_trichotomy x 1 with hl|rfl|hr
    · have hr' : 1 < x⁻¹ := (one_lt_inv₀ hx).mpr hl
      simp [P, q, M, hr', not_lt.mpr hl.le]
    · simp [P, q, M, h₁]
    · have hl' : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr.le
      simp [P, q, M, hr, not_lt.mpr hl']
  rw [← introTraceArchimedean_conj_inv χ w M]
  change introTraceArchimedean χ h w = introTraceArchimedean χ P w + introTraceArchimedean χ q w
  unfold introTraceArchimedean
  rw [← mul_add, ← integral_add hP hq]
  congr 1
  apply integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  simp only [introTraceTest]
  rw [he _ (NNReal.coe_pos.mpr (Units.zero_lt _))]
  ring

/-- The zero of a differentiable compact profile cancels the denominator at the origin. -/
private theorem introTraceArchimedean_sample_integrable (g : ℝ → ℂ) (hc : Continuous g)
    (hd : DifferentiableAt ℝ g 0) (hs : HasCompactSupport g) (hz : g 0 = 0)
    (b : ℝ) (hb : b ≠ 0) (v : ℂ) :
    IntegrableOn (fun t : ℝ ↦ g (b*t) * Complex.exp (-v * t) / (1 - (Real.exp (-t) : ℂ))) (Ioi 0) := by
  let G (t : ℝ) := g (b*t)
  let D (t : ℝ) := 1 - Real.exp (-t)
  have hG : Continuous G := hc.comp (continuous_const.mul continuous_id)
  have hg : DifferentiableAt ℝ G 0 := by
    dsimp [G]
    have h₀ : DifferentiableAt ℝ g (b * 0) := by simpa using hd
    exact h₀.comp 0 (show DifferentiableAt ℝ (fun t : ℝ ↦ b*t) 0 by fun_prop)
  have hD' : HasDerivAt D 1 0 := by
    have he := (Real.hasDerivAt_exp (-(0 : ℝ))).comp 0 (hasDerivAt_id (0 : ℝ)).neg
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub he using 1 <;> norm_num [D, Function.comp_def, Pi.sub_def]
  have hN : Continuous (dslope G 0) := continuousOn_univ.mp
    ((continuousOn_dslope univ_mem).mpr ⟨hG.continuousOn, hg⟩)
  have hD : Continuous (dslope D 0) := continuousOn_univ.mp
    ((continuousOn_dslope univ_mem).mpr ⟨(show Continuous D by dsimp [D]; fun_prop).continuousOn,
      hD'.differentiableAt⟩)
  have hne (t : ℝ) : dslope D 0 t ≠ 0 := by
    by_cases ht : t = 0
    · subst t
      rw [dslope_same, hD'.deriv]
      norm_num
    · rw [dslope_of_ne D ht]
      have hE : 1 - Real.exp (-t) ≠ 0 := by
        intro e
        have he : Real.exp (-t) = Real.exp 0 := by rw [Real.exp_zero]; exact (sub_eq_zero.mp e).symm
        exact ht (by linarith [Real.exp_injective he])
      simpa [slope, D, ht] using hE
  have hGcs : HasCompactSupport G := hs.comp_homeomorph (Homeomorph.mulLeft₀ b hb)
  have hNs : HasCompactSupport (dslope G 0) := by
    rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at hGcs ⊢
    filter_upwards [hGcs, (isCompact_singleton (x := (0:ℝ))).compl_mem_cocompact] with t ht hne
    have ht0 : t ≠ 0 := hne
    rw [dslope_of_ne G ht0]
    simp [slope, ht, G, hz] at *
  let A (t : ℝ) := (dslope G 0 t) * Complex.exp (-v * t) / ((dslope D 0 t : ℝ) : ℂ)
  have hA : Continuous A := (hN.mul (by fun_prop)).div (Complex.continuous_ofReal.comp hD)
    (fun t ↦ Complex.ofReal_ne_zero.mpr (hne t))
  have hAs : HasCompactSupport A := by
    change HasCompactSupport (fun t ↦ dslope G 0 t * _ / _)
    simpa only [div_eq_mul_inv, Pi.mul_def] using
      (hNs.mul_right (f' := fun t : ℝ ↦ Complex.exp (-v * t))).mul_right
        (f' := fun t : ℝ ↦ ((dslope D 0 t : ℝ) : ℂ)⁻¹)
  refine (hA.integrable_of_hasCompactSupport hAs).integrableOn.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 := ne_of_gt (show 0 < t from ht)
  simp only [A, dslope_of_ne G ht0, dslope_of_ne D ht0, slope, G, D, sub_zero, hz, mul_zero,
    neg_zero, Real.exp_zero, sub_self, vsub_eq_sub, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]
  field_simp [Complex.ofReal_ne_zero.mpr ht0]

/-- The two samples of the digamma kernel correspond to the two half-lines of the logarithmic profile. -/
private theorem introTraceArchimedean_kernel_two_halves (g : ℝ → ℂ) (hc : Continuous g)
    (hd : DifferentiableAt ℝ g 0) (hs : HasCompactSupport g) (hz : g 0 = 0)
    (k : ℝ) (hk : 0 < k) (v : ℂ) :
    let P (y : ℝ) := if 0 < y then g y else 0
    let M (y : ℝ) := if 0 < y then conj (g (-y)) else 0
    let K := heckeArchimedeanDigammaKernel k v (conj v)
    (∫ t in Ioi (0:ℝ), K g t) = (∫ t in Ioi (0:ℝ), K P t) + conj (∫ t in Ioi (0:ℝ), K M t) := by
  intro P M K
  let D (t : ℝ) : ℂ := 1 - (Real.exp (-t) : ℂ)
  have eP (t : ℝ) (ht : 0 < t) : K P t = -(k : ℂ) *
      (g (k*t) * Complex.exp (-v * t) / D t) := by
    have hkt := mul_pos hk ht
    have hneg : ¬ 0 < -(k*t) := by linarith
    simp only [K, heckeArchimedeanDigammaKernel, P, lt_irrefl, ite_false, hkt, ite_true,
      hneg, mul_zero, zero_div, zero_mul, add_zero, zero_sub, D]
    ring
  have eM (t : ℝ) (ht : 0 < t) : conj (K M t) = -(k : ℂ) *
      (g ((-k)*t) * Complex.exp (-(conj v) * t) / D t) := by
    have hkt := mul_pos hk ht
    have hneg : ¬ 0 < -(k*t) := by linarith
    simp only [K, heckeArchimedeanDigammaKernel, M, lt_irrefl, ite_false, hkt, ite_true,
      hneg, mul_zero, zero_div, zero_mul, add_zero, zero_sub, D, neg_mul, map_mul, map_neg,
      map_div₀, map_sub, map_one, Complex.conj_ofReal, Complex.conj_conj, ← Complex.exp_conj]
    ring
  have hP : IntegrableOn (K P) (Ioi (0:ℝ)) :=
    IntegrableOn.congr_fun ((introTraceArchimedean_sample_integrable g hc hd hs hz k hk.ne' v).const_mul (-(k : ℂ)))
      (fun t ht ↦ (eP t ht).symm) measurableSet_Ioi
  have hM : IntegrableOn (fun t ↦ conj (K M t)) (Ioi (0:ℝ)) :=
    IntegrableOn.congr_fun ((introTraceArchimedean_sample_integrable g hc hd hs hz (-k) (neg_ne_zero.mpr hk.ne') (conj v)).const_mul (-(k : ℂ)))
      (fun t ht ↦ (eM t ht).symm) measurableSet_Ioi
  rw [← integral_conj, ← integral_add hP hM]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ?_)
  rw [eP t ht, eM t ht]
  simp only [K, heckeArchimedeanDigammaKernel, hz, mul_zero, zero_div, zero_sub, D, neg_mul]
  ring

open Classical in
/-- Paper: §1.4.1, p. 28, and Theorem B.4.2.2, p. 616. For a compact smooth
logarithmic profile vanishing at norm one, the local trace equals the negative
digamma integral, with contributions from both sides of norm one. -/
theorem introTraceArchimedean_eq_neg_digamma_of_vanishing_at_one (χ : U𝔽) (w : InfinitePlace F)
    (f : ℝ → ℂ) (hzero : f 1 = 0)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun u ↦ f (Real.exp u)))
    (hsupp : HasCompactSupport (fun u ↦ f (Real.exp u)))
    (hi : Integrable (archIntegrand(χ, f, w)) (infiniteLocalMultiplicativeTamagawaMeasure F w)) :
    introTraceArchimedean χ f w = -(if hw : w.IsReal then
      let p := (realHeckeCharacter_parameters χ w hw).exists.choose
      ∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1/2)
        ((1/2 + p.1 + p.2.val)/2) ((1/2 - p.1 + p.2.val)/2) (fun y ↦ f (Real.exp y)) t
    else
      let p := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
      ∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
        (1/2 + p.1 + (p.2.natAbs : ℂ)/2) (1/2 - p.1 + (p.2.natAbs : ℂ)/2)
        (fun y ↦ f (Real.exp y)) t) := by
  classical
  let g (y : ℝ) := f (Real.exp y)
  let P := (Ioi (1 : ℝ)).indicator f
  let M := (Ioi (1 : ℝ)).indicator (fun x : ℝ ↦ conj (f x⁻¹))
  have hg : g 0 = 0 := by simpa [g] using hzero
  have hP : Measurable P := by
    have eq : P = (Ioi 1).indicator (fun x ↦ g (Real.log x)) := by
      funext x
      by_cases hx : 1 < x
      · simp [P, g, Set.indicator, hx, Real.exp_log (zero_lt_one.trans hx)]
      · simp [P, Set.indicator, hx]
    exact eq ▸ (hsmooth.continuous.measurable.comp Real.measurable_log).indicator measurableSet_Ioi
  have hM : Measurable M := by
    have eq : M = (Ioi 1).indicator (fun x ↦ conj (g (-Real.log x))) := by
      funext x
      by_cases hx : 1 < x
      · simp [M, g, Set.indicator, hx, Real.exp_neg, Real.exp_log (zero_lt_one.trans hx)]
      · simp [M, Set.indicator, hx]
    exact eq ▸ (Complex.continuous_conj.measurable.comp (hsmooth.continuous.measurable.comp
      Real.measurable_log.neg)).indicator measurableSet_Ioi
  have hp := introTraceArchimedean_eq_neg_digamma_of_supported_above_one χ w P hP
    (fun x hx ↦ Set.indicator_of_notMem (not_lt.mpr hx) _) (introTraceArchimedean_above_integrable χ w f hi)
  have hm := introTraceArchimedean_eq_neg_digamma_of_supported_above_one χ w M hM
    (fun x hx ↦ Set.indicator_of_notMem (not_lt.mpr hx) _)
    (introTraceArchimedean_above_integrable χ w _ (introTraceArchimedean_inv_integrable χ w f hi))
  have h := introTraceArchimedean_two_halves χ w f hzero hi
  change introTraceArchimedean χ f w = introTraceArchimedean χ P w + conj (introTraceArchimedean χ M w) at h
  rw [h, hp, hm, map_neg, ← neg_add]
  congr 1
  have hsplit (k : ℝ) (hk : 0 < k) (v q : ℂ) (hq : conj v = q) :
      (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k v q (fun y ↦ P (Real.exp y)) t) +
      conj (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k v q (fun y ↦ M (Real.exp y)) t) =
      ∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k v q g t := by
    subst q
    have hh := introTraceArchimedean_kernel_two_halves g hsmooth.continuous
      (hsmooth.differentiable (by simp) 0) hsupp hg k hk v
    simpa [P, M, Set.indicator, g, Real.one_lt_exp_iff, Real.exp_neg] using hh.symm
  split_ifs with hw
  · let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    have hr : p.1.re = 0 := (realHeckeCharacter_parameters χ w hw).exists.choose_spec.1
    have hpr : conj p.1 = -p.1 := by apply Complex.ext <;> simp [hr]
    apply hsplit _ (by norm_num)
    change conj ((1/2 + p.1 + p.2.val)/2) = (1/2 - p.1 + p.2.val)/2
    simp only [map_div₀, map_add, map_one, map_ofNat, map_natCast, hpr]
    ring
  · let p := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    have hr : p.1.re = 0 := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose_spec.1
    have hpr : conj p.1 = -p.1 := by apply Complex.ext <;> simp [hr]
    apply hsplit _ (by norm_num)
    change conj (1/2 + p.1 + (p.2.natAbs : ℂ)/2) = 1/2 - p.1 + (p.2.natAbs : ℂ)/2
    simp only [map_div₀, map_add, map_one, map_ofNat, map_natCast, hpr]
    ring

end

/-- The radial tail in the complex plane is integrable for exponents below minus two. -/
private theorem introTraceApprox_archimedean_sub_shiftTwo_complexTail {d : ℝ} (hd : d < -2) :
    Integrable (fun u : ℂ ↦ (Ioi (2 : ℝ)).indicator (fun r ↦ r ^ d) ‖u‖) := by
  rw [integrable_fun_norm_addHaar (μ := volume) (f := (Ioi (2 : ℝ)).indicator fun r ↦ r ^ d),
    Complex.finrank_real_complex]
  have hbase : Integrable ((Ioi (2 : ℝ)).indicator fun r ↦ r ^ (d + 1)) :=
    (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num))
  refine hbase.integrableOn.congr_fun (fun y (hy : y ∈ Ioi (0 : ℝ)) ↦ ?_) measurableSet_Ioi
  by_cases h : y ∈ Ioi (2 : ℝ)
  · simp [h, smul_eq_mul, Real.rpow_add hy, mul_comm]
  · simp [h]

/-- The inverse distance to one is locally integrable in the complex plane. -/
private theorem introTraceApprox_archimedean_sub_shiftTwo_complexNear :
    Integrable (fun u : ℂ ↦ (Metric.ball (0 : ℂ) 4).indicator (fun z ↦ ‖z‖⁻¹) (u - 1)) := by
  have hi : IntegrableOn (fun u : ℂ ↦ ‖u‖⁻¹) (Metric.ball 0 4) := by
    rw [integrableOn_fun_norm_addHaar (μ := volume) (f := fun y : ℝ ↦ y⁻¹), Complex.finrank_real_complex]
    refine (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun (fun y (hy : y ∈ Ioo 0 4) ↦ ?_)
      measurableSet_Ioo
    simp [smul_eq_mul, hy.1.ne']
  have h := (integrable_indicator_iff measurableSet_ball).2 hi
  simpa only [sub_eq_add_neg] using h.comp_add_right (-1 : ℂ)

/-- For the corrected squared complex denominator, one power of the distance to one
cancels on the inner annulus. Outside radius two the radial density decays as
`‖u‖ ^ (-2*a-3)`. -/
private theorem introTraceApprox_archimedean_sub_shiftTwo_complexBound {a C : ℝ} (hC : 0 ≤ C) (u : ℂ) (hu : 1 < ‖u‖)
    (q : ℂ) (hq : ‖q‖ ≤ (C * (‖u‖ ^ 2) ^ (-a)) * (8 * (‖u‖ ^ 2 - 1) / ‖u‖ ^ 2)) :
    ‖(((‖u‖^2)⁻¹ : ℝ) : ℂ) * (q * (‖u‖ : ℂ) / ((‖1 - u‖ ^ 2 : ℝ) : ℂ))‖ ≤
      (24 * C * (1 + 4 ^ (-a))) * ((Metric.ball (0 : ℂ) 4).indicator (fun z ↦ ‖z‖⁻¹) (u - 1)) +
      (32 * C) * ((Ioi (2 : ℝ)).indicator (fun r ↦ r ^ (-2 * a - 3)) ‖u‖) := by
  let r := ‖u‖
  let b := ‖1 - u‖
  have hr : 1 < r := hu
  have hr₀ : 0 < r := by linarith
  have hbr : r - 1 ≤ b := by simpa [r, b, norm_sub_rev u 1] using norm_sub_norm_le u (1 : ℂ)
  have hb : 0 < b := by linarith
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr.le
  have hq' : ‖q‖ ≤ C * (r ^ 2) ^ (-a) * (8 * (r ^ 2 - 1) / r ^ 2) := hq
  rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (sq_nonneg _)]
  change (r ^ 2)⁻¹ * (‖q‖ * r / b ^ 2) ≤ _
  rw [show (r ^ 2)⁻¹ * (‖q‖ * r / b ^ 2) = ‖q‖ / r / b ^ 2 by field_simp]
  by_cases hr₁ : r ≤ 2
  · have hb4 : ‖u - 1‖ < 4 := by
      have h := norm_sub_le u (1 : ℂ)
      rw [norm_one] at h
      change r ≤ 2 at hr₁
      linarith
    rw [indicator_of_mem (mem_ball_zero_iff.mpr hb4),
      indicator_of_notMem (show ‖u‖ ∉ Ioi (2 : ℝ) from not_lt.mpr hr₁), mul_zero, add_zero, norm_sub_rev u 1]
    have hpow : (r ^ 2) ^ (-a) ≤ 1 + 4 ^ (-a) := by
      rcases le_or_gt (-a) 0 with h | h
      · exact (Real.rpow_le_one_of_one_le_of_nonpos hr2 h).trans (le_add_of_nonneg_right (by positivity))
      · exact (Real.rpow_le_rpow (sq_nonneg r) (by nlinarith : r ^ 2 ≤ 4) h.le).trans (by linarith)
    have hfac : 8 * (r ^ 2 - 1) / r ^ 2 ≤ 24 * b := by
      refine (div_le_self (by nlinarith) hr2).trans ?_
      have h := mul_le_mul (show r - 1 ≤ b from hbr) (show r + 1 ≤ 3 by linarith)
        (by linarith : 0 ≤ r + 1) hb.le
      nlinarith
    have hqle : ‖q‖ ≤ C * (1 + 4 ^ (-a)) * (24 * b) := hq'.trans (by gcongr)
    calc ‖q‖ / r / b ^ 2 ≤ (C * (1 + 4 ^ (-a)) * (24 * b)) / b ^ 2 :=
           div_le_div_of_nonneg_right ((div_le_self (norm_nonneg _) hr.le).trans hqle) (sq_nonneg _)
         _ = _ := by change _ = _ * b⁻¹; field_simp
  · have hr₁' : 2 < r := lt_of_not_ge hr₁
    rw [indicator_of_mem (show ‖u‖ ∈ Ioi (2 : ℝ) from hr₁')]
    have hnn : 0 ≤ (Metric.ball (0 : ℂ) 4).indicator (fun z ↦ ‖z‖⁻¹) (u - 1) :=
      indicator_nonneg (fun _ _ ↦ by positivity) _
    apply le_add_of_nonneg_of_le (mul_nonneg (by positivity) hnn)
    have hfac : 8 * (r ^ 2 - 1) / r ^ 2 ≤ 8 := (div_le_iff₀ (sq_pos_of_pos hr₀)).2 (by nlinarith)
    have hqle : ‖q‖ ≤ C * (r ^ 2) ^ (-a) * 8 := hq'.trans (by gcongr)
    have hden : 0 < r / 2 := by positivity
    calc ‖q‖ / r / b ^ 2 ≤ (C * (r ^ 2) ^ (-a) * 8) / r / (r / 2) ^ 2 := by
           gcongr
           linarith
         _ = (32 * C) * r ^ (-2 * a - 3) := by
           rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr₀.le,
             show -2 * a - 3 = (2 : ℝ) * (-a) - (3:ℕ) by push_cast; ring,
             Real.rpow_sub hr₀, Real.rpow_natCast]
           push_cast
           field_simp
           ring

/-- A common integrable bound for the matched smoothed kernels also bounds their
pointwise limits. Dominated convergence applies while the complex parameter varies. -/
private theorem introTraceApprox_archimedean_sub_shiftTwo_weighted {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (r : Ω → ℝ) (hr : Measurable r) (K : Ω → ℂ) (hK : Measurable K)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (hdom : ∀ a : ℝ, -(1 / 2 : ℝ) < a → ∃ B : Ω → ℝ, Integrable B μ ∧
      ∀ n (w : ℂ), a ≤ w.re → ∀ t, ‖K t * (introTraceApprox (h n) (ρ n) w (r t) -
        introTraceApprox (h n) (ρ n) (w + 2) (r t))‖ ≤ B t) :
    let X (n : ℕ) (w : ℂ) (t : Ω) := K t * (introTraceApprox (h n) (ρ n) w (r t) -
        introTraceApprox (h n) (ρ n) (w + 2) (r t))
    let Y (w : ℂ) (t : Ω) := K t * (introTracePower w (r t) - introTracePower (w + 2) (r t))
    (∀ w ∈ right(-(1 / 2 : ℝ)), Integrable (Y w) μ) ∧
    TendstoLocallyUniformlyOn (fun n w ↦ ∫ t, X n w t ∂μ) (fun w ↦ ∫ t, Y w t ∂μ)
      atTop right(-(1 / 2 : ℝ)) := by
  intro X Y
  let f (n : ℕ) (w : ℂ) := introTraceApprox (h n) (ρ n) w
  have hm (n : ℕ) (w : ℂ) := (introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n w).1
  have hXm (n : ℕ) (w : ℂ) : Measurable (X n w) :=
    hK.mul (((hm _ _).measurable.comp hr).sub ((hm _ _).measurable.comp hr))
  have hYm (w : ℂ) : Measurable (Y w) := hK.mul (((introTraceApprox_mellin_tendsto_power_measurable _).comp hr).sub
    ((introTraceApprox_mellin_tendsto_power_measurable _).comp hr))
  have hzero (n : ℕ) (w : ℂ) (t : ℝ) (ht : t ≤ 1) : f n w t = 0 :=
    image_eq_zero_of_notMem_tsupport fun hm ↦ ht.not_gt (introTraceApprox_support h ρ hA n w hm)
  have hXlim (z : ℂ) (t : Ω) :
      Tendsto (fun i : ℕ × ℂ ↦ X i.1 i.2 t) (atTop ×ˢ 𝓝 z) (𝓝 (Y z t)) := by
    by_cases ht : 1 < r t
    · have hplus : Tendsto (fun i : ℕ × ℂ ↦ (i.1, i.2 + 2)) (atTop ×ˢ 𝓝 z) (atTop ×ˢ 𝓝 (z + 2)) :=
        tendsto_fst.prodMk (tendsto_snd.add_const _)
      exact tendsto_const_nhds.mul ((introTraceApprox_mellin_tendsto_radial hA z ht).sub
        ((introTraceApprox_mellin_tendsto_radial hA (z + 2) ht).comp hplus))
    · change Tendsto (fun i : ℕ × ℂ ↦ K t * (f i.1 i.2 (r t) - f i.1 (i.2 + 2) (r t))) _ _
      simp [Y, hzero _ _ _ (le_of_not_gt ht), introTracePower, ht]
  have hYcont (t : Ω) : Continuous (fun z ↦ Y z t) := by
    have h := (introTracePower_differentiable (r t)).continuous
    exact continuous_const.mul (h.sub (h.comp (continuous_id.add_const 2)))
  have hYb {B : Ω → ℝ} {w : ℂ} (hb : ∀ n t, ‖X n w t‖ ≤ B t) (t : Ω) : ‖Y w t‖ ≤ B t := by
    have hseq : Tendsto (fun n : ℕ ↦ (n, w)) atTop (atTop ×ˢ 𝓝 w) := tendsto_id.prodMk tendsto_const_nhds
    exact le_of_tendsto ((hXlim w t).comp hseq).norm (.of_forall fun n ↦ hb n t)
  constructor
  · intro z hz
    obtain ⟨B, hB, hD⟩ := hdom z.re hz
    exact hB.mono' (hYm z).aestronglyMeasurable (.of_forall (hYb (fun n ↦ hD n z le_rfl)))
  apply (isOpen_Ioi.preimage Complex.continuous_re).tendstoLocallyUniformlyOn_iff_forall_tendsto.2
  intro z hz
  obtain ⟨a, ha, haz⟩ := exists_between (show -(1 / 2 : ℝ) < z.re from hz)
  obtain ⟨B, hB, hD⟩ := hdom a ha
  let l := (atTop : Filter ℕ) ×ˢ 𝓝 z
  have hnear : ∀ᶠ i in l, a ≤ i.2.re :=
    (Complex.continuous_re.continuousAt.tendsto.comp tendsto_snd).eventually (le_mem_nhds haz)
  have h₁ : Tendsto (fun i : ℕ × ℂ ↦ ∫ t, X i.1 i.2 t ∂μ) l (𝓝 (∫ t, Y z t ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence B (.of_forall fun _ ↦ (hXm _ _).aestronglyMeasurable)
      (hnear.mono fun i hi ↦ .of_forall (hD _ _ hi)) hB (.of_forall (hXlim z))
  have h₂ : Tendsto (fun i : ℕ × ℂ ↦ ∫ t, Y i.2 t ∂μ) l (𝓝 (∫ t, Y z t ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence B (.of_forall fun _ ↦ (hYm _).aestronglyMeasurable)
      (hnear.mono fun i hi ↦ .of_forall (hYb (fun n ↦ hD n _ hi))) hB
      (.of_forall fun t ↦ (hYcont t).continuousAt.tendsto.comp tendsto_snd)
  exact (h₂.prodMk_nhds h₁).mono_right (nhds_le_uniformity _)

/-- Each fixed cutoff is supported away from norm one, so its individual complex
place density is continuous and compactly supported. -/
private theorem introTraceApprox_archimedean_sub_shiftTwo_complexFixed (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi 1) :
    Integrable (fun t : ℂ ↦ (((‖t‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (f (‖t‖ ^ 2) * (‖t‖ : ℂ) / ((‖1 - t‖ ^ 2 : ℝ) : ℂ))) := by
  let W (t : ℂ) := (((‖t‖ ^ 2)⁻¹ : ℝ) : ℂ) * (f (‖t‖ ^ 2) * (‖t‖ : ℂ) / ((‖1 - t‖ ^ 2 : ℝ) : ℂ))
  have hW : Continuous W := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : ‖x‖ ^ 2 ≤ 1
    · have he := notMem_tsupport_iff_eventuallyEq.mp (fun ht ↦ (hs ht).not_ge hx)
      apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(continuous_norm.pow 2).continuousAt.tendsto.eventually he] with t ht
      simp [W, show f (‖t‖ ^ 2) = 0 from ht]
    · have hpos : 0 < ‖x‖ := by contrapose! hx; simp [le_antisymm hx (norm_nonneg _)]
      have hne : 1 - x ≠ 0 := fun h ↦ hx (by rw [← sub_eq_zero.mp h]; norm_num)
      have hden : ((‖1 - x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr hne))
      dsimp only [W]
      fun_prop (disch := first | exact hden | positivity)
  obtain ⟨R, hR⟩ := hc.bddAbove
  refine hW.integrable_of_hasCompactSupport (exists_compact_iff_hasCompactSupport.mp
    ⟨Metric.closedBall (0 : ℂ) (R + 1), isCompact_closedBall _ _, fun t ht ↦ ?_⟩)
  have hz : f (‖t‖ ^ 2) = 0 := by
    by_contra hn
    have h₁ := hR (subset_tsupport _ hn)
    apply ht
    rw [mem_closedBall_zero_iff]
    nlinarith [sq_nonneg (‖t‖-1 / 2)]
  simp [W, hz]

/-- A coordinate formula that also transfers integrability gives the result for the
actual two local archimedean terms, separately integrated at each cutoff. -/
private theorem introTraceApprox_archimedean_sub_shiftTwo_chart {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (r : Ω → ℝ) (hr : Measurable r) (K : Ω → ℂ) (hK : Measurable K) (c : ℂ)
    (χ : U𝔽) (v : InfinitePlace F) (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (hcoord : ∀ f : ℝ → ℂ, Measurable f →
      (Integrable archIntegrand(χ, f, v) (infiniteLocalMultiplicativeTamagawaMeasure F v) ↔
        Integrable (fun t ↦ K t * f (r t)) μ) ∧
      introTraceArchimedean χ f v = c * ∫ t, K t * f (r t) ∂μ)
    (hfixed : ∀ n z, Integrable (fun t ↦ K t * introTraceApprox (h n) (ρ n) z (r t)) μ)
    (hdom : ∀ a : ℝ, -(1 / 2 : ℝ) < a → ∃ B : Ω → ℝ, Integrable B μ ∧
      ∀ n (w : ℂ), a ≤ w.re → ∀ t, ‖K t * (introTraceApprox (h n) (ρ n) w (r t) -
        introTraceApprox (h n) (ρ n) (w + 2) (r t))‖ ≤ B t) :
    (∀ z ∈ right(-(1 / 2 : ℝ)), Integrable
      archIntegrand(χ, (fun t ↦ introTracePower z t - introTracePower (z + 2) t), v)
      (infiniteLocalMultiplicativeTamagawaMeasure F v)) ∧
    TendstoLocallyUniformlyOn (fun n z ↦
      introTraceArchimedean χ (introTraceApprox (h n) (ρ n) z) v -
      introTraceArchimedean χ (introTraceApprox (h n) (ρ n) (z + 2)) v)
      (fun z ↦ introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z + 2) t) v)
      atTop right(-(1 / 2 : ℝ)) := by
  obtain ⟨hi, hlim⟩ := introTraceApprox_archimedean_sub_shiftTwo_weighted μ r hr K hK h ρ hA hdom
  have hm (z : ℂ) := (introTraceApprox_mellin_tendsto_power_measurable z).sub
    (introTraceApprox_mellin_tendsto_power_measurable (z + 2))
  have hfm (n : ℕ) (z : ℂ) := (introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n z).1.measurable
  refine ⟨fun z hz ↦ (hcoord _ (hm z)).1.mpr (hi z hz), ?_⟩
  refine ((uniformContinuous_const_smul (M := ℂ) c).comp_tendstoLocallyUniformlyOn hlim).congr
      (fun n z _ ↦ ?_) |>.congr_right (fun z _ ↦ (hcoord _ (hm z)).2.symm)
  rw [(hcoord _ (hfm n z)).2, (hcoord _ (hfm n (z + 2))).2, ← mul_sub,
      ← integral_sub (hfixed n z) (hfixed n (z + 2))]
  change c * (∫ t, K t * (_ - _) ∂μ) = c * ∫ t, K t * _ - K t * _ ∂μ
  congr 1
  apply integral_congr_ae
  exact .of_forall fun _ ↦ mul_sub _ _ _

/-- The real and complex coordinate bounds apply to each actual matched family, with
an integrable limiting density on the original group of local units. -/
private theorem introTraceApprox_archimedean_sub_shiftTwo_matched (χ : U𝔽) (v : InfinitePlace F)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (hmatch : ∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1) :
    (∀ z ∈ right(-(1 / 2 : ℝ)), Integrable
      archIntegrand(χ, (fun t ↦ introTracePower z t - introTracePower (z + 2) t), v)
      (infiniteLocalMultiplicativeTamagawaMeasure F v)) ∧
    TendstoLocallyUniformlyOn (fun n z ↦
      introTraceArchimedean χ (introTraceApprox (h n) (ρ n) z) v -
      introTraceArchimedean χ (introTraceApprox (h n) (ρ n) (z + 2)) v)
      (fun z ↦ introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z + 2) t) v)
      atTop right(-(1 / 2 : ℝ)) := by
  let f (n : ℕ) (z : ℂ) := introTraceApprox (h n) (ρ n) z
  have hf (n : ℕ) (z : ℂ) := introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n z
  have hzero (n : ℕ) (z : ℂ) (t : ℝ) (ht : t ≤ 1) : f n z t = 0 :=
    image_eq_zero_of_notMem_tsupport fun hm ↦ ht.not_gt (introTraceApprox_support h ρ hA n z hm)
  by_cases hv : v.IsReal
  · obtain ⟨m, hm, hnm, _, he⟩ := introTraceApprox_archimedean_sub_shiftTwo_realCoordinate χ v hv
    let K (t : ℝ) := m t * (((|t|⁻¹ : ℝ) : ℂ) * ((Real.sqrt |t| : ℂ) / ((|1 - t| : ℝ) : ℂ)))
    have hK : Measurable K := by dsimp [K]; fun_prop
    have hW (t : ℝ) (q : ℂ) : m t * (((|t|⁻¹ : ℝ) : ℂ) * (q * (Real.sqrt |t| : ℂ) /
        ((|1 - t| : ℝ) : ℂ))) = K t * q := by dsimp [K]; ring
    simp_rw [hW] at he
    apply introTraceApprox_archimedean_sub_shiftTwo_chart volume (fun t : ℝ ↦ |t|) continuous_abs.measurable K hK (1 / 2) χ v h ρ hA he
    · intro n z
      have hb := introTraceApprox_rat_sub_shiftTwo_integrable _ (hf n z).1 (hf n z).2 (introTraceApprox_support h ρ hA n z)
      apply hb.mono (hK.mul ((hf n z).1.measurable.comp continuous_abs.measurable)).aestronglyMeasurable
      exact .of_forall fun t ↦ by simp only [Pi.mul_apply, Function.comp_apply]; rw [← hW, norm_mul, hnm, one_mul]
    · intro a ha
      let C := (1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)
      let d := -a - 3 / 2
      let p := (Ioi (1 : ℝ)).indicator fun t ↦ t ^ d
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hp : Integrable p := (integrable_indicator_iff measurableSet_Ioi).2
        (integrableOn_Ioi_rpow_of_lt (show d < -1 by dsimp [d]; linarith) zero_lt_one)
      refine ⟨fun t ↦ (8 * C) * (p t + p (-t)), (hp.add hp.comp_neg).const_mul _, ?_⟩
      intro n w hw t
      rw [← hW, norm_mul, hnm, one_mul]
      by_cases ht : 1 < |t|
      · have hb := introTraceApprox_rat_sub_shiftTwo_density_bound t a C hC ht _ <|
          introTraceApprox_rat_sub_shiftTwo_bound h ρ hA hmatch n ht hw
        have hp' : p t + p (-t) = |t| ^ d := by
          rcases le_or_gt 0 t with hts | hts
          · rw [abs_of_nonneg hts] at ht ⊢
            simp [p, ht, show ¬1 < -t by linarith]
          · rw [abs_of_neg hts] at ht ⊢
            simp [p, ht, show ¬1 < t by linarith]
        simpa only [hp'] using hb
      · have hp' (x : ℝ) : 0 ≤ p x := indicator_nonneg (fun y hy ↦
          Real.rpow_nonneg (zero_le_one.trans (mem_Ioi.mp hy).le) d) x
        change ‖_ * (((f n w |t| - f n (w + 2) |t|) * _) / _)‖ ≤ _
        simpa [hzero _ _ _ (le_of_not_gt ht)] using mul_nonneg (show 0 ≤ 8 * C by positivity)
          (add_nonneg (hp' t) (hp' (-t)))
  · obtain ⟨m, hm, hnm, he⟩ := introTraceApprox_archimedean_sub_shiftTwo_complexCoordinate χ v (InfinitePlace.not_isReal_iff_isComplex.mp hv)
    let K (t : ℂ) := m t * ((((‖t‖^2)⁻¹ : ℝ) : ℂ) * ((‖t‖ : ℂ) / ((‖1 - t‖^2 : ℝ) : ℂ)))
    have hK : Measurable K := by dsimp [K]; fun_prop
    have hW (t q : ℂ) : m t * ((((‖t‖^2)⁻¹ : ℝ) : ℂ) * (q * (‖t‖ : ℂ) /
        ((‖1 - t‖^2 : ℝ) : ℂ))) = K t * q := by dsimp [K]; ring
    simp_rw [hW] at he
    apply introTraceApprox_archimedean_sub_shiftTwo_chart (2 • volume) (fun t : ℂ ↦ ‖t‖^2) (by fun_prop) K hK
      (1 / (2 * (Real.pi:ℂ))) χ v h ρ hA he
    · intro n z
      have hb := introTraceApprox_archimedean_sub_shiftTwo_complexFixed _ (hf n z).1 (hf n z).2 (introTraceApprox_support h ρ hA n z)
      rw [two_smul]
      apply Integrable.add_measure <;> apply hb.mono (hK.mul ((hf n z).1.measurable.comp (by fun_prop))).aestronglyMeasurable <;>
        exact .of_forall fun t ↦ by simp only [Pi.mul_apply, Function.comp_apply]; rw [← hW, norm_mul, hnm, one_mul]
    · intro a ha
      let C := (1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)
      have hC : 0 ≤ C := by dsimp [C]; positivity
      let near (t : ℂ) := (Metric.ball (0 : ℂ) 4).indicator (fun z ↦ ‖z‖⁻¹) (t - 1)
      let far (t : ℂ) := (Ioi (2 : ℝ)).indicator (fun r ↦ r ^ (-2 * a - 3)) ‖t‖
      let B (t : ℂ) := (24 * C * (1 + 4 ^ (-a))) * near t + (32 * C) * far t
      have hB : Integrable B := (introTraceApprox_archimedean_sub_shiftTwo_complexNear.const_mul _).add
        ((introTraceApprox_archimedean_sub_shiftTwo_complexTail (d := -2 * a - 3) (by linarith)).const_mul _)
      refine ⟨B, by simpa only [two_smul] using hB.add_measure hB, ?_⟩
      intro n w hw t
      rw [← hW, norm_mul, hnm, one_mul]
      by_cases ht : 1 < ‖t‖^2
      · exact introTraceApprox_archimedean_sub_shiftTwo_complexBound hC t (by contrapose! ht; exact pow_le_one₀ (norm_nonneg _) ht) _
          (introTraceApprox_rat_sub_shiftTwo_bound h ρ hA hmatch n ht hw)
      · have hnear : 0 ≤ near t := indicator_nonneg (fun _ _ ↦ by positivity) _
        have hfar : 0 ≤ far t := indicator_nonneg (fun r hr ↦ Real.rpow_nonneg (by linarith [mem_Ioi.mp hr]) _) _
        change ‖_ * (((f n w _ - f n (w + 2) _) * _) / _)‖ ≤ _
        simpa [hzero _ _ _ (le_of_not_gt ht), B] using
          add_nonneg (mul_nonneg (by positivity) hnear) (mul_nonneg (by positivity) hfar)

/-- A single matched family realizes the full finite archimedean sum. -/
private theorem introTraceApprox_archimedean_sub_shiftTwo_matched_sum (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ)
    (hmatch : ∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1) :
      TendstoLocallyUniformlyOn (fun n z ↦
        (∑ v : InfinitePlace F, introTraceArchimedean χ (introTraceApprox (h n) (ρ n) z) v) -
         ∑ v : InfinitePlace F, introTraceArchimedean χ (introTraceApprox (h n) (ρ n) (z + 2)) v)
        (fun z ↦ ∑ v : InfinitePlace F, introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z + 2) t) v)
        atTop right(-(1 / 2 : ℝ)) := by
  classical
  have hlocal (v : InfinitePlace F) := introTraceApprox_archimedean_sub_shiftTwo_matched χ v h ρ hA hmatch
  suffices ∀ S : Finset (InfinitePlace F), TendstoLocallyUniformlyOn (fun n z ↦
      (∑ v ∈ S, introTraceArchimedean χ (introTraceApprox (h n) (ρ n) z) v) -
       ∑ v ∈ S, introTraceArchimedean χ (introTraceApprox (h n) (ρ n) (z + 2)) v)
      (fun z ↦ ∑ v ∈ S, introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z + 2) t) v)
      atTop right(-(1 / 2 : ℝ)) from this Finset.univ
  intro S
  induction S using Finset.induction_on with
  | empty =>
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0)
      ).tendstoUniformlyOn_const (s := right(-(1 / 2 : ℝ)))).tendstoLocallyUniformlyOn
  | insert v S hv ih =>
    refine (((hlocal v).2.add ih).congr (fun n z _ ↦ ?_)).congr_right (fun z _ ↦ ?_)
    · simp only [Finset.sum_insert hv, Pi.add_apply]
      ring
    · simp only [Finset.sum_insert hv, Pi.add_apply]

/-- Paper: §1.4.3, p. 29. For any admissible initial family, a cofinal reindexing of
the mollifiers makes the reference-subtracted local terms and their full archimedean
sum converge locally uniformly on `Re z > -1/2`, for every unitary character. The
limiting test is the difference of the powers at `z` and `z+2`, and its local
Tamagawa integrands are integrable at every infinite place.
Deviation: Match the additive mollifier widths to the lower cutoff before removing
the cutoffs. The complex-place estimate uses the corrected squared denominator. -/
theorem introTraceApprox_archimedean_sub_shiftTwo_tendsto (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ IsIntroTraceApproximation h (ρ ∘ k) ∧
      ∀ χ : U𝔽,
      (∀ v : InfinitePlace F, ∀ z ∈ right(-(1 / 2 : ℝ)), Integrable
        archIntegrand(χ, (fun t ↦ introTracePower z t - introTracePower (z + 2) t), v)
        (infiniteLocalMultiplicativeTamagawaMeasure F v)) ∧
      (∀ v : InfinitePlace F, TendstoLocallyUniformlyOn (fun n z ↦
        introTraceArchimedean χ (introTraceApprox (h n) (ρ (k n)) z) v -
        introTraceArchimedean χ (introTraceApprox (h n) (ρ (k n)) (z + 2)) v)
        (fun z ↦ introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z + 2) t) v)
        atTop right(-(1 / 2 : ℝ))) ∧
      TendstoLocallyUniformlyOn (fun n z ↦
        (∑ v : InfinitePlace F, introTraceArchimedean χ (introTraceApprox (h n) (ρ (k n)) z) v) -
         ∑ v : InfinitePlace F, introTraceArchimedean χ (introTraceApprox (h n) (ρ (k n)) (z + 2)) v)
        (fun z ↦ ∑ v : InfinitePlace F, introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z + 2) t) v)
        atTop right(-(1 / 2 : ℝ)) := by
  classical
  obtain ⟨k, hk, hAk, hmatch⟩ := introTraceApprox_rat_sub_shiftTwo_match h ρ hA
  refine ⟨k, hk, hAk, ?_⟩
  intro χ
  have hlocal (v : InfinitePlace F) := introTraceApprox_archimedean_sub_shiftTwo_matched χ v h (ρ ∘ k) hAk hmatch
  exact ⟨fun v ↦ (hlocal v).1, fun v ↦ (hlocal v).2, introTraceApprox_archimedean_sub_shiftTwo_matched_sum χ h (ρ ∘ k) hAk hmatch⟩

/-- For matched supports, the smoothed rational archimedean differences converge
locally uniformly. Domination is applied on both real sign branches at once. -/
private theorem introTraceApprox_rat_sub_shiftTwo_matched (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ)
    (hmatch : ∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1) :
    TendstoLocallyUniformlyOn (fun n z ↦
      introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) z) Rat.infinitePlace -
      introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) (z + 2)) Rat.infinitePlace)
      (fun z ↦ 1 / (z + 1 / 2)) atTop right(-(1 / 2 : ℝ)) := by
  exact ((introTraceApprox_archimedean_sub_shiftTwo_matched (F := ℚ) 1 Rat.infinitePlace h ρ hA hmatch).2).congr_right
    (fun z hz ↦ introTraceArchimedean_rat_sub_shiftTwo z hz)

/-- Paper: §1.4.3, p. 29. For any admissible cutoff and mollifier family one can
retain all cutoffs and select cofinal mollifier indices so that the difference
of the two actual rational real-place terms at `z` and `z+2` converges locally
uniformly to `1/(z+1/2)` on `Re z > -1/2`.
Deviation: Match each mollifier width to the distance of the cutoff support from
one before passing to the limit. -/
theorem introTraceApprox_rat_sub_shiftTwo_tendsto (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ IsIntroTraceApproximation h (ρ ∘ k) ∧
      TendstoLocallyUniformlyOn (fun n z ↦
        introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ (k n)) z) Rat.infinitePlace -
        introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ (k n)) (z + 2)) Rat.infinitePlace)
        (fun z ↦ 1 / (z + 1 / 2)) atTop right(-(1 / 2 : ℝ)) := by
  obtain ⟨k, hcof, hAk, hmatch⟩ := introTraceApprox_rat_sub_shiftTwo_match h ρ hA
  exact ⟨k, hcof, hAk, introTraceApprox_rat_sub_shiftTwo_matched h (ρ ∘ k) hAk hmatch⟩

/-- Paper: §1.4.3, p. 29. A common subsequence of the two archimedean sums
has holomorphic limits on the interior of the compact set if the stated
uniform bounds hold.
Deviation: The bounds are hypotheses of the Montel implication. The real-place
bound fails for the rational trivial character. -/
theorem introTrace_montel_of_bounded (K : Set ℂ) (_hK : IsCompact K)
    (A B : ℕ → ℂ → ℂ) (_hA : ∀ n, DifferentiableOn ℂ (A n) (interior K))
    (_hB : ∀ n, DifferentiableOn ℂ (B n) (interior K))
    (_hbound : ∃ C : ℝ, 0 < C ∧ ∀ n z, z ∈ K → ‖A n z‖ ≤ C ∧ ‖B n z‖ ≤ C) :
    ∃ (k : ℕ → ℕ) (L₁ L₂ : ℂ → ℂ), StrictMono k ∧
      TendstoLocallyUniformlyOn (A ∘ k) L₁ atTop (interior K) ∧
      TendstoLocallyUniformlyOn (B ∘ k) L₂ atTop (interior K) ∧
      AnalyticOnNhd ℂ L₁ (interior K) ∧ AnalyticOnNhd ℂ L₂ (interior K) := by
  rcases _hbound with ⟨C, _, hC⟩
  have hdiff : ∀ n, DifferentiableOn ℂ (fun z ↦ (A n z, B n z)) (interior K) :=
    fun n ↦ (_hA n).prodMk (_hB n)
  have hbounded : External.TauCeti.IsLocallyBoundedOn
      (fun n z ↦ (A n z, B n z)) (interior K) :=
    External.TauCeti.isLocallyBoundedOn_of_forall_norm_le fun n z hz ↦
      norm_prod_le_iff.mpr (hC n z (interior_subset hz))
  obtain ⟨k, L, hk, hL, hconv⟩ := External.TauCeti.montel isOpen_interior hdiff hbounded
  exact ⟨k, Prod.fst ∘ L, Prod.snd ∘ L, hk,
    uniformContinuous_fst.comp_tendstoLocallyUniformlyOn hconv,
    uniformContinuous_snd.comp_tendstoLocallyUniformlyOn hconv,
    hL.fst.analyticOnNhd isOpen_interior, hL.snd.analyticOnNhd isOpen_interior⟩

-- TODO(paper-gap): Pointwise convergence of the individual Mellin terms
-- leaves the infinite zero sum uncontrolled. At the trivial rational character and
-- a window containing the full divisor the zero sum itself diverges at z = 2.

/-- Twisting a unitary character by `|·|^{iy}` shifts its norm twists by `iy`. -/
private theorem introTraceApprox_spectral_summable_twist (χ χ' : U𝔽) (y : ℝ)
    (hχ' : ∀ g, (χ' g : ℂ) = χ g * (N(g) : ℂ) ^ ((y : ℂ) * Complex.I)) (w : ℂ) (g : C𝔽) :
    ideleClassNormTwist χ' w g = ideleClassNormTwist χ (w + y * Complex.I) g := by
  have hN : (N(g) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  change (χ' g : ℂ) * (N(g) : ℂ) ^ w = (χ g : ℂ) * (N(g) : ℂ) ^ (w + y * Complex.I)
  rw [hχ', Complex.cpow_add _ _ hN]
  ring

/-- The gamma factor of a twist by `|·|^{iy}` is the shifted gamma factor. -/
private theorem introTraceApprox_spectral_summable_gamma (χ χ' : U𝔽) (y : ℝ)
    (hχ' : ∀ g, (χ' g : ℂ) = χ g * (N(g) : ℂ) ^ ((y : ℂ) * Complex.I)) (w : ℂ) :
    heckeGammaFactor χ' w = heckeGammaFactor χ (w + y * Complex.I) := by
  classical
  have htw := introTraceApprox_spectral_summable_twist χ χ' y hχ'
  have hsplit (g : C𝔽) : ideleClassNormTwist χ' 0 g =
      ideleClassNormTwist χ 0 g * (N(g) : ℂ) ^ ((y : ℂ) * Complex.I) := by
    rw [htw, zero_add]
    change (χ g : ℂ) * (N(g) : ℂ) ^ ((y : ℂ) * Complex.I) =
      ((χ g : ℂ) * (N(g) : ℂ) ^ (0 : ℂ)) * (N(g) : ℂ) ^ ((y : ℂ) * Complex.I)
    rw [Complex.cpow_zero, mul_one]
  unfold heckeGammaFactor
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  by_cases hv : v.IsReal
  · simp only [dif_pos hv]
    let a := (realHeckeCharacter_parameters χ v hv).exists.choose
    have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec
    have hr : (realHeckeCharacter_parameters χ' v hv).exists.choose = (a.1 + y * Complex.I, a.2) := by
      refine (realHeckeCharacter_parameters χ' v hv).unique
        (realHeckeCharacter_parameters χ' v hv).exists.choose_spec ⟨by have ha1 : a.1.re = 0 := ha.1; simp [ha1], fun x ↦ ?_⟩
      let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
      let g := IdeleClassGroup.ofCompletion (𝓞 F) F v (Units.map e.toMonoidHom x)
      have hx := ha.2 x
      change ideleClassNormTwist χ' 0 g = _
      change ideleClassNormTwist χ 0 g = _ at hx
      have hn : N(g) = ‖(x : ℝ)‖ := by
        change ((ideleClassNorm F (IdeleClassGroup.ofCompletion (𝓞 F) F v _)).val : ℝ) = _
        rw [ideleClassNorm_ofCompletion, hv.mult_eq_one, pow_one]
        exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero
          (map_zero e) (x : ℝ)
      have hx0 : ((‖(x : ℝ)‖ : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
      rw [hsplit, hx, hn, Complex.cpow_add _ _ hx0]
      ring
    rw [hr]
    congr 1
    ring
  · simp only [dif_neg hv]
    have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let a := (complexHeckeCharacter_parameters χ v hc).exists.choose
    have ha := (complexHeckeCharacter_parameters χ v hc).exists.choose_spec
    have hr : (complexHeckeCharacter_parameters χ' v hc).exists.choose =
        (a.1 + y * Complex.I, a.2) := by
      refine (complexHeckeCharacter_parameters χ' v hc).unique
        (complexHeckeCharacter_parameters χ' v hc).exists.choose_spec ⟨by have ha1 : a.1.re = 0 := ha.1; simp [ha1], fun x ↦ ?_⟩
      let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm
      let g := IdeleClassGroup.ofCompletion (𝓞 F) F v (Units.map e.toMonoidHom x)
      have hx := ha.2 x
      change ideleClassNormTwist χ' 0 g = _
      change ideleClassNormTwist χ 0 g = _ at hx
      have hn : N(g) = ‖(x : ℂ)‖ ^ 2 := by
        change ((ideleClassNorm F (IdeleClassGroup.ofCompletion (𝓞 F) F v _)).val : ℝ) = _
        rw [ideleClassNorm_ofCompletion, hc.mult_eq_two]
        have := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
          (map_zero e) (x : ℂ)
        have h2 : ‖e (x : ℂ)‖ = ‖(x : ℂ)‖ := this
        simpa using h2
      have hx0 : ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero))
      rw [hsplit, hx, hn, Complex.cpow_add _ _ hx0]
      ring
    rw [hr]
    congr 2
    ring

/-- The zero divisor of a twist by `|·|^{iy}` is the divisor shifted by `iy`. -/
private theorem introTraceApprox_spectral_summable_shift (χ χ' : U𝔽) (y : ℝ)
    (hχ' : ∀ g, (χ' g : ℂ) = χ g * (N(g) : ℂ) ^ ((y : ℂ) * Complex.I)) (s : ℂ) :
    zeroOrder(χ', s) = zeroOrder(χ, s + y * Complex.I) := by
  classical
  have htw := introTraceApprox_spectral_summable_twist χ χ' y hχ'
  have hre (w : ℂ) : (w + y * Complex.I).re = w.re := by simp
  have hsplit (g : C𝔽) : ideleClassNormTwist χ' 0 g =
      ideleClassNormTwist χ 0 g * (N(g) : ℂ) ^ ((y : ℂ) * Complex.I) := by
    rw [htw, zero_add]
    change (χ g : ℂ) * (N(g) : ℂ) ^ ((y : ℂ) * Complex.I) =
      ((χ g : ℂ) * (N(g) : ℂ) ^ (0 : ℂ)) * (N(g) : ℂ) ^ ((y : ℂ) * Complex.I)
    rw [Complex.cpow_zero, mul_one]
  -- Ramification is unchanged since integer units have norm one.
  have hunit (v : V) (x : (v.adicCompletionIntegers F)ˣ) :
      (ideleClassNormTwist χ' 0).restrict v x = (ideleClassNormTwist χ 0).restrict v x := by
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    have hn : ‖(u : v.adicCompletion F)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := u)).mp
          ⟨x.val.property, x.inv.property⟩)
    have hN : N(IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = 1 := by
      change ((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)).val : ℝ) = 1
      rw [ideleClassNorm_ofAdicCompletion]
      exact hn
    change (ideleClassNormTwist χ' 0).restrict v (u : v.adicCompletion F) =
      (ideleClassNormTwist χ 0).restrict v (u : v.adicCompletion F)
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe, HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change ideleClassNormTwist χ' 0 (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) =
      ideleClassNormTwist χ 0 (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)
    rw [hsplit, hN]
    simp
  have hram (v : V) : (ideleClassNormTwist χ' 0).IsUnramifiedAt v ↔
      (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
    simp only [HeckeCharacter.isUnramifiedAt_iff, hunit]
  -- The Euler factors and finite L-functions agree after the shift.
  have hfac (w : ℂ) (hw : 1 < w.re) (v : V) :
      finiteHeckeEulerFactor χ' v w = finiteHeckeEulerFactor χ v (w + y * Complex.I) := by
    by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
    · let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
      have hπ := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
      let π : (v.adicCompletion F)ˣ := Units.mk0 _ hπ.ne_zero
      have h1 := finiteHeckeEulerFactor_inv_uniformizer χ' v π hπ ((hram v).mpr hu)
        (show w ∈ Complex.re ⁻¹' Ioi (1 : ℝ) from hw)
      have h2 := finiteHeckeEulerFactor_inv_uniformizer χ v π hπ hu
        (show w + y * Complex.I ∈ Complex.re ⁻¹' Ioi (1 : ℝ) from by
          change 1 < (w + y * Complex.I).re; rw [hre]; exact hw)
      have h3 : finitePlaceRestriction F v (ideleClassNormTwist χ' w) π =
          finitePlaceRestriction F v (ideleClassNormTwist χ (w + y * Complex.I)) π := htw w _
      rw [← inv_inj, h1, h2, h3]
    · unfold finiteHeckeEulerFactor
      rw [if_neg (mt (hram v).mp hu), if_neg hu]
  have hcomp (w : ℂ) (hw : 1 < w.re) :
      completedHeckeL χ' ⟨w, hw⟩ = completedHeckeL χ ⟨w + y * Complex.I, by
        change 1 < (w + y * Complex.I).re; rw [hre]; exact hw⟩ := by
    have hw' : 1 < (w + y * Complex.I).re := by rw [hre]; exact hw
    have h1 := finiteHeckeL_hasProd χ' ⟨w, hw⟩
    have h2 := finiteHeckeL_hasProd χ ⟨w + y * Complex.I, hw'⟩
    change HasProd (fun v ↦ finiteHeckeEulerFactor χ' v w) _ at h1
    change HasProd (fun v ↦ finiteHeckeEulerFactor χ v (w + y * Complex.I)) _ at h2
    rw [show (fun v ↦ finiteHeckeEulerFactor χ' v w) =
      fun v ↦ finiteHeckeEulerFactor χ v (w + y * Complex.I) from funext (hfac w hw)] at h1
    unfold completedHeckeL
    change heckeGammaFactor χ' w * finiteHeckeL χ' ⟨w, hw⟩ =
      heckeGammaFactor χ (w + y * Complex.I) * finiteHeckeL χ ⟨w + y * Complex.I, hw'⟩
    rw [introTraceApprox_spectral_summable_gamma χ χ' y hχ', h1.unique h2]
  -- The continuations agree near every point.
  have hL' := continuedCompletedHeckeL_spec χ'
  have hL := continuedCompletedHeckeL_spec χ
  let g : ℂ → ℂ := fun w ↦ continuedCompletedHeckeL χ (w + y * Complex.I)
  have hg : MeromorphicOn g univ := fun w _ ↦
    (hL.1 (mem_univ _)).meromorphicAt.comp_analyticAt (analyticAt_id.add analyticAt_const)
  have hTwo : meromorphicOrderAt (continuedCompletedHeckeL χ' - g) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with w hw
    have hw' : 1 < (w + y * Complex.I).re := by rw [hre]; exact hw
    refine sub_eq_zero.mpr ?_
    change continuedCompletedHeckeL χ' w = continuedCompletedHeckeL χ (w + y * Complex.I)
    rw [show w = ((⟨w, hw⟩ : Complex.re ⁻¹' Ioi (1 : ℝ)) : ℂ) from rfl, hL'.2 ⟨w, hw⟩, hcomp w hw]
    exact (hL.2 ⟨w + y * Complex.I, hw'⟩).symm
  have hev : continuedCompletedHeckeL χ' =ᶠ[𝓝[≠] s] g :=
    (meromorphicOrderAt_eq_top_iff.mp
      ((hL'.1.meromorphicOn.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
        (mem_univ (2 : ℂ)) (mem_univ s) hTwo)).mono fun _ hz ↦ sub_eq_zero.mp hz
  rw [MeromorphicOn.divisor_apply hL'.1.meromorphicOn (mem_univ s),
    MeromorphicOn.divisor_apply hL.1.meromorphicOn (mem_univ _), meromorphicOrderAt_congr hev,
    ← meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  rfl

open Classical in
/-- Vanishing at one removes the conductor term from the signed explicit formula.
The two radial prime shells give the positive and negative samples of the logarithmic test. -/
private theorem introTrace_spectral_digamma_of_vanishing_at_one (χ : U𝔽) (f : ℝ → ℂ)
    (hzero : f 1 = 0) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun u ↦ f (Real.exp u)))
    (hsupp : HasCompactSupport (fun u ↦ f (Real.exp u))) :
    HasSum (fun z : ℂ ↦ (MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z : ℂ) *
      introTraceMellin f (z-1/2))
      ((∑ w : InfinitePlace F, if hw : w.IsReal then
        let p := (realHeckeCharacter_parameters χ w hw).exists.choose
        ∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel (1/2)
          ((1/2 + p.1 + p.2.val)/2) ((1/2 - p.1 + p.2.val)/2) (fun u ↦ f (Real.exp u)) t
        else
          let p := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          ∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel 1
            (1/2 + p.1 + (p.2.natAbs : ℂ)/2) (1/2 - p.1 + (p.2.natAbs : ℂ)/2) (fun u ↦ f (Real.exp u)) t) -
        ∑' j : HeightOneSpectrum (𝓞 F) × ℕ, introTracePrimePower χ f j.1 j.2) := by
  classical
  let φ : SchwartzMap ℝ ℂ := hsupp.toSchwartzMap hsmooth
  have hdec : ExponentialDecay φ := by
    have hc : HasCompactSupport (φ : ℝ → ℂ) := hsupp
    have hz (j : ℕ) : iteratedDeriv j (φ : ℝ → ℂ) =ᶠ[cocompact ℝ] 0 := by
      have hh := hc.iteratedFDeriv (𝕜 := ℝ) j
      rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at hh
      filter_upwards [hh] with x hx
      rw [iteratedDeriv_eq_iteratedFDeriv, hx]
      rfl
    exact ⟨fun j _ _ ↦ ((hz j).filter_mono atTop_le_cocompact).trans_isBigO
      (Asymptotics.isBigO_zero _ _), fun j _ _ ↦ ((hz j).filter_mono atBot_le_cocompact).trans_isBigO
      (Asymptotics.isBigO_zero _ _)⟩
  let L := continuedCompletedHeckeL χ
  have hL := continuedCompletedHeckeL_spec χ
  have H := hasSum_heckeExplicitFormula χ φ hdec L hL.1 hL.2
  have hphi0 : φ 0 = 0 := by change f (Real.exp 0) = 0; rw [Real.exp_zero]; exact hzero
  have hmell (s : ℂ) : mellin (fun t : ℝ ↦ φ (Real.log t)) s = introTraceMellin f s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change _ • f (Real.exp (Real.log t)) = _ • _
    rw [Real.exp_log ht]
  simp_rw [hmell] at H
  simp only [hphi0, mul_zero, zero_sub, sub_zero] at H
  convert H using 1
  rw [sub_eq_add_neg, add_comm]
  congr 1
  · congr 1
    apply tsum_congr
    rintro ⟨v,j⟩
    let N := (v.asIdeal.absNorm : ℝ)
    have hN : 1 < N := by dsimp [N]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    let n' := j+1
    let y : ℝ := (n':ℝ)*Real.log N
    have he : Real.exp y = N^n' := by simp [y, Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hN)]
    have he2 : ((Real.exp (-y/2) : ℝ) : ℂ) = ((N : ℂ) ^ ((n' : ℂ)/2))⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (zero_lt_one.trans hN).ne'),
        ← Complex.exp_neg, ← Complex.ofReal_log (zero_lt_one.trans hN).le, Complex.ofReal_exp]
      congr 1
      dsimp [y]
      push_cast
      ring
    have hval : (ideleClassNormTwist χ⁻¹ 0).localValue v = star ((ideleClassNormTwist χ 0).localValue v) := by
      let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
      let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
        val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
      change (ideleClassNormTwist χ⁻¹ 0).restrict v (u : v.adicCompletion F) =
        star ((ideleClassNormTwist χ 0).restrict v (u : v.adicCompletion F))
      simp only [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
      change ((χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))⁻¹ : ℂ) * _ ^ (0 : ℂ) =
        star ((χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℂ) * _ ^ (0 : ℂ))
      simp only [Complex.cpow_zero, mul_one]
      exact Circle.coe_inv_eq_conj _
    unfold introTracePrimePower
    change (if _ then _ else _) = (if _ then _ else _)
    split_ifs with hv
    · change _ * (_ * f (N^n') + _ * f ((N^n')⁻¹)) / _ =
        ((Real.log N * Real.exp (-y/2) : ℝ) : ℂ) * (_ * φ y + _ * φ (-y))
      rw [show φ (-y) = f ((N^n')⁻¹) by change f (Real.exp (-y)) = _; rw [Real.exp_neg, he],
        show φ y = f (N^n') by
        change f (Real.exp y) = _; rw [he], Complex.ofReal_mul, he2, hval]
      ring
    · rfl

open Classical in
/-- The one-character explicit formula of Theorem B.4.2.2, p. 616, for a smooth compact
logarithmic profile supported above one in the multiplicative coordinate. The conductor term
vanishes and the prime samples agree with the geometric prime-power terms. -/
private theorem introTrace_spectral_digamma_of_supported_above_one (χ : U𝔽) (f : ℝ → ℂ)
    (hzero : ∀ x ≤ 1, f x = 0) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun u ↦ f (Real.exp u)))
    (hsupp : HasCompactSupport (fun u ↦ f (Real.exp u))) :
    HasSum (fun z : ℂ ↦ (MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z : ℂ) *
      introTraceMellin f (z-1/2))
      ((∑ w : InfinitePlace F, if hw : w.IsReal then
        let p := (realHeckeCharacter_parameters χ w hw).exists.choose
        ∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel (1/2)
          ((1/2 + p.1 + p.2.val)/2) ((1/2 - p.1 + p.2.val)/2) (fun u ↦ f (Real.exp u)) t
        else
          let p := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          ∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel 1
            (1/2 + p.1 + (p.2.natAbs : ℂ)/2) (1/2 - p.1 + (p.2.natAbs : ℂ)/2) (fun u ↦ f (Real.exp u)) t) -
        ∑' j : HeightOneSpectrum (𝓞 F) × ℕ, introTracePrimePower χ f j.1 j.2) := by
  exact introTrace_spectral_digamma_of_vanishing_at_one χ f (hzero 1 le_rfl) hsmooth hsupp

/-- Paper: §1.4.3, p. 29. At each fixed cutoff the zero sum converges at every
parameter. This gives the totalized spectral sum its intended value in every chart. -/
theorem introTraceApprox_spectral_summable (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (a : ℝ) (_ha : 0 < a) (z : ℂ) :
    Summable (fun r : windowZeros(χ, a) ↦
      (zeroOrder(χ, r.val) : ℂ) * introTraceMellin approx(h, ρ, n, z) (r.val - 1 / 2)) := by
  let f := approx(h, ρ, n, z)
  have hzero (t : ℝ) (ht : t ≤ 1) : f t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hu ↦ (not_lt_of_ge ht) (introTraceApprox_support h ρ _hA n z hu))
  have hreg := introTraceApprox_logProfile h ρ _hA n z
  exact (introTrace_spectral_digamma_of_supported_above_one χ f hzero hreg.1 hreg.2).summable.subtype _

/-- Removing the gamma factor gives a continuation of the finite L-function. The entire
reciprocal gamma factor can only increase the order at a zero. -/
private theorem zeroCount_finite_companion (χ : U𝔽) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧ (∀ z : right(1), L z = finiteHeckeL χ z) ∧
      ∀ z, meromorphicOrderAt (continuedCompletedHeckeL χ) z ≤ meromorphicOrderAt L z := by
  let Λ := continuedCompletedHeckeL χ
  let G (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let P := G * Λ
  obtain ⟨hΛ, hval⟩ := continuedCompletedHeckeL_spec χ
  have hG := differentiable_inv_heckeGammaFactor χ
  have hm : MeromorphicOn P univ := fun z hz ↦
    (hG.analyticAt z).meromorphicAt.mul (hΛ hz).meromorphicAt
  refine ⟨toMeromorphicNFOn P univ, meromorphicNFOn_toMeromorphicNFOn _ _, ?_, ?_⟩
  · intro z
    have hγ := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans z.property)
    have hNF : MeromorphicNFAt P z :=
      (meromorphicNFAt_mul_iff_right (hG.analyticAt z) (inv_ne_zero hγ)).2 (hΛ (mem_univ _))
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _), toMeromorphicNFAt_eq_self.mpr hNF]
    simp [P, Λ, G, hval z, completedHeckeL, finiteHeckeL, hγ]
  · intro z
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _),
      show meromorphicOrderAt P z = _ from meromorphicOrderAt_mul
        (hG.analyticAt z).meromorphicAt (hΛ (mem_univ z)).meromorphicAt]
    exact le_add_of_nonneg_left (hG.analyticAt z).meromorphicOrderAt_nonneg

/-- Paper: §1.4.3, p. 29, for the proof that the zero sum is entire. Weighted zero count:
for every unitary character `χ` and every half-width `a`, the zeros of the completed Hecke
L-function in the open window `|Re s - 1/2| < a`, counted with their orders, satisfy
`∑ ord(ρ) / (1 + |Im ρ|)² < ∞`. This is the classical consequence of the zero count
`N(T + 1) - N(T) = O(log T)` for Hecke L-functions. -/
private theorem introTraceApprox_spectral_differentiable_zeroCount (χ : U𝔽) (a : ℝ) :
    Summable (fun r : windowZeros(χ, a) ↦ (zeroOrder(χ, r.val) : ℝ) / (1 + |r.val.im|) ^ 2) := by
  obtain ⟨L, hL, hSeries, hOrder⟩ := zeroCount_finite_companion χ
  obtain ⟨hLine, k, _, hInv⟩ := finiteHeckeL_inv_isBigO_oneLine χ L hL hSeries
  exact summable_divisor_div_one_add_abs_im_sq (k := k) (σ := 1)
    (continuedCompletedHeckeL_spec χ).1.meromorphicOn hL hOrder
    (finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries) (hLine.mono fun _ ht ↦ ht.2)
    hInv (1 / 2) a

/-- A Mellin transform of a function vanishing outside `(a, b)`, with `0 < a`, is the
interval integral over `[a, b]`. -/
private theorem introTraceApprox_spectral_differentiable_mellin_interval (f : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hf : ∀ t, f t ≠ 0 → t ∈ Ioo a b) (s : ℂ) :
    introTraceMellin f s = ∫ t in a..b, (t : ℂ) ^ (s - 1) * f t := by
  unfold introTraceMellin mellin
  have hsub : Ioc a b ⊆ Ioi (0 : ℝ) := fun t ht ↦ ha.trans ht.1
  rw [intervalIntegral.integral_of_le hab]
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
    fun t ht ↦ ?_).trans rfl
  by_contra hne
  have hft : f t ≠ 0 := fun h0 ↦ hne (by rw [h0, smul_zero])
  exact ht.2 (Ioo_subset_Ioc_self (hf t hft))

/-- Two integrations by parts bound an interval Mellin integral of a `C²` function vanishing
to first order at both ends by `C / (1 + |Im s|)²` on a vertical strip. -/
private theorem introTraceApprox_spectral_differentiable_parts {f : ℝ → ℂ} {a b B D0 D2 : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hf : ContDiff ℝ 2 f) (hfa : f a = 0) (hfb : f b = 0)
    (hfa' : deriv f a = 0) (hfb' : deriv f b = 0) (h0 : ∀ t ∈ Icc a b, ‖f t‖ ≤ D0)
    (h2 : ∀ t ∈ Icc a b, ‖deriv (deriv f) t‖ ≤ D2) (s : ℂ) (hs : |s.re| ≤ B) :
    ‖∫ t in a..b, (t : ℂ) ^ (s - 1) * f t‖ ≤
      4 * (b - a) * (max b a⁻¹ + 1) ^ (B + 1) * max D0 D2 / (1 + |s.im|) ^ 2 := by
  set M := max b a⁻¹ + 1 with hMdef
  have ha' : 0 < a⁻¹ := inv_pos.mpr ha
  have hM1 : 1 ≤ M := by have := le_max_right b a⁻¹; linarith
  have hB : 0 ≤ B := (abs_nonneg _).trans hs
  have hD0 : 0 ≤ D0 := (norm_nonneg _).trans (h0 a ⟨le_rfl, hab⟩)
  have hD2 : 0 ≤ D2 := (norm_nonneg _).trans (h2 a ⟨le_rfl, hab⟩)
  have hpow : ∀ t ∈ Icc a b, ∀ x : ℝ, |x| ≤ B + 1 → t ^ x ≤ M ^ (B + 1) := by
    intro t ht x hx
    have htpos : 0 < t := ha.trans_le ht.1
    have hlogt : |Real.log t| ≤ Real.log M := by
      rw [abs_le]
      constructor
      · have hinv : t⁻¹ ≤ M := (inv_anti₀ ha ht.1).trans (by have := le_max_right b a⁻¹; linarith)
        have := Real.log_le_log (inv_pos.mpr htpos) hinv
        rw [Real.log_inv] at this
        linarith
      · exact Real.log_le_log htpos (by have := le_max_left b a⁻¹; linarith [ht.2])
    rw [Real.rpow_def_of_pos htpos, Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    calc Real.log t * x ≤ |Real.log t * x| := le_abs_self _
      _ = |Real.log t| * |x| := abs_mul _ _
      _ ≤ Real.log M * (B + 1) := mul_le_mul hlogt hx (abs_nonneg _) (Real.log_nonneg hM1)
  set T := M ^ (B + 1) with hTdef
  have hT : 0 ≤ T := by positivity
  have hnorm (t : ℝ) (ht : t ∈ Icc a b) (w : ℂ) (hw : |w.re| ≤ B + 1) : ‖(t : ℂ) ^ w‖ ≤ T := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le ht.1)]
    exact hpow t ht _ hw
  have hsub : ∀ x ∈ Set.uIoc a b, x ∈ Icc a b := fun x hx ↦ by
    rw [Set.uIoc_of_le hab] at hx
    exact Ioc_subset_Icc_self hx
  have hre1 : |(s - 1).re| ≤ B + 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    calc |s.re - 1| ≤ |s.re| + |1| := abs_sub _ _
      _ ≤ B + 1 := by rw [abs_one]; linarith
  have hre2 : |(s + 1).re| ≤ B + 1 := by
    simp only [Complex.add_re, Complex.one_re]
    calc |s.re + 1| ≤ |s.re| + |1| := abs_add_le _ _
      _ ≤ B + 1 := by rw [abs_one]; linarith
  have hA : ‖∫ t in a..b, (t : ℂ) ^ (s - 1) * f t‖ ≤ T * D0 * (b - a) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := T * D0)
      (f := fun t ↦ (t : ℂ) ^ (s - 1) * f t) (a := a) (b := b) (fun x hx ↦ by
        rw [norm_mul]
        exact mul_le_mul (hnorm x (hsub x hx) _ hre1) (h0 x (hsub x hx)) (norm_nonneg _) hT)
    rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at this
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hden : 0 < (1 + |s.im|) ^ 2 := by positivity
  by_cases hI : |s.im| ≤ 1
  · rw [le_div_iff₀ hden]
    have h4 : (1 + |s.im|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg s.im]
    calc ‖∫ t in a..b, (t : ℂ) ^ (s - 1) * f t‖ * (1 + |s.im|) ^ 2
        ≤ (T * D0 * (b - a)) * 4 := mul_le_mul hA h4 hden.le (by positivity)
      _ ≤ 4 * (b - a) * T * max D0 D2 := by
          have := le_max_left D0 D2
          have : T * D0 * (b - a) ≤ T * max D0 D2 * (b - a) := by gcongr
          nlinarith
  push Not at hI
  have hs0 : s ≠ 0 := fun h ↦ by rw [h] at hI; simp at hI; linarith
  have hs1 : s + 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im] at this
    rw [this, abs_zero] at hI
    linarith
  -- Regularity of `f`.
  have hf' := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)
  have hd1 : Differentiable ℝ f := hf'.1
  have hf'' := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv f) from hf'.2.2)
  have hd2 : Differentiable ℝ (deriv f) := hf''.1
  have hc2 : Continuous (deriv (deriv f)) := hf''.2.2.continuous
  have hc1 : Continuous (deriv f) := hd2.continuous
  have hpos : ∀ x ∈ Set.uIcc a b, x ≠ 0 := fun x hx ↦ by
    rw [Set.uIcc_of_le hab] at hx
    exact (ha.trans_le hx.1).ne'
  have hcpow (w : ℂ) : IntervalIntegrable (fun y : ℝ ↦ (y : ℂ) ^ w) volume a b :=
    ContinuousOn.intervalIntegrable fun x hx ↦
      (Complex.continuousAt_ofReal_cpow_const x w (Or.inr (hpos x hx))).continuousWithinAt
  -- First integration by parts.
  have hp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b) (u := f)
    (u' := deriv f) (v := fun y : ℝ ↦ (y : ℂ) ^ ((s - 1) + 1) / ((s - 1) + 1))
    (v' := fun y : ℝ ↦ (y : ℂ) ^ (s - 1))
    (fun x _ ↦ (hd1 x).hasDerivAt)
    (fun x hx ↦ hasDerivAt_ofReal_cpow_const' (hpos x hx) (by
      intro h; apply hs0; linear_combination h))
    (hc1.intervalIntegrable a b) (hcpow _)
  -- Second integration by parts.
  have hp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b) (u := deriv f)
    (u' := deriv (deriv f)) (v := fun y : ℝ ↦ (y : ℂ) ^ (s + 1) / (s + 1))
    (v' := fun y : ℝ ↦ (y : ℂ) ^ s)
    (fun x _ ↦ (hd2 x).hasDerivAt)
    (fun x hx ↦ hasDerivAt_ofReal_cpow_const' (hpos x hx) (by
      intro h; apply hs1; linear_combination h))
    (hc2.intervalIntegrable a b) (hcpow _)
  simp only [sub_add_cancel, hfa, hfb, hfa', hfb', zero_mul, sub_zero, zero_sub] at hp1 hp2
  have hparts : ∫ t in a..b, (t : ℂ) ^ (s - 1) * f t =
      (∫ t in a..b, (t : ℂ) ^ (s + 1) * deriv (deriv f) t) / (s * (s + 1)) := by
    have e1 : ∫ t in a..b, (t : ℂ) ^ (s - 1) * f t = ∫ t in a..b, f t * (t : ℂ) ^ (s - 1) :=
      intervalIntegral.integral_congr fun t _ ↦ mul_comm _ _
    have e2 : ∫ t in a..b, deriv f t * ((t : ℂ) ^ s / s) =
        (∫ t in a..b, deriv f t * (t : ℂ) ^ s) / s := by
      rw [← intervalIntegral.integral_div]
      exact intervalIntegral.integral_congr fun t _ ↦ by ring
    have e3 : ∫ t in a..b, deriv (deriv f) t * ((t : ℂ) ^ (s + 1) / (s + 1)) =
        (∫ t in a..b, (t : ℂ) ^ (s + 1) * deriv (deriv f) t) / (s + 1) := by
      rw [← intervalIntegral.integral_div]
      exact intervalIntegral.integral_congr fun t _ ↦ by ring
    rw [e1, hp1, e2, hp2, e3]
    field_simp
  rw [hparts, norm_div, norm_mul]
  have hI0 : 0 < |s.im| := by linarith
  have hns : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hns1 : |s.im| ≤ ‖s + 1‖ := by
    have := Complex.abs_im_le_norm (s + 1)
    simpa using this
  have hB2 : ‖∫ t in a..b, (t : ℂ) ^ (s + 1) * deriv (deriv f) t‖ ≤ T * D2 * (b - a) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := T * D2)
      (f := fun t ↦ (t : ℂ) ^ (s + 1) * deriv (deriv f) t) (a := a) (b := b) (fun x hx ↦ by
        rw [norm_mul]
        exact mul_le_mul (hnorm x (hsub x hx) _ hre2) (h2 x (hsub x hx)) (norm_nonneg _) hT)
    rwa [abs_of_nonneg hba] at this
  have hsq : (1 + |s.im|) ^ 2 ≤ 4 * (‖s‖ * ‖s + 1‖) := by
    have : 1 + |s.im| ≤ 2 * |s.im| := by linarith
    nlinarith [mul_le_mul hns hns1 hI0.le (norm_nonneg _)]
  rw [div_le_div_iff₀ (by positivity) hden]
  calc ‖∫ t in a..b, (t : ℂ) ^ (s + 1) * deriv (deriv f) t‖ * (1 + |s.im|) ^ 2
      ≤ (T * D2 * (b - a)) * (4 * (‖s‖ * ‖s + 1‖)) := mul_le_mul hB2 hsq hden.le (by positivity)
    _ ≤ 4 * (b - a) * T * max D0 D2 * (‖s‖ * ‖s + 1‖) := by
        have : T * D2 * (b - a) ≤ T * max D0 D2 * (b - a) := by gcongr; exact le_max_right _ _
        have hss : 0 ≤ ‖s‖ * ‖s + 1‖ := by positivity
        nlinarith

/-- The kernels `t ↦ h(t) ρ(t - v)` of the mollified cutoff are `C²`, vanish to first order at the
ends of a fixed interval `[a, b] ⊂ (0, ∞)` containing the cutoff's support, and have value and second
derivative bounded uniformly in `v`. -/
private theorem introTraceApprox_spectral_differentiable_kernel (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (n : ℕ) :
    ∃ a b D : ℝ, 0 < a ∧ a ≤ b ∧ (∀ t, h n t ≠ 0 → t ∈ Ioo a b) ∧
      ∀ v : ℝ, ContDiff ℝ 2 (fun t ↦ (h n t : ℂ) * (ρ n (t - v) : ℂ)) ∧
        (fun t ↦ (h n t : ℂ) * (ρ n (t - v) : ℂ)) a = 0 ∧
        (fun t ↦ (h n t : ℂ) * (ρ n (t - v) : ℂ)) b = 0 ∧
        deriv (fun t ↦ (h n t : ℂ) * (ρ n (t - v) : ℂ)) a = 0 ∧
        deriv (fun t ↦ (h n t : ℂ) * (ρ n (t - v) : ℂ)) b = 0 ∧
        (∀ t, ‖(h n t : ℂ) * (ρ n (t - v) : ℂ)‖ ≤ D) ∧
        ∀ t, ‖deriv (deriv (fun t ↦ (h n t : ℂ) * (ρ n (t - v) : ℂ))) t‖ ≤ D := by
  obtain ⟨hh, -, -, ε, -, hρ⟩ := hA
  obtain ⟨hhs, hhc, hhsub, -⟩ := hh n
  obtain ⟨-, hρs, -, hρsub, -⟩ := hρ n
  -- The support of the cutoff lies in `[c, R]` with `1 < c`.
  obtain ⟨c, hc1, hc⟩ : ∃ c, 1 < c ∧ ∀ x ∈ tsupport (h n), c ≤ x := by
    rcases (tsupport (h n)).eq_empty_or_nonempty with he | hne
    · exact ⟨2, by norm_num, by simp [he]⟩
    · obtain ⟨c, hcK, hcmin⟩ := hhc.exists_isMinOn hne continuousOn_id
      exact ⟨c, hhsub hcK, fun x hx ↦ hcmin hx⟩
  obtain ⟨R, hR⟩ := hhc.bddAbove
  have hzero (t : ℝ) (ht : h n t ≠ 0) : c ≤ t ∧ t ≤ R :=
    ⟨hc t (subset_tsupport _ ht), hR (subset_tsupport _ ht)⟩
  have hcR : c ≤ R ∨ ∀ t, h n t = 0 := by
    by_cases hall : ∀ t, h n t = 0
    · exact Or.inr hall
    · push Not at hall
      obtain ⟨t, ht⟩ := hall
      exact Or.inl ((hzero t ht).1.trans (hzero t ht).2)
  let a : ℝ := 1 / 2
  let b : ℝ := max R c + 1
  have hab : a ≤ b := by
    have := le_max_right R c
    simp only [a, b]
    linarith
  -- Smoothness and derivative bounds of the two factors.
  let H : ℝ → ℂ := fun t ↦ (h n t : ℂ)
  let P : ℝ → ℂ := fun t ↦ (ρ n t : ℂ)
  have hHs : ContDiff ℝ (⊤ : ℕ∞) H := Complex.ofRealCLM.contDiff.comp hhs
  have hPs : ContDiff ℝ (⊤ : ℕ∞) P := Complex.ofRealCLM.contDiff.comp hρs
  have hHc : HasCompactSupport H := hhc.comp_left Complex.ofReal_zero
  have hPc : HasCompactSupport P :=
    (HasCompactSupport.intro' isCompact_Icc isClosed_Icc fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hρsub h')).comp_left Complex.ofReal_zero
  obtain ⟨CH, hCH0, hCH⟩ := hHc.exists_bound_iteratedFDeriv hHs 2
  obtain ⟨CP, hCP0, hCP⟩ := hPc.exists_bound_iteratedFDeriv hPs 2
  refine ⟨a, b, 4 * CH * CP, by norm_num [a], hab, fun t ht ↦ ?_, fun v ↦ ?_⟩
  · obtain ⟨h1, h2⟩ := hzero t ht
    exact ⟨by simp only [a]; linarith, by simp only [b]; linarith [le_max_left R c]⟩
  let Pv : ℝ → ℂ := fun t ↦ P (t - v)
  have hPvs : ContDiff ℝ (⊤ : ℕ∞) Pv := hPs.comp (contDiff_id.sub contDiff_const)
  have hk : (fun t ↦ (h n t : ℂ) * (ρ n (t - v) : ℂ)) = fun t ↦ H t * Pv t := rfl
  have hloc (x : ℝ) (hx : x < c ∨ R < x) :
      (fun t ↦ (h n t : ℂ) * (ρ n (t - v) : ℂ)) =ᶠ[𝓝 x] fun _ ↦ 0 := by
    rcases hx with hx | hx
    · filter_upwards [Iio_mem_nhds hx] with t ht
      have : h n t = 0 := by
        by_contra hne
        exact (not_le.mpr ht) (hzero t hne).1
      simp [this]
    · filter_upwards [Ioi_mem_nhds hx] with t ht
      have : h n t = 0 := by
        by_contra hne
        exact (not_le.mpr ht) (hzero t hne).2
      simp [this]
  have hac : a < c := by simp only [a]; linarith
  have hbR : R < b ∨ ∀ t, h n t = 0 := by
    rcases hcR with hcR | hall
    · left; simp only [b]; linarith [le_max_left R c]
    · exact Or.inr hall
  have hb0 : (fun t ↦ (h n t : ℂ) * (ρ n (t - v) : ℂ)) =ᶠ[𝓝 b] fun _ ↦ 0 := by
    rcases hbR with hbR | hall
    · exact hloc b (Or.inr hbR)
    · exact Eventually.of_forall fun t ↦ by simp [hall t]
  have hbound (t : ℝ) : ‖iteratedFDeriv ℝ 2 (fun t ↦ H t * Pv t) t‖ ≤ 4 * CH * CP := by
    refine (norm_iteratedFDeriv_mul_le (hHs.of_le (by simp)) (hPvs.of_le (by simp)) t
      (n := 2) (N := 2) le_rfl).trans ?_
    have hterm (i : ℕ) (hi : i ∈ Finset.range 3) :
        ((2 : ℕ).choose i : ℝ) * ‖iteratedFDeriv ℝ i H t‖ * ‖iteratedFDeriv ℝ (2 - i) Pv t‖ ≤
          ((2 : ℕ).choose i : ℝ) * CH * CP := by
      have hi3 : i ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hPvi : ‖iteratedFDeriv ℝ (2 - i) Pv t‖ ≤ CP := by
        have := iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := P) (2 - i) v t
        change ‖iteratedFDeriv ℝ (2 - i) (fun z ↦ P (z - v)) t‖ ≤ CP
        rw [this]
        exact hCP _ (Nat.sub_le _ _) _
      gcongr
      exact hCH i hi3 t
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    simp [Finset.sum_range_succ]
    ring
  refine ⟨hk ▸ (hHs.mul hPvs).of_le (by simp), ?_, ?_, ?_, ?_, fun t ↦ ?_, fun t ↦ ?_⟩
  · exact (hloc a (Or.inl hac)).self_of_nhds
  · exact hb0.self_of_nhds
  · rw [(hloc a (Or.inl hac)).deriv_eq, deriv_const]
  · rw [hb0.deriv_eq, deriv_const]
  · have h0 := hbound t
    have hH0 := hCH 0 (by norm_num) t
    have hP0 := hCP 0 (by norm_num) (t - v)
    rw [norm_iteratedFDeriv_zero] at hH0 hP0
    rw [norm_mul]
    calc ‖(h n t : ℂ)‖ * ‖(ρ n (t - v) : ℂ)‖ ≤ CH * CP :=
          mul_le_mul hH0 hP0 (norm_nonneg _) hCH0
      _ ≤ 4 * CH * CP := by nlinarith [mul_nonneg hCH0 hCP0]
  · have h2 := hbound t
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate] at h2
    simpa [hk] using h2

/-- On `[p, q] ⊂ (0, ∞)`, a real power is bounded by the sum of its values at the ends. -/
private theorem introTraceApprox_spectral_differentiable_rpow_le {p q t x : ℝ} (hp : 0 < p)
    (hpt : p ≤ t) (htq : t ≤ q) : t ^ x ≤ p ^ x + q ^ x := by
  rcases le_total 0 x with hx | hx
  · exact (Real.rpow_le_rpow (hp.le.trans hpt) htq hx).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hp.le _))
  · exact (Real.rpow_le_rpow_of_nonpos hp hpt hx).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (hp.le.trans (hpt.trans htq)) _))

/-- Fubini: the Mellin transform of the approximant is the integral of the radial power against
the Mellin transforms of the kernels `t ↦ h(t) ρ(t - v)`. -/
private theorem introTraceApprox_spectral_differentiable_fubini (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : ∀ t, h n t ≠ 0 → t ∈ Ioo a b) (z s : ℂ) :
    introTraceMellin approx(h, ρ, n, z) s = ∫ v, introTracePower z v *
      ∫ t in a..b, (t : ℂ) ^ (s - 1) * ((h n t : ℂ) * (ρ n (t - v) : ℂ)) := by
  obtain ⟨hh, -, -, ε, -, hρ⟩ := hA
  obtain ⟨hε0, hρs, -, hρsub, -⟩ := hρ n
  have hPm := introTraceApprox_mellin_tendsto_power_measurable z
  rw [introTraceApprox_spectral_differentiable_mellin_interval _ ha hab (fun t ht ↦ hsupp t
    (fun h0 ↦ ht (by simp [introTraceApprox, h0]))) s]
  have hconv (t : ℝ) : introTraceApprox (h n) (ρ n) z t =
      (h n t : ℂ) * ∫ v, (ρ n (t - v) : ℂ) * introTracePower z v := by
    unfold introTraceApprox
    congr 1
    rw [← integral_sub_left_eq_self (fun u ↦ (ρ n u : ℂ) * introTracePower z (t - u)) volume t]
    simp only [sub_sub_cancel]
  simp_rw [hconv]
  -- Bounds for the integrand.
  obtain ⟨Cρ, hCρ⟩ := hρs.continuous.bounded_above_of_compact_support
    (HasCompactSupport.intro' isCompact_Icc isClosed_Icc fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hρsub h'))
  let T : ℝ := a ^ (s - 1).re + b ^ (s - 1).re
  let L : ℝ := b + ε n + 1
  let BP : ℝ := 1 + (1 : ℝ) ^ (-z.re) + L ^ (-z.re)
  have hT (t : ℝ) (ht : t ∈ Icc a b) : ‖(t : ℂ) ^ (s - 1)‖ ≤ T := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le ht.1)]
    exact introTraceApprox_spectral_differentiable_rpow_le ha ht.1 ht.2
  have hBP (v : ℝ) (hv : v ≤ L) : ‖introTracePower z v‖ ≤ BP := by
    unfold introTracePower
    have hL0 : 0 < L := by simp only [L]; linarith
    have h0 : (0 : ℝ) ≤ (1 : ℝ) ^ (-z.re) + L ^ (-z.re) :=
      add_nonneg (Real.rpow_nonneg zero_le_one _) (Real.rpow_nonneg hL0.le _)
    split_ifs with h1 h2
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans h1), Complex.neg_re]
      have := introTraceApprox_spectral_differentiable_rpow_le (x := -z.re) zero_lt_one h1.le hv
      simp only [BP]
      linarith
    · have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      simp only [BP, this]
      linarith
    · simp only [norm_zero, BP]; linarith
  have hT0 : 0 ≤ T := add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (ha.le.trans hab) _)
  have hCρ0 : 0 ≤ Cρ := (norm_nonneg _).trans (hCρ 0)
  have hBP0 : 0 ≤ BP := (norm_nonneg _).trans (hBP 0 (by simp only [L]; linarith))
  have hK0 : 0 ≤ T * Cρ * BP := by positivity
  let G : ℝ → ℝ → ℂ := fun t v ↦ if t ∈ Ioc a b then
    (t : ℂ) ^ (s - 1) * ((h n t : ℂ) * ((ρ n (t - v) : ℂ) * introTracePower z v)) else 0
  have hGm : Measurable (uncurry G) := by
    refine Measurable.ite (measurableSet_Ioc.preimage measurable_fst) ?_ measurable_const
    refine ((Complex.measurable_ofReal.pow_const _).comp measurable_fst).mul
      ((Complex.measurable_ofReal.comp ((hh n).1.continuous.measurable.comp measurable_fst)).mul
      ((Complex.measurable_ofReal.comp (hρs.continuous.measurable.comp
        (measurable_fst.sub measurable_snd))).mul (hPm.comp measurable_snd)))
  have hGint : Integrable (uncurry G) (volume.prod volume) := by
    have hg : Integrable (fun p : ℝ × ℝ ↦ (Icc a b).indicator (fun _ ↦ T * Cρ * BP) p.1 *
        (Icc (a - ε n) (b + ε n)).indicator (fun _ ↦ (1 : ℝ)) p.2) (volume.prod volume) :=
      Integrable.mul_prod (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc)
        (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc)
    refine hg.mono' hGm.aestronglyMeasurable (Eventually.of_forall fun p ↦ ?_)
    obtain ⟨t, v⟩ := p
    change ‖G t v‖ ≤ _
    by_cases ht : t ∈ Ioc a b
    swap
    · simp only [G, if_neg ht, norm_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ ↦ hK0) _)
        (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
    by_cases hv : ρ n (t - v) = 0
    · simp only [G, if_pos ht, hv, Complex.ofReal_zero, zero_mul, mul_zero, norm_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ ↦ hK0) _)
        (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
    have hvt := hρsub (subset_tsupport _ hv)
    have hvI : v ∈ Icc (a - ε n) (b + ε n) := ⟨by linarith [hvt.2, ht.1], by linarith [hvt.1, ht.2]⟩
    simp only [G, if_pos ht, indicator_of_mem (Ioc_subset_Icc_self ht),
      indicator_of_mem hvI, mul_one]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    have hh1 : ‖h n t‖ ≤ 1 := by
      rw [Real.norm_of_nonneg ((hh n).2.2.2 t).1]; exact ((hh n).2.2.2 t).2
    calc ‖(t : ℂ) ^ (s - 1)‖ * (‖h n t‖ * (‖ρ n (t - v)‖ * ‖introTracePower z v‖))
        ≤ T * (1 * (Cρ * BP)) := by
          refine mul_le_mul (hT t (Ioc_subset_Icc_self ht)) ?_ (by positivity) hT0
          refine mul_le_mul hh1 ?_ (by positivity) zero_le_one
          exact mul_le_mul (hCρ _) (hBP v (by simp only [L]; linarith [hvI.2])) (norm_nonneg _) hCρ0
      _ = T * Cρ * BP := by ring
  -- Swap the integrals.
  have hL : ∫ t in a..b, (t : ℂ) ^ (s - 1) *
      ((h n t : ℂ) * ∫ v, (ρ n (t - v) : ℂ) * introTracePower z v) = ∫ t, ∫ v, G t v := by
    rw [intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc]
    congr 1
    funext t
    by_cases ht : t ∈ Ioc a b
    · simp only [indicator_of_mem ht, G, if_pos ht]
      rw [integral_const_mul, integral_const_mul]
    · simp only [indicator_of_notMem ht, G, if_neg ht, integral_zero]
  rw [hL, integral_integral_swap hGint]
  congr 1
  funext v
  have hG : (fun t ↦ G t v) = (Ioc a b).indicator (fun t ↦ introTracePower z v *
      ((t : ℂ) ^ (s - 1) * ((h n t : ℂ) * (ρ n (t - v) : ℂ)))) := by
    funext t
    by_cases ht : t ∈ Ioc a b
    · simp only [G, if_pos ht, indicator_of_mem ht]; ring
    · simp only [G, if_neg ht, indicator_of_notMem ht]
  rw [hG, integral_indicator measurableSet_Ioc, integral_const_mul,
    ← intervalIntegral.integral_of_le hab]

/-- The radial power is bounded on `(-∞, L]` uniformly for `|Re z| ≤ r`. -/
private theorem introTraceApprox_spectral_differentiable_power_le {z : ℂ} {r L v : ℝ}
    (hL : 1 ≤ L) (hz : |z.re| ≤ r) (hv : v ≤ L) : ‖introTracePower z v‖ ≤ 2 + L ^ r := by
  have hLr : 0 ≤ L ^ r := Real.rpow_nonneg (zero_le_one.trans hL) _
  unfold introTracePower
  split_ifs with h1 h2
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans h1), Complex.neg_re]
    have h3 := introTraceApprox_spectral_differentiable_rpow_le (x := -z.re) zero_lt_one h1.le hv
    have h4 : L ^ (-z.re) ≤ L ^ r :=
      Real.rpow_le_rpow_of_exponent_le hL (by linarith [neg_abs_le z.re])
    rw [Real.one_rpow] at h3
    linarith
  · have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    linarith
  · rw [norm_zero]
    linarith

/-- Paper: §§1.4.2–1.4.3, pp. 28–29. At a fixed cutoff and a fixed Mellin variable `s`, the
Mellin transform of the approximant is entire in the parameter `z`. The approximant is
supported in a fixed compact subset of `(1, ∞)` and is entire in `z` at each radius
(`introTraceApprox_differentiable`), with bounds locally uniform in `z`. -/
private theorem introTraceApprox_spectral_differentiable_mellin_entire (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (s : ℂ) :
    Differentiable ℂ (fun z ↦ introTraceMellin approx(h, ρ, n, z) s) := by
  obtain ⟨a', b', D, ha, hab, hsupp, hk⟩ := introTraceApprox_spectral_differentiable_kernel h ρ _hA n
  have hfub := introTraceApprox_spectral_differentiable_fubini h ρ _hA n ha hab hsupp
  obtain ⟨hh, -, -, ε, -, hρ⟩ := _hA
  obtain ⟨hε0, hρs, -, hρsub, -⟩ := hρ n
  let m : ℝ → ℂ := fun v ↦ ∫ t in a'..b', (t : ℂ) ^ (s - 1) * ((h n t : ℂ) * (ρ n (t - v) : ℂ))
  have hm0 (v : ℝ) (hv : v ∉ Icc (a' - ε n) (b' + ε n)) : m v = 0 := by
    refine (intervalIntegral.integral_congr fun t ht ↦ ?_).trans intervalIntegral.integral_zero
    rw [Set.uIcc_of_le hab] at ht
    have : ρ n (t - v) = 0 := by
      by_contra hne
      have := hρsub (subset_tsupport _ hne)
      exact hv ⟨by linarith [this.2, ht.1], by linarith [this.1, ht.2]⟩
    simp [this]
  let Bm : ℝ := (a' ^ (s - 1).re + b' ^ (s - 1).re) * D * (b' - a')
  have hD : 0 ≤ D := (norm_nonneg _).trans ((hk 0).2.2.2.2.2.1 a')
  have hm (v : ℝ) : ‖m v‖ ≤ Bm := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := (a' ^ (s - 1).re + b' ^ (s - 1).re) * D)
      (f := fun t ↦ (t : ℂ) ^ (s - 1) * ((h n t : ℂ) * (ρ n (t - v) : ℂ))) (a := a') (b := b')
      (fun x hx ↦ by
        rw [Set.uIoc_of_le hab] at hx
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans hx.1)]
        exact mul_le_mul (introTraceApprox_spectral_differentiable_rpow_le ha hx.1.le hx.2)
          ((hk v).2.2.2.2.2.1 x) (norm_nonneg _)
          (add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (ha.le.trans hab) _)))
    rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at this
  have hmm : Measurable m := by
    have hF : StronglyMeasurable (uncurry fun t v : ℝ ↦
        (t : ℂ) ^ (s - 1) * ((h n t : ℂ) * (ρ n (t - v) : ℂ))) :=
      (((Complex.measurable_ofReal.pow_const _).comp measurable_fst).mul
        ((Complex.measurable_ofReal.comp
          ((hh n).1.continuous.measurable.comp measurable_fst)).mul
        (Complex.measurable_ofReal.comp (hρs.continuous.measurable.comp
          (measurable_fst.sub measurable_snd))))).stronglyMeasurable
    have hme : m = fun v ↦ ∫ t, (t : ℂ) ^ (s - 1) * ((h n t : ℂ) * (ρ n (t - v) : ℂ))
        ∂(volume.restrict (Ioc a' b')) := funext fun v ↦ intervalIntegral.integral_of_le hab
    rw [hme]
    exact (hF.integral_prod_left (μ := volume.restrict (Ioc a' b'))).measurable
  rw [show (fun z ↦ introTraceMellin approx(h, ρ, n, z) s) = fun z ↦ ∫ v, introTracePower z v * m v
    from funext fun z ↦ hfub z s]
  intro z₀
  let L : ℝ := b' + ε n + 1
  have hL1 : 1 ≤ L := by simp only [L]; linarith
  let r : ℝ := |z₀.re| + 1
  have hball (z : ℂ) (hz : z ∈ Metric.ball z₀ 1) : |z.re| ≤ r := by
    have h1 : |z.re - z₀.re| < 1 :=
      (Complex.abs_re_le_norm (z - z₀)).trans_lt (by simpa [dist_eq_norm] using hz)
    have h2 := abs_sub_abs_le_abs_sub z.re z₀.re
    simp only [r]
    linarith
  have hPm := introTraceApprox_mellin_tendsto_power_measurable
  have hLr : 0 ≤ 2 + L ^ r := by positivity
  have hBm : 0 ≤ Bm := (norm_nonneg _).trans (hm 0)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hvL (v : ℝ) (hv : v ∈ Icc (a' - ε n) (b' + ε n)) : v ≤ L := by
    simp only [L]; linarith [hv.2]
  let F' : ℂ → ℝ → ℂ := fun z v ↦
    (if 1 < v then (v : ℂ) ^ (-z) * Complex.log v * (-1) else 0) * m v
  let bnd : ℝ → ℝ := (Icc (a' - ε n) (b' + ε n)).indicator fun _ ↦ (2 + L ^ r) * Real.log L * Bm
  have hFint : Integrable (fun v ↦ introTracePower z₀ v * m v) := by
    refine Integrable.mono' (g := (Icc (a' - ε n) (b' + ε n)).indicator fun _ ↦ (2 + L ^ r) * Bm)
      (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc)
      ((hPm z₀).mul hmm).aestronglyMeasurable (Eventually.of_forall fun v ↦ ?_)
    by_cases hv : v ∈ Icc (a' - ε n) (b' + ε n)
    · rw [indicator_of_mem hv, norm_mul]
      exact mul_le_mul (introTraceApprox_spectral_differentiable_power_le hL1
        (by simp only [r]; linarith) (hvL v hv)) (hm v) (norm_nonneg _) hLr
    · rw [hm0 v hv, mul_zero, norm_zero, indicator_of_notMem hv]
  have hF'meas : AEStronglyMeasurable (F' z₀) volume :=
    ((Measurable.ite measurableSet_Ioi (((Complex.measurable_ofReal.pow_const _).mul
      (Complex.measurable_log.comp Complex.measurable_ofReal)).mul_const _) measurable_const).mul
      hmm).aestronglyMeasurable
  have hbound : ∀ᵐ v ∂volume, ∀ z ∈ Metric.ball z₀ 1, ‖F' z v‖ ≤ bnd v := by
    refine Eventually.of_forall fun v z hz ↦ ?_
    by_cases hv : v ∈ Icc (a' - ε n) (b' + ε n)
    · simp only [bnd, indicator_of_mem hv, F']
      split_ifs with h1
      · have hp := introTraceApprox_spectral_differentiable_power_le hL1 (hball z hz) (hvL v hv)
        unfold introTracePower at hp
        rw [if_pos h1] at hp
        have hlog : ‖Complex.log (v : ℂ)‖ ≤ Real.log L := by
          rw [← Complex.ofReal_log (zero_le_one.trans h1.le), Complex.norm_real,
            Real.norm_of_nonneg (Real.log_nonneg h1.le)]
          exact Real.log_le_log (zero_lt_one.trans h1) (hvL v hv)
        rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_one, mul_one]
        exact mul_le_mul (mul_le_mul hp hlog (norm_nonneg _) hLr) (hm v) (norm_nonneg _)
          (mul_nonneg hLr hlogL)
      · rw [zero_mul, norm_zero]
        positivity
    · simp only [bnd, indicator_of_notMem hv, F', hm0 v hv, mul_zero, norm_zero, le_refl]
  have hdiff : ∀ᵐ v ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun z ↦ introTracePower z v * m v) (F' z v) z := by
    refine Eventually.of_forall fun v z _ ↦ ?_
    by_cases h1 : 1 < v
    · have hfun : (fun z ↦ introTracePower z v * m v) = fun z ↦ (v : ℂ) ^ (-z) * m v :=
        funext fun z ↦ by simp [introTracePower, h1]
      simp only [F', if_pos h1]
      rw [hfun]
      exact ((hasDerivAt_neg z).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans h1).ne'))).mul_const (m v)
    · have hc : (fun z ↦ introTracePower z v * m v) = fun _ ↦ introTracePower 0 v * m v :=
        funext fun z ↦ by simp [introTracePower, h1]
      simp only [F', if_neg h1, zero_mul]
      rw [hc]
      exact hasDerivAt_const _ _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z ↦ ((hPm z).mul hmm).aestronglyMeasurable) hFint hF'meas hbound
    (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc) hdiff).2.differentiableAt

/-- Paper: §§1.4.2–1.4.3, pp. 28–29. At a fixed cutoff the Mellin transforms of the approximants
decay like `(1 + |Im s|)⁻²` on vertical strips, uniformly for `z` in a compact set. The approximant
is the cutoff times the mollified power, a smooth function supported in a fixed compact subset
of `(1, ∞)` whose radial derivatives are bounded locally uniformly in `z`. Two integrations by
parts in the logarithmic coordinate give the bound. -/
private theorem introTraceApprox_spectral_differentiable_mellin_decay (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (K : Set ℂ) (_hK : IsCompact K) (b : ℝ) :
    ∃ C : ℝ, ∀ z ∈ K, ∀ s : ℂ, |s.re| ≤ b →
      ‖introTraceMellin approx(h, ρ, n, z) s‖ ≤ C / (1 + |s.im|) ^ 2 := by
  obtain ⟨a', b', D, ha, hab, hsupp, hk⟩ := introTraceApprox_spectral_differentiable_kernel h ρ _hA n
  have hfub := introTraceApprox_spectral_differentiable_fubini h ρ _hA n ha hab hsupp
  obtain ⟨-, -, -, ε, -, hρ⟩ := _hA
  obtain ⟨hε0, -, -, hρsub, -⟩ := hρ n
  obtain ⟨R0, hR0⟩ := _hK.isBounded.exists_norm_le
  let L : ℝ := b' + ε n + 1
  have hL1 : 1 ≤ L := by simp only [L]; linarith
  let r : ℝ := |R0|
  have hzr (z : ℂ) (hz : z ∈ K) : |z.re| ≤ r :=
    (Complex.abs_re_le_norm z).trans ((hR0 z hz).trans (le_abs_self _))
  let Cp : ℝ := 4 * (b' - a') * (max b' a'⁻¹ + 1) ^ (b + 1) * max D D
  let len : ℝ := (b' + ε n) - (a' - ε n)
  have hlen : 0 ≤ len := by simp only [len]; linarith
  have hLr : 0 ≤ 2 + L ^ r := by positivity
  refine ⟨(2 + L ^ r) * Cp * len, fun z hz s hs ↦ ?_⟩
  rw [hfub z s]
  have hQ : 0 < (1 + |s.im|) ^ 2 := by positivity
  have hmv (v : ℝ) : ‖∫ t in a'..b', (t : ℂ) ^ (s - 1) * ((h n t : ℂ) * (ρ n (t - v) : ℂ))‖ ≤
      Cp / (1 + |s.im|) ^ 2 :=
    introTraceApprox_spectral_differentiable_parts ha hab (hk v).1 (hk v).2.1 (hk v).2.2.1
      (hk v).2.2.2.1 (hk v).2.2.2.2.1 (fun t _ ↦ (hk v).2.2.2.2.2.1 t)
      (fun t _ ↦ (hk v).2.2.2.2.2.2 t) s hs
  have hCp : 0 ≤ Cp / (1 + |s.im|) ^ 2 := (norm_nonneg _).trans (hmv 0)
  have hm0 (v : ℝ) (hv : v ∉ Icc (a' - ε n) (b' + ε n)) :
      ∫ t in a'..b', (t : ℂ) ^ (s - 1) * ((h n t : ℂ) * (ρ n (t - v) : ℂ)) = 0 := by
    refine (intervalIntegral.integral_congr fun t ht ↦ ?_).trans intervalIntegral.integral_zero
    rw [Set.uIcc_of_le hab] at ht
    have : ρ n (t - v) = 0 := by
      by_contra hne
      have := hρsub (subset_tsupport _ hne)
      exact hv ⟨by linarith [this.2, ht.1], by linarith [this.1, ht.2]⟩
    simp [this]
  calc ‖∫ v, introTracePower z v *
        ∫ t in a'..b', (t : ℂ) ^ (s - 1) * ((h n t : ℂ) * (ρ n (t - v) : ℂ))‖
      ≤ ∫ v, (Icc (a' - ε n) (b' + ε n)).indicator
          (fun _ ↦ (2 + L ^ r) * (Cp / (1 + |s.im|) ^ 2)) v := by
        refine norm_integral_le_of_norm_le
          (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc)
          (Eventually.of_forall fun v ↦ ?_)
        by_cases hv : v ∈ Icc (a' - ε n) (b' + ε n)
        · rw [indicator_of_mem hv, norm_mul]
          exact mul_le_mul (introTraceApprox_spectral_differentiable_power_le hL1 (hzr z hz)
            (by simp only [L]; linarith [hv.2])) (hmv v) (norm_nonneg _) hLr
        · rw [hm0 v hv, mul_zero, norm_zero, indicator_of_notMem hv]
    _ = (2 + L ^ r) * Cp * len / (1 + |s.im|) ^ 2 := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, Measure.real,
          Real.volume_Icc, ENNReal.toReal_ofReal hlen, smul_eq_mul]
        ring

/-- Paper: §1.4.3, p. 29. Each fixed-cutoff zero sum is entire in the
test parameter.
Deviation: The sum uses full zero orders and the corrected centered window.
Passing to a holomorphic limit needs a further estimate on the zero sum. -/
theorem introTraceApprox_spectral_differentiable (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (a : ℝ) (_ha : 0 < a) :
    Differentiable ℂ (fun z ↦ introTraceSpectralSum χ approx(h, ρ, n, z) a) := by
  intro z₀
  have hU : IsOpen (Metric.ball z₀ 1) := Metric.isOpen_ball
  obtain ⟨C, hC⟩ := introTraceApprox_spectral_differentiable_mellin_decay h ρ _hA n
    (Metric.closedBall z₀ 1) (isCompact_closedBall z₀ 1) a
  have hsum := (introTraceApprox_spectral_differentiable_zeroCount χ a).mul_left (max C 0)
  have hdiff : DifferentiableOn ℂ (fun z ↦ ∑' r : windowZeros(χ, a),
      (zeroOrder(χ, r.val) : ℂ) * introTraceMellin approx(h, ρ, n, z) (r.val - 1 / 2))
      (Metric.ball z₀ 1) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun r ↦
      ((introTraceApprox_spectral_differentiable_mellin_entire h ρ _hA n _).const_mul _).differentiableOn)
      hU (fun r z hz ↦ ?_)
    have hpos : (0 : ℝ) < (zeroOrder(χ, r.val) : ℝ) := Int.cast_pos.mpr r.property.1
    have hre : |(r.val - 1 / 2).re| ≤ a := by
      simpa using r.property.2.le
    have hb := hC z (Metric.ball_subset_closedBall hz) _ hre
    have him : (r.val - 1 / 2).im = r.val.im := by simp
    rw [him] at hb
    have hd : 0 < (1 + |r.val.im|) ^ 2 := by positivity
    rw [norm_mul, Complex.norm_intCast, abs_of_pos hpos]
    calc (zeroOrder(χ, r.val) : ℝ) * ‖introTraceMellin approx(h, ρ, n, z) (r.val - 1 / 2)‖
        ≤ (zeroOrder(χ, r.val) : ℝ) * (max C 0 / (1 + |r.val.im|) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (hb.trans ?_) hpos.le
          exact div_le_div_of_nonneg_right (le_max_left _ _) hd.le
      _ = max C 0 * ((zeroOrder(χ, r.val) : ℝ) / (1 + |r.val.im|) ^ 2) := by ring
  unfold introTraceSpectralSum
  exact (hdiff z₀ (Metric.mem_ball_self one_pos)).differentiableAt
    (hU.mem_nhds (Metric.mem_ball_self one_pos))

/-- A resolvent on a bounded set separated from its pole decays
uniformly like the reciprocal of one plus the height of the pole. -/
private theorem introTrace_resolvent_inv_norm_of_separation {s z : ℂ} {δ R : ℝ}
    (hδ : 0 < δ) (hd : δ ≤ ‖z - s‖) (hR : ‖z‖ ≤ R) :
    1 / ‖z - s‖ ≤ (1 + (1 + R) / δ) / (1 + |s.im|) := by
  have hheight : |s.im| ≤ R + ‖z - s‖ := calc
    |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    _ = ‖z - (z - s)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖z‖ + ‖z - s‖ := norm_sub_le _ _
    _ ≤ R + ‖z - s‖ := by linarith
  have hC : 0 ≤ (1 + R) / δ := div_nonneg (by linarith [norm_nonneg z]) hδ.le
  have hscale := mul_le_mul_of_nonneg_left hd hC
  rw [div_mul_cancel₀ _ hδ.ne'] at hscale
  apply (div_le_div_iff₀ (hδ.trans_le hd) (by positivity)).2
  nlinarith

/-- A resolvent on a bounded set separated horizontally from its pole decays
uniformly like the reciprocal of one plus the height of the pole. -/
private theorem introTrace_spectral_referenceSub_inv_bound {s z : ℂ} {δ R : ℝ}
    (hδ : 0 < δ) (hsep : δ ≤ z.re - s.re) (hR : ‖z‖ ≤ R) :
    1 / ‖z - s‖ ≤ (1 + (1 + R) / δ) / (1 + |s.im|) := by
  exact introTrace_resolvent_inv_norm_of_separation hδ
    (hsep.trans ((le_abs_self (z - s).re).trans (Complex.abs_re_le_norm _))) hR

/-- The difference of the resolvents at two parameters in a compact set is
bounded by a constant times the reciprocal square of the imaginary height weight. -/
private theorem introTrace_spectral_referenceSub_bound {a : ℝ}
    (K : Set ℂ) (hKsub : K ⊆ right(a)) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ z ∈ K, ∀ z₀ ∈ K, ∀ s : ℂ, s.re ≤ a →
      ‖1 / (z - s) - 1 / (z₀ - s)‖ ≤ C / (1 + |s.im|) ^ 2 := by
  rcases K.eq_empty_or_nonempty with rfl | hneK
  · exact ⟨0, by simp⟩
  obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hneK Complex.continuous_re.continuousOn
  obtain ⟨v, _, hmax⟩ := hK.exists_isMaxOn hneK continuous_norm.continuousOn
  let δ := w.re - a
  let R := ‖v‖
  let B := 1 + (1 + R) / δ
  have hδ : 0 < δ := sub_pos.mpr (hKsub hw)
  have hR (z : ℂ) (hz : z ∈ K) : ‖z‖ ≤ R := isMaxOn_iff.mp hmax z hz
  have hB : 0 ≤ B := by dsimp [B, R]; positivity
  refine ⟨(2 * R) * B ^ 2, fun z hz z₀ hz₀ s hs ↦ ?_⟩
  have hsep (x : ℂ) (hx : x ∈ K) : δ ≤ x.re - s.re :=
    sub_le_sub (isMinOn_iff.mp hmin x hx) hs
  have hinv (x : ℂ) (hx : x ∈ K) : 1 / ‖x - s‖ ≤ B / (1 + |s.im|) :=
    introTrace_spectral_referenceSub_inv_bound hδ (hsep x hx) (hR x hx)
  have hne (x : ℂ) (hx : x ∈ K) : x - s ≠ 0 :=
    sub_ne_zero.mpr fun he ↦ (lt_of_lt_of_le hδ (hsep x hx)).ne' (by rw [he, sub_self])
  have hid : 1 / (z - s) - 1 / (z₀ - s) =
      (z₀ - z) * (1 / (z - s)) * (1 / (z₀ - s)) := by
    field_simp [hne z hz, hne z₀ hz₀]
    ring
  have hnum : ‖z₀ - z‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith [hR z hz, hR z₀ hz₀])
  rw [hid, norm_mul, norm_mul, norm_div, norm_div, norm_one]
  calc
    _ ≤ (2 * R) * (B / (1 + |s.im|)) * (B / (1 + |s.im|)) := by
      have htwo : 0 ≤ 2 * R := by dsimp [R]; positivity
      exact mul_le_mul (mul_le_mul hnum (hinv z hz) (by positivity) htwo) (hinv z₀ hz₀)
        (by positivity) (mul_nonneg htwo (by positivity))
    _ = _ := by rw [pow_two, pow_two, mul_div_mul_comm]; ring

/-- Paper: §1.4.3, p. 29. Subtracting the spectral Mellin moment at a holomorphically
varying reference parameter gives a normally convergent resolvent series on the open
half-plane to the right of the centered zero window. For each finite set of
zeros the mollified Mellin differences converge locally uniformly to the
corresponding finite sum, and these sums in turn converge locally uniformly
to a holomorphic function. The reference can be constant or can be `z+2`,
as in the rational real-place calculation.
Deviation: The two limits are taken in the displayed order. This regularizes
the limiting Mellin kernels at a reference parameter, as called for in F255. -/
theorem introTrace_spectral_referenceSub (χ : U𝔽) (a : ℝ) (w : ℂ → ℂ)
    (hw : MapsTo w right(a) right(a)) (hdw : DifferentiableOn ℂ w right(a)) :
    let s (r : windowZeros(χ, a)) := r.val - 1 / 2
    let term (r : windowZeros(χ, a)) (z : ℂ) := (zeroOrder(χ, r.val) : ℂ) *
      (1 / (z - s r) - 1 / (w z - s r))
    (∀ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ → ∀ T : Finset (windowZeros(χ, a)),
      TendstoLocallyUniformlyOn (fun n z ↦ ∑ r ∈ T, (zeroOrder(χ, r.val) : ℂ) *
        (introTraceMellin approx(h, ρ, n, z) (s r) - introTraceMellin approx(h, ρ, n, (w z)) (s r)))
        (fun z ↦ ∑ r ∈ T, term r z) atTop right(a)) ∧
    (∀ K ⊆ right(a), IsCompact K → ∃ u : windowZeros(χ, a) → ℝ,
      Summable u ∧ ∀ r z, z ∈ K → ‖term r z‖ ≤ u r) ∧
    TendstoLocallyUniformlyOn (fun (T : Finset (windowZeros(χ, a))) z ↦ ∑ r ∈ T, term r z)
      (fun z ↦ ∑' r, term r z) atTop right(a) ∧
    AnalyticOnNhd ℂ (fun z ↦ ∑' r, term r z) right(a) := by
  classical
  intro s term
  have hs (r : windowZeros(χ, a)) : (s r).re < a := by
    simpa [s] using (abs_lt.mp r.property.2).2
  have hopen : IsOpen right(a) := isOpen_Ioi.preimage Complex.continuous_re
  refine ⟨?_, ?_⟩
  · intro h ρ hA T
    have hterm (r : windowZeros(χ, a)) :
        TendstoLocallyUniformlyOn (fun n z ↦ (zeroOrder(χ, r.val) : ℂ) *
          (introTraceMellin approx(h, ρ, n, z) (s r) - introTraceMellin approx(h, ρ, n, (w z)) (s r)))
        (term r) atTop right(a) := by
      have hlim := (introTraceApprox_mellin_tendsto h ρ hA (s r)).mono
        (show right(a) ⊆ right((s r).re) from fun x hx ↦ (hs r).trans hx)
      have href := hlim.comp w hw hdw.continuousOn
      have hscaled := (uniformContinuous_const_smul (X := ℂ) (zeroOrder(χ, r.val) : ℂ)).comp_tendstoLocallyUniformlyOn
        (hlim.sub href)
      refine hscaled.congr_right fun z hz ↦ ?_
      change (zeroOrder(χ, r.val) : ℂ) * (introTraceMellin (introTracePower z) (s r) -
        introTraceMellin (introTracePower (w z)) (s r)) = term r z
      rw [(introTracePower_mellin z (s r) ((hs r).trans hz)).2,
        (introTracePower_mellin (w z) (s r) ((hs r).trans (hw hz))).2]
    induction T using Finset.induction_on with
    | empty =>
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0)
        ).tendstoUniformlyOn_const (s := right(a))).tendstoLocallyUniformlyOn
    | insert r T hr ih =>
      simpa only [Finset.sum_insert hr, Pi.add_def] using (hterm r).add ih
  · have hmajor (K : Set ℂ) (hsub : K ⊆ right(a)) (hK : IsCompact K) :
        ∃ u : windowZeros(χ, a) → ℝ, Summable u ∧ ∀ r z, z ∈ K → ‖term r z‖ ≤ u r := by
      have hKw : IsCompact (K ∪ w '' K) := hK.union (hK.image_of_continuousOn (hdw.continuousOn.mono hsub))
      have hsubw : K ∪ w '' K ⊆ right(a) := union_subset hsub (fun _ ⟨x, hx, he⟩ ↦ he ▸ hw (hsub hx))
      obtain ⟨C, hC⟩ := introTrace_spectral_referenceSub_bound (K ∪ w '' K) hsubw hKw
      refine ⟨_, (introTraceApprox_spectral_differentiable_zeroCount χ a).mul_left C, ?_⟩
      intro r z hz
      have hn : 0 < (zeroOrder(χ, r.val) : ℝ) := Int.cast_pos.mpr r.property.1
      have hb := hC z (Or.inl hz) (w z) (Or.inr (mem_image_of_mem _ hz)) (s r) (hs r).le
      have him : (s r).im = r.val.im := by simp [s]
      rw [him] at hb
      change ‖(zeroOrder(χ, r.val) : ℂ) * _‖ ≤ _
      rw [norm_mul, Complex.norm_intCast, abs_of_pos hn]
      exact (mul_le_mul_of_nonneg_left hb hn.le).trans_eq (by ring)
    have hconv : TendstoLocallyUniformlyOn
        (fun (T : Finset (windowZeros(χ, a))) z ↦ ∑ r ∈ T, term r z)
        (fun z ↦ ∑' r, term r z) atTop right(a) := by
      apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).2
      intro K hsub hK
      obtain ⟨u, hu, hbound⟩ := hmajor K hsub hK
      exact tendstoUniformlyOn_tsum hu hbound
    refine ⟨hmajor, hconv, (hconv.differentiableOn (.of_forall fun T ↦ ?_) hopen).analyticOnNhd hopen⟩
    apply DifferentiableOn.fun_sum
    intro r _
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.sub
    · refine (differentiableOn_const _).div (differentiableOn_id.sub (differentiableOn_const _)) ?_
      intro z hz
      exact sub_ne_zero.mpr fun eq ↦ ((hs r).trans hz).ne (congrArg Complex.re eq.symm)
    · refine (differentiableOn_const _).div (hdw.sub (differentiableOn_const _)) ?_
      intro z hz
      exact sub_ne_zero.mpr fun eq ↦ ((hs r).trans (hw hz)).ne (congrArg Complex.re eq.symm)

/-- A cutoff-uniform inverse-square Mellin estimate exchanges the cutoff limit with the
full spectral sum on the right of a window. -/
private theorem introTrace_spectral_referenceSub_of_bound (χ : U𝔽) (a : ℝ)
    (w : ℂ → ℂ) (hw : MapsTo w right(a) right(a)) (hdw : DifferentiableOn ℂ w right(a))
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (hB : ∀ K ⊆ right(a), IsCompact K → ∃ C : ℝ, ∀ᶠ n in atTop, ∀ r : windowZeros(χ, a),
      ∀ z ∈ K, ‖introTraceMellin approx(h, ρ, n, z) (r.val - 1 / 2) -
        introTraceMellin approx(h, ρ, n, (w z)) (r.val - 1 / 2)‖ ≤ C / (1 + |r.val.im|) ^ 2) :
    TendstoLocallyUniformlyOn (fun n z ↦ introTraceSpectralSum χ approx(h, ρ, n, z) a -
      introTraceSpectralSum χ approx(h, ρ, n, (w z)) a)
      (fun z ↦ ∑' r : windowZeros(χ, a), (zeroOrder(χ, r.val) : ℂ) *
        (1 / (z - (r.val - 1 / 2)) - 1 / (w z - (r.val - 1 / 2)))) atTop right(a) := by
  classical
  let s (r : windowZeros(χ, a)) : ℂ := r.val - 1 / 2
  let m (r : windowZeros(χ, a)) : ℂ := zeroOrder(χ, r.val)
  let v (n : ℕ) (z : ℂ) (r : windowZeros(χ, a)) := m r *
    (introTraceMellin approx(h, ρ, n, z) (s r) - introTraceMellin approx(h, ρ, n, (w z)) (s r))
  let g (z : ℂ) (r : windowZeros(χ, a)) := m r * (1 / (z - s r) - 1 / (w z - s r))
  obtain ⟨hfin, _, _, hhol⟩ := introTrace_spectral_referenceSub χ a w hw hdw
  have hopen : IsOpen right(a) := isOpen_Ioi.preimage Complex.continuous_re
  apply hopen.tendstoLocallyUniformlyOn_iff_forall_tendsto.2
  intro z hz
  let l := (atTop : Filter ℕ) ×ˢ 𝓝 z
  have hcont (r : windowZeros(χ, a)) : ContinuousAt (fun x ↦ g x r) z := by
    have hr : (s r).re < a := by simpa [s] using (abs_lt.mp r.property.2).2
    have h₁ : z - s r ≠ 0 := sub_ne_zero.mpr fun e ↦ (hr.trans hz).ne (congrArg Complex.re e.symm)
    have h₂ : w z - s r ≠ 0 := sub_ne_zero.mpr fun e ↦ (hr.trans (hw hz)).ne (congrArg Complex.re e.symm)
    have wh := hdw.continuousOn.continuousAt (hopen.mem_nhds hz)
    exact continuousAt_const.mul ((continuousAt_const.div (continuousAt_id.sub_const _) h₁).sub
      (continuousAt_const.div (wh.sub_const _) h₂))
  have hl (r : windowZeros(χ, a)) : Tendsto (fun p : ℕ × ℂ ↦ v p.1 p.2 r) l (𝓝 (g z r)) := by
    have hv : TendstoLocallyUniformlyOn (fun n x ↦ v n x r) (fun x ↦ g x r) atTop right(a) := by
      simpa only [Finset.sum_singleton] using hfin h ρ hA {r}
    exact ((hcont r).tendsto.comp tendsto_snd).congr_uniformity
      (hopen.tendstoLocallyUniformlyOn_iff_forall_tendsto.1 hv z hz)
  obtain ⟨ε, hε, hK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hopen.mem_nhds hz)
  obtain ⟨C, hC⟩ := hB _ hK (isCompact_closedBall z ε)
  have hbd := (introTraceApprox_spectral_differentiable_zeroCount χ a).mul_left C
  have hsum : Tendsto (fun p : ℕ × ℂ ↦ ∑' r, v p.1 p.2 r) l (𝓝 (∑' r, g z r)) := by
    apply tendsto_tsum_of_dominated_convergence hbd hl
    filter_upwards [tendsto_fst.eventually hC, tendsto_snd.eventually (Metric.closedBall_mem_nhds z hε)]
      with p hn hp r
    have hpos : 0 ≤ (zeroOrder(χ, r.val) : ℝ) := (Int.cast_pos.mpr r.property.1).le
    dsimp only [v, m]
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hpos]
    exact (mul_le_mul_of_nonneg_left (hn r _ hp) hpos).trans_eq (by ring)
  have hsum1 (n : ℕ) (y : ℂ) : Summable (fun r : windowZeros(χ, a) ↦ m r *
      introTraceMellin approx(h, ρ, n, y) (s r)) := by
    obtain ⟨D, hD⟩ := introTraceApprox_spectral_differentiable_mellin_decay h ρ hA n
      {y} (isCompact_singleton) a
    apply ((introTraceApprox_spectral_differentiable_zeroCount χ a).mul_left D).of_norm_bounded
    intro r
    have hp : 0 ≤ (zeroOrder(χ, r.val) : ℝ) := (Int.cast_pos.mpr r.property.1).le
    have hb := hD y (mem_singleton y) (s r) (by simpa [s] using r.property.2.le)
    have him : (s r).im = r.val.im := by simp [s]
    rw [him] at hb
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hp]
    exact (mul_le_mul_of_nonneg_left hb hp).trans_eq (by ring)
  have he (n : ℕ) (z : ℂ) : (∑' r, v n z r) = introTraceSpectralSum χ approx(h, ρ, n, z) a -
      introTraceSpectralSum χ approx(h, ρ, n, (w z)) a := by
    simp only [v, mul_sub, m, s, introTraceSpectralSum]
    exact (hsum1 n z).tsum_sub (hsum1 n (w z))
  have hloc := hhol.continuousOn.continuousAt (hopen.mem_nhds hz)
  exact ((hloc.tendsto.comp tendsto_snd).prodMk_nhds (hsum.congr fun p ↦ he p.1 p.2)).mono_right
    (nhds_le_uniformity _)

/-- The dilated cutoff is supported between the lower mesh and twice the radius. -/
private theorem introTraceApprox_dilated_cutoff_support {R : ℝ} (hR : 0 < R) :
    tsupport (fun t : ℝ ↦ Real.smoothTransition (R * (t - 1) - 1) *
      Real.smoothTransition (2 - t / R)) ⊆ Icc (1 + 1 / R) (2 * R) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  obtain ⟨hl, hr⟩ := mul_ne_zero_iff.mp ht
  have hleft := lt_of_not_ge (hl ∘ Real.smoothTransition.zero_of_nonpos)
  have hright := lt_of_not_ge (hr ∘ Real.smoothTransition.zero_of_nonpos)
  have hp := (div_lt_iff₀ hR).2 (show 1 < (t - 1) * R by linarith)
  exact ⟨by linarith, ((div_lt_iff₀ hR).mp (show t / R < 2 by linarith)).le⟩

/-- For these cutoffs the lower transition occupies one
mesh interval and the upper transition has width comparable to its radius. -/
private theorem introTraceApprox_exists_dilated :
    let hcut (n : ℕ) : ℝ := (n : ℝ) + 4
    let h (n : ℕ) (t : ℝ) := Real.smoothTransition (hcut n * (t - 1) - 1) *
      Real.smoothTransition (2 - t / hcut n)
    ∃ ρ : ℕ → ℝ → ℝ, IsIntroTraceApproximation h ρ ∧
      ∀ n u, ρ n u ≠ 0 → |u| ≤ 1 / (2 * hcut n) := by
  intro hcut h
  have hcut_spec (n : ℕ) : hcut n = (n : ℝ) + 4 := rfl
  let d (n : ℕ) := 1 / hcut n
  let ε (n : ℕ) := d n / 2
  have hR (n : ℕ) : 0 < hcut n := by rw [hcut_spec]; positivity
  have hd (n : ℕ) : 0 < d n := one_div_pos.mpr (hR n)
  have hε (n : ℕ) : 0 < ε n := half_pos (hd n)
  let b (n : ℕ) : ContDiffBump (0 : ℝ) :=
    ⟨ε n / 2, ε n, half_pos (hε n), half_lt_self (hε n)⟩
  have hs (n : ℕ) : tsupport (h n) ⊆ Icc (1 + d n) (2 * hcut n) :=
    introTraceApprox_dilated_cutoff_support (hR n)
  have hg : Tendsto hcut atTop atTop := by
    exact tendsto_atTop_mono (fun n ↦ show (n : ℝ) ≤ hcut n by rw [hcut_spec]; linarith) tendsto_natCast_atTop_atTop
  have hbd (n : ℕ) : tsupport ((b n).normed volume) ⊆ Icc (-ε n) (ε n) := by
    rw [(b n).tsupport_normed_eq, Real.closedBall_eq_Icc]
    simp [b]
  refine ⟨fun n ↦ (b n).normed volume, ⟨?_, ?_, ?_, ε, ?_, ?_⟩, ?_⟩
  · intro n
    refine ⟨(Real.smoothTransition.contDiff.comp (by fun_prop)).mul
      (Real.smoothTransition.contDiff.comp (by fun_prop)), isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hs n),
      fun t ht ↦ (lt_add_of_pos_right 1 (hd n)).trans_le ((hs n ht).1), fun t ↦ ?_⟩
    exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
      (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans
        (Real.smoothTransition.le_one _)⟩
  · intro m n hmn t
    have hmn' : hcut m ≤ hcut n := by simp only [hcut_spec, add_le_add_iff_right]; exact_mod_cast hmn
    by_cases ht : 1 ≤ t
    · exact mul_le_mul (Real.smoothTransition.monotone (sub_le_sub_right
        (mul_le_mul_of_nonneg_right hmn' (sub_nonneg.mpr ht)) _))
        (Real.smoothTransition.monotone (sub_le_sub_left (div_le_div_of_nonneg_left
          (zero_le_one.trans ht) (hR m) hmn') _))
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    · have hz (j : ℕ) : hcut j * (t - 1) - 1 ≤ 0 := by
        linarith [mul_nonpos_of_nonneg_of_nonpos (hR j).le (sub_nonpos.mpr (le_of_not_ge ht))]
      simp [h, Real.smoothTransition.zero_of_nonpos (hz m), Real.smoothTransition.zero_of_nonpos (hz n)]
  · intro t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [hg.eventually_ge_atTop (2 / (t - 1)), hg.eventually_ge_atTop t] with n hl hr
    have hleft : 1 ≤ hcut n * (t - 1) - 1 := by linarith [(div_le_iff₀ (sub_pos.mpr ht)).mp hl]
    have hright : 1 ≤ 2 - t / hcut n := by linarith [(div_le_one (hR n)).2 hr]
    simp [h, Real.smoothTransition.one_of_one_le hleft, Real.smoothTransition.one_of_one_le hright]
  · simpa [ε, d, one_div] using (tendsto_inv_atTop_zero.comp hg).div_const 2
  · intro n
    exact ⟨hε n, (b n).contDiff_normed, (b n).nonneg_normed, hbd n, (b n).integral_normed⟩
  · intro n u hu
    have hle := abs_le.mpr (hbd n (subset_tsupport _ hu))
    exact hle.trans_eq (by dsimp [ε, d]; rw [div_div, mul_comm])

/-- Translation differentiates the cutoff-free complex power through order two
on the interior of the support. -/
private theorem introTraceApprox_translated_power_jet (w : ℂ) {t u : ℝ} (ht : 1 < t - u) :
    let f := fun y : ℝ ↦ introTracePower w (y - u)
    let v := ((t - u : ℝ) : ℂ)
    HasDerivAt f (-w * v ^ (-w - 1)) t ∧
      HasDerivAt (deriv f) ((-w) * (-w - 1) * v ^ (-w - 2)) t := by
  intro f v
  have hshift (q : ℂ) (y : ℝ) (hy : 1 < y - u) :
      HasDerivAt (fun x : ℝ ↦ ((x - u : ℝ) : ℂ) ^ q) (q * ((y - u : ℝ) : ℂ) ^ (q - 1)) y := by
    have hu0 := (zero_lt_one.trans hy).ne'
    have hd := (differentiableAt_id.ofReal_cpow_const q hu0).hasDerivAt
    have he := Complex.deriv_ofReal_cpow_const q hu0
    simp only [id_eq] at hd
    rw [he] at hd
    have hi : HasDerivAt (fun x : ℝ ↦ x - u) 1 y := (hasDerivAt_id y).sub_const u
    simpa only [Function.comp_def, one_smul] using hd.scomp y hi
  have hf (y : ℝ) (hy : 1 < y - u) :
      HasDerivAt f (-w * ((y - u : ℝ) : ℂ) ^ (-w - 1)) y := by
    apply (hshift (-w) y hy).congr_of_eventuallyEq
    filter_upwards [(continuous_id.sub continuous_const).continuousAt.tendsto.eventually (lt_mem_nhds hy)]
      with x hx
    change 1 < x - u at hx
    simp only [f, introTracePower, hx, ite_true]
  refine ⟨hf t ht, ?_⟩
  have h := (hshift (-w - 1) t ht).const_mul (-w)
  rw [show -w - 1 - 1 = -w - 2 by ring, ← mul_assoc] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(continuous_id.sub continuous_const).continuousAt.tendsto.eventually (lt_mem_nhds ht)]
    with x hx
  exact (hf x hx).deriv

/-- The derivative of the inverse power on `[1,x]` is bounded by the norm of its exponent. -/
private theorem introTraceApprox_power_sub_one {q : ℂ} (hq : 0 ≤ q.re) {x : ℝ} (hx : 1 ≤ x) :
    ‖(x : ℂ) ^ (-q) - 1‖ ≤ ‖q‖ * (x - 1) := by
  let f (y : ℝ) := (y : ℂ) ^ (-q)
  let d (y : ℝ) := -q * (y : ℂ) ^ (-q - 1)
  have hd (y : ℝ) (hy : 1 ≤ y) : HasDerivAt f (d y) y := by
    have hy0 := (zero_lt_one.trans_le hy).ne'
    have h := (differentiableAt_id.ofReal_cpow_const (-q) hy0).hasDerivAt
    simpa only [id_eq, Complex.deriv_ofReal_cpow_const (-q) hy0, f, d] using h
  have hb (y : ℝ) (hy : 1 ≤ y) : ‖d y‖ ≤ ‖q‖ := by
    dsimp only [d]
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hy)]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hy (by simp; linarith))
  simpa only [f, Complex.ofReal_one, Complex.one_cpow] using
    norm_image_sub_le_of_norm_deriv_le_segment' (a := 1) (b := x) (f := f) (f' := d)
      (fun y hy ↦ (hd y hy.1).hasDerivWithinAt) (fun y hy ↦ hb y hy.1) x ⟨hx, le_rfl⟩

/-- On the lower transition both powers agree at one before translation. For `t ≥ 2`,
the triangle inequality and the ordinary inverse-power estimate suffice. -/
private theorem introTraceApprox_translated_reference_lower {m Z : ℝ} (hm : 0 ≤ m) (hZ : 0 ≤ Z) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (z w : ℂ) (t u : ℝ), m ≤ z.re → m ≤ w.re → ‖z‖ ≤ Z → ‖w‖ ≤ Z →
      1 < t → |u| ≤ 1 → |u| ≤ t - 1 → 1 < t - u →
      ‖introTracePower z (t - u) - introTracePower w (t - u)‖ ≤ (D * t ^ (-m)) * ((t - 1) / t) := by
  let b := (1 / 2 : ℝ) ^ (-m) + 2 ^ (-m)
  let D := max (8 * Z * 2 ^ m) (4 * b)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hD : 0 ≤ D := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hb).trans (le_max_right _ _)
  refine ⟨D, hD, ?_⟩
  intro z w t u hz hw hzn hwn ht hu hsep hx
  have ht0 : 0 < t := zero_lt_one.trans ht
  by_cases ht2 : t ≤ 2
  · have hz' := introTraceApprox_power_sub_one (hm.trans hz) hx.le
    have hw' := introTraceApprox_power_sub_one (hm.trans hw) hx.le
    have hsub : t - u - 1 ≤ 2 * (t - 1) := by linarith [(abs_le.mp hsep).1]
    have hsmall : ‖introTracePower z (t - u) - introTracePower w (t - u)‖ ≤ 4 * Z * (t - 1) := by
      simp only [introTracePower, hx, ite_true]
      calc
        _ ≤ ‖((t - u : ℝ) : ℂ) ^ (-z) - 1‖ + ‖((t - u : ℝ) : ℂ) ^ (-w) - 1‖ := by
          simpa only [norm_sub_rev (1 : ℂ) _] using
            norm_sub_le_norm_sub_add_norm_sub (((t - u : ℝ) : ℂ) ^ (-z)) 1 (((t - u : ℝ) : ℂ) ^ (-w))
        _ ≤ Z * (2 * (t - 1)) + Z * (2 * (t - 1)) := by
          exact add_le_add (hz'.trans (mul_le_mul hzn hsub (by linarith) hZ))
            (hw'.trans (mul_le_mul hwn hsub (by linarith) hZ))
        _ = _ := by ring
    have htp : t ^ m ≤ 2 ^ m := Real.rpow_le_rpow ht0.le ht2 hm
    have hconst : (4 * Z * t ^ m) * t ≤ D := (calc
      _ ≤ (4 * Z * 2 ^ m) * 2 := by gcongr
      _ = 8 * Z * 2 ^ m := by ring).trans (le_max_left _ _)
    refine hsmall.trans ?_
    calc
      _ = (((4 * Z * t ^ m) * t) * t ^ (-m)) * ((t - 1) / t) := by
        rw [Real.rpow_neg ht0.le]
        field_simp
      _ ≤ _ := by gcongr
  · have hpow (q : ℂ) (hq : m ≤ q.re) : ‖introTracePower q (t - u)‖ ≤ b * t ^ (-m) :=
      introTraceApprox_mellin_tendsto_power_bound ht (by simpa using hu) hq
    have hlarge := (norm_sub_le (introTracePower z (t - u)) (introTracePower w (t - u))).trans
      (add_le_add (hpow z hz) (hpow w hw))
    have hhalf : (1 / 2 : ℝ) ≤ (t - 1) / t := (le_div_iff₀ ht0).2 (by linarith)
    calc
      _ ≤ b * t ^ (-m) + b * t ^ (-m) := hlarge
      _ = ((4 * b) * t ^ (-m)) * (1 / 2) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- A difference of translated powers vanishes to first order at the lower endpoint.
Its first two radial derivatives have uniform power decay for bounded parameters. -/
private theorem introTraceApprox_translated_reference_jet_bound (m Z : ℝ) (hm : 0 ≤ m) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z w : ℂ) (t u : ℝ), m ≤ z.re → m ≤ w.re → ‖z‖ ≤ Z → ‖w‖ ≤ Z → 1 < t →
      |u| ≤ 1 → |u| ≤ t - 1 → 1 < t - u →
      let f := fun y : ℝ ↦ introTracePower z (y - u) - introTracePower w (y - u)
      ‖f t‖ ≤ (C * t ^ (-m)) * ((t - 1) / t) ∧
      ‖deriv f t‖ ≤ C * t ^ (-m - 1) ∧ ‖deriv (deriv f) t‖ ≤ C * t ^ (-m - 2) := by
  obtain ⟨D, hD, hlow⟩ := introTraceApprox_translated_reference_lower hm hZ
  let B (j : ℝ) := (1 / 2 : ℝ) ^ (-(m + j)) + 2 ^ (-(m + j))
  let A := Z + 1
  let C := max D (max (2 * A * B 1) (2 * A ^ 2 * B 2))
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hC : 0 ≤ C := hD.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro z w t u hz hw hnorm hwn ht hu hmatch hx f
  let v := ((t - u : ℝ) : ℂ)
  have hpow (q : ℂ) (j : ℝ) (hq : m + j ≤ q.re) :
      ‖v ^ (-q)‖ ≤ B j * t ^ (-(m + j)) := by
    simpa only [v, introTracePower, hx, ite_true, B] using
      introTraceApprox_mellin_tendsto_power_bound (z := q) ht (by simpa using hu : |(t - u) - t| ≤ 1) hq
  have hjet (w : ℂ) := introTraceApprox_translated_power_jet w hx
  let p := fun w : ℂ ↦ -w * v ^ (-w - 1)
  let q := fun w : ℂ ↦ (-w) * (-w - 1) * v ^ (-w - 2)
  have hd : deriv f t = p z - p w := ((hjet z).1.sub (hjet w).1).deriv
  have hdd : deriv (deriv f) t = q z - q w := by
    apply HasDerivAt.deriv
    apply ((hjet z).2.sub (hjet w).2).congr_of_eventuallyEq
    filter_upwards [(continuous_id.sub continuous_const).continuousAt.tendsto.eventually (lt_mem_nhds hx)]
      with x hxy
    change 1 < x - u at hxy
    exact deriv_sub ((introTraceApprox_translated_power_jet z hxy).1.differentiableAt)
      ((introTraceApprox_translated_power_jet w hxy).1.differentiableAt)
  have hcoeff (w : ℂ) (hw : ‖w‖ ≤ Z) :
      ‖-w‖ ≤ A ∧ ‖-w - 1‖ ≤ A := by
    rw [norm_neg]; constructor
    · dsimp [A]; linarith
    · exact (norm_sub_le _ _).trans (by simp [A]; linarith)
  have hderivs (w : ℂ) (hw : ‖w‖ ≤ Z) (hw' : m ≤ w.re) :
      ‖p w‖ ≤ A * (B 1 * t ^ (-m - 1)) ∧ ‖q w‖ ≤ A ^ 2 * (B 2 * t ^ (-m - 2)) := by
    obtain ⟨h1,h2⟩ := hcoeff w hw
    have hp1 := hpow (w + 1) 1 (by simpa using hw')
    have hp2 := hpow (w + 2) 2 (by simpa using hw')
    simp only [show -(w + 1) = -w - 1 by ring, show -(w + 2) = -w - 2 by ring,
      show -(m + 1) = -m - 1 by ring, show -(m + 2) = -m - 2 by ring] at hp1 hp2
    constructor
    · exact (norm_mul _ _).le.trans (mul_le_mul h1 hp1 (norm_nonneg _) hA)
    · simp only [q, norm_mul]
      apply mul_le_mul _ hp2 (norm_nonneg _) (sq_nonneg _)
      simpa [sq] using mul_le_mul h1 h2 (norm_nonneg _) hA
  obtain ⟨hp1,hq1⟩ := hderivs z hnorm hz
  obtain ⟨hp2,hq2⟩ := hderivs w hwn hw
  refine ⟨?_, ?_, ?_⟩
  · refine (hlow z w t u hz hw hnorm hwn ht hu hmatch hx).trans ?_
    have hDC : D ≤ C := le_max_left _ _
    gcongr
  · rw [hd]
    refine (norm_sub_le _ _).trans ((add_le_add hp1 hp2).trans ?_)
    have h1 : 2 * A * B 1 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
    calc _ = (2 * A * B 1) * t ^ (-m - 1) := by ring
      _ ≤ _ := by gcongr
  · rw [hdd]
    refine (norm_sub_le _ _).trans ((add_le_add hq1 hq2).trans ?_)
    have h2 : 2 * A ^ 2 * B 2 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
    calc _ = (2 * A ^ 2 * B 2) * t ^ (-m - 2) := by ring
      _ ≤ _ := by gcongr

/-- The affine transition has derivative bounds with precisely one or two powers
of its scale. The constants are global for all the affine translates. -/
private theorem introTraceApprox_affine_transition_jet :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ α b t : ℝ,
      let c := fun x : ℝ ↦ (Real.smoothTransition (α * x + b) : ℂ)
      ‖c t‖ ≤ 1 ∧ ‖deriv c t‖ ≤ D*|α| ∧ ‖deriv (deriv c) t‖ ≤ D*|α|^2 := by
  obtain ⟨D1,h1⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  obtain ⟨D2,h2⟩ := Real.smoothTransition.exists_forall_norm_deriv_deriv_le
  let D := max 1 (max D1 D2)
  have hD1 : D1 ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hD2 : D2 ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨D, le_max_left _ _, ?_⟩
  intro α b t c
  let ψ := Real.smoothTransition
  have hlin (t : ℝ) : HasDerivAt (fun x : ℝ ↦ α * x + b) α t := by
    simpa using (((hasDerivAt_id t).const_mul α).add_const b)
  have hd (x : ℝ) : HasDerivAt c ((deriv ψ (α * x + b) * α : ℝ) : ℂ) x := by
    have hψ := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) (α * x + b)).hasDerivAt
    simpa only [Function.comp_def, c, ψ] using (hψ.comp x (hlin x)).ofReal_comp
  have he : deriv c = fun x ↦ ((deriv ψ (α * x + b) * α : ℝ) : ℂ) := funext fun x ↦ (hd x).deriv
  have hdd := (((Real.smoothTransition.differentiable_deriv (α * t + b)).hasDerivAt.comp t (hlin t)).mul_const α).ofReal_comp
  simp only [Function.comp_def] at hdd
  have hu : ‖c t‖ ≤ 1 := by simpa only [c, Complex.norm_real, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)] using Real.smoothTransition.le_one (α * t + b)
  refine ⟨hu, ?_, ?_⟩
  · rw [he, Complex.norm_real, norm_mul, Real.norm_eq_abs α]
    exact mul_le_mul_of_nonneg_right ((h1 _).trans hD1) (abs_nonneg _)
  · dsimp only [ψ] at he
    rw [he, hdd.deriv, Complex.norm_real, norm_mul, norm_mul, Real.norm_eq_abs α]
    simpa [sq, mul_assoc] using mul_le_mul_of_nonneg_right
      ((h2 _).trans hD2) (mul_nonneg (abs_nonneg α) (abs_nonneg α))

/-- Away from the lower transition the dilated cutoff agrees locally with the upper
transition. The two transitions are disjoint for `R ≥ 4`. -/
private theorem introTraceApprox_dilated_cutoff_jet :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ R t : ℝ, 4 ≤ R →
      let c := fun x : ℝ ↦ ((Real.smoothTransition (R * (x - 1) - 1) * Real.smoothTransition (2 - x / R) : ℝ) : ℂ)
      ‖c t‖ ≤ 1 ∧
      (t ≤ 1 + 2 / R → ‖deriv c t‖ ≤ D * R ∧ ‖deriv (deriv c) t‖ ≤ D * R ^ 2) ∧
      (1 + 2 / R < t → ‖deriv c t‖ ≤ D / R ∧ ‖deriv (deriv c) t‖ ≤ D / R ^ 2) := by
  obtain ⟨D, hD, hjet⟩ := introTraceApprox_affine_transition_jet
  refine ⟨D, hD, ?_⟩
  intro R t hR c
  have hp : 0 < R := by linarith
  have hc : ‖c t‖ ≤ 1 := by
    rw [Complex.norm_real]
    exact (abs_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))).le.trans
      ((mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans
        (Real.smoothTransition.le_one _))
  refine ⟨hc, ?_, ?_⟩
  · intro ht
    have htwo : 2 / R ≤ 1 := (div_le_one hp).2 (by linarith)
    have he : c =ᶠ[𝓝 t] fun x : ℝ ↦ (Real.smoothTransition (R * x + (-R - 1)) : ℂ) := by
      filter_upwards [eventually_lt_nhds (show t < R by linarith)] with x hx
      simp [c, Real.smoothTransition.one_of_one_le (show 1 ≤ 2 - x / R by
        linarith [(div_le_one hp).2 hx.le]), show R * (x - 1) - 1 = R * x + (-R - 1) by ring]
    simpa only [he.deriv_eq, he.deriv.deriv_eq, abs_of_pos hp] using (hjet R (-R - 1) t).2
  · intro ht
    have he : c =ᶠ[𝓝 t] fun x : ℝ ↦ (Real.smoothTransition ((-R⁻¹) * x + 2) : ℂ) := by
      filter_upwards [eventually_gt_nhds ht] with x hx
      have hmul := (div_lt_iff₀ hp).mp (show 2 / R < x - 1 by linarith)
      simp [c, Real.smoothTransition.one_of_one_le (show 1 ≤ R * (x - 1) - 1 by linarith),
        show 2 - x / R = (-R⁻¹) * x + 2 by ring]
    rw [he.deriv_eq, he.deriv.deriv_eq]
    simpa only [abs_neg, abs_inv, abs_of_pos hp, inv_pow, div_eq_mul_inv] using (hjet (-R⁻¹) 2 t).2

private theorem introTraceApprox_product_second_bound {c f : ℝ → ℂ} {t : ℝ}
    (hc : ContDiffAt ℝ 2 c t) (hf : ContDiffAt ℝ 2 f t) :
    ‖deriv (deriv (c * f)) t‖ ≤ ‖deriv (deriv c) t‖ * ‖f t‖ +
      2 * ‖deriv c t‖ * ‖deriv f t‖ + ‖c t‖ * ‖deriv (deriv f) t‖ := by
  have he := iteratedDeriv_mul hc hf
  norm_num [Finset.sum_range_succ, iteratedDeriv_succ, nsmul_eq_mul] at he
  rw [he]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by
      grw [norm_add_le]
      simp only [norm_mul, Complex.norm_two]
      linarith

/-- For the translated inner kernel of an actual matched additive convolution the
second derivative costs one inverse mesh unit in the lower boundary layer, and
decays like `t^(-m-2)` throughout the remaining support. -/
private theorem introTraceApprox_reference_dilated_second_bound (m Z : ℝ) (hm : 0 ≤ m) (hZ : 0 ≤ Z) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (R t u : ℝ) (z w : ℂ),
      4 ≤ R → 1 + 1 / R ≤ t → t ≤ 2 * R → |u| ≤ 1 / (2 * R) → m ≤ z.re → m ≤ w.re → ‖z‖ ≤ Z → ‖w‖ ≤ Z →
      let c := fun x : ℝ ↦ ((Real.smoothTransition (R * (x - 1) - 1) * Real.smoothTransition (2 - x / R) : ℝ) : ℂ)
      let f := fun x : ℝ ↦ introTracePower z (x - u) - introTracePower w (x - u)
      (t ≤ 1 + 2 / R → ‖deriv (deriv (c * f)) t‖ ≤ A * R) ∧
      (1 + 2 / R < t → ‖deriv (deriv (c * f)) t‖ ≤ A * t ^ (-m - 2)) := by
  obtain ⟨C, hC, hfjet⟩ := introTraceApprox_translated_reference_jet_bound m Z hm hZ
  obtain ⟨D, hD, hcjet⟩ := introTraceApprox_dilated_cutoff_jet
  let A := (8 * D + 1) * C
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro R t u z w hR hl hr hu hz hw hnorm hwn c f
  have hp : 0 < R := by linarith
  have hd : 0 < 1 / R := by positivity
  have hh : 1 / (2 * R) < 1 / R := one_div_lt_one_div_of_lt hp (by linarith)
  have ht : 1 < t := by linarith
  have ht0 : 0 < t := zero_lt_one.trans ht
  have h1 : |u| ≤ 1 := hu.trans (by apply (div_le_one (by positivity)).2; linarith)
  have hsep : |u| ≤ t - 1 := by linarith
  have hx : 1 < t - u := by linarith [(abs_le.mp hu).2]
  obtain ⟨hf0,hf1,hf2⟩ := hfjet z w t u hz hw hnorm hwn ht h1 hsep hx
  obtain ⟨hc0,hlo,hhi⟩ := hcjet R t hR
  have hc : ContDiffAt ℝ 2 c t := (Complex.ofRealCLM.contDiff.comp
    ((Real.smoothTransition.contDiff.comp (by fun_prop)).mul
      (Real.smoothTransition.contDiff.comp (by fun_prop)))).contDiffAt
  have hpwr (w : ℂ) : ContDiffAt ℝ 2 (fun x : ℝ ↦ introTracePower w (x - u)) t := by
    have h := (introTracePower_contDiffOn w).contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds
      (show t - u ∈ ({1}ᶜ : Set ℝ) from hx.ne'))
    exact (h.comp t (contDiffAt_id.sub contDiffAt_const)).of_le (by simp)
  have hprod := introTraceApprox_product_second_bound hc ((hpwr z).sub (hpwr w))
  have hweight (j : ℝ) (hj : 0 ≤ j) : t ^ (-m - j) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht.le (by linarith)
  have hfbase : ‖f t‖ ≤ C * t ^ (-m) := hf0.trans
    (mul_le_of_le_one_right (by positivity) ((div_le_one ht0).2 (by linarith)))
  constructor
  · intro hlow
    obtain ⟨hc1,hc2⟩ := hlo hlow
    have hfrac : (t - 1) / t ≤ 2 / R := ((div_le_iff₀ ht0).2 (by nlinarith [mul_nonneg (show 0 ≤ 2 / R by positivity) (sub_nonneg.mpr ht.le)]))
    have hfsmall : ‖f t‖ ≤ C * (2 / R) := hf0.trans (mul_le_mul
      (mul_le_of_le_one_right hC (by simpa using hweight 0 le_rfl)) hfrac
      (by positivity) hC)
    have hfl1 := hf1.trans (mul_le_of_le_one_right hC (hweight 1 zero_le_one))
    have hfl2 := hf2.trans (mul_le_of_le_one_right hC (hweight 2 (by norm_num)))
    refine hprod.trans ?_
    calc
      _ ≤ (D * R ^ 2) * (C * (2 / R)) + 2 * (D * R) * C + 1 * C := by gcongr
      _ = 4 * D * C * R + C := by field_simp; ring
      _ ≤ A * R := by
        have hcr : C ≤ C * R := le_mul_of_one_le_right hC (by linarith)
        dsimp [A]
        nlinarith [mul_nonneg (mul_nonneg hD0 hC) hp.le]
  · intro hhigh
    obtain ⟨hc1,hc2⟩ := hhi hhigh
    have hq : t / R ≤ 2 := (div_le_iff₀ hp).2 hr
    have hqn : 0 ≤ t / R := by positivity
    have hpone : t ^ (-m - 1) = t ^ (-m) / t := by rw [Real.rpow_sub ht0, Real.rpow_one]
    have hptwo : t ^ (-m - 2) = t ^ (-m) / t ^ 2 := by rw [Real.rpow_sub ht0, Real.rpow_ofNat]
    refine hprod.trans ?_
    calc
      _ ≤ (D / R ^ 2) * (C * t ^ (-m)) + 2 * (D / R) * (C * t ^ (-m - 1)) + 1 * (C * t ^ (-m - 2)) := by gcongr
      _ = (D * (t / R) ^ 2 + 2 * D * (t / R) + 1) * (C * t ^ (-m) / t ^ 2) := by rw [hpone,hptwo]; field_simp
      _ ≤ (D * 2 ^ 2 + 2 * D * 2 + 1) * (C * t ^ (-m) / t ^ 2) := by gcongr
      _ = A * t ^ (-m - 2) := by rw [hptwo]; dsimp [A]; ring

open Classical in
/-- The cutoff keeps a translated power away from its jump at one. -/
private theorem introTraceApprox_single_dilated_support {R u : ℝ} (hR : 4 ≤ R)
    (hu : |u| ≤ 1 / (2 * R)) (z : ℂ) :
    let c := fun x : ℝ ↦ ((Real.smoothTransition (R * (x - 1) - 1) * Real.smoothTransition (2 - x / R) : ℝ) : ℂ)
    let f := fun x : ℝ ↦ introTracePower z (x - u)
    ContDiff ℝ 2 (c * f) ∧ tsupport (c * f) ⊆ Icc (1 + 1 / R) (2 * R) := by
  intro c f
  have hp : 0 < R := by linarith
  have hc : ContDiff ℝ 2 c := Complex.ofRealCLM.contDiff.comp
    ((Real.smoothTransition.contDiff.comp (by fun_prop)).mul
      (Real.smoothTransition.contDiff.comp (by fun_prop)))
  have hs : tsupport (c * f) ⊆ Icc (1 + 1 / R) (2 * R) := by
    apply tsupport_mul_subset_left.trans
    apply (closure_mono (support_comp_subset (g := Complex.ofReal) Complex.ofReal_zero _)).trans
    exact introTraceApprox_dilated_cutoff_support hp
  refine ⟨contDiff_iff_contDiffAt.mpr (fun t ↦ ?_), hs⟩
  by_cases ht : t ∈ tsupport (c * f)
  · have hh : 1 / (2 * R) < 1 / R := one_div_lt_one_div_of_lt hp (by linarith)
    have hx : 1 < t - u := by linarith [(hs ht).1, (abs_le.mp hu).2]
    have hpow (w : ℂ) : ContDiffAt ℝ 2 (fun x : ℝ ↦ introTracePower w (x - u)) t := by
      have h := (introTracePower_contDiffOn w).contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds
        (show t - u ∈ ({1}ᶜ : Set ℝ) from hx.ne'))
      exact (h.comp t (contDiffAt_id.sub contDiffAt_const)).of_le (by simp)
    exact hc.contDiffAt.mul (hpow z)
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp ht)

private theorem introTraceApprox_reference_dilated_support {R u : ℝ} (hR : 4 ≤ R)
    (hu : |u| ≤ 1 / (2 * R)) (z w : ℂ) :
    let c := fun x : ℝ ↦ ((Real.smoothTransition (R * (x - 1) - 1) * Real.smoothTransition (2 - x / R) : ℝ) : ℂ)
    let f := fun x : ℝ ↦ introTracePower z (x - u) - introTracePower w (x - u)
    ContDiff ℝ 2 (c * f) ∧ tsupport (c * f) ⊆ Icc (1 + 1 / R) (2 * R) := by
  intro c f
  obtain ⟨hz,hs⟩ := introTraceApprox_single_dilated_support hR hu z
  obtain ⟨hw,ht⟩ := introTraceApprox_single_dilated_support hR hu w
  let g (q : ℂ) := c * (fun x : ℝ ↦ introTracePower q (x-u))
  have he : c * f = g z - g w := funext fun x ↦ mul_sub _ _ _
  rw [he]
  refine ⟨hz.sub hw,?_⟩
  intro t htt
  by_contra hn
  have hz0 := notMem_tsupport_iff_eventuallyEq.mp (mt (fun h ↦ hs h) hn)
  have hw0 := notMem_tsupport_iff_eventuallyEq.mp (mt (fun h ↦ ht h) hn)
  exact (notMem_tsupport_iff_eventuallyEq.mpr (show g z - g w =ᶠ[𝓝 t] 0 by simpa only [sub_zero] using hz0.sub hw0)) htt

/-- The translated profile multiplied by the chosen smooth cutoff has uniformly
bounded weighted zeroth and second radial derivatives. The lower-layer cost
`R` is integrated over an interval of length `1/R`. -/
private theorem introTraceApprox_reference_dilated_weighted (a m Z : ℝ) (ha : 0 ≤ a)
    (ham : a < m) (hZ : 0 ≤ Z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (R u : ℝ) (z w : ℂ),
      4 ≤ R → |u| ≤ 1 / (2 * R) → m ≤ z.re → m ≤ w.re → ‖z‖ ≤ Z → ‖w‖ ≤ Z →
      let c := fun x : ℝ ↦ ((Real.smoothTransition (R * (x - 1) - 1) * Real.smoothTransition (2 - x / R) : ℝ) : ℂ)
      let f := fun x : ℝ ↦ introTracePower z (x - u) - introTracePower w (x - u)
      (∫ t in 1..3 * R, t ^ (a - 1) * ‖(c * f) t‖) ≤ B ∧
      (∫ t in 1..3 * R, t ^ (a + 1) * ‖deriv (deriv (c * f)) t‖) ≤ B := by
  obtain ⟨C, hC, hjet⟩ := introTraceApprox_translated_reference_jet_bound m Z (ha.trans ham.le) hZ
  obtain ⟨A, hA, hbound⟩ := introTraceApprox_reference_dilated_second_bound m Z (ha.trans ham.le) hZ
  let p (t : ℝ) := t ^ (a - m - 1)
  have hpint : IntegrableOn p (Ioi 1) := integrableOn_Ioi_rpow_of_lt (by linarith : a - m - 1 < -1) zero_lt_one
  have hpnn : ∀ᵐ t ∂volume.restrict (Ioi 1), 0 ≤ p t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (zero_le_one.trans (le_of_lt ht)) _
  let I := ∫ t in Ioi 1, p t
  have hI : 0 ≤ I := integral_nonneg_of_ae hpnn
  let B := max (C * I) (A * 2 ^ (a + 1) + A * I)
  refine ⟨B, (mul_nonneg hC hI).trans (le_max_left _ _), ?_⟩
  intro R u z w hR hu hz hw hnorm hwn c f
  let S := Ioc (1 : ℝ) (3 * R)
  let L := Icc (1 + 1 / R) (1 + 2 / R)
  let H := A * R * 2 ^ (a + 1)
  have hR0 : 0 < R := by linarith
  have hRu : 0 < 1 / R := by positivity
  have hlohi : 1 + 1 / R ≤ 1 + 2 / R := by gcongr; norm_num
  have hfrac : 2 / R ≤ 1 := (div_le_one hR0).2 (by linarith)
  have hLS : L ⊆ S := fun t ⟨ht,ht'⟩ ↦ ⟨by linarith, by linarith⟩
  have hSS : S ⊆ Ioi 1 := fun _ h ↦ h.1
  have hKI : IntegrableOn (L.indicator (fun _ ↦ H)) S :=
    (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc).integrableOn
  have hLI : ∫ t in S, L.indicator (fun _ ↦ H) t = A * 2 ^ (a + 1) := by
    rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hLS, setIntegral_const,
      Real.volume_real_Icc_of_le hlohi, smul_eq_mul]
    dsimp [H]
    field_simp
    ring
  have htailI : ∫ t in S, p t ≤ I :=
    setIntegral_mono_set hpint hpnn (ae_of_all _ hSS)
  obtain ⟨hsm, hs⟩ := introTraceApprox_reference_dilated_support hR hu z w
  have h1R : 1 ≤ 3 * R := by linarith
  rw [intervalIntegral.integral_of_le h1R, intervalIntegral.integral_of_le h1R]
  have hpowers (t : ℝ) (ht : 1 < t) (j k : ℝ) (hjk : j + k=a - m - 1) : t ^ j * t ^ k = p t := by
    rw [← Real.rpow_add (zero_lt_one.trans ht), hjk]
  have hbase (t : ℝ) (ht : 1 < t) : t ^ (a - 1)*‖(c * f) t‖ ≤ C * p t := by
    by_cases hm : t ∈ tsupport (c * f)
    · obtain ⟨hl,hr⟩ := hs hm
      have hcomp : 1 / (2 * R)<1 / R := one_div_lt_one_div_of_lt hR0 (by linarith)
      have hsep : |u| ≤ t - 1 := by linarith
      have hnear : |u| ≤ 1 := hu.trans ((div_le_one (by positivity)).2 (by linarith))
      have hx : 1 < t - u := by linarith [(abs_le.mp hu).2]
      have hf := (hjet z w t u hz hw hnorm hwn ht hnear hsep hx).1
      have hsmall : (t - 1) / t ≤ 1 := (div_le_one (zero_lt_one.trans ht)).2 (by linarith)
      have hfv := hf.trans (mul_le_of_le_one_right (by positivity) hsmall)
      have hc : ‖c t‖ ≤ 1 := by
        dsimp only [c]
        rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))]
        exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)
      calc
        _ = t ^ (a - 1) * (‖c t‖*‖f t‖) := by rw [Pi.mul_apply, norm_mul]
        _ ≤ t ^ (a - 1) * (1 * (C * t ^ (-m))) := by gcongr
        _ = C * p t := by rw [← hpowers t ht (a - 1) (-m) (by ring)]; ring
    · rw [image_eq_zero_of_notMem_tsupport hm, norm_zero, mul_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans ht.le) _)
  have hsecond (t : ℝ) (ht : 1 < t) :
      t ^ (a + 1) * ‖deriv (deriv (c * f)) t‖ ≤ L.indicator (fun _ ↦ H) t + A * p t := by
    have hnon : 0 ≤ A * p t := mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans ht.le) _)
    by_cases hm : t ∈ tsupport (c * f)
    · obtain ⟨hl,hr⟩ := hs hm
      obtain ⟨low,high⟩ := hbound R t u z w hR hl hr hu hz hw hnorm hwn
      by_cases htop : t ≤ 1 + 2 / R
      · rw [indicator_of_mem (show t ∈ L from ⟨hl,htop⟩)]
        refine le_add_of_le_of_nonneg ?_ hnon
        have htp : t ^ (a + 1) ≤ 2 ^ (a + 1) := Real.rpow_le_rpow (zero_le_one.trans ht.le) (by linarith) (by linarith)
        exact (mul_le_mul htp (low htop) (norm_nonneg _) (by positivity)).trans_eq (by dsimp [H]; ring)
      · rw [indicator_of_notMem (show t ∉ L from fun h ↦ htop h.2), zero_add]
        calc
          _ ≤ t ^ (a + 1) * (A * t ^ (-m - 2)) := by gcongr; exact high (lt_of_not_ge htop)
          _ = A * p t := by rw [← hpowers t ht (a + 1) (-m - 2) (by ring)]; ring
    · have he := (notMem_tsupport_iff_eventuallyEq.mp hm).deriv.deriv_eq
      have hzero : deriv (deriv (c * f)) t = 0 := by simpa using he
      rw [hzero, norm_zero, mul_zero]
      exact add_nonneg (indicator_nonneg (fun _ _ ↦ show 0 ≤ H by dsimp [H]; positivity) _) hnon
  constructor
  · refine (integral_mono_of_nonneg ?_ ((hpint.mono_set hSS).const_mul C) ?_).trans ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans ht.1.le) _) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hbase t ht.1
    · rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left htailI hC).trans (le_max_left _ _)
  · refine (integral_mono_of_nonneg ?_ (hKI.add ((hpint.mono_set hSS).const_mul A)) ?_).trans ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans ht.1.le) _) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hsecond t ht.1
    · simp only [Pi.add_apply]
      rw [integral_add hKI ((hpint.mono_set hSS).const_mul A), hLI, integral_const_mul]
      calc
        _ ≤ A * 2 ^ (a + 1) + A * I := by gcongr
        _ ≤ B := le_max_right _ _

private theorem introTrace_intervalMellin_shift {f : ℝ → ℂ} {T : ℝ} (hT : 1 ≤ T)
    (hf : ContDiff ℝ 1 f) (h1 : f 1 = 0) (hr : f T = 0) (s : ℂ) :
    s * (∫ t in (1 : ℝ)..T, (t : ℂ) ^ (s - 1) * f t) =
      -(∫ t in (1 : ℝ)..T, (t : ℂ) ^ s * deriv f t) := by
  have hpos {t : ℝ} (ht : t ∈ uIcc 1 T) : t ≠ 0 := by
    rw [uIcc_of_le hT] at ht
    exact (zero_lt_one.trans_le ht.1).ne'
  have hpow (w : ℂ) : IntervalIntegrable (fun t : ℝ ↦ (t : ℂ) ^ w) volume 1 T :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (Complex.continuousAt_ofReal_cpow_const t w (.inr (hpos ht))).continuousWithinAt
  have hp : ∀ t ∈ uIcc 1 T, HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ s) (s * (t : ℂ) ^ (s - 1)) t := by
    intro t ht
    have hh := (differentiableAt_id.ofReal_cpow_const s (hpos ht)).hasDerivAt
    simp only [id_eq] at hh
    rwa [Complex.deriv_ofReal_cpow_const s (hpos ht)] at hh
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 1) (b := T)
    (fun t _ ↦ (hf.differentiable_one t).hasDerivAt) hp
    ((hf.continuous_deriv le_rfl).intervalIntegrable _ _) ((hpow _).const_mul s)
  simp only [h1, hr, zero_mul, sub_zero, zero_sub] at H
  rw [← intervalIntegral.integral_const_mul]
  convert H using 1
  · exact intervalIntegral.integral_congr fun t _ ↦ by ring
  · congr 1
    exact intervalIntegral.integral_congr fun t _ ↦ mul_comm _ _

/-- Two weighted radial integrals control the Mellin transform throughout a half-plane,
with a constant independent of the upper end of the support. -/
private theorem introTraceMellin_le_of_weighted_deriv {f : ℝ → ℂ} {T A B : ℝ}
    (hT : 1 ≤ T) (hf : ContDiff ℝ 2 f) (hsupp : tsupport f ⊆ Ioo 1 T)
    (h0 : (∫ t in (1 : ℝ)..T, t ^ (A - 1) * ‖f t‖) ≤ B)
    (h2 : (∫ t in (1 : ℝ)..T, t ^ (A + 1) * ‖deriv (deriv f) t‖) ≤ B)
    (s : ℂ) (hs : s.re ≤ A) : ‖introTraceMellin f s‖ ≤ 4 * B / (1+|s.im|) ^ 2 := by
  have h1 : 1 ∉ tsupport f := fun h ↦ (lt_irrefl _) (hsupp h).1
  have hr : T ∉ tsupport f := fun h ↦ (lt_irrefl _) (hsupp h).2
  have hf' := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)
  have hdd := (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv f) from hf'.2.2)).2.2.continuous
  have hnorm (w : ℂ) (b : ℝ) (hw : w.re ≤ b) (g : ℝ → ℂ) (hg : Continuous g) :
      ‖∫ t in (1 : ℝ)..T, (t : ℂ) ^ w * g t‖ ≤ ∫ t in (1 : ℝ)..T, t ^ b * ‖g t‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le hT (.of_forall fun t ht ↦ ?_) ?_
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht.1)]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht.1.le hw) (norm_nonneg _)
    · apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [uIcc_of_le hT] at ht
      exact ((Real.continuousAt_rpow_const _ _ (.inl (zero_lt_one.trans_le ht.1).ne')).mul
        (hg.norm.continuousAt)).continuousWithinAt
  rw [introTraceApprox_spectral_differentiable_mellin_interval f zero_lt_one hT
    (fun t ht ↦ hsupp (subset_tsupport _ ht))]
  have l0 := (hnorm (s - 1) (A - 1) (by simpa using hs) f hf.continuous).trans h0
  have hB : 0 ≤ B := (norm_nonneg _).trans l0
  have hden : 0 < (1+|s.im|) ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  by_cases h : |s.im| ≤ 1
  · calc _ ≤ B * 4 := mul_le_mul l0 (by nlinarith [abs_nonneg s.im]) hden.le hB
         _ = 4 * B := mul_comm _ _
  have hp := introTrace_intervalMellin_shift hT (hf.of_le (by decide))
    (image_eq_zero_of_notMem_tsupport h1) (image_eq_zero_of_notMem_tsupport hr) s
  have hq := introTrace_intervalMellin_shift hT hf'.2.2 (deriv_of_notMem_tsupport h1)
    (deriv_of_notMem_tsupport hr) (s + 1)
  rw [add_sub_cancel_right] at hq
  have he : (s + 1) * s * (∫ t in (1 : ℝ)..T, (t : ℂ) ^ (s - 1) * f t) =
      ∫ t in (1 : ℝ)..T, (t : ℂ) ^ (s + 1) * deriv (deriv f) t := by
    rw [mul_assoc, hp, mul_neg, hq, neg_neg]
  have l2 := (hnorm (s + 1) (A + 1) (by simpa using hs) _ hdd).trans h2
  have hweight : (1+|s.im|) ^ 2 ≤ 4 * (‖s + 1‖ * ‖s‖) := by
    have e₁ : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
    have e₂ := Complex.abs_im_le_norm s
    nlinarith [mul_le_mul e₁ e₂ (abs_nonneg _) (norm_nonneg _)]
  rw [← he, norm_mul, norm_mul] at l2
  calc _ ≤ _ := mul_le_mul_of_nonneg_left hweight (norm_nonneg _)
       _ ≤ 4 * B := by linarith

private theorem introTracePower_norm_le_one {z : ℂ} (hz : 0 ≤ z.re) (x : ℝ) :
    ‖introTracePower z x‖ ≤ 1 := by
  by_cases hx : 1 < x
  · rw [introTracePower, ite_eq_left hx, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx.le (by simpa using hz)
  · by_cases he : x = 1
    · norm_num [introTracePower, hx, he]
    · simp [introTracePower, hx, he]

open Classical in
/-- The Mellin integral of a cutoff is the integral of its translated powers against the mollifier. -/
private theorem introTraceApprox_mellin_translated_kernel {h ρ : ℝ → ℝ} {T : ℝ}
    (hT : 1 ≤ T) (hh : Continuous h) (hsupp : tsupport h ⊆ Ioo 1 T)
    (hr : Integrable ρ) (hm : Measurable ρ) (z s : ℂ) (hz : 0 ≤ z.re) :
    let μ := volume.restrict (Ioc 1 T)
    let v (t : ℝ) : ℂ := (t : ℂ) ^ (s - 1) * (h t : ℂ)
    let k (t u : ℝ) : ℂ := (ρ u : ℂ) * (v t * introTracePower z (t - u))
    Integrable (uncurry k) (μ.prod volume) ∧
    introTraceMellin (introTraceApprox h ρ z) s = ∫ u : ℝ, ∫ t : ℝ, k t u ∂μ := by
  intro μ v k
  have hvm : Measurable v := by dsimp [v]; fun_prop
  have hv : Integrable v μ := by
    refine ContinuousOn.integrableOn_Icc (μ := volume) (a := 1) (b := T) (f := v) ?_ |>.mono_set Ioc_subset_Icc_self
    intro t ht
    exact ((Complex.continuousAt_ofReal_cpow_const t (s - 1) (.inr
      (zero_lt_one.trans_le ht.1).ne')).mul
      (Complex.continuous_ofReal.comp hh).continuousAt).continuousWithinAt
  have hi : Integrable (uncurry k) (μ.prod volume) := by
    have pm := (introTraceApprox_mellin_tendsto_power_measurable z).comp
      (measurable_fst.sub measurable_snd : Measurable fun a : ℝ × ℝ ↦ a.1 - a.2)
    refine (hv.norm.mul_prod hr.norm).mono' ((((Complex.measurable_ofReal.comp hm).comp measurable_snd).mul
      ((hvm.comp measurable_fst).mul pm)).aestronglyMeasurable) ?_
    filter_upwards with a
    simp only [uncurry, k, norm_mul, Complex.norm_real]
    calc _ ≤ ‖ρ a.2‖ * (‖v a.1‖ * 1) := by
             gcongr
             exact introTracePower_norm_le_one hz _
         _ = _ := by ring
  have hM : introTraceMellin (introTraceApprox h ρ z) s =
      ∫ t, ∫ u : ℝ, k t u ∂volume ∂μ := by
    rw [introTraceApprox_spectral_differentiable_mellin_interval _ zero_lt_one hT
      (fun t ht ↦ hsupp (subset_tsupport _ (fun hzero ↦ ht (by simp [introTraceApprox, hzero])))),
      intervalIntegral.integral_of_le hT]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [introTraceApprox]
    rw [← mul_assoc, ← integral_const_mul]
    exact integral_congr_ae (.of_forall fun u ↦ by dsimp [k,v]; ring)
  exact ⟨hi,hM.trans (integral_integral_swap hi)⟩

/-- Write a difference of smoothed Mellin moments as the mollifier average of the
moments of the translated, cut-off difference. -/
private theorem introTraceApprox_mellin_sub_eq_integral {h ρ : ℝ → ℝ} {T : ℝ}
    (hT : 1 ≤ T) (hh : Continuous h) (hsupp : tsupport h ⊆ Ioo 1 T)
    (hr : Integrable ρ) (hm : Measurable ρ) (z w s : ℂ) (hz : 0 ≤ z.re) (hw : 0 ≤ w.re) :
    introTraceMellin (introTraceApprox h ρ z) s - introTraceMellin (introTraceApprox h ρ w) s =
    ∫ u : ℝ, (ρ u : ℂ) * introTraceMellin
      (fun t : ℝ ↦ (h t : ℂ) * (introTracePower z (t - u) - introTracePower w (t - u))) s := by
  let μ := volume.restrict (Ioc 1 T)
  let v (t : ℝ) : ℂ := (t : ℂ) ^ (s - 1) * (h t : ℂ)
  let k (q : ℂ) (t u : ℝ) : ℂ := (ρ u : ℂ) * (v t * introTracePower q (t - u))
  have hk (q : ℂ) (hq : 0 ≤ q.re) := introTraceApprox_mellin_translated_kernel hT hh hsupp hr hm q s hq
  have hi (q : ℂ) (hq : 0 ≤ q.re) : Integrable (uncurry (k q)) (μ.prod volume) := (hk q hq).1
  have hM (q : ℂ) (hq : 0 ≤ q.re) : introTraceMellin (introTraceApprox h ρ q) s =
      ∫ u : ℝ, ∫ t : ℝ, k q t u ∂μ := (hk q hq).2
  have houter (q : ℂ) (hq : 0 ≤ q.re) : Integrable (fun u ↦ ∫ t, k q t u ∂μ) :=
    (hi q hq).integral_prod_right
  rw [hM z hz, hM w hw,
    ← integral_sub (houter z hz) (houter w hw)]
  apply integral_congr_ae
  filter_upwards [(hi z hz).prod_left_ae, (hi w hw).prod_left_ae]
    with u hzu hwu
  change Integrable (fun t ↦ k z t u) μ at hzu
  change Integrable (fun t ↦ k w t u) μ at hwu
  rw [← integral_sub hzu hwu, introTraceApprox_spectral_differentiable_mellin_interval _ zero_lt_one hT
    (fun t ht ↦ hsupp (subset_tsupport _ (fun hzero ↦ ht (by simp [hzero])))),
    intervalIntegral.integral_of_le hT, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun t ↦ by dsimp [k,v]; ring)

private theorem introTraceApprox_mellin_sub_le_of_translated {h ρ : ℝ → ℝ} {T B : ℝ}
    (hT : 1 ≤ T) (hh : Continuous h) (hsupp : tsupport h ⊆ Ioo 1 T)
    (hr : Integrable ρ) (hm : Measurable ρ) (hρ : ∀ u, 0 ≤ ρ u) (h1 : ∫ u, ρ u = 1)
    (z w s : ℂ) (hz : 0 ≤ z.re) (hw : 0 ≤ w.re)
    (hbound : ∀ u, ρ u ≠ 0 → ‖introTraceMellin
      (fun t : ℝ ↦ (h t : ℂ) * (introTracePower z (t - u) - introTracePower w (t - u))) s‖ ≤ B) :
    ‖introTraceMellin (introTraceApprox h ρ z) s - introTraceMellin (introTraceApprox h ρ w) s‖ ≤ B := by
  rw [introTraceApprox_mellin_sub_eq_integral hT hh hsupp hr hm z w s hz hw]
  calc _ ≤ ∫ u : ℝ, ρ u * B := by
         apply norm_integral_le_of_norm_le (hr.mul_const B)
         filter_upwards with u
         by_cases hu : ρ u = 0
         · simp [hu]
         · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ u)]
           exact mul_le_mul_of_nonneg_left (hbound u hu) (hρ u)
       _ = B := by rw [integral_mul_const, h1, one_mul]

open Classical in
/-- Exchange Mellin integration with the mollifier for a single cutoff power. -/
private theorem introTraceApprox_mellin_eq_translated {h ρ : ℝ → ℝ} {T : ℝ}
    (hT : 1 ≤ T) (hh : Continuous h) (hsupp : tsupport h ⊆ Ioo 1 T)
    (hr : Integrable ρ) (hm : Measurable ρ) (z s : ℂ) (hz : 0 ≤ z.re) :
    introTraceMellin (introTraceApprox h ρ z) s =
    ∫ u : ℝ, (ρ u : ℂ) * introTraceMellin
      (fun t : ℝ ↦ (h t : ℂ) * introTracePower z (t - u)) s := by
  rw [(introTraceApprox_mellin_translated_kernel hT hh hsupp hr hm z s hz).2]
  apply integral_congr_ae
  filter_upwards with u
  rw [introTraceApprox_spectral_differentiable_mellin_interval _ zero_lt_one hT
    (fun t ht ↦ hsupp (subset_tsupport _ (fun hzero ↦ ht (by simp [hzero])))),
    intervalIntegral.integral_of_le hT, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun t ↦ by ring)

open Classical in
/-- One weighted radial derivative gives inverse first-power decay in the Mellin height. -/
private theorem introTraceMellin_le_of_first_deriv {f : ℝ → ℂ} {T A B : ℝ}
    (hT : 1 ≤ T) (hf : ContDiff ℝ 1 f) (hsupp : tsupport f ⊆ Ioo 1 T)
    (h0 : (∫ t in (1:ℝ)..T, t^(A-1) * ‖f t‖) ≤ B)
    (h1 : (∫ t in (1:ℝ)..T, t^A * ‖deriv f t‖) ≤ B)
    (s : ℂ) (hs : s.re ≤ A) : ‖introTraceMellin f s‖ ≤ 2 * B / (1 + |s.im|) := by
  have hnorm (w : ℂ) (b : ℝ) (hw : w.re ≤ b) (g : ℝ → ℂ) (hg : Continuous g) :
      ‖∫ t in (1:ℝ)..T, (t:ℂ)^w * g t‖ ≤ ∫ t in (1:ℝ)..T, t^b * ‖g t‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le hT (.of_forall fun t ht ↦ ?_) ?_
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht.1)]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht.1.le hw) (norm_nonneg _)
    · apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [uIcc_of_le hT] at ht
      exact ((Real.continuousAt_rpow_const _ _ (.inl (zero_lt_one.trans_le ht.1).ne')).mul
        hg.norm.continuousAt).continuousWithinAt
  rw [introTraceApprox_spectral_differentiable_mellin_interval f zero_lt_one hT
    (fun t ht ↦ hsupp (subset_tsupport _ ht))]
  have hv := (hnorm (s-1) (A-1) (by simpa using hs) f hf.continuous).trans h0
  have hd := (hnorm s A hs (deriv f) (hf.continuous_deriv le_rfl)).trans h1
  have hp := introTrace_intervalMellin_shift hT hf
    (image_eq_zero_of_notMem_tsupport fun h ↦ (lt_irrefl _) (hsupp h).1)
    (image_eq_zero_of_notMem_tsupport fun h ↦ (lt_irrefl _) (hsupp h).2) s
  have ht := congrArg norm hp
  rw [norm_mul,norm_neg] at ht
  have hlin := (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s)
    (norm_nonneg (∫ t in (1:ℝ)..T, (t:ℂ)^(s-1) * f t))).trans (ht.le.trans hd)
  rw [le_div_iff₀ (by positivity)]
  linarith only [hv,hlin]

open Classical in
/-- The derivative costs one inverse mesh unit near the lower cutoff and decays with the translated power elsewhere. -/
private theorem introTraceApprox_single_dilated_jet (m Z : ℝ) (hm : 0 ≤ m) (hZ : 0 ≤ Z) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (R t u : ℝ) (z : ℂ),
      4 ≤ R → 1 + 1 / R ≤ t → t ≤ 2 * R → |u| ≤ 1 / (2 * R) →
      m ≤ z.re → ‖z‖ ≤ Z →
      let c := fun x : ℝ ↦ ((Real.smoothTransition (R * (x - 1) - 1) *
        Real.smoothTransition (2 - x / R) : ℝ) : ℂ)
      let f := fun x : ℝ ↦ introTracePower z (x-u)
      ‖(c*f) t‖ ≤ A * t^(-m) ∧
      (t ≤ 1+2/R → ‖deriv (c*f) t‖ ≤ A*R) ∧
      (1+2/R < t → ‖deriv (c*f) t‖ ≤ A * t^(-m-1)) := by
  obtain ⟨D,hD,hcut⟩ := introTraceApprox_dilated_cutoff_jet
  let b (x : ℝ) := (1/2 : ℝ)^(-x) + 2^(-x)
  let A := 2*D*b m + Z*b (m+1)
  have hb (x : ℝ) : 0 ≤ b x := by dsimp [b]; positivity
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hA : 0 ≤ A := by dsimp [A]; positivity [hb m, hb (m+1)]
  have hbA : b m ≤ A := by
    have := mul_le_mul_of_nonneg_right hD (hb m)
    dsimp [A]; nlinarith [hb m,mul_nonneg hZ (hb (m+1))]
  refine ⟨A,hA,?_⟩
  intro R t u z hR hl hr hu hz hZz c f
  have hR0 : 0 < R := by linarith
  have hgap := one_div_lt_one_div_of_lt hR0 (show R < 2*R by linarith)
  have ht : 1 < t := by linarith [show 0 < 1/R by positivity]
  have ht0 := zero_lt_one.trans ht
  have hu1 : |u| ≤ 1 := hu.trans ((div_le_one (by positivity)).2 (by linarith))
  have hx : 1 < t-u := by linarith [(abs_le.mp hu).2]
  let v : ℂ := ((t-u:ℝ):ℂ)
  have hp (q : ℂ) (a : ℝ) (ha : a ≤ q.re) : ‖v^(-q)‖ ≤ b a * t^(-a) := by
    simpa only [v,b,introTracePower,hx,ite_true] using
      (introTraceApprox_mellin_tendsto_power_bound (z := q) ht (by simpa using hu1 : |(t-u)-t| ≤ 1) ha)
  have hf : ‖f t‖ ≤ b m * t^(-m) := by simpa only [f,introTracePower,hx,ite_true] using hp z m hz
  have hj := (introTraceApprox_translated_power_jet z hx).1
  have hf' : ‖deriv f t‖ ≤ Z * b (m+1) * t^(-m-1) := by
    rw [show deriv f t = -z * v^(-z-1) from hj.deriv, norm_mul,norm_neg]
    have hq := hp (z+1) (m+1) (by simpa using hz)
    rw [neg_add_rev,show -(1:ℂ) + -z = -z-1 by ring,show -(m+1) = -m-1 by ring] at hq
    exact (mul_le_mul hZz hq (norm_nonneg _) hZ).trans_eq (mul_assoc _ _ _).symm
  obtain ⟨hc,hlo,hhi⟩ := hcut R t hR
  have hcd : ContDiff ℝ 2 c := Complex.ofRealCLM.contDiff.comp
    ((Real.smoothTransition.contDiff.comp (by fun_prop)).mul
      (Real.smoothTransition.contDiff.comp (by fun_prop)))
  have hprod : ‖deriv (c*f) t‖ ≤ ‖deriv c t‖ * ‖f t‖ + ‖c t‖ * ‖deriv f t‖ := by
    rw [deriv_mul (hcd.differentiable (by decide) t) hj.differentiableAt]
    simpa only [norm_mul] using norm_add_le (deriv c t * f t) (c t * deriv f t)
  refine ⟨?_,?_,?_⟩
  · rw [Pi.mul_apply,norm_mul]
    exact (mul_le_mul hc hf (norm_nonneg _) zero_le_one).trans
      (by rw [one_mul]; gcongr)
  · intro hlow
    have hf0 := hf.trans (mul_le_of_le_one_right (hb m)
      (Real.rpow_le_one_of_one_le_of_nonpos ht.le (neg_nonpos.mpr hm)))
    have hf1 := hf'.trans (mul_le_of_le_one_right (mul_nonneg hZ (hb _))
      (Real.rpow_le_one_of_one_le_of_nonpos ht.le (by linarith)))
    apply hprod.trans
    calc
      _ ≤ D*R*b m + 1*(Z*b (m+1)) := by gcongr; exact (hlo hlow).1
      _ ≤ A*R := by
        have hZR := le_mul_of_one_le_right (mul_nonneg hZ (hb (m+1))) (show 1 ≤ R by linarith)
        dsimp [A]; nlinarith [mul_nonneg (mul_nonneg hD0 hR0.le) (hb m)]
  · intro hhigh
    have hpower : t^(-m-1) = t^(-m)/t := by rw [Real.rpow_sub ht0, Real.rpow_one]
    have hdiv : 1/R ≤ 2/t := (div_le_div_iff₀ hR0 ht0).2 (by linarith)
    apply hprod.trans
    calc
      _ ≤ (D/R)*(b m*t^(-m)) + 1*(Z*b (m+1)*t^(-m-1)) := by gcongr; exact (hhi hhigh).1
      _ ≤ (D*(2/t))*(b m*t^(-m)) + 1*(Z*b (m+1)*t^(-m-1)) := by
        rw [show D/R=D*(1/R) by ring]; gcongr
      _ = A*t^(-m-1) := by rw [hpower]; dsimp [A]; ring

open Classical in
/-- After integration, the lower cutoff layer and the tail give a bound independent of the mesh. -/
private theorem introTraceApprox_single_dilated_weighted (a m Z : ℝ) (ha : 0 ≤ a)
    (ham : a < m) (hZ : 0 ≤ Z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (R u : ℝ) (z : ℂ),
      4 ≤ R → |u| ≤ 1 / (2 * R) → m ≤ z.re → ‖z‖ ≤ Z →
      let c := fun x : ℝ ↦ ((Real.smoothTransition (R * (x - 1) - 1) * Real.smoothTransition (2 - x / R) : ℝ) : ℂ)
      let f := fun x : ℝ ↦ introTracePower z (x - u)
      (∫ t in 1..3 * R, t ^ (a - 1) * ‖(c * f) t‖) ≤ B ∧
      (∫ t in 1..3 * R, t ^ a * ‖deriv (c * f) t‖) ≤ B := by
  obtain ⟨A, hA, hjet⟩ := introTraceApprox_single_dilated_jet m Z (ha.trans ham.le) hZ
  let p (t : ℝ) := t ^ (a - m - 1)
  have hpint : IntegrableOn p (Ioi 1) := integrableOn_Ioi_rpow_of_lt (by linarith : a - m - 1 < -1) zero_lt_one
  have hpnn : ∀ᵐ t ∂volume.restrict (Ioi 1), 0 ≤ p t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (zero_le_one.trans (le_of_lt ht)) _
  let I := ∫ t in Ioi 1, p t
  have hI : 0 ≤ I := integral_nonneg_of_ae hpnn
  let B := max (A * I) (A * 2 ^ a + A * I)
  refine ⟨B, (mul_nonneg hA hI).trans (le_max_left _ _), ?_⟩
  intro R u z hR hu hz hnorm c f
  let S := Ioc (1 : ℝ) (3 * R)
  let L := Icc (1 + 1 / R) (1 + 2 / R)
  let H := A * R * 2 ^ a
  have hR0 : 0 < R := by linarith
  have hRu : 0 < 1 / R := by positivity
  have hlohi : 1 + 1 / R ≤ 1 + 2 / R := by gcongr; norm_num
  have hfrac : 2 / R ≤ 1 := (div_le_one hR0).2 (by linarith)
  have hLS : L ⊆ S := fun t ⟨ht,ht'⟩ ↦ ⟨by linarith, by linarith⟩
  have hSS : S ⊆ Ioi 1 := fun _ h ↦ h.1
  have hKI : IntegrableOn (L.indicator (fun _ ↦ H)) S :=
    (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc).integrableOn
  have hLI : ∫ t in S, L.indicator (fun _ ↦ H) t = A * 2 ^ a := by
    rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hLS, setIntegral_const,
      Real.volume_real_Icc_of_le hlohi, smul_eq_mul]
    dsimp [H]
    field_simp
    ring
  have htailI : ∫ t in S, p t ≤ I :=
    setIntegral_mono_set hpint hpnn (ae_of_all _ hSS)
  obtain ⟨hsm, hs⟩ := introTraceApprox_single_dilated_support hR hu z
  have h1R : 1 ≤ 3 * R := by linarith
  rw [intervalIntegral.integral_of_le h1R, intervalIntegral.integral_of_le h1R]
  have hpowers (t : ℝ) (ht : 1 < t) (j k : ℝ) (hjk : j + k=a - m - 1) : t ^ j * t ^ k = p t := by
    rw [← Real.rpow_add (zero_lt_one.trans ht), hjk]
  have hbase (t : ℝ) (ht : 1 < t) : t ^ (a - 1)*‖(c * f) t‖ ≤ A * p t := by
    by_cases hm : t ∈ tsupport (c * f)
    · obtain ⟨hl,hr⟩ := hs hm
      have hf := (hjet R t u z hR hl hr hu hz hnorm).1
      calc
        _ ≤ t ^ (a - 1) * (A * t ^ (-m)) := by gcongr
        _ = A * p t := by rw [← hpowers t ht (a - 1) (-m) (by ring)]; ring
    · rw [image_eq_zero_of_notMem_tsupport hm, norm_zero, mul_zero]
      exact mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans ht.le) _)
  have hsecond (t : ℝ) (ht : 1 < t) :
      t ^ a * ‖deriv (c * f) t‖ ≤ L.indicator (fun _ ↦ H) t + A * p t := by
    have hnon : 0 ≤ A * p t := mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans ht.le) _)
    by_cases hm : t ∈ tsupport (c * f)
    · obtain ⟨hl,hr⟩ := hs hm
      obtain ⟨_,low,high⟩ := hjet R t u z hR hl hr hu hz hnorm
      by_cases htop : t ≤ 1 + 2 / R
      · rw [indicator_of_mem (show t ∈ L from ⟨hl,htop⟩)]
        refine le_add_of_le_of_nonneg ?_ hnon
        have htp : t ^ a ≤ 2 ^ a := Real.rpow_le_rpow (zero_le_one.trans ht.le) (by linarith) (by linarith)
        exact (mul_le_mul htp (low htop) (norm_nonneg _) (by positivity)).trans_eq (by dsimp [H]; ring)
      · rw [indicator_of_notMem (show t ∉ L from fun h ↦ htop h.2), zero_add]
        calc
          _ ≤ t ^ a * (A * t ^ (-m - 1)) := by gcongr; exact high (lt_of_not_ge htop)
          _ = A * p t := by rw [← hpowers t ht a (-m - 1) (by ring)]; ring
    · have he := (notMem_tsupport_iff_eventuallyEq.mp hm).deriv_eq
      have hzero : deriv (c * f) t = 0 := by simpa using he
      rw [hzero, norm_zero, mul_zero]
      exact add_nonneg (indicator_nonneg (fun _ _ ↦ show 0 ≤ H by dsimp [H]; positivity) _) hnon
  constructor
  · refine (integral_mono_of_nonneg ?_ ((hpint.mono_set hSS).const_mul A) ?_).trans ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans ht.1.le) _) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hbase t ht.1
    · rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left htailI hA).trans (le_max_left _ _)
  · refine (integral_mono_of_nonneg ?_ (hKI.add ((hpint.mono_set hSS).const_mul A)) ?_).trans ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans ht.1.le) _) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hsecond t ht.1
    · simp only [Pi.add_apply]
      rw [integral_add hKI ((hpint.mono_set hSS).const_mul A), hLI, integral_const_mul]
      calc
        _ ≤ A * 2 ^ a + A * I := by gcongr
        _ ≤ B := le_max_right _ _

open Classical in
/-- One matched cutoff family supplies the reference differences and a uniform reciprocal-height bound for individual Mellin moments. -/
private theorem introTraceApprox_exists_reference_and_sparse_moments :
    ∃ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ ∧
      (∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1) ∧
      (∀ a m Z : ℝ, 0 ≤ a → a < m → 0 ≤ Z → ∃ B : ℝ, 0 ≤ B ∧
        ∀ (n : ℕ) (z s : ℂ), m ≤ z.re → ‖z‖ ≤ Z → s.re ≤ a →
          ‖introTraceMellin approx(h, ρ, n, z) s‖ ≤ B / (1 + |s.im|)) ∧
      ∀ (χ : U𝔽) (a : ℝ), 0 ≤ a → ∀ w : ℂ → ℂ, MapsTo w right(a) right(a) →
        DifferentiableOn ℂ w right(a) →
        TendstoLocallyUniformlyOn (fun n z ↦ introTraceSpectralSum χ approx(h, ρ, n, z) a -
          introTraceSpectralSum χ approx(h, ρ, n, (w z)) a)
          (fun z ↦ ∑' r : windowZeros(χ, a), (zeroOrder(χ, r.val) : ℂ) *
            (1 / (z - (r.val - 1 / 2)) - 1 / (w z - (r.val - 1 / 2)))) atTop right(a) := by
  let R (n : ℕ) : ℝ := (n : ℝ) + 4
  let h (n : ℕ) (t : ℝ) := Real.smoothTransition (R n * (t - 1) - 1) * Real.smoothTransition (2 - t / R n)
  have hR (n : ℕ) : 4 ≤ R n := by dsimp [R]; exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hp (n : ℕ) : 0 < R n := by linarith [hR n]
  obtain ⟨ρ, ha, hρ⟩ := introTraceApprox_exists_dilated
  change IsIntroTraceApproximation h ρ at ha
  have hs (n : ℕ) : tsupport (h n) ⊆ Icc (1 + 1 / R n) (2 * R n) :=
    introTraceApprox_dilated_cutoff_support (hp n)
  have hmatch (n : ℕ) (t u : ℝ) (ht : h n t ≠ 0) (hu : ρ n u ≠ 0) :
      |u| ≤ 1 ∧ |u| ≤ t - 1 := by
    obtain ⟨hl,_⟩ := hs n (subset_tsupport _ ht)
    have hu' : |u| ≤ 1 / (2 * R n) := hρ n u hu
    have hsmall := one_div_lt_one_div_of_lt (hp n) (show R n < 2 * R n by linarith [hp n])
    exact ⟨hu'.trans ((div_le_one (by positivity)).2 (by linarith [hR n])), by linarith⟩
  refine ⟨h, ρ, ha, hmatch, ?_, ?_⟩
  · intro a m Z ha₀ ham hZ
    obtain ⟨B,hB,hweighted⟩ := introTraceApprox_single_dilated_weighted a m Z ha₀ ham hZ
    refine ⟨2*B,by positivity,?_⟩
    intro n z s hz hzN hsre
    have hupper : Icc (1 + 1/R n) (2*R n) ⊆ Ioo 1 (3*R n) := fun t ht ↦
      ⟨by linarith [ht.1,show 0 < 1/R n by positivity],by linarith [ht.2,hR n]⟩
    obtain ⟨ε, _, hε⟩ := ha.2.2.2
    obtain ⟨_,hsm,hnn,hsρ,hmass⟩ := hε n
    have hi : Integrable (ρ n) := hsm.continuous.integrable_of_hasCompactSupport
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsρ)
    rw [introTraceApprox_mellin_eq_translated (T := 3*R n) (by linarith [hR n])
      (ha.1 n).1.continuous ((hs n).trans hupper) hi hsm.continuous.measurable z s (ha₀.trans (ham.le.trans hz))]
    calc
      _ ≤ ∫ u : ℝ, ρ n u * (2*B / (1+|s.im|)) := by
        apply norm_integral_le_of_norm_le (hi.mul_const _)
        filter_upwards with u
        by_cases hu : ρ n u = 0
        · simp [hu]
        · rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hnn u)]
          apply mul_le_mul_of_nonneg_left _ (hnn u)
          obtain ⟨h0,h1⟩ := hweighted (R n) u z (hR n) (hρ n u hu) hz hzN
          obtain ⟨hreg,hsupp⟩ := introTraceApprox_single_dilated_support (hR n) (hρ n u hu) z
          apply introTraceMellin_le_of_first_deriv (by linarith [hR n]) (hreg.of_le (by decide)) (hsupp.trans hupper) h0 h1 s hsre
      _ = _ := by rw [integral_mul_const,hmass,one_mul]
  intro χ a ha₀ w hw hdw
  apply introTrace_spectral_referenceSub_of_bound χ a w hw hdw h ρ ha
  intro K hsub hK
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, .of_forall fun _ _ _ hz ↦ hz.elim⟩
  let S := K ∪ w '' K
  have hS : IsCompact S := hK.union (hK.image_of_continuousOn (hdw.continuousOn.mono hsub))
  have hSR : S ⊆ right(a) := union_subset hsub (fun _ ⟨q, hq, e⟩ ↦ e ▸ hw (hsub hq))
  obtain ⟨y, hy, hmin⟩ := hS.exists_isMinOn (hne.mono subset_union_left) Complex.continuous_re.continuousOn
  obtain ⟨Z, hZ⟩ := hS.isBounded.exists_norm_le
  have hym : a < y.re := hSR hy
  obtain ⟨B, _, hB⟩ := introTraceApprox_reference_dilated_weighted a y.re Z ha₀ hym
    ((norm_nonneg _).trans (hZ _ hy))
  refine ⟨4 * B, .of_forall fun n r z hz ↦ ?_⟩
  have h₁ : z ∈ S := Or.inl hz
  have h₂ : w z ∈ S := Or.inr (mem_image_of_mem _ hz)
  have hminz : y.re ≤ z.re := isMinOn_iff.mp hmin z h₁
  have hminw : y.re ≤ (w z).re := isMinOn_iff.mp hmin (w z) h₂
  have hz₀ := ha₀.trans (hym.le.trans hminz)
  have hw₀ := ha₀.trans (hym.le.trans hminw)
  have hsub' : Icc (1 + 1 / R n) (2 * R n) ⊆ Ioo 1 (3 * R n) := by
    intro t ht
    have hr : 0 < 1 / R n := by positivity
    exact ⟨by linarith [ht.1], by linarith [hp n,ht.2]⟩
  obtain ⟨ε, _, hρ'⟩ := ha.2.2.2
  obtain ⟨_, hsm, hnn, hsρ, hmass⟩ := hρ' n
  have hcompact := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsρ
  have hi : Integrable (ρ n) := hsm.continuous.integrable_of_hasCompactSupport hcompact
  apply introTraceApprox_mellin_sub_le_of_translated (T := 3 * R n) (by linarith [hp n,hR n])
    (ha.1 n).1.continuous ((hs n).trans hsub') hi hsm.continuous.measurable hnn hmass
    z (w z) (r.val - 1 / 2) hz₀ hw₀
  intro u hu
  have hu' : |u| ≤ 1 / (2 * R n) := hρ n u hu
  obtain ⟨h0,h2⟩ := hB (R n) u z (w z) (hR n) hu' hminz hminw (hZ z h₁) (hZ _ h₂)
  obtain ⟨hsm',hs'⟩ := introTraceApprox_reference_dilated_support (hR n) hu' z (w z)
  have hre : (r.val - 1 / 2).re ≤ a := by simpa using (abs_lt.mp r.property.2).2.le
  simpa only [Pi.mul_def, h, Complex.sub_im, Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero] using
    introTraceMellin_le_of_weighted_deriv (by linarith [hR n]) hsm' (hs'.trans hsub') h0 h2 _ hre

/-- The explicit spectral family has matched supports at the lower cutoff. This
same family can therefore be used in the archimedean limit. -/
private theorem introTraceApprox_exists_reference_spectral_matched :
    ∃ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ ∧
      (∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1) ∧
      ∀ (χ : U𝔽) (a : ℝ), 0 ≤ a → ∀ w : ℂ → ℂ, MapsTo w right(a) right(a) →
        DifferentiableOn ℂ w right(a) →
        TendstoLocallyUniformlyOn (fun n z ↦ introTraceSpectralSum χ approx(h, ρ, n, z) a -
          introTraceSpectralSum χ approx(h, ρ, n, (w z)) a)
          (fun z ↦ ∑' r : windowZeros(χ, a), (zeroOrder(χ, r.val) : ℂ) *
            (1 / (z - (r.val - 1 / 2)) - 1 / (w z - (r.val - 1 / 2)))) atTop right(a) := by
  obtain ⟨h, ρ, ha, hm, _, hl⟩ := introTraceApprox_exists_reference_and_sparse_moments (F := F)
  exact ⟨h, ρ, ha, hm, hl⟩

/-- Paper: §1.4.3, p. 29. One admissible family realizes the multiplicity-weighted
resolvent series for every character, every centered window of half-width `a ≥ 0`,
and every holomorphic reference map `w` from `Re z > a` into itself. At each cutoff
first sum the smoothed Mellin differences at `z` and `w z` over the entire window.
The cutoff limit is locally uniform on `Re z > a`. The same family gives the rational
real-place limit for the shift by two on `Re z > -1/2`.
Deviation: On each compact set `K`, estimate both parameters on `K ∪ w '' K`. Their
powers agree at one, which controls the lower transition of the matched cutoffs. -/
theorem introTraceApprox_exists_reference_spectral_limit :
    ∃ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ ∧
      TendstoLocallyUniformlyOn (fun n z ↦
        introTraceArchimedean (F := ℚ) 1 approx(h, ρ, n, z) Rat.infinitePlace -
        introTraceArchimedean (F := ℚ) 1 approx(h, ρ, n, (z + 2)) Rat.infinitePlace)
        (fun z ↦ 1 / (z + 1 / 2)) atTop right(-(1 / 2 : ℝ)) ∧
      ∀ (χ : U𝔽) (a : ℝ), 0 ≤ a → ∀ w : ℂ → ℂ, MapsTo w right(a) right(a) →
        DifferentiableOn ℂ w right(a) →
        TendstoLocallyUniformlyOn (fun n z ↦ introTraceSpectralSum χ approx(h, ρ, n, z) a -
          introTraceSpectralSum χ approx(h, ρ, n, (w z)) a)
          (fun z ↦ ∑' r : windowZeros(χ, a), (zeroOrder(χ, r.val) : ℂ) *
            (1 / (z - (r.val - 1 / 2)) - 1 / (w z - (r.val - 1 / 2)))) atTop right(a) := by
  obtain ⟨h, ρ, hA, hmatch, hs⟩ := introTraceApprox_exists_reference_spectral_matched (F := F)
  exact ⟨h, ρ, hA, introTraceApprox_rat_sub_shiftTwo_matched h ρ hA hmatch, hs⟩

/-- Paper: §1.4.3, p. 29. Subtract the value at `z+2` at each cutoff. For one
admissible smooth family, the differences of the full spectral sums converge
locally uniformly to the resolvent series on `Re z > a` for every character and
window of half-width `a ≥ 0`. For the same family the rational real-place
differences converge to `1/(z+1/2)` on `Re z > -1/2`.
Deviation: Dilate the transition at the upper cutoff and choose the width of the
additive mollifier below the distance of the lower cutoff from one. -/
theorem introTraceApprox_exists_shiftTwo_spectral_limit :
    ∃ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ ∧
      TendstoLocallyUniformlyOn (fun n z ↦
        introTraceArchimedean (F := ℚ) 1 approx(h, ρ, n, z) Rat.infinitePlace -
        introTraceArchimedean (F := ℚ) 1 approx(h, ρ, n, (z + 2)) Rat.infinitePlace)
        (fun z ↦ 1 / (z + 1 / 2)) atTop right(-(1 / 2 : ℝ)) ∧
      ∀ (χ : U𝔽) (a : ℝ), 0 ≤ a →
        TendstoLocallyUniformlyOn (fun n z ↦ introTraceSpectralSum χ approx(h, ρ, n, z) a -
          introTraceSpectralSum χ approx(h, ρ, n, (z + 2)) a)
          (fun z ↦ ∑' r : windowZeros(χ, a), (zeroOrder(χ, r.val) : ℂ) *
            (1 / (z - (r.val - 1 / 2)) - 1 / (z + 2 - (r.val - 1 / 2)))) atTop right(a) := by
  obtain ⟨h, ρ, hA, harch, hspec⟩ := introTraceApprox_exists_reference_spectral_limit (F := F)
  refine ⟨h, ρ, hA, harch, fun χ a ha ↦ hspec χ a ha (fun z ↦ z + 2) ?_ (by fun_prop)⟩
  intro z hz
  change a < z.re at hz
  change a < (z + 2).re
  simpa using (show a < z.re + 2 by linarith)

/-- At real parameters two and four the power difference is a nonnegative real function. -/
private theorem introTraceApprox_exists_rat_sub_shiftTwo_unmatched_power (x : ℝ) :
    introTracePower 2 x - introTracePower 4 x =
      ((if 1 < x then (x ^ 2 - 1) / x ^ 4 else 0 : ℝ) : ℂ) := by
  by_cases hx : 1 < x
  · have hn : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    simp only [introTracePower, hx, ite_true, Complex.cpow_neg, Complex.cpow_ofNat]
    push_cast
    field_simp
  · simp [introTracePower, hx]

/-- A mollifier supported between `-ε` and `-ε/2` leaves a contribution of order
`ε log (1/d)` when the cutoff already equals one on `[1+d,2]`. -/
private theorem introTraceApprox_exists_rat_sub_shiftTwo_unmatched_lower (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (n : ℕ) {ε d : ℝ}
    (he : 0 < ε) (he1 : ε ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hcut : ∀ t ∈ Icc (1 + d) 2, h n t = 1)
    (hs : ∀ u, ρ n u ≠ 0 → u ∈ Icc (-ε) (-ε / 2)) :
    ε / 324 * Real.log (1 / d) ≤
      (introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) 2) Rat.infinitePlace -
       introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) 4) Rat.infinitePlace).re := by
  let P := fun x : ℝ ↦ if 1 < x then (x ^ 2 - 1) / x ^ 4 else 0
  let b := fun t : ℝ ↦ h n t * ∫ u, ρ n u * P (t - u)
  let g := fun t : ℝ ↦ |t|⁻¹ * (b |t| * Real.sqrt |t| / |1 - t|)
  let f := fun z : ℂ ↦ introTraceApprox (h n) (ρ n) z
  let W := fun (z : ℂ) (t : ℝ) ↦ ((|t|⁻¹ : ℝ) : ℂ) *
    (f z |t| * (Real.sqrt |t| : ℂ) / ((|1 - t| : ℝ) : ℂ))
  obtain ⟨_, _, hρ⟩ := hA.2.2.2
  obtain ⟨_, hsm, hpos, hsupp, hmass⟩ := hρ n
  have hc : HasCompactSupport (ρ n) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hr : Integrable (ρ n) := hsm.continuous.integrable_of_hasCompactSupport hc
  have hi (t : ℝ) (z : ℂ) : Integrable (fun u : ℝ ↦ (ρ n u : ℂ) * introTracePower z (t - u)) :=
    (hc.comp_left (g := Complex.ofReal) (by simp)).convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ)
      (Complex.continuous_ofReal.comp hsm.continuous) (introTracePower_locallyIntegrable z) t
  -- Express the convolution difference as an integral of a nonnegative real function.
  have hpt (t u : ℝ) : (ρ n u : ℂ) * introTracePower 2 (t - u) -
      (ρ n u : ℂ) * introTracePower 4 (t - u) = ((ρ n u * P (t - u) : ℝ) : ℂ) := by
    rw [← mul_sub, introTraceApprox_exists_rat_sub_shiftTwo_unmatched_power, Complex.ofReal_mul]
  have hpre (t : ℝ) : Integrable (fun u ↦ ρ n u * P (t - u)) := by
    exact ((hi t 2).sub (hi t 4)).re.congr (.of_forall fun u ↦ by
      change ((ρ n u : ℂ) * _ - (ρ n u : ℂ) * _).re = _
      rw [hpt, Complex.ofReal_re])
  have hb (t : ℝ) : f 2 t - f 4 t = (b t : ℂ) := by
    dsimp only [f, introTraceApprox, b]
    rw [← mul_sub, ← integral_sub (hi t 2) (hi t 4), Complex.ofReal_mul, ← integral_complex_ofReal]
    congr 1
    exact integral_congr_ae (.of_forall fun u ↦ hpt t u)
  have hP0 (x : ℝ) : 0 ≤ P x := by
    dsimp only [P]
    split_ifs with ht
    · exact div_nonneg (by nlinarith) (by positivity)
    · exact le_rfl
  have hb0 (t : ℝ) : 0 ≤ b t := mul_nonneg ((hA.1 n).2.2.2 t).1
    (integral_nonneg fun u ↦ mul_nonneg (hpos _) (hP0 _))
  have hbl (t : ℝ) (ht : t ∈ Icc (1 + d) 2) : ε / 81 ≤ b t := by
    dsimp only [b]
    rw [hcut t ht, one_mul]
    calc ε / 81 = ∫ u, ρ n u * (ε / 81) := by rw [integral_mul_const, hmass, one_mul]
         _ ≤ _ := integral_mono (hr.mul_const _) (hpre t) fun u ↦ by
           by_cases hu : ρ n u = 0
           · simp [hu]
           obtain ⟨hlo, hhi⟩ := hs u hu
           obtain ⟨ht₁, ht₂⟩ := ht
           have hv : 1 < t - u := by linarith
           have h3 : t - u ≤ 3 := by linarith
           have h4 : (t - u) ^ 4 ≤ 81 := by
             simpa only [show (3 : ℝ) ^ 4 = 81 by norm_num] using
               pow_le_pow_left₀ (by linarith : 0 ≤ t - u) h3 4
           apply mul_le_mul_of_nonneg_left _ (hpos u)
           rw [show P (t - u) = ((t - u) ^ 2 - 1) / (t - u) ^ 4 by simp [P, hv]]
           apply (le_div_iff₀ (pow_pos (by linarith) 4)).2
           calc ε / 81 * (t - u) ^ 4 ≤ ε / 81 * 81 := by gcongr
                _ ≤ (t - u) ^ 2 - 1 := by nlinarith [sq_nonneg (t - u - 1)]
  -- Pass to the real coordinate and retain the positive branch on the shell.
  have hW (z : ℂ) : Integrable (W z) := by
    obtain ⟨hcon, hcom⟩ := introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n z
    exact introTraceApprox_rat_sub_shiftTwo_integrable _ hcon hcom (introTraceApprox_support h ρ hA n z)
  have hWe (t : ℝ) : W 2 t - W 4 t = (g t : ℂ) := by
    dsimp only [W, g]
    push_cast
    rw [← hb]
    ring
  have hgi : Integrable g := ((hW 2).sub (hW 4)).re.congr (.of_forall fun t ↦ by
    change (W 2 t - W 4 t).re = _
    rw [hWe, Complex.ofReal_re])
  have heq :
      (introTraceArchimedean (F := ℚ) 1 (f 2) Rat.infinitePlace -
       introTraceArchimedean (F := ℚ) 1 (f 4) Rat.infinitePlace).re = (∫ t, g t) / 2 := by
    have hm (z : ℂ) := (introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n z).1.measurable
    rw [introTraceArchimedean_rat_sub_shiftTwo_integral _ (hm 2),
        introTraceArchimedean_rat_sub_shiftTwo_integral _ (hm 4), ← mul_sub]
    change ((1 / 2 : ℂ) * ((∫ t, W 2 t) - ∫ t, W 4 t)).re = _
    rw [← integral_sub (hW 2) (hW 4), integral_congr_ae (.of_forall hWe), integral_complex_ofReal]
    simp [Complex.mul_re, div_eq_mul_inv, mul_comm]
  have hg0 (t : ℝ) : 0 ≤ g t := by
    exact mul_nonneg (by positivity)
      (div_nonneg (mul_nonneg (hb0 _) (Real.sqrt_nonneg _)) (abs_nonneg _))
  have hgl (t : ℝ) (ht : t ∈ Icc (1 + d) 2) : (ε / 162) * (t - 1)⁻¹ ≤ g t := by
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 1 < t := by linarith [ht.1]
    have hroot : 1 ≤ Real.sqrt t := by simpa using Real.sqrt_le_sqrt ht1.le
    have hinv : 1 / 2 ≤ t⁻¹ := by simpa only [one_div] using inv_anti₀ ht0 ht.2
    have hcoeff := mul_le_mul (hbl t ht) hroot (by norm_num) (hb0 t)
    dsimp only [g]
    rw [abs_of_pos ht0, abs_sub_comm, abs_of_pos (sub_pos.mpr ht1)]
    calc (ε / 162) * (t - 1)⁻¹ = (1 / 2) * ((ε / 81 * 1) / (t - 1)) := by ring
         _ ≤ _ := mul_le_mul hinv (div_le_div_of_nonneg_right hcoeff (by linarith))
           (by positivity) (inv_nonneg.mpr ht0.le)
  have hab : 1 + d ≤ 2 := by linarith
  -- Integrating the reciprocal distance to one gives the logarithmic lower bound.
  have hIi : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume (1 + d) 2 := by
    rw [intervalIntegrable_sub_inv_iff]
    exact Or.inr (by rw [uIcc_of_le hab]; exact fun hx ↦ by linarith [hx.1])
  have hIl := intervalIntegral.integral_mono_on hab (hIi.const_mul (ε / 162)) hgi.intervalIntegrable hgl
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x⁻¹) (1 : ℝ)] at hIl
  have hstep : 1 + d - 1 = d := by ring
  rw [hstep, show (2 : ℝ) - 1 = 1 by norm_num, integral_inv_of_pos hd zero_lt_one,
    intervalIntegral.integral_of_le hab] at hIl
  have hTot := setIntegral_le_integral (s := Ioc (1 + d) 2) hgi (.of_forall hg0)
  change _ ≤ (introTraceArchimedean (F := ℚ) 1 (f 2) Rat.infinitePlace -
       introTraceArchimedean (F := ℚ) 1 (f 4) Rat.infinitePlace).re
  rw [heq]
  linarith

/-- Paper: §1.4.2–§1.4.3, pp. 28–29. For one admissible pair the real part of the
rational real-place difference at two and four tends to positive infinity.
Deviation: The reference subtraction is a proposed regularization of the real-place
term. With `N = n + 1` the mollifier is supported in `[-1/N,-1/(2N)]` and the cutoff
equals one on `[1+exp(-N²),2]`, giving a lower bound of `N/324`. -/
theorem introTraceApprox_exists_rat_sub_shiftTwo_unmatched :
    ∃ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ ∧
      Tendsto (fun n ↦ (introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) 2) Rat.infinitePlace -
        introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) 4) Rat.infinitePlace).re) atTop atTop := by
  let N (n : ℕ) : ℝ := (n : ℝ) + 1
  let ε (n : ℕ) : ℝ := 1 / N n
  let d (n : ℕ) := Real.exp (-(N n) ^ 2)
  let k (n : ℕ) := n + ⌈2 * Real.exp ((N n) ^ 2)⌉₊
  let R (j : ℕ) : ℝ := (j : ℝ) + 4
  let H (j : ℕ) (t : ℝ) := Real.smoothTransition (R j * (t - 1) - 1) * Real.smoothTransition (2 - t / R j)
  obtain ⟨_, hA, _⟩ := introTraceApprox_exists_dilated
  change IsIntroTraceApproximation H _ at hA
  have hN (n : ℕ) : 0 < N n := by dsimp [N]; positivity
  have he (n : ℕ) : 0 < ε n := one_div_pos.mpr (hN n)
  have he1 (n : ℕ) : ε n ≤ 1 := (div_le_one (hN n)).2 (by dsimp [N]; linarith)
  let b (n : ℕ) : ContDiffBump (-3 * ε n / 4) :=
    ⟨ε n / 8, ε n / 4, by linarith [he n], by linarith [he n]⟩
  let ρ (n : ℕ) := (b n).normed volume
  have hneg (n : ℕ) : tsupport (ρ n) ⊆ Icc (-ε n) (-ε n / 2) := by
    dsimp only [ρ]
    rw [(b n).tsupport_normed_eq, Real.closedBall_eq_Icc]
    exact Icc_subset_Icc (by dsimp [b]; linarith) (by dsimp [b]; linarith)
  have hmono : Monotone k := by
    intro i j hij
    have hij' : N i ≤ N j := by dsimp [N]; exact_mod_cast (Nat.add_le_add_right hij 1)
    exact Nat.add_le_add hij (Nat.ceil_mono (by gcongr))
  have hk : Tendsto k atTop atTop := tendsto_atTop_mono (fun n ↦ Nat.le_add_right n _) tendsto_id
  have hfamily : IsIntroTraceApproximation (H ∘ k) ρ := by
    refine ⟨fun _ ↦ hA.1 _, hA.2.1.comp hmono, fun t ht ↦ (hA.2.2.1 t ht).comp hk,
      ε, tendsto_one_div_add_atTop_nhds_zero_nat, fun n ↦ ?_⟩
    refine ⟨he n, (b n).contDiff_normed, (b n).nonneg_normed,
      (hneg n).trans (Icc_subset_Icc le_rfl (by linarith [he n])), (b n).integral_normed⟩
  have hbound (n : ℕ) :
      N n / 324 ≤ (introTraceArchimedean (F := ℚ) 1 (introTraceApprox ((H ∘ k) n) (ρ n) 2) Rat.infinitePlace -
        introTraceArchimedean (F := ℚ) 1 (introTraceApprox ((H ∘ k) n) (ρ n) 4) Rat.infinitePlace).re := by
    have hd : 0 < d n := Real.exp_pos _
    have hd1 : d n ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
    have hR : 2 * Real.exp ((N n) ^ 2) ≤ R (k n) := by
      have hceil := Nat.le_ceil (2 * Real.exp ((N n) ^ 2))
      dsimp only [R, k]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hR₀ : 4 ≤ R (k n) := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) (k n)]
    have hcut (t : ℝ) (ht : t ∈ Icc (1 + d n) 2) : (H ∘ k) n t = 1 := by
      have hdR : 2 ≤ R (k n) * d n := by
        dsimp only [d]; rw [Real.exp_neg]
        simpa only [div_eq_mul_inv] using (le_div_iff₀ (Real.exp_pos _)).2 hR
      have hlt : 1 ≤ R (k n) * (t - 1) - 1 := by
        have := mul_le_mul_of_nonneg_left (show d n ≤ t - 1 by linarith [ht.1]) (by linarith : 0 ≤ R (k n))
        linarith
      have hrt : 1 ≤ 2 - t / R (k n) := by
        have := (div_le_one (by linarith : 0 < R (k n))).2 (show t ≤ R (k n) by linarith [ht.2])
        linarith
      simp [H, Real.smoothTransition.one_of_one_le hlt, Real.smoothTransition.one_of_one_le hrt]
    have hlog : Real.log (1 / d n) = (N n) ^ 2 := by simp [d, Real.exp_neg]
    have hl := introTraceApprox_exists_rat_sub_shiftTwo_unmatched_lower (H ∘ k) ρ hfamily n (he n) (he1 n) hd hd1 hcut
      (fun u hu ↦ hneg n (subset_tsupport _ hu))
    rw [hlog] at hl
    convert hl using 1
    dsimp only [ε]
    field_simp [(hN n).ne']
  refine ⟨H ∘ k, ρ, hfamily, tendsto_atTop_mono hbound ?_⟩
  refine tendsto_atTop.2 fun M ↦ ?_
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (324 * M)] with n hn
  dsimp [N]
  linarith

/-- Paper: §1.4.3, p. 29. The shift-by-two rational real-place limit fails for
some admissible pairs on their original common index. The obstruction occurs at two.
Deviation: The preceding counterexample tests the proposed reference subtraction.
The cofinal reindexing in `introTraceApprox_rat_sub_shiftTwo_tendsto` gives the
locally uniform limit for each initial pair. -/
theorem introTraceApprox_not_forall_rat_sub_shiftTwo :
    ¬ ∀ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ →
      TendstoLocallyUniformlyOn (fun n z ↦
        introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) z) Rat.infinitePlace -
        introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) (z + 2)) Rat.infinitePlace)
        (fun z ↦ 1 / (z + 1 / 2)) atTop right(-(1 / 2 : ℝ)) := by
  obtain ⟨h, ρ, hA, hdiv⟩ := introTraceApprox_exists_rat_sub_shiftTwo_unmatched
  intro hlim
  have hp := (hlim h ρ hA).tendsto_at (a := (2 : ℂ)) (by
    change -(1 / 2 : ℝ) < (2 : ℂ).re
    norm_num)
  apply not_tendsto_nhds_of_tendsto_atTop hdiv _
  simpa only [show (2 : ℂ) + 2 = 4 by norm_num, Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp hp

/-- At parameter two the radial approximant is real and nonnegative. -/
private theorem introTraceApprox_rat_spectral_tendsto_atBot_profile (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (n : ℕ) :
    ∃ g : ℝ → ℝ, (∀ t, 0 ≤ g t) ∧ approx(h, ρ, n, (2 : ℂ)) = fun t ↦ (g t : ℂ) := by
  let P (x : ℝ) : ℝ := if 1 < x then (x ^ 2)⁻¹ else if x = 1 then 1 / 2 else 0
  have hP (x : ℝ) : introTracePower 2 x = (P x : ℂ) := by
    unfold introTracePower P
    split_ifs <;> norm_num [Complex.cpow_neg]
  obtain ⟨ε, _, hρ⟩ := hA.2.2.2
  refine ⟨fun t ↦ h n t * ∫ u, ρ n u * P (t - u), fun t ↦ ?_, ?_⟩
  · apply mul_nonneg ((hA.1 n).2.2.2 t).1
    apply integral_nonneg
    intro u
    apply mul_nonneg ((hρ n).2.2.1 u)
    unfold P
    split_ifs <;> positivity
  · funext t
    simp only [introTraceApprox, hP, ← Complex.ofReal_mul, integral_complex_ofReal]

/-- Fatou’s lemma makes nonnegative cutoff integrals diverge when they eventually dominate a
nonintegrable density pointwise on a measurable set. -/
private theorem introTraceApprox_trivial_archimedean_fatou {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (q : ℕ → E → ℝ) (B : E → ℝ) (S : Set E) (hS : MeasurableSet S)
    (hi : ∀ n, Integrable (q n) μ) (hq : ∀ n x, 0 ≤ q n x)
    (hm : Measurable B) (hB : ∀ x, 0 ≤ B x) (hbig : ¬ IntegrableOn B S μ)
    (hlo : ∀ x ∈ S, ∀ᶠ n in atTop, B x ≤ q n x) :
    Tendsto (fun n ↦ ∫ x, q n x ∂μ) atTop atTop := by
  let X (n : ℕ) := ∫⁻ x, ENNReal.ofReal (q n x) ∂μ
  have htop : ∫⁻ x in S, ENNReal.ofReal (B x) ∂μ = ⊤ := by
    by_contra hn
    exact hbig ((lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (ae_of_all _ hB)).1 hn)
  have hlim : liminf X atTop = ⊤ := by
    apply top_le_iff.mp
    calc
      (⊤ : ENNReal) = ∫⁻ x in S, ENNReal.ofReal (B x) ∂μ := htop.symm
      _ ≤ ∫⁻ x in S, liminf (fun n ↦ ENNReal.ofReal (q n x)) atTop ∂μ := by
        apply setLIntegral_mono' hS
        intro x hx
        exact le_liminf_of_le (by isBoundedDefault) ((hlo x hx).mono (fun _ hn ↦ ENNReal.ofReal_le_ofReal hn))
      _ ≤ ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (q n x)) atTop ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl
      _ ≤ liminf X atTop := lintegral_liminf_le' (fun n ↦ ENNReal.measurable_ofReal.comp_aemeasurable (hi n).aemeasurable)
  apply tendsto_atTop.mpr
  intro c
  have hlt : ENNReal.ofReal (max c 0) < liminf X atTop := by simpa only [hlim] using ENNReal.ofReal_lt_top
  filter_upwards [eventually_lt_of_lt_liminf hlt] with n hn
  have hi' := (lintegral_ofReal_ne_top_iff_integrable (hi n).aestronglyMeasurable (ae_of_all _ (hq n))).2 (hi n)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hq n)) (hi n).aestronglyMeasurable]
  exact (le_max_left _ _).trans ((ENNReal.ofReal_lt_iff_lt_toReal (le_max_right _ _) hi').mp hn).le

/-- The logarithmic test is supported on positive coordinates. -/
private theorem introTraceApprox_spectral_tendsto_atBot_log_support (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    tsupport (fun x ↦ introTraceApprox (h n) (ρ n) z (Real.exp x)) ⊆ Ioi 0 := by
  intro x hx
  have hcont : Continuous Real.exp := Real.continuous_exp
  have hsub : tsupport (fun x ↦ introTraceApprox (h n) (ρ n) z (Real.exp x)) ⊆
      Real.exp ⁻¹' tsupport (introTraceApprox (h n) (ρ n) z) := by
    apply closure_minimal
    · intro a ha
      exact subset_tsupport _ ha
    · exact (isClosed_tsupport _).preimage hcont
  exact Real.one_lt_exp_iff.mp (introTraceApprox_support h ρ hA n z (hsub hx))

/-- On the closed right half-plane, averaging a cutoff power against a probability mollifier preserves its unit bound. -/
private theorem introTraceApprox_euler_norm (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) (hz : 0 ≤ z.re) (x : ℝ) :
    ‖introTraceApprox (h n) (ρ n) z x‖ ≤ 1 := by
  obtain ⟨ε, _, hρ⟩ := hA.2.2.2
  have hi : Integrable (ρ n) volume := (hρ n).2.1.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hρ n).2.2.2.1)
  have hb : ‖∫ u : ℝ, (ρ n u : ℂ) * introTracePower z (x-u)‖ ≤ ∫ u, ρ n u := by
    apply norm_integral_le_of_norm_le hi
    exact .of_forall fun u ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((hρ n).2.2.1 _)]
      exact mul_le_of_le_one_right ((hρ n).2.2.1 _) (introTracePower_norm_le_one hz _)
  rw [(hρ n).2.2.2.2] at hb
  rw [introTraceApprox, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((hA.1 n).2.2.2 _).1]
  exact (mul_le_of_le_one_right ((hA.1 n).2.2.2 _).1 hb).trans ((hA.1 n).2.2.2 _).2

/-- At parameter two, convolution against a probability mollifier preserves the unit bound. -/
private theorem introTraceApprox_spectral_tendsto_atBot_log_norm (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (n : ℕ) (x : ℝ) :
    ‖introTraceApprox (h n) (ρ n) 2 x‖ ≤ 1 := by
  exact introTraceApprox_euler_norm h ρ hA n 2 (by norm_num) x

/-- A compact positive-coordinate profile vanishes near the gamma kernel’s singularity. -/
private theorem introTraceApprox_spectral_tendsto_atBot_integrable_weight
    {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) (h0 : 0 ∉ tsupport f)
    {k : ℝ} (hk : 0 < k) (p : ℂ) :
    Integrable (fun t : ℝ ↦ (k : ℂ) * f (k*t) * Complex.exp (-p * t) / (1 - (Real.exp (-t) : ℂ))) := by
  let H := fun t : ℝ ↦ (k : ℂ) * f (k*t) * Complex.exp (-p * t) / (1 - (Real.exp (-t) : ℂ))
  have hz : ∀ᶠ t in 𝓝 (0 : ℝ), f (k*t) = 0 := by
    have he := notMem_tsupport_iff_eventuallyEq.mp h0
    have ht : Tendsto (fun t : ℝ ↦ k*t) (𝓝 0) (𝓝 0) := by
      have c : Continuous (fun t : ℝ ↦ k*t) := by fun_prop
      simpa using c.tendsto 0
    exact ht.eventually he
  have hc : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hz] with t ht
      simp [H, ht]
    · have he : (1:ℂ) - (Real.exp (-x) : ℂ) ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (show (1:ℝ) ≠ Real.exp (-x) from fun h ↦ hx (by
          have hh : Real.exp 0 = Real.exp (-x) := by simpa using h
          linarith [Real.exp_injective hh]))
      have hu : ContinuousAt (fun t : ℝ ↦ (k : ℂ) * f (k*t) * Complex.exp (-p * t)) x := by fun_prop
      have hd : ContinuousAt (fun t : ℝ ↦ (1:ℂ) - (Real.exp (-t) : ℂ)) x := by fun_prop
      exact hu.div hd he
  have hsc : HasCompactSupport (fun t : ℝ ↦ f (k*t)) :=
    hs.comp_homeomorph (Homeomorph.mulLeft₀ k hk.ne')
  apply hc.integrable_of_hasCompactSupport
  apply hsc.mono
  intro t ht
  exact fun h ↦ ht (by simp [H, h])

/-- A nonnegative part diverges if it eventually dominates a multiple of the reciprocal
coordinate on a right neighborhood of zero. -/
private theorem introTraceApprox_spectral_tendsto_atBot_singular {c δ : ℝ} (hc : 0 < c) (hd : 0 < δ)
    (w : ℕ → ℝ → ℝ) (hi : ∀ n, IntegrableOn (w n) (Ioi 0))
    (hl : ∀ t ∈ Ioo (0 : ℝ) δ, ∀ᶠ n in atTop, c / t ≤ w n t) :
    Tendsto (fun n ↦ ∫ t in Ioi (0 : ℝ), max (w n t) 0) atTop atTop := by
  let B := fun t : ℝ ↦ c * |t|⁻¹
  have hbad : ¬ IntegrableOn B (Ioo 0 δ) (volume.restrict (Ioi 0)) := by
    intro h
    rw [IntegrableOn, Measure.restrict_restrict_of_subset Ioo_subset_Ioi_self] at h
    have h' : IntegrableOn (fun t : ℝ ↦ t ^ (-1 : ℝ)) (Ioo 0 δ) := by
      have hi : IntegrableOn (fun t ↦ c⁻¹ * B t) (Ioo (0 : ℝ) δ) := h.const_mul _
      apply hi.congr_fun _ measurableSet_Ioo
      intro t ht
      simp [B, abs_of_pos ht.1, hc.ne', Real.rpow_neg_one]
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff hd).mp h'
    linarith
  apply introTraceApprox_trivial_archimedean_fatou (volume.restrict (Ioi 0))
    (fun n t ↦ max (w n t) 0) B (Ioo 0 δ) measurableSet_Ioo (fun n ↦ (hi n).pos_part)
    (fun n t ↦ le_max_right _ _) (by dsimp [B]; fun_prop) (fun t ↦ by dsimp [B]; positivity) hbad
  intro t ht
  filter_upwards [hl t ht] with n hn
  exact (show B t ≤ w n t by simpa [B, abs_of_pos ht.1, div_eq_mul_inv] using hn).trans (le_max_left _ _)

/-- For one-sided profiles converging to the parameter-two power, the real part of the
digamma integral tends to minus infinity. The positive part of the opposite integrand dominates
a reciprocal near zero, and its negative part has a uniform exponential majorant. -/
private theorem introTraceApprox_spectral_tendsto_atBot_gamma (b : ℕ → ℝ → ℝ)
    (hbc : ∀ n, Continuous (b n)) (hbs : ∀ n, HasCompactSupport (b n))
    (hpos : ∀ n, tsupport (b n) ⊆ Ioi 0) (hb : ∀ n t, b n t ∈ Icc (0:ℝ) 1)
    (hlim : ∀ t : ℝ, 0 < t → Tendsto (fun n ↦ b n t) atTop (𝓝 (Real.exp (-2*t))))
    {k : ℝ} (hk : 0 < k) (p q : ℂ) (hpr : 0 < p.re) :
    Tendsto (fun n ↦ (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k p q
      (fun u ↦ (b n u : ℂ)) t).re) atTop atBot := by
  let G (n : ℕ) (t : ℝ) : ℂ := (k : ℂ) * (b n (k*t) : ℂ) * Complex.exp (-p * t) /
    (1 - (Real.exp (-t) : ℂ))
  have hI (n : ℕ) : Integrable (G n) := by
    apply introTraceApprox_spectral_tendsto_atBot_integrable_weight (Complex.continuous_ofReal.comp (hbc n))
      ((hbs n).comp_left Complex.ofReal_zero) _ hk
    have hsub : tsupport (fun u ↦ (b n u : ℂ)) ⊆ tsupport (b n) :=
      closure_mono (fun u hu ↦ fun h ↦ hu (by simp [h]))
    exact fun h ↦ lt_irrefl (0:ℝ) (hpos n (hsub h))
  have hReal (n : ℕ) (t : ℝ) : (G n t).re =
      k * b n (k*t) * (Complex.exp (-p*t)).re / (1-Real.exp (-t)) := by
    dsimp [G]
    rw [show (1:ℂ) - (Real.exp (-t) : ℂ) = ((1-Real.exp (-t):ℝ):ℂ) by push_cast; rfl,
      Complex.div_ofReal_re]
    simp [Complex.mul_re, Complex.mul_im]
  have hphase : ∀ᶠ t : ℝ in 𝓝 0, 1/2 < (Complex.exp (-p*t)).re := by
    have hcont : Continuous (fun t : ℝ ↦ (Complex.exp (-p*t)).re) := by fun_prop
    exact continuousAt_const.eventually_lt (hcont.continuousAt (x := 0)) (by norm_num)
  obtain ⟨e, he, hphase'⟩ := Metric.eventually_nhds_iff.mp hphase
  let δ := min e 1
  have hδ : 0 < δ := lt_min he zero_lt_one
  let a := Real.exp (-2*k)/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hden {t : ℝ} (ht : 0 < t) : 0 < 1-Real.exp (-t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hphaseδ {t : ℝ} (ht : 0 < t) (htδ : t < δ) : 1/2 ≤ (Complex.exp (-p*t)).re :=
    (hphase' (show dist t 0 < e by simpa [Real.dist_eq, abs_of_pos ht] using htδ.trans_le (min_le_left e 1))).le
  have hU := introTraceApprox_spectral_tendsto_atBot_singular (show 0 < k*a/2 by positivity) hδ
    (fun n t ↦ (G n t).re) (fun n ↦ (hI n).integrableOn.re) (fun t ht ↦ by
      have ha' : a < Real.exp (-2*(k*t)) := by
        have ht1 := ht.2.trans_le (min_le_right e 1)
        have hle : Real.exp (-2*k) ≤ Real.exp (-2*(k*t)) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left ht1.le hk.le])
        dsimp [a]
        linarith [Real.exp_pos (-2*k)]
      filter_upwards [(hlim _ (mul_pos hk ht.1)).eventually (lt_mem_nhds ha')] with n hn
      rw [hReal]
      have hD : 1-Real.exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
      calc
        k*a/2/t ≤ (k*a/2)/(1-Real.exp (-t)) := div_le_div_of_nonneg_left (by positivity) (hden ht.1) hD
        _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ (hden ht.1).le
          have hh := mul_le_mul hn.le (hphaseδ ht.1 ht.2) (by norm_num) (hb n _).1
          nlinarith [mul_le_mul_of_nonneg_left hh hk.le])
  let D := k/(1-Real.exp (-δ))
  have hDpos : 0 < D := div_pos hk (hden hδ)
  let E (t : ℝ) := D * Real.exp (-p.re*t)
  have hE : IntegrableOn E (Ioi 0) := (exp_neg_integrableOn_Ioi 0 hpr).const_mul D
  have hneg (n : ℕ) : (∫ t in Ioi (0:ℝ), max (-(G n t).re) 0) ≤ ∫ t in Ioi (0:ℝ), E t := by
    refine setIntegral_mono_on (hI n).integrableOn.re.neg_part hE measurableSet_Ioi (fun t ht ↦ ?_)
    change 0 < t at ht
    have hEt : 0 ≤ E t := mul_nonneg hDpos.le (Real.exp_pos _).le
    apply max_le _ hEt
    rw [hReal]
    by_cases hs : t < δ
    · apply le_trans _ hEt
      have hh := hphaseδ ht hs
      exact neg_nonpos.mpr (div_nonneg (mul_nonneg (mul_nonneg hk.le (hb n _).1) (by linarith)) (hden ht).le)
    · have hdt : 1-Real.exp (-δ) ≤ 1-Real.exp (-t) := by
        have hh := Real.exp_le_exp.mpr (neg_le_neg (le_of_not_gt hs))
        linarith
      have hnorm : ‖Complex.exp (-p*t)‖ = Real.exp (-p.re*t) := by simp [Complex.norm_exp, Complex.mul_re]
      have hnegRe : -(Complex.exp (-p*t)).re ≤ Real.exp (-p.re*t) := by
        rw [← hnorm]
        exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      rw [← neg_div, show -(k*b n (k*t)*(Complex.exp (-p*t)).re) = k*b n (k*t)*(-(Complex.exp (-p*t)).re) by ring]
      calc
        _ ≤ (k * Real.exp (-p.re*t))/(1-Real.exp (-t)) := by
          apply div_le_div_of_nonneg_right _ (hden ht).le
          exact (mul_le_mul_of_nonneg_left hnegRe (mul_nonneg hk.le (hb n _).1)).trans
            (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hk.le (hb n _).2) (Real.exp_pos _).le)
        _ ≤ (k * Real.exp (-p.re*t))/(1-Real.exp (-δ)) := div_le_div_of_nonneg_left (by positivity) (hden hδ) hdt
        _ = E t := by dsimp [E,D]; ring
  have hK (n : ℕ) : (∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel k p q
      (fun u ↦ (b n u : ℂ)) t).re = -(∫ t in Ioi (0:ℝ), (G n t).re) := by
    have hz {u : ℝ} (hu : u ≤ 0) : b n u = 0 := image_eq_zero_of_notMem_tsupport
      (fun hh ↦ hu.not_gt (hpos n hh))
    have hh : (∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel k p q
        (fun u ↦ (b n u : ℂ)) t) = ∫ t in Ioi (0:ℝ), -G n t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change 0 < t at ht
      simp [heckeArchimedeanDigammaKernel, G, hz (u := 0) le_rfl, hz (neg_nonpos.mpr (mul_nonneg hk.le ht.le))]
      ring
    rw [hh, integral_neg, Complex.neg_re]
    exact congrArg Neg.neg (integral_re ((hI n).integrableOn (s := Ioi (0:ℝ)))).symm
  apply tendsto_atBot.mpr
  intro M
  filter_upwards [tendsto_atTop.mp hU ((∫ t in Ioi (0:ℝ), E t) - M)] with n hn
  have heq : (∫ t in Ioi (0:ℝ), (G n t).re) = (∫ t in Ioi (0:ℝ), max (G n t).re 0) -
      ∫ t in Ioi (0:ℝ), max (-(G n t).re) 0 := by
    have hR : Integrable (fun t : ℝ ↦ (G n t).re) (volume.restrict (Ioi (0 : ℝ))) :=
      ((hI n).integrableOn (s := Ioi (0 : ℝ))).re
    calc
      _ = ∫ t in Ioi (0:ℝ), max (G n t).re 0 - max (-(G n t).re) 0 :=
        setIntegral_congr_fun measurableSet_Ioi (fun t _ ↦ (posPart_sub_negPart _).symm)
      _ = _ := integral_sub hR.pos_part hR.neg_part
  rw [hK, heq]
  linarith [hneg n]

/-- Each positive-coordinate radial approximant at parameter two satisfies the one-sided
digamma estimate. -/
private theorem introTraceApprox_spectral_tendsto_atBot_gamma_profile (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) {k : ℝ} (hk : 0 < k) (p q : ℂ) (hp : 0 < p.re) :
    Tendsto (fun n ↦ (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k p q
      (fun u ↦ introTraceApprox (h n) (ρ n) 2 (Real.exp u)) t).re) atTop atBot := by
  let b (n : ℕ) (t : ℝ) := (introTraceApprox (h n) (ρ n) 2 (Real.exp t)).re
  have hval (n : ℕ) (t : ℝ) : introTraceApprox (h n) (ρ n) 2 (Real.exp t) = (b n t : ℂ) := by
    obtain ⟨g, _, hg⟩ := introTraceApprox_rat_spectral_tendsto_atBot_profile h ρ hA n
    simp [b, hg]
  have hbe (n : ℕ) : (fun u ↦ introTraceApprox (h n) (ρ n) 2 (Real.exp u)) =
      fun u ↦ (b n u : ℂ) := funext (hval n)
  simp_rw [hbe]
  apply introTraceApprox_spectral_tendsto_atBot_gamma b _ _ _ _ _ hk p q hp
  · intro n
    exact Complex.continuous_re.comp (introTraceApprox_logProfile h ρ hA n 2).1.continuous
  · intro n
    exact (introTraceApprox_logProfile h ρ hA n 2).2.comp_left (g := Complex.re) (by simp)
  · intro n
    refine (closure_mono (fun t ht ↦ ?_)).trans (introTraceApprox_spectral_tendsto_atBot_log_support h ρ hA n 2)
    intro h0
    exact ht (by simp [b,h0])
  · intro n t
    obtain ⟨g, h0, hg⟩ := introTraceApprox_rat_spectral_tendsto_atBot_profile h ρ hA n
    refine ⟨by simpa [b,hg] using h0 (Real.exp t), ?_⟩
    exact (Complex.re_le_norm _).trans (introTraceApprox_spectral_tendsto_atBot_log_norm h ρ hA n (Real.exp t))
  · intro t ht
    have h := (Complex.continuous_re.tendsto _).comp (introTraceApprox_tendsto h ρ hA
      (2:ℂ) (Real.exp t) (Real.exp_pos _) (Real.one_lt_exp_iff.mpr ht).ne')
    have hpow : (introTracePower 2 (Real.exp t)).re = Real.exp (-2*t) := by
      rw [introTracePower, ite_eq_left (Real.one_lt_exp_iff.mpr ht),
        Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'),
        ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
      rw [show (↑t : ℂ) * -(2:ℂ) = ((-2*t : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
      rfl
    rw [hpow] at h
    exact h

/-- For the parameter-two approximants, the sum of infinite-place digamma integrals in
the one-sided explicit formula has real part tending to minus infinity. -/
private theorem introTraceApprox_spectral_tendsto_atBot_analytic (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) :
    let f (n : ℕ) := introTraceApprox (h n) (ρ n) (2 : ℂ)
    let m := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
    ∃ A : ℕ → ℂ, Tendsto (fun n ↦ (A n).re) atTop atBot ∧
      ∀ n, HasSum (fun z : ℂ ↦ (m z : ℂ) * introTraceMellin (f n) (z-1/2))
        (A n - ∑' j : HeightOneSpectrum (𝓞 F) × ℕ, introTracePrimePower χ (f n) j.1 j.2) := by
  classical
  intro f m
  have hzero (n : ℕ) {x : ℝ} (hx : x ≤ 1) : f n x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx.not_gt (introTraceApprox_support _ _ hA n 2 h))
  let K (w : InfinitePlace F) : ℝ := if w.IsReal then 1/2 else 1
  let P (w : InfinitePlace F) : ℂ := if hw : w.IsReal then
    let e := (realHeckeCharacter_parameters χ w hw).exists.choose
    (1/2 + e.1 + e.2.val)/2
    else
    let e := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    1/2 + e.1 + (e.2.natAbs : ℂ)/2
  let Q (w : InfinitePlace F) : ℂ := if hw : w.IsReal then
    let e := (realHeckeCharacter_parameters χ w hw).exists.choose
    (1/2 - e.1 + e.2.val)/2
    else
    let e := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    1/2 - e.1 + (e.2.natAbs : ℂ)/2
  let W (n : ℕ) (w : InfinitePlace F) := ∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel (K w) (P w) (Q w) (fun u ↦ f n (Real.exp u)) t
  have hW (w : InfinitePlace F) : Tendsto (fun n ↦ (W n w).re) atTop atBot := by
    have hk : 0 < K w := by dsimp [K]; split_ifs <;> norm_num
    have hp : 0 < (P w).re := by
      dsimp only [P]
      split_ifs with hw
      · have ht := (realHeckeCharacter_parameters χ w hw).exists.choose_spec.1
        simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re, Complex.natCast_re, ht, add_zero]
        positivity
      · have ht := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose_spec.1
        simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re, Complex.natCast_re, ht, add_zero]
        positivity
    exact introTraceApprox_spectral_tendsto_atBot_gamma_profile h ρ hA hk (P w) (Q w) hp
  refine ⟨fun n ↦ ∑ w, W n w, ?_, fun n ↦ ?_⟩
  · obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    apply tendsto_atBot.mpr
    intro c
    have hall : ∀ᶠ n in atTop, ∀ w, (W n w).re ≤ min c 0 :=
      eventually_all.mpr fun w ↦ tendsto_atBot.mp (hW w) _
    filter_upwards [hall] with n hn
    rw [Complex.re_sum]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    exact (add_le_of_nonpos_left (Finset.sum_nonpos (fun w _ ↦ (hn w).trans (min_le_right _ _)))).trans
      ((hn v).trans (min_le_left _ _))
  · have hprofile := introTraceApprox_logProfile h ρ hA n 2
    convert introTrace_spectral_digamma_of_supported_above_one χ (f n) (fun x hx ↦ hzero n hx)
      hprofile.1 hprofile.2 using 1
    congr 1
    exact Finset.sum_congr rfl fun w _ ↦ by by_cases hw : w.IsReal <;> simp [W, K, P, Q, hw]

/-- The negative orders of the completed function form a finite set in the left closed
half-plane Re s ≤ 1. -/
private theorem introTraceApprox_spectral_tendsto_atBot_poles (χ : U𝔽) :
    let m := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
    ∃ P : Finset ℂ, (∀ z, z ∈ P ↔ m z < 0) ∧ ∀ z ∈ P, z.re ≤ 1 := by
  classical
  intro m
  let L := continuedCompletedHeckeL χ
  have hL := continuedCompletedHeckeL_spec χ
  have hreg (z : ℂ) (ha : AnalyticAt ℂ L z) : 0 ≤ m z := by
    dsimp [m]
    rw [MeromorphicOn.divisor_apply hL.1.meromorphicOn (mem_univ z)]
    have h := ha.meromorphicOrderAt_nonneg
    change 0 ≤ (meromorphicOrderAt L z).untop₀
    generalize meromorphicOrderAt L z = o at h ⊢
    cases o with
    | top => simp
    | coe i => simpa using h
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨t, ⟨-, -, -, han⟩, -⟩ := completedHeckeL_continuation_simplePoles χ L hL.1 hL.2 hχ
    let U : Finset ℂ := {Complex.I * (t:ℂ), 1+Complex.I*(t:ℂ)}
    refine ⟨U.filter (fun z ↦ m z < 0), fun z ↦ ?_, fun z hz ↦ ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨And.right, fun h ↦ ⟨?_,h⟩⟩
      by_contra hU
      exact h.not_ge (hreg z (han z (by simpa [U] using hU)))
    · have hh := (Finset.mem_filter.mp hz).1
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl <;> simp
  · refine ⟨∅, fun z ↦ ?_, by simp⟩
    simp [(hreg z ((completedHeckeL_continuation_entire χ L hL.1 hL.2 hχ).analyticAt z)).not_gt]

/-- Split the signed divisor sum into its full zero window and the finitely many poles. -/
private theorem introTraceApprox_spectral_tendsto_atBot_split (χ : U𝔽) (f : ℝ → ℂ)
    (P : Finset ℂ) (hP : ∀ z, z ∈ P ↔ MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z < 0) :
    let m := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
    let g (z : ℂ) := (m z : ℂ) * introTraceMellin f (z-1/2)
    Summable g → (∑' z, g z) = introTraceSpectralSum χ f 1 + ∑ z ∈ P, g z := by
  classical
  intro m g hg
  let Z := {z : ℂ | 0 < m z ∧ |z.re - 1/2| < (1:ℝ)}
  have hZ {z : ℂ} (hz : 0 < m z) : z ∈ Z := by
    have hmem := explicitFormulaCompletedHeckeL_zero_re_mem χ hz
    exact ⟨hz, abs_lt.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩⟩
  rw [← hg.tsum_subtype_add_tsum_subtype_compl Z]
  change (∑' z : Z, g z.val) + (∑' z : (Zᶜ : Set ℂ), g z.val) = (∑' z : Z, g z.val) + _
  congr 1
  rw [tsum_subtype]
  rw [tsum_eq_sum (s := P) (fun z hz ↦ ?_)]
  · apply Finset.sum_congr rfl
    intro z hz
    refine indicator_of_mem (show z ∈ Zᶜ from fun h ↦ (hP z).mp hz |>.not_ge h.1.le) _
  · by_cases hmem : z ∈ Z
    · exact indicator_of_notMem (notMem_compl_iff.mpr hmem) _
    · rw [indicator_of_mem hmem]
      have zero : m z = 0 := le_antisymm (le_of_not_gt (fun h ↦ hmem (hZ h)))
        (le_of_not_gt (fun h ↦ hz ((hP z).mpr h)))
      simp [g,zero]

/-- Near the identity all powers sampled by a sufficiently small mollifier have nonnegative
real part after the archimedean phase is applied. The cutoff and the mollifier can shrink independently. -/
private theorem introTraceApprox_euler_phase (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (z p : ℂ) (hz : 0 ≤ z.re) (k : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioo 0 δ,
      0 ≤ (introTraceApprox (h n) (ρ n) z (Real.exp (k*t)) * Complex.exp (-p*t)).re := by
  let X (x : ℝ × ℝ) := Real.exp (k*x.1) - x.2
  have hX : Continuous X := by dsimp [X]; fun_prop
  have hX0 : X (0,0) = 1 := by simp [X]
  have hpow : ContinuousAt (fun x : ℝ × ℝ ↦ (X x : ℂ)^(-z)) (0,0) :=
    ((Complex.continuous_ofReal.comp hX).continuousAt (x := (0,0))).tendsto.cpow
      (tendsto_const_nhds (x := -z)) (by simp [hX0])
  have hph : Continuous (fun x : ℝ × ℝ ↦ Complex.exp (-p*x.1)) := by fun_prop
  have hc := Complex.continuous_re.continuousAt.comp (hpow.mul hph.continuousAt)
  have hgood : ∀ᶠ x : ℝ × ℝ in 𝓝 (0,0), 0 < (((X x : ℂ)^(-z))*Complex.exp (-p*x.1)).re :=
    continuousAt_const.eventually_lt hc (by simp [X])
  obtain ⟨δ,hδ,hg⟩ := Metric.eventually_nhds_iff.mp hgood
  refine ⟨δ,hδ,?_⟩
  obtain ⟨ε,hε,hρ⟩ := hA.2.2.2
  filter_upwards [hε.eventually_lt_const hδ] with n hn
  intro t ht
  let A := Complex.exp (-p*t)
  let x := Real.exp (k*t)
  have hnon (u : ℝ) : 0 ≤ ((ρ n u : ℂ) * (introTracePower z (x-u) * A)).re := by
    by_cases hzero : ρ n u = 0
    · simp [hzero]
    rw [Complex.re_ofReal_mul]
    apply mul_nonneg ((hρ n).2.2.1 _)
    have hu := (hρ n).2.2.2.1 (subset_tsupport _ hzero)
    have hdist : dist (t,u) (0,0) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [Real.dist_eq,abs_of_pos ht.1] using ht.2,by
        simpa [Real.dist_eq,abs_lt] using And.intro (lt_of_lt_of_le (neg_lt_neg hn) hu.1) (hu.2.trans_lt hn)⟩
    have good : 0 < (((x-u : ℝ):ℂ)^(-z)*A).re := hg hdist
    unfold introTracePower
    split_ifs with hx h1
    · exact good.le
    · simp only [h1, Complex.ofReal_one, Complex.one_cpow, one_mul] at good
      simp [Complex.mul_re, good.le]
    · simp
  have hr : Integrable (ρ n) := (hρ n).2.1.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hρ n).2.2.2.1)
  have hInt : Integrable (fun u : ℝ ↦ (ρ n u : ℂ) * introTracePower z (x-u)) := by
    apply hr.mono' ((Complex.measurable_ofReal.comp (hρ n).2.1.continuous.measurable).mul
      ((introTraceApprox_mellin_tendsto_power_measurable z).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    apply ae_of_all
    intro u
    change ‖(ρ n u : ℂ)*introTracePower z (x-u)‖ ≤ ρ n u
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ((hρ n).2.2.1 _)]
    exact mul_le_of_le_one_right ((hρ n).2.2.1 _) (introTracePower_norm_le_one hz _)
  have hpos : 0 ≤ ((∫ u, (ρ n u : ℂ) * introTracePower z (x-u)) * A).re := by
    have he := integral_re (hInt.mul_const A)
    simp only [RCLike.re_to_complex] at he
    rw [← integral_mul_const, ← he]
    apply integral_nonneg
    intro u
    simpa [mul_assoc] using hnon u
  change 0 ≤ (((h n x : ℂ) * _) * A).re
  rw [mul_assoc]
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg ((hA.1 n).2.2.2 _).1 hpos

/-- The positive part of the digamma integrand dominates a reciprocal near zero. Its negative part has a uniform integrable bound. -/
private theorem introTraceApprox_euler_gamma (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (z : ℂ) (hz : 0 ≤ z.re) {k : ℝ} (hk : 0 < k) (p q : ℂ) (hp : 0 < p.re) :
    Tendsto (fun n ↦ (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k p q
      (fun u ↦ introTraceApprox (h n) (ρ n) z (Real.exp u)) t).re) atTop atBot := by
  let b (n : ℕ) (u : ℝ) := introTraceApprox (h n) (ρ n) z (Real.exp u)
  let G (n : ℕ) (t : ℝ) := (k:ℂ) * b n (k*t) * Complex.exp (-p*t) / (1-(Real.exp (-t):ℂ))
  have hzero (n : ℕ) {u : ℝ} (hu : u ≤ 0) : b n u = 0 := image_eq_zero_of_notMem_tsupport
    (fun h ↦ hu.not_gt (introTraceApprox_spectral_tendsto_atBot_log_support _ _ hA n z h))
  have hI (n : ℕ) : Integrable (G n) := introTraceApprox_spectral_tendsto_atBot_integrable_weight
    (introTraceApprox_logProfile h ρ hA n z).1.continuous (introTraceApprox_logProfile h ρ hA n z).2
    (fun H ↦ lt_irrefl _ (introTraceApprox_spectral_tendsto_atBot_log_support _ _ hA n z H)) hk p
  have hReal (n : ℕ) (t : ℝ) : (G n t).re =
      k * (b n (k*t) * Complex.exp (-p*t)).re / (1-Real.exp (-t)) := by
    dsimp only [G]
    rw [mul_assoc,show (1:ℂ)-(Real.exp (-t):ℂ) = ((1-Real.exp (-t):ℝ):ℂ) by push_cast; rfl,Complex.div_ofReal_re]
    simp [Complex.mul_re]
  have hden {t : ℝ} (ht : 0 < t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht))
  let H (t : ℝ) := (((Real.exp (k*t):ℝ):ℂ)^(-z)*Complex.exp (-p*t)).re
  have hC : ContinuousAt H 0 := by
    have hP : ContinuousAt (fun t : ℝ ↦ ((Real.exp (k*t):ℝ):ℂ)^(-z)) 0 :=
      (show Tendsto (fun t : ℝ ↦ ((Real.exp (k*t):ℝ):ℂ)) (𝓝 0) (𝓝 ((Real.exp (k*0):ℝ):ℂ)) from
        (show Continuous (fun t : ℝ ↦ ((Real.exp (k*t):ℝ):ℂ)) by fun_prop).continuousAt.tendsto).cpow
          (tendsto_const_nhds (x := -z)) (by simp)
    exact Complex.continuous_re.continuousAt.comp (hP.mul (by fun_prop))
  have hlower : ∀ᶠ t in 𝓝 (0:ℝ), 1/2 < H t :=
    continuousAt_const.eventually_lt hC (by norm_num [H])
  obtain ⟨c,hc,hphase⟩ := introTraceApprox_euler_phase h ρ hA z p hz k
  obtain ⟨d,hd,hdH⟩ := Metric.eventually_nhds_iff.mp hlower
  let δ := min c d
  have hδ : 0 < δ := lt_min hc hd
  have hU := introTraceApprox_spectral_tendsto_atBot_singular (show 0 < k/2 by positivity) hδ
    (fun n t ↦ (G n t).re) (fun n ↦ (hI n).integrableOn.re) (fun t ht ↦ by
      have hpwr := introTraceApprox_tendsto h ρ hA z (Real.exp (k*t)) (Real.exp_pos _) (Real.one_lt_exp_iff.mpr (mul_pos hk ht.1)).ne'
      rw [introTracePower,ite_eq_left (Real.one_lt_exp_iff.mpr (mul_pos hk ht.1))] at hpwr
      have hlim : Tendsto (fun n ↦ (b n (k*t)*Complex.exp (-p*t)).re) atTop (𝓝 (H t)) :=
        (Complex.continuous_re.tendsto _).comp (hpwr.mul_const _)
      have hHt := hdH (show dist t 0 < d by simpa [Real.dist_eq,abs_of_pos ht.1] using ht.2.trans_le (min_le_right c d))
      filter_upwards [hlim.eventually (lt_mem_nhds hHt)] with n hn
      rw [hReal]
      calc
        k/2/t ≤ k/2/(1-Real.exp (-t)) := div_le_div_of_nonneg_left (by positivity) (hden ht.1) (by linarith [Real.add_one_le_exp (-t)])
        _ ≤ _ := div_le_div_of_nonneg_right (by linarith [mul_le_mul_of_nonneg_left hn.le hk.le]) (hden ht.1).le)
  let D := k/(1-Real.exp (-δ))
  let E (t : ℝ) := D * Real.exp (-p.re*t)
  have hD : 0 < D := div_pos hk (hden hδ)
  have hE : IntegrableOn E (Ioi 0) := (exp_neg_integrableOn_Ioi 0 hp).const_mul D
  have hNeg : ∀ᶠ n in atTop, (∫ t in Ioi (0:ℝ), max (-(G n t).re) 0) ≤ ∫ t in Ioi (0:ℝ), E t := by
    filter_upwards [hphase] with n hn
    refine setIntegral_mono_on (hI n).integrableOn.re.neg_part hE measurableSet_Ioi (fun t ht ↦ ?_)
    change 0 < t at ht
    have hEt : 0 ≤ E t := mul_nonneg hD.le (Real.exp_pos _).le
    apply max_le _ hEt
    by_cases hs : t < δ
    · rw [hReal]
      apply le_trans _ hEt
      exact neg_nonpos.mpr (div_nonneg (mul_nonneg hk.le (hn t ⟨ht,hs.trans_le (min_le_left c d)⟩)) (hden ht).le)
    · have hdt : 1-Real.exp (-δ) ≤ 1-Real.exp (-t) :=
        sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg (le_of_not_gt hs))) 1
      have he : ‖Complex.exp (-p*t)‖ = Real.exp (-p.re*t) := by simp [Complex.norm_exp, Complex.mul_re]
      have hb := introTraceApprox_euler_norm h ρ hA n z hz (Real.exp (k*t))
      calc
        -(G n t).re ≤ ‖G n t‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        _ = k * ‖b n (k*t)‖ * Real.exp (-p.re*t)/(1-Real.exp (-t)) := by
          dsimp only [G]
          rw [show (1:ℂ)-(Real.exp (-t):ℂ) = ((1-Real.exp (-t):ℝ):ℂ) by push_cast; rfl]
          rw [norm_div, norm_mul, norm_mul, he]
          simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, abs_of_pos (hden ht)]
        _ ≤ (k * Real.exp (-p.re*t))/(1-Real.exp (-t)) := by
          apply div_le_div_of_nonneg_right _ (hden ht).le
          exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hk.le hb) (Real.exp_pos _).le
        _ ≤ (k * Real.exp (-p.re*t))/(1-Real.exp (-δ)) := div_le_div_of_nonneg_left (by positivity) (hden hδ) hdt
        _ = E t := by dsimp [E,D]; ring
  have hK (n : ℕ) : (∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel k p q (b n) t).re =
      -(∫ t in Ioi (0:ℝ), (G n t).re) := by
    have eq : (∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel k p q (b n) t) = ∫ t in Ioi (0:ℝ), -G n t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change 0 < t at ht
      simp [heckeArchimedeanDigammaKernel,G,hzero n (u := 0) le_rfl,hzero n (neg_nonpos.mpr (mul_nonneg hk.le ht.le))]
      ring
    rw [eq, integral_neg, Complex.neg_re]
    exact congrArg Neg.neg (integral_re ((hI n).integrableOn (s := Ioi (0:ℝ)))).symm
  apply tendsto_atBot.mpr
  intro M
  filter_upwards [tendsto_atTop.mp hU ((∫ t in Ioi (0:ℝ), E t) - M),hNeg] with n hn hneg
  have hR : Integrable (fun t ↦ (G n t).re) (volume.restrict (Ioi (0:ℝ))) :=
    ((hI n).integrableOn (s := Ioi (0:ℝ))).re
  have eq : (∫ t in Ioi (0:ℝ), (G n t).re) = (∫ t in Ioi (0:ℝ), max (G n t).re 0) -
      ∫ t in Ioi (0:ℝ), max (-(G n t).re) 0 := by
    rw [← integral_sub hR.pos_part hR.neg_part]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ ↦ (posPart_sub_negPart _).symm)
  change (∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel k p q (b n) t).re ≤ M
  rw [hK,eq]
  linarith

/-- Local digamma divergence at each infinite place passes to the signed one-character explicit formula. -/
private theorem introTraceApprox_spectral_atBot_of_local_digamma (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (w₀ : ℂ) (hK : ∀ {k : ℝ}, 0 < k → ∀ p q : ℂ, 0 < p.re →
      Tendsto (fun n ↦ (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k p q
        (fun u ↦ introTraceApprox (h n) (ρ n) w₀ (Real.exp u)) t).re) atTop atBot) :
    let f (n : ℕ) := introTraceApprox (h n) (ρ n) w₀
    let m := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
    ∃ A : ℕ → ℂ, Tendsto (fun n ↦ (A n).re) atTop atBot ∧
      ∀ n, HasSum (fun z : ℂ ↦ (m z : ℂ) * introTraceMellin (f n) (z-1/2))
        (A n - ∑' j : HeightOneSpectrum (𝓞 F) × ℕ, introTracePrimePower χ (f n) j.1 j.2) := by
  classical
  intro f m
  have hzero (n : ℕ) {x : ℝ} (hx : x ≤ 1) : f n x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx.not_gt (introTraceApprox_support _ _ hA n w₀ h))
  let K (w : InfinitePlace F) : ℝ := if w.IsReal then 1/2 else 1
  let P (w : InfinitePlace F) : ℂ := if hw : w.IsReal then
    let e := (realHeckeCharacter_parameters χ w hw).exists.choose
    (1/2 + e.1 + e.2.val)/2
    else
    let e := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    1/2 + e.1 + (e.2.natAbs : ℂ)/2
  let Q (w : InfinitePlace F) : ℂ := if hw : w.IsReal then
    let e := (realHeckeCharacter_parameters χ w hw).exists.choose
    (1/2 - e.1 + e.2.val)/2
    else
    let e := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    1/2 - e.1 + (e.2.natAbs : ℂ)/2
  let W (n : ℕ) (w : InfinitePlace F) := ∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel (K w) (P w) (Q w) (fun u ↦ f n (Real.exp u)) t
  have hW (w : InfinitePlace F) : Tendsto (fun n ↦ (W n w).re) atTop atBot := by
    have hk : 0 < K w := by dsimp [K]; split_ifs <;> norm_num
    have hp : 0 < (P w).re := by
      dsimp only [P]
      split_ifs with hw
      · have ht := (realHeckeCharacter_parameters χ w hw).exists.choose_spec.1
        simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re, Complex.natCast_re, ht, add_zero]
        positivity
      · have ht := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose_spec.1
        simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re, Complex.natCast_re, ht, add_zero]
        positivity
    exact hK hk (P w) (Q w) hp
  refine ⟨fun n ↦ ∑ w, W n w, ?_, fun n ↦ ?_⟩
  · obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    apply tendsto_atBot.mpr
    intro c
    have hall : ∀ᶠ n in atTop, ∀ w, (W n w).re ≤ min c 0 :=
      eventually_all.mpr fun w ↦ tendsto_atBot.mp (hW w) _
    filter_upwards [hall] with n hn
    rw [Complex.re_sum]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    exact (add_le_of_nonpos_left (Finset.sum_nonpos (fun w _ ↦ (hn w).trans (min_le_right _ _)))).trans
      ((hn v).trans (min_le_left _ _))
  · have hprofile := introTraceApprox_logProfile h ρ hA n w₀
    convert introTrace_spectral_digamma_of_supported_above_one χ (f n) (fun x hx ↦ hzero n hx)
      hprofile.1 hprofile.2 using 1
    congr 1
    exact Finset.sum_congr rfl fun w _ ↦ by by_cases hw : w.IsReal <;> simp [W, K, P, Q, hw]

/-- In a full window, bounded prime terms and convergent polar moments transfer divergence of the signed sum to the spectral sum. -/
private theorem introTraceApprox_spectral_atBot_of_bounds (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (w₀ : ℂ) (hw₀ : 1/2 < w₀.re)
    (hArch :
      let f (n : ℕ) := introTraceApprox (h n) (ρ n) w₀
      let m := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
      ∃ A : ℕ → ℂ, Tendsto (fun n ↦ (A n).re) atTop atBot ∧
        ∀ n, HasSum (fun z : ℂ ↦ (m z : ℂ) * introTraceMellin (f n) (z-1/2))
          (A n - ∑' j : HeightOneSpectrum (𝓞 F) × ℕ, introTracePrimePower χ (f n) j.1 j.2))
    (hQ : ∃ B : ℝ, ∀ᶠ n in atTop, -(∑' j : HeightOneSpectrum (𝓞 F) × ℕ,
      introTracePrimePower χ (introTraceApprox (h n) (ρ n) w₀) j.1 j.2).re ≤ B) :
    Tendsto (fun n ↦ (introTraceSpectralSum χ (introTraceApprox (h n) (ρ n) w₀) 1).re) atTop atBot := by
  classical
  let f (n : ℕ) := introTraceApprox (h n) (ρ n) w₀
  let m := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
  obtain ⟨P, hP, hre⟩ := introTraceApprox_spectral_tendsto_atBot_poles χ
  let S (n : ℕ) := ∑ z ∈ P, (m z : ℂ) * introTraceMellin (f n) (z-1/2)
  let s := ∑ z ∈ P, (m z : ℂ) * introTraceMellin (introTracePower w₀) (z-1/2)
  have hS : Tendsto S atTop (𝓝 s) := by
    apply tendsto_finsetSum
    intro z hz
    apply Filter.Tendsto.const_mul
    apply (introTraceApprox_mellin_tendsto h ρ hA (z-1/2)).tendsto_at
    change (z-1/2).re < w₀.re
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith [hre z hz]
  obtain ⟨A, hAneg, hsum⟩ := hArch
  obtain ⟨B,hB⟩ := hQ
  have hlow := ((Complex.continuous_re.tendsto _).comp hS).eventually (lt_mem_nhds (sub_one_lt s.re))
  apply tendsto_atBot.mpr
  intro c
  filter_upwards [tendsto_atBot.mp hAneg (c-B+s.re-1), hB, hlow] with n hn hbn hsn
  have hspl := introTraceApprox_spectral_tendsto_atBot_split χ (f n) P hP (hsum n).summable
  rw [(hsum n).tsum_eq] at hspl
  have hreal := congrArg Complex.re hspl
  change ((A n) - _ : ℂ).re = (introTraceSpectralSum χ (f n) 1 + S n).re at hreal
  simp only [Complex.add_re, Complex.sub_re] at hreal
  change s.re-1 < (S n).re at hsn
  change (introTraceSpectralSum χ (f n) 1).re ≤ _
  change -(∑' j : HeightOneSpectrum (𝓞 F) × ℕ, introTracePrimePower χ (f n) j.1 j.2).re ≤ B at hbn
  linarith

/-- In the full zero window, the pole moments converge and a lower bound for the prime
term suffices for the real part of the spectral sum to tend to minus infinity. -/
private theorem introTraceApprox_spectral_tendsto_atBot_of_primeBound (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ)
    (hQ : ∃ B : ℝ, ∀ᶠ n in atTop, -(∑' j : HeightOneSpectrum (𝓞 F) × ℕ,
      introTracePrimePower χ (introTraceApprox (h n) (ρ n) 2) j.1 j.2).re ≤ B) :
    Tendsto (fun n ↦ (introTraceSpectralSum χ (introTraceApprox (h n) (ρ n) 2) 1).re) atTop atBot := by
  exact introTraceApprox_spectral_atBot_of_bounds χ h ρ hA 2 (by norm_num)
    (introTraceApprox_spectral_tendsto_atBot_analytic χ h ρ hA) hQ

/-- With a nonnegative real radial profile the real part of each trivial-character
prime-power contribution is nonnegative. -/
private theorem introTraceApprox_rat_spectral_tendsto_atBot_prime_nonneg (g : ℝ → ℝ)
    (hg : ∀ t, 0 ≤ g t) (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) :
    0 ≤ (introTracePrimePower (F := ℚ) 1 (fun t ↦ (g t : ℂ)) v k).re := by
  classical
  have htriv : ideleClassNormTwist (F := ℚ) 1 0 = 1 := by
    ext1 x
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hunit (u : (v.adicCompletion ℚ)ˣ) :
      (1 : HeckeCharacter (𝓞 ℚ) ℚ).restrict v u = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  let val : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  have hv : (1 : HeckeCharacter (𝓞 ℚ) ℚ).localValue v = 1 :=
    hunit (Units.mk0 _ val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero)
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hden : (q : ℂ) ^ (((k + 1 : ℕ) : ℂ) / 2) = ((q ^ ((k + 1 : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (zero_le_one.trans hq)]
    push_cast
    rfl
  simp only [introTracePrimePower, htriv]
  split_ifs
  · simp only [hv, one_pow, star_one, one_mul]
    change 0 ≤ ((Real.log q : ℂ) * ((g (q ^ (k + 1)) : ℂ) + (g ((q ^ (k + 1))⁻¹) : ℂ)) /
      (q : ℂ) ^ (((k + 1 : ℕ) : ℂ) / 2)).re
    rw [hden, ← Complex.ofReal_add, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_nonneg (mul_nonneg (Real.log_nonneg hq) (add_nonneg (hg _) (hg _)))
      (Real.rpow_nonneg (zero_le_one.trans hq) _)
  · exact le_rfl

open Classical in
private theorem introTrace_normalized_signed_divisor_split
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 F) F) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (f : ℝ → ℂ) :
    let g := fun z : ℂ ↦ (MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z : ℂ) *
      introTraceMellin f (z - 1/2)
    Summable g → (∑' z, g z) = introTraceSpectralSum χ f 1 -
      (if χ = 1 then introTraceMellin f (1/2) + introTraceMellin f (-1/2) else 0) := by
  classical
  intro g hg
  by_cases h : χ = 1
  · subst χ
    obtain ⟨h0, h1⟩ := idelicExplicitFormula_trivial_poles (F := F)
    have hP (z : ℂ) : z ∈ ({0,1} : Finset ℂ) ↔
        MeromorphicOn.divisor (continuedCompletedHeckeL (1 : U𝔽)) univ z < 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl)
        · change MeromorphicOn.divisor (explicitFormulaCompletedHeckeL (1 : U𝔽)) univ 0 < 0
          rw [h0]
          decide
        · change MeromorphicOn.divisor (explicitFormulaCompletedHeckeL (1 : U𝔽)) univ 1 < 0
          rw [h1]
          decide
      · exact fun hz ↦ (idelicExplicitFormula_chart_poles τ hτ (1 : U𝔽) hχ z hz).2
    convert introTraceApprox_spectral_tendsto_atBot_split (1 : U𝔽) f {0,1} hP hg using 1
    change _ = _ + ∑ z ∈ ({0,1} : Finset ℂ), (MeromorphicOn.divisor (explicitFormulaCompletedHeckeL (1 : U𝔽))
      univ z : ℂ) * introTraceMellin f (z-1/2)
    simp [h0,h1]
    ring_nf
  · have hP (z : ℂ) : z ∈ (∅ : Finset ℂ) ↔ MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z < 0 := by
      simp only [Finset.notMem_empty, false_iff]
      exact fun hz ↦ h (idelicExplicitFormula_chart_poles τ hτ χ hχ z hz).1
    simpa [h,g] using introTraceApprox_spectral_tendsto_atBot_split χ f ∅ hP hg

open scoped ComplexConjugate in
/-- A radial Bruhat test in a normalized character recovers its compact smooth logarithmic profile. -/
private theorem introTrace_characterTrace_log_profile (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1)
    (h : ℝ → ℂ) (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g, φ.val g = introTraceTest χ h g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ h (Real.exp y)) ∧ HasCompactSupport (fun y ↦ h (Real.exp y)) := by
  let vol : ℂ := ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℝ)
  let s (y : ℝ) := positiveRealLogEquiv.symm (Multiplicative.ofAdd y)
  have hV : vol ≠ 0 := introTrace_characterTrace_volume
  have he (y : ℝ) : ((s y).val : ℝ) = Real.exp y := by
    have hlog := positiveRealLogEquiv_apply (s y)
    rw [show positiveRealLogEquiv (s y) = Multiplicative.ofAdd y from
      positiveRealLogEquiv.apply_symm_apply _, toAdd_ofAdd] at hlog
    exact (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt (s y)))).symm.trans (congrArg Real.exp hlog.symm)
  obtain ⟨Φ, _, hΦ⟩ := idelicExplicitFormula_radialProfile τ hτ φ χ vol⁻¹
  have eq (y : ℝ) : Φ y = h (Real.exp y) := by
    rw [hΦ]
    have eq' (u : (ideleClassNorm F).ker) :
        φ.val (τ (s y) * (u : C𝔽)) * (χ (u : C𝔽) : ℂ) = h (Real.exp y) := by
      have hN : ((ideleClassNorm F (τ (s y) * (u : C𝔽))).val : ℝ) = Real.exp y := by
        rw [map_mul, hτ, MonoidHom.mem_ker.mp u.property, mul_one, he]
      rw [hφ, introTraceTest, hN, map_mul, hχ, one_mul]
      have unit (c : Circle) : star (c : ℂ) * (c : ℂ) = 1 := by
        change conj (c : ℂ) * (c : ℂ) = 1
        simp [← Circle.coe_inv_eq_conj]
      rw [mul_right_comm, unit, one_mul]
    rw [show (fun u : (ideleClassNorm F).ker ↦ φ.val (τ (s y) * (u : C𝔽)) * (χ (u : C𝔽) : ℂ)) =
      (fun _ ↦ h (Real.exp y)) from funext eq', integral_const]
    simp only [Measure.real, Complex.real_smul]
    change vol⁻¹ * (vol * h (Real.exp y)) = h (Real.exp y)
    rw [inv_mul_cancel_left₀ hV]
  refine ⟨(funext eq) ▸ Φ.smooth ⊤, ?_⟩
  obtain ⟨B, hB⟩ := introTrace_characterTrace_radial_bound τ hτ χ h φ hφ
  apply HasCompactSupport.intro (isCompact_Icc (a := -(B:ℝ)) (b := (B:ℝ)))
  intro y hy
  by_contra hn
  have hbound := hB _ (Real.exp_pos y) hn
  exact hy ⟨by linarith [Real.add_one_le_exp (-y), (le_max_right _ _).trans hbound,
    Real.exp_neg y], by linarith [Real.add_one_le_exp y, (le_max_left _ _).trans hbound]⟩

/-- Restriction of the Bruhat test to local units gives the ordinary integrability at each infinite place. -/
private theorem introTrace_characterTrace_arch_integrable (χ : U𝔽) (w : InfinitePlace F)
    (f : ℝ → ℂ) (hz : f 1 = 0) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ g, φ.val g = introTraceTest χ f g) :
    Integrable (archIntegrand(χ, f, w)) (infiniteLocalMultiplicativeTamagawaMeasure F w) := by
  obtain ⟨A, hA⟩ := idelicExplicitFormula_infiniteTestMap (F := F) w
  have hlocal (u : w.Completionˣ) : (A φ).val u = introTraceTest χ f (archClass(w) u) :=
    (hA φ u).trans (hφ _)
  by_cases hw : w.IsReal
  · exact (introTraceArchimedean_eq_realPrincipalValue χ f hz w hw (A φ) hlocal).1
  · have h1 : (A φ).val 1 = 0 := by simp [hlocal, introTraceTest, hz]
    simpa only [hlocal] using (introTrace_characterTrace_complex_place w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) (A φ) h1).1

/-- Orthogonality restricts the exterior-zero cancellation for this test to its own isotype. -/
private theorem introTrace_characterTrace_exterior_isotype (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1)
    (h : ℝ → ℂ) (φ : D𝔽) (hφ : ∀ g, φ.val g = introTraceTest χ h g) (a : ℝ)
    (hTail : HasSum (fun z : {p : {η : U𝔽 // ∀ t, η (τ t) = 1} × ℂ //
        0 < zeroOrder(p.1.val, p.2) ∧ a ≤ |p.2.re - 1 / 2|} ↦
        (zeroOrder(z.val.1.val, z.val.2) : ℂ) *
          ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2) g ∂ideleClassTamagawaMeasure F) 0) :
    HasSum (fun r : {s : ℂ // 0 < zeroOrder(χ, s) ∧ a ≤ |s.re - 1/2|} ↦
      (zeroOrder(χ, r.val) : ℂ) * introTraceMellin h (r.val-1/2)) 0 := by
  classical
  let A := {p : {η : U𝔽 // ∀ t, η (τ t) = 1} × ℂ //
    0 < zeroOrder(p.1.val, p.2) ∧ a ≤ |p.2.re - 1/2|}
  let E := {s : ℂ // 0 < zeroOrder(χ, s) ∧ a ≤ |s.re - 1/2|}
  let ι (r : E) : A := ⟨(⟨χ, hχ⟩, r.val), r.property⟩
  have hi : Injective ι := fun _ _ he ↦ Subtype.ext (congrArg (fun z : A ↦ z.val.2) he)
  let mom (η : U𝔽) (s : ℂ) := ∫ g, φ.val g * ideleClassNormTwist η s g ∂ideleClassTamagawaMeasure F
  let term (z : A) := (zeroOrder(z.val.1.val, z.val.2) : ℂ) * mom z.val.1.val (z.val.2 - 1/2)
  have hm (η : U𝔽) (hη : ∀ t, η (τ t) = 1) (s : ℂ) :
      mom η s = if η = χ then τVolume * introTraceMellin h s else 0 :=
    introTrace_characterTrace_mellin τ hτ χ η hχ hη h φ hφ s
  have hoff (z : A) (hz : z ∉ range ι) : term z = 0 := by
    have hne : z.val.1.val ≠ χ := by
      rintro he
      refine hz ⟨⟨z.val.2, he ▸ z.property⟩, ?_⟩
      exact Subtype.ext (Prod.ext (Subtype.ext he.symm) rfl)
    simp only [term, hm _ z.val.1.property, ite_eq_right hne, mul_zero]
  have hnorm := (hi.hasSum_iff (f := term) hoff).mpr hTail
  have hscalar := hnorm.mul_left τVolume⁻¹
  rw [mul_zero] at hscalar
  refine hscalar.congr_fun fun r ↦ ?_
  change _ = τVolume⁻¹ * ((zeroOrder(χ, r.val) : ℂ) * mom χ (r.val - 1/2))
  rw [hm χ hχ, ite_eq_left rfl]
  field_simp [introTrace_characterTrace_volume (F := F)]

open Classical in
/-- Paper: §1.4.1, p. 28. For any window, the omitted Mellin moments sum to the exact
error in the trace on this radial test. -/
theorem introTrace_characterTrace_exterior_error (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (h : ℝ → ℂ) (hh : h 1 = 0) (φ : D𝔽)
    (hφ : ∀ g, φ.val g = introTraceTest χ h g) (a : ℝ) :
    HasSum (fun r : {z : ℂ // 0 < zeroOrder(χ, z) ∧ a ≤ |z.re - 1 / 2|} ↦
      (zeroOrder(χ, r.val) : ℂ) * introTraceMellin h (r.val - 1 / 2))
      ((if χ = 1 then introTraceMellin h (1 / 2) + introTraceMellin h (-1 / 2) else 0) -
        (∑ w : InfinitePlace F, introTraceArchimedean χ h w) -
        (∑' p : V × ℕ, introTracePrimePower χ h p.1 p.2) - introTraceSpectralSum χ h a) := by
  classical
  let Z : Set ℂ := {z | 0 < zeroOrder(χ, z) ∧ |z.re - 1 / 2| < 1}
  let W : Set ℂ := {z | 0 < zeroOrder(χ, z) ∧ |z.re - 1 / 2| < a}
  let E : Set ℂ := {z | 0 < zeroOrder(χ, z) ∧ a ≤ |z.re - 1 / 2|}
  let g (z : ℂ) := (zeroOrder(χ, z) : ℂ) * introTraceMellin h (z - 1 / 2)
  have hz {z : ℂ} (hpos : 0 < zeroOrder(χ, z)) : z ∈ Z := by
    have H := explicitFormulaCompletedHeckeL_zero_re_mem χ hpos
    exact ⟨hpos,abs_lt.mpr ⟨by linarith [H.1],by linarith [H.2]⟩⟩
  have hW : W ⊆ Z := fun _ h ↦ hz h.1
  have hE : E = Z \ W := by
    ext z
    exact ⟨fun he ↦ ⟨hz he.1,fun hw ↦ he.2.not_gt hw.2⟩,
      fun ⟨hz',hw⟩ ↦ ⟨hz'.1,le_of_not_gt fun hi ↦ hw ⟨hz'.1,hi⟩⟩⟩
  have hreg := introTrace_characterTrace_log_profile τ hτ χ hχ h φ hφ
  have hI := fun w ↦ introTrace_characterTrace_arch_integrable χ w h hh φ hφ
  have H := introTrace_spectral_digamma_of_vanishing_at_one χ h hh hreg.1 hreg.2
  have hpole := introTrace_normalized_signed_divisor_split τ hτ χ hχ h H.summable
  let k (w : InfinitePlace F) := if hw : w.IsReal then
    let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    ∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel (1/2)
      ((1/2+p.1+p.2.val)/2) ((1/2-p.1+p.2.val)/2) (fun y ↦ h (Real.exp y)) t
    else
    let p := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    ∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel 1
      (1/2+p.1+(p.2.natAbs:ℂ)/2) (1/2-p.1+(p.2.natAbs:ℂ)/2) (fun y ↦ h (Real.exp y)) t
  have hk (w : InfinitePlace F) : k w = -introTraceArchimedean χ h w :=
    by
      have hw : introTraceArchimedean χ h w = -k w :=
        introTraceArchimedean_eq_neg_digamma_of_vanishing_at_one χ w h hh hreg.1 hreg.2 (hI w)
      rw [hw, neg_neg]
  have he := H.tsum_eq
  change (∑' z, g z) = (∑ w, k w) - _ at he
  rw [Finset.sum_congr rfl (fun w _ ↦ hk w), Finset.sum_neg_distrib] at he
  let T := (if χ = 1 then introTraceMellin h (1/2) + introTraceMellin h (-1/2) else 0) -
    (∑ w : InfinitePlace F, introTraceArchimedean χ h w) -
    ∑' p : V × ℕ, introTracePrimePower χ h p.1 p.2
  have hZ : HasSum (fun r : Z ↦ g r.val) T := by
    have hg : Summable g := H.summable
    have hfull : HasSum (fun r : Z ↦ g r.val) (∑' r : Z, g r.val) :=
      (hg.subtype (fun z ↦ z ∈ Z)).hasSum
    have hvalue : (∑' r : Z, g r.val) = T := by
      change introTraceSpectralSum χ h 1 = T
      dsimp only [T]
      linear_combination he - hpole
    exact hvalue ▸ hfull
  have hZI := (hasSum_subtype_iff_indicator (f := g) (s := Z)).mp hZ
  have summ : Summable g := H.summable
  have hWI := (hasSum_subtype_iff_indicator (f := g) (s := W)).mp (summ.subtype (fun z ↦ z ∈ W)).hasSum
  apply (hasSum_subtype_iff_indicator (f := g) (s := E)).mpr
  rw [hE, Set.indicator_sdiff hW]
  exact hZI.sub hWI

open Classical in
/-- For a fixed normalized radial test and any width, the stated trace holds exactly
when the Mellin moments of its omitted zeros sum to zero. -/
theorem introTrace_characterTrace_iff_exterior (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (h : ℝ → ℂ) (hh : h 1 = 0) (φ : D𝔽)
    (hφ : ∀ g, φ.val g = introTraceTest χ h g) (a : ℝ) :
    HasSum (fun r : windowZeros(χ, a) ↦ (zeroOrder(χ, r.val) : ℂ) * introTraceMellin h (r.val - 1 / 2))
      ((if χ = 1 then introTraceMellin h (1 / 2) + introTraceMellin h (-1 / 2) else 0) -
        (∑ w : InfinitePlace F, introTraceArchimedean χ h w) -
        ∑' p : V × ℕ, introTracePrimePower χ h p.1 p.2) ↔
    HasSum (fun r : {z : ℂ // 0 < zeroOrder(χ, z) ∧ a ≤ |z.re - 1 / 2|} ↦
      (zeroOrder(χ, r.val) : ℂ) * introTraceMellin h (r.val - 1 / 2)) 0 := by
  have he := introTrace_characterTrace_exterior_error τ hτ χ hχ h hh φ hφ a
  have reg := introTrace_characterTrace_log_profile τ hτ χ hχ h φ hφ
  have hg := (introTrace_spectral_digamma_of_vanishing_at_one χ h hh reg.1 reg.2).summable
  have hi := (hg.subtype (fun z ↦ 0 < zeroOrder(χ, z) ∧ |z.re - 1/2| < a)).hasSum
  change HasSum _ (introTraceSpectralSum χ h a) at hi
  constructor
  · intro H
    rwa [hi.unique H, sub_self] at he
  · intro H
    exact (sub_eq_zero.mp (he.unique H)).symm ▸ hi

open Classical in
/-- The fixed-cutoff character trace uses the cancellation of the exterior zeros
only for the given test. Full windows supply this from the classical critical strip. -/
private theorem introTrace_characterTrace_of_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    (h : ℝ → ℂ) (_hh : h 1 = 0) (φ : D𝔽)
    (_hφ : ∀ g, φ.val g = introTraceTest χ h g) (a : ℝ)
    (hTail : (∀ g : (ideleClassNorm F).ker, φ.val g = 0) → HasSum
      (fun z : {p : {η : U𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1} × ℂ //
        0 < zeroOrder(p.1.val, p.2) ∧ a ≤ |p.2.re - 1 / 2|} ↦
        (zeroOrder(z.val.1.val, z.val.2) : ℂ) *
          ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2) g ∂ideleClassTamagawaMeasure F) 0) :
    (∀ w : InfinitePlace F,
      Integrable archIntegrand(χ, h, w) (infiniteLocalMultiplicativeTamagawaMeasure F w)) ∧
    Summable (fun p : V × ℕ ↦ introTracePrimePower χ h p.1 p.2) ∧
    HasSum (fun ρ : windowZeros(χ, a) ↦
      (zeroOrder(χ, ρ.val) : ℂ) * introTraceMellin h (ρ.val - 1 / 2))
      ((if χ = 1 then introTraceMellin h (1 / 2) + introTraceMellin h (-1 / 2) else 0) -
        (∑ w : InfinitePlace F, introTraceArchimedean χ h w) -
        ∑' p : V × ℕ, introTracePrimePower χ h p.1 p.2) := by
  classical
  refine ⟨fun w ↦ introTrace_characterTrace_arch_integrable χ w h _hh φ _hφ,
    introTrace_characterTrace_primes_summable τ _hτ χ h φ _hφ, ?_⟩
  apply (introTrace_characterTrace_iff_exterior τ _hτ χ _hχ h _hh φ _hφ a).mpr
  apply introTrace_characterTrace_exterior_isotype τ _hτ χ _hχ h φ _hφ a
  apply hTail
  intro u
  rw [_hφ, introTraceTest, show ideleClassNorm F u.val = 1 from u.property]
  simp [_hh]

open Classical in

/-- Paper: §1.4.1, p. 28. In a single isotype, the local terms equal the
polar moments minus the zero sum. The polar moments occur in the trivial isotype.
Deviation: The character is represented by its extension trivial on the chosen
norm section. The window is centered as in §1.8.4. The identity specializes
the corrected `traceFormula`, using normalized local kernels and unit averages.
The common Tamagawa volume cancels against the Mellin disintegration factor.
The arbitrary window still depends on `traceFormula_exteriorZeros`. -/
theorem introTrace_characterTrace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    (h : ℝ → ℂ) (_hh : h 1 = 0) (φ : D𝔽)
    (_hφ : ∀ g, φ.val g = introTraceTest χ h g) (a : ℝ) (_ha : 0 < a) :
    (∀ w : InfinitePlace F,
      Integrable archIntegrand(χ, h, w) (infiniteLocalMultiplicativeTamagawaMeasure F w)) ∧
    Summable (fun p : V × ℕ ↦ introTracePrimePower χ h p.1 p.2) ∧
    HasSum (fun ρ : windowZeros(χ, a) ↦
      (zeroOrder(χ, ρ.val) : ℂ) * introTraceMellin h (ρ.val - 1 / 2))
      ((if χ = 1 then introTraceMellin h (1 / 2) + introTraceMellin h (-1 / 2) else 0) -
        (∑ w : InfinitePlace F, introTraceArchimedean χ h w) -
        ∑' p : V × ℕ, introTracePrimePower χ h p.1 p.2) := by
  apply introTrace_characterTrace_of_exteriorZeros τ _hτ χ _hχ h _hh φ _hφ a
  intro hz
  simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ, Set.indicator_univ] using
    traceFormula_exteriorZeros τ _hτ φ hz _ha

open Classical in
/-- Paper: §1.4.1, pp. 27–28. On a full critical-strip window every radial
Bruhat test vanishing at norm one satisfies the one-character trace formula.
The logarithmic profile can meet both sides of norm one. -/
theorem introTrace_characterTrace_of_half_le (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    (h : ℝ → ℂ) (_hh : h 1 = 0) (φ : D𝔽)
    (_hφ : ∀ g, φ.val g = introTraceTest χ h g) (a : ℝ) (_ha : 1 / 2 ≤ a) :
    (∀ w : InfinitePlace F,
      Integrable archIntegrand(χ, h, w) (infiniteLocalMultiplicativeTamagawaMeasure F w)) ∧
    Summable (fun p : V × ℕ ↦ introTracePrimePower χ h p.1 p.2) ∧
    HasSum (fun ρ : windowZeros(χ, a) ↦
      (zeroOrder(χ, ρ.val) : ℂ) * introTraceMellin h (ρ.val - 1 / 2))
      ((if χ = 1 then introTraceMellin h (1 / 2) + introTraceMellin h (-1 / 2) else 0) -
        (∑ w : InfinitePlace F, introTraceArchimedean χ h w) -
        ∑' p : V × ℕ, introTracePrimePower χ h p.1 p.2) := by
  apply introTrace_characterTrace_of_exteriorZeros τ _hτ χ _hχ h _hh φ _hφ a
  intro _
  simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ, Set.indicator_univ] using
    traceFormula_exteriorZeros_of_half_le τ φ _ha

/-- Paper: §1.4.3, p. 29. For the trivial rational character, the zero
sum in the window of half-width one has real part tending to minus infinity
at parameter two.
Deviation: This replaces the claimed separate holomorphic spectral limit.
The full explicit formula suffices for this window because it contains all zeros. -/
theorem introTraceApprox_rat_spectral_tendsto_atBot (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) :
    Tendsto (fun n ↦ (introTraceSpectralSum (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) 1).re)
      atTop atBot := by
  apply introTraceApprox_spectral_tendsto_atBot_of_primeBound _ _ _ _hA
  refine ⟨0, .of_forall fun n ↦ ?_⟩
  apply neg_nonpos.mpr
  obtain ⟨g, hg, he⟩ := introTraceApprox_rat_spectral_tendsto_atBot_profile h ρ _hA n
  rw [he]
  by_cases hs : Summable (fun j : HeightOneSpectrum (𝓞 ℚ) × ℕ ↦ introTracePrimePower (F := ℚ) 1
      (fun t ↦ (g t : ℂ)) j.1 j.2)
  · rw [Complex.re_tsum hs]
    exact tsum_nonneg fun j ↦ introTraceApprox_rat_spectral_tendsto_atBot_prime_nonneg g hg j.1 j.2
  · simp [tsum_eq_zero_of_not_summable hs]

/-- A nonnegative smooth profile of mass one fits inside any sufficiently short positive interval. -/
private theorem introTrace_positive_divisor_infinite_test {d : ℝ} (hd : 0 < d) :
    ∃ (g : ℝ → ℝ) (f : SchwartzMap ℝ ℂ), Continuous g ∧ Integrable g ∧ (∀ x, 0 ≤ g x) ∧
      (∫ x, g x) = 1 ∧ (∀ x, g x ≠ 0 → d/4 ≤ x ∧ x ≤ d) ∧
      (∀ x, f x = (g x : ℂ)) ∧ ExponentialDecay f := by
  let β : ContDiffBump (d/2) := ⟨d/8, d/4, by positivity, by linarith⟩
  let g := β.normed volume
  have hc : HasCompactSupport (fun x ↦ (g x : ℂ)) :=
    (β.hasCompactSupport_normed (μ := volume)).comp_left Complex.ofReal_zero
  let f := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff_normed)
  refine ⟨g, f, β.continuous_normed, β.integrable_normed, β.nonneg_normed,
    β.integral_normed, ?_, fun _ ↦ rfl, ?_⟩
  · intro x hx
    have hball : x ∈ Metric.ball (d/2) β.rOut := (β.support_normed_eq (μ := volume)) ▸ hx
    change dist x (d/2) < d/4 at hball
    rw [Real.dist_eq, abs_lt] at hball
    constructor <;> linarith
  · have hz (j : ℕ) : iteratedDeriv j (f : ℝ → ℂ) =ᶠ[cocompact ℝ] 0 := by
      have hfc : HasCompactSupport (f : ℝ → ℂ) := hc
      have hh := hfc.iteratedFDeriv (𝕜 := ℝ) j
      rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at hh
      filter_upwards [hh] with x hx
      rw [iteratedDeriv_eq_iteratedFDeriv, hx]
      rfl
    exact ⟨fun j _ _ ↦ ((hz j).filter_mono atTop_le_cocompact).trans_isBigO
      (Asymptotics.isBigO_zero _ _), fun j _ _ ↦ ((hz j).filter_mono atBot_le_cocompact).trans_isBigO
      (Asymptotics.isBigO_zero _ _)⟩

/-- A unit-mass positive profile supported in the unit interval has a uniform Mellin bound at each
fixed point. -/
private theorem introTrace_positive_divisor_infinite_mellin {g : ℝ → ℝ} {d : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hi : Integrable g) (hn : ∀ x, 0 ≤ g x)
    (hm : (∫ x, g x) = 1) (hs : ∀ x, g x ≠ 0 → d/4 ≤ x ∧ x ≤ d)
    (s : ℂ) : ‖mellin (fun t : ℝ ↦ (g (Real.log t) : ℂ)) s‖ ≤ Real.exp |s.re| := by
  have he : mellin (fun t : ℝ ↦ (g (Real.log t) : ℂ)) s =
      ∫ x : ℝ, (g x : ℂ) * Complex.exp (s * ↑x) := by
    rw [mellin, ← integral_comp_exp]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
      ← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 1
    ring_nf
  rw [he]
  calc
    _ ≤ ∫ x : ℝ, g x * Real.exp |s.re| := norm_integral_le_of_norm_le (hi.mul_const _) (.of_forall fun x ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn x), Complex.norm_exp,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      by_cases hx : g x = 0
      · simp [hx]
      apply mul_le_mul_of_nonneg_left _ (hn x)
      apply Real.exp_le_exp.mpr
      have h := hs x hx
      calc s.re * x ≤ |s.re| * x := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
           _ ≤ |s.re| * 1 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
           _ = _ := mul_one _)
    _ = _ := by rw [integral_mul_const, hm, one_mul]

/-- A short positive profile samples the real part of the gamma kernel near its singularity. Its
integral is at most `-C` once the support is sufficiently close to zero. -/
private theorem introTrace_positive_divisor_infinite_arch {g : ℝ → ℝ} {d k C : ℝ}
    (hd : 0 < d) (hk : 0 < k) (hC : 0 < C) (hdC : 2 * C * d ≤ k)
    (hc : Continuous g) (hi : Integrable g) (hn : ∀ x, 0 ≤ g x)
    (hm : (∫ x, g x) = 1) (hs : ∀ x, g x ≠ 0 → d/4 ≤ x ∧ x ≤ d)
    (p q : ℂ) (hp : ∀ t : ℝ, 0 < t → k*t ≤ d → 1/2 ≤ (Complex.exp (-p * t)).re) :
    (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k p q (fun u ↦ (g u : ℂ)) t).re ≤ -C := by
  let H (t : ℝ) : ℂ := -(k : ℂ) * (g (k*t) : ℂ) * Complex.exp (-p * t) / (1 - (Real.exp (-t) : ℂ))
  have h0 {x : ℝ} (hx : x ≤ 0) : g x = 0 := by
    by_contra h
    linarith [(hs x h).1]
  have hK : (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k p q (fun u ↦ (g u : ℂ)) t) =
      ∫ t in Ioi (0 : ℝ), H t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    simp [heckeArchimedeanDigammaKernel, H, h0 le_rfl, h0 (neg_nonpos.mpr (mul_nonneg hk.le ht.le))]
    ring
  have hsupport : support H ⊆ Icc (d/4/k) (d/k) := by
    intro t ht
    have ht' : g (k*t) ≠ 0 := fun he ↦ ht (by simp [H, he])
    obtain ⟨hl, hu⟩ := hs _ ht'
    exact ⟨(div_le_iff₀ hk).mpr (by linarith), (le_div_iff₀ hk).mpr (by linarith)⟩
  have hI : Integrable H := by
    apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
    have hnum : Continuous (fun t : ℝ ↦ -(k : ℂ) * (g (k*t) : ℂ) * Complex.exp (-p * t)) := by fun_prop
    have hden : Continuous (fun t : ℝ ↦ (1 : ℂ) - (Real.exp (-t) : ℂ)) := by fun_prop
    have hnz (x : ℝ) (hx : x ∈ Icc (d/4/k) (d/k)) : (1 : ℂ) - (Real.exp (-x) : ℂ) ≠ 0 := by
      have hpos : 0 < x := lt_of_lt_of_le (by positivity : 0 < d/4/k) hx.1
      have hne : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      exact sub_ne_zero.mpr (by exact_mod_cast hne.ne.symm)
    exact (hnum.continuousOn.div hden.continuousOn hnz).integrableOn_compact isCompact_Icc
  have hgI : Integrable (fun t ↦ g (k*t)) := (integrable_comp_mul_left_iff g hk.ne').mpr hi
  have hcmp : ∀ t ∈ Ioi (0:ℝ), (H t).re ≤ (-C*k)*g (k*t) := by
    intro t ht
    change 0 < t at ht
    by_cases hgt : g (k*t) = 0
    · simp [H, hgt]
    have hu := (hs (k*t) hgt).2
    have hden : 0 < 1 - Real.exp (-t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    have hdt : 1 - Real.exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
    have hCt : C * t ≤ 1/2 := by
      apply (mul_le_mul_iff_left₀ hk).mp
      nlinarith [mul_le_mul_of_nonneg_left hu (show 0 ≤ 2*C by positivity)]
    have hweight : C ≤ (Complex.exp (-p * t)).re / (1 - Real.exp (-t)) := by
      apply (le_div_iff₀ hden).mpr
      exact ((mul_le_mul_of_nonneg_left hdt hC.le).trans hCt).trans (hp t ht hu)
    have hre : (H t).re = -(k*g (k*t)) * ((Complex.exp (-p * t)).re / (1 - Real.exp (-t))) := by
      change (-(k:ℂ) * (g (k*t) : ℂ) * _ / ((1:ℂ) - (Real.exp (-t) : ℂ))).re = _
      rw [show (1:ℂ) - (Real.exp (-t) : ℂ) = ((1 - Real.exp (-t) : ℝ) : ℂ) by push_cast; rfl,
        Complex.div_ofReal_re]
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [hre]
    nlinarith [mul_le_mul_of_nonneg_left hweight (mul_nonneg hk.le (hn (k*t)))]
  have hmass : (∫ t in Ioi (0 : ℝ), g (k*t)) = k⁻¹ := by
    rw [integral_comp_mul_left_Ioi g 0 hk, mul_zero, setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ h0 (le_of_not_gt hx)), hm, smul_eq_mul, mul_one]
  have hRe : (∫ t in Ioi (0 : ℝ), H t).re = ∫ t in Ioi (0 : ℝ), (H t).re :=
    (integral_re (hI.integrableOn (s := Ioi (0 : ℝ)))).symm
  rw [hK, hRe]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), (-C*k)*g (k*t) :=
      setIntegral_mono_on hI.integrableOn.re (hgI.const_mul _).integrableOn measurableSet_Ioi hcmp
    _ = -C := by rw [integral_const_mul, hmass]; field_simp


/-- A completed Hecke function has at most two poles, so finitely many positive orders force a
finite signed divisor. -/
private theorem introTrace_positive_divisor_infinite_support (χ : U𝔽)
    (h : {z : ℂ | 0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z}.Finite) :
    ∃ S : Finset ℂ, ∀ z ∉ S, MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z = 0 := by
  classical
  let L := continuedCompletedHeckeL χ
  have hL := continuedCompletedHeckeL_spec χ
  have hp : ∃ P : Finset ℂ, ∀ z ∉ P, AnalyticAt ℂ L z := by
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t, ⟨-, -, -, han⟩, -⟩ := completedHeckeL_continuation_simplePoles χ L hL.1 hL.2 hχ
      exact ⟨{Complex.I * (t : ℂ), 1 + Complex.I * (t : ℂ)}, fun z hz ↦ han z (by simpa using hz)⟩
    · exact ⟨∅, fun z _ ↦ (completedHeckeL_continuation_entire χ L hL.1 hL.2 hχ).analyticAt z⟩
  obtain ⟨P, hP⟩ := hp
  refine ⟨P ∪ h.toFinset, fun z hz ↦ ?_⟩
  have hn := hP z (fun h ↦ hz (Finset.mem_union_left _ h))
  have hz' : ¬0 < MeromorphicOn.divisor L univ z := fun hp ↦ hz
    (Finset.mem_union_right _ (h.mem_toFinset.mpr hp))
  apply le_antisymm (le_of_not_gt hz')
  rw [MeromorphicOn.divisor_apply hL.1.meromorphicOn (mem_univ z)]
  have ht := hn.meromorphicOrderAt_nonneg
  change 0 ≤ (meromorphicOrderAt L z).untop₀
  generalize meromorphicOrderAt L z = o at ht ⊢
  cases o with
  | top => simp
  | coe n => simpa using ht

/-- Apply the one-character explicit formula of Theorem B.4.2.2, p. 616, to a profile below the
first prime-power logarithm. The prime and conductor terms vanish. Each infinite place then
contributes less than a uniform lower bound for any finite signed divisor. -/
private theorem introTrace_positive_divisor_infinite_from_digamma (χ : U𝔽) :
    Infinite {z : ℂ // 0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z} := by
  classical
  let L := continuedCompletedHeckeL χ
  let m := MeromorphicOn.divisor L univ
  by_contra hinf
  have : Finite {z : ℂ // 0 < m z} := not_infinite_iff_finite.mp hinf
  obtain ⟨S, hS⟩ := introTrace_positive_divisor_infinite_support χ (Set.toFinite _)
  let M := ∑ z ∈ S, ‖(m z : ℂ)‖ * Real.exp |(z - 1/2).re|
  let C := M + 1
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hC : 0 < C := by dsimp [C]; linarith
  let k (w : InfinitePlace F) : ℝ := if w.IsReal then 1/2 else 1
  let p (w : InfinitePlace F) : ℂ := if hw : w.IsReal then
    let e := (realHeckeCharacter_parameters χ w hw).exists.choose
    (1/2 + e.1 + e.2.val)/2
    else
    let e := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    1/2 + e.1 + (e.2.natAbs : ℂ)/2
  let q (w : InfinitePlace F) : ℂ := if hw : w.IsReal then
    let e := (realHeckeCharacter_parameters χ w hw).exists.choose
    (1/2 - e.1 + e.2.val)/2
    else
    let e := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    1/2 - e.1 + (e.2.natAbs : ℂ)/2
  have hk (w) : 1/2 ≤ k w := by dsimp [k]; split_ifs <;> norm_num
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ w, 1/2 < (Complex.exp (-(p w) * t)).re := by
    apply eventually_all.mpr
    intro w
    have hcont : Continuous (fun t : ℝ ↦ (Complex.exp (-(p w) * t)).re) := by fun_prop
    exact continuousAt_const.eventually_lt (hcont.continuousAt (x := 0)) (by norm_num)
  obtain ⟨e, he, hew⟩ := Metric.eventually_nhds_iff.mp hev
  let d := min (e/4) (min (1/(8*C)) (min (Real.log 2 / 2) (1/2)))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < d := by dsimp [d]; positivity
  have hde : d ≤ e/4 := min_le_left _ _
  have hdC : d ≤ 1/(8*C) := (min_le_right _ _).trans (min_le_left _ _)
  have hds : d ≤ min (Real.log 2/2) (1/2) := (min_le_right _ _).trans (min_le_right _ _)
  have hdlog : d < Real.log 2 := by linarith [hds.trans (min_le_left _ _)]
  have hd1 : d ≤ 1 := by linarith [hds.trans (min_le_right _ _)]
  obtain ⟨g, f, hc, hi, hn, hm, hs, hf, hexf⟩ := introTrace_positive_divisor_infinite_test hd
  have hfg : (f : ℝ → ℂ) = fun x ↦ (g x : ℂ) := funext hf
  have hvan {x : ℝ} (hx : x ≤ 0 ∨ d < x) : f x = 0 := by
    rw [hf, Complex.ofReal_eq_zero]
    by_contra h
    rcases hx with h₁ | h₁ <;> linarith [(hs _ h).1, (hs _ h).2]
  have hz := hvan (x := 0) (Or.inl le_rfl)
  have hpr (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
      f (((n + 1 : ℕ) : ℝ) * Real.log (v.asIdeal.absNorm : ℝ)) = 0 ∧
      f (-(((n + 1 : ℕ) : ℝ) * Real.log (v.asIdeal.absNorm : ℝ))) = 0 := by
    have hv : (2 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hℓ := Real.log_le_log (by norm_num : (0:ℝ)<2) hv
    have hn₁ : (1 : ℝ) ≤ (n+1:ℕ) := by exact_mod_cast Nat.succ_pos n
    have hx : d < ((n + 1 : ℕ) : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) := calc
      _ < Real.log 2 := hdlog
      _ ≤ _ := hℓ.trans (le_mul_of_one_le_left (by linarith) hn₁)
    exact ⟨hvan (Or.inr hx), hvan (Or.inl (by linarith))⟩
  let A (w : InfinitePlace F) := ∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel (k w) (p w) (q w) f t
  have hA (w : InfinitePlace F) : (A w).re ≤ -C := by
    dsimp only [A]
    rw [hfg]
    refine introTrace_positive_divisor_infinite_arch hd (lt_of_lt_of_le (by norm_num) (hk w))
      hC ?_ hc hi hn hm hs _ _ (fun t ht hu ↦ ?_)
    · have h := (le_div_iff₀ (by positivity : 0 < 8*C)).mp hdC
      linarith [hk w]
    · apply (hew (show dist t 0 < e from ?_) w).le
      rw [Real.dist_eq, sub_zero, abs_of_pos ht]
      nlinarith [mul_le_mul_of_nonneg_right (hk w) ht.le]
  have hL := continuedCompletedHeckeL_spec χ
  have form := (hasSum_heckeExplicitFormula χ f hexf L hL.1 hL.2).tsum_eq
  have hpSum : ∑' j : HeightOneSpectrum (𝓞 F) × ℕ,
      (if (ideleClassNormTwist χ 0).IsUnramifiedAt j.1 then
        let x := ((j.2 + 1 : ℕ) : ℝ) * Real.log (j.1.asIdeal.absNorm : ℝ)
        ((Real.log (j.1.asIdeal.absNorm : ℝ) * Real.exp (-x/2) : ℝ) : ℂ) *
          (((ideleClassNormTwist χ 0).localValue j.1) ^ (j.2 + 1) * f x +
           ((ideleClassNormTwist χ⁻¹ 0).localValue j.1) ^ (j.2 + 1) * f (-x))
       else 0) = 0 := by
    rw [tsum_congr (g := fun _ ↦ (0 : ℂ)) ?_, tsum_zero]
    rintro ⟨v,n⟩
    simp only [(hpr v n).1, (hpr v n).2, mul_zero, add_zero, ite_self]
  rw [hpSum, hz, mul_zero, sub_zero, zero_add] at form
  have hid : (∑ z ∈ S, (m z : ℂ) * mellin (fun t : ℝ ↦ f (Real.log t)) (z-1/2)) = ∑ w, A w := by
    rw [tsum_eq_sum (s := S) (fun z hz ↦ by rw [hS z hz, Int.cast_zero, zero_mul])] at form
    refine form.trans (Finset.sum_congr rfl fun w _ ↦ ?_)
    by_cases hw : w.IsReal <;> simp [hw, A, k, p, q]
  have hb : ‖∑ w, A w‖ ≤ M := by
    rw [← hid]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ ↦ ?_)
    rw [norm_mul, hfg]
    exact mul_le_mul_of_nonneg_left (introTrace_positive_divisor_infinite_mellin hd hd1 hi hn hm hs _) (norm_nonneg _)
  have hreal : (∑ w, A w).re ≤ -C := by
    rw [Complex.re_sum]
    calc
      _ ≤ ∑ _w : InfinitePlace F, -C := Finset.sum_le_sum fun w _ ↦ hA w
      _ = (Fintype.card (InfinitePlace F) : ℝ) * (-C) := by simp
      _ ≤ -C := by
        have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
        nlinarith
  have hh := (abs_le.mp ((Complex.abs_re_le_norm (∑ w, A w)).trans hb)).1
  dsimp [C] at hreal
  linarith

/-- Paper: §1.4.3, p. 29. The completed L-function of the trivial rational character
has infinitely many distinct positive-divisor zeros. Otherwise its smoothed spectral
sum in the unit window would have a finite limit at parameter two, since each
individual Mellin moment converges there. -/
theorem introTrace_rat_positive_divisor_infinite :
    Infinite {z : ℂ // 0 < MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) 1) univ z} := by
  exact introTrace_positive_divisor_infinite_from_digamma (F := ℚ) 1

/-- Paper: §1.4.4, p. 29. The negative prime-power norms lie below one,
where every cutoff test vanishes. -/
theorem introTraceApprox_primePower_inv_zero (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) (v : V) (m : ℕ) (_hm : 0 < m) :
    approx(h, ρ, n, z) ((q(v) ^ m)⁻¹) = 0 := by
  have hq : 1 ≤ q(v) := by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hle : (q(v) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hq)
  apply image_eq_zero_of_notMem_tsupport
  exact fun ht ↦ hle.not_gt (introTraceApprox_support h ρ _hA n z ht)

/-- Distinct pairs of a finite place and an exponent give distinct positive prime powers. -/
private theorem introTraceApprox_primeSum_tendsto_injective :
    Injective (fun p : V × ℕ ↦ p.1.asIdeal ^ (p.2 + 1)) := by
  rintro ⟨v, k⟩ ⟨w, j⟩ hvw
  simp only at hvw
  have hv : v = w := by
    have hd : v.asIdeal ∣ w.asIdeal ^ (j + 1) := hvw ▸ dvd_pow_self _ (Nat.succ_ne_zero k)
    have hle : w.asIdeal ≤ v.asIdeal := Ideal.le_of_dvd (v.prime.dvd_of_dvd_pow hd)
    exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hle).symm
  subst hv
  have hm := congrArg (multiplicity v.asIdeal) hvw
  rw [multiplicity_pow_self_of_prime v.prime, multiplicity_pow_self_of_prime v.prime] at hm
  simp only [Prod.mk.injEq, true_and]
  omega

/-- Paper: §1.4.4, p. 29. The finite terms converge locally uniformly to
the negative logarithmic derivative of the finite Hecke L-function.
Deviation: The sign is negative by differentiation of the Euler product,
as in `finiteHeckeL_logDeriv_hasSum_ideals`. The same argument works on
`Re z > 1/2`, the absolute-convergence region for `s = z + 1/2`.
The local coefficients include the unit averaging in the corrected trace formula. -/
theorem introTraceApprox_primeSum_tendsto (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) :
    TendstoLocallyUniformlyOn (fun n z ↦ primeSum(χ, approx(h, ρ, n, z)))
      (fun z ↦ -logDeriv finiteL(χ) (z + 1 / 2)) atTop right(1 / 2) := by
  classical
  let L := (finiteHeckeL_exists_continuation (F := F) χ).choose
  have hL := (finiteHeckeL_exists_continuation (F := F) χ).choose_spec
  let c := ideleClassNormTwist χ 0
  -- The prime-power term of a radial profile, without the vanishing negative shell.
  let T : (ℝ → ℂ) → V × ℕ → ℂ := fun A p ↦
    if c.IsUnramifiedAt p.1 then
      (Real.log q(p.1) : ℂ) * (c.localValue p.1 ^ (p.2 + 1) * A (q(p.1) ^ (p.2 + 1))) /
        (q(p.1) : ℂ) ^ (((p.2 + 1 : ℕ) : ℂ) / 2)
    else 0
  have hT (A : ℝ → ℂ) (v : V) (k : ℕ) (hA0 : A ((q(v) ^ (k + 1))⁻¹) = 0) :
      introTracePrimePower χ A v k = T A (v, k) := by
    simp only [introTracePrimePower, T, hA0, mul_zero, add_zero]
    rfl
  have hq (v : V) : 1 < q(v) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqm (v : V) (k : ℕ) : 1 < q(v) ^ (k + 1) := one_lt_pow₀ (hq v) (Nat.succ_ne_zero k)
  -- The terms converge along `atTop ×ˢ 𝓝 z`.
  have hconv (z : ℂ) (p : V × ℕ) :
      Tendsto (fun r : ℕ × ℂ ↦ T approx(h, ρ, r.1, r.2) p) (atTop ×ˢ 𝓝 z)
        (𝓝 (T (introTracePower z) p)) := by
    by_cases hu : c.IsUnramifiedAt p.1
    · simp only [T, if_pos hu]
      exact (tendsto_const_nhds.mul (tendsto_const_nhds.mul
        (introTraceApprox_mellin_tendsto_radial _hA z (hqm p.1 p.2)))).div_const _
    · simp only [T, if_neg hu]
      exact tendsto_const_nhds
  have hconv' (z : ℂ) (p : V × ℕ) :
      Tendsto (fun r : ℕ × ℂ ↦ T (introTracePower r.2) p) (atTop ×ˢ 𝓝 z)
        (𝓝 (T (introTracePower z) p)) := by
    by_cases hu : c.IsUnramifiedAt p.1
    · simp only [T, if_pos hu]
      exact (tendsto_const_nhds.mul (tendsto_const_nhds.mul
        ((introTracePower_differentiable _).continuous.continuousAt.tendsto.comp tendsto_snd))).div_const _
    · simp only [T, if_neg hu]
      exact tendsto_const_nhds
  -- Domination by a summable sequence.
  have hdom (a : ℝ) (ha : 1 / 2 < a) : ∃ B : V × ℕ → ℝ, Summable B ∧
      ∀ (A : ℝ → ℂ), (∀ t, 1 < t → ‖A t‖ ≤ ((1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)) * t ^ (-a)) →
        ∀ p, ‖T A p‖ ≤ B p := by
    let C := (1 / 2 : ℝ) ^ (-a) + 2 ^ (-a)
    let σ := a + 1 / 2
    let r := (1 + σ) / 2
    let ε := σ - r
    have hr : 1 < r := by simp only [r, σ]; linarith
    have hε : 0 < ε := by simp only [ε, r, σ]; linarith
    have hC : 0 ≤ C := by positivity
    let N : V × ℕ → ℝ := fun p ↦ ((p.1.asIdeal ^ (p.2 + 1)).absNorm : ℝ)
    have hN (p : V × ℕ) : N p = q(p.1) ^ (p.2 + 1) := by simp [N, map_pow]
    refine ⟨fun p ↦ C * (N p ^ (-r) / ε), ?_, fun A hA p ↦ ?_⟩
    · exact (((summable_absNorm_rpow F hr).comp_injective
        introTraceApprox_primeSum_tendsto_injective).div_const ε).mul_left C
    have hB0 : 0 ≤ C * (N p ^ (-r) / ε) := by
      have : 0 ≤ N p := by positivity
      positivity
    by_cases hu : c.IsUnramifiedAt p.1
    swap
    · simp only [T, if_neg hu, norm_zero]; exact hB0
    simp only [T, if_pos hu]
    set t := q(p.1) ^ (p.2 + 1)
    have ht := hqm p.1 p.2
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hq0 : 0 < q(p.1) := zero_lt_one.trans (hq p.1)
    have hlog : 0 ≤ Real.log q(p.1) := Real.log_nonneg (hq p.1).le
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow,
      one_mul, Complex.norm_real, Real.norm_of_nonneg hlog,
      Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    have hre : (((p.2 + 1 : ℕ) : ℂ) / 2).re = ((p.2 + 1 : ℕ) : ℝ) / 2 := by simp
    rw [hre]
    have hsq : q(p.1) ^ (((p.2 + 1 : ℕ) : ℝ) / 2) = t ^ (1 / 2 : ℝ) := by
      rw [div_eq_mul_one_div, Real.rpow_mul hq0.le, Real.rpow_natCast]
    have hNt : N p = t := hN p
    rw [hsq, ← hNt]
    have hN1 : 1 < N p := hNt ▸ ht
    have hNpos : 0 < N p := zero_lt_one.trans hN1
    have hqN : q(p.1) ≤ N p := by
      rw [hNt]
      calc q(p.1) = q(p.1) ^ 1 := (pow_one _).symm
        _ ≤ t := pow_le_pow_right₀ (hq p.1).le (Nat.succ_pos _)
    have key : N p ^ (-r) = N p ^ ε * N p ^ (-a) / N p ^ (1 / 2 : ℝ) := by
      rw [show -r = ε + -a - 1 / 2 by simp only [ε, r, σ]; ring,
        Real.rpow_sub hNpos, Real.rpow_add hNpos]
    calc Real.log q(p.1) * ‖A (N p)‖ / N p ^ (1 / 2 : ℝ)
        ≤ (N p ^ ε / ε) * (C * N p ^ (-a)) / N p ^ (1 / 2 : ℝ) := by
          apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hNpos.le _)
          exact mul_le_mul ((Real.log_le_log hq0 hqN).trans (Real.log_le_rpow_div hNpos.le hε))
            (hA _ hN1) (norm_nonneg _) (div_nonneg (Real.rpow_nonneg hNpos.le _) hε.le)
      _ = C * (N p ^ (-r) / ε) := by
          rw [key]
          ring
  -- The limit is the logarithmic derivative on the half-plane.
  have hid (w : ℂ) (hw : 1 / 2 < w.re) :
      ∑' p, T (introTracePower w) p = -logDeriv L (w + 1 / 2) := by
    have hs : w + 1 / 2 ∈ Complex.re ⁻¹' Ioi (1 : ℝ) := by
      change 1 < (w + 1 / 2).re
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
      linarith
    have hS := (finiteHeckeL_logDeriv_hasSum_ideals χ L hL.1 hL.2 ⟨w + 1 / 2, hs⟩).2.2
    let φ : V × ℕ → {I : Ideal (𝓞 F) // I ≠ ⊥} := fun p ↦
      ⟨p.1.asIdeal ^ (p.2 + 1), pow_ne_zero _ p.1.ne_bot⟩
    have hφ : Injective φ := fun p p' hp ↦
      introTraceApprox_primeSum_tendsto_injective (congrArg Subtype.val hp)
    have hzero : ∀ I ∉ range φ, -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val /
        (I.val.absNorm : ℂ) ^ (w + 1 / 2) = 0 := by
      intro I hI
      have hΛ : idealVonMangoldt I.val = 0 := by
        unfold idealVonMangoldt
        rw [dif_neg]
        rintro ⟨v, k, hk, hvk⟩
        refine hI ⟨(v, k - 1), Subtype.ext ?_⟩
        change v.asIdeal ^ (k - 1 + 1) = I.val
        rw [Nat.sub_add_cancel hk, hvk]
      simp [heckeIdealVonMangoldt, hΛ]
    have hS' := ((hφ.hasSum_iff hzero).mpr hS).neg
    rw [← hS'.tsum_eq]
    congr 1
    funext p
    obtain ⟨v, k⟩ := p
    change T (introTracePower w) (v, k) =
      -(-heckeIdealVonMangoldt c (v.asIdeal ^ (k + 1)) /
        ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ^ (w + 1 / 2))
    rw [neg_div, neg_neg, heckeIdealVonMangoldt, heckeIdealValue_prime_pow _ v (Nat.succ_pos k),
      idealVonMangoldt_prime_pow v (Nat.succ_pos k)]
    by_cases hu : c.IsUnramifiedAt v
    swap
    · simp [T, hu]
    simp only [T, if_pos hu, introTracePower, if_pos (hqm v k)]
    have hq0 : 0 < q(v) := zero_lt_one.trans (hq v)
    set t := q(v) ^ (k + 1)
    have ht0 : 0 < t := zero_lt_one.trans (hqm v k)
    have hN : (((v.asIdeal ^ (k + 1)).absNorm : ℕ) : ℂ) = (t : ℂ) := by simp [t, map_pow]
    have hsq : (q(v) : ℂ) ^ (((k + 1 : ℕ) : ℂ) / 2) = (t : ℂ) ^ (1 / 2 : ℂ) := by
      have h1 : (((k + 1 : ℕ) : ℂ) / 2) = ((((k + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
      have h2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [h1, h2, ← Complex.ofReal_cpow hq0.le, ← Complex.ofReal_cpow ht0.le]
      congr 1
      rw [div_eq_mul_one_div, Real.rpow_mul hq0.le, Real.rpow_natCast]
    have ht0' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    rw [hN, hsq, Complex.cpow_add _ _ ht0', Complex.cpow_neg]
    field_simp
  -- Assemble the locally uniform convergence.
  apply (isOpen_Ioi.preimage Complex.continuous_re).tendstoLocallyUniformlyOn_iff_forall_tendsto.2
  intro z hz
  obtain ⟨a, hza, haz⟩ := exists_between (show (1 / 2 : ℝ) < z.re from hz)
  obtain ⟨B, hB, hbd⟩ := hdom a hza
  let l : Filter (ℕ × ℂ) := atTop ×ˢ 𝓝 z
  have hnear : ∀ᶠ r : ℕ × ℂ in l, a ≤ r.2.re :=
    (Complex.continuous_re.continuousAt.tendsto.comp tendsto_snd).eventually (le_mem_nhds haz)
  have hpow : Tendsto (fun r : ℕ × ℂ ↦ -logDeriv L (r.2 + 1 / 2)) l
      (𝓝 (-logDeriv L (z + 1 / 2))) := by
    have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := l) hB (hconv' z) (by
      filter_upwards [hnear] with r hr p
      exact hbd _ (fun t ht ↦ introTraceApprox_mellin_tendsto_power_bound (x := t) ht (by simp) hr) p)
    rw [hid z hz] at hlim
    refine hlim.congr' ?_
    filter_upwards [hnear] with r hr
    exact hid r.2 (hza.trans_le hr)
  have happ : Tendsto (fun r : ℕ × ℂ ↦ ∑' p : V × ℕ, introTracePrimePower χ approx(h, ρ, r.1, r.2) p.1 p.2)
      l (𝓝 (-logDeriv L (z + 1 / 2))) := by
    have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := l) hB (hconv z) (by
      filter_upwards [hnear, (show Tendsto Prod.fst l atTop from tendsto_fst).eventually
          (introTraceApprox_mellin_tendsto_cutoff_bound _hA a)] with r hr hc p
      exact hbd _ (fun t ht ↦ hc r.2 t hr ht) p)
    rw [hid z hz] at hlim
    refine hlim.congr' (Eventually.of_forall fun r ↦ ?_)
    refine tsum_congr fun p ↦ (hT _ p.1 p.2 ?_).symm
    exact introTraceApprox_primePower_inv_zero h ρ _hA r.1 r.2 p.1 (p.2 + 1) (Nat.succ_pos _)
  exact (hpow.prodMk_nhds happ).mono_right (nhds_le_uniformity _)

open Classical in
/-- Paper: §1.4.5, pp. 29–30. If the archimedean and zero terms together
converge on the common half-plane to the restriction of a holomorphic
function on the right of the window, that function extends the regularized
shifted logarithmic derivative.
Deviation: The two polar moments are added to the logarithmic derivative
because the finite sum tends to its negative. The character is normalized
on the norm section so the poles have the printed coordinates. The corrected
trace formula gives the identity at each cutoff with the centered zero window
and normalized local terms. Neither separate Montel limit in the sketch
supplies the hypothesis on the combined terms. -/
theorem introTrace_logDeriv_extension_of_limit (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    (a : ℝ) (_ha : 0 < a) (h ρ : ℕ → ℝ → ℝ) (_hA : IsIntroTraceApproximation h ρ)
    (H : ℂ → ℂ) (_hH : AnalyticOnNhd ℂ H right(a))
    (_hlim : TendstoLocallyUniformlyOn
      (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a)
      H atTop right(max a 1)) :
    EqOn H (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
      if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1) := by
  classical
  intro z hz
  have hz₁ : 1 < z.re := (le_max_right a 1).trans_lt hz
  have hp : (1 / 2 : ℂ).re < z.re := by norm_num; linarith
  have hm : (-1 / 2 : ℂ).re < z.re := by norm_num; linarith
  have hprime := (introTraceApprox_primeSum_tendsto χ h ρ _hA).tendsto_at
    (a := z) (show 1 / 2 < z.re by linarith)
  let P (n : ℕ) := if χ = 1 then introTraceMellin approx(h, ρ, n, z) (1 / 2) +
    introTraceMellin approx(h, ρ, n, z) (-1 / 2) else 0
  have he (n : ℕ) : archSum(χ, approx(h, ρ, n, z)) +
      introTraceSpectralSum χ approx(h, ρ, n, z) a = P n - primeSum(χ, approx(h, ρ, n, z)) := by
    obtain ⟨φ, hφ⟩ := introTraceApprox_exists_bruhat χ h ρ _hA n z
    have hzero : approx(h, ρ, n, z) 1 = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hu ↦ lt_irrefl _ (introTraceApprox_support h ρ _hA n z hu))
    have hsum := (introTrace_characterTrace τ _hτ χ _hχ _ hzero φ hφ a _ha).2.2.tsum_eq
    change introTraceSpectralSum χ approx(h, ρ, n, z) a =
      P n - archSum(χ, approx(h, ρ, n, z)) - primeSum(χ, approx(h, ρ, n, z)) at hsum
    rw [hsum]
    ring
  have hpolar : Tendsto P atTop
      (𝓝 (if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0)) := by
    by_cases htriv : χ = 1
    · simp only [P, ite_eq_left htriv]
      have h₁ := (introTraceApprox_mellin_tendsto h ρ _hA (1 / 2)).tendsto_at hp
      have h₂ := (introTraceApprox_mellin_tendsto h ρ _hA (-1 / 2)).tendsto_at hm
      rw [(introTracePower_mellin z _ hp).2] at h₁
      rw [(introTracePower_mellin z _ hm).2] at h₂
      simpa [sub_neg_eq_add, neg_div, add_comm] using h₁.add h₂
    · simp [P, htriv]
  have hlim := _hlim.tendsto_at hz
  simp_rw [he] at hlim
  simpa only [sub_neg_eq_add, add_comm] using tendsto_nhds_unique hlim (hpolar.sub hprime)

-- TODO(paper-gap): The reference to §5.1 on p. 29 (also p. 55) supplies no
-- continuation argument. The corrected cutoff identity does not itself bound
-- the separate terms or provide the holomorphic limit of their sum.

open Classical in
/-- Convergence of the prime and polar terms gives the entire shifted Euler half-plane. -/
private theorem introTrace_combined_euler_of_fixed_identity (χ : U𝔽) {a : ℝ}
    (h ρ : ℕ → ℝ → ℝ) (_hA : IsIntroTraceApproximation h ρ)
    (harch : ∀ n z, archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a =
      (if χ = 1 then introTraceMellin approx(h, ρ, n, z) (1 / 2) +
        introTraceMellin approx(h, ρ, n, z) (-1 / 2) else 0) - primeSum(χ, approx(h, ρ, n, z))) :
    TendstoLocallyUniformlyOn
      (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) +
        introTraceSpectralSum χ approx(h, ρ, n, z) a)
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) atTop right(1/2) := by
  have hsub₁ : right(1/2) ⊆ right(((1/2 : ℂ)).re) := by norm_num
  have hsub₂ : right(1/2) ⊆ right(((-1/2 : ℂ)).re) := by
    intro z hz
    change (-1/2 : ℂ).re < z.re
    norm_num
    linarith [show (1/2:ℝ) < z.re from hz]
  let P : ℕ → ℂ → ℂ := fun n z ↦ if χ = 1 then
    introTraceMellin approx(h, ρ, n, z) (1 / 2) +
      introTraceMellin approx(h, ρ, n, z) (-1 / 2) else 0
  have hM₁ : TendstoLocallyUniformlyOn (fun n z ↦ introTraceMellin approx(h, ρ, n, z) (1 / 2))
      (fun z ↦ 1 / (z - 1 / 2)) atTop right(1/2) :=
    ((introTraceApprox_mellin_tendsto h ρ _hA (1 / 2)).mono hsub₁).congr_right
      fun z hz ↦ (introTracePower_mellin z (1 / 2) (hsub₁ hz)).2
  have hM₂ : TendstoLocallyUniformlyOn (fun n z ↦ introTraceMellin approx(h, ρ, n, z) (-1 / 2))
      (fun z ↦ 1 / (z + 1 / 2)) atTop right(1/2) :=
    ((introTraceApprox_mellin_tendsto h ρ _hA (-1 / 2)).mono hsub₂).congr_right fun z hz ↦ by
      have hp := (introTracePower_mellin z (-1 / 2) (hsub₂ hz)).2
      show introTraceMellin (introTracePower z) (-1 / 2) = 1 / (z + 1 / 2)
      rw [hp]
      congr 1
      ring
  have hzero : TendstoLocallyUniformlyOn (fun (_ : ℕ) (_ : ℂ) ↦ (0 : ℂ)) (fun _ ↦ 0)
      atTop right(1/2) := by
    intro u hu x _
    exact ⟨univ, univ_mem, Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hu⟩
  have hP : TendstoLocallyUniformlyOn P
      (fun z ↦ if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) atTop
      right(1/2) := by
    by_cases htriv : χ = 1
    · subst htriv
      have hsum := hM₁.add hM₂
      refine (hsum.congr (fun n ↦ ?_)).congr_right (fun z _ ↦ ?_)
      · intro z _
        simp [P, Pi.add_apply]
      · simp [Pi.add_apply, add_comm]
    · refine (hzero.congr (fun n ↦ ?_)).congr_right (fun z _ ↦ ?_)
      · intro z _
        simp [P, htriv]
      · simp [htriv]
  have hpr := introTraceApprox_primeSum_tendsto χ h ρ _hA
  have hcomb := hP.sub hpr
  refine (hcomb.congr (fun n ↦ ?_)).congr_right (fun z _ ↦ ?_)
  · intro z _
    exact (harch n z).symm
  · show (if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) -
      -logDeriv finiteL(χ) (z + 1 / 2) = logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0
    rw [sub_neg_eq_add, add_comm]

open Classical in
/-- A fixed-cutoff identity gives the overlap limit by convergence of its prime and polar terms. -/
private theorem introTrace_combined_limit_of_fixed_identity (χ : U𝔽) {a : ℝ}
    (h ρ : ℕ → ℝ → ℝ) (_hA : IsIntroTraceApproximation h ρ)
    (harch : ∀ n z, archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a =
      (if χ = 1 then introTraceMellin approx(h, ρ, n, z) (1 / 2) +
        introTraceMellin approx(h, ρ, n, z) (-1 / 2) else 0) - primeSum(χ, approx(h, ρ, n, z))) :
    TendstoLocallyUniformlyOn
      (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) +
        introTraceSpectralSum χ approx(h, ρ, n, z) a)
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) atTop right(max a 1) := by
  apply (introTrace_combined_euler_of_fixed_identity χ h ρ _hA harch).mono
  intro z hz
  have h1 : (1 : ℝ) < z.re := (le_max_right a 1).trans_lt hz
  change (1 : ℝ) / 2 < z.re
  linarith

open Classical in
/-- The overlap limit follows from the prime and polar limits whenever the
exterior-zero terms cancel in the fixed-cutoff trace identity. -/
private theorem introTrace_combined_limit_of_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    {a : ℝ}
    (hTail : ∀ φ : D𝔽, (∀ g : (ideleClassNorm F).ker, φ.val g = 0) → HasSum
      (fun z : {p : {η : U𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1} × ℂ //
        0 < zeroOrder(p.1.val, p.2) ∧ a ≤ |p.2.re - 1 / 2|} ↦
        (zeroOrder(z.val.1.val, z.val.2) : ℂ) *
          ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2) g ∂ideleClassTamagawaMeasure F) 0)
    (h ρ : ℕ → ℝ → ℝ) (_hA : IsIntroTraceApproximation h ρ) :
    TendstoLocallyUniformlyOn
      (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) +
        introTraceSpectralSum χ approx(h, ρ, n, z) a)
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) atTop right(max a 1) := by
  let P : ℕ → ℂ → ℂ := fun n z ↦ if χ = 1 then
    introTraceMellin approx(h, ρ, n, z) (1 / 2) +
      introTraceMellin approx(h, ρ, n, z) (-1 / 2) else 0
  apply introTrace_combined_limit_of_fixed_identity χ h ρ _hA
  intro n z
  obtain ⟨φ, hφ⟩ := introTraceApprox_exists_bruhat χ h ρ _hA n z
  have hz : approx(h, ρ, n, z) 1 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hu ↦ lt_irrefl _ (introTraceApprox_support h ρ _hA n z hu))
  have hsum := (introTrace_characterTrace_of_exteriorZeros τ _hτ χ _hχ _ hz φ hφ a (hTail φ)).2.2.tsum_eq
  change introTraceSpectralSum χ approx(h, ρ, n, z) a =
    P n z - archSum(χ, approx(h, ρ, n, z)) - primeSum(χ, approx(h, ρ, n, z)) at hsum
  rw [hsum]
  ring

open Classical in
/-- Paper: §1.4.5, pp. 29–30. For any approximating family the combined
archimedean and spectral terms converge locally uniformly on `Re z > max a 1`
to the regularized shifted logarithmic derivative: the fixed-cutoff trace
identity writes the combined sum as the polar moments minus the prime-power
sum, and both of those converge there. -/
private theorem introTrace_combined_limit_extension_overlap (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    {a : ℝ} (_ha : 0 < a) (h ρ : ℕ → ℝ → ℝ) (_hA : IsIntroTraceApproximation h ρ) :
    TendstoLocallyUniformlyOn
      (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) +
        introTraceSpectralSum χ approx(h, ρ, n, z) a)
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) atTop right(max a 1) := by
  apply introTrace_combined_limit_of_exteriorZeros τ _hτ χ _hχ _ h ρ _hA
  intro φ hz
  simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ, Set.indicator_univ] using
    traceFormula_exteriorZeros τ _hτ φ hz _ha

/-- Pair the two translates 1+x and 1−x in the complex plane. Away from x=0 the parallelogram
identity puts one outside the unit disk. The limiting lower bound is a positive multiple of the
nonintegrable density ‖x‖⁻². -/
private theorem introTraceApprox_trivial_archimedean_complexDensity (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) :
    let b (n : ℕ) (t : ℝ) := (introTraceApprox (h n) (ρ n) 2 t).re
    let G (n : ℕ) (u : ℂ) := (‖u‖^2)⁻¹ * (b n (‖u‖^2) * ‖u‖ / ‖1-u‖^2)
    Tendsto (fun n ↦ ∫ u, G n u) atTop atTop := by
  intro b G
  have hb (n : ℕ) (t : ℝ) : 0 ≤ b n t := by
    obtain ⟨g, hg, he⟩ := introTraceApprox_rat_spectral_tendsto_atBot_profile h ρ hA n
    simpa [b, he] using hg t
  have hG (n : ℕ) (u : ℂ) : 0 ≤ G n u := mul_nonneg (by positivity) (div_nonneg (mul_nonneg (hb _ _) (norm_nonneg _)) (sq_nonneg _))
  have hi (n : ℕ) : Integrable (G n) := by
    obtain ⟨hf, hc⟩ := introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n 2
    have hu := (introTraceApprox_archimedean_sub_shiftTwo_complexFixed _ hf hc (introTraceApprox_support h ρ hA n 2)).re
    exact hu.congr (.of_forall fun u ↦ by simp only [G, b, RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.div_ofReal_re, Complex.re_mul_ofReal])
  let B (x : ℂ) := (1/256 : ℝ) * ‖x‖ ^ (-2 : ℝ)
  let S := Metric.ball (0 : ℂ) (1/2)
  have hq := introTraceApprox_trivial_archimedean_fatou volume (fun n x ↦ G n (1+x) + G n (1-x)) B S measurableSet_ball
    (fun n ↦ ((hi n).comp_add_left 1).add ((integrable_comp_sub_left _ 1).2 (hi n)))
    (fun n x ↦ add_nonneg (hG _ _) (hG _ _)) (by dsimp [B]; fun_prop)
    (fun x ↦ by dsimp [B]; positivity)
  have hbad : ¬ IntegrableOn B S := by
    intro h'
    have hs : IntegrableOn (fun x : ℂ ↦ ‖x‖ ^ (-2 : ℝ)) S := by
      simpa [B, IntegrableOn, mul_assoc] using h'.const_mul 256
    have hh := (External.TauCeti.integrableOn_norm_rpow_ball_iff (by norm_num : (0:ℝ)<1/2)).1 hs
    norm_num [Complex.finrank_real_complex] at hh
  have hlow (u : ℂ) (hu : 1 < ‖u‖) (hu' : ‖u‖ ≤ 2) :
      ∀ᶠ n in atTop, 1/256 / ‖1-u‖^2 ≤ G n u := by
    let r := ‖u‖^2
    have hr : 1 < r := by dsimp [r]; nlinarith
    have hr' : r ≤ 4 := by dsimp [r]; nlinarith [sq_nonneg (2-‖u‖), norm_nonneg u, mul_self_le_mul_self (norm_nonneg u) hu']
    have hseq : Tendsto (fun n : ℕ ↦ (n, (2 : ℂ))) atTop (atTop ×ˢ 𝓝 2) := tendsto_id.prodMk tendsto_const_nhds
    have hp := Complex.continuous_re.continuousAt.tendsto.comp ((introTraceApprox_mellin_tendsto_radial hA 2 hr).comp hseq)
    have hp' : 1/64 < (introTracePower 2 r).re := by
      simp [introTracePower, hr, Complex.cpow_neg, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
      apply (lt_inv_comm₀ (by norm_num) (by positivity)).2
      nlinarith [mul_self_le_mul_self (by linarith : 0 ≤ r) hr']
    filter_upwards [hp.eventually (lt_mem_nhds hp')] with n hn
    change 1/64 < b n r at hn
    change _ ≤ r⁻¹ * (b n r * ‖u‖ / _)
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hr0 : 0 < r := by linarith
    have hi4 : 1/4 ≤ r⁻¹ := by simpa only [one_div] using inv_anti₀ hr0 hr'
    calc 1/256 = (1/4)*(1/64)*(1:ℝ) := by norm_num
      _ ≤ r⁻¹ * b n r * ‖u‖ := by gcongr <;> linarith
      _ = _ := by ring
  have hp := hq hbad (by
    intro x hx
    obtain rfl | hx' := eq_or_ne x 0
    · exact .of_forall fun n ↦ by simpa [B] using add_nonneg (hG n (1+0)) (hG n (1-0))
    have hxn : ‖x‖ < 1/2 := mem_ball_zero_iff.mp hx
    have hp : ‖1+x‖ ≤ 2 := by have := norm_add_le (1:ℂ) x; rw [norm_one] at this; linarith
    have hm : ‖1-x‖ ≤ 2 := by have := norm_sub_le (1:ℂ) x; rw [norm_one] at this; linarith
    have hor : 1 < ‖1+x‖ ∨ 1 < ‖1-x‖ := by
      by_contra! hn
      have he := parallelogram_law_with_norm ℝ (1:ℂ) x
      rw [norm_one] at he
      nlinarith [mul_self_le_mul_self (norm_nonneg _) hn.1, mul_self_le_mul_self (norm_nonneg _) hn.2, sq_pos_of_pos (norm_pos_iff.mpr hx')]
    rcases hor with hl | hl
    · filter_upwards [hlow (1+x) hl hp] with n hn
      have haux : B x ≤ G n (1+x) := by simpa [B, Real.rpow_neg (norm_nonneg _), div_eq_mul_inv] using hn
      linarith [hG n (1-x)]
    · filter_upwards [hlow (1-x) hl hm] with n hn
      have haux : B x ≤ G n (1-x) := by simpa [B, Real.rpow_neg (norm_nonneg _), div_eq_mul_inv] using hn
      linarith [hG n (1+x)])
  apply tendsto_atTop.2
  intro a
  filter_upwards [tendsto_atTop.1 hp (a+a)] with n hn
  rw [integral_add ((hi n).comp_add_left 1) ((integrable_comp_sub_left _ 1).2 (hi n)), integral_add_left_eq_self, integral_sub_left_eq_self] at hn
  linarith

/-- The complex Tamagawa measure has twice the Euclidean density, so the divergent real integral
has coefficient 1/π. -/
private theorem introTraceApprox_trivial_archimedean_complexPlace
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (v : InfinitePlace F) (hv : v.IsComplex) :
    Tendsto (fun n ↦ (introTraceArchimedean (F := F) 1 approx(h, ρ, n, (2 : ℂ)) v).re) atTop atTop := by
  classical
  have hν : (2 • (volume : Measure ℂ)).restrict {(0 : ℂ)}ᶜ = 2 • volume := by
    simp [two_smul, Measure.restrict_add, restrict_compl_singleton]
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
  obtain ⟨m, _, _, hm, he⟩ := introTraceApprox_archimedean_sub_shiftTwo_coordinate
    (F := F) 1 v e (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).isometry
    (2 • volume) hν (dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hv))
  have hlim := introTraceApprox_trivial_archimedean_complexDensity h ρ hA
  apply ((tendsto_const_nhds (x := Real.pi⁻¹)).pos_mul_atTop (inv_pos.2 Real.pi_pos) hlim).congr
  intro n
  let f := approx(h, ρ, n, (2 : ℂ))
  obtain ⟨hf, hc⟩ := introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n 2
  have hloc := (he f hf.measurable).2
  simp only [hm rfl, one_mul, InfinitePlace.not_isReal_iff_isComplex.mpr hv, ite_false,
    hv.mult_eq_two, Real.sqrt_sq (norm_nonneg _)] at hloc
  let p (u : ℂ) := (((‖u‖ ^ 2)⁻¹ : ℝ) : ℂ) * (f (‖u‖ ^ 2) * (‖u‖ : ℂ) / ((‖1-u‖^2 : ℝ) : ℂ))
  have hi : Integrable p := introTraceApprox_archimedean_sub_shiftTwo_complexFixed f hf hc (introTraceApprox_support h ρ hA n 2)
  change introTraceArchimedean (F := F) 1 f v = _ * ∫ u, p u ∂(2 • volume) at hloc
  change _ = (introTraceArchimedean (F := F) 1 f v).re
  rw [hloc, two_smul, integral_add_measure hi hi]
  have hh : (1/(2*(Real.pi : ℂ))) = ((1/(2*Real.pi) : ℝ) : ℂ) := by push_cast; rfl
  rw [hh, Complex.re_ofReal_mul, Complex.add_re]
  have hr := integral_re hi
  simp only [RCLike.re_to_complex] at hr
  rw [← hr]
  have hpoint (u : ℂ) : (p u).re = (‖u‖^2)⁻¹ * ((f (‖u‖^2)).re * ‖u‖ / ‖1-u‖^2) := by
    simp only [p, Complex.re_ofReal_mul, Complex.div_ofReal_re, Complex.re_mul_ofReal]
  simp_rw [hpoint]
  dsimp [f]
  ring

/-- A unitary multiplier equals one at the singularity. Its real part is at least
one half nearby. Away from that neighborhood the absolute density is bounded by
an integrable multiple of the inverse square of the normalized local norm. -/
private theorem introTraceApprox_archimedean_phase_lower_bound {E : Type*} [NormedField E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (d : ℕ) (hfin : Module.finrank ℝ E = d)
    (m : E → ℂ) (hm : Measurable m) (hunit : ∀ t, ‖m t‖ = 1) (hmc : ContinuousAt m 1) (hm1 : m 1 = 1)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) :
    let b (n : ℕ) (t : ℝ) := (introTraceApprox (h n) (ρ n) 2 t).re
    let G (n : ℕ) (u : E) := (‖u‖^d)⁻¹ * (b n (‖u‖^d) * (Real.sqrt (‖u‖^d)) / ‖1-u‖^d)
    (∀ n, Integrable (G n) μ) →
    Tendsto (fun n ↦ ∫ u, G n u ∂μ) atTop atTop →
    Tendsto (fun n ↦ ∫ u, (m u).re * G n u ∂μ) atTop atTop := by
  intro b G hi hlim
  have hd : 0 < d := hfin ▸ Module.finrank_pos
  have hre (t : E) : |(m t).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (hunit t).le
  have hpos : ∀ᶠ t in 𝓝 (1 : E), 1/2 < (m t).re := by
    apply (Complex.continuous_re.continuousAt.comp hmc).tendsto.eventually
    apply lt_mem_nhds
    norm_num [Function.comp_def, hm1]
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hpos
  let C := (1/2 : ℝ)^(-(2 : ℝ)) + 2^(-(2 : ℝ))
  let K := C / δ^d
  let S := (Metric.closedBall (0:E) 1)ᶜ
  let B (t : E) := S.indicator (fun t ↦ ((‖t‖^d)^2)⁻¹) t
  have hBi : Integrable B μ := by
    rw [show B = S.indicator (fun t : E ↦ ‖t‖ ^ (-(2*d : ℝ))) by
      dsimp only [B]
      apply congrArg (fun f : E → ℝ ↦ S.indicator f)
      funext x
      rw [Real.rpow_neg (norm_nonneg x), mul_comm (2 : ℝ), Real.rpow_mul (norm_nonneg x), Real.rpow_natCast]
      norm_num]
    apply (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet.compl).2
    apply (External.TauCeti.integrableOn_norm_rpow_compl_closedBall_iff zero_lt_one).2
    rw [hfin]
    exact_mod_cast (show -(2*(d:ℤ)) < -(d:ℤ) by omega)
  have hB0 (t : E) : 0 ≤ B t := indicator_nonneg (fun _ _ ↦ by positivity) t
  have hb (n : ℕ) (t : ℝ) : 0 ≤ b n t := by
    obtain ⟨g, hg, he⟩ := introTraceApprox_rat_spectral_tendsto_atBot_profile h ρ hA n
    simpa [b, he] using hg t
  have hG (n : ℕ) (t : E) : 0 ≤ G n t :=
    mul_nonneg (by positivity) (div_nonneg (mul_nonneg (hb _ _) (Real.sqrt_nonneg _)) (by positivity))
  have hK0 : 0 ≤ K := by dsimp [K, C]; positivity
  have hMi (n : ℕ) : Integrable (fun t ↦ (m t).re * G n t) μ :=
    (hi n).bdd_mul (Complex.continuous_re.measurable.comp hm).aestronglyMeasurable (.of_forall hre)
  have hcmp : ∀ᶠ n in atTop, ∀ t, G n t / 2 - (m t).re * G n t ≤ (2*K) * B t := by
    filter_upwards [introTraceApprox_mellin_tendsto_cutoff_bound hA 2] with n hn t
    by_cases ht : t ∈ Metric.ball 1 δ
    · have hmhalf := hδsub ht
      dsimp only [mem_setOf_eq] at hmhalf
      nlinarith [mul_le_mul_of_nonneg_right hmhalf.le (hG n t), mul_nonneg hK0 (hB0 t)]
    by_cases hN : 1 < ‖t‖ ^ d
    · have hnorm : 1 < ‖t‖ := by contrapose! hN; exact pow_le_one₀ (norm_nonneg _) hN
      have hB : B t = ((‖t‖^d)^2)⁻¹ := by
        apply indicator_of_mem
        simpa [S, mem_closedBall_zero_iff] using hnorm
      have hdist : δ ≤ ‖1 - t‖ := by
        simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using ht
      let N := ‖t‖^d
      have hNp : 0 < N := zero_lt_one.trans hN
      have hbound : b n N ≤ C * (N^2)⁻¹ := by
        calc b n N ≤ ‖introTraceApprox (h n) (ρ n) 2 N‖ := Complex.re_le_norm _
          _ ≤ _ := by simpa [C, Real.rpow_neg hNp.le] using hn 2 N (by norm_num) hN
      have hsqrt : Real.sqrt N ≤ N := (Real.sqrt_le_iff).2 ⟨hNp.le, by nlinarith [mul_le_mul_of_nonneg_left hN.le hNp.le]⟩
      have hden : 0 < ‖1-t‖^d := pow_pos (hδ.trans_le hdist) _
      have hGb : G n t ≤ K * B t := by
        rw [hB]
        change N⁻¹ * (b n N * Real.sqrt N / _) ≤ _
        calc N⁻¹ * (b n N * Real.sqrt N / ‖1-t‖^d) ≤
            N⁻¹ * (C*(N^2)⁻¹ * N / δ^d) := by
              gcongr <;> first | exact pow_le_pow_left₀ hδ.le hdist _ | exact hbound | exact hsqrt | positivity
          _ = K * (N^2)⁻¹ := by dsimp [K]; field_simp <;> ring
      have hmlo := (abs_le.mp (hre t)).1
      nlinarith [mul_le_mul_of_nonneg_right hmlo (hG n t), mul_nonneg hK0 (hB0 t)]
    · have hzero : introTraceApprox (h n) (ρ n) 2 (‖t‖^d) = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht ↦ hN (introTraceApprox_support h ρ hA n 2 ht))
      simpa [G, b, hzero] using mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hK0) (hB0 t)
  let D := ∫ t, (2*K) * B t ∂μ
  apply tendsto_atTop.mpr
  intro c
  filter_upwards [hcmp, tendsto_atTop.1 hlim (2*(c+D))] with n hn hbig
  have ha := integral_mono (((hi n).div_const 2).sub (hMi n)) (hBi.const_mul (2*K)) (hn ·)
  simp only [Pi.sub_apply] at ha
  rw [integral_sub ((hi n).div_const 2) (hMi n), integral_div] at ha
  change _ ≤ D at ha
  linarith

/-- In additive coordinates the real part of the local integral is the real phase
times a nonnegative radial density. Divergence transfers from the trivial character. -/
private theorem introTraceApprox_archimedean_phase_chart {E : Type*} [NormedField E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (χ : U𝔽) (v : InfinitePlace F) (e : v.Completion ≃+* E) (hi : Isometry e)
    (ν : Measure E) [ν.IsAddHaarMeasure] (hν : ν.restrict {0}ᶜ = ν)
    (hμ : letI := instMeasurableSpaceCompletion_riemannMasullo F v
      infiniteLocalAdditiveTamagawaMeasure F v = ν.map e.symm)
    (hd : Module.finrank ℝ E = v.mult)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) :
    let f (n : ℕ) := approx(h, ρ, n, (2 : ℂ))
    let G (n : ℕ) (u : E) := (‖u‖^v.mult)⁻¹ *
      ((f n (‖u‖^v.mult)).re * (Real.sqrt (‖u‖^v.mult)) / ‖1-u‖^v.mult)
    (∀ n, Integrable (G n) ν) →
    Tendsto (fun n ↦ (introTraceArchimedean (F := F) 1 (f n) v).re) atTop atTop →
    Tendsto (fun n ↦ (introTraceArchimedean χ (f n) v).re) atTop atTop := by
  classical
  intro f G hGi h0
  let c : ℝ := if v.IsReal then 1/2 else 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c]; split <;> positivity
  have hcoord (ψ : U𝔽) : ∃ m : E → ℂ, Measurable m ∧ (∀ t, ‖m t‖ = 1) ∧
      (ψ = 1 → ∀ t, m t = 1) ∧ ContinuousAt m 1 ∧ m 1 = 1 ∧
      ∀ n, (introTraceArchimedean ψ (f n) v).re = c * ∫ t, (m t).re * G n t ∂ν := by
    obtain ⟨m, hm, hnorm, hm0, hmc, hm1, he⟩ := introTraceApprox_archimedean_coordinate_continuousAt_one ψ v e hi ν hν hμ
    refine ⟨m, hm, hnorm, hm0, hmc, hm1, fun n ↦ ?_⟩
    obtain ⟨g, hg, hfg⟩ := introTraceApprox_rat_spectral_tendsto_atBot_profile h ρ hA n
    let W (t : E) := m t * (G n t : ℂ)
    have hWi : Integrable W ν := (hGi n).ofReal.bdd_mul hm.aestronglyMeasurable
      (.of_forall fun t ↦ (hnorm t).le)
    have hW (t : E) : m t * ((((‖t‖^v.mult)⁻¹ : ℝ) : ℂ) *
        (f n (‖t‖^v.mult) * (Real.sqrt (‖t‖^v.mult) : ℂ) / ((‖1-t‖^v.mult : ℝ) : ℂ))) = W t := by
      simp only [W, G, f, hfg, Complex.ofReal_re, Complex.ofReal_mul, Complex.ofReal_div]
    have hval := (he (f n) (introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n 2).1.measurable).2
    simp_rw [hW] at hval
    have hcoef : (if v.IsReal then 1/2 else 1/(2*(Real.pi : ℂ))) = (c : ℂ) := by
      dsimp [c]
      split <;> push_cast <;> rfl
    have hr := integral_re hWi
    simp only [RCLike.re_to_complex] at hr
    rw [hval, hcoef, Complex.re_ofReal_mul, ← hr]
    congr 1
    exact integral_congr_ae (.of_forall fun t ↦ Complex.re_mul_ofReal _ _)
  obtain ⟨m₀, _, _, h₀, _, _, he₀⟩ := hcoord 1
  have hin : Tendsto (fun n ↦ ∫ t, G n t ∂ν) atTop atTop := by
    apply ((tendsto_const_nhds (x := c⁻¹)).pos_mul_atTop (inv_pos.2 hc) h0).congr
    intro n
    rw [he₀ n]
    simp [h₀ rfl, ← mul_assoc, hc.ne']
  obtain ⟨m, hm, hn, _, hmc, hm1, he⟩ := hcoord χ
  have hh := introTraceApprox_archimedean_phase_lower_bound ν v.mult hd m hm hn hmc hm1 h ρ hA hGi hin
  exact ((tendsto_const_nhds (x := c)).pos_mul_atTop hc hh).congr fun n ↦ (he n).symm

/-- All real places give the same trivial-character integral as the rational real place. -/
private theorem introTraceApprox_archimedean_trivial_real_place (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (v : InfinitePlace F) (hv : v.IsReal) :
    Tendsto (fun n ↦ (introTraceArchimedean (F := F) 1 approx(h, ρ, n, (2 : ℂ)) v).re) atTop atTop := by
  classical
  have hq := introTraceApprox_rat_archimedean_tendsto_atTop h ρ hA
  simp only [Fintype.sum_subsingleton _ Rat.infinitePlace] at hq
  apply hq.congr
  intro n
  let f := approx(h, ρ, n, (2 : ℂ))
  have hf := (introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n 2).1.measurable
  obtain ⟨m, _, _, hm, he⟩ := introTraceApprox_archimedean_sub_shiftTwo_realCoordinate (F := F) 1 v hv
  have heq : introTraceArchimedean (F := F) 1 f v = introTraceArchimedean (F := ℚ) 1 f Rat.infinitePlace := by
    rw [introTraceArchimedean_rat_sub_shiftTwo_integral f hf, (he f hf).2]
    simp only [hm rfl, one_mul]
  exact congrArg Complex.re heq.symm

/-- Paper: §1.4.3, p. 29. At every infinite place of every number field and for every
unitary character, the real part of the unregularized term at parameter two tends to
positive infinity for every admissible family. -/
theorem introTraceApprox_archimedean_local_tendsto_atTop (χ : U𝔽) (v : InfinitePlace F)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) :
    Tendsto (fun n ↦ (introTraceArchimedean χ approx(h, ρ, n, (2 : ℂ)) v).re) atTop atTop := by
  classical
  by_cases hv : v.IsReal
  · apply introTraceApprox_archimedean_phase_chart χ v (InfinitePlace.Completion.ringEquivRealOfIsReal hv)
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).isometry volume
      (restrict_compl_singleton (μ := volume) 0) (dite_eq_left hv)
      (by simp [hv.mult_eq_one]) h ρ hA _ (introTraceApprox_archimedean_trivial_real_place h ρ hA v hv)
    intro n
    obtain ⟨hf, hc⟩ := introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n 2
    have hi := (introTraceApprox_rat_sub_shiftTwo_integrable _ hf hc (introTraceApprox_support h ρ hA n 2)).re
    apply hi.congr
    exact .of_forall fun t ↦ by simp only [RCLike.re_to_complex, hv.mult_eq_one, pow_one,
      Real.norm_eq_abs, Complex.re_ofReal_mul, Complex.div_ofReal_re, Complex.re_mul_ofReal]
  · have hw := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have hν : (2 • (volume : Measure ℂ)).restrict {(0 : ℂ)}ᶜ = 2 • volume := by
      simp [two_smul, Measure.restrict_add, restrict_compl_singleton]
    letI : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      have hhaar := Measure.IsAddHaarMeasure.smul (volume : Measure ℂ) (c := (2 : ENNReal)) (by norm_num) (by norm_num)
      convert hhaar using 1
      rw [two_smul, show (2 : ENNReal) = 1 + 1 by norm_num, add_smul, one_smul]
    apply introTraceApprox_archimedean_phase_chart χ v (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry (2 • volume)
      hν (dite_eq_right hv) (by simp [hw.mult_eq_two]) h ρ hA _ (introTraceApprox_trivial_archimedean_complexPlace h ρ hA v hw)
    intro n
    obtain ⟨hf, hc⟩ := introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n 2
    have hi := (introTraceApprox_archimedean_sub_shiftTwo_complexFixed _ hf hc (introTraceApprox_support h ρ hA n 2)).re
    rw [two_smul]
    apply Integrable.add_measure <;> apply hi.congr <;>
      exact .of_forall fun t ↦ by simp only [RCLike.re_to_complex, hw.mult_eq_two,
        Real.sqrt_sq (norm_nonneg _), Complex.re_ofReal_mul, Complex.div_ofReal_re, Complex.re_mul_ofReal]

/-- Paper: §1.4.3, p. 29. The real part of the full archimedean sum at parameter two
tends to positive infinity for every unitary character and admissible cutoff family. -/
theorem introTraceApprox_archimedean_tendsto_atTop (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) :
    Tendsto (fun n ↦ (∑ v : InfinitePlace F, introTraceArchimedean χ approx(h, ρ, n, (2 : ℂ)) v).re)
      atTop atTop := by
  classical
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
  apply tendsto_atTop.mpr
  intro c
  have hall : ∀ᶠ n in atTop, ∀ w : InfinitePlace F,
      max c 0 ≤ (introTraceArchimedean χ approx(h, ρ, n, (2 : ℂ)) w).re :=
    eventually_all.mpr fun w ↦ tendsto_atTop.mp (introTraceApprox_archimedean_local_tendsto_atTop χ w h ρ hA) _
  filter_upwards [hall] with n hn
  rw [Complex.re_sum]
  exact ((le_max_left _ _).trans (hn v)).trans
    (Finset.single_le_sum (fun w _ ↦ (le_max_right c 0).trans (hn w)) (Finset.mem_univ v))

private theorem introTrace_positive_order_re_lt_one (χ : U𝔽) {z : ℂ}
    (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z) : z.re < 1 := by
  rcases le_or_gt z.re 0 with h | h
  · exact h.trans_lt zero_lt_one
  · obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
    exact completedHeckeL_continuation_zeros χ _ hL heq h hz

private theorem introTrace_positive_divisor_in_critical_strip (χ : U𝔽) (z : ℂ)
    (hz : 0 < zeroOrder(χ, z)) :
    |z.re - 1 / 2| < (1 / 2 : ℝ) := by
  obtain ⟨hL, hLh⟩ := continuedCompletedHeckeL_spec χ
  have hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z := by
    rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)] at hz
    cases he : meromorphicOrderAt (continuedCompletedHeckeL χ) z with
    | top => simp
    | coe k =>
      rw [he, WithTop.untop₀_coe] at hz
      exact_mod_cast hz
  have hu := introTrace_positive_order_re_lt_one χ hp
  obtain ⟨hD, hDh⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hne, hfe⟩ :=
    completedHeckeL_continuation_functionalEquation χ _ _ hL hLh hD hDh
  have hcomp : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) z =
      meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - z) := by
    simpa [Function.comp_def] using
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
        (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z by fun_prop)
        (show deriv (fun s : ℂ ↦ 1 - s) z ≠ 0 by simp)
  rw [show (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) =
      ε * continuedCompletedHeckeL χ from funext hfe,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at hcomp
  have hl := introTrace_positive_order_re_lt_one χ⁻¹ (hcomp ▸ hp)
  rw [Complex.sub_re, Complex.one_re] at hl
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Restricting the zero sum to an open window preserves its value if the window contains each positive-order zero. -/
private theorem introTrace_spectral_sum_eq_unit_window_of_contains (χ : U𝔽) (f : ℝ → ℂ) (a : ℝ) (hall : ∀ s : ℂ, 0 < zeroOrder(χ, s) → |s.re - 1 / 2| < a) :
    introTraceSpectralSum χ f a = introTraceSpectralSum χ f 1 := by
  let e : windowZeros(χ, a) ≃ windowZeros(χ, (1 : ℝ)) := {
    toFun := fun t ↦ ⟨t.val, t.property.1, (introTrace_positive_divisor_in_critical_strip χ t.val t.property.1).trans (by norm_num)⟩
    invFun := fun t ↦ ⟨t.val, t.property.1, hall t.val t.property.1⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  unfold introTraceSpectralSum
  exact e.tsum_eq (fun r : windowZeros(χ, (1 : ℝ)) ↦
    (zeroOrder(χ, r.val) : ℂ) * introTraceMellin f (r.val - 1 / 2))

/-- Every positive-order completed zero belongs to every full window. -/
private theorem introTrace_full_window_spectral_sum_eq (χ : U𝔽) (f : ℝ → ℂ) (a : ℝ) (ha : 1 / 2 ≤ a) :
    introTraceSpectralSum χ f a = introTraceSpectralSum χ f 1 :=
  introTrace_spectral_sum_eq_unit_window_of_contains χ f a fun s hs ↦
    (introTrace_positive_divisor_in_critical_strip χ s hs).trans_le ha

/-- A continuous compact radial profile supported above one has an integrable local trace at
every infinite place. -/
private theorem introTrace_archimedean_integrable_of_compact_profile (χ : U𝔽) (v : InfinitePlace F) (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi 1) :
    Integrable archIntegrand(χ, f, v) (infiniteLocalMultiplicativeTamagawaMeasure F v) := by
  by_cases hv : v.IsReal
  · obtain ⟨m, hm, hnm, _, he⟩ := introTraceApprox_archimedean_sub_shiftTwo_realCoordinate χ v hv
    exact (he _ hf.measurable).1.mpr ((introTraceApprox_rat_sub_shiftTwo_integrable _ hf hc hs).bdd_mul
      hm.aestronglyMeasurable (.of_forall fun t ↦ (hnm t).le))
  · obtain ⟨m, hm, hnm, he⟩ := introTraceApprox_archimedean_sub_shiftTwo_complexCoordinate χ v (InfinitePlace.not_isReal_iff_isComplex.mp hv)
    apply (he _ hf.measurable).1.mpr
    have hp := (introTraceApprox_archimedean_sub_shiftTwo_complexFixed _ hf hc hs).bdd_mul hm.aestronglyMeasurable
      (.of_forall fun t ↦ (hnm t).le)
    simpa only [two_smul] using hp.add_measure hp

private theorem introTraceApprox_archimedean_integrable (χ : U𝔽) (v : InfinitePlace F)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    Integrable archIntegrand(χ, (introTraceApprox (h n) (ρ n) z), v) (infiniteLocalMultiplicativeTamagawaMeasure F v) := by
  have hf := introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n z
  exact introTrace_archimedean_integrable_of_compact_profile χ v _ hf.1 hf.2 (introTraceApprox_support h ρ hA n z)

open Classical in
/-- The normalized signed explicit formula specializes to every one-sided full-window cutoff. -/
private theorem introTraceApprox_full_window_fixed_digamma (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1)
    {a : ℝ} (ha : 1 / 2 ≤ a) (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    let f := introTraceApprox (h n) (ρ n) z
    (∑ w : InfinitePlace F, introTraceArchimedean χ f w) + introTraceSpectralSum χ f a =
      (if χ = 1 then introTraceMellin f (1/2) + introTraceMellin f (-1/2) else 0) -
      ∑' j : HeightOneSpectrum (𝓞 F) × ℕ, introTracePrimePower χ f j.1 j.2 := by
  intro f
  have hz (x : ℝ) (hx : x ≤ 1) : f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hu ↦ (not_lt_of_ge hx) (introTraceApprox_support h ρ hA n z hu))
  have hreg := introTraceApprox_logProfile h ρ hA n z
  have hm : Measurable f := (introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n z).1.measurable
  have H := introTrace_spectral_digamma_of_supported_above_one χ f hz hreg.1 hreg.2
  have hpole := introTrace_normalized_signed_divisor_split τ hτ χ hχ f H.summable
  let k (w : InfinitePlace F) := if hw : w.IsReal then
    let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    ∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel (1/2)
      ((1/2+p.1+p.2.val)/2) ((1/2-p.1+p.2.val)/2) (fun y ↦ f (Real.exp y)) t
    else
    let p := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    ∫ t in Ioi (0:ℝ), heckeArchimedeanDigammaKernel 1
      (1/2+p.1+(p.2.natAbs:ℂ)/2) (1/2-p.1+(p.2.natAbs:ℂ)/2) (fun y ↦ f (Real.exp y)) t
  have hk (w : InfinitePlace F) : introTraceArchimedean χ f w = -k w :=
    introTraceArchimedean_eq_neg_digamma_of_supported_above_one χ w f hm hz
      (introTraceApprox_archimedean_integrable χ w h ρ hA n z)
  have hsum := H.tsum_eq
  change _ = (∑ w, k w) - _ at hsum
  rw [hpole] at hsum
  simp only [hk, Finset.sum_neg_distrib]
  rw [introTrace_full_window_spectral_sum_eq χ f a ha]
  linear_combination hsum

open Classical in
/-- Paper: §§1.4.3–1.4.5, pp. 29–30. In a full zero window the raw combined
cutoffs converge locally uniformly on the entire shifted Euler half-plane, for
every admissible family and every norm-section-normalized character. -/
theorem introTrace_full_window_combined_euler_limit
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1)
    {a : ℝ} (ha : 1 / 2 ≤ a) (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) :
    TendstoLocallyUniformlyOn
      (fun n z ↦ archSum(χ, approx(h,ρ,n,z)) + introTraceSpectralSum χ approx(h,ρ,n,z) a)
      (fun z ↦ logDeriv finiteL(χ) (z+1/2) + if χ = 1 then 1/(z+1/2) + 1/(z-1/2) else 0)
      atTop right(1/2) :=
  introTrace_combined_euler_of_fixed_identity χ h ρ hA
    (introTraceApprox_full_window_fixed_digamma τ hτ χ hχ ha h ρ hA)

/-- On a full rational window the exterior sum vanishes by the critical strip, so
the combined real-place and spectral term has a finite limit for every family. -/
private theorem introTraceApprox_rat_combined_limit (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (a : ℝ) (ha : 1 / 2 ≤ a) :
    TendstoLocallyUniformlyOn (fun n z ↦
      introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) z) Rat.infinitePlace +
      introTraceSpectralSum (F := ℚ) 1 (introTraceApprox (h n) (ρ n) z) a)
      (fun z ↦ logDeriv (finiteHeckeL_exists_continuation (F := ℚ) 1).choose (z + 1 / 2) +
        (1 / (z + 1 / 2) + 1 / (z - 1 / 2))) atTop right(max a 1) := by
  classical
  let τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ :=
    ⟨(QuotientGroup.mk' _).comp (canonicalIdeleNormSection ℚ),
      continuous_quotient_mk'.comp (canonicalIdeleNormSection_continuous _)⟩
  have hcomb := introTrace_combined_limit_of_fixed_identity (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) h ρ hA
    (introTraceApprox_full_window_fixed_digamma τ (canonicalIdeleNormSection_rightInverse ℚ)
      1 (fun _ ↦ rfl) ha h ρ hA)
  simpa only [Fintype.sum_subsingleton _ Rat.infinitePlace, ite_true] using hcomb

/-- A limit for the rational real-place difference fixes the full spectral limit
on the trace overlap by the explicit formula. -/
private theorem introTraceApprox_rat_spectral_shiftTwo_of_arch (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ)
    (harch : TendstoLocallyUniformlyOn (fun n z ↦
      introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) z) Rat.infinitePlace -
      introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) (z+2)) Rat.infinitePlace)
      (fun z ↦ 1/(z+1/2)) atTop right(-(1/2 : ℝ))) (a : ℝ) (ha : 1/2 ≤ a) :
    let L := fun z : ℂ ↦ logDeriv (finiteHeckeL_exists_continuation (F := ℚ) 1).choose (z+1/2) +
      (1/(z+1/2) + 1/(z-1/2))
    TendstoLocallyUniformlyOn (fun n z ↦
      introTraceSpectralSum (F := ℚ) 1 (introTraceApprox (h n) (ρ n) z) a -
      introTraceSpectralSum (F := ℚ) 1 (introTraceApprox (h n) (ρ n) (z+2)) a)
      (fun z ↦ L z - L (z+2) - 1/(z+1/2)) atTop right(max a 1) := by
  classical
  have hcomb := introTraceApprox_rat_combined_limit h ρ hA a ha
  have hshift : MapsTo (fun z : ℂ ↦ z + 2) right(max a 1) right(max a 1) := by
    intro z hz
    change max a 1 < z.re at hz
    change max a 1 < (z + 2).re
    simpa using (show max a 1 < z.re + 2 by linarith)
  have hsub : right(max a 1) ⊆ right(-(1 / 2 : ℝ)) := fun z hz ↦
    (show -(1 / 2 : ℝ) < 1 by norm_num).trans ((le_max_right a 1).trans_lt hz)
  have hlim := (hcomb.sub (hcomb.comp (fun z : ℂ ↦ z + 2) hshift (by fun_prop))).sub (harch.mono hsub)
  refine (hlim.congr (fun n z _ ↦ ?_)).congr_right (fun z _ ↦ ?_)
  · simp only [Pi.sub_apply, Function.comp_apply]
    ring
  · rfl

/-- Paper: §§1.4.3–1.4.5, pp. 29–30. For the trivial rational character and
any full window, the same matched cutoffs give a locally uniform limit of the
differences of the complete smoothed zero sums on the trace overlap. Here
`L` is the polar-corrected shifted logarithmic derivative.
Deviation: The fixed-cutoff identity uses the full explicit formula. For
half-widths at least one half the exterior-zero sum vanishes by the critical strip. -/
theorem introTraceApprox_rat_spectral_sub_shiftTwo_tendsto (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ IsIntroTraceApproximation h (ρ ∘ k) ∧
      TendstoLocallyUniformlyOn (fun n z ↦
        introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ (k n)) z) Rat.infinitePlace -
        introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ (k n)) (z + 2)) Rat.infinitePlace)
        (fun z ↦ 1 / (z + 1 / 2)) atTop right(-(1 / 2 : ℝ)) ∧
      ∀ a : ℝ, 1 / 2 ≤ a →
        let L := fun z : ℂ ↦ logDeriv (finiteHeckeL_exists_continuation (F := ℚ) 1).choose (z + 1 / 2) +
          (1 / (z + 1 / 2) + 1 / (z - 1 / 2))
        TendstoLocallyUniformlyOn (fun n z ↦
          introTraceSpectralSum (F := ℚ) 1 (introTraceApprox (h n) (ρ (k n)) z) a -
          introTraceSpectralSum (F := ℚ) 1 (introTraceApprox (h n) (ρ (k n)) (z + 2)) a)
          (fun z ↦ L z - L (z + 2) - 1 / (z + 1 / 2)) atTop right(max a 1) := by
  classical
  obtain ⟨k, hk, hAk, harch⟩ := introTraceApprox_rat_sub_shiftTwo_tendsto h ρ hA
  exact ⟨k, hk, hAk, harch, introTraceApprox_rat_spectral_shiftTwo_of_arch h (ρ ∘ k) hAk harch⟩

/-- Paper: §§1.4.3–1.4.5, pp. 29–30. For one admissible family the rational
real-place difference at two and four tends to positive infinity in real part, and the
difference of the full smoothed spectral sums tends to negative infinity in real part
for every half-width `1/2 ≤ a < 2`.
Deviation: Summing over zeros before removing these cutoffs makes the spectral sum
and real-place term diverge with opposite signs. Removing the cutoffs for each finite set first
gives the convergent resolvent series by `introTrace_spectral_referenceSub`. -/
theorem introTraceApprox_exists_rat_spectral_sub_shiftTwo_atBot :
    ∃ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ ∧
      Tendsto (fun n ↦ (introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) 2) Rat.infinitePlace -
        introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) 4) Rat.infinitePlace).re) atTop atTop ∧
      ∀ a : ℝ, 1 / 2 ≤ a → a < 2 →
        Tendsto (fun n ↦ (introTraceSpectralSum (F := ℚ) 1 (introTraceApprox (h n) (ρ n) 2) a -
          introTraceSpectralSum (F := ℚ) 1 (introTraceApprox (h n) (ρ n) 4) a).re) atTop atBot := by
  classical
  obtain ⟨h, ρ, hA, hdiv⟩ := introTraceApprox_exists_rat_sub_shiftTwo_unmatched
  refine ⟨h, ρ, hA, hdiv, ?_⟩
  intro a ha ha₂
  have hcomb := introTraceApprox_rat_combined_limit h ρ hA a ha
  have hmax : max a 1 < 2 := max_lt ha₂ (by norm_num)
  have h₂ := hcomb.tendsto_at (a := (2 : ℂ)) (by simpa using hmax)
  have h₄ := hcomb.tendsto_at (a := (4 : ℂ)) (by simpa using hmax.trans (by norm_num : (2 : ℝ) < 4))
  let A (n : ℕ) (z : ℂ) := introTraceArchimedean (F := ℚ) 1 (introTraceApprox (h n) (ρ n) z) Rat.infinitePlace
  let S (n : ℕ) (z : ℂ) := introTraceSpectralSum (F := ℚ) 1 (introTraceApprox (h n) (ρ n) z) a
  let L (z : ℂ) := logDeriv (finiteHeckeL_exists_continuation (F := ℚ) 1).choose (z + 1 / 2) +
    (1 / (z + 1 / 2) + 1 / (z - 1 / 2))
  -- The finite limit of the combined differences gives an eventual upper bound.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, Tendsto (fun n ↦ (A n 2 + S n 2 - (A n 4 + S n 4)).re) atTop (𝓝 C) := by
    refine ⟨(L 2 - L 4).re, ?_⟩
    simpa only [Function.comp_def, A, S, L, Pi.sub_apply] using
      Complex.continuous_re.continuousAt.tendsto.comp (h₂.sub h₄)
  change Tendsto (fun n ↦ (A n 2 - A n 4).re) atTop atTop at hdiv
  apply tendsto_atBot.2
  intro M
  filter_upwards [hC.eventually_le_const (show C < C + 1 by linarith),
    hdiv.eventually_ge_atTop (C + 1 - M)] with n hn ha'
  change (S n 2 - S n 4).re ≤ M
  simp only [Complex.sub_re, Complex.add_re] at hn ha' ⊢
  linarith

/-- On a matched translate x, factor a power of x to shift both parameters one
unit right. The endpoint cancellation bound then holds even for negative real parts. -/
private theorem introTraceApprox_archimedean_reference_power_bound {a Z : ℝ} (ha : -(1 / 2 : ℝ) < a) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z w : ℂ) (t u : ℝ), a ≤ z.re → a ≤ w.re → ‖z‖ ≤ Z → ‖w‖ ≤ Z →
    1 < t → |u| ≤ 1 → |u| ≤ t - 1 →
    ‖introTracePower z (t - u) - introTracePower w (t - u)‖ ≤
      (C * t ^ (-a)) * (8 * (t - 1) / t) := by
  obtain ⟨D, hD, hb⟩ := introTraceApprox_translated_reference_lower (m := a + 1) (Z := Z + 1) (by linarith) (by linarith)
  refine ⟨D, hD, fun z w t u hz hw hzn hwn ht hu hsep ↦ ?_⟩
  let x := t - u
  have hx : 1 ≤ x := by dsimp [x]; linarith [(abs_le.mp hsep).2]
  have ht0 : 0 < t := zero_lt_one.trans ht
  rcases eq_or_lt_of_le hx with he | hx
  · change ‖introTracePower z x - introTracePower w x‖ ≤ _
    rw [← he]
    simp only [introTracePower, lt_irrefl, ite_false, ite_true, sub_self, norm_zero]
    positivity
  have hx0 := zero_lt_one.trans hx
  have hlt : x ≤ 2 * t := by dsimp [x]; linarith [(abs_le.mp hu).1]
  have hfac (q : ℂ) : introTracePower q x = (x : ℂ)*introTracePower (q + 1) x := by
    simp only [introTracePower, hx, ite_true]
    rw [show -(q + 1) = -q - 1 by ring, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx0.ne'), Complex.cpow_one]
    field_simp [Complex.ofReal_ne_zero.mpr hx0.ne']
  have hh := hb (z + 1) (w + 1) t u (by simpa using hz) (by simpa using hw)
    ((norm_add_le _ _).trans (by simp; linarith)) ((norm_add_le _ _).trans (by simp; linarith)) ht hu hsep hx
  change ‖introTracePower z x - introTracePower w x‖ ≤ _
  rw [hfac z, hfac w, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  calc x * _ ≤ (2 * t) * ((D * t ^ (-(a + 1))) * ((t - 1)/t)) := mul_le_mul hlt hh (norm_nonneg _) (by positivity)
    _ = (D * t^(-a)) * (2 * (t - 1)/t) := by
      rw [show -(a + 1) = -a-1 by ring, Real.rpow_sub ht0, Real.rpow_one]
      field_simp <;> ring
    _ ≤ _ := by gcongr <;> norm_num

/-- A nonnegative, mass-one mollifier preserves the cancellation estimate under
its integral, uniformly for parameters in a bounded part of the half-plane. -/
private theorem introTraceApprox_archimedean_reference_radial_bound (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ)
    (hmatch : ∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1)
    {a Z : ℝ} (ha : -(1 / 2 : ℝ) < a) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (z w : ℂ) (t : ℝ), a ≤ z.re → a ≤ w.re → ‖z‖ ≤ Z → ‖w‖ ≤ Z → 1 < t →
      ‖introTraceApprox (h n) (ρ n) z t - introTraceApprox (h n) (ρ n) w t‖ ≤
        (C * t ^ (-a)) * (8 * (t - 1) / t) := by
  obtain ⟨C, hC, hb⟩ := introTraceApprox_archimedean_reference_power_bound ha hZ
  refine ⟨C, hC, fun n z w t hz hw hzn hwn ht ↦ ?_⟩
  let B := (C * t ^ (-a)) * (8 * (t - 1) / t)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  by_cases hzero : h n t = 0
  · simpa [introTraceApprox, hzero, B] using hB
  obtain ⟨ε, _, hρ⟩ := hA.2.2.2
  obtain ⟨_, hsm, hp, hs, hm⟩ := hρ n
  have hc : HasCompactSupport (ρ n) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  have hcast := hc.comp_left (g := Complex.ofReal) (by simp)
  have hi (w : ℂ) : Integrable (fun u : ℝ ↦ (ρ n u : ℂ) * introTracePower w (t - u)) :=
    hcast.convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ)
      (Complex.continuous_ofReal.comp hsm.continuous) (introTracePower_locallyIntegrable w) t
  unfold introTraceApprox
  rw [← mul_sub, ← integral_sub (hi z) (hi w), norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ((hA.1 n).2.2.2 t).1]
  refine (mul_le_of_le_one_left (norm_nonneg _) ((hA.1 n).2.2.2 t).2).trans ?_
  calc
    _ ≤ ∫ u, ρ n u * B := norm_integral_le_of_norm_le
      ((hsm.continuous.integrable_of_hasCompactSupport hc).mul_const B) (by
        apply Eventually.of_forall
        intro u
        by_cases hu : ρ n u = 0
        · simp [hu]
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp _)]
        obtain ⟨hu1, hsep⟩ := hmatch n t u hzero hu
        exact mul_le_mul_of_nonneg_left (hb z w t u hz hw hzn hwn ht hu1 hsep) (hp u))
    _ = B := by rw [integral_mul_const, hm, one_mul]

/-- A locally integrable majorant for an entire family bounds its derivatives by the
Cauchy estimate on a smaller disk. Difference quotients give derivative measurability. -/
private theorem introTraceApprox_archimedean_reference_integral_analytic {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℂ → Ω → ℂ) (hm : ∀ z, Measurable (Y z)) (hd : ∀ t, Differentiable ℂ (Y · t))
    {U : Set ℂ} (hU : IsOpen U)
    (hdom : ∀ z ∈ U, ∃ B : Ω → ℝ, Integrable B μ ∧ ∀ᶠ w in 𝓝 z, ∀ t, ‖Y w t‖ ≤ B t) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ t, Y z t ∂μ) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro z hz
  obtain ⟨B, hB, hnear⟩ := hdom z hz
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := ε / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have hi := hB.mono' (hm z).aestronglyMeasurable (.of_forall (hball (Metric.mem_ball_self hε)))
  let D (w : ℂ) (t : Ω) := deriv (Y · t) w
  have hD (w : ℂ) : Measurable (D w) := by
    obtain ⟨seq, hseq⟩ := exists_seq_tendsto (𝓝[≠] w)
    let Q (n : ℕ) (t : Ω) := slope (Y · t) w (seq n)
    have hQ (n : ℕ) : Measurable (Q n) := by
      change Measurable (fun t ↦ (seq n - w)⁻¹ * (Y (seq n) t - Y w t))
      fun_prop (disch := exact hm _)
    apply measurable_of_tendsto_metrizable hQ (tendsto_pi_nhds.2 (fun t ↦ ?_))
    exact (hd t w).hasDerivAt.tendsto_slope.comp hseq
  have hb (t : Ω) (w : ℂ) (hw : w ∈ Metric.ball z r) : ‖D w t‖ ≤ B t / r := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr (hd t).diffContOnCl
    intro q hq
    apply hball
    have he : dist q w = r := hq
    have hl : dist w z < r := hw
    have hδ := dist_triangle q w z
    dsimp [r] at he hl
    change dist q z < ε
    linarith
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z hr)
    (.of_forall fun w ↦ (hm w).aestronglyMeasurable) hi (hD z).aestronglyMeasurable
    (.of_forall hb) (hB.div_const r) (.of_forall fun t w _ ↦ (hd t w).hasDerivAt)).2.differentiableAt.differentiableWithinAt

/-- Local domination yields both integrability of the limiting difference and joint
convergence as the parameter varies and the cutoffs are removed. -/
private theorem introTraceApprox_archimedean_reference_weighted {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (r : Ω → ℝ) (hr : Measurable r) (K : Ω → ℂ) (hK : Measurable K)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) (w₀ : ℂ) (hw₀ : -(1 / 2 : ℝ) < w₀.re)
    (hdom : ∀ a : ℝ, -(1 / 2 : ℝ) < a → ∀ Z : ℝ, 0 ≤ Z → ∃ B : Ω → ℝ, Integrable B μ ∧
      ∀ n (w : ℂ), a ≤ w.re → a ≤ w₀.re → ‖w‖ ≤ Z → ‖w₀‖ ≤ Z → ∀ t, ‖K t * (introTraceApprox (h n) (ρ n) w (r t) -
        introTraceApprox (h n) (ρ n) w₀ (r t))‖ ≤ B t) :
    let X (n : ℕ) (w : ℂ) (t : Ω) := K t * (introTraceApprox (h n) (ρ n) w (r t) -
        introTraceApprox (h n) (ρ n) w₀ (r t))
    let Y (w : ℂ) (t : Ω) := K t * (introTracePower w (r t) - introTracePower w₀ (r t))
    AnalyticOnNhd ℂ (fun w ↦ ∫ t, Y w t ∂μ) right(-(1 / 2 : ℝ)) ∧
    (∀ w ∈ right(-(1 / 2 : ℝ)), Integrable (Y w) μ) ∧
    TendstoLocallyUniformlyOn (fun n w ↦ ∫ t, X n w t ∂μ) (fun w ↦ ∫ t, Y w t ∂μ)
      atTop right(-(1 / 2 : ℝ)) := by
  intro X Y
  let f (n : ℕ) (w : ℂ) := introTraceApprox (h n) (ρ n) w
  have hm (n : ℕ) (w : ℂ) := (introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n w).1
  have hXm (n : ℕ) (w : ℂ) : Measurable (X n w) :=
    hK.mul (((hm _ _).measurable.comp hr).sub ((hm _ _).measurable.comp hr))
  have hYm (w : ℂ) : Measurable (Y w) := hK.mul (((introTraceApprox_mellin_tendsto_power_measurable _).comp hr).sub
    ((introTraceApprox_mellin_tendsto_power_measurable _).comp hr))
  have hzero (n : ℕ) (w : ℂ) (t : ℝ) (ht : t ≤ 1) : f n w t = 0 :=
    image_eq_zero_of_notMem_tsupport fun hm ↦ ht.not_gt (introTraceApprox_support h ρ hA n w hm)
  have hXlim (z : ℂ) (t : Ω) :
      Tendsto (fun i : ℕ × ℂ ↦ X i.1 i.2 t) (atTop ×ˢ 𝓝 z) (𝓝 (Y z t)) := by
    by_cases ht : 1 < r t
    · have hplus : Tendsto (fun i : ℕ × ℂ ↦ (i.1, w₀)) (atTop ×ˢ 𝓝 z) (atTop ×ˢ 𝓝 w₀) :=
        tendsto_fst.prodMk tendsto_const_nhds
      exact tendsto_const_nhds.mul ((introTraceApprox_mellin_tendsto_radial hA z ht).sub
        ((introTraceApprox_mellin_tendsto_radial hA w₀ ht).comp hplus))
    · change Tendsto (fun i : ℕ × ℂ ↦ K t * (f i.1 i.2 (r t) - f i.1 w₀ (r t))) _ _
      simp [Y, hzero _ _ _ (le_of_not_gt ht), introTracePower, ht]
  have hYcont (t : Ω) : Continuous (fun z ↦ Y z t) := by
    have h := (introTracePower_differentiable (r t)).continuous
    exact continuous_const.mul (h.sub continuous_const)
  have hYb {B : Ω → ℝ} {w : ℂ} (hb : ∀ n t, ‖X n w t‖ ≤ B t) (t : Ω) : ‖Y w t‖ ≤ B t := by
    have hseq : Tendsto (fun n : ℕ ↦ (n, w)) atTop (atTop ×ˢ 𝓝 w) := tendsto_id.prodMk tendsto_const_nhds
    exact le_of_tendsto ((hXlim w t).comp hseq).norm (.of_forall fun n ↦ hb n t)
  have hloc (z : ℂ) (hz : -(1 / 2 : ℝ) < z.re) :
      ∃ B : Ω → ℝ, Integrable B μ ∧ ∀ᶠ w in 𝓝 z, ∀ n t, ‖X n w t‖ ≤ B t := by
    obtain ⟨a, ha, haz⟩ := exists_between (lt_min hz hw₀)
    let Z := max ‖z‖ ‖w₀‖ + 1
    have hZ : 0 ≤ Z := by dsimp [Z]; positivity
    obtain ⟨B, hB, hD⟩ := hdom a ha Z hZ
    refine ⟨B, hB, ?_⟩
    have hZn : ‖z‖ < Z := by dsimp [Z]; linarith [le_max_left ‖z‖ ‖w₀‖]
    have hZ₀ : ‖w₀‖ ≤ Z := by dsimp [Z]; linarith [le_max_right ‖z‖ ‖w₀‖]
    filter_upwards [Complex.continuous_re.continuousAt.tendsto.eventually (lt_mem_nhds (lt_min_iff.mp haz).1),
      continuous_norm.continuousAt.tendsto.eventually (gt_mem_nhds hZn)] with w hw hwn n t
    exact hD n w hw.le (lt_min_iff.mp haz).2.le hwn.le hZ₀ t
  refine ⟨?_, ?_, ?_⟩
  · refine introTraceApprox_archimedean_reference_integral_analytic μ Y hYm ?_ (isOpen_Ioi.preimage Complex.continuous_re) ?_
    · exact fun t ↦ ((introTracePower_differentiable (r t)).sub_const (introTracePower w₀ (r t))).const_mul _
    · intro z hz
      obtain ⟨B, hi, he⟩ := hloc z hz
      exact ⟨B, hi, he.mono fun w hw ↦ hYb hw⟩
  · intro z hz
    obtain ⟨B, hB, hD⟩ := hloc z hz
    exact hB.mono' (hYm z).aestronglyMeasurable (.of_forall (hYb hD.self_of_nhds))
  apply (isOpen_Ioi.preimage Complex.continuous_re).tendstoLocallyUniformlyOn_iff_forall_tendsto.2
  intro z hz
  obtain ⟨B, hB, hD⟩ := hloc z hz
  let l := (atTop : Filter ℕ) ×ˢ 𝓝 z
  have hnear : ∀ᶠ i in l, ∀ n t, ‖X n i.2 t‖ ≤ B t := tendsto_snd.eventually hD
  have h₁ : Tendsto (fun i : ℕ × ℂ ↦ ∫ t, X i.1 i.2 t ∂μ) l (𝓝 (∫ t, Y z t ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence B (.of_forall fun _ ↦ (hXm _ _).aestronglyMeasurable)
      (hnear.mono fun i hi ↦ .of_forall (hi _)) hB (.of_forall (hXlim z))
  have h₂ : Tendsto (fun i : ℕ × ℂ ↦ ∫ t, Y i.2 t ∂μ) l (𝓝 (∫ t, Y z t ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence B (.of_forall fun _ ↦ (hYm _).aestronglyMeasurable)
      (hnear.mono fun i hi ↦ .of_forall (hYb hi)) hB
      (.of_forall fun t ↦ (hYcont t).continuousAt.tendsto.comp tendsto_snd)
  exact (h₂.prodMk_nhds h₁).mono_right (nhds_le_uniformity _)

/-- Transfer the weighted difference back to the two separately integrated local
terms at each fixed cutoff. The limiting local integral is absolutely integrable. -/
private theorem introTraceApprox_archimedean_reference_chart {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (r : Ω → ℝ) (hr : Measurable r) (K : Ω → ℂ) (hK : Measurable K) (c : ℂ)
    (χ : U𝔽) (v : InfinitePlace F) (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) (w₀ : ℂ) (hw₀ : -(1 / 2 : ℝ) < w₀.re)
    (hcoord : ∀ f : ℝ → ℂ, Measurable f →
      (Integrable archIntegrand(χ, f, v) (infiniteLocalMultiplicativeTamagawaMeasure F v) ↔
        Integrable (fun t ↦ K t * f (r t)) μ) ∧
      introTraceArchimedean χ f v = c * ∫ t, K t * f (r t) ∂μ)
    (hfixed : ∀ n z, Integrable (fun t ↦ K t * introTraceApprox (h n) (ρ n) z (r t)) μ)
    (hdom : ∀ a : ℝ, -(1 / 2 : ℝ) < a → ∀ Z : ℝ, 0 ≤ Z → ∃ B : Ω → ℝ, Integrable B μ ∧
      ∀ n (w : ℂ), a ≤ w.re → a ≤ w₀.re → ‖w‖ ≤ Z → ‖w₀‖ ≤ Z → ∀ t, ‖K t * (introTraceApprox (h n) (ρ n) w (r t) -
        introTraceApprox (h n) (ρ n) w₀ (r t))‖ ≤ B t) :
    AnalyticOnNhd ℂ (fun z ↦ introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower w₀ t) v) right(-(1 / 2 : ℝ)) ∧
    (∀ z ∈ right(-(1 / 2 : ℝ)), Integrable
      archIntegrand(χ, (fun t ↦ introTracePower z t - introTracePower w₀ t), v)
      (infiniteLocalMultiplicativeTamagawaMeasure F v)) ∧
    TendstoLocallyUniformlyOn (fun n z ↦
      introTraceArchimedean χ (introTraceApprox (h n) (ρ n) z) v -
      introTraceArchimedean χ (introTraceApprox (h n) (ρ n) w₀) v)
      (fun z ↦ introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower w₀ t) v)
      atTop right(-(1 / 2 : ℝ)) := by
  obtain ⟨han, hi, hlim⟩ := introTraceApprox_archimedean_reference_weighted μ r hr K hK h ρ hA w₀ hw₀ hdom
  have hm (z : ℂ) := (introTraceApprox_mellin_tendsto_power_measurable z).sub
    (introTraceApprox_mellin_tendsto_power_measurable w₀)
  have hfm (n : ℕ) (z : ℂ) := (introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n z).1.measurable
  have he : (fun z ↦ introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower w₀ t) v) =
      fun z ↦ c * ∫ t, K t * (introTracePower z (r t) - introTracePower w₀ (r t)) ∂μ :=
    funext fun z ↦ (hcoord _ (hm z)).2
  refine ⟨he ▸ analyticOnNhd_const.mul han, fun z hz ↦ (hcoord _ (hm z)).1.mpr (hi z hz), ?_⟩
  refine ((uniformContinuous_const_smul (M := ℂ) c).comp_tendstoLocallyUniformlyOn hlim).congr
      (fun n z _ ↦ ?_) |>.congr_right (fun z _ ↦ (hcoord _ (hm z)).2.symm)
  rw [(hcoord _ (hfm n z)).2, (hcoord _ (hfm n w₀)).2, ← mul_sub,
      ← integral_sub (hfixed n z) (hfixed n w₀)]
  change c * (∫ t, K t * (_ - _) ∂μ) = c * ∫ t, K t * _ - K t * _ ∂μ
  congr 1
  apply integral_congr_ae
  exact .of_forall fun _ ↦ mul_sub _ _ _

/-- On the real chart the vanishing factor cancels the denominator. On the complex
chart it leaves an integrable inverse-distance singularity at one. -/
private theorem introTraceApprox_archimedean_reference_matched (χ : U𝔽) (v : InfinitePlace F)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) (w₀ : ℂ) (hw₀ : -(1 / 2 : ℝ) < w₀.re)
    (hmatch : ∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1) :
    AnalyticOnNhd ℂ (fun z ↦ introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower w₀ t) v) right(-(1 / 2 : ℝ)) ∧
    (∀ z ∈ right(-(1 / 2 : ℝ)), Integrable
      archIntegrand(χ, (fun t ↦ introTracePower z t - introTracePower w₀ t), v)
      (infiniteLocalMultiplicativeTamagawaMeasure F v)) ∧
    TendstoLocallyUniformlyOn (fun n z ↦
      introTraceArchimedean χ (introTraceApprox (h n) (ρ n) z) v -
      introTraceArchimedean χ (introTraceApprox (h n) (ρ n) w₀) v)
      (fun z ↦ introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower w₀ t) v)
      atTop right(-(1 / 2 : ℝ)) := by
  let f (n : ℕ) (z : ℂ) := introTraceApprox (h n) (ρ n) z
  have hf (n : ℕ) (z : ℂ) := introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n z
  have hzero (n : ℕ) (z : ℂ) (t : ℝ) (ht : t ≤ 1) : f n z t = 0 :=
    image_eq_zero_of_notMem_tsupport fun hm ↦ ht.not_gt (introTraceApprox_support h ρ hA n z hm)
  by_cases hv : v.IsReal
  · obtain ⟨m, hm, hnm, _, he⟩ := introTraceApprox_archimedean_sub_shiftTwo_realCoordinate χ v hv
    let K (t : ℝ) := m t * (((|t|⁻¹ : ℝ) : ℂ) * ((Real.sqrt |t| : ℂ) / ((|1 - t| : ℝ) : ℂ)))
    have hK : Measurable K := by dsimp [K]; fun_prop
    have hW (t : ℝ) (q : ℂ) : m t * (((|t|⁻¹ : ℝ) : ℂ) * (q * (Real.sqrt |t| : ℂ) /
        ((|1 - t| : ℝ) : ℂ))) = K t * q := by dsimp [K]; ring
    simp_rw [hW] at he
    apply introTraceApprox_archimedean_reference_chart volume (fun t : ℝ ↦ |t|) continuous_abs.measurable K hK (1 / 2) χ v h ρ hA w₀ hw₀ he
    · intro n z
      have hb := introTraceApprox_rat_sub_shiftTwo_integrable _ (hf n z).1 (hf n z).2 (introTraceApprox_support h ρ hA n z)
      apply hb.mono (hK.mul ((hf n z).1.measurable.comp continuous_abs.measurable)).aestronglyMeasurable
      exact .of_forall fun t ↦ by simp only [Pi.mul_apply, Function.comp_apply]; rw [← hW, norm_mul, hnm, one_mul]
    · intro a ha Z hZ
      obtain ⟨C, hC, hpow⟩ := introTraceApprox_archimedean_reference_radial_bound h ρ hA hmatch ha hZ
      let d := -a - 3 / 2
      let p := (Ioi (1 : ℝ)).indicator fun t ↦ t ^ d
      have hp : Integrable p := (integrable_indicator_iff measurableSet_Ioi).2
        (integrableOn_Ioi_rpow_of_lt (show d < -1 by dsimp [d]; linarith) zero_lt_one)
      refine ⟨fun t ↦ (8 * C) * (p t + p (-t)), (hp.add hp.comp_neg).const_mul _, ?_⟩
      intro n w hw hw₀' hwn hw₀n t
      rw [← hW, norm_mul, hnm, one_mul]
      by_cases ht : 1 < |t|
      · have hb := introTraceApprox_rat_sub_shiftTwo_density_bound t a C hC ht _ <|
          hpow n w w₀ _ hw hw₀' hwn hw₀n ht
        have hp' : p t + p (-t) = |t| ^ d := by
          rcases le_or_gt 0 t with hts | hts
          · rw [abs_of_nonneg hts] at ht ⊢
            simp [p, ht, show ¬1 < -t by linarith]
          · rw [abs_of_neg hts] at ht ⊢
            simp [p, ht, show ¬1 < t by linarith]
        simpa only [hp'] using hb
      · have hp' (x : ℝ) : 0 ≤ p x := indicator_nonneg (fun y hy ↦
          Real.rpow_nonneg (zero_le_one.trans (mem_Ioi.mp hy).le) d) x
        change ‖_ * (((f n w |t| - f n w₀ |t|) * _) / _)‖ ≤ _
        simpa [hzero _ _ _ (le_of_not_gt ht)] using mul_nonneg (show 0 ≤ 8 * C by positivity)
          (add_nonneg (hp' t) (hp' (-t)))
  · obtain ⟨m, hm, hnm, he⟩ := introTraceApprox_archimedean_sub_shiftTwo_complexCoordinate χ v (InfinitePlace.not_isReal_iff_isComplex.mp hv)
    let K (t : ℂ) := m t * ((((‖t‖^2)⁻¹ : ℝ) : ℂ) * ((‖t‖ : ℂ) / ((‖1 - t‖^2 : ℝ) : ℂ)))
    have hK : Measurable K := by dsimp [K]; fun_prop
    have hW (t q : ℂ) : m t * ((((‖t‖^2)⁻¹ : ℝ) : ℂ) * (q * (‖t‖ : ℂ) /
        ((‖1 - t‖^2 : ℝ) : ℂ))) = K t * q := by dsimp [K]; ring
    simp_rw [hW] at he
    apply introTraceApprox_archimedean_reference_chart (2 • volume) (fun t : ℂ ↦ ‖t‖^2) (by fun_prop) K hK
      (1 / (2 * (Real.pi:ℂ))) χ v h ρ hA w₀ hw₀ he
    · intro n z
      have hb := introTraceApprox_archimedean_sub_shiftTwo_complexFixed _ (hf n z).1 (hf n z).2 (introTraceApprox_support h ρ hA n z)
      rw [two_smul]
      apply Integrable.add_measure <;> apply hb.mono (hK.mul ((hf n z).1.measurable.comp (by fun_prop))).aestronglyMeasurable <;>
        exact .of_forall fun t ↦ by simp only [Pi.mul_apply, Function.comp_apply]; rw [← hW, norm_mul, hnm, one_mul]
    · intro a ha Z hZ
      obtain ⟨C, hC, hpow⟩ := introTraceApprox_archimedean_reference_radial_bound h ρ hA hmatch ha hZ
      let near (t : ℂ) := (Metric.ball (0 : ℂ) 4).indicator (fun z ↦ ‖z‖⁻¹) (t - 1)
      let far (t : ℂ) := (Ioi (2 : ℝ)).indicator (fun r ↦ r ^ (-2 * a - 3)) ‖t‖
      let B (t : ℂ) := (24 * C * (1 + 4 ^ (-a))) * near t + (32 * C) * far t
      have hB : Integrable B := (introTraceApprox_archimedean_sub_shiftTwo_complexNear.const_mul _).add
        ((introTraceApprox_archimedean_sub_shiftTwo_complexTail (d := -2 * a - 3) (by linarith)).const_mul _)
      refine ⟨B, by simpa only [two_smul] using hB.add_measure hB, ?_⟩
      intro n w hw hw₀' hwn hw₀n t
      rw [← hW, norm_mul, hnm, one_mul]
      by_cases ht : 1 < ‖t‖^2
      · exact introTraceApprox_archimedean_sub_shiftTwo_complexBound hC t (by contrapose! ht; exact pow_le_one₀ (norm_nonneg _) ht) _
          (hpow n w w₀ _ hw hw₀' hwn hw₀n ht)
      · have hnear : 0 ≤ near t := indicator_nonneg (fun _ _ ↦ by positivity) _
        have hfar : 0 ≤ far t := indicator_nonneg (fun r hr ↦ Real.rpow_nonneg (by linarith [mem_Ioi.mp hr]) _) _
        change ‖_ * (((f n w _ - f n w₀ _) * _) / _)‖ ≤ _
        simpa [hzero _ _ _ (le_of_not_gt ht), B] using
          add_nonneg (mul_nonneg (by positivity) hnear) (mul_nonneg (by positivity) hfar)

/-- The same matched family gives convergence of the finite sum over all infinite places. -/
private theorem introTraceApprox_archimedean_reference_matched_sum (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (w₀ : ℂ) (hw₀ : -(1 / 2 : ℝ) < w₀.re)
    (hmatch : ∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1) :
      TendstoLocallyUniformlyOn (fun n z ↦
        (∑ v : InfinitePlace F, introTraceArchimedean χ (introTraceApprox (h n) (ρ n) z) v) -
         ∑ v : InfinitePlace F, introTraceArchimedean χ (introTraceApprox (h n) (ρ n) w₀) v)
        (fun z ↦ ∑ v : InfinitePlace F, introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower w₀ t) v)
        atTop right(-(1 / 2 : ℝ)) := by
  classical
  have hlocal (v : InfinitePlace F) := introTraceApprox_archimedean_reference_matched χ v h ρ hA w₀ hw₀ hmatch
  suffices ∀ S : Finset (InfinitePlace F), TendstoLocallyUniformlyOn (fun n z ↦
      (∑ v ∈ S, introTraceArchimedean χ (introTraceApprox (h n) (ρ n) z) v) -
       ∑ v ∈ S, introTraceArchimedean χ (introTraceApprox (h n) (ρ n) w₀) v)
      (fun z ↦ ∑ v ∈ S, introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower w₀ t) v)
      atTop right(-(1 / 2 : ℝ)) from this Finset.univ
  intro S
  induction S using Finset.induction_on with
  | empty =>
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0)
      ).tendstoUniformlyOn_const (s := right(-(1 / 2 : ℝ)))).tendstoLocallyUniformlyOn
  | insert v S hv ih =>
    refine (((hlocal v).2.2.add ih).congr (fun n z _ ↦ ?_)).congr_right (fun z _ ↦ ?_)
    · simp only [Finset.sum_insert hv, Pi.add_apply]
      ring
    · simp only [Finset.sum_insert hv, Pi.add_apply]

/-- Paper: §1.4.3, pp. 28–29. One cofinal reindexing of the mollifiers matches
the cutoffs for all unitary characters and all fixed reference parameters at once.
For Re z and Re w₀ greater than −1/2, subtract the radial power at w₀ from the
radial power at z. Each limiting local integrand is absolutely integrable. The local
integrals and their finite sum are analytic in z and are locally uniform limits of
the corresponding differences of cutoff terms. -/
theorem introTraceApprox_archimedean_reference_tendsto (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ IsIntroTraceApproximation h (ρ ∘ k) ∧
      (∀ n t u, h n t ≠ 0 → ρ (k n) u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1) ∧
      ∀ (χ : U𝔽) (w₀ : ℂ), -(1 / 2 : ℝ) < w₀.re →
      (∀ v : InfinitePlace F, AnalyticOnNhd ℂ (fun z ↦
        introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower w₀ t) v) right(-(1 / 2 : ℝ))) ∧
      AnalyticOnNhd ℂ (fun z ↦
        archSum(χ, (fun t ↦ introTracePower z t - introTracePower w₀ t))) right(-(1 / 2 : ℝ)) ∧
      (∀ v : InfinitePlace F, ∀ z ∈ right(-(1 / 2 : ℝ)), Integrable
        archIntegrand(χ, (fun t ↦ introTracePower z t - introTracePower w₀ t), v)
        (infiniteLocalMultiplicativeTamagawaMeasure F v)) ∧
      (∀ v : InfinitePlace F, TendstoLocallyUniformlyOn (fun n z ↦
        introTraceArchimedean χ (introTraceApprox (h n) (ρ (k n)) z) v -
        introTraceArchimedean χ (introTraceApprox (h n) (ρ (k n)) w₀) v)
        (fun z ↦ introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower w₀ t) v)
        atTop right(-(1 / 2 : ℝ))) ∧
      TendstoLocallyUniformlyOn (fun n z ↦
        (∑ v : InfinitePlace F, introTraceArchimedean χ (introTraceApprox (h n) (ρ (k n)) z) v) -
         ∑ v : InfinitePlace F, introTraceArchimedean χ (introTraceApprox (h n) (ρ (k n)) w₀) v)
        (fun z ↦ ∑ v : InfinitePlace F, introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower w₀ t) v)
        atTop right(-(1 / 2 : ℝ)) := by
  classical
  obtain ⟨k, hk, hAk, hmatch⟩ := introTraceApprox_rat_sub_shiftTwo_match h ρ hA
  refine ⟨k, hk, hAk, hmatch, ?_⟩
  intro χ w₀ hw₀
  have hlocal (v : InfinitePlace F) := introTraceApprox_archimedean_reference_matched χ v h (ρ ∘ k) hAk w₀ hw₀ hmatch
  exact ⟨fun v ↦ (hlocal v).1, Finset.analyticOnNhd_fun_sum _ fun v _ ↦ (hlocal v).1,
    fun v ↦ (hlocal v).2.1, fun v ↦ (hlocal v).2.2,
    introTraceApprox_archimedean_reference_matched_sum χ h (ρ ∘ k) hAk w₀ hw₀ hmatch⟩

open Classical in
/-- Paper: §§1.4.3–1.4.5, pp. 29–30. A single admissible cutoff family gives the combined trace relative to an arbitrary
anchor anywhere in the chart. The difference has an explicit holomorphic limit.
Convergence at the anchor controls the original combined functions on the whole chart,
including after restricting to any cofinal sequence. -/
theorem introTrace_combined_cutoff_anchor :
    ∃ h ρ : ℕ → ℝ → ℝ, IsIntroTraceApproximation h ρ ∧
      ∀ (χ : U𝔽) (a : ℝ), 0 ≤ a → ∀ w : ℂ, a < w.re →
        let C (n : ℕ) (z : ℂ) := archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a
        let K (z : ℂ) := archSum(χ, (fun t ↦ introTracePower z t - introTracePower w t)) +
          ∑' r : windowZeros(χ, a), (zeroOrder(χ, r.val) : ℂ) *
            (1 / (z - (r.val - 1 / 2)) - 1 / (w - (r.val - 1 / 2)))
        AnalyticOnNhd ℂ K right(a) ∧ K w = 0 ∧
          TendstoLocallyUniformlyOn (fun n z ↦ C n z - C n w) K atTop right(a) ∧
          ∀ k : ℕ → ℕ, Tendsto k atTop atTop → ∀ c : ℂ,
            (Tendsto (fun n ↦ C (k n) w) atTop (𝓝 c) ↔
              TendstoLocallyUniformlyOn (fun n ↦ C (k n)) (fun z ↦ K z + c) atTop right(a)) := by
  obtain ⟨h, ρ, hA, hmatch, hspec⟩ := introTraceApprox_exists_reference_spectral_matched (F := F)
  refine ⟨h, ρ, hA, ?_⟩
  intro χ a ha w hw C K
  have hw' : -(1/2:ℝ) < w.re := by linarith
  have hsub : right(a) ⊆ right(-(1/2:ℝ)) := fun z hz ↦ by
    change -(1/2:ℝ) < z.re
    linarith [show a < z.re from hz]
  have hmap : MapsTo (fun _ : ℂ ↦ w) right(a) right(a) := fun _ _ ↦ hw
  have harch := (introTraceApprox_archimedean_reference_matched_sum χ h ρ hA w hw' hmatch).mono hsub
  have hsp := hspec χ a ha (fun _ ↦ w) hmap (differentiableOn_const w)
  have hlocal := harch.add hsp
  have hD : TendstoLocallyUniformlyOn (fun n z ↦ C n z - C n w) K atTop right(a) := by
    apply hlocal.congr
    intro n z _
    dsimp only [C,Pi.add_apply]
    ring
  have h0 : K w = 0 := by
    have hlim : Tendsto (fun _ : ℕ ↦ (0:ℂ)) atTop (𝓝 (K w)) := by simpa using hD.tendsto_at (a := w) hw
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have harchA := Finset.analyticOnNhd_fun_sum Finset.univ (fun v _ ↦
    (introTraceApprox_archimedean_reference_matched χ v h ρ hA w hw' hmatch).1.mono hsub)
  have hspA := (introTrace_spectral_referenceSub χ a _ hmap (differentiableOn_const w)).2.2.2
  refine ⟨harchA.add hspA,h0,hD,?_⟩
  intro k hk c
  constructor
  · intro hc
    have hsubseq : TendstoLocallyUniformlyOn (fun n z ↦ C (k n) z - C (k n) w) K atTop right(a) := by
      intro u hu z hz
      obtain ⟨neighborhood, hV, hU⟩ := hD u hu z hz
      exact ⟨neighborhood,hV,hk.eventually hU⟩
    apply (hsubseq.add (hc.tendstoUniformlyOn_const (s := right(a))).tendstoLocallyUniformlyOn).congr
    intro n z _
    simp only [Pi.add_apply,sub_add_cancel]
  · intro hlim
    simpa only [h0,zero_add] using hlim.tendsto_at (a := w) hw

/-- A strictly increasing reindexing of both cutoff sequences preserves admissibility. -/
private theorem introTraceApproximation_comp_strictMono {h ρ : ℕ → ℝ → ℝ} (hA : IsIntroTraceApproximation h ρ)
    {k : ℕ → ℕ} (hk : StrictMono k) : IsIntroTraceApproximation (h ∘ k) (ρ ∘ k) := by
  obtain ⟨hh, hm, ht, ε, hε, hρ⟩ := hA
  exact ⟨fun n ↦ hh (k n), hm.comp hk.monotone, fun t ht' ↦ (ht t ht').comp hk.tendsto_atTop,
    ε ∘ k, hε.comp hk.tendsto_atTop, fun n ↦ hρ (k n)⟩

open Classical in
/-- Paper: §1.4.5, p. 30. On one matched cutoff family a cofinal holomorphic limit on the whole window
exists exactly when the combined cutoff visits a bounded set infinitely often at
one point of the window. The retained subsequence is itself admissible. -/
theorem introTrace_combined_cutoff_subsequence_iff_bounded :
    ∃ h ρ : ℕ → ℝ → ℝ, IsIntroTraceApproximation h ρ ∧
      ∀ (χ : U𝔽) (a : ℝ), 0 ≤ a → ∀ w : ℂ, a < w.re →
        let C (n : ℕ) (z : ℂ) := archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a
        (∃ R : ℝ, ∃ᶠ n in atTop, ‖C n w‖ ≤ R) ↔
          ∃ (k : ℕ → ℕ) (H : ℂ → ℂ), StrictMono k ∧ IsIntroTraceApproximation (h ∘ k) (ρ ∘ k) ∧
            AnalyticOnNhd ℂ H right(a) ∧ TendstoLocallyUniformlyOn (fun n ↦ C (k n)) H atTop right(a) := by
  obtain ⟨h,ρ,hA,hanchor⟩ := introTrace_combined_cutoff_anchor (F := F)
  refine ⟨h,ρ,hA,?_⟩
  intro χ a ha w hw C
  obtain ⟨hK, -, -, hconv⟩ := hanchor χ a ha w hw
  constructor
  · rintro ⟨R,hR⟩
    have hball : ∃ᶠ n in atTop, C n w ∈ Metric.closedBall (0:ℂ) R := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hR
    obtain ⟨c,_,k,hk,hc⟩ := (isCompact_closedBall (0:ℂ) R).tendsto_subseq' hball
    exact ⟨k,_,hk,introTraceApproximation_comp_strictMono hA hk,hK.add analyticOnNhd_const,
      (hconv k hk.tendsto_atTop c).mp hc⟩
  · rintro ⟨k,H,hk,-,-,hL⟩
    have hc := (continuous_norm.tendsto (H w)).comp (hL.tendsto_at (a := w) hw)
    refine ⟨‖H w‖+1,hk.tendsto_atTop.frequently ?_⟩
    exact ((hc.eventually (gt_mem_nhds (lt_add_one ‖H w‖))).mono fun n hn ↦ hn.le).frequently

open Classical in
/-- Paper: §1.4.5, p. 30. For one matched cutoff family and any cofinal sequence, pointwise convergence
to a specified holomorphic function on a set accumulating inside the chart implies
locally uniform convergence to that same function on the whole chart. -/
theorem introTrace_combined_cutoff_of_accumulating_set :
    ∃ h ρ : ℕ → ℝ → ℝ, IsIntroTraceApproximation h ρ ∧
      ∀ (χ : U𝔽) (a : ℝ), 0 ≤ a → ∀ (k : ℕ → ℕ), Tendsto k atTop atTop →
        ∀ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) →
        ∀ U : Set ℂ, U ⊆ right(a) → ∀ w ∈ right(a), w ∈ closure (U \ {w}) →
          let C (n : ℕ) (z : ℂ) := archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a
          (∀ z ∈ U, Tendsto (fun n ↦ C (k n) z) atTop (𝓝 (H z))) ↔
            TendstoLocallyUniformlyOn (fun n ↦ C (k n)) H atTop right(a) := by
  obtain ⟨h,ρ,hA,hanchor⟩ := introTrace_combined_cutoff_anchor (F := F)
  refine ⟨h,ρ,hA,?_⟩
  intro χ a ha k hk H hH U hU w hw hacc C
  constructor
  · intro hpoint
    obtain ⟨u,hu⟩ : U.Nonempty := by
      by_contra! he
      simp [he] at hacc
    obtain ⟨han, -, -, hconv⟩ := hanchor χ a ha u (hU hu)
    have lim := (hconv k hk (H u)).mp (hpoint u hu)
    apply lim.congr_right
    apply (han.add analyticOnNhd_const).eqOn_of_preconnected_of_mem_closure hH
      (convex_halfSpace_re_gt _).isPreconnected hw
    refine (closure_mono (Set.sdiff_subset_sdiff_left ?_)) hacc
    intro z hz
    exact tendsto_nhds_unique (lim.tendsto_at (hU hz)) (hpoint z hz)
  · exact fun hlim z hz ↦ hlim.tendsto_at (hU hz)

/-- Changing the reference subtracts a constant independent of the running parameter z. -/
theorem introTrace_archimedean_reference_cocycle (χ : U𝔽) (z w u : ℂ)
    (hz : -(1 / 2 : ℝ) < z.re) (hw : -(1 / 2 : ℝ) < w.re) (hu : -(1 / 2 : ℝ) < u.re) :
    let A (s r : ℂ) := archSum(χ, (fun t ↦ introTracePower s t - introTracePower r t))
    A z w = A z u - A w u := by
  intro A
  obtain ⟨h, ρ, hA⟩ := exists_introTraceApproximation
  obtain ⟨k, _, hk, hmatch⟩ := introTraceApprox_rat_sub_shiftTwo_match h ρ hA
  have hl (b : ℂ) (hb : -(1 / 2 : ℝ) < b.re) := introTraceApprox_archimedean_reference_matched_sum χ h (ρ ∘ k) hk b hb hmatch
  exact tendsto_nhds_unique ((hl w hw).tendsto_at hz) <|
    (((hl u hu).tendsto_at hz).sub ((hl u hu).tendsto_at hw)).congr fun n ↦ by
      ring

/-- Holomorphic moving references follow by composing two regularizations relative to zero. -/
theorem introTraceApprox_archimedean_movingReference_tendsto (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (hmatch : ∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1)
    (w : ℂ → ℂ) (hw : MapsTo w right(-(1 / 2 : ℝ)) right(-(1 / 2 : ℝ)))
    (han : AnalyticOnNhd ℂ w right(-(1 / 2 : ℝ))) :
    let A (s r : ℂ) := archSum(χ, (fun t ↦ introTracePower s t - introTracePower r t))
    AnalyticOnNhd ℂ (fun z ↦ A z (w z)) right(-(1 / 2 : ℝ)) ∧
    TendstoLocallyUniformlyOn (fun n z ↦ (∑ v, introTraceArchimedean χ approx(h, ρ, n, z) v) -
      ∑ v, introTraceArchimedean χ approx(h, ρ, n, (w z)) v) (fun z ↦ A z (w z)) atTop right(-(1 / 2 : ℝ)) := by
  intro A
  have hl := introTraceApprox_archimedean_reference_matched_sum χ h ρ hA 0 (by norm_num) hmatch
  have hH : AnalyticOnNhd ℂ (fun z ↦ A z 0) right(-(1 / 2 : ℝ)) :=
    Finset.analyticOnNhd_fun_sum _ fun v _ ↦ (introTraceApprox_archimedean_reference_matched χ v h ρ hA 0 (by norm_num) hmatch).1
  have he (z : ℂ) (hz : -(1 / 2 : ℝ) < z.re) : A z 0 - A (w z) 0 = A z (w z) :=
    (introTrace_archimedean_reference_cocycle χ z (w z) 0 hz (hw hz) (by norm_num)).symm
  constructor
  · apply AnalyticOnNhd.congr (isOpen_Ioi.preimage Complex.continuous_re) (hH.sub (hH.comp han hw))
    exact fun z hz ↦ he z hz
  · apply ((hl.sub (hl.comp w hw han.continuousOn)).congr _).congr_right
    · exact fun z hz ↦ he z hz
    · intro n z _
      simp only [Pi.sub_apply, comp_apply]
      ring

/-- After first-order cancellation in dimension d, the singularity at the identity is
bounded by the locally integrable power ‖t − 1‖^(1−d). At infinity the additive
Haar density is bounded by ‖t‖^(−2d). -/
private theorem introTrace_archimedean_character_majorant_addHaar {E : Type*} [NormedField E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (d : ℕ) (hd : Module.finrank ℝ E = d) :
    ∃ B : E → ℝ, Measurable B ∧ (∀ t, 0 ≤ B t) ∧ Integrable B μ ∧
      ∀ t : E, 1 < ‖t‖ ^ d →
        (‖t‖ ^ d)⁻¹ * (((‖t‖ ^ d) ^ 2)⁻¹ * Real.sqrt (‖t‖ ^ d) * ‖1 - t‖ / ‖1 - t‖ ^ d) ≤ B t := by
  let near := fun t : E ↦ (Metric.ball 0 4).indicator (fun x : E ↦ ‖x‖ ^ (1 - (d : ℝ))) (t - 1)
  let far := (Metric.closedBall (0 : E) 1)ᶜ.indicator (fun t : E ↦ ‖t‖ ^ (-(2 * (d : ℝ))))
  have hdim : 0 < d := hd ▸ Module.finrank_pos
  have hn : Integrable near μ := by
    have hn' : IntegrableOn (fun x : E ↦ ‖x‖ ^ (1 - (d : ℝ))) (Metric.ball 0 4) μ :=
      External.TauCeti.integrableOn_norm_rpow_ball (by rw [hd]; linarith)
    simpa [near, sub_eq_add_neg] using ((integrable_indicator_iff measurableSet_ball).2 hn').comp_add_right (-1 : E)
  have hf : Integrable far μ := (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet.compl).2
    ((External.TauCeti.integrableOn_norm_rpow_compl_closedBall_iff zero_lt_one).2
      (by
        rw [hd]
        have : 0 < (d : ℝ) := by exact_mod_cast hdim
        linarith))
  have hnm : Measurable near :=
    ((by fun_prop : Measurable fun x : E ↦ ‖x‖ ^ (1 - (d : ℝ))).indicator measurableSet_ball).comp (measurable_id.sub measurable_const)
  have hfm : Measurable far := (by fun_prop : Measurable fun t : E ↦ ‖t‖ ^ (-(2 * (d : ℝ)))).indicator
    Metric.isClosed_closedBall.measurableSet.compl
  have hn0 (t : E) : 0 ≤ near t := indicator_nonneg (fun _ _ ↦ by positivity) _
  have hf0 (t : E) : 0 ≤ far t := indicator_nonneg (fun _ _ ↦ by positivity) _
  refine ⟨fun t ↦ near t + far t, hnm.add hfm, fun t ↦ add_nonneg (hn0 t) (hf0 t), hn.add hf, ?_⟩
  intro t ht
  let N := ‖t‖ ^ d
  let b := ‖1 - t‖
  have hN : 1 < N := ht
  have ht1 : 1 < ‖t‖ := by contrapose! ht; exact pow_le_one₀ (norm_nonneg _) ht
  have hb' : ‖t‖ - 1 ≤ b := by simpa only [b, norm_one, norm_sub_rev t 1] using norm_sub_norm_le t (1 : E)
  have hb : 0 < b := by linarith
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hW : N⁻¹ * Real.sqrt N ≤ 1 := by
    have hs : Real.sqrt N ≤ N := (Real.sqrt_le_iff).2 ⟨hN0.le, by nlinarith [mul_le_mul_of_nonneg_left hN.le hN0.le]⟩
    calc N⁻¹ * Real.sqrt N ≤ N⁻¹ * N := by gcongr
      _ = 1 := inv_mul_cancel₀ hN0.ne'
  have hW' : (N ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hN.le)
  have he : b / b ^ d = b ^ (1 - (d : ℝ)) := by rw [Real.rpow_sub hb, Real.rpow_one, Real.rpow_natCast]
  change N⁻¹ * ((N ^ 2)⁻¹ * Real.sqrt N * b / b ^ d) ≤ _
  rw [show N⁻¹ * ((N ^ 2)⁻¹ * Real.sqrt N * b / b ^ d) =
    (N⁻¹ * Real.sqrt N) * ((N ^ 2)⁻¹ * (b / b ^ d)) by ring, he]
  apply (mul_le_of_le_one_left (by positivity) hW).trans
  by_cases hsmall : ‖t‖ ≤ 2
  · have hball : t - 1 ∈ Metric.ball 0 4 := by
      rw [mem_ball_zero_iff]
      have h := norm_sub_le t (1 : E)
      rw [norm_one] at h
      linarith
    have hnear : near t = b ^ (1 - (d : ℝ)) := by
      change (Metric.ball 0 4).indicator _ (t - 1) = _
      rw [indicator_of_mem hball, norm_sub_rev t 1]
    change _ ≤ near t + far t
    rw [hnear]
    exact (mul_le_of_le_one_left (by positivity) hW').trans (le_add_of_nonneg_right (hf0 t))
  · have hfar : far t = (N ^ 2)⁻¹ := by
      change (Metric.closedBall (0 : E) 1)ᶜ.indicator _ t = _
      rw [indicator_of_mem (show t ∈ (Metric.closedBall (0 : E) 1)ᶜ by simpa [mem_closedBall_zero_iff] using ht1)]
      rw [Real.rpow_neg (norm_nonneg _), mul_comm (2 : ℝ), Real.rpow_mul (norm_nonneg _), Real.rpow_natCast]
      norm_num [N]
    have h₁ : 1 ≤ b := by linarith
    have hpow : b ^ (1 - (d : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h₁ (by exact_mod_cast (show (1 : ℤ) - (d : ℤ) ≤ 0 by omega))
    have hbnd := mul_le_of_le_one_right (show 0 ≤ (N ^ 2)⁻¹ by positivity) hpow
    calc _ ≤ (N ^ 2)⁻¹ := hbnd
      _ ≤ near t + far t := by rw [hfar]; linarith [hn0 t]

/-- Transport the additive majorant to local units. The norm-one sphere has measure
zero, so the limiting half value of the radial test at one does not affect the integral. -/
private theorem introTrace_archimedean_character_majorant_chart {E : Type*} [NormedField E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : InfinitePlace F) (e : v.Completion ≃+* E) (hi : Isometry e)
    (ν : Measure E) [ν.IsAddHaarMeasure] (hd : Module.finrank ℝ E = v.mult)
    (hν : ν.restrict {0}ᶜ = ν)
    (hμ : letI := instMeasurableSpaceCompletion_riemannMasullo F v
      infiniteLocalAdditiveTamagawaMeasure F v = ν.map e.symm) :
    (∀ᵐ u : v.Completionˣ ∂infiniteLocalMultiplicativeTamagawaMeasure F v, ‖(u : v.Completion)‖ ^ v.mult ≠ 1) ∧
    ∃ B : v.Completionˣ → ℝ, Integrable B (infiniteLocalMultiplicativeTamagawaMeasure F v) ∧
      (∀ u, 0 ≤ B u) ∧ ∀ u : v.Completionˣ, 1 < ‖(u : v.Completion)‖ ^ v.mult →
        ((‖(u : v.Completion)‖ ^ v.mult) ^ 2)⁻¹ * Real.sqrt (‖(u : v.Completion)‖ ^ v.mult) *
          ‖1 - (u : v.Completion)‖ / ‖1 - (u : v.Completion)‖ ^ v.mult ≤ B u := by
  obtain ⟨H, hm, h0, hI, hb⟩ := introTrace_archimedean_character_majorant_addHaar ν _ hd
  let j : v.Completion ≃ᵢ E := ⟨e.toEquiv, hi⟩
  let : MeasurableSpace v.Completion := instMeasurableSpaceCompletion_riemannMasullo F v
  let : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace v.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let φ (u : v.Completionˣ) := e (u : v.Completion)
  have hemb : MeasurableEmbedding φ :=
    j.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comp
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.Completion)).measurableEmbedding
  let N (t : E) := ‖t‖ ^ v.mult
  have hNm : Measurable N := by dsimp [N]; fun_prop
  have hN0 (t : E) : 0 ≤ N t := pow_nonneg (norm_nonneg _) _
  let D (t : E) := ENNReal.ofReal (N t)⁻¹
  have hD : Measurable D := ENNReal.measurable_ofReal.comp hNm.inv
  have hmap : (infiniteLocalMultiplicativeTamagawaMeasure F v).map φ = ν.withDensity D := by
    apply Measure.ext_of_lintegral
    intro Φ hΦ
    rw [lintegral_map hΦ hemb.measurable, lintegral_withDensity_eq_lintegral_mul _ hD hΦ]
    simpa [φ, D, N, mul_comm] using introTraceApprox_archimedean_sub_shiftTwo_lintegral v e hi ν hν hμ Φ hΦ
  have he (x : v.Completion) : ‖e x‖ = ‖x‖ := hi.norm_map_of_map_zero (map_zero e) x
  have hnorm (u : v.Completionˣ) : N (φ u) = ‖(u : v.Completion)‖ ^ v.mult := by simp only [N, φ, he]
  constructor
  · have hnull : ∀ᵐ t ∂ν, N t ≠ 1 := by
      have hs : ∀ᵐ t ∂ν, t ∉ Metric.sphere (0 : E) 1 := compl_mem_ae_iff.mpr (Measure.addHaar_sphere ν (0 : E) 1)
      filter_upwards [hs] with t ht
      have ht' : ‖t‖ ≠ 1 := by simpa [Metric.mem_sphere, dist_zero_right] using ht
      have hd' : v.mult ≠ 0 := (hd ▸ Module.finrank_pos).ne'
      rcases lt_or_gt_of_ne ht' with hlt | hgt
      · exact (pow_lt_one₀ (norm_nonneg _) hlt hd').ne
      · exact (one_lt_pow₀ hgt hd').ne'
    have hnull' : ∀ᵐ t ∂(infiniteLocalMultiplicativeTamagawaMeasure F v).map φ, N t ≠ 1 := by
      rw [hmap]
      exact (withDensity_absolutelyContinuous ν D).ae_le hnull
    simpa only [← hnorm] using hemb.ae_map_iff.mp hnull'
  let J (t : E) := N t * H t
  refine ⟨J ∘ φ, ?_, fun u ↦ mul_nonneg (hN0 _) (h0 _), ?_⟩
  · rw [← hemb.integrable_map_iff, hmap, integrable_withDensity_iff_integrable_smul' hD (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    refine hI.mono' (((hD.ennreal_toReal).mul (hNm.mul hm)).aestronglyMeasurable) (.of_forall fun t ↦ ?_)
    simp only [D, ENNReal.toReal_ofReal (inv_nonneg.mpr (hN0 t)), smul_eq_mul, J, ← mul_assoc]
    by_cases ht : N t = 0
    · simp [ht, h0 t]
    · simp [inv_mul_cancel₀ ht, Real.norm_eq_abs, abs_of_nonneg (h0 t)]
  · intro u hu
    have hb' := hb (φ u) (by simpa only [← hnorm] using hu)
    have hsub : ‖1 - φ u‖ = ‖1 - (u : v.Completion)‖ := by
      change ‖1 - e _‖ = _
      rw [← map_one e, ← map_sub, he]
    change (N (φ u))⁻¹ * _ ≤ H (φ u) at hb'
    simp only [hsub, φ, he] at hb'
    change _ ≤ N (φ u) * H (φ u)
    rw [hnorm]
    have hpn : 0 < ‖(u : v.Completion)‖ ^ v.mult := zero_lt_one.trans hu
    simpa only [N, he, ← mul_assoc, mul_inv_cancel₀ hpn.ne', one_mul] using mul_le_mul_of_nonneg_left hb' hpn.le

private theorem introTrace_archimedean_character_majorant (v : InfinitePlace F) :
    (∀ᵐ u : v.Completionˣ ∂infiniteLocalMultiplicativeTamagawaMeasure F v, ‖(u : v.Completion)‖ ^ v.mult ≠ 1) ∧
    ∃ B : v.Completionˣ → ℝ, Integrable B (infiniteLocalMultiplicativeTamagawaMeasure F v) ∧
      (∀ u, 0 ≤ B u) ∧ ∀ u : v.Completionˣ, 1 < ‖(u : v.Completion)‖ ^ v.mult →
        ((‖(u : v.Completion)‖ ^ v.mult) ^ 2)⁻¹ * Real.sqrt (‖(u : v.Completion)‖ ^ v.mult) *
          ‖1 - (u : v.Completion)‖ / ‖1 - (u : v.Completion)‖ ^ v.mult ≤ B u := by
  by_cases hv : v.IsReal
  · exact introTrace_archimedean_character_majorant_chart v (InfinitePlace.Completion.ringEquivRealOfIsReal hv)
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).isometry volume (by simp [hv.mult_eq_one])
      (restrict_compl_singleton (μ := volume) 0) (dite_eq_left hv)
  · have hw := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      have hm := Measure.IsAddHaarMeasure.smul (volume : Measure ℂ) (c := (2 : ENNReal)) (by norm_num) (by norm_num)
      convert hm using 1
      rw [two_smul, show (2 : ENNReal) = 1 + 1 by norm_num, add_smul, one_smul]
    exact introTrace_archimedean_character_majorant_chart v (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry (2 • volume) (by simp [hw.mult_eq_two])
      (by simp [two_smul, Measure.restrict_add, restrict_compl_singleton]) (dite_eq_right hv)

private theorem introTrace_archimedean_real_character_differentiable (χ : U𝔽) (v : InfinitePlace F) (hv : v.IsReal) :
    let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
    ∃ p : ℝ → ℂ, DifferentiableAt ℝ p 1 ∧ p 1 = 1 ∧
      ∀ u : v.Completionˣ, p (e (u : v.Completion)) = (χ (archClass(v) u) : ℂ) := by
  intro e
  obtain ⟨a, ⟨_, hval⟩, _⟩ := realHeckeCharacter_parameters χ v hv
  let p (t : ℝ) := ((‖t‖ : ℝ) : ℂ) ^ a.1 * (if 0 < t then 1 else (-1 : ℂ)) ^ a.2.val
  have hpow : DifferentiableAt ℝ (fun z : ℂ ↦ z ^ a.1) 1 :=
    ((differentiableAt_id (x := (1 : ℂ))).cpow_const (Complex.ofReal_mem_slitPlane.mpr (by norm_num : (0 : ℝ) < 1))).restrictScalars ℝ
  refine ⟨p, ?_, by simp [p], ?_⟩
  · have hh := hpow.comp 1 (Complex.ofRealCLM.differentiableAt (x := (1 : ℝ)))
    apply hh.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht
    simp [p, ht, abs_of_pos ht]
  · intro u
    have h := hval (Units.map e.toMonoidHom u)
    change (χ (archClass(v) (Units.map e.symm.toMonoidHom (Units.map e.toMonoidHom u))) : ℂ) *
      _ ^ (0 : ℂ) = p (e (u : v.Completion)) at h
    have he : Units.map e.symm.toMonoidHom (Units.map e.toMonoidHom u) = u := by ext; simp
    rw [he, Complex.cpow_zero, mul_one] at h
    exact h.symm

private theorem introTrace_archimedean_complex_character_differentiable (χ : U𝔽) (v : InfinitePlace F) (hv : v.IsComplex) :
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
    ∃ p : ℂ → ℂ, DifferentiableAt ℝ p 1 ∧ p 1 = 1 ∧
      ∀ u : v.Completionˣ, p (e (u : v.Completion)) = (χ (archClass(v) u) : ℂ) := by
  intro e
  obtain ⟨a, ⟨_, hval⟩, _⟩ := complexHeckeCharacter_parameters χ v hv
  let p (t : ℂ) := ((‖t‖ ^ 2 : ℝ) : ℂ) ^ a.1 * (t / (‖t‖:ℂ)) ^ a.2
  have hpow : DifferentiableAt ℝ (fun z : ℂ ↦ z ^ a.1) 1 :=
    ((differentiableAt_id (x := (1 : ℂ))).cpow_const (Complex.ofReal_mem_slitPlane.mpr (by norm_num : (0 : ℝ) < 1))).restrictScalars ℝ
  have hn : DifferentiableAt ℝ (fun t : ℂ ↦ ‖t‖) 1 := (differentiableAt_id (𝕜 := ℝ) (x := (1 : ℂ))).norm ℂ (by simp)
  have hr : DifferentiableAt ℝ (fun t : ℂ ↦ ((‖t‖ ^ 2 : ℝ) : ℂ)) 1 := Complex.ofRealCLM.differentiableAt.comp 1 (hn.pow 2)
  have hr' : DifferentiableAt ℝ (fun t : ℂ ↦ ((‖t‖ ^ 2 : ℝ) : ℂ) ^ a.1) 1 := by
    have hp : DifferentiableAt ℝ (fun z : ℂ ↦ z ^ a.1) ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by simpa using hpow
    exact hp.comp 1 hr
  have hang : DifferentiableAt ℝ (fun t : ℂ ↦ t / (‖t‖:ℂ)) 1 := by
    have hrinv : DifferentiableAt ℝ (fun t : ℂ ↦ ‖t‖⁻¹) 1 := hn.inv (by simp)
    have hs : DifferentiableAt ℝ (fun t : ℂ ↦ ‖t‖⁻¹ • t) 1 := hrinv.smul (differentiableAt_id (𝕜 := ℝ))
    simpa only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using hs
  have hz : DifferentiableAt ℝ (fun z : ℂ ↦ z ^ a.2) ((1 : ℂ) / (‖(1 : ℂ)‖:ℂ)) :=
    (differentiableAt_zpow.mpr (Or.inl (by simp))).restrictScalars ℝ
  have hangle : DifferentiableAt ℝ (fun t : ℂ ↦ (t / (‖t‖:ℂ)) ^ a.2) 1 := by
    exact DifferentiableAt.comp (g := fun x : ℂ ↦ x ^ a.2) (f := fun t : ℂ ↦ t / (‖t‖:ℂ)) 1 hz hang
  refine ⟨p, ?_, by simp [p], ?_⟩
  · dsimp only [p]
    exact hr'.fun_mul hangle
  · intro u
    have h := hval (Units.map e.toMonoidHom u)
    change (χ (archClass(v) (Units.map e.symm.toMonoidHom (Units.map e.toMonoidHom u))) : ℂ) *
      _ ^ (0 : ℂ) = p (e (u : v.Completion)) at h
    have he : Units.map e.symm.toMonoidHom (Units.map e.toMonoidHom u) = u := by ext; simp
    rw [he, Complex.cpow_zero, mul_one] at h
    exact h.symm

private theorem introTrace_archimedean_character_lipschitz_chart (χ : U𝔽) (v : InfinitePlace F)
    {E : Type*} [NormedField E] [NormedSpace ℝ E]
    (e : v.Completion ≃+* E) (hi : Isometry e) (p : E → ℂ) (hd : DifferentiableAt ℝ p 1)
    (hp : p 1 = 1) (hval : ∀ u : v.Completionˣ, p (e (u : v.Completion)) = (χ (archClass(v) u) : ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : v.Completionˣ, ‖(χ (archClass(v) u) : ℂ) - 1‖ ≤ C * ‖1 - (u : v.Completion)‖ := by
  obtain ⟨K, hK, hk⟩ := hd.isBigO_sub.exists_nonneg
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hk.bound
  refine ⟨max K (2 / δ), hK.trans (le_max_left _ _), fun u ↦ ?_⟩
  have he : ‖e (u : v.Completion) - 1‖ = ‖1 - (u : v.Completion)‖ := by
    rw [← map_one e, ← map_sub, hi.norm_map_of_map_zero (map_zero e), norm_sub_rev]
  by_cases hx : e (u : v.Completion) ∈ Metric.ball 1 δ
  · have hb := hball hx
    change ‖p (e (u : v.Completion)) - p 1‖ ≤ K * ‖e (u : v.Completion) - 1‖ at hb
    rw [hp, hval, he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · have hsep : δ ≤ ‖1 - (u : v.Completion)‖ := by
      change ¬ dist (e (u : v.Completion)) 1 < δ at hx
      rw [dist_eq_norm, he] at hx
      exact le_of_not_gt hx
    calc
      ‖(χ (archClass(v) u) : ℂ) - 1‖ ≤ 2 := by simpa only [Circle.norm_coe, norm_one, one_add_one_eq_two] using norm_sub_le (χ (archClass(v) u) : ℂ) 1
      _ = (2 / δ) * δ := by field_simp
      _ ≤ _ := mul_le_mul (le_max_right _ _) hsep hδ.le (hK.trans (le_max_left _ _))

/-- At every archimedean place a unitary character differs from one by at most
a constant times the distance from the identity. -/
private theorem introTrace_archimedean_character_lipschitz (χ : U𝔽) (v : InfinitePlace F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : v.Completionˣ, ‖(χ (archClass(v) u) : ℂ) - 1‖ ≤ C * ‖1 - (u : v.Completion)‖ := by
  by_cases hr : v.IsReal
  · obtain ⟨p, hd, hp, he⟩ := introTrace_archimedean_real_character_differentiable χ v hr
    exact introTrace_archimedean_character_lipschitz_chart χ v _ (InfinitePlace.Completion.isometryEquivRealOfIsReal hr).isometry p hd hp he
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hr
    obtain ⟨p, hd, hp, he⟩ := introTrace_archimedean_complex_character_differentiable χ v hc
    exact introTrace_archimedean_character_lipschitz_chart χ v _ (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).isometry p hd hp he

open scoped Classical in
/-- Paper: §1.4.3, pp. 28–29. At parameter two, subtract the archimedean term of
the trivial character at the same cutoff. For every independently admissible family,
the difference converges to the absolutely convergent integral of the difference
of the actual local kernels. The local character supplies first-order cancellation. -/
theorem introTraceApprox_archimedean_sub_trivial_at_two (χ : U𝔽) (v : InfinitePlace F)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) :
    let μ := infiniteLocalMultiplicativeTamagawaMeasure F v
    let Y := fun u ↦ archIntegrand(χ, introTracePower 2, v) u - archIntegrand((1 : U𝔽), introTracePower 2, v) u
    Integrable Y μ ∧ Tendsto (fun n ↦ introTraceArchimedean χ (introTraceApprox (h n) (ρ n) 2) v -
       introTraceArchimedean (1 : U𝔽) (introTraceApprox (h n) (ρ n) 2) v) atTop
       (𝓝 ((if v.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ))) * ∫ u, Y u ∂μ)) := by
  classical
  intro μ Y
  let : MeasurableSpace v.Completion := instMeasurableSpaceCompletion_riemannMasullo F v
  let : BorelSpace v.Completion := ⟨rfl⟩
  obtain ⟨hsphere, B, hI, hB0, hB⟩ := introTrace_archimedean_character_majorant v
  obtain ⟨C, hC0, hC⟩ := introTrace_archimedean_character_lipschitz χ v
  let f (n : ℕ) := approx(h, ρ, n, (2 : ℂ))
  let N (u : v.Completionˣ) := ‖(u : v.Completion)‖ ^ v.mult
  let b (u : v.Completionˣ) := ‖1 - (u : v.Completion)‖
  let K (u : v.Completionˣ) := ((star (χ (archClass(v) u) : ℂ) - 1) * (Real.sqrt (N u) : ℂ)) / ((b u ^ v.mult : ℝ) : ℂ)
  have he (p : ℝ → ℂ) (u : v.Completionˣ) :
      archIntegrand(χ, p, v) u - archIntegrand((1 : U𝔽), p, v) u = K u * p (N u) := by
    have hn : (((ideleClassNorm F) (archClass(v) u)).val : ℝ) = N u := by rw [ideleClassNorm_ofCompletion]; rfl
    simp only [introTraceTest, hn, K, N, b]
    simp
    ring
  let X (n : ℕ) (u : v.Completionˣ) := archIntegrand(χ, f n, v) u - archIntegrand((1 : U𝔽), f n, v) u
  have hXi (n : ℕ) : Integrable (X n) μ :=
    (introTraceApprox_archimedean_integrable χ v h ρ hA n 2).sub (introTraceApprox_archimedean_integrable 1 v h ρ hA n 2)
  have hp : ∀ᵐ u ∂μ, Tendsto (fun n ↦ X n u) atTop (𝓝 (Y u)) := by
    filter_upwards [hsphere] with u hu
    simp only [X, Y, he]
    apply Filter.Tendsto.const_mul
    change N u ≠ 1 at hu
    rcases lt_or_gt_of_ne hu with hlt | hgt
    · have hf (n : ℕ) : f n (N u) = 0 :=
        image_eq_zero_of_notMem_tsupport fun hm ↦ hlt.not_gt (introTraceApprox_support h ρ hA n 2 hm)
      simp only [hf, introTracePower, ite_eq_right hlt.not_gt, ite_eq_right hlt.ne]
      exact tendsto_const_nhds
    · exact (introTraceApprox_mellin_tendsto_radial hA (2 : ℂ) hgt).comp (tendsto_id.prodMk tendsto_const_nhds)
  let Q := ((1 / 2 : ℝ) ^ (-(2 : ℝ)) + 2 ^ (-(2 : ℝ)))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb : ∀ᶠ n in atTop, ∀ u, ‖X n u‖ ≤ (C * Q) * B u := by
    filter_upwards [introTraceApprox_mellin_tendsto_cutoff_bound hA 2] with n hn
    intro u
    rw [show X n u = K u * f n (N u) from he _ _]
    by_cases ht : 1 < N u
    · have hf : ‖f n (N u)‖ ≤ Q * ((N u) ^ 2)⁻¹ := by
        have hs := hn (2 : ℂ) (N u) (by norm_num) ht
        simpa only [Q, Real.rpow_neg (show 0 ≤ N u from pow_nonneg (norm_nonneg _) _), Real.rpow_two] using hs
      have hχ : ‖star (χ (archClass(v) u) : ℂ) - 1‖ ≤ C * b u := by
        rw [show star (χ (archClass(v) u) : ℂ) - 1 = star ((χ (archClass(v) u) : ℂ) - 1) by simp, norm_star]
        exact hC u
      have hb0 : 0 ≤ b u := norm_nonneg _
      simp only [K, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (pow_nonneg hb0 _)]
      calc
        _ ≤ ((C * b u) * Real.sqrt (N u) / (b u) ^ v.mult) * (Q * ((N u) ^ 2)⁻¹) := by gcongr
        _ = (C * Q) * (((N u) ^ 2)⁻¹ * Real.sqrt (N u) * b u / (b u) ^ v.mult) := by ring
        _ ≤ (C * Q) * B u := mul_le_mul_of_nonneg_left (hB u ht) (mul_nonneg hC0 hQ)
    · have hzero : f n (N u) = 0 :=
        image_eq_zero_of_notMem_tsupport fun hm ↦ ht (introTraceApprox_support h ρ hA n 2 hm)
      simpa [hzero] using mul_nonneg (mul_nonneg hC0 hQ) (hB0 u)
  have hYm : AEStronglyMeasurable Y μ := aestronglyMeasurable_of_tendsto_ae _ (fun n ↦ (hXi n).aestronglyMeasurable) hp
  refine ⟨(hI.const_mul (C * Q)).mono' hYm ?_, ?_⟩
  · filter_upwards [hp] with u hu
    exact le_of_tendsto hu.norm (hb.mono fun n hn ↦ hn u)
  · have hi := tendsto_integral_filter_of_dominated_convergence (fun u ↦ (C * Q) * B u)
        (.of_forall fun n ↦ (hXi n).aestronglyMeasurable) (hb.mono fun n hn ↦ .of_forall hn) (hI.const_mul (C * Q)) hp
    refine (hi.const_mul (if v.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ)))).congr' (.of_forall fun n ↦ ?_)
    simp only [X, introTraceArchimedean, f]
    rw [integral_sub (introTraceApprox_archimedean_integrable χ v h ρ hA n 2) (introTraceApprox_archimedean_integrable 1 v h ρ hA n 2), mul_sub]

local notation "archSubTrivialKernel(" χ ", " z ", " v ")" =>
  (fun u ↦ archIntegrand(χ, introTracePower z, v) u - archIntegrand((1 : U𝔽), introTracePower 2, v) u)
open Classical in
local notation "archSubTrivial(" χ ", " z ", " v ")" =>
  ((if (v : InfinitePlace F).IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ))) *
    ∫ u, archSubTrivialKernel(χ, z, v) u ∂infiniteLocalMultiplicativeTamagawaMeasure F v)
local notation "archSubTrivialSum(" χ ", " z ")" =>
  (∑ v : InfinitePlace F, archSubTrivial(χ, z, v))

open Classical in
/-- Split at the same character's value at two. The difference in the parameter
and the difference in the character are separately absolutely integrable. -/
private theorem introTraceApprox_archimedean_common_matched (χ : U𝔽) (v : InfinitePlace F)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (hmatch : ∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1) :
    (∀ z ∈ right(-(1 / 2 : ℝ)), Integrable archSubTrivialKernel(χ, z, v)
      (infiniteLocalMultiplicativeTamagawaMeasure F v)) ∧
    AnalyticOnNhd ℂ (fun z ↦ archSubTrivial(χ, z, v)) right(-(1 / 2 : ℝ)) ∧
    TendstoLocallyUniformlyOn (fun n z ↦ introTraceArchimedean χ approx(h, ρ, n, z) v -
       introTraceArchimedean (1 : U𝔽) approx(h, ρ, n, (2 : ℂ)) v)
       (fun z ↦ archSubTrivial(χ, z, v)) atTop right(-(1 / 2 : ℝ)) := by
  classical
  let μ := infiniteLocalMultiplicativeTamagawaMeasure F v
  let Y (z : ℂ) := archSubTrivialKernel(χ, z, v)
  let c := if v.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ))
  obtain ⟨ha, hi, hl⟩ := introTraceApprox_archimedean_reference_matched χ v h ρ hA 2 (by norm_num) hmatch
  obtain ⟨hi', hl'⟩ := introTraceApprox_archimedean_sub_trivial_at_two χ v h ρ hA
  let Z (z : ℂ) := archIntegrand(χ, (fun t ↦ introTracePower z t - introTracePower 2 t), v)
  have he (z : ℂ) : Z z + Y 2 = Y z := by
    funext u
    dsimp [Z, Y, introTraceTest]
    ring
  have hE (z : ℂ) (hz : z ∈ right(-(1 / 2 : ℝ))) :
      introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower 2 t) v + c * (∫ u, Y 2 u ∂μ) =
        c * ∫ u, Y z u ∂μ := by
    change c * (∫ u, Z z u ∂μ) + _ = _
    rw [← mul_add, ← integral_add (hi z hz) hi', ← he]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    change Integrable (Y z) μ
    rw [← he]
    exact (hi z hz).add hi'
  · exact (ha.add analyticOnNhd_const).congr (isOpen_Ioi.preimage Complex.continuous_re) hE
  · have hc := (hl'.tendstoUniformlyOn_const (s := right(-(1 / 2 : ℝ)))).tendstoLocallyUniformlyOn
    refine ((hl.add hc).congr (fun n z hz ↦ ?_)).congr_right hE
    simp only [Pi.add_apply]
    ring

open Classical in
private theorem introTraceApprox_archimedean_common_matched_sum (χ : U𝔽)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (hmatch : ∀ n t u, h n t ≠ 0 → ρ n u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1) :
    TendstoLocallyUniformlyOn (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) -
      archSum((1 : U𝔽), approx(h, ρ, n, (2 : ℂ))))
      (fun z ↦ archSubTrivialSum(χ, z)) atTop right(-(1 / 2 : ℝ)) := by
  classical
  suffices ∀ S : Finset (InfinitePlace F), TendstoLocallyUniformlyOn (fun n z ↦
      (∑ v ∈ S, introTraceArchimedean χ approx(h, ρ, n, z) v) -
       ∑ v ∈ S, introTraceArchimedean (1 : U𝔽) approx(h, ρ, n, (2 : ℂ)) v)
      (fun z ↦ ∑ v ∈ S, archSubTrivial(χ, z, v)) atTop right(-(1 / 2 : ℝ)) from this Finset.univ
  intro S
  induction S using Finset.induction_on with
  | empty =>
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0)
      ).tendstoUniformlyOn_const (s := right(-(1 / 2 : ℝ)))).tendstoLocallyUniformlyOn
  | insert v S hv ih =>
    have hl := (introTraceApprox_archimedean_common_matched χ v h ρ hA hmatch).2.2
    refine ((hl.add ih).congr (fun n z _ ↦ ?_)).congr_right (fun z _ ↦ ?_)
    · simp only [Finset.sum_insert hv, Pi.add_apply]
      ring
    · simp only [Finset.sum_insert hv, Pi.add_apply]

open Classical in
/-- Paper: §1.4.3, pp. 28–29. Use the trivial character's archimedean term at
two as the same cutoff-dependent subtraction for all characters. One cofinal
choice of mollifier indices gives locally uniform convergence on Re z > −1/2,
both at each place and after summation. Each limiting local integral is
absolutely convergent. -/
theorem introTraceApprox_archimedean_sub_trivial_two_tendsto (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ IsIntroTraceApproximation h (ρ ∘ k) ∧
      (∀ n t u, h n t ≠ 0 → ρ (k n) u ≠ 0 → |u| ≤ 1 ∧ |u| ≤ t - 1) ∧
      ∀ χ : U𝔽,
      (∀ v : InfinitePlace F, ∀ z ∈ right(-(1 / 2 : ℝ)), Integrable archSubTrivialKernel(χ, z, v)
        (infiniteLocalMultiplicativeTamagawaMeasure F v)) ∧
      (∀ v : InfinitePlace F, AnalyticOnNhd ℂ (fun z ↦ archSubTrivial(χ, z, v)) right(-(1 / 2 : ℝ))) ∧
      AnalyticOnNhd ℂ (fun z ↦ archSubTrivialSum(χ, z)) right(-(1 / 2 : ℝ)) ∧
      (∀ v : InfinitePlace F, TendstoLocallyUniformlyOn (fun n z ↦
        introTraceArchimedean χ approx(h, (ρ ∘ k), n, z) v -
        introTraceArchimedean (1 : U𝔽) approx(h, (ρ ∘ k), n, (2 : ℂ)) v)
        (fun z ↦ archSubTrivial(χ, z, v)) atTop right(-(1 / 2 : ℝ))) ∧
      TendstoLocallyUniformlyOn (fun n z ↦ archSum(χ, approx(h, (ρ ∘ k), n, z)) -
        archSum((1 : U𝔽), approx(h, (ρ ∘ k), n, (2 : ℂ))))
        (fun z ↦ archSubTrivialSum(χ, z)) atTop right(-(1 / 2 : ℝ)) := by
  classical
  obtain ⟨k, hk, hAk, hmatch⟩ := introTraceApprox_rat_sub_shiftTwo_match h ρ hA
  refine ⟨k, hk, hAk, hmatch, fun χ ↦ ?_⟩
  have hl (v : InfinitePlace F) := introTraceApprox_archimedean_common_matched χ v h (ρ ∘ k) hAk hmatch
  exact ⟨fun v ↦ (hl v).1, fun v ↦ (hl v).2.1, Finset.analyticOnNhd_fun_sum _ fun v _ ↦ (hl v).2.1,
    fun v ↦ (hl v).2.2, introTraceApprox_archimedean_common_matched_sum χ h (ρ ∘ k) hAk hmatch⟩

section ArchimedeanGammaEvaluation

/-- Subtract the two convergent Gauss integrals before integration at zero. -/
private theorem introTrace_archimedean_gamma_difference_integral (k : ℝ) (w b : ℂ) (hw : 0 < w.re) (hb : 0 < b.re) :
    let G (t : ℝ) := (k : ℂ) * (Complex.exp (-w * t) - Complex.exp (-b * t)) /
      (1 - (Real.exp (-t) : ℂ))
    IntegrableOn G (Ioi 0) ∧ ∫ t in Ioi (0:ℝ), G t = (k:ℂ)*(Complex.digamma b - Complex.digamma w) := by
  intro G
  have hw' := integral_gaussDigammaDifference (w := w) (d := 1) one_pos (by simpa using hw)
  have hb' := integral_gaussDigammaDifference (w := b) (d := 1) one_pos (by simpa using hb)
  have heq : G = fun t ↦ (k : ℂ) * (gaussDigammaDifference 1 b t - gaussDigammaDifference 1 w t) := by
    funext t
    simp only [G, gaussDigammaDifference, Complex.ofReal_one, Complex.ofReal_exp, Complex.ofReal_neg,
      neg_one_mul]
    ring
  rw [heq]
  refine ⟨(hb'.1.sub hw'.1).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub hb'.1 hw'.1, hb'.2, hw'.2]
  simp

/-- Multiplication by the same bounded cutoff preserves the Gauss difference limit. -/
private theorem introTrace_archimedean_gamma_difference_cutoff (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    {k : ℝ} (hk : 0 < k) (w b : ℂ) (hw : 0 < w.re) (hb : 0 < b.re) :
    let G (t : ℝ) := (k : ℂ) * (Complex.exp (-w * t) - Complex.exp (-b * t)) /
      (1 - (Real.exp (-t) : ℂ))
    Tendsto (fun n ↦ ∫ t in Ioi (0 : ℝ), (h n (Real.exp (k*t)) : ℂ) * G t)
      atTop (𝓝 ((k:ℂ)*(Complex.digamma b - Complex.digamma w))) := by
  intro G
  obtain ⟨hi, he⟩ := introTrace_archimedean_gamma_difference_integral k w b hw hb
  rw [← he]
  apply tendsto_integral_of_dominated_convergence (fun t ↦ ‖G t‖)
  · intro n
    have hm : Continuous (fun t : ℝ ↦ (h n (Real.exp (k*t)) : ℂ)) :=
      Complex.continuous_ofReal.comp ((hA.1 n).1.continuous.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    exact hm.aestronglyMeasurable.mul hi.aestronglyMeasurable
  · exact hi.norm
  · intro n
    refine .of_forall fun t ↦ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((hA.1 n).2.2.2 _).1]
    exact mul_le_of_le_one_left (norm_nonneg _) ((hA.1 n).2.2.2 _).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change Tendsto (fun n ↦ (h n (Real.exp (k*t)) : ℂ) * G t) atTop (𝓝 (G t))
    simpa only [Function.comp_apply, Complex.ofReal_one, one_mul] using ((Complex.continuous_ofReal.tendsto 1).comp
      (hA.2.2.1 _ (Real.one_lt_exp_iff.mpr (mul_pos hk ht)))).mul (tendsto_const_nhds (x := G t))

local notation "cutPower(" h ", " n ", " z ")" =>
  (fun x : ℝ ↦ ((h : ℕ → ℝ → ℝ) n x : ℂ) * introTracePower (z : ℂ) x)

/-- Multiplying the limiting power by a fixed cutoff produces a continuous compact test. -/
private theorem introTrace_archimedean_gamma_cutoff_profile (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (n : ℕ) (z : ℂ) :
    Continuous cutPower(h,n,z) ∧ HasCompactSupport cutPower(h,n,z) ∧
    tsupport cutPower(h,n,z) ⊆ Ioi 1 := by
  have he : cutPower(h,n,z) = fun x ↦ (h n x : ℂ) * ((max x 1 : ℝ) : ℂ) ^ (-z) := by
    funext x
    by_cases hx : 1 < x
    · simp [introTracePower, hx, max_eq_left hx.le]
    · have h0 : h n x = 0 := image_eq_zero_of_notMem_tsupport (fun hm ↦ hx ((hA.1 n).2.2.1 hm))
      simp [h0]
  have hc : Continuous (fun x ↦ (h n x : ℂ)) := Complex.continuous_ofReal.comp (hA.1 n).1.continuous
  have hb : Continuous (fun x : ℝ ↦ ((max x 1 : ℝ) : ℂ)^(-z)) :=
    continuous_iff_continuousAt.mpr fun x ↦
      (Complex.continuous_ofReal.comp (continuous_id.max continuous_const)).continuousAt.cpow
        continuousAt_const (Complex.ofReal_mem_slitPlane.mpr (zero_lt_one.trans_le (le_max_right x 1)))
  have hs : tsupport cutPower(h,n,z) ⊆ tsupport (h n) := closure_mono fun x hx ↦ by
    intro h0
    exact hx (by simp [h0])
  exact ⟨he ▸ hc.mul hb, (hA.1 n).2.1.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans (hA.1 n).2.2.1⟩

open Classical in
/-- The common cutoff multiplies the difference of the two geometric integrands. Their
known integrability therefore gives convergence by dominated convergence. -/
private theorem introTrace_archimedean_gamma_cutoff_geometry (χ : U𝔽) (v : InfinitePlace F) (z : ℂ)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (hY : Integrable (fun u ↦ archIntegrand(χ, introTracePower z, v) u -
      archIntegrand((1:U𝔽), introTracePower 2, v) u) (infiniteLocalMultiplicativeTamagawaMeasure F v)) :
    Tendsto (fun n ↦ introTraceArchimedean χ cutPower(h,n,z) v - introTraceArchimedean (1:U𝔽) cutPower(h,n,2) v)
      atTop (𝓝 ((if v.IsReal then (1/2:ℂ) else 1/(2*(Real.pi:ℂ))) *
        ∫ u, archIntegrand(χ, introTracePower z, v) u - archIntegrand((1:U𝔽), introTracePower 2, v) u
          ∂infiniteLocalMultiplicativeTamagawaMeasure F v)) := by
  classical
  let : MeasurableSpace v.Completion := instMeasurableSpaceCompletion_riemannMasullo F v
  let : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace v.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let μ := infiniteLocalMultiplicativeTamagawaMeasure F v
  let N (u : v.Completionˣ) := ‖(u : v.Completion)‖^v.mult
  let Y (u : v.Completionˣ) := archIntegrand(χ, introTracePower z, v) u - archIntegrand((1:U𝔽), introTracePower 2, v) u
  have hN : Measurable N := by
    exact (continuous_norm.comp Units.continuous_val).measurable.pow_const _
  have hpoint (η : U𝔽) (s : ℂ) (n : ℕ) (u : v.Completionˣ) :
      archIntegrand(η,cutPower(h,n,s),v) u = (h n (N u) : ℂ) * archIntegrand(η,introTracePower s,v) u := by
    simp only [introTraceTest, ideleClassNorm_ofCompletion]
    change _ * ((h n (N u):ℂ) * _) * _ / _ = _
    ring
  have hi (n : ℕ) (a : ℂ) (η : U𝔽) := introTrace_archimedean_integrable_of_compact_profile η v _
    (introTrace_archimedean_gamma_cutoff_profile h ρ hA n a).1
    (introTrace_archimedean_gamma_cutoff_profile h ρ hA n a).2.1 (introTrace_archimedean_gamma_cutoff_profile h ρ hA n a).2.2
  have hlim : Tendsto (fun n ↦ ∫ u, (h n (N u):ℂ) * Y u ∂μ) atTop (𝓝 (∫ u, Y u ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun u ↦ ‖Y u‖)
    · intro n
      exact ((Complex.measurable_ofReal.comp ((hA.1 n).1.continuous.measurable.comp hN)).aestronglyMeasurable).mul
        hY.aestronglyMeasurable
    · exact hY.norm
    · intro n
      refine .of_forall fun u ↦ ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((hA.1 n).2.2.2 _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) ((hA.1 n).2.2.2 _).2
    · filter_upwards [(introTrace_archimedean_character_majorant v).1] with u hu
      change N u ≠ 1 at hu
      rcases lt_or_gt_of_ne hu with hu | hu
      · have h0 : Y u = 0 := by
          simp only [Y,introTraceTest,ideleClassNorm_ofCompletion]
          change _ * introTracePower z (N u) * _ / _ - _ * introTracePower 2 (N u) * _ / _ = _
          simp [introTracePower, hu.not_gt, hu.ne]
        simp [h0]
      · simpa using ((Complex.continuous_ofReal.tendsto 1).comp (hA.2.2.1 _ hu)).mul (tendsto_const_nhds (x:=Y u))
  apply (hlim.const_mul _).congr'
  refine .of_forall fun n ↦ ?_
  simp only [introTraceArchimedean]
  rw [← mul_sub, ← integral_sub (hi n z χ) (hi n 2 1)]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun u ↦ by simp only [hpoint,Y,mul_sub]

/-- Each individual gamma integral converges with its compact logarithmic cutoff. -/
private theorem introTrace_archimedean_gamma_weight_integrable (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (n : ℕ) {k : ℝ} (hk : 0 < k) (w : ℂ) :
    Integrable (fun t : ℝ ↦ (k:ℂ)*(h n (Real.exp (k*t)):ℂ)*Complex.exp (-w*t)/(1-(Real.exp (-t):ℂ))) := by
  let H := fun t : ℝ ↦ (k:ℂ)*(h n (Real.exp (k*t)):ℂ)*Complex.exp (-w*t)/(1-(Real.exp (-t):ℂ))
  let K := (Homeomorph.mulLeft₀ k hk.ne') ⁻¹' (Real.log '' tsupport (h n))
  have hK : IsCompact K := (Homeomorph.mulLeft₀ k hk.ne').isCompact_preimage.mpr
    ((hA.1 n).2.1.image_of_continuousOn (Real.continuousOn_log.mono fun x hx ↦
      (zero_lt_one.trans ((hA.1 n).2.2.1 hx)).ne'))
  have hsup : support H ⊆ K := by
    intro t ht
    refine ⟨Real.exp (k*t), subset_tsupport _ ?_, Real.log_exp _⟩
    exact fun h0 ↦ ht (by simp [H,h0])
  apply (integrableOn_iff_integrable_of_support_subset hsup).mp
  apply ContinuousOn.integrableOn_compact hK
  have hc : Continuous (fun t : ℝ ↦ (h n (Real.exp (k*t)):ℂ)) :=
    Complex.continuous_ofReal.comp ((hA.1 n).1.continuous.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  refine (show Continuous (fun t : ℝ ↦ (k:ℂ)*(h n (Real.exp (k*t)):ℂ)*Complex.exp (-w*t)) by fun_prop).continuousOn.div
    (show Continuous (fun t : ℝ ↦ (1:ℂ)-(Real.exp (-t):ℂ)) by fun_prop).continuousOn ?_
  rintro t ⟨x,hx,he⟩
  change Real.log x = k*t at he
  have ht : 0 < t := (mul_pos_iff_of_pos_left hk).mp (he ▸ Real.log_pos ((hA.1 n).2.2.1 hx))
  apply sub_ne_zero.mpr
  exact_mod_cast (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)).ne'

/-- For a one-sided cut power, only the positive sample in the local digamma kernel survives. -/
private theorem introTrace_archimedean_gamma_cutoff_kernel (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (n : ℕ) (z p q : ℂ) {k : ℝ} (hk : 0 < k) :
    -(∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k p q
      (fun y ↦ cutPower(h,n,z) (Real.exp y)) t) =
      ∫ t in Ioi (0:ℝ), (k:ℂ)*(h n (Real.exp (k*t)):ℂ)*Complex.exp (-(p+(k:ℂ)*z)*t)/(1-(Real.exp (-t):ℂ)) := by
  rw [← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hvan {y : ℝ} (hy : y ≤ 0) : h n (Real.exp y) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs ↦ (Real.exp_le_one_iff.mpr hy).not_gt ((hA.1 n).2.2.1 hs))
  have hkt : 0 < k*t := mul_pos hk ht
  have hp : introTracePower z (Real.exp (k*t)) = Complex.exp (-(z * (k:ℂ)*t)) := by
    rw [introTracePower, ite_eq_left (Real.one_lt_exp_iff.mpr hkt),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos (k*t)).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
    congr 1
    push_cast
    ring
  simp only [heckeArchimedeanDigammaKernel, hvan (le_refl 0), hvan (neg_nonpos.mpr hkt.le), hp,
    Complex.ofReal_zero, zero_mul, mul_zero, zero_div, zero_sub, add_zero, mul_neg, neg_neg]
  rw [show -(p+(k:ℂ)*z)*(t:ℂ) = -(z*(k:ℂ)*t) + -p*t by ring, Complex.exp_add]
  ring

open Classical in
local notation "archScale(" v ")" =>
  (show ℝ from if (v : InfinitePlace F).IsReal then 1/2 else 1)
open Classical in
local notation "archShift(" χ ", " v ")" =>
  (if hv : (v : InfinitePlace F).IsReal then
    let p := (realHeckeCharacter_parameters (χ:U𝔽) v hv).exists.choose
    p.1 + (p.2.val : ℂ)
  else
    let p := (complexHeckeCharacter_parameters (χ:U𝔽) v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
    p.1 + (p.2.natAbs : ℂ)/2)
local notation "gammaWeight(" h ", " n ", " k ", " w ")" =>
  (fun t : ℝ ↦ ((k : ℝ):ℂ)*((h : ℕ → ℝ → ℝ) n (Real.exp (k*t)):ℂ)*Complex.exp (-(w:ℂ)*t)/(1-(Real.exp (-t):ℂ)))

open Classical in
/-- At each infinite place, the local trace of a cut power is a single weighted exponential integral. -/
private theorem introTrace_archimedean_gamma_cutoff_local (χ : U𝔽) (v : InfinitePlace F)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    introTraceArchimedean χ cutPower(h,n,z) v =
      ∫ t in Ioi (0:ℝ), gammaWeight(h,n,archScale(v),(archScale(v):ℂ)*(z + 1/2 + archShift(χ,v))) t := by
  classical
  obtain ⟨hc,hs,hp⟩ := introTrace_archimedean_gamma_cutoff_profile h ρ hA n z
  have hh := introTraceArchimedean_eq_neg_digamma_of_supported_above_one χ v cutPower(h,n,z) hc.measurable
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport (f := cutPower(h,n,z)) (fun hh ↦ hx.not_gt (hp hh)))
    (introTrace_archimedean_integrable_of_compact_profile χ v _ hc hs hp)
  rw [hh]
  by_cases hv : v.IsReal
  · simp only [hv, dite_true, ite_true]
    rw [introTrace_archimedean_gamma_cutoff_kernel h ρ hA n z _ _ (by norm_num : (0:ℝ)<1/2)]
    congr 1
    funext t
    push_cast
    ring_nf
  · simp only [hv, dite_false, ite_false]
    rw [introTrace_archimedean_gamma_cutoff_kernel h ρ hA n z _ _ one_pos]
    congr 1
    funext t
    push_cast
    ring_nf

open Classical in
/-- The geometric subtraction equals a difference of digamma values, with factor one half at
a real place and factor one at a complex place. -/
private theorem introTrace_archimedean_sub_eq_digamma (χ : U𝔽) (v : InfinitePlace F) (z : ℂ) (hz : -(1/2:ℝ) < z.re) :
    let k := (archScale(v):ℂ)
    let A := (if v.IsReal then (1/2:ℂ) else 1/(2*(Real.pi:ℂ))) *
      ∫ u, archIntegrand(χ,introTracePower z,v) u - archIntegrand((1:U𝔽),introTracePower 2,v) u
        ∂infiniteLocalMultiplicativeTamagawaMeasure F v
    A = k*(Complex.digamma (k*((2:ℂ)+1/2+archShift((1:U𝔽),v))) -
      Complex.digamma (k*(z+1/2+archShift(χ,v)))) := by
  classical
  intro k A
  let w := k*(z+1/2+archShift(χ,v))
  let b := k*((2:ℂ)+1/2+archShift((1:U𝔽),v))
  have hk : 0 < archScale(v) := by split <;> norm_num
  have hshift (η : U𝔽) : 0 ≤ (archShift(η,v)).re := by
    split_ifs with hv
    · have h := (realHeckeCharacter_parameters η v hv).exists.choose_spec.1
      simp only [Complex.add_re, h, zero_add, Complex.natCast_re]
      positivity
    · have h := (complexHeckeCharacter_parameters η v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose_spec.1
      simp only [Complex.add_re, h, zero_add, Complex.div_ofNat_re, Complex.natCast_re]
      positivity
  have hre (s : ℂ) (η : U𝔽) (hs : -(1/2:ℝ) < s.re) :
      0 < (k*(s+1/2+archShift(η,v))).re := by
    dsimp only [k]
    rw [Complex.re_ofReal_mul]
    exact mul_pos hk (by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith [hshift η])
  obtain ⟨h, ρ, hA, hm, -⟩ := introTraceApprox_exists_reference_spectral_matched (F:=F)
  have hg := introTrace_archimedean_gamma_cutoff_geometry χ v z h ρ hA
    ((introTraceApprox_archimedean_common_matched χ v h ρ hA hm).1 z hz)
  have hd := introTrace_archimedean_gamma_difference_cutoff h ρ hA hk w b (hre z χ hz) (hre 2 1 (by norm_num))
  apply tendsto_nhds_unique hg (hd.congr' (.of_forall fun n ↦ ?_))
  change _ = introTraceArchimedean χ cutPower(h,n,z) v - introTraceArchimedean (1:U𝔽) cutPower(h,n,2) v
  rw [introTrace_archimedean_gamma_cutoff_local χ v h ρ hA n z, introTrace_archimedean_gamma_cutoff_local (1:U𝔽) v h ρ hA n 2]
  rw [← integral_sub (introTrace_archimedean_gamma_weight_integrable h ρ hA n hk w).integrableOn
    (introTrace_archimedean_gamma_weight_integrable h ρ hA n hk b).integrableOn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change (h n (Real.exp (archScale(v)*t)):ℂ) * (k * (Complex.exp (-w*t) - Complex.exp (-b*t)) /
    (1 - (Real.exp (-t):ℂ))) = gammaWeight(h,n,archScale(v),w) t - gammaWeight(h,n,archScale(v),b) t
  dsimp only [k]
  ring

/-- The logarithmic derivative of a translated and scaled gamma function includes the
contribution from its exponential prefactor. -/
private theorem introTrace_logDeriv_gamma_affine (k B s b : ℂ) (hB : B ≠ 0) (hs : 0 < (k*(s+b)).re) :
    logDeriv (fun z ↦ B^(-(k*(z+b))) * Complex.Gamma (k*(z+b))) s =
      k*(Complex.digamma (k*(s+b)) - Complex.log B) := by
  let u (z : ℂ) := k*(z+b)
  let E (z : ℂ) := B ^ (-u z)
  have hu : HasDerivAt u k s := by simpa [u] using ((hasDerivAt_id' s).add_const b).const_mul k
  have hE := hu.neg.const_cpow (Or.inl hB)
  have he : E s ≠ 0 := by simp [E,Complex.cpow_eq_zero_iff,hB]
  have hG := (Complex.hasDerivAt_Gamma_of_re_pos hs).differentiableAt
  change logDeriv (fun z ↦ E z * Complex.Gamma (u z)) s = _
  rw [logDeriv_fun_mul (f:=E) (g:=fun z ↦ Complex.Gamma (u z)) s he (Complex.Gamma_ne_zero_of_re_pos hs)
    hE.differentiableAt (hG.comp s hu.differentiableAt), hu.logDeriv_Gamma (fun n hn ↦ by
      have hh := congrArg Complex.re hn
      simp only [Complex.neg_re,Complex.natCast_re] at hh
      change 0 < (u s).re at hs
      linarith [show (0:ℝ) ≤ n by positivity])]
  rw [logDeriv_apply, show deriv E s = E s * Complex.log B * -k from hE.deriv]
  change _ = k * (Complex.digamma (u s) - Complex.log B)
  field_simp
  ring

open Classical in
local notation "archGamma(" χ ", " v ")" =>
  (fun s : ℂ ↦ if (v : InfinitePlace F).IsReal then Complex.Gammaℝ (s + archShift(χ,v))
    else Complex.Gammaℂ (s + archShift(χ,v)) / 2)

open Classical in
/-- Evaluate the local Hecke gamma logarithmic derivative on its positive half-plane. -/
private theorem introTrace_logDeriv_local_gamma (χ : U𝔽) (v : InfinitePlace F) (s : ℂ) (hs : 0 < s.re) :
    logDeriv archGamma(χ,v) s =
      (archScale(v):ℂ)*(Complex.digamma ((archScale(v):ℂ)*(s+archShift(χ,v))) -
        Complex.log (if v.IsReal then (Real.pi:ℂ) else 2*(Real.pi:ℂ))) := by
  classical
  by_cases hv : v.IsReal
  · simp only [hv, ite_true, dite_true]
    let p := (realHeckeCharacter_parameters χ v hv).exists.choose
    let b := p.1 + (p.2.val:ℂ)
    have hp : p.1.re = 0 := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
    have hs' : 0 < ((1/2:ℂ)*(s+b)).re := by
      rw [one_div_mul_eq_div]; simp only [b,Complex.div_ofNat_re,Complex.add_re,hp,Complex.natCast_re,zero_add]
      positivity
    have he : (fun z ↦ Complex.Gammaℝ (z+b)) =
        fun z ↦ (Real.pi:ℂ)^(-((1/2:ℂ)*(z+b))) * Complex.Gamma ((1/2:ℂ)*(z+b)) := by
      funext z
      rw [Complex.Gammaℝ_def,one_div_mul_eq_div,neg_div]
    change logDeriv (fun z ↦ Complex.Gammaℝ (z+b)) s = _
    rw [he,introTrace_logDeriv_gamma_affine _ _ _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hs']
    push_cast
    rfl
  · simp only [hv, ite_false, dite_false]
    let p := (complexHeckeCharacter_parameters χ v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
    let b := p.1 + (p.2.natAbs:ℂ)/2
    have hp : p.1.re = 0 :=
      (complexHeckeCharacter_parameters χ v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose_spec.1
    have hs' : 0 < ((1:ℂ)*(s+b)).re := by
      simp only [b,one_mul,Complex.add_re,hp,Complex.div_ofNat_re,Complex.natCast_re,zero_add]
      positivity
    have he : (fun z ↦ Complex.Gammaℂ (z+b)/2) =
        fun z ↦ (2*(Real.pi:ℂ))^(-((1:ℂ)*(z+b))) * Complex.Gamma ((1:ℂ)*(z+b)) := by
      funext z
      rw [Complex.Gammaℂ_def, one_mul]
      ring
    change logDeriv (fun z ↦ Complex.Gammaℂ (z+b)/2) s = _
    rw [he,introTrace_logDeriv_gamma_affine _ _ _ _ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hs']
    dsimp only [b,p]
    norm_num

open Classical in
/-- Paper: §1.4.3, p. 29; §3.2.1, pp. 123–124; Theorem B.4.2.2, p. 616. The finite geometric
subtraction at a single infinite place equals the logarithmic derivative of its trivial gamma
factor at five halves minus that of the character’s gamma factor at the shifted argument. At
a complex place the shift includes one half the absolute angular frequency. -/
theorem introTrace_archimedean_sub_eq_localGamma_logDeriv (χ : U𝔽) (v : InfinitePlace F) (z : ℂ) (hz : -(1/2:ℝ) < z.re) :
    archSubTrivial(χ, z, v) =
      logDeriv archGamma((1:U𝔽),v) (2+1/2) - logDeriv archGamma(χ,v) (z+1/2) := by
  rw [introTrace_archimedean_sub_eq_digamma χ v z hz, introTrace_logDeriv_local_gamma (1:U𝔽) v _ (by norm_num),
    introTrace_logDeriv_local_gamma χ v _ (by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith)]
  ring

open Classical in
/-- On the positive half-plane the Hecke gamma factor has logarithmic derivative equal to
the sum of the local logarithmic derivatives. -/
private theorem introTrace_heckeGamma_logDeriv_eq_sum (χ : U𝔽) (s : ℂ) (hs : 0 < s.re) :
    logDeriv (heckeGammaFactor χ) s = ∑ v : InfinitePlace F, logDeriv archGamma(χ,v) s := by
  classical
  have hprod : heckeGammaFactor χ = fun a ↦ ∏ v : InfinitePlace F, archGamma(χ,v) a := by
    funext a
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : v.IsReal <;> simp [hv,add_assoc]
  have hn (v : InfinitePlace F) : archGamma(χ,v) s ≠ 0 := by
    have hh := heckeGammaFactor_ne_zero_of_re_pos χ hs
    rw [hprod,Finset.prod_ne_zero_iff] at hh
    exact hh _ (Finset.mem_univ _)
  rw [hprod]
  apply logDeriv_fun_prod (fun v _ ↦ hn v)
  intro v _
  have hn' := hn v
  by_cases hv : v.IsReal
  · simp only [hv,ite_true,dite_true] at hn' ⊢
    let b := archShift(χ,v)
    have h0 : Complex.Gammaℝ (s+b) ≠ 0 := by simpa [b,hv] using hn'
    have hg := (Complex.differentiable_Gammaℝ_inv.differentiableAt (x:=s+b)).inv (inv_ne_zero h0)
    have hg' : DifferentiableAt ℂ Complex.Gammaℝ (s+b) := by simpa only [Pi.inv_def,inv_inv] using hg
    simpa [b,hv,Function.comp_def] using hg'.comp s ((differentiableAt_id (x:=s)).add_const b)
  · simp only [hv,ite_false,dite_false] at hn' ⊢
    let b := archShift(χ,v)
    have h0 : Complex.Gammaℂ (s+b) ≠ 0 := by
      intro hz
      apply hn'
      simpa [b,hv] using (show Complex.Gammaℂ (s+b)/2=0 by rw [hz]; simp)
    have hg := (Complex.differentiable_Gammaℂ_inv.differentiableAt (x:=s+b)).inv (inv_ne_zero h0)
    have hg' : DifferentiableAt ℂ Complex.Gammaℂ (s+b) := by simpa only [Pi.inv_def,inv_inv] using hg
    simpa [b,hv,Function.comp_def] using (hg'.comp s ((differentiableAt_id (x:=s)).add_const b)).div_const 2

open Classical in
/-- Paper: §1.4.3, p. 29, and §3.2.1, pp. 123–124. The analytic archimedean term in the
common-counterterm limit is the difference of the logarithmic derivatives of two Hecke gamma factors. -/
theorem introTrace_archimedean_sub_sum_eq_heckeGamma_logDeriv (χ : U𝔽) (z : ℂ) (hz : -(1/2:ℝ) < z.re) :
    archSubTrivialSum(χ, z) =
      logDeriv (heckeGammaFactor (1:U𝔽)) (5/2) - logDeriv (heckeGammaFactor χ) (z+1/2) := by
  rw [introTrace_heckeGamma_logDeriv_eq_sum (1:U𝔽) _ (by norm_num), introTrace_heckeGamma_logDeriv_eq_sum χ _
    (by simp only [Complex.add_re,Complex.div_ofNat_re,Complex.one_re]; linarith), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simpa only [show (2:ℂ)+1/2=5/2 by norm_num] using introTrace_archimedean_sub_eq_localGamma_logDeriv χ v z hz

open Classical in
/-- Paper: §1.4.3, p. 29. After the common cofinal choice of mollifier indices, the
archimedean subtraction converges locally uniformly to its explicit gamma-factor expression. -/
theorem introTraceApprox_archimedean_sub_tendsto_heckeGamma_logDeriv (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ IsIntroTraceApproximation h (ρ ∘ k) ∧
      ∀ χ : U𝔽, TendstoLocallyUniformlyOn (fun n z ↦ archSum(χ, approx(h, (ρ ∘ k), n, z)) -
        archSum((1 : U𝔽), approx(h, (ρ ∘ k), n, (2 : ℂ))))
        (fun z ↦ logDeriv (heckeGammaFactor (1 : U𝔽)) (5 / 2) -
          logDeriv (heckeGammaFactor χ) (z + 1 / 2)) atTop right(-(1 / 2 : ℝ)) := by
  obtain ⟨k, hk, hAk, _, hχ⟩ := introTraceApprox_archimedean_sub_trivial_two_tendsto (F := F) h ρ hA
  exact ⟨k, hk, hAk, fun χ ↦ (hχ χ).2.2.2.2.congr_right fun z hz ↦ introTrace_archimedean_sub_sum_eq_heckeGamma_logDeriv χ z hz⟩

/-- Removing the simple singularity in the Gauss kernel leaves a positive
factor bounded by one on the positive real axis. -/
private theorem introTrace_gauss_remainder_bounds (x : ℝ) (hx : 0 < x) :
    0 ≤ (1-Real.exp (-x))⁻¹-x⁻¹ ∧ (1-Real.exp (-x))⁻¹-x⁻¹ ≤ 1 := by
  let D := 1-Real.exp (-x)
  have hd : 0 < D := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
  have hdx : D ≤ x := by dsimp only [D]; linarith [Real.add_one_le_exp (-x)]
  refine ⟨sub_nonneg.mpr (inv_anti₀ hd hdx),?_⟩
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at h
  change D⁻¹-x⁻¹ ≤ 1
  apply sub_le_iff_le_add.mpr
  rw [inv_le_iff_one_le_mul₀ hd]
  dsimp only [D]
  field_simp
  nlinarith

/-- The Laplace transform of the bounded Gauss remainder has norm at most
the reciprocal of the real part of its argument. -/
private theorem introTrace_gauss_remainder_laplace (w : ℂ) (hw : 0 < w.re) :
    let A (x : ℝ) := (1-Real.exp (-x))⁻¹-x⁻¹
    let G (x : ℝ) := Complex.exp (-w*x)*(A x : ℂ)
    IntegrableOn G (Ioi 0) ∧ ‖∫ x in Ioi (0:ℝ), G x‖ ≤ w.re⁻¹ := by
  intro A G
  have he : IntegrableOn (fun x : ℝ ↦ Real.exp (-w.re*x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hw) 0
  have h : ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)), ‖G x‖ ≤ Real.exp (-w.re*x) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have ha := introTrace_gauss_remainder_bounds x hx
    change ‖Complex.exp (-w*x)*(A x : ℂ)‖ ≤ _
    rw [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_of_nonneg ha.1]
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_le_of_le_one_right (Real.exp_pos _).le ha.2
  exact ⟨he.mono' (by dsimp [G,A]; fun_prop) h,(norm_integral_le_of_norm_le he h).trans_eq
    (by rw [integral_exp_mul_Ioi (neg_neg_of_pos hw)]; simp [one_div])⟩

/-- The positive Gauss kernel is the centered Binet kernel plus one half. -/
private theorem introTrace_gauss_eq_binet {x : ℝ} (hx : 0 < x) :
    (((1-Real.exp (-x))⁻¹-x⁻¹ : ℝ) : ℂ) = HardyCriticalLine.bennettGammaBinetKernel x + 1/2 := by
  rw [HardyCriticalLine.bennettGammaBinetKernel_eq_ofReal, ← Complex.ofReal_ofNat, ← Complex.ofReal_one,
    ← Complex.ofReal_div, ← Complex.ofReal_add, Complex.ofReal_inj]
  have he := Real.one_lt_exp_iff.mpr hx
  have hn : 1 - (Real.exp x)⁻¹ ≠ 0 := by rw [← Real.exp_neg]; linarith [Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)]
  rw [Real.exp_neg]
  field_simp [hx.ne', (Real.exp_pos x).ne', (sub_pos.mpr he).ne', hn]
  ring

/-- The logarithmic derivative of the gamma function has a Laplace correction
to its principal logarithm throughout the right half-plane. The correction
has norm at most the reciprocal of the real part. -/
theorem introTrace_digamma_log_laplace (w : ℂ) (hw : 0 < w.re) :
    let A (x : ℝ) := (1-Real.exp (-x))⁻¹-x⁻¹
    Complex.digamma w-Complex.log w = -(∫ x in Ioi (0:ℝ), Complex.exp (-w*x)*(A x : ℂ)) ∧
      ‖Complex.digamma w-Complex.log w‖ ≤ w.re⁻¹ := by
  intro A
  have he := integrableOn_exp_mul_complex_Ioi (a := -w) (by simpa using hw) 0
  have eq : (∫ x in Ioi (0:ℝ), Complex.exp (-w*x)*(A x : ℂ)) =
      HardyCriticalLine.bennettGammaBinetIntegral w + 1/(2*w) := by
    calc
      _ = ∫ x in Ioi (0:ℝ), HardyCriticalLine.bennettGammaBinetKernel x * Complex.exp (-(x:ℂ)*w) +
          Complex.exp (-w*x) * (1/2:ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [show (A x:ℂ) = _ from introTrace_gauss_eq_binet hx, show -(x:ℂ)*w = -w*x by ring]
        ring
      _ = _ := by
        rw [integral_add (HardyCriticalLine.integrableOn_bennettGammaBinetIntegrand hw) (he.mul_const _),
          integral_mul_const, integral_exp_mul_complex_Ioi (by simpa using hw)]
        simp [HardyCriticalLine.bennettGammaBinetIntegral]
  have h := HardyCriticalLine.bennettGammaBinetDigamma_eqOn hw
  have hmain : Complex.digamma w-Complex.log w = -(∫ x in Ioi (0:ℝ), Complex.exp (-w*x)*(A x:ℂ)) := by
    rw [eq,h]; ring
  exact ⟨hmain, by rw [hmain,norm_neg]; exact (introTrace_gauss_remainder_laplace w hw).2⟩

open scoped FourierTransform RealInnerProductSpace in
/-- On each positive vertical line the digamma correction tends to zero at
both height ends, by the Riemann–Lebesgue lemma for its Laplace density. -/
private theorem introTrace_digamma_vertical_log_remainder (u : ℝ) (hu : 0 < u) :
    Tendsto (fun t : ℝ ↦ Complex.digamma ((u:ℂ)+(t:ℂ)*Complex.I) -
      Complex.log ((u:ℂ)+(t:ℂ)*Complex.I)) (cocompact ℝ) (𝓝 0) := by
  classical
  let A (x : ℝ) := (1-Real.exp (-x))⁻¹-x⁻¹
  let f (x : ℝ) := Complex.exp (-(u:ℂ)*x)*(A x : ℂ)
  let F₀ := (Ioi (0:ℝ)).indicator f
  have hscale : Tendsto (fun t : ℝ ↦ t/(2*Real.pi)) (cocompact ℝ) (cocompact ℝ) := by
    simpa only [div_eq_mul_inv] using Filter.tendsto_cocompact_mul_right₀ (a := (2*Real.pi)⁻¹) (by positivity)
  have h := ((Real.zero_at_infty_fourier F₀).comp hscale).neg
  rw [neg_zero] at h
  apply h.congr
  intro t
  let w : ℂ := (u:ℂ)+(t:ℂ)*Complex.I
  have hw : 0 < w.re := by simpa [w] using hu
  rw [(introTrace_digamma_log_laplace w hw).1]
  change -((𝓕 F₀) (t/(2*Real.pi))) = -∫ x in Ioi (0:ℝ), Complex.exp (-w*x)*(A x : ℂ)
  congr 1
  rw [Real.fourier_eq',← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ioi (0:ℝ)
  · simp only [F₀,Set.indicator_of_mem hx, f,smul_eq_mul,Real.inner_apply]
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    dsimp only [w]
    push_cast
    field_simp [Real.pi_ne_zero,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring
  · simp [F₀,hx]

/-- The real digamma main term along an affine vertical line retains the
logarithm of its positive height scale. -/
private theorem introTrace_digamma_affine_log_main_term (u k b : ℝ) (hu : 0 < u) (hk : 0 < k) :
    Tendsto (fun t : ℝ ↦ (Complex.digamma ((u:ℂ)+((k*t+b:ℝ):ℂ)*Complex.I)).re - Real.log |t|)
      (cocompact ℝ) (𝓝 (Real.log k)) := by
  let w (t : ℝ) := (u:ℂ)+((k*t+b:ℝ):ℂ)*Complex.I
  have ha : Tendsto (fun t : ℝ ↦ k*t+b) (cocompact ℝ) (cocompact ℝ) :=
    (Homeomorph.addRight b).isClosedEmbedding.tendsto_cocompact.comp
      (Filter.tendsto_cocompact_mul_left₀ hk.ne')
  have h₁ : Tendsto (fun t : ℝ ↦ (Complex.digamma (w t)).re - Real.log ‖w t‖)
      (cocompact ℝ) (𝓝 0) := by
    simpa only [Function.comp_def, Complex.sub_re, Complex.log_re, Complex.zero_re, w] using
      Complex.continuous_re.continuousAt.tendsto.comp ((introTrace_digamma_vertical_log_remainder u hu).comp ha)
  let c : ℂ := (u:ℂ)+(b:ℂ)*Complex.I
  let q (t : ℝ) := c*(t:ℂ)⁻¹+(k:ℂ)*Complex.I
  have htop := tendsto_norm_cocompact_atTop (E := ℝ)
  have hr : Tendsto (fun t : ℝ ↦ t⁻¹) (cocompact ℝ) (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_inv_atTop_zero.comp htop)
    exact Eventually.of_forall fun t ↦ (norm_inv t).le
  have hi : Tendsto (fun t : ℝ ↦ (t:ℂ)⁻¹) (cocompact ℝ) (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hq : Tendsto q (cocompact ℝ) (𝓝 ((k:ℂ)*Complex.I)) := by
    simpa [q] using (hi.const_mul c).add_const ((k:ℂ)*Complex.I)
  have hn : Tendsto (fun t : ℝ ↦ ‖q t‖) (cocompact ℝ) (𝓝 k) := by
    simpa only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_of_nonneg hk.le] using hq.norm
  have h₂ : Tendsto (fun t : ℝ ↦ Real.log ‖w t‖ - Real.log |t|) (cocompact ℝ) (𝓝 (Real.log k)) := by
    apply ((Real.continuousAt_log hk.ne').tendsto.comp hn).congr'
    filter_upwards [htop.eventually_gt_atTop 0, hn.eventually (lt_mem_nhds hk)] with t ht hqt
    have ht' : t ≠ 0 := norm_pos_iff.mp ht
    have he : w t = (t:ℂ)*q t := by
      dsimp [w,q,c]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr ht']
      ring
    change Real.log ‖q t‖ = Real.log ‖w t‖ - Real.log |t|
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Real.log_mul (abs_ne_zero.mpr ht') hqt.ne']
    ring
  simpa only [zero_add,sub_add_sub_cancel] using h₁.add h₂

open Classical in
/-- Paper: Section 1.4.3. On every fixed positive vertical line the real
logarithmic derivative of the Hecke gamma factor has leading term
`[F : ℚ] / 2 * (log |t| - log (2π))`, with an error vanishing at both ends. -/
theorem introTrace_heckeGamma_vertical_main_term (χ : U𝔽) (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun t : ℝ ↦ (logDeriv (heckeGammaFactor χ) ((σ:ℂ)+(t:ℂ)*Complex.I)).re -
      ((Module.finrank ℚ F : ℝ)/2)*(Real.log |t| - Real.log (2*Real.pi))) (cocompact ℝ) (𝓝 0) := by
  classical
  let s (t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I
  have hs (t : ℝ) : 0 < (s t).re := by simpa [s] using hσ
  have hlocal (v : InfinitePlace F) : Tendsto (fun t : ℝ ↦ (logDeriv archGamma(χ,v) (s t)).re -
      archScale(v)*(Real.log |t| - Real.log (2*Real.pi))) (cocompact ℝ) (𝓝 0) := by
    let k := archScale(v)
    let b := archShift(χ,v)
    let D : ℝ := if v.IsReal then Real.pi else 2*Real.pi
    have hk : 0 < k := by dsimp [k]; split_ifs <;> norm_num
    have hD : D = (2*Real.pi)*k := by dsimp [D,k]; split_ifs <;> ring
    have hDC : (if v.IsReal then (Real.pi:ℂ) else 2*(Real.pi:ℂ)) = (D:ℂ) := by
      dsimp [D]; split_ifs <;> push_cast <;> rfl
    have hlog : (Complex.log (D:ℂ)).re = Real.log (2*Real.pi) + Real.log k := by
      rw [Complex.log_re,Complex.norm_real,Real.norm_of_nonneg (by rw [hD]; positivity),
        hD,Real.log_mul (by positivity) hk.ne']
    have hb : 0 ≤ b.re := by
      dsimp only [b]
      split_ifs with hv
      · have h := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
        simp only [Complex.add_re, h, zero_add, Complex.natCast_re]
        positivity
      · have h := (complexHeckeCharacter_parameters χ v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose_spec.1
        simp only [Complex.add_re,h,zero_add,Complex.div_ofNat_re,Complex.natCast_re]
        positivity
    let u := k*(σ+b.re)
    have h := introTrace_digamma_affine_log_main_term u k (k*b.im) (mul_pos hk (add_pos_of_pos_of_nonneg hσ hb)) hk
    have hzero := (h.sub_const (Real.log k)).const_mul k
    rw [sub_self,mul_zero] at hzero
    apply hzero.congr
    intro t
    have he : (k : ℂ)*(s t + b) = (u : ℂ) + ((k*t+k*b.im : ℝ) : ℂ)*Complex.I := by
      apply Complex.ext <;> simp [s,u,Complex.mul_re,Complex.mul_im]
      ring
    rw [introTrace_logDeriv_local_gamma χ v (s t) (hs t)]
    change _ = ((k:ℂ)*(Complex.digamma ((k:ℂ)*(s t+b)) - Complex.log _)).re -
      k*(Real.log |t|-Real.log (2*Real.pi))
    rw [he,hDC,Complex.re_ofReal_mul,Complex.sub_re,hlog]
    ring
  have hh := tendsto_finsetSum Finset.univ (fun v _ ↦ hlocal v)
  simp only [Finset.sum_const_zero] at hh
  have hkdeg : ∑ v : InfinitePlace F, archScale(v) = (Module.finrank ℚ F : ℝ)/2 := by
    calc
      _ = ∑ v : InfinitePlace F, (InfinitePlace.mult v : ℝ)/2 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v.IsReal <;> simp [InfinitePlace.mult,hv]
      _ = _ := by rw [← Finset.sum_div,← Nat.cast_sum,InfinitePlace.sum_mult_eq]
  apply hh.congr
  intro t
  rw [introTrace_heckeGamma_logDeriv_eq_sum χ (s t) (hs t), Complex.re_sum]
  simp only [Finset.sum_sub_distrib,← Finset.sum_mul,hkdeg]

/-- After its first Stirling correction, the digamma remainder has
quadratic decay in the height on the entire open right half-plane. -/
private theorem introTrace_digamma_quadratic_remainder (z : ℂ) (hz : 0 < z.re)
    (hi : z.im ≠ 0) :
    ‖Complex.digamma z - Complex.log z + 1 / (2*z)‖ ≤ 1 / (2*z.im^2) := by
  let b := |z.im|
  have hb : 0 < b := abs_pos.mpr hi
  have hB := HardyCriticalLine.bennettGammaBinetDigamma_eqOn hz
  dsimp only at hB
  rw [hB, ← HardyCriticalLine.complexBinetSawtoothCorrection_eq_bennett hz,
    HardyCriticalLine.complexBinetSawtoothCorrection,
    HardyCriticalLine.integral_binetSawtooth_div_sq_eq_periodicPrimitive hz]
  set J := ∫ u : ℝ in Ioi 0, (HardyCriticalLine.binetSawtoothPrimitive u : ℂ)/(z+(u:ℂ))^3
  rw [show Complex.log z - 1/(2*z) - 2*J - Complex.log z + 1/(2*z) = -(2*J) by ring,
    norm_neg,norm_mul,Complex.norm_ofNat]
  have hJ : ‖J‖ ≤ (1/(4*b))*(1/b) := by
    rw [← HardyCriticalLine.integral_Ioi_one_div_add_sq hb, ← integral_const_mul]
    apply norm_integral_le_of_norm_le ((HardyCriticalLine.integrableOn_one_div_sq_add_const hb).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu₀ : 0 < u := hu
    let w := z+(u:ℂ)
    have hw : b ≤ ‖w‖ := by simpa [w,b] using Complex.abs_im_le_norm w
    have hws : ‖w‖ ^ 2 = (z.re+u)^2+b^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [w,b,pow_two]
    have hq : (u+b)^2 ≤ 2*‖w‖^2 := by
      rw [hws]; nlinarith [sq_nonneg (u-b), mul_nonneg hu₀.le hz.le, sq_nonneg z.re]
    have hcube : b*(u+b)^2 ≤ 2*‖w‖^3 := calc
      _ ≤ b*(2*‖w‖^2) := mul_le_mul_of_nonneg_left hq hb.le
      _ ≤ ‖w‖*(2*‖w‖^2) := mul_le_mul_of_nonneg_right hw (by positivity)
      _ = _ := by ring
    change ‖(HardyCriticalLine.binetSawtoothPrimitive u : ℂ)/w^3‖ ≤ _
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    have hw₀ := hb.trans_le hw
    calc
      _ ≤ (1/8)/‖w‖^3 := div_le_div_of_nonneg_right (HardyCriticalLine.abs_binetSawtoothPrimitive_le u) (by positivity)
      _ ≤ _ := by
        rw [show 1/(4*b)*(1/(u+b)^2) = 1/(4*(b*(u+b)^2)) by field_simp]
        have := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
          (show 0 < 4*(b*(u+b)^2) by positivity) (show 4*(b*(u+b)^2) ≤ 8*‖w‖^3 by linarith)
        convert this using 1; field_simp
  calc
    2*‖J‖ ≤ 2*((1/(4*b))*(1/b)) := by linarith
    _ = 1/(2*z.im^2) := by rw [← sq_abs z.im]; change _ = 1/(2*b^2); ring

/-- The real digamma remainder after subtracting the logarithm of the
absolute height is bounded by an explicit multiple of its inverse square. -/
theorem introTrace_digamma_real_log_height_bound (z : ℂ) (hz : 0 < z.re) (hi : z.im ≠ 0) :
    |(Complex.digamma z).re - Real.log (|z.im|)| ≤
      (z.re^2 + z.re + 1) / (2*z.im^2) := by
  have hi₂ := sq_pos_of_ne_zero hi
  have hz₂ : ‖z‖^2 = z.re^2 + z.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
  have hn : 0 < ‖z‖ := lt_of_lt_of_le (abs_pos.mpr hi) (Complex.abs_im_le_norm z)
  let e := Complex.digamma z - Complex.log z + 1/(2*z)
  have he : |e.re| ≤ 1/(2*z.im^2) :=
    (Complex.abs_re_le_norm e).trans (introTrace_digamma_quadratic_remainder z hz hi)
  have hrec : (1/(2*z)).re = z.re / (2*‖z‖^2) := by
    rw [show (1/(2*z) : ℂ) = z⁻¹/2 by ring,Complex.div_ofNat_re,Complex.inv_re,Complex.sq_norm]
    ring
  have hrec' : |(1/(2*z)).re| ≤ z.re/(2*z.im^2) := by
    rw [hrec,abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left hz.le (by positivity) (by nlinarith [sq_nonneg z.re])
  have hr : ‖z‖^2 / |z.im|^2 = 1 + z.re^2/z.im^2 := by
    rw [hz₂,sq_abs]; field_simp [hi]; ring
  have hlog : Real.log ‖z‖ - Real.log |z.im| ≤ z.re^2/(2*z.im^2) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ‖z‖^2 / |z.im|^2 by positivity)
    rw [Real.log_div (pow_ne_zero _ hn.ne') (pow_ne_zero _ (abs_pos.mpr hi).ne'),Real.log_pow,
      Real.log_pow,hr] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [show z.re^2/(2*z.im^2) = (z.re^2/z.im^2)/2 by ring]
  have hdiff : 0 ≤ Real.log ‖z‖ - Real.log |z.im| :=
    sub_nonneg.mpr (Real.log_le_log (abs_pos.mpr hi) (Complex.abs_im_le_norm z))
  have he' : (Complex.digamma z).re - Real.log |z.im| =
      e.re - (1/(2*z)).re + (Real.log ‖z‖ - Real.log |z.im|) := by
    simp [e,Complex.log_re]
  rw [he']
  calc
    _ ≤ |e.re - (1/(2*z)).re| + |Real.log ‖z‖ - Real.log (|z.im|)| := abs_add_le _ _
    _ ≤ (|e.re| + |(1/(2*z)).re|) + (Real.log ‖z‖ - Real.log |z.im|) := by
      rw [abs_of_nonneg hdiff]; linarith [abs_sub e.re (1/(2*z)).re]
    _ ≤ 1/(2*z.im^2) + z.re/(2*z.im^2) + z.re^2/(2*z.im^2) := by linarith
    _ = _ := by ring

/-- The linear Taylor approximation of the height logarithm has a
quadratic error whenever the height dominates the fixed translation. -/
private theorem introTrace_log_abs_add_linear_bound {t b : ℝ} (ht : t ≠ 0) (hb : 2*|b| ≤ |t|) :
    |Real.log |t+b| - Real.log |t| - b/t| ≤ 2*b^2/t^2 := by
  let x := b/t
  have hx : |x| ≤ 1/2 := by
    dsimp only [x]
    rw [abs_div, div_le_iff₀ (abs_pos.mpr ht)]
    linarith
  have hp : 0 < 1+x := by linarith [(abs_le.mp hx).1]
  have hlog : Real.log |t+b| - Real.log |t| = Real.log (1+x) := by
    rw [show t+b=t*(1+x) by dsimp only [x]; field_simp,
      abs_mul,abs_of_pos hp,Real.log_mul (abs_pos.mpr ht).ne' hp.ne']
    ring
  rw [hlog]
  change |Real.log (1+x)-x| ≤ _
  have hupper := Real.log_le_sub_one_of_pos hp
  rw [abs_of_nonpos (show Real.log (1+x)-x ≤ 0 by linarith)]
  have hlow := Real.one_sub_inv_le_log_of_pos hp
  have hedge : x-(1-(1+x)⁻¹) = x^2/(1+x) := by field_simp; ring
  have hsmall : x^2/(1+x) ≤ 2*x^2 := by
    rw [div_le_iff₀ hp]
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 2*x+1 by linarith [(abs_le.mp hx).1])]
  calc
    _ ≤ x^2/(1+x) := by linarith
    _ ≤ 2*x^2 := hsmall
    _ = _ := by dsimp only [x]; ring

/-- On an affine vertical line the imaginary translation produces the
reciprocal-height term in the real digamma asymptotic. -/
private theorem introTrace_digamma_affine_quadratic (u k b : ℝ) (hu : 0 < u) (hk : 0 < k)
    (t : ℝ) (ht : t ≠ 0) (hb : 2*|b| ≤ |t|) :
    |(Complex.digamma ((u:ℂ) + ((k*(t+b):ℝ):ℂ)*Complex.I)).re -
      Real.log |t| - Real.log k - b/t| ≤ (2*(u^2+u+1)/k^2 + 2*b^2)/t^2 := by
  let w := (u:ℂ) + ((k*(t+b):ℝ):ℂ)*Complex.I
  have hre : w.re = u := by simp [w]
  have him : w.im = k*(t+b) := by simp [w]
  have htri : |t| ≤ |t+b|+|b| := by
    simpa only [add_sub_cancel_right] using abs_sub (t+b) b
  have hdist : |t|/2 ≤ |t+b| := by linarith
  have htb : 0 < |t+b| := lt_of_lt_of_le (half_pos (abs_pos.mpr ht)) hdist
  have hi : w.im ≠ 0 := by rw [him]; exact mul_ne_zero hk.ne' (abs_pos.mp htb)
  have h := introTrace_digamma_real_log_height_bound w (hre.symm ▸ hu) hi
  rw [hre,him,abs_mul,abs_of_pos hk,Real.log_mul hk.ne' htb.ne'] at h
  have hv := introTrace_log_abs_add_linear_bound ht hb
  have hsq : t^2 ≤ 4*(t+b)^2 := by
    have hle : |t| ≤ 2*|t+b| := by linarith
    have h₂ := pow_le_pow_left₀ (abs_nonneg t) hle 2
    norm_num only [mul_pow,sq_abs,Nat.reducePow,one_mul, OfNat.ofNat] at h₂ ⊢
    nlinarith only [h₂]
  have htb₀ := abs_pos.mp htb
  have hn : 0 < 2*(k*(t+b))^2 := by positivity
  have hdiff : (u^2+u+1)/(2*(k*(t+b))^2) ≤ (2*(u^2+u+1)/k^2)/t^2 := by
    rw [div_div,div_le_div_iff₀ hn (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ k^2*(u^2+u+1) by positivity)
    nlinarith only [hmul]
  calc
    _ = |((Complex.digamma w).re - (Real.log k + Real.log |t+b|)) +
        (Real.log |t+b| - Real.log |t| - b/t)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add (h.trans hdiff) hv) |>.trans_eq (by ring)

open Classical in
/-- For a fixed unitary character the imaginary parts of its archimedean
parameters give the first reciprocal-height correction on every positive
vertical line. The remaining error is bounded by a constant times the
inverse square of the height in both directions. -/
theorem introTrace_heckeGamma_vertical_first_correction (χ : U𝔽) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in cocompact ℝ,
      |(logDeriv (heckeGammaFactor χ) ((σ:ℂ)+(t:ℂ)*Complex.I)).re -
        ((Module.finrank ℚ F : ℝ)/2)*(Real.log |t| - Real.log (2*Real.pi)) -
        (∑ v : InfinitePlace F, archScale(v)*(archShift(χ,v)).im)/t| ≤ C/t^2 := by
  classical
  let k (v : InfinitePlace F) := archScale(v)
  let b (v : InfinitePlace F) := archShift(χ,v)
  let u (v : InfinitePlace F) := k v * (σ + (b v).re)
  let M (v : InfinitePlace F) := 2*((u v)^2+u v+1)/(k v)^2 + 2*(b v).im^2
  let s (t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I
  let L (t : ℝ) := Real.log |t| - Real.log (2*Real.pi)
  have hs (t : ℝ) : 0 < (s t).re := by simpa [s] using hσ
  have hk (v : InfinitePlace F) : 0 < k v := by dsimp [k]; split_ifs <;> norm_num
  have hu (v : InfinitePlace F) : 0 < u v := by
    apply mul_pos (hk v)
    apply add_pos_of_pos_of_nonneg hσ
    dsimp only [b]
    split_ifs with hv
    · have h := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
      simp only [Complex.add_re,h,zero_add,Complex.natCast_re]; positivity
    · have h := (complexHeckeCharacter_parameters χ v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose_spec.1
      simp only [Complex.add_re,h,zero_add,Complex.div_ofNat_re,Complex.natCast_re]; positivity
  have hdeg : ∑ v : InfinitePlace F, k v = (Module.finrank ℚ F : ℝ)/2 := by
    calc
      _ = ∑ v : InfinitePlace F, (InfinitePlace.mult v : ℝ)/2 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v.IsReal <;> simp [k,InfinitePlace.mult,hv]
      _ = _ := by rw [← Finset.sum_div,← Nat.cast_sum,InfinitePlace.sum_mult_eq]
  let err (v : InfinitePlace F) (t : ℝ) := (logDeriv archGamma(χ,v) (s t)).re -
    k v * L t - (k v * (b v).im)/t
  have hv (v : InfinitePlace F) : ∀ᶠ t : ℝ in cocompact ℝ, |err v t| ≤ (k v*M v)/t^2 := by
    have htend := tendsto_norm_cocompact_atTop (E := ℝ)
    filter_upwards [htend.eventually_gt_atTop 0,htend.eventually_ge_atTop (2*|(b v).im|)] with t ht hb
    have ht₀ := norm_pos_iff.mp ht
    have h := introTrace_digamma_affine_quadratic (u v) (k v) (b v).im (hu v) (hk v) t ht₀ hb
    let D : ℝ := if v.IsReal then Real.pi else 2*Real.pi
    have hD : D = (2*Real.pi)*k v := by dsimp [D,k]; split_ifs <;> ring
    have hDC : (if v.IsReal then (Real.pi:ℂ) else 2*(Real.pi:ℂ)) = (D:ℂ) := by
      dsimp [D]; split_ifs <;> push_cast <;> rfl
    have hlog : (Complex.log (D:ℂ)).re = Real.log (2*Real.pi) + Real.log (k v) := by
      rw [Complex.log_re,Complex.norm_real,Real.norm_of_nonneg (by rw [hD]; positivity),
        hD,Real.log_mul (by positivity) (hk v).ne']
    have he : (k v : ℂ)*(s t + b v) = (u v : ℂ) + ((k v*(t+(b v).im):ℝ):ℂ)*Complex.I := by
      apply Complex.ext <;> simp [s,u,Complex.mul_re,Complex.mul_im]
    let w := (u v : ℂ) + ((k v*(t+(b v).im):ℝ):ℂ)*Complex.I
    have hE : err v t = k v *((Complex.digamma w).re-Real.log |t|-Real.log (k v)-(b v).im/t) := by
      dsimp only [err,L]
      rw [introTrace_logDeriv_local_gamma χ v (s t) (hs t)]
      change ((k v:ℂ)*(Complex.digamma ((k v:ℂ)*(s t + b v))-Complex.log _)).re - _ - _ = _
      rw [he,hDC,Complex.re_ofReal_mul,Complex.sub_re,hlog]; dsimp only [w]; ring
    rw [hE,abs_mul,abs_of_pos (hk v),mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h (hk v).le
  refine ⟨∑ v, k v*M v, Finset.sum_nonneg (fun v _ ↦ ?_), ?_⟩
  · have := hu v
    have := hk v
    dsimp only [M]
    positivity
  filter_upwards [eventually_all.mpr hv] with t ht
  have he : (logDeriv (heckeGammaFactor χ) (s t)).re -
      ((Module.finrank ℚ F:ℝ)/2)*L t - (∑ v, k v * (b v).im)/t = ∑ v, err v t := by
    rw [introTrace_heckeGamma_logDeriv_eq_sum χ (s t) (hs t),Complex.re_sum]
    simp only [err,Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.sum_div,hdeg]
  change |(logDeriv (heckeGammaFactor χ) (s t)).re - _*L t - _/t| ≤ _
  rw [he,Finset.sum_div]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun v _ ↦ ht v))

end ArchimedeanGammaEvaluation

open Classical in
/-- On the Euler overlap the full-window resolvent at two arbitrary parameters is the
difference of the polar-corrected finite logarithmic derivatives minus the archimedean
reference correction. The norm section and character are normalized as in the trace identity. -/
theorem introTrace_reference_resolvent_eq_logDeriv_sub_archimedean (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (a : ℝ) (ha : 1 / 2 ≤ a) :
    let L (z : ℂ) := logDeriv finiteL(χ) (z + 1 / 2) + if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0
    ∀ z w : ℂ, max a 1 < z.re → max a 1 < w.re →
      (∑' r : windowZeros(χ, a), (zeroOrder(χ, r.val) : ℂ) *
        (1 / (z - (r.val - 1 / 2)) - 1 / (w - (r.val - 1 / 2)))) = L z - L w -
          archSum(χ, (fun t ↦ introTracePower z t - introTracePower w t)) := by
  classical
  intro L z w hz hw
  obtain ⟨h, ρ, hA, hmatch, hspec⟩ := introTraceApprox_exists_reference_spectral_matched (F := F)
  have hconst : MapsTo (fun _ : ℂ ↦ w) right(a) right(a) := fun _ _ ↦ (le_max_left a 1).trans_lt hw
  have hs := (hspec χ a (by linarith) _ hconst (by fun_prop)).tendsto_at ((le_max_left a 1).trans_lt hz)
  have hlocal := (introTraceApprox_archimedean_reference_matched_sum χ h ρ hA w (by linarith [le_max_right a 1]) hmatch).tendsto_at
    (a := z) (by change -(1 / 2 : ℝ) < z.re; linarith [le_max_right a 1])
  have hc := introTrace_combined_limit_of_fixed_identity χ h ρ hA
    (introTraceApprox_full_window_fixed_digamma τ hτ χ hχ ha h ρ hA)
  apply tendsto_nhds_unique hs
  apply (((hc.tendsto_at hz).sub (hc.tendsto_at hw)).sub hlocal).congr
  intro n
  ring

open Classical in
/-- Paper: §§1.4.3–1.4.5, pp. 29–30. For a chart character and a full centered window,
the multiplicity-weighted resolvent difference equals the difference of the
polar-corrected logarithmic derivatives at `z` and `z+2`, minus the finite sum of
the regularized local archimedean integrals, on `Re z > max(a,1)`.
Deviation: Use one matched family for the spectral and archimedean limits.
The critical strip makes the exterior-zero sum vanish in every window of half-width
at least one half. The combined trace limit follows from the one-character explicit formula. -/
theorem introTrace_shiftTwo_resolvent_eq_logDeriv_sub_archimedean
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 F) F) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (a : ℝ) (ha : 1 / 2 ≤ a) :
    let L := fun z : ℂ ↦ logDeriv finiteL(χ) (z + 1 / 2) +
      if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0
    ∀ z : ℂ, max a 1 < z.re →
      (∑' r : windowZeros(χ, a), (zeroOrder(χ, r.val) : ℂ) *
        (1 / (z - (r.val - 1 / 2)) - 1 / (z + 2 - (r.val - 1 / 2)))) =
      L z - L (z + 2) - ∑ v : InfinitePlace F,
        introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z + 2) t) v := by
  intro L z hz
  have hz' : max a 1 < (z + 2).re := by
    change max a 1 < z.re + 2
    linarith
  exact introTrace_reference_resolvent_eq_logDeriv_sub_archimedean τ hτ χ hχ a ha z (z + 2) hz hz'

/-- Paper: §§1.4.3–1.4.5, pp. 29–30. In every full window for the trivial rational
character, the multiplicity-weighted shift-two resolvent series agrees on the
trace overlap with the difference of the polar-corrected logarithmic derivatives
after subtracting the real-place term. -/
theorem introTrace_rat_shiftTwo_resolvent_eq_logDeriv (a : ℝ) (ha : 1 / 2 ≤ a) :
    let m := MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) 1) univ
    let L := fun z : ℂ ↦ logDeriv (finiteHeckeL_exists_continuation (F := ℚ) 1).choose (z + 1 / 2) +
      (1 / (z + 1 / 2) + 1 / (z - 1 / 2))
    ∀ z : ℂ, max a 1 < z.re →
      (∑' r : {r : ℂ // 0 < m r ∧ |r.re - 1 / 2| < a},
        (m r.val : ℂ) * (1 / (z - (r.val - 1 / 2)) - 1 / (z + 2 - (r.val - 1 / 2)))) =
        L z - L (z + 2) - 1 / (z + 1 / 2) := by
  intro m L z hz
  obtain ⟨h, ρ, hA, harch, hspec⟩ := introTraceApprox_exists_shiftTwo_spectral_limit (F := ℚ)
  have hr := introTraceApprox_rat_spectral_shiftTwo_of_arch h ρ hA harch a ha
  exact tendsto_nhds_unique ((hspec 1 a (by linarith)).tendsto_at ((le_max_left a 1).trans_lt hz))
    (hr.tendsto_at hz)

section WindowResolvents

open Classical

local notation "poleKernel(" s ", " z ")" => (1 / ((z : ℂ) - (s : ℂ)) - 1 / (z + 2 - s))
local notation "resolvent(" χ ", " a ")" =>
  (fun z : ℂ ↦ ∑' r : windowZeros(χ, a), (zeroOrder(χ, r.val) : ℂ) * poleKernel(r.val - 1 / 2, z))
local notation "windowOrder(" χ ", " a ", " p ")" =>
  (if 0 < zeroOrder(χ, p + 1 / 2) ∧ |(p + 1 / 2).re - 1 / 2| < (a : ℝ) then
    (zeroOrder(χ, p + 1 / 2) : ℂ) else 0)

/-- Separate all other poles from one fixed point using local finiteness of the divisor. -/
private theorem introTrace_window_pole_separation (χ : U𝔽) (a : ℝ) (p : ℂ) :
    ∃ η > 0, ∀ r : windowZeros(χ, a), r.val - 1 / 2 ≠ p → η ≤ ‖(r.val - 1 / 2) - p‖ := by
  have hD :=
    (MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ).eq_zero_codiscreteWithin
  have h := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hD) (p + 1 / 2) (mem_univ _)
  rw [compl_univ, union_empty] at h
  obtain ⟨η, hη, hh⟩ := Metric.mem_nhdsWithin_iff.mp h
  refine ⟨η, hη, fun r hne ↦ le_of_not_gt fun hlt ↦ ?_⟩
  have hd : r.val ∈ Metric.ball (p + 1 / 2) η := by
    rw [Metric.mem_ball, dist_eq_norm]
    convert hlt using 2
    ring
  have hn : r.val ∈ ({p + 1 / 2} : Set ℂ)ᶜ := by
    intro he
    apply hne
    rw [show r.val = p + 1 / 2 from he]
    ring
  have hz : zeroOrder(χ, r.val) = 0 := hh ⟨hd, hn⟩
  exact r.property.1.ne' hz

section WindowCanonicalProduct

/-- A genus-one factor with multiplicity differs from one by at most
twice its multiplicity times the squared displacement near the origin. -/
private theorem introTrace_canonical_factor_bound (u : ℂ) (n : ℕ)
    (hu : ‖u‖ ≤ 1 / 2) (hn : (n : ℝ) * ‖u‖ ^ 2 ≤ 1) :
    ‖((1 + u) * Complex.exp (-u)) ^ n - 1‖ ≤ 2 * ((n : ℝ) * ‖u‖ ^ 2) := by
  have hu₁ : ‖u‖ < 1 := by linarith
  have hne : 1 + u ≠ 0 := by
    intro h
    have he : u = (-1 : ℂ) := by linear_combination h
    simp [he] at hu₁
  let L := Complex.log (1 + u) - u
  have hL : ‖L‖ ≤ ‖u‖ ^ 2 := by
    apply (Complex.norm_log_one_add_sub_self_le hu₁).trans
    have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by linarith)
    nlinarith only [mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖u‖)]
  have hnorm : ‖(n : ℂ) * L‖ ≤ (n : ℝ) * ‖u‖ ^ 2 := by
    simpa only [norm_mul, Complex.norm_natCast] using mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg n)
  have he : ((1 + u) * Complex.exp (-u)) ^ n = Complex.exp ((n : ℂ) * L) := by
    rw [Complex.exp_nat_mul]
    dsimp only [L]
    rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_log hne]
  rw [he]
  exact (Complex.norm_exp_sub_one_le (hnorm.trans hn)).trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))

/-- Square summability of the reciprocals, weighted by the given positive
multiplicities, gives an entire genus-one product and its precise zero set. -/
private theorem introTrace_canonical_product_normal {ι : Type*} (n : ι → ℕ) (q : ι → ℂ)
    (hn : ∀ i, 0 < n i) (hq : Summable (fun i ↦ (n i : ℝ) * ‖q i‖ ^ 2)) (b : ℂ) :
    let f (i : ι) (z : ℂ) := ((1 + (z - b) * q i) * Complex.exp (-((z - b) * q i))) ^ (n i)
    let P (z : ℂ) := ∏' i, f i z
    HasProdLocallyUniformlyOn f P univ ∧ Differentiable ℂ P ∧ P b = 1 ∧
      ∀ z, P z = 0 ↔ ∃ i, 1 + (z - b) * q i = 0 := by
  classical
  intro f P
  let e (i : ι) (z : ℂ) := f i z - 1
  have hfe (i : ι) (z : ℂ) : 1 + e i z = f i z := by dsimp only [e]; ring
  have hdiff (i : ι) : Differentiable ℂ (f i) := by dsimp only [f]; fun_prop
  have hbound (K : Set ℂ) (hc : IsCompact K) :
      ∃ v : ι → ℝ, Summable v ∧ ∀ᶠ i in cofinite, ∀ z ∈ K, ‖e i z‖ ≤ v i := by
    obtain ⟨B, hB⟩ := hc.isBounded.exists_norm_le
    let R := |B| + ‖b‖
    have hR : 0 ≤ R := by dsimp only [R]; positivity
    let v (i : ι) := R ^ 2 * ((n i : ℝ) * ‖q i‖ ^ 2)
    have hv : Summable v := hq.mul_left _
    refine ⟨fun i ↦ 2 * v i, hv.mul_left 2, ?_⟩
    filter_upwards [hv.tendsto_cofinite_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)] with i hi
    intro z hz
    have hzR : ‖z - b‖ ≤ R := (norm_sub_le _ _).trans (add_le_add ((hB z hz).trans (le_abs_self B)) le_rfl)
    have he : ‖(z - b) * q i‖ ^ 2 ≤ R ^ 2 * ‖q i‖ ^ 2 := by
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hzR 2) (sq_nonneg _)
    have hw : (n i : ℝ) * ‖(z - b) * q i‖ ^ 2 ≤ v i := by
      exact (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)).trans_eq (by dsimp only [v]; ring)
    have h₁ : (1 : ℝ) ≤ n i := by exact_mod_cast hn i
    have hu : ‖(z - b) * q i‖ ≤ 1 / 2 := by
      nlinarith only [sq_nonneg (‖(z - b) * q i‖ - 1 / 2), hw, hi,
        mul_le_mul_of_nonneg_right h₁ (sq_nonneg ‖(z - b) * q i‖)]
    exact (introTrace_canonical_factor_bound _ _ hu (by linarith [hw, hi])).trans
      (mul_le_mul_of_nonneg_left hw (by norm_num))
  have hprod : HasProdLocallyUniformlyOn f P univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K _ hc
    obtain ⟨v, hv, h⟩ := hbound K hc
    simpa only [hfe] using Summable.hasProdUniformlyOn_one_add hc hv h
      (fun i ↦ ((hdiff i).continuous.sub continuous_const).continuousOn)
  have hP : Differentiable ℂ P := by
    rw [← differentiableOn_univ]
    apply hprod.differentiableOn _ isOpen_univ
    exact Eventually.of_forall fun S ↦ DifferentiableOn.fun_finsetProd (u := S) (fun i _ ↦ (hdiff i).differentiableOn)
  refine ⟨hprod, hP, by simp [P, f], ?_⟩
  intro z
  constructor
  · contrapose!
    intro hz
    obtain ⟨v, hv, h⟩ := hbound {z} isCompact_singleton
    have hs : Summable (fun i ↦ ‖e i z‖) := hv.of_norm_bounded_eventually (by
      filter_upwards [h] with i hi
      simpa only [norm_norm] using hi z (mem_singleton z))
    have hf (i : ι) : 1 + e i z ≠ 0 := by
      rw [hfe]
      exact pow_ne_zero _ (mul_ne_zero (hz i) (Complex.exp_ne_zero _))
    simpa only [hfe] using tprod_one_add_ne_zero_of_summable hf hs
  · rintro ⟨i, hi⟩
    apply tprod_of_exists_eq_zero
    exact ⟨i, by simp [f, hi, ne_of_gt (hn i)]⟩

/-- Separating a single factor from the entire product identifies its
vanishing order, since the complementary product is nonzero there. -/
private theorem introTrace_canonical_product_order {ι : Type*} (p : ι → ℂ) (hp : Injective p)
    (b : ℂ) (hb : ∀ i, b ≠ p i) (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (hQ : Summable (fun i ↦ (n i : ℝ) * ‖(b - p i)⁻¹‖ ^ 2)) (i : ι) :
    let f (j : ι) (z : ℂ) := ((1 + (z - b) * (b - p j)⁻¹) * Complex.exp (-((z - b) * (b - p j)⁻¹))) ^ (n j)
    analyticOrderAt (fun z ↦ ∏' j, f j z) (p i) = (n i : ℕ∞) := by
  classical
  intro f
  let S : Finset ι := {i}
  let U (z : ℂ) := ∏' j : {j // j ∉ S}, f j.val z
  obtain ⟨_, hP, _, _⟩ := introTrace_canonical_product_normal n (fun j ↦ (b - p j)⁻¹) hn hQ b
  obtain ⟨hprod, hU, _, hzeros⟩ := introTrace_canonical_product_normal
    (fun j : {j // j ∉ S} ↦ n j.val) (fun j ↦ (b - p j.val)⁻¹) (fun j ↦ hn j.val) (hQ.subtype _) b
  have he (z : ℂ) (j : ι) : 1 + (z - b) * (b - p j)⁻¹ = (z - p j) * (b - p j)⁻¹ := by
    field_simp [sub_ne_zero.mpr (hb j)]; ring
  have hne : U (p i) ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := (hzeros (p i)).mp h
    rw [he] at hj
    have heq := hp (sub_eq_zero.mp (mul_eq_zero.mp hj |>.resolve_right (inv_ne_zero (sub_ne_zero.mpr (hb j.val)))))
    exact j.property (by simpa only [S, Finset.mem_singleton] using heq.symm)
  let v (z : ℂ) := ((b - p i)⁻¹ * Complex.exp (-((z - b) * (b - p i)⁻¹))) ^ (n i)
  apply (hP.analyticAt (p i)).analyticOrderAt_eq_natCast.mpr
  refine ⟨fun z ↦ v z * U z, ?_, mul_ne_zero (pow_ne_zero _
    (mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr (hb i))) (Complex.exp_ne_zero _))) hne, ?_⟩
  · apply AnalyticAt.mul _ (hU.analyticAt _)
    dsimp only [v]
    fun_prop
  · apply Eventually.of_forall
    intro z
    have hout : Multipliable (fun j : {j // j ∉ S} ↦ f j.val z) := (hprod.hasProd (mem_univ z)).multipliable
    have hin : Multipliable (fun j : {j // j ∈ S} ↦ f j.val z) := (hasProd_fintype _).multipliable
    have hs := Multipliable.tprod_mul_tprod_compl (s := (S : Set ι)) (f := fun j ↦ f j z) hin hout
    rw [Finset.tprod_subtype' S (fun j ↦ f j z)] at hs
    change (∏ j ∈ S, f j z) * U z = _ at hs
    rw [← hs, show (∏ j ∈ S, f j z) = f i z by simp [S], smul_eq_mul]
    dsimp only [f, v]
    rw [he, mul_assoc, mul_pow, mul_assoc]

/-- The logarithmic derivative of a normalized genus-one factor is the
difference of its resolvents at the variable and reference points. -/
private theorem introTrace_canonical_factor_logDeriv (p b z : ℂ) (n : ℕ) (hb : b ≠ p) (hz : z ≠ p) :
    logDeriv (fun w : ℂ ↦ ((1 + (w - b) * (b - p)⁻¹) * Complex.exp (-((w - b) * (b - p)⁻¹))) ^ n) z =
      (n : ℂ) * (1 / (z - p) - 1 / (b - p)) := by
  let q := (b - p)⁻¹
  have hb₀ := sub_ne_zero.mpr hb
  have hz₀ := sub_ne_zero.mpr hz
  have he : 1 + (z - b) * q = (z - p) / (b - p) := by dsimp only [q]; field_simp [hb₀]; ring
  have hf : 1 + (z - b) * q ≠ 0 := he ▸ div_ne_zero hz₀ hb₀
  have hlin : HasDerivAt (fun w : ℂ ↦ (w - b) * q) q z := by
    simpa using (((hasDerivAt_id z).sub_const b).mul_const q)
  have hpow := logDeriv_fun_pow (f := fun w : ℂ ↦ (1 + (w - b) * q) * Complex.exp (-((w - b) * q)))
    (x := z) (by fun_prop) n
  rw [hpow, logDeriv_fun_mul (f := fun w : ℂ ↦ 1 + (w - b) * q)
    (g := fun w : ℂ ↦ Complex.exp (-((w - b) * q))) z hf (Complex.exp_ne_zero _) (by fun_prop) (by fun_prop)]
  have hneg : HasDerivAt (fun w : ℂ ↦ -((w - b) * q)) (-q) z := hlin.neg
  rw [logDeriv_apply, logDeriv_apply, (hlin.const_add 1).deriv, hneg.cexp.deriv, he]
  dsimp only [q]
  field_simp [hb₀, hz₀, Complex.exp_ne_zero]
  ring

/-- At any point off the shifted zero set, the squared reciprocals of the
distances to the zeros are summable with their actual multiplicities. -/
private theorem introTrace_canonical_reciprocal_squares (χ : U𝔽) (a : ℝ) (z : ℂ)
    (hz : ∀ r : windowZeros(χ, a), z ≠ r.val - 1 / 2) :
    Summable (fun r : windowZeros(χ, a) ↦ (zeroOrder(χ, r.val) : ℝ) * ‖(z - (r.val - 1 / 2))⁻¹‖ ^ 2) := by
  obtain ⟨η, hη, hsep⟩ := introTrace_window_pole_separation χ a z
  let C := 1 + (1 + ‖z‖) / η
  apply ((introTraceApprox_spectral_differentiable_zeroCount χ a).mul_left (C ^ 2)).of_norm_bounded
  intro r
  have hm : 0 ≤ (zeroOrder(χ, r.val) : ℝ) := (Int.cast_pos.mpr r.property.1).le
  have hδ : η ≤ ‖z - (r.val - 1 / 2)‖ := by
    rw [norm_sub_rev]
    exact hsep r (hz r).symm
  have h := introTrace_resolvent_inv_norm_of_separation hη hδ (le_refl ‖z‖)
  have hw : ‖(z - (r.val - 1 / 2))⁻¹‖ ≤ C / (1 + |r.val.im|) := by
    simpa [C, norm_inv, one_div, Complex.sub_im] using h
  rw [Real.norm_of_nonneg (mul_nonneg hm (sq_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw 2) hm).trans_eq
    (by rw [div_pow]; ring)

/-- Subtraction at the reference point gives an absolutely summable
resolvent difference at every point away from the selected zeros. -/
private theorem introTrace_canonical_resolvent_summable (χ : U𝔽) (a : ℝ) (b z : ℂ)
    (hb : ∀ r : windowZeros(χ, a), b ≠ r.val - 1 / 2) (hz : ∀ r : windowZeros(χ, a), z ≠ r.val - 1 / 2) :
    Summable (fun r : windowZeros(χ, a) ↦ (zeroOrder(χ, r.val) : ℂ)*
      (1 / (z - (r.val - 1 / 2)) - 1 / (b - (r.val - 1 / 2)))) := by
  have h := (introTrace_canonical_reciprocal_squares χ a z hz).add (introTrace_canonical_reciprocal_squares χ a b hb)
  apply (h.mul_left ‖b - z‖).of_norm_bounded
  intro r
  let p := r.val - 1 / 2
  let m := (zeroOrder(χ, r.val) : ℝ)
  have hm : 0 ≤ m := (Int.cast_pos.mpr r.property.1).le
  have hid : 1 / (z - p) - 1 / (b - p) = (b - z) * (z - p)⁻¹ * (b - p)⁻¹ := by
    have hz₀ : z - p ≠ 0 := sub_ne_zero.mpr (hz r)
    have hb₀ : b - p ≠ 0 := sub_ne_zero.mpr (hb r)
    field_simp [hz₀, hb₀]
    ring
  change ‖(zeroOrder(χ, r.val) : ℂ) * (1 / (z - p) - 1 / (b - p))‖ ≤ _
  rw [hid, norm_mul, norm_mul, norm_mul, Complex.norm_intCast, abs_of_nonneg hm]
  let A := ‖(z - p)⁻¹‖
  let B := ‖(b - p)⁻¹‖
  change m * ((‖b - z‖ * A) * B) ≤ ‖b - z‖ * (m * A ^ 2 + m * B ^ 2)
  have hab : A * B ≤ A ^ 2 + B ^ 2 := by nlinarith [sq_nonneg (A - B), sq_nonneg A, sq_nonneg B]
  exact (show m * ((‖b - z‖ * A) * B) = ‖b - z‖ * (m * (A * B)) by ring).le.trans
    ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab hm) (norm_nonneg _)).trans_eq (by ring))

open Classical in
/-- Paper: §§1.4.3–1.4.5, pp. 29–30. Deviation: encode the
reference-subtracted spectral resolvent by a genus-one canonical product.
It is entire and normalized at the reference point. Its zeros are exactly
the shifted window zeros, with their original multiplicities, and its
logarithmic derivative sums the resolvent differences off this zero set. -/
theorem introTrace_window_canonical_product (χ : U𝔽) (a : ℝ) (b : ℂ)
    (hb : ∀ r : windowZeros(χ, a), b ≠ r.val - 1 / 2) :
    let p (r : windowZeros(χ, a)) := r.val - 1 / 2
    let n (r : windowZeros(χ, a)) := (zeroOrder(χ, r.val)).toNat
    let f (r : windowZeros(χ, a)) (z : ℂ) :=
      ((1 + (z - b) * (b - p r)⁻¹) * Complex.exp (-((z - b) * (b - p r)⁻¹))) ^ (n r)
    let P (z : ℂ) := ∏' r, f r z
    TendstoLocallyUniformlyOn (fun (S : Finset (windowZeros(χ, a))) z ↦ ∏ r ∈ S, f r z) P atTop univ ∧
      Differentiable ℂ P ∧ P b = 1 ∧ (∀ z, P z = 0 ↔ ∃ r, z = p r) ∧
      (∀ r, analyticOrderAt P (p r) = (n r : ℕ∞)) ∧
      ∀ z, (∀ r, z ≠ p r) →
        HasSum (fun r ↦ (zeroOrder(χ, r.val) : ℂ) * (1 / (z - p r) - 1 / (b - p r))) (logDeriv P z) := by
  classical
  intro p n f P
  have hn (r : windowZeros(χ, a)) : 0 < n r := by
    have h := r.property.1
    dsimp only [n]
    omega
  have hr (r : windowZeros(χ, a)) : (n r : ℝ) = (zeroOrder(χ, r.val) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg r.property.1.le
  have hc (r : windowZeros(χ, a)) : (n r : ℂ) = (zeroOrder(χ, r.val) : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg r.property.1.le
  have hQ : Summable (fun r ↦ (n r : ℝ) * ‖(b - p r)⁻¹‖ ^ 2) := by
    simpa only [hr] using introTrace_canonical_reciprocal_squares χ a b hb
  obtain ⟨hprod, hP, hbP, hzeros⟩ := introTrace_canonical_product_normal n (fun r ↦ (b - p r)⁻¹) hn hQ b
  have he (z : ℂ) (r : windowZeros(χ, a)) : 1 + (z - b) * (b - p r)⁻¹ = (z - p r) * (b - p r)⁻¹ := by
    have hr₀ : b - p r ≠ 0 := sub_ne_zero.mpr (hb r)
    field_simp [hr₀]
    ring
  have he₀ (z : ℂ) (r : windowZeros(χ, a)) : 1 + (z - b) * (b - p r)⁻¹ = 0 ↔ z = p r := by
    rw [he, mul_eq_zero, or_iff_left (inv_ne_zero (sub_ne_zero.mpr (hb r))), sub_eq_zero]
  have hzero (z : ℂ) : P z = 0 ↔ ∃ r, z = p r := by simpa only [he₀] using hzeros z
  have hinj : Injective p := fun r s h ↦ Subtype.ext (sub_left_inj.mp h)
  refine ⟨hprod, hP, hbP, hzero, introTrace_canonical_product_order p hinj b hb n hn hQ, ?_⟩
  intro z hz
  have hf (r : windowZeros(χ, a)) : f r z ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (fun h ↦ hz r ((he₀ z r).mp h)) (Complex.exp_ne_zero _))
  have hfd (r : windowZeros(χ, a)) : DifferentiableOn ℂ (f r) univ := by dsimp only [f]; fun_prop
  have hlog (r : windowZeros(χ, a)) :
      logDeriv (f r) z = (zeroOrder(χ, r.val) : ℂ) * (1 / (z - p r) - 1 / (b - p r)) := by
    simpa only [hc] using introTrace_canonical_factor_logDeriv (p r) b z (n r) (hb r) (hz r)
  have hsum := introTrace_canonical_resolvent_summable χ a b z hb hz
  have hs : Summable (fun r ↦ logDeriv (f r) z) := by simpa only [hlog] using hsum
  have hne : P z ≠ 0 := fun h ↦ (hzero z |>.mp h).elim fun r h' ↦ hz r h'
  have hd := logDeriv_tprod_eq_tsum isOpen_univ (mem_univ z) hf hfd hs hprod.multipliableLocallyUniformlyOn hne
  exact hsum.hasSum_iff.mpr (by simpa only [hlog] using hd.symm)

/-- Changing the reference of one genus-one factor multiplies its
normalized value by an exponential of a linear function. -/
private theorem introTrace_canonical_factor_change_anchor (p b c z : ℂ) (n : ℕ) (hb : b ≠ p) (hc : c ≠ p) :
    let f (v w : ℂ) := ((1 + (w - v) * (v - p)⁻¹) * Complex.exp (-((w - v) * (v - p)⁻¹))) ^ n
    f c z * f b c * Complex.exp ((z - c) * ((n : ℂ) * (1 / (c - p) - 1 / (b - p)))) = f b z := by
  intro f
  have he (v w : ℂ) (hv : v ≠ p) : 1 + (w - v) * (v - p)⁻¹ = (w - p) * (v - p)⁻¹ := by
    field_simp [sub_ne_zero.mpr hv]; ring
  have hp : (z - c) * ((n : ℂ) * (1 / (c - p) - 1 / (b - p))) =
      (n : ℂ) * ((z - c) * (1 / (c - p) - 1 / (b - p))) := by ring
  dsimp only [f]
  rw [hp, Complex.exp_nat_mul, ← mul_pow, ← mul_pow]
  congr 1
  rw [he c z hc, he b c hb, he b z hb]
  let u := -((z - c) * (c - p)⁻¹)
  let v := -((c - b) * (b - p)⁻¹)
  let w := (z - c) * (1 / (c - p) - 1 / (b - p))
  have heq : (z - p) * (c - p)⁻¹ * Complex.exp u * ((c - p) * (b - p)⁻¹ * Complex.exp v) * Complex.exp w =
      ((z - p) * (c - p)⁻¹ * (c - p) * (b - p)⁻¹) * (Complex.exp u * Complex.exp v * Complex.exp w) := by ring
  rw [heq, ← Complex.exp_add, ← Complex.exp_add, inv_mul_cancel_right₀ (sub_ne_zero.mpr hc)]
  congr 2
  dsimp only [u, v, w]
  ring

/-- Paper: §§1.4.3–1.4.5, pp. 29–30. Deviation: changing the reference of
the canonical product changes it by its value at the new reference and by
a linear exponential determined by the old logarithmic derivative there. -/
theorem introTrace_window_canonical_product_change_anchor (χ : U𝔽) (a : ℝ) (b c : ℂ)
    (hb : ∀ r : windowZeros(χ, a), b ≠ r.val - 1 / 2) (hc : ∀ r : windowZeros(χ, a), c ≠ r.val - 1 / 2) :
    let p (r : windowZeros(χ, a)) := r.val - 1 / 2
    let n (r : windowZeros(χ, a)) := (zeroOrder(χ, r.val)).toNat
    let f (v : ℂ) (r : windowZeros(χ, a)) (z : ℂ) :=
      ((1 + (z - v) * (v - p r)⁻¹) * Complex.exp (-((z - v) * (v - p r)⁻¹))) ^ (n r)
    let P (v z : ℂ) := ∏' r, f v r z
    ∀ z, P b z = P c z * P b c * Complex.exp ((z - c) * logDeriv (P b) c) := by
  classical
  intro p n f P z
  obtain ⟨hB, _, _, _, _, hs⟩ := introTrace_window_canonical_product χ a b hb
  obtain ⟨hC, _, _, _, _, _⟩ := introTrace_window_canonical_product χ a c hc
  let d (r : windowZeros(χ, a)) := (zeroOrder(χ, r.val) : ℂ) * (1 / (c - p r) - 1 / (b - p r))
  have hsum : HasSum d (logDeriv (P b) c) := hs c hc
  have harith (r : windowZeros(χ, a)) : (n r : ℂ) = (zeroOrder(χ, r.val) : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg r.property.1.le
  have hrow (r : windowZeros(χ, a)) : f c r z * f b r c * Complex.exp ((z - c) * d r) = f b r z := by
    simpa only [harith] using introTrace_canonical_factor_change_anchor (p r) b c z (n r) (hb r) (hc r)
  have hcprod : HasProd (fun r ↦ f c r z) (P c z) := hC.tendsto_at (mem_univ z)
  have hbprod : HasProd (fun r ↦ f b r c) (P b c) := hB.tendsto_at (mem_univ c)
  have h := ((hcprod.mul hbprod).mul ((hsum.mul_left (z - c)).cexp)).congr_fun (fun r ↦ (hrow r).symm)
  exact h.tprod_eq

open Classical in
/-- Paper: §1.4.5, pp. 29–30. Deviation: on the common right half-plane
the normalized products for two nested zero windows agree up to a
nowhere-vanishing entire factor exactly when the larger window contains
no additional zeros. -/
theorem introTrace_window_canonical_product_eqOn_iff (χ : U𝔽) {a c : ℝ} (hac : a ≤ c) (b : ℂ)
    (hb : ∀ r : windowZeros(χ, c), b ≠ r.val - 1 / 2) :
    let f (s z : ℂ) := ((1 + (z - b) * (b - (s - 1 / 2))⁻¹) * Complex.exp (-((z - b) * (b - (s - 1 / 2))⁻¹)))^
      (zeroOrder(χ, s)).toNat
    let P (t : ℝ) (z : ℂ) := ∏' r : windowZeros(χ, t), f r.val z
    (∃ E : ℂ → ℂ, Differentiable ℂ E ∧ (∀ z, E z ≠ 0) ∧
      EqOn (P c) (fun z ↦ E z * P a z) right(c)) ↔ ∀ r : windowZeros(χ, c), |r.val.re - 1 / 2| < a := by
  classical
  intro f P
  let up (r : windowZeros(χ, a)) : windowZeros(χ, c) := ⟨r.val, r.property.1, r.property.2.trans_le hac⟩
  have hba (r : windowZeros(χ, a)) : b ≠ r.val - 1 / 2 := hb (up r)
  obtain ⟨_, ha, _, hza, _, _⟩ := introTrace_window_canonical_product χ a b hba
  obtain ⟨_, hc, _, hzc, _, _⟩ := introTrace_window_canonical_product χ c b hb
  change Differentiable ℂ (P a) at ha
  change Differentiable ℂ (P c) at hc
  constructor
  · rintro ⟨E, hE, hne, he⟩ r
    have hopen : IsOpen right(c) := isOpen_Ioi.preimage Complex.continuous_re
    have hx : ((c + 1 : ℝ) : ℂ) ∈ right(c) := by change c < ((c + 1 : ℝ) : ℂ).re; simp
    have hnear : P c =ᶠ[𝓝 ((c + 1 : ℝ) : ℂ)] (fun z ↦ E z * P a z) := by
      filter_upwards [hopen.mem_nhds hx] with z hz using he hz
    have hAc : AnalyticOnNhd ℂ (P c) univ := fun z _ ↦ hc.analyticAt z
    have hmul : AnalyticOnNhd ℂ (fun z ↦ E z * P a z) univ := fun z _ ↦ (hE.analyticAt z).mul (ha.analyticAt z)
    have hevery := hAc.eq_of_eventuallyEq hmul hnear
    have hz : P c (r.val - 1 / 2) = 0 := (hzc _).mpr ⟨r, rfl⟩
    rw [hevery] at hz
    obtain ⟨s, hs⟩ := (hza _).mp ((mul_eq_zero.mp hz).resolve_left (hne _))
    have him : r.val = s.val := sub_left_inj.mp hs
    rw [him]; exact s.property.2
  · intro h
    let eqv : windowZeros(χ, a) ≃ windowZeros(χ, c) := {
      toFun := up
      invFun := fun r ↦ ⟨r.val, r.property.1, h r⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    refine ⟨fun _ ↦ 1, differentiable_const _, fun _ ↦ one_ne_zero, ?_⟩
    intro z _
    change P c z = 1 * P a z
    rw [one_mul]
    exact (eqv.tprod_eq (fun r ↦ f r.val z)).symm

open Classical in
/-- Paper: §§1.4.3–1.4.5, pp. 29–30. The shift-by-two window resolvent
is the logarithmic derivative of the quotient of the canonical product
by its translate. The reference term cancels. -/
theorem introTrace_window_canonical_quotient_resolvent (χ : U𝔽) (a : ℝ) (b : ℂ)
    (hb : ∀ r : windowZeros(χ, a), b ≠ r.val - 1 / 2) :
    let p (r : windowZeros(χ, a)) := r.val - 1 / 2
    let P (z : ℂ) := ∏' r : windowZeros(χ, a),
      ((1 + (z - b) * (b - p r)⁻¹) * Complex.exp (-((z - b) * (b - p r)⁻¹))) ^
        (zeroOrder(χ, r.val)).toNat
    let Q (z : ℂ) := P z / P (z + 2)
    MeromorphicOn Q univ ∧ ∀ z, (∀ r, z ≠ p r) → (∀ r, z + 2 ≠ p r) →
      HasSum (fun r ↦ (zeroOrder(χ, r.val) : ℂ) * (1 / (z - p r) - 1 / (z + 2 - p r)))
        (logDeriv Q z) := by
  classical
  intro p P Q
  obtain ⟨_, hP, _, hzeros, _, hs⟩ := introTrace_window_canonical_product χ a b hb
  change Differentiable ℂ P at hP
  let g (z : ℂ) := z + 2
  have hg (z : ℂ) : HasDerivAt g 1 z := (hasDerivAt_id z).add_const 2
  have hPg : Differentiable ℂ (P ∘ g) := hP.comp (fun z ↦ (hg z).differentiableAt)
  refine ⟨fun z _ ↦ (hP.analyticAt z).meromorphicAt.div (hPg.analyticAt z).meromorphicAt, ?_⟩
  intro z hz hshift
  have hne (w : ℂ) (hw : ∀ r, w ≠ p r) : P w ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := (hzeros w).mp h
    exact hw r hr
  have he : logDeriv Q z = logDeriv P z - logDeriv P (z + 2) := by
    change logDeriv (P / (P ∘ g)) z = _
    rw [logDeriv_div (g := P ∘ g) z (hne z hz) (hne (z + 2) hshift) (hP z) (hPg z),
      logDeriv_comp (hP (g z)) (hg z).differentiableAt, (hg z).deriv, mul_one]
  rw [he]
  apply ((hs z hz).sub (hs (z + 2) hshift)).congr_fun
  intro r
  dsimp only [Pi.sub_apply]
  ring

end WindowCanonicalProduct

private theorem introTrace_window_kernel_norm {s z : ℂ} {δ R : ℝ} (hδ : 0 < δ)
    (hd : δ ≤ ‖z - s‖) (hd' : δ ≤ ‖z + 2 - s‖) (hR : ‖z‖ ≤ R) (hR' : ‖z + 2‖ ≤ R) :
    ‖poleKernel(s, z)‖ ≤ (2 * (1 + (1 + R) / δ) ^ 2) / (1+|s.im|) ^ 2 := by
  have hn := norm_pos_iff.mp (hδ.trans_le hd)
  have hn' := norm_pos_iff.mp (hδ.trans_le hd')
  have he : poleKernel(s, z) = 2 * (1 / (z - s)) * (1 / (z + 2 - s)) := by
    field_simp [hn, hn']
    ring
  have hb := introTrace_resolvent_inv_norm_of_separation hδ hd hR
  have hb' := introTrace_resolvent_inv_norm_of_separation hδ hd' hR'
  rw [he, norm_mul, norm_mul, norm_div, norm_div, norm_one]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ 2 * ((1 + (1 + R) / δ) / (1+|s.im|)) * ((1 + (1 + R) / δ) / (1+|s.im|)) :=
      mul_le_mul (by linarith only [hb]) hb' (by positivity)
        (by nlinarith [le_trans (by positivity : 0 ≤ 1/‖z - s‖) hb])
    _ = _ := by field_simp

/-- Removing the summand at the center leaves a normally convergent analytic sum on a ball. -/
private theorem introTrace_window_tail_analytic (χ : U𝔽) (a : ℝ) (ha : a ≤ 1 / 2)
    (p : ℂ) (hp : -1 < p.re) :
    let term := fun (r : windowZeros(χ, a)) z ↦
      (zeroOrder(χ, r.val) : ℂ) * poleKernel(r.val - 1 / 2, z)
    let tail := fun r : windowZeros(χ, a) ↦ fun z ↦ if r.val - 1 / 2 = p then 0 else term r z
    AnalyticAt ℂ (fun z ↦ ∑' r, tail r z) p ∧
      ∀ᶠ z in 𝓝 p, Summable fun r ↦ tail r z := by
  classical
  intro term tail
  obtain ⟨η, hη, hgap⟩ := introTrace_window_pole_separation χ a p
  -- A quarter-unit ball also stays clear of every pole translated by minus two.
  let δ := min (η / 2) (1 / 4)
  let R := ‖p‖ + 4
  let C := 2 * (1 + (1 + R) / δ) ^ 2
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδη : δ ≤ η / 2 := min_le_left _ _
  have hδq : δ ≤ 1 / 4 := min_le_right _ _
  let U := Metric.ball p δ
  have hup : p ∈ U := Metric.mem_ball_self hδ
  have hopen : IsOpen U := Metric.isOpen_ball
  have hb (r : windowZeros(χ, a)) (z : ℂ) (hz : z ∈ U) (hne : r.val - 1 / 2 ≠ p) :
      δ ≤ ‖z - (r.val - 1 / 2)‖ ∧ δ ≤ ‖z + 2 - (r.val - 1 / 2)‖ ∧ ‖z‖ ≤ R ∧ ‖z + 2‖ ≤ R := by
    let s := r.val - 1 / 2
    have hzp : ‖z - p‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm, U] using hz
    have hs : s.re < 1 / 2 := by simpa [s] using ((abs_lt.mp r.property.2).2.trans_le ha)
    have htri := norm_sub_le_norm_sub_add_norm_sub s z p
    have hgap' := hgap r hne
    change η ≤ ‖s - p‖ at hgap'
    have hreal := Complex.abs_re_le_norm (z - p)
    have hreal' := (le_abs_self (z + 2 - s).re).trans (Complex.abs_re_le_norm _)
    have hlower := neg_abs_le (z - p).re
    norm_num [Complex.sub_re, Complex.add_re] at hreal hreal' hlower
    have hn := norm_le_norm_sub_add z p
    have hn' := norm_add_le z (2: ℂ)
    norm_num only [Complex.norm_ofNat] at hn'
    change δ ≤ ‖z - s‖ ∧ δ ≤ ‖z + 2 - s‖ ∧ ‖z‖ ≤ R ∧ ‖z + 2‖ ≤ R
    rw [norm_sub_rev s z] at htri
    dsimp only [R]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hmajor := (introTraceApprox_spectral_differentiable_zeroCount χ a).mul_left C
  have hbd (r : windowZeros(χ, a)) (z : ℂ) (hz : z ∈ U) :
      ‖tail r z‖ ≤ C * ((zeroOrder(χ, r.val) : ℝ) / (1+|r.val.im|) ^ 2) := by
    have hn : 0 < (zeroOrder(χ, r.val):ℝ) := Int.cast_pos.mpr r.property.1
    by_cases he : r.val - 1 / 2 = p
    · simp only [tail, he, ite_true, norm_zero]
      dsimp [C]
      positivity
    · obtain ⟨h, h', k, k'⟩ := hb r z hz he
      have hk := introTrace_window_kernel_norm hδ h h' k k'
      have him : (r.val - 1 / 2).im = r.val.im := by simp
      rw [him] at hk
      simp only [tail, term, he, ite_false, norm_mul, Complex.norm_intCast, abs_of_pos hn]
      exact (mul_le_mul_of_nonneg_left hk hn.le).trans_eq (by dsimp [C]; ring)
  refine ⟨?_, Filter.Eventually.mono (hopen.mem_nhds hup) fun z hz ↦
    hmajor.of_norm_bounded (fun r ↦ hbd r z hz)⟩
  apply (Complex.differentiableOn_tsum_of_summable_norm hmajor ?_ hopen hbd).analyticOnNhd hopen p hup
  intro r
  by_cases he : r.val - 1 / 2 = p
  · simpa only [tail, he, ite_true] using (differentiableOn_const (0: ℂ) : DifferentiableOn ℂ _ U)
  · simp only [tail, he, ite_false, term]
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.sub
    · apply (differentiableOn_const _).div (differentiableOn_id.sub (differentiableOn_const _))
      exact fun z hz ↦ norm_pos_iff.mp (hδ.trans_le (hb r z hz he).1)
    · apply (differentiableOn_const _).div
        ((differentiableOn_id.add (differentiableOn_const _)).sub (differentiableOn_const _))
      exact fun z hz ↦ norm_pos_iff.mp (hδ.trans_le (hb r z hz he).2.1)

/-- The singular part of the resolvent germ is a single term, weighted by its multiplicity. -/
private theorem introTrace_window_resolvent_germ (χ : U𝔽) (a : ℝ) (ha : a ≤ 1 / 2)
    (p : ℂ) (hp : -1 < p.re) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A p ∧
      resolvent(χ, a) =ᶠ[𝓝 p] fun z ↦ A z + windowOrder(χ, a, p) * poleKernel(p, z) := by
  classical
  let term := fun (r : windowZeros(χ, a)) z ↦
    (zeroOrder(χ, r.val) : ℂ) * poleKernel(r.val - 1 / 2, z)
  let tail := fun r : windowZeros(χ, a) ↦ fun z ↦ if r.val - 1 / 2 = p then 0 else term r z
  obtain ⟨hA, hS⟩ := introTrace_window_tail_analytic χ a ha p hp
  refine ⟨_, hA, ?_⟩
  filter_upwards [hS] with z hz
  change Summable (fun r ↦ tail r z) at hz
  change (∑' r, term r z) = (∑' r, tail r z) + windowOrder(χ, a, p) * poleKernel(p, z)
  by_cases hm : 0 < zeroOrder(χ, p + 1 / 2) ∧ |(p + 1 / 2).re - 1 / 2| < a
  · let r₀ : windowZeros(χ, a) := ⟨p + 1 / 2, hm⟩
    have he (r : windowZeros(χ, a)) : r.val - 1 / 2 = p ↔ r = r₀ := by
      constructor
      · exact fun h ↦ Subtype.ext (sub_eq_iff_eq_add.mp h)
      · rintro rfl
        dsimp [r₀]
        ring
    have hsum : Summable (fun r ↦ term r z) := hz.congr_cofinite (by
      filter_upwards [eventually_cofinite_ne r₀] with r hr
      simp only [tail, ite_eq_right ((he r).not.mpr hr)])
    rw [hsum.tsum_eq_add_tsum_ite r₀, add_comm, ite_eq_left hm]
    congr 1
    · exact tsum_congr fun r ↦ by simp only [tail, he]
    · simp [term, r₀]
  · rw [ite_eq_right hm, zero_mul, add_zero]
    apply tsum_congr
    intro r
    have hn : r.val - 1 / 2 ≠ p := by
      intro eq
      exact hm (sub_eq_iff_eq_add.mp eq ▸ r.property)
    simp only [tail, ite_eq_right hn]

private theorem introTrace_window_resolvent_meromorphic (χ : U𝔽) (a : ℝ) (ha : a ≤ 1 / 2) :
    MeromorphicOn (resolvent(χ, a)) right(-1) := by
  intro p hp
  obtain ⟨A, hA, he⟩ := introTrace_window_resolvent_germ χ a ha p hp
  apply MeromorphicAt.congr _ (he.filter_mono nhdsWithin_le_nhds).symm
  apply hA.meromorphicAt.add
  fun_prop

/-- Shifted poles lie to the left of this domain, so they contribute no residue here. -/
private theorem introTrace_window_resolvent_residue (χ : U𝔽) (a : ℝ) (ha : a ≤ 1 / 2)
    (p : ℂ) (hp : -1 < p.re) :
    Tendsto (fun z ↦ (z - p) * resolvent(χ, a) z) (𝓝[≠] p) (𝓝 (windowOrder(χ, a, p))) := by
  obtain ⟨A, hA, he⟩ := introTrace_window_resolvent_germ χ a ha p hp
  let c := windowOrder(χ, a, p)
  let B := fun z : ℂ ↦ (z - p) * A z + c * (1 - (z - p) / (z + 2 - p))
  have hden : p + 2 - p ≠ 0 := by ring_nf; norm_num
  have hB : ContinuousAt B p := by
    dsimp [B]
    fun_prop (disch := first | exact hA.continuousAt | exact hden)
  have hBp : B p = c := by simp [B]
  apply (hBp ▸ hB.tendsto.mono_left nhdsWithin_le_nhds : Tendsto B (𝓝[≠] p) (𝓝 c)).congr'
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hne
  change z ≠ p at hne
  rw [hz]
  dsimp only [B, c]
  have hn := sub_ne_zero.mpr hne
  rw [mul_add, mul_comm (z - p) (windowOrder(χ, a, p) * _), mul_assoc, sub_mul]
  field_simp [hn]

private theorem introTrace_window_order_eq_of_resolvent_eqOn (χ : U𝔽) (a b : ℝ)
    (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2)
    (h : EqOn (resolvent(χ, a)) (resolvent(χ, b)) right(1)) (p : ℂ) (hp : -1 < p.re) :
    windowOrder(χ, a, p) = windowOrder(χ, b, p) := by
  let D := resolvent(χ, a) - resolvent(χ, b)
  have hm : MeromorphicOn D right(-1) :=
    (introTrace_window_resolvent_meromorphic χ a ha).sub (introTrace_window_resolvent_meromorphic χ b hb)
  have hq : meromorphicOrderAt D 2 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have h2 : (2 : ℂ) ∈ right(1) := by norm_num
    have hU : IsOpen right(1) := isOpen_Ioi.preimage Complex.continuous_re
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (hU.mem_nhds h2)] with z hz
    exact sub_eq_zero.mpr (h hz)
  have hbase : (2 : ℂ) ∈ right(-1) := by norm_num
  have hord := hm.meromorphicOrderAt_eq_top_of_isPreconnected (convex_halfSpace_re_gt _).isPreconnected
    hbase (show p ∈ right(-1) from hp) hq
  refine tendsto_nhds_unique_of_eventuallyEq (introTrace_window_resolvent_residue χ a ha p hp)
    (introTrace_window_resolvent_residue χ b hb p hp) ?_
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hord] with z hz
  exact congrArg ((z - p)*·) (sub_eq_zero.mp hz)

private theorem introTrace_shiftTwo_resolvent_eqOn_iff_windows (χ : U𝔽) (a : ℝ) (ha : a ≤ 1 / 2) :
    EqOn resolvent(χ, a) resolvent(χ, 1 / 2) right(1) ↔
      ∀ r : windowZeros(χ, 1 / 2), |r.val.re - 1 / 2| < a := by
  classical
  constructor
  · intro he r
    change EqOn (resolvent(χ, a)) (resolvent(χ, 1 / 2)) right(1) at he
    let p := r.val - 1 / 2
    have hp : -1 < p.re := by
      dsimp [p]
      simp only [Complex.div_ofNat_re, Complex.one_re]
      linarith [(abs_lt.mp r.property.2).1]
    have hcoeff :=
      introTrace_window_order_eq_of_resolvent_eqOn χ a (1 / 2) ha le_rfl he p hp
    have hpr : p + 1 / 2 = r.val := sub_add_cancel _ _
    by_contra hne
    have hcast : (zeroOrder(χ, r.val) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr r.property.1.ne'
    simp only [hpr, r.property.1, r.property.2, hne, and_true, and_false, ite_true,
      ite_false] at hcoeff
    exact hcast hcoeff.symm
  · intro h z _
    let e : windowZeros(χ, a) ≃ windowZeros(χ, 1 / 2) :=
      { toFun := fun r ↦ ⟨r.val, r.property.1, r.property.2.trans_le ha⟩
        invFun := fun r ↦ ⟨r.val, r.property.1, h r⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact e.tsum_eq (fun r ↦ (zeroOrder(χ, r.val) : ℂ) *
      (1 / (z - (r.val - 1 / 2)) - 1 / (z + 2 - (r.val - 1 / 2))))

/-- Paper: §1.4.5, p. 30. For a fixed unitary character and half-width at most one half,
its shift-by-two resolvent agrees with the full critical-strip resolvent on the Euler
half-plane exactly when every completed zero lies strictly inside the narrower window.
Deviation: The comparison detects a zero on either boundary of the open window. -/
theorem introTrace_shiftTwo_resolvent_eqOn_iff_no_exterior_zeros (χ : U𝔽) (a : ℝ) (ha : a ≤ 1 / 2) :
    EqOn resolvent(χ, a) resolvent(χ, 1 / 2) right(1) ↔
      ∀ s : ℂ, 0 < zeroOrder(χ, s) → |s.re - 1 / 2| < a := by
  apply (introTrace_shiftTwo_resolvent_eqOn_iff_windows χ a ha).trans
  constructor
  · exact fun h s hs ↦ h ⟨s, hs, introTrace_positive_divisor_in_critical_strip χ s hs⟩
  · exact fun h r ↦ h r.val r.property.1

/-- Paper: §1.4.5, pp. 29–30. On a normalized chart of half-width at most
one half, the raw combined cutoff sums converge to the stated logarithmic
derivative on the Euler half-plane for every approximation family exactly when
every positive-order zero belongs to the open window. A boundary zero is excluded. -/
theorem introTrace_combined_overlap_iff_window_contains_all_zeros
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) :
    (∀ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ →
      TendstoLocallyUniformlyOn (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) +
        introTraceSpectralSum χ approx(h, ρ, n, z) a)
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) atTop right(1)) ↔
      ∀ s : ℂ, 0 < zeroOrder(χ, s) → |s.re - 1 / 2| < a := by
  constructor
  · intro hlim
    obtain ⟨h, ρ, hA, _, hs⟩ := introTraceApprox_exists_reference_spectral_matched (F := F)
    have hn := hlim h ρ hA
    have hf := introTrace_combined_limit_of_fixed_identity χ h ρ hA
      (introTraceApprox_full_window_fixed_digamma τ hτ χ hχ (a := 1 / 2) le_rfl h ρ hA)
    have hm : max (1 / 2 : ℝ) 1 = 1 := by norm_num
    rw [hm] at hf
    have hd (w : ℂ) (hw : 1 < w.re) : Tendsto (fun n ↦
        introTraceSpectralSum χ approx(h, ρ, n, w) a -
          introTraceSpectralSum χ approx(h, ρ, n, w) (1 / 2)) atTop (𝓝 0) := by
      convert (hn.tendsto_at hw).sub (hf.tendsto_at hw) using 1
      · funext n
        ring
      · simp
    apply (introTrace_shiftTwo_resolvent_eqOn_iff_no_exterior_zeros χ a ha').mp
    intro z hz
    have hz₁ : 1 < z.re := hz
    have hz₂ : 1 < (z + 2).re := by simpa using (show 1 < z.re + 2 by linarith)
    have shift (b : ℝ) : MapsTo (fun w : ℂ ↦ w + 2) right(b) right(b) := by
      intro w hw
      simpa using (show b < w.re + 2 by linarith [show b < w.re from hw])
    have ha₁ : a < z.re := by linarith
    have hh₁ : (1 / 2 : ℝ) < z.re := by linarith
    have h₁ := (hs χ a ha _ (shift a) (by fun_prop)).tendsto_at ha₁
    have h₂ := (hs χ (1 / 2) (by norm_num) _ (shift _) (by fun_prop)).tendsto_at hh₁
    apply sub_eq_zero.mp
    apply tendsto_nhds_unique (h₁.sub h₂)
    convert (hd z hz₁).sub (hd (z + 2) hz₂) using 1
    · funext n
      ring
    · simp
  · intro hall h ρ hA
    have hm : max a 1 = 1 := max_eq_right (by linarith)
    have hlim := introTrace_combined_limit_of_fixed_identity χ (a := a) h ρ hA (fun n z ↦ by
      rw [introTrace_spectral_sum_eq_unit_window_of_contains χ _ a hall]
      exact introTraceApprox_full_window_fixed_digamma τ hτ χ hχ (a := 1) (by norm_num) h ρ hA n z)
    simpa only [hm] using hlim

/-- Paper: §1.4.5, pp. 29–30. For a normalized character the combined cutoff
limit asserted on the Euler overlap, for every positive half-width and every
admissible approximation family, holds exactly when all positive-order zeros of
that character's completed L-function have real part one half. -/
theorem introTrace_combined_all_overlaps_iff_critical_line
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) :
    (∀ a : ℝ, 0 < a → ∀ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ →
      TendstoLocallyUniformlyOn (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) +
        introTraceSpectralSum χ approx(h, ρ, n, z) a)
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) atTop right(max a 1)) ↔
      ∀ s : ℂ, 0 < zeroOrder(χ, s) → s.re = 1 / 2 := by
  constructor
  · intro hlim s hs
    by_contra hne
    let a := |s.re - 1 / 2|
    have ha : 0 < a := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hb : a < 1 / 2 := introTrace_positive_divisor_in_critical_strip χ s hs
    have hm : max a 1 = 1 := max_eq_right (by linarith)
    have hw := (introTrace_combined_overlap_iff_window_contains_all_zeros τ hτ χ hχ ha.le hb.le).mp
      (by simpa only [hm] using hlim a ha)
    exact (lt_irrefl a) (hw s hs)
  · intro hcrit a ha h ρ hA
    by_cases hb : a ≤ 1 / 2
    · have hall (s : ℂ) (hs : 0 < zeroOrder(χ, s)) : |s.re - 1 / 2| < a := by
        simpa only [hcrit s hs, sub_self, abs_zero] using ha
      have hm : max a 1 = 1 := max_eq_right (by linarith)
      simpa only [hm] using
        (introTrace_combined_overlap_iff_window_contains_all_zeros τ hτ χ hχ ha.le hb).mpr hall h ρ hA
    · exact introTrace_combined_limit_of_fixed_identity χ h ρ hA
        (introTraceApprox_full_window_fixed_digamma τ hτ χ hχ (le_of_not_ge hb) h ρ hA)

/-- Paper: §§1.4.3–1.4.5, pp. 29–30. The difference between the full and narrow
resolvents is the sum over the omitted zeros on the Euler half-plane. Its meromorphic
continuation has residue equal to the omitted multiplicity at each point, including
zeros on the boundary of the open window. -/
theorem introTrace_shiftTwo_exterior_resolvent (χ : U𝔽) (a : ℝ) (ha : a ≤ 1 / 2) :
    let E := fun z : ℂ ↦ resolvent(χ, 1 / 2) z - resolvent(χ, a) z
    (∀ z : ℂ, 1 < z.re → HasSum
      (fun r : {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a} ↦
        (zeroOrder(χ, r.val.val) : ℂ) * poleKernel(r.val.val - 1 / 2, z)) (E z)) ∧
    MeromorphicOn E right(-1) ∧
    ∀ p : ℂ, -1 < p.re → Tendsto (fun z ↦ (z - p) * E z) (𝓝[≠] p)
      (𝓝 (if 0 < zeroOrder(χ, p + 1 / 2) ∧ ¬ |(p + 1 / 2).re - 1 / 2| < a
        then (zeroOrder(χ, p + 1 / 2) : ℂ) else 0)) := by
  intro E
  refine ⟨?_, (introTrace_window_resolvent_meromorphic χ (1 / 2) le_rfl).sub
    (introTrace_window_resolvent_meromorphic χ a ha), ?_⟩
  · intro z hz
    let t (r : windowZeros(χ, 1 / 2)) := (zeroOrder(χ, r.val) : ℂ) * poleKernel(r.val - 1 / 2, z)
    let I := {r : windowZeros(χ, 1 / 2) | |r.val.re - 1 / 2| < a}
    let e : I ≃ windowZeros(χ, a) :=
      { toFun := fun r ↦ ⟨r.val.val, r.val.property.1, r.property⟩
        invFun := fun r ↦ ⟨⟨r.val, r.property.1, r.property.2.trans_le ha⟩, r.property.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hshift : MapsTo (fun w : ℂ ↦ w + 2) right(1 / 2) right(1 / 2) := by
      intro w hw
      change (1 / 2 : ℝ) < (w + 2).re
      simpa using (show (1 / 2 : ℝ) < w.re + 2 by linarith [show (1 / 2 : ℝ) < w.re from hw])
    have ht : HasSum t (resolvent(χ, 1 / 2) z) :=
      (introTrace_spectral_referenceSub χ (1 / 2) _ hshift (by fun_prop)).2.2.1.tendsto_at
        (show z ∈ right(1 / 2) by change (1 / 2 : ℝ) < z.re; linarith)
    have hinner : (∑' r : I, t r.val) = resolvent(χ, a) z :=
      e.tsum_eq (fun r ↦ (zeroOrder(χ, r.val) : ℂ) * poleKernel(r.val - 1 / 2, z))
    have hsum := ht.summable.tsum_subtype_add_tsum_subtype_compl I
    rw [hinner, ht.tsum_eq] at hsum
    have he : (∑' r : {r : windowZeros(χ, 1 / 2) // r ∉ I}, t r.val) = E z := eq_sub_of_add_eq' hsum
    rw [← he]
    exact (ht.summable.subtype (fun r ↦ r ∉ I)).hasSum
  · intro p hp
    have h := (introTrace_window_resolvent_residue χ (1 / 2) le_rfl p hp).sub
      (introTrace_window_resolvent_residue χ a ha p hp)
    have hres : windowOrder(χ, 1 / 2, p) - windowOrder(χ, a, p) =
        if 0 < zeroOrder(χ, p + 1 / 2) ∧ ¬ |(p + 1 / 2).re - 1 / 2| < a
          then (zeroOrder(χ, p + 1 / 2) : ℂ) else 0 := by
      by_cases hpos : 0 < zeroOrder(χ, p + 1 / 2)
      · have hfull := introTrace_positive_divisor_in_critical_strip χ (p + 1 / 2) hpos
        by_cases hi : |(p + 1 / 2).re - 1 / 2| < a <;>
          simp only [hpos, hfull, hi, true_and, not_true_eq_false, not_false_eq_true,
            ite_true, ite_false, sub_self, sub_zero]
      · simp only [hpos, false_and, ite_false, sub_self]
    rw [← hres]
    simpa only [E, mul_sub] using h

/-- Paper: §1.4.5, p. 30. Agreement with the full shift-by-two resolvent on the Euler
half-plane for every positive half-width below one half is equivalent to the critical-line
condition for this character. -/
theorem introTrace_shiftTwo_all_windows_iff_critical_line (χ : U𝔽) :
    (∀ a : ℝ, 0 < a → a < 1 / 2 → EqOn resolvent(χ, a) resolvent(χ, 1 / 2) right(1)) ↔
      ∀ s : ℂ, 0 < zeroOrder(χ, s) → s.re = 1 / 2 := by
  constructor
  · intro h s hs
    by_contra hn
    let d := |s.re - 1 / 2|
    have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hn)
    have hd' : d < 1 / 2 := introTrace_positive_divisor_in_critical_strip χ s hs
    exact (lt_irrefl d) ((introTrace_shiftTwo_resolvent_eqOn_iff_no_exterior_zeros χ d hd'.le).mp
      (h d hd hd') s hs)
  · intro h a ha ha'
    apply (introTrace_shiftTwo_resolvent_eqOn_iff_no_exterior_zeros χ a ha'.le).mpr
    intro s hs
    simpa only [h s hs, sub_self, abs_zero] using ha

private theorem introTrace_shiftTwo_power_factor (z : ℂ) (t : ℝ) (ht : 0 < t) :
    introTracePower z t - introTracePower (z + 2) t =
      (introTracePower 0 t - introTracePower 2 t) * (t : ℂ) ^ (-z) := by
  by_cases h : 1 < t
  · have hn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    simp only [introTracePower, h, ite_true, neg_zero, Complex.cpow_zero]
    rw [show -(z + 2) = -z + (-2) by ring, Complex.cpow_add _ _ hn]
    ring
  · simp [introTracePower, h]

/-- The limiting subtracted archimedean integrals, with the corrected local
Tamagawa kernels, are analytic throughout their open half-plane of integrability. -/
private theorem introTrace_archimedean_sub_shiftTwo_analytic (χ : U𝔽) (v : InfinitePlace F) :
    AnalyticOnNhd ℂ
      (fun z ↦ introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z + 2) t) v)
      right(-(1 / 2 : ℝ)) := by
  classical
  let : MeasurableSpace v.Completion := instMeasurableSpaceCompletion_riemannMasullo F v
  let : BorelSpace v.Completion := ⟨rfl⟩
  let : BorelSpace v.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let N (u : v.Completionˣ) := ‖u.val‖ ^ v.mult
  have hN (u : v.Completionˣ) : 0 < N u := pow_pos (norm_pos_iff.mpr u.ne_zero) _
  have hNm : Measurable N := (continuous_norm.comp Units.continuous_val).measurable.pow_const _
  let P (z : ℂ) (t : ℝ) := introTracePower z t - introTracePower (z + 2) t
  let W (z : ℂ) := archIntegrand(χ, P z, v)
  have hf (z : ℂ) (u : v.Completionˣ) : W z u = W 0 u * (N u : ℂ) ^ (-z) := by
    have hnu : (((ideleClassNorm F) (IdeleClassGroup.ofCompletion (𝓞 F) F v u)).val : ℝ) = N u := by
      rw [ideleClassNorm_ofCompletion]; rfl
    dsimp only [W, introTraceTest, P]
    rw [hnu, introTrace_shiftTwo_power_factor z _ (hN u), zero_add]
    ring
  obtain ⟨h, ρ, hA⟩ := exists_introTraceApproximation
  obtain ⟨_, _, _, hall⟩ := introTraceApprox_archimedean_sub_shiftTwo_tendsto (F := F) h ρ hA
  have hint := (hall χ).1 v
  let μ := infiniteLocalMultiplicativeTamagawaMeasure F v
  have hI : AnalyticOnNhd ℂ (fun s : ℂ ↦ ∫ u, W 0 u * (N u : ℂ) ^ s ∂μ)
      (Complex.re ⁻¹' Iio (1 / 2: ℝ)) := by
    apply analyticOnNhd_integral_mul_cpow_of_integrable μ (W 0) N hNm hN isOpen_Iio
    intro s hs
    have hₛ : -s ∈ right(-(1 / 2 : ℝ)) := by change -(1 / 2 : ℝ) < (-s).re; simpa using neg_lt_neg hs
    apply (hint (-s) hₛ).congr
    exact .of_forall fun u ↦ by simpa only [neg_neg] using hf (-s) u
  intro z hz
  have hz' : -z ∈ Complex.re ⁻¹' Iio (1 / 2: ℝ) := by
    change (-z).re < 1 / 2
    simpa using neg_lt_neg (show -(1 / 2 : ℝ) < z.re from hz)
  have h := (hI (-z) hz').comp (show AnalyticAt ℂ (fun w : ℂ ↦ -w) z by fun_prop)
  have he : (fun w ↦ introTraceArchimedean χ (P w) v) =
      fun w ↦ (if v.IsReal then (1 / 2: ℂ) else 1 / (2 * (Real.pi: ℂ))) *
        (∫ u, W 0 u * (N u : ℂ) ^ (-w) ∂μ) := by
    funext w
    unfold introTraceArchimedean
    congr 1
    exact integral_congr_ae (.of_forall (hf w))
  change AnalyticAt ℂ (fun w ↦ introTraceArchimedean χ (P w) v) z
  rw [he]
  exact analyticAt_const.mul h

/-- The narrow resolvent, the regularized archimedean integrals, and the translated
Euler logarithmic derivative are analytic on the entire open chart. -/
private theorem introTrace_regularized_chart_analytic (χ : U𝔽) (a : ℝ) (ha : 0 ≤ a) :
    let L := fun z : ℂ ↦ logDeriv finiteL(χ) (z + 1 / 2) +
      if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0
    let R := resolvent(χ, a)
    let J := fun z : ℂ ↦ ∑ v : InfinitePlace F,
      introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z + 2) t) v
    AnalyticOnNhd ℂ (fun z ↦ R z + J z + L (z + 2)) right(a) := by
  classical
  intro L R J
  let f := (finiteHeckeL_exists_continuation (F := F) χ).choose
  have hshift : MapsTo (fun w : ℂ ↦ w + 2) right(a) right(a) := by
    intro w hw
    change a < (w + 2).re
    simpa using (show a < w.re + 2 by linarith [show a < w.re from hw])
  have hR : AnalyticOnNhd ℂ R right(a) := (introTrace_spectral_referenceSub χ a (fun w ↦ w + 2)
    hshift (by fun_prop)).2.2.2
  have hJ : AnalyticOnNhd ℂ J right(a) := by
    intro z hz
    apply Finset.analyticAt_fun_sum
    intro v _
    exact introTrace_archimedean_sub_shiftTwo_analytic χ v z (show -(1 / 2: ℝ) < z.re by
      linarith [show a < z.re from hz])
  have hL : AnalyticOnNhd ℂ (fun w ↦ L (w + 2)) right(a) := by
    intro z hz
    have hz₀ : 0 < z.re := ha.trans_lt hz
    let w := z + 2 + 1 / 2
    have hw : 1 < w.re := by dsimp [w]; norm_num; linarith
    have hnf : MeromorphicNFAt f w := (finiteHeckeL_exists_continuation χ).choose_spec.1 (mem_univ w)
    have hne : f w ≠ 0 := by
      rw [show f w = finiteHeckeL χ ⟨w, hw⟩ from (finiteHeckeL_exists_continuation χ).choose_spec.2 ⟨w, hw⟩]
      exact finiteHeckeL_ne_zero_of_one_lt_re χ _
    have ho := hnf.meromorphicOrderAt_eq_zero_iff.mpr hne
    have han := hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp ho.ge
    have hD : AnalyticAt ℂ (fun q : ℂ ↦ logDeriv f (q + 2 + 1 / 2)) z :=
      (han.deriv.div han hne).comp (f := fun q : ℂ ↦ q + 2 + 1 / 2) (x := z) (by fun_prop)
    have hp : z + 2 + 1 / 2 ≠ 0 := by intro e; have h := congrArg Complex.re e; norm_num at h; linarith
    have hm : z + 2 - 1 / 2 ≠ 0 := by intro e; have h := congrArg Complex.re e; norm_num at h; linarith
    apply hD.add
    split_ifs <;> fun_prop (disch := first | exact hp | exact hm)
  exact (hR.add hJ).add hL


/-- Paper: §§1.4.3–1.4.5, pp. 29–30. One matched cutoff family gives an analytic
regularization on every normalized narrow chart. On the Euler overlap the difference
between the polar-corrected logarithmic derivative and this analytic function is
exactly the exterior-zero resolvent. Its residues are given by
`introTrace_shiftTwo_exterior_resolvent`. -/
theorem introTrace_regularized_chart_with_exterior_zeros :
    ∃ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ ∧
    ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽), RightInverse τ (ideleClassNorm F) →
      ∀ (χ : U𝔽), (∀ t, χ (τ t) = 1) → ∀ a : ℝ, 0 ≤ a → a ≤ 1 / 2 →
      let L := fun z : ℂ ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0
      let J := fun z : ℂ ↦ ∑ v : InfinitePlace F,
        introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z + 2) t) v
      let H := fun z : ℂ ↦ resolvent(χ, a) z + J z + L (z + 2)
      let E := fun z : ℂ ↦ resolvent(χ, 1 / 2) z - resolvent(χ, a) z
      AnalyticOnNhd ℂ H right(a) ∧
      TendstoLocallyUniformlyOn (fun n z ↦
        introTraceSpectralSum χ approx(h, ρ, n, z) a - introTraceSpectralSum χ approx(h, ρ, n, (z + 2)) a +
        ((∑ v : InfinitePlace F, introTraceArchimedean χ approx(h, ρ, n, z) v) -
          ∑ v : InfinitePlace F, introTraceArchimedean χ approx(h, ρ, n, (z + 2)) v))
        (fun z ↦ resolvent(χ, a) z + J z) atTop right(a) ∧
      MeromorphicOn (H + E) right(a) ∧ EqOn (H + E) L right(1) ∧
      ∀ p ∈ right(a), Tendsto (fun z ↦ (z - p) * (H z + E z)) (𝓝[≠] p)
        (𝓝 (if 0 < zeroOrder(χ, p + 1 / 2) then (zeroOrder(χ, p + 1 / 2) : ℂ) else 0)) := by
  obtain ⟨h, ρ, hA, hmatch, hs⟩ := introTraceApprox_exists_reference_spectral_matched (F := F)
  refine ⟨h, ρ, hA, ?_⟩
  intro τ hτ χ hχ a ha ha' L J H E
  have hH : AnalyticOnNhd ℂ H right(a) := introTrace_regularized_chart_analytic χ a ha
  obtain ⟨_, hE, hres⟩ := introTrace_shiftTwo_exterior_resolvent χ a ha'
  have hsub : right(a) ⊆ right(-1) := fun z hz ↦ by
    change -1 < z.re
    linarith [show a < z.re from hz]
  refine ⟨hH, ?_, hH.meromorphicOn.add (hE.mono_set hsub), ?_, ?_⟩
  · have hshift : MapsTo (fun w : ℂ ↦ w + 2) right(a) right(a) := by
      intro w hw
      change a < (w + 2).re
      simpa using (show a < w.re + 2 by linarith [show a < w.re from hw])
    have harch := (introTraceApprox_archimedean_sub_shiftTwo_matched_sum χ h ρ hA hmatch).mono
      (show right(a) ⊆ right(-(1 / 2 : ℝ)) from fun w hw ↦ by
        change -(1 / 2 : ℝ) < w.re
        linarith [show a < w.re from hw])
    exact (hs χ a ha _ hshift (by fun_prop)).add harch
  · intro z hz
    have hz' : 1 < z.re := hz
    have hf := introTrace_shiftTwo_resolvent_eq_logDeriv_sub_archimedean τ hτ χ hχ
      (1 / 2) le_rfl z (max_lt (by linarith) hz')
    change resolvent(χ, 1 / 2) z = L z - L (z + 2) - J z at hf
    change (resolvent(χ, a) z + J z + L (z + 2)) + (resolvent(χ, 1 / 2) z - resolvent(χ, a) z) = L z
    rw [hf]
    ring
  · intro p hp
    have hlim : Tendsto (fun z ↦ (z - p) * H z) (𝓝[≠] p) (𝓝 0) := by
      have hc : ContinuousAt (fun z ↦ (z - p) * H z) p :=
        (continuousAt_id.sub continuousAt_const).mul (hH p hp).continuousAt
      simpa only [sub_self, zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hext : ¬ |(p + 1 / 2).re - 1 / 2| < a := by
      have hpr : a < p.re := hp
      rw [Complex.add_re]
      norm_num
      linarith [le_abs_self p.re]
    simpa only [mul_add, zero_add, hext, not_false_eq_true, and_true] using
      hlim.add (hres p (hsub hp))

private theorem introTrace_narrow_continuation_of_shiftTwo_comparison (χ : U𝔽) (a : ℝ) (ha : 0 ≤ a) :
    let L := fun z : ℂ ↦ logDeriv finiteL(χ) (z + 1 / 2) +
      if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0
    let R := resolvent(χ, a)
    let J := fun z : ℂ ↦ ∑ v : InfinitePlace F,
      introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z + 2) t) v
    (∀ z ∈ right(max a 1), R z = L z - L (z + 2) - J z) →
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧ EqOn H L right(max a 1) := by
  classical
  intro L R J hcmp
  refine ⟨fun z ↦ R z + J z + L (z + 2), introTrace_regularized_chart_analytic χ a ha, ?_⟩
  intro z hz
  change R z + J z + L (z + 2) = L z
  rw [hcmp z hz]
  ring

/-- Paper: §1.4.5, p. 30. For a character trivial on the norm section and a half-width
in `[0, 1/2)`, comparison of the narrow and full resolvents on the Euler
half-plane gives the claimed continuation of the polar-corrected logarithmic derivative.
The continuation is the sum of the narrow resolvent, the regularized archimedean
contribution, and the polar-corrected logarithmic derivative at the translated parameter.
The full-window identity follows from the one-character explicit formula. -/
theorem introTrace_narrow_continuation_of_full_resolvent_comparison
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 F) F) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (a : ℝ) (ha : 0 ≤ a) (ha' : a < 1 / 2) :
    EqOn resolvent(χ, a) resolvent(χ, 1 / 2) right(1) →
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧ EqOn H
      (fun z : ℂ ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1) := by
  intro heq
  apply introTrace_narrow_continuation_of_shiftTwo_comparison χ a ha
  intro z hz
  have hmax : max a 1 = 1 := max_eq_right (by linarith)
  change max a 1 < z.re at hz
  rw [hmax] at hz
  have hz₁ : 1 < z.re := hz
  exact (heq hz₁).trans (introTrace_shiftTwo_resolvent_eq_logDeriv_sub_archimedean
    τ hτ χ hχ (1 / 2) le_rfl z (max_lt (by linarith) hz₁))

private theorem introTraceApprox_cutoff_omitted_sum (χ : U𝔽) (a : ℝ) (ha : a ≤ 1 / 2)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    introTraceSpectralSum χ approx(h, ρ, n, z) a +
      ∑' r : {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a},
        (zeroOrder(χ, r.val.val) : ℂ) *
        introTraceMellin approx(h, ρ, n, z) (r.val.val - 1 / 2) =
      introTraceSpectralSum χ approx(h, ρ, n, z) (1 / 2) := by
  let t (r : windowZeros(χ, 1 / 2)) := (zeroOrder(χ, r.val) : ℂ) *
    introTraceMellin approx(h, ρ, n, z) (r.val - 1 / 2)
  let I := {r : windowZeros(χ, 1 / 2) | |r.val.re - 1 / 2| < a}
  let e : I ≃ windowZeros(χ, a) :=
    { toFun := fun r ↦ ⟨r.val.val, r.val.property.1, r.property⟩
      invFun := fun r ↦ ⟨⟨r.val, r.property.1, r.property.2.trans_le ha⟩, r.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hinner : (∑' r : I, t r.val) = introTraceSpectralSum χ approx(h, ρ, n, z) a :=
    e.tsum_eq (fun r : windowZeros(χ, a) ↦ (zeroOrder(χ, r.val) : ℂ) *
      introTraceMellin approx(h, ρ, n, z) (r.val - 1 / 2))
  have hsum : Summable t := introTraceApprox_spectral_summable χ h ρ hA n _ (by norm_num) z
  exact hinner ▸ hsum.tsum_subtype_add_tsum_subtype_compl I

private theorem introTraceApprox_finite_omitted_limit (χ : U𝔽) (a : ℝ)
    [Finite {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a}]
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) :
    TendstoLocallyUniformlyOn (fun n z ↦ ∑' r : {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a},
        (zeroOrder(χ, r.val.val) : ℂ) *
        introTraceMellin approx(h, ρ, n, z) (r.val.val - 1 / 2))
      (fun z ↦ ∑' r : {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a},
        (zeroOrder(χ, r.val.val) : ℂ) / (z - (r.val.val - 1 / 2)))
      atTop right(1) := by
  let E := {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a}
  let _ := Fintype.ofFinite E
  let m (r : E) := (zeroOrder(χ, r.val.val) : ℂ)
  let p (r : E) := r.val.val - 1 / 2
  have ht (r : E) : (p r).re < 1 := by
    have hh := (abs_lt.mp r.val.property.2).2
    dsimp [p]
    simp only [Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hr (r : E) : TendstoLocallyUniformlyOn (fun n z ↦ m r * introTraceMellin approx(h, ρ, n, z) (p r))
      (fun z ↦ m r / (z - p r)) atTop right(1) := by
    have hsub : right(1) ⊆ right((p r).re) := fun z hz ↦ (ht r).trans hz
    have H := (introTraceApprox_mellin_tendsto h ρ hA (p r)).mono hsub
    have hc : UniformContinuous (fun w : ℂ ↦ m r * w) := uniformContinuous_const_smul (m r)
    apply (hc.comp_tendstoLocallyUniformlyOn H).congr_right
    intro z hz
    simp only [comp_apply, (introTracePower_mellin z (p r) (hsub hz)).2, div_eq_mul_inv, one_mul]
  suffices H : ∀ S : Finset E, TendstoLocallyUniformlyOn
      (fun n z ↦ ∑ r ∈ S, m r * introTraceMellin approx(h, ρ, n, z) (p r))
      (fun z ↦ ∑ r ∈ S, m r / (z - p r)) atTop right(1) by
    simpa only [tsum_fintype] using H Finset.univ
  intro S
  induction S using Finset.induction_on with
  | empty =>
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0)
      ).tendstoUniformlyOn_const (s := right(1))).tendstoLocallyUniformlyOn
  | insert r S hrs ih =>
    refine (((hr r).add ih).congr (fun n z _ ↦ ?_)).congr_right (fun z _ ↦ ?_)
    · simp only [Finset.sum_insert hrs, Pi.add_apply]
    · simp only [Finset.sum_insert hrs, Pi.add_apply]

/-- Paper: §§1.4.3–1.4.5, pp. 29–30. If only finitely many positive-order zeros
are omitted by a narrow window, the combined cutoff sums have a holomorphic limit
for every approximation family. On the Euler half-plane its value is the
polar-corrected logarithmic derivative minus the finite sum of the omitted poles. -/
theorem introTrace_combined_limit_of_finite_exterior_zeros
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1)
    (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ 1 / 2)
    [Finite {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a}] :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧
      EqOn H (fun z ↦ (logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) -
          ∑' r : {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a},
        (zeroOrder(χ, r.val.val) : ℂ) / (z - (r.val.val - 1 / 2))) right(1) ∧
      ∀ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ → TendstoLocallyUniformlyOn
        (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a)
        H atTop right(max a 1) := by
  let E := {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a}
  let _ := Fintype.ofFinite E
  let m (r : E) := (zeroOrder(χ, r.val.val) : ℂ)
  let p (r : E) := r.val.val - 1 / 2
  let tailSum (z : ℂ) := ∑ r : E, m r / (z - p r)
  let shiftedTail (z : ℂ) := ∑ r : E, m r / (z + 2 - p r)
  let L (z : ℂ) := logDeriv finiteL(χ) (z + 1 / 2) + if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0
  let J (z : ℂ) := ∑ v : InfinitePlace F, introTraceArchimedean χ (fun t ↦ introTracePower z t - introTracePower (z+2) t) v
  let H₀ (z : ℂ) := resolvent(χ, a) z + J z + L (z+2)
  have hV : AnalyticOnNhd ℂ shiftedTail right(a) := by
    intro z hz
    apply Finset.analyticAt_fun_sum
    intro r _
    have hr := (abs_lt.mp r.val.property.2).2
    have hpr : (p r).re < 1 := by
      dsimp [p]
      simp only [Complex.div_ofNat_re, Complex.one_re]
      linarith
    have hne : z + 2 - p r ≠ 0 := by
      intro e
      have he := congrArg Complex.re e
      change z.re + 2 - (p r).re = 0 at he
      linarith [show a < z.re from hz]
    exact analyticAt_const.div (by fun_prop) hne
  have hH : AnalyticOnNhd ℂ H₀ right(a) := introTrace_regularized_chart_analytic χ a ha
  have heuler (z : ℂ) (hz : 1 < z.re) : H₀ z - shiftedTail z = L z - tailSum z := by
    have hR := introTrace_shiftTwo_resolvent_eq_logDeriv_sub_archimedean τ hτ χ hχ
      (1 / 2) le_rfl z (max_lt (by linarith) hz)
    change resolvent(χ, 1 / 2) z = L z - L (z+2) - J z at hR
    have hE := ((introTrace_shiftTwo_exterior_resolvent χ a hb).1 z hz).tsum_eq
    have he : resolvent(χ, 1 / 2) z - resolvent(χ, a) z = tailSum z - shiftedTail z := by
      refine hE.symm.trans ?_
      rw [tsum_fintype, show tailSum z - shiftedTail z = ∑ r : E, (m r / (z - p r) - m r / (z+2 - p r)) by
        simp only [tailSum, shiftedTail, Finset.sum_sub_distrib]]
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [m, p]
      ring
    dsimp only [H₀]
    linear_combination hR - he
  refine ⟨fun z ↦ H₀ z - shiftedTail z, hH.sub hV, ?_, ?_⟩
  · intro z hz
    simpa only [tsum_fintype] using heuler z hz
  · intro h ρ hA
    have hm : max a 1 = 1 := max_eq_right (by linarith)
    rw [hm]
    have hf := (introTrace_combined_overlap_iff_window_contains_all_zeros τ hτ χ hχ
      (a := 1/2) (by norm_num) le_rfl).mpr (introTrace_positive_divisor_in_critical_strip χ) h ρ hA
    have hx := introTraceApprox_finite_omitted_limit χ a h ρ hA
    refine ((hf.sub hx).congr (fun n ↦ ?_)).congr_right (fun z hz ↦ ?_)
    · intro z _
      change (archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) (1/2)) - _ = _
      rw [← introTraceApprox_cutoff_omitted_sum χ a hb h ρ hA n z]
      ring
    · simpa only [Pi.sub_apply, tsum_fintype] using (heuler z hz).symm

/-- Paper: §1.4.5, p. 30. With finitely many but at least one omitted zero,
no approximation family converges to the polar-corrected logarithmic derivative
at any individual point of the Euler half-plane. Each omitted pole contributes
a strictly positive real part to the discrepancy. -/
theorem introTrace_no_pointwise_overlap_of_finite_exterior_zero
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ 1 / 2)
    [Finite {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a}]
    [Nonempty {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a}]
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) (z : ℂ) (hz : 1 < z.re) :
    ¬ Tendsto (fun n ↦ archSum(χ, approx(h, ρ, n, z)) +
      introTraceSpectralSum χ approx(h, ρ, n, z) a) atTop
        (𝓝 (logDeriv finiteL(χ) (z + 1 / 2) +
          if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0)) := by
  let E := {r : windowZeros(χ, 1 / 2) // ¬ |r.val.re - 1 / 2| < a}
  let _ := Fintype.ofFinite E
  obtain ⟨H, _, hEq, hlim⟩ := introTrace_combined_limit_of_finite_exterior_zeros τ hτ χ hχ a ha hb
  intro hclaimed
  have hactual := (hlim h ρ hA).tendsto_at (a := z) (max_lt (by linarith) hz)
  have he := (hEq hz).symm.trans (tendsto_nhds_unique hactual hclaimed)
  have hzero : (∑ r : E, (zeroOrder(χ, r.val.val) : ℂ) /
      (z - (r.val.val - 1 / 2))) = 0 := by
    simpa only [sub_eq_self, tsum_fintype] using he
  have hpos : 0 < (∑ r : E, (zeroOrder(χ, r.val.val) : ℂ) /
      (z - (r.val.val - 1 / 2))).re := by
    rw [Complex.re_sum]
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro r _
    have hden : 0 < (z - (r.val.val - 1 / 2)).re := by
      have hright := (abs_lt.mp r.val.property.2).2
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
      linarith
    have hne : z - (r.val.val - 1 / 2) ≠ 0 := fun e ↦ hden.ne' (congrArg Complex.re e)
    have hmult : 0 < (zeroOrder(χ, r.val.val) : ℝ) := by exact_mod_cast r.val.property.1
    simp only [Complex.div_re, Complex.intCast_re, Complex.intCast_im, zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos hmult hden) (Complex.normSq_pos.mpr hne)
  exact hpos.ne' (congrArg Complex.re hzero)

end WindowResolvents

open Classical in
/-- Chapter 12's cancellation for every test makes the exterior zero set empty.
The one-character full-window formula then gives the cutoff limit for every family. -/
private theorem introTrace_combined_overlap_of_exterior_cancellation (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1)
    {a : ℝ} (ha : 0 < a) (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) :
    TendstoLocallyUniformlyOn (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) +
      introTraceSpectralSum χ approx(h, ρ, n, z) a)
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) atTop right(max a 1) := by
  have hempty := isEmpty_exteriorZeros_of_hasSum τ hτ a
    (fun φ hφ ↦ traceFormula_exteriorZeros τ hτ φ hφ ha)
  have hall (s : ℂ) (hs : 0 < zeroOrder(χ, s)) : |s.re - 1 / 2| < a := by
    by_contra! hout
    exact hempty.false ⟨(⟨χ, hχ⟩, s), hs, hout⟩
  apply introTrace_combined_limit_of_fixed_identity χ h ρ hA
  intro n z
  rw [introTrace_spectral_sum_eq_unit_window_of_contains χ _ a hall]
  exact introTraceApprox_full_window_fixed_digamma τ hτ χ hχ (a := 1) (by norm_num) h ρ hA n z

open Classical in
/-- Paper: §1.4.5, p. 30. The extension the paper asserts without proof: the
germ of the regularized shifted logarithmic derivative extends holomorphically
from the overlap `Re z > max a 1` to the whole chart `Re z > a`. Away from the
trivial character this says that the finite Hecke L-function has no zero with
`Re s > 1 / 2 + a`, which is the content of the paper's continuation step. At
the trivial character's `z = 1 / 2` it says only that the two poles cancel as
a germ: the value of the raw expression at that point depends on the total
values Lean assigns to `logDeriv` at the pole of `finiteL 1` at one and to
`1/0`, so the extension is stated as a function agreeing on the overlap rather
than as `AnalyticOnNhd` of the raw expression itself. The character is trivial
on the norm section, as in the chart: a norm twist of the trivial character
moves the pole of its finite L-function off the real axis, where the
correction term does not cancel it.

Subtracting the cutoff terms at `z+2` gives convergent spectral and archimedean
differences for the same matched family. The overlap identity used to identify
their sum depends on `traceFormula_exteriorZeros`. -/
private theorem introTrace_combined_limit_extension_analytic (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    {a : ℝ} (_ha : 0 < a) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧
      EqOn H (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1) := by
  obtain ⟨h, ρ, hA, hmatch, hspec⟩ := introTraceApprox_exists_reference_spectral_matched (F := F)
  have hshift : MapsTo (fun z : ℂ ↦ z + 2) right(a) right(a) := by
    intro z hz
    change a < z.re + 2
    linarith [show a < z.re from hz]
  have hs := hspec χ a _ha.le _ hshift (by fun_prop)
  have harch := introTraceApprox_archimedean_sub_shiftTwo_matched_sum χ h ρ hA hmatch
  have hc := introTrace_combined_overlap_of_exterior_cancellation τ _hτ χ _hχ _ha h ρ hA
  apply introTrace_narrow_continuation_of_shiftTwo_comparison χ a _ha.le
  intro z hz
  have hzₐ : a < z.re := (le_max_left a 1).trans_lt hz
  have hz' : z + 2 ∈ right(max a 1) := by
    change max a 1 < z.re + 2
    linarith [show max a 1 < z.re from hz]
  have hzarch : z ∈ right(-(1 / 2 : ℝ)) := by
    change -(1 / 2 : ℝ) < z.re
    linarith
  apply tendsto_nhds_unique (hs.tendsto_at (a := z) hzₐ)
  apply (((hc.tendsto_at hz).sub (hc.tendsto_at hz')).sub (harch.tendsto_at hzarch)).congr
  intro n
  ring

/-- Paper: §1.4.5, pp. 29–30. In each normalized chart a holomorphic function
on the right of the window agrees on the common half-plane with the limit of
the combined archimedean and spectral terms for a cofinal family of tests.
Gap: The separate limits on p. 29 diverge for the trivial rational character.
The paper gives no extension of the combined value across the overlap.
Deviation: Only the restriction of the extension to the overlap must be a
cutoff limit. One cofinal family for each chart and width suffices.
Split: the overlap limit is `introTrace_combined_limit_extension_overlap`, and
the extension across the overlap is `introTrace_combined_limit_extension_analytic`. -/
theorem introTrace_combined_limit_extension (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    (a : ℝ) (_ha : 0 < a) :
    ∃ (h ρ : ℕ → ℝ → ℝ) (H : ℂ → ℂ), IsIntroTraceApproximation h ρ ∧
      AnalyticOnNhd ℂ H right(a) ∧ TendstoLocallyUniformlyOn
        (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a)
        H atTop right(max a 1) := by
  obtain ⟨h, ρ, hA⟩ := exists_introTraceApproximation
  obtain ⟨H, hH, hEq⟩ := introTrace_combined_limit_extension_analytic τ _hτ χ _hχ _ha
  refine ⟨h, ρ, H, hA, hH, ?_⟩
  exact (introTrace_combined_overlap_of_exterior_cancellation τ _hτ χ _hχ _ha h ρ hA).congr_right
    fun z hz ↦ (hEq hz).symm

/-- A normalized meromorphic function admits a holomorphic continuation of its logarithmic
derivative from a right half-plane exactly when its divisor vanishes in the larger half-plane. -/
private theorem introTrace_logDeriv_extension_iff_order (a : ℝ) (g D : ℂ → ℂ)
    (hg : MeromorphicNFOn g univ) (hfin : ∀ z, meromorphicOrderAt g z ≠ ⊤)
    (heq : EqOn (logDeriv g) D right(max a 1)) :
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧ EqOn H D right(max a 1)) ↔
      ∀ z ∈ right(a), meromorphicOrderAt g z = 0 := by
  constructor
  · rintro ⟨H, hH, hD⟩ z hz
    have hlog : MeromorphicOn (logDeriv g) right(a) := fun w _ ↦ (hg (mem_univ w)).meromorphicAt.logDeriv
    have hm := hlog.sub hH.meromorphicOn
    let q : ℂ := (max a 1 + 1 : ℝ)
    have hq : max a 1 < q.re := by simp [q]
    have hb : meromorphicOrderAt (logDeriv g - H) q = ⊤ := by
      apply meromorphicOrderAt_eq_top_iff.mpr
      have hnear := Complex.continuous_re.continuousAt.eventually (eventually_gt_nhds hq)
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with w hw
      exact sub_eq_zero.mpr ((heq hw).trans (hD hw).symm)
    have h := hm.meromorphicOrderAt_eq_top_of_isPreconnected (convex_halfSpace_re_gt _).isPreconnected
      ((le_max_left _ _).trans_lt hq) hz hb
    have hnear : logDeriv g =ᶠ[𝓝[≠] z] H := (meromorphicOrderAt_eq_top_iff.mp h).mono fun w hw ↦ sub_eq_zero.mp hw
    have hn : 0 ≤ meromorphicOrderAt (logDeriv g) z := (meromorphicOrderAt_congr hnear).symm ▸ (hH z hz).meromorphicOrderAt_nonneg
    by_contra hzero
    rw [meromorphicOrderAt_logDeriv_eq_neg_one hzero (hfin z)] at hn
    exact (by decide : ¬ (0 : WithTop ℤ) ≤ -1) hn
  · intro h
    refine ⟨logDeriv g, fun z hz ↦ ?_, heq⟩
    have hnf := hg (mem_univ z)
    have ho := h z hz
    have ha := hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp ho.ge
    exact ha.deriv.div ha (hnf.meromorphicOrderAt_eq_zero_iff.mp ho)

/-- The polar factors have order one at the exceptional point of the trivial chart and
order zero everywhere else in the right half-plane. -/
private theorem introTrace_polar_factor_order (c : Prop) [Decidable c] (z : ℂ) (hz : 0 < z.re)
    (k : WithTop ℤ) :
    meromorphicOrderAt (if c then fun w : ℂ ↦ (w + 1 / 2) * (w - 1 / 2) else fun _ ↦ 1) z + k = 0 ↔
      k = if c ∧ z + 1 / 2 = 1 then -1 else 0 := by
  by_cases hχ : c
  · simp only [hχ, ite_true, true_and]
    have hp : z + 1 / 2 ≠ 0 := by intro he; have := congrArg Complex.re he; norm_num at this; linarith
    have hleft : meromorphicOrderAt (fun w : ℂ ↦ w + 1 / 2) z = 0 :=
      (show AnalyticAt ℂ (fun w : ℂ ↦ w + 1 / 2) z by fun_prop).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hp
    have hpord := meromorphicOrderAt_mul
      (show MeromorphicAt (fun w : ℂ ↦ w + 1 / 2) z by fun_prop)
      (show MeromorphicAt (fun w : ℂ ↦ w - 1 / 2) z by fun_prop)
    rw [show meromorphicOrderAt (fun w : ℂ ↦ (w + 1 / 2) * (w - 1 / 2)) z = _ from hpord, hleft, zero_add]
    by_cases h : z = 1 / 2
    · subst z
      rw [meromorphicOrderAt_id_sub_const, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, ite_eq_left rfl]
      cases k with
      | top =>
        change (1 + (⊤ : WithTop ℤ) = 0) ↔ (⊤ : WithTop ℤ) = ↑(-1 : ℤ)
        exact iff_of_false (by simp) WithTop.top_ne_coe
      | coe n =>
        change ((↑(1 : ℤ) : WithTop ℤ) + ↑n = ↑(0 : ℤ)) ↔ (↑n : WithTop ℤ) = ↑(-1 : ℤ)
        rw [← WithTop.coe_add, WithTop.coe_inj, WithTop.coe_inj]
        omega
    · have hn : z + 1 / 2 ≠ 1 := by intro he; apply h; linear_combination he
      have hr : meromorphicOrderAt (fun w : ℂ ↦ w - 1 / 2) z = 0 :=
        (show AnalyticAt ℂ (fun w : ℂ ↦ w - 1 / 2) z by fun_prop).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (sub_ne_zero.mpr h)
      simp only [hr, zero_add, ite_eq_right hn]
  · have hc : meromorphicOrderAt (fun _ : ℂ ↦ (1 : ℂ)) z = 0 :=
      analyticAt_const.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr one_ne_zero
    simp only [hχ, ite_false, false_and, hc, zero_add]

open Classical in
/-- Paper: §1.4.5, p. 30. At any fixed half-width the claimed continuation exists precisely
when the finite Hecke function has order zero to the right of the corresponding line, apart
from the simple pole canceled by the correction in the trivial chart. -/
theorem introTrace_continuation_iff_finiteL_orders (χ : U𝔽) (a : ℝ) (ha : 0 ≤ a) :
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧ EqOn H
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1)) ↔
      ∀ s : ℂ, a + 1 / 2 < s.re → meromorphicOrderAt finiteL(χ) s =
        if χ = 1 ∧ s = 1 then -1 else 0 := by
  classical
  let L := finiteL(χ)
  let S : ℂ → ℂ := fun z ↦ L (z + 1 / 2)
  let P : ℂ → ℂ := if χ = 1 then fun z ↦ (z + 1 / 2) * (z - 1 / 2) else fun _ ↦ 1
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hS : Meromorphic S := fun z ↦ meromorphicAt_comp_add_const_iff_meromorphicAt.mpr (hL.1 (mem_univ _)).meromorphicAt
  have hP (z : ℂ) : AnalyticAt ℂ P z := by dsimp only [P]; split_ifs <;> fun_prop
  let f := P * S
  have hf : MeromorphicOn f univ := fun z _ ↦ (hP z).meromorphicAt.mul (hS z)
  let g := toMeromorphicNFOn f univ
  have hg : MeromorphicNFOn g univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have heuler (z : ℂ) (hz : 1 < z.re) : AnalyticAt ℂ S z ∧ S z ≠ 0 ∧ P z ≠ 0 := by
    have hw : 1 < (z + 1 / 2).re := by norm_num; linarith
    have hne : L (z + 1 / 2) ≠ 0 := by
      rw [show L (z + 1 / 2) = finiteHeckeL χ ⟨_, hw⟩ from hL.2 ⟨_, hw⟩]
      exact finiteHeckeL_ne_zero_of_one_lt_re χ _
    have H := hL.1 (mem_univ (z + 1 / 2))
    have haL := H.meromorphicOrderAt_nonneg_iff_analyticAt.mp (H.meromorphicOrderAt_eq_zero_iff.mpr hne).ge
    refine ⟨haL.comp (f := fun w : ℂ ↦ w + 1 / 2) (x := z) (by fun_prop), hne, ?_⟩
    dsimp only [P]; split_ifs
    · apply mul_ne_zero <;> intro h <;> have he := congrArg Complex.re h <;> norm_num at he <;> linarith
    · exact one_ne_zero
  have hgf (z : ℂ) (hz : 1 < z.re) : g =ᶠ[𝓝 z] f := by
    have hnear := Complex.continuous_re.continuousAt.eventually (eventually_gt_nhds hz)
    filter_upwards [hnear] with w hw
    exact (toMeromorphicNFOn_eq_toMeromorphicNFAt hf (mem_univ w)).trans
      (congrFun (toMeromorphicNFAt_eq_self.mpr ((hP w).mul (heuler w hw).1).meromorphicNFAt) w)
  have hfinite (z : ℂ) : meromorphicOrderAt g z ≠ ⊤ := by
    apply hg.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := 2) (mem_univ _) (mem_univ z)
    have h := heuler 2 (by norm_num)
    have hne : g 2 ≠ 0 := (hgf 2 (by norm_num)).eq_of_nhds ▸ mul_ne_zero h.2.2 h.2.1
    rw [(hg (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr hne]
    exact WithTop.zero_ne_top
  have hEq : EqOn (logDeriv g) (fun z ↦ logDeriv L (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1) := by
    intro z hz
    have hz' : 1 < z.re := (le_max_right _ _).trans_lt hz
    have h := heuler z hz'
    have hf' := hgf z hz'
    calc logDeriv g z = logDeriv f z := by simp only [logDeriv_apply, hf'.deriv_eq, hf'.eq_of_nhds]
         _ = logDeriv P z + logDeriv S z := logDeriv_mul z h.2.2 h.2.1 (hP z).differentiableAt h.1.differentiableAt
         _ = _ := by
           have hs : logDeriv S z = logDeriv L (z + 1 / 2) := by simp [S, logDeriv_apply, deriv_comp_add_const]
           rw [hs, add_comm]; congr 1
           dsimp only [P]; split_ifs
           · have h₁ : z + 1 / 2 ≠ 0 := by intro he; have := congrArg Complex.re he; norm_num at this; linarith
             have h₂ : z - 1 / 2 ≠ 0 := by intro he; have := congrArg Complex.re he; norm_num at this; linarith
             rw [logDeriv_fun_mul z h₁ h₂ (by fun_prop) (by fun_prop)]
             simp [logDeriv_apply]
           · simp [logDeriv_apply]
  rw [introTrace_logDeriv_extension_iff_order a g _ hg hfinite hEq]
  have hord (z : ℂ) (hz : a < z.re) : meromorphicOrderAt g z = 0 ↔
      meromorphicOrderAt L (z + 1 / 2) = if χ = 1 ∧ z + 1 / 2 = 1 then -1 else 0 := by
    rw [show meromorphicOrderAt g z = meromorphicOrderAt f z from meromorphicOrderAt_toMeromorphicNFOn hf (mem_univ z),
      show meromorphicOrderAt f z = meromorphicOrderAt P z + meromorphicOrderAt S z from meromorphicOrderAt_mul (hP z).meromorphicAt (hS z),
      show meromorphicOrderAt S z = meromorphicOrderAt L (z + 1 / 2) from meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
    exact introTrace_polar_factor_order (χ = 1) z (ha.trans_lt hz) _
  constructor
  · intro h s hs
    have hz : a < (s - 1 / 2).re := by norm_num; linarith
    change meromorphicOrderAt L s = _
    simpa only [sub_add_cancel] using (hord _ hz).mp (h _ hz)
  · intro h z hz
    apply (hord _ hz).mpr
    apply h
    change a < z.re at hz
    norm_num; linarith


open Classical in
/-- Paper: §1.4.5, p. 30. If the half-width is at least one half, the proposed
continuation holds for every unitary character by nonvanishing on the Euler half-plane. -/
theorem introTrace_continuation_of_half_le (χ : U𝔽) {a : ℝ} (ha : 1 / 2 ≤ a) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧ EqOn H
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1) := by
  classical
  apply (introTrace_continuation_iff_finiteL_orders χ a (by linarith)).mpr
  intro s hs
  have hre : 1 < s.re := by linarith
  have hn : ¬(χ = 1 ∧ s = 1) := fun h ↦ (lt_irrefl (1 : ℝ)) (by simpa [h.2] using hre)
  rw [ite_eq_right hn]
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  apply (hL.1 (mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr
  rw [show finiteL(χ) s = finiteHeckeL χ ⟨s, hre⟩ from hL.2 ⟨s, hre⟩]
  exact finiteHeckeL_ne_zero_of_one_lt_re χ _

/-- On the positive half-plane the reciprocal gamma factor is regular and nonzero. -/
private theorem introTrace_normalized_finite_order_eq_completed (χ : U𝔽) (s : ℂ) (hs : 0 < s.re) :
    meromorphicOrderAt finiteL(χ) s = meromorphicOrderAt (continuedCompletedHeckeL χ) s := by
  let L := continuedCompletedHeckeL χ
  let G (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  have hG := differentiable_inv_heckeGammaFactor χ
  have hL := continuedCompletedHeckeL_spec χ
  have hF := (finiteHeckeL_exists_continuation χ).choose_spec
  have hm : MeromorphicOn (fun z ↦ G z * L z) univ := fun z hz ↦
    (hG.analyticAt z).meromorphicAt.mul (hL.1 hz).meromorphicAt
  have he (z : ℂ) (hz : 1 < z.re) : finiteL(χ) z = G z * L z := by
    rw [hF.2 ⟨z, hz⟩, show L z = completedHeckeL χ ⟨z, hz⟩ from hL.2 ⟨z, hz⟩]
    exact (inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)) _).symm
  have hU : ∀ᶠ z : ℂ in 𝓝 2, 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have htop : meromorphicOrderAt (finiteL(χ) - fun z ↦ G z * L z) 2 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (eventuallyEq_iff_sub.mp
      ((hU.mono he).filter_mono nhdsWithin_le_nhds))
  have ht := (hF.1.meromorphicOn.sub hm).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) htop
  have hlocal : finiteL(χ) =ᶠ[𝓝[≠] s] (fun z ↦ G z * L z) :=
    eventuallyEq_iff_sub.mpr (meromorphicOrderAt_eq_top_iff.mp ht)
  rw [meromorphicOrderAt_congr hlocal]
  exact meromorphicOrderAt_mul_of_ne_zero (hG.analyticAt s)
    (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hs))

/-- A nontrivial chart representative must already be nontrivial on the norm-one classes. -/
private theorem introTrace_normalized_nontrivial_on_kernel
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (hn : χ ≠ 1) :
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 := by
  intro he
  apply hn
  ext1 g
  let u := g / τ (ideleClassNorm F g)
  have hu : u ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (g / τ _) = 1
    rw [map_div, hτ, div_self']
  have hc := DFunLike.congr_fun he (⟨u, hu⟩ : (ideleClassNorm F).ker)
  change χ u = 1 at hc
  dsimp [u] at hc
  rwa [map_div, hχ, div_one] at hc

/-- The unshifted pole of the completed trivial character has order minus one. -/
private theorem introTrace_normalized_trivial_order_one :
    meromorphicOrderAt (continuedCompletedHeckeL (F := F) 1) 1 = -1 := by
  let χ : U𝔽 := 1
  let L := continuedCompletedHeckeL χ
  have hL := continuedCompletedHeckeL_spec χ
  obtain ⟨t, ⟨_, ho₀, ho₁, _⟩, _⟩ := completedHeckeL_continuation_simplePoles χ L hL.1 hL.2
    (by ext; rfl)
  have ht : Complex.I * (t : ℂ) = 0 := by
    by_contra hne
    have hne' : Complex.I * (t : ℂ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp [Complex.mul_re] at this
    have hmem : Complex.I * (t : ℂ) ∈ ({0, 1}ᶜ : Set ℂ) := by simpa using And.intro hne hne'
    have hnn := (completedHeckeL_one_analyticOnNhd (F := F) L hL.1 hL.2 _ hmem).meromorphicOrderAt_nonneg
    rw [ho₀] at hnn
    exact (WithTop.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by decide)).not_ge hnn
  simpa [ht] using ho₁

/-- Away from the unshifted trivial pole, a chart character has no poles in the positive half-plane. -/
private theorem introTrace_normalized_completed_order_nonneg
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (s : ℂ) (hs : 0 < s.re) (hn : ¬(χ = 1 ∧ s = 1)) :
    0 ≤ meromorphicOrderAt (continuedCompletedHeckeL χ) s := by
  have hL := continuedCompletedHeckeL_spec χ
  by_cases h : χ = 1
  · subst χ
    have h₀ : s ≠ 0 := fun h ↦ (ne_of_gt hs) (by rw [h]; rfl)
    have h₁ : s ≠ 1 := fun h ↦ hn ⟨rfl, h⟩
    exact (completedHeckeL_one_analyticOnNhd (F := F) _ hL.1 hL.2 s
      (by simpa using And.intro h₀ h₁)).meromorphicOrderAt_nonneg
  · exact ((completedHeckeL_continuation_entire χ _ hL.1 hL.2
      (introTrace_normalized_nontrivial_on_kernel τ hτ χ hχ h)).analyticAt s).meromorphicOrderAt_nonneg

open Classical in
/-- Paper: §1.4.5, p. 30. In a normalized chart, fixed-width continuation is equivalent to
absence of completed zeros strictly to the right of the window. -/
theorem introTrace_normalized_continuation_iff_no_right_zeros
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (a : ℝ) (ha : 0 ≤ a) :
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧ EqOn H
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1)) ↔
    ∀ s : ℂ, a + 1 / 2 < s.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s := by
  rw [introTrace_continuation_iff_finiteL_orders χ a ha]
  constructor
  · intro h s hs
    have ho := h s hs
    rw [introTrace_normalized_finite_order_eq_completed χ s (by linarith)] at ho
    rw [ho]
    split_ifs <;> norm_num
  · intro h s hs
    rw [introTrace_normalized_finite_order_eq_completed χ s (by linarith)]
    split_ifs with he
    · obtain ⟨rfl, rfl⟩ := he
      exact introTrace_normalized_trivial_order_one
    · exact le_antisymm (not_lt.mp (h s hs))
        (introTrace_normalized_completed_order_nonneg τ hτ χ hχ s (by linarith) he)

open Classical in
/-- Paper: §1.4.5, p. 30. Proposition 3.2.1.3 excludes positive order on and to the right of the Euler boundary,
so the fixed-width criterion only tests the open strip below one. -/
theorem introTrace_normalized_continuation_iff_no_right_zeros_in_strip
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (a : ℝ) (ha : 0 ≤ a) :
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧ EqOn H
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1)) ↔
    ∀ s : ℂ, a + 1 / 2 < s.re → s.re < 1 → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s := by
  rw [introTrace_normalized_continuation_iff_no_right_zeros τ hτ χ hχ a ha]
  constructor
  · exact fun h s hs _ ↦ h s hs
  · intro h s hs hp
    have hL := continuedCompletedHeckeL_spec χ
    exact h s hs (completedHeckeL_continuation_zeros χ _ hL.1 hL.2 (by linarith) hp) hp

open scoped ComplexConjugate in
/-- Complex conjugation of both the parameter and the value preserves a local meromorphic normal form and its order. -/
private theorem introTrace_conjugate_germ_order (f : ℂ → ℂ) (s : ℂ) (hf : MeromorphicNFAt f (conj s)) :
    MeromorphicNFAt (conj ∘ f ∘ conj) s ∧
      meromorphicOrderAt (conj ∘ f ∘ conj) s = meromorphicOrderAt f (conj s) := by
  have hc := Complex.continuous_conj.tendsto s
  rcases hf with hz | ⟨n, g, hg, hn, hfg⟩
  · have hr : conj ∘ f ∘ conj =ᶠ[𝓝 s] 0 := by
      filter_upwards [hc.eventually hz] with w hw
      exact (congrArg conj hw).trans (map_zero _)
    exact ⟨Or.inl hr,
      (meromorphicOrderAt_eq_top_iff.mpr (hr.filter_mono nhdsWithin_le_nhds)).trans
        (meromorphicOrderAt_eq_top_iff.mpr (hz.filter_mono nhdsWithin_le_nhds)).symm⟩
  · have hga : AnalyticAt ℂ (conj ∘ g ∘ conj) s := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      filter_upwards [hc.eventually (Complex.analyticAt_iff_eventually_differentiableAt.mp hg)] with w hw
      simpa only [Complex.conj_conj] using hw.comp_ringHom conj conj
    have hgn : (conj ∘ g ∘ conj) s ≠ 0 := (map_ne_zero_iff _ (starRingEnd ℂ).injective).mpr hn
    have he : (conj ∘ f ∘ conj) =ᶠ[𝓝 s] (· - s) ^ n • (conj ∘ g ∘ conj) := by
      filter_upwards [hc.eventually hfg] with w hw
      simpa only [comp_apply, Pi.smul_apply', Pi.pow_apply, smul_eq_mul, map_mul, map_zpow₀,
        map_sub, Complex.conj_conj] using congrArg conj hw
    have hr : MeromorphicNFAt (conj ∘ f ∘ conj) s := Or.inr ⟨n, _, hga, hgn, he⟩
    have hf : MeromorphicNFAt f (conj s) := Or.inr ⟨n, g, hg, hn, hfg⟩
    exact ⟨hr, ((meromorphicOrderAt_eq_int_iff hr.meromorphicAt).mpr
      ⟨_, hga, hgn, he.filter_mono nhdsWithin_le_nhds⟩).trans
      ((meromorphicOrderAt_eq_int_iff hf.meromorphicAt).mpr
        ⟨g, hg, hn, hfg.filter_mono nhdsWithin_le_nhds⟩).symm⟩

open scoped ComplexConjugate in
/-- Conjugating a finite Euler product on the half-plane of absolute convergence
replaces the character by its inverse and conjugates the parameter. -/
private theorem introTrace_finite_euler_conj (χ : U𝔽) (s : ℂ) (hs : 1 < s.re) :
    finiteHeckeL χ⁻¹ ⟨s, hs⟩ = conj (finiteHeckeL χ ⟨conj s, hs⟩) := by
  have htwist (z : ℂ) (g : C𝔽) :
      ideleClassNormTwist χ⁻¹ z g = conj (ideleClassNormTwist χ (conj z) g) := by
    have hn : (N(g) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg (NNReal.coe_nonneg _)]
      exact Real.pi_ne_zero.symm
    change (((χ g)⁻¹ : Circle) : ℂ) * (N(g) : ℂ) ^ z =
      conj ((χ g : ℂ) * (N(g) : ℂ) ^ (conj z))
    rw [Circle.coe_inv_eq_conj, map_mul, ← Complex.conj_cpow _ _ hn, Complex.conj_ofReal]
  apply (finiteHeckeL_hasProd χ⁻¹ ⟨s, hs⟩).unique
  apply ((finiteHeckeL_hasProd χ ⟨conj s, hs⟩).map conj Complex.continuous_conj).congr_fun
  intro v
  have hunit (x : (v.adicCompletionIntegers F)ˣ) :
      (ideleClassNormTwist χ⁻¹ 0).restrict v x = conj ((ideleClassNormTwist χ 0).restrict v x) := by
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    change (ideleClassNormTwist χ⁻¹ 0).restrict v (u : v.adicCompletion F) =
      conj ((ideleClassNormTwist χ 0).restrict v (u : v.adicCompletion F))
    simp only [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change ideleClassNormTwist χ⁻¹ 0 (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) =
      conj (ideleClassNormTwist χ 0 (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))
    simpa only [map_zero] using htwist 0 (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)
  have hu : (ideleClassNormTwist χ⁻¹ 0).IsUnramifiedAt v ↔ (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
    simp only [HeckeCharacter.isUnramifiedAt_iff, hunit, map_eq_one_iff _ (starRingEnd ℂ).injective]
  change finiteHeckeEulerFactor χ⁻¹ v s = conj (finiteHeckeEulerFactor χ v (conj s))
  by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    have hπ := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
    let π : (v.adicCompletion F)ˣ := Units.mk0 _ hπ.ne_zero
    rw [← inv_inj, ← map_inv₀,
      finiteHeckeEulerFactor_inv_uniformizer χ⁻¹ v π hπ (hu.mpr h) hs,
      finiteHeckeEulerFactor_inv_uniformizer χ v π hπ h (show 1 < (conj s).re from hs), map_sub, map_one]
    exact congrArg (1 - ·) (htwist s (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π))
  · unfold finiteHeckeEulerFactor
    rw [ite_eq_right (mt hu.mp h), ite_eq_right h, map_one]

open scoped ComplexConjugate in
/-- The finite Hecke continuations for inverse unitary characters have the same order at conjugate points. -/
private theorem introTrace_finite_conj_order (χ : U𝔽) (s : ℂ) :
    meromorphicOrderAt finiteL(χ⁻¹) s = meromorphicOrderAt finiteL(χ) (conj s) := by
  let R := conj ∘ finiteL(χ) ∘ conj
  have hχ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hI := (finiteHeckeL_exists_continuation χ⁻¹).choose_spec
  have hg (z : ℂ) := introTrace_conjugate_germ_order finiteL(χ) z (hχ.1 (mem_univ _))
  have hR : MeromorphicOn R univ := fun z _ ↦ (hg z).1.meromorphicAt
  have he (z : ℂ) (hz : 1 < z.re) : finiteL(χ⁻¹) z = R z :=
    (hI.2 ⟨z, hz⟩).trans <| (introTrace_finite_euler_conj χ z hz).trans (congrArg conj (hχ.2 ⟨conj z, hz⟩)).symm
  have hU : ∀ᶠ z : ℂ in 𝓝 2, 1 < z.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have ht : meromorphicOrderAt (finiteL(χ⁻¹) - R) 2 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (eventuallyEq_iff_sub.mp ((hU.mono he).filter_mono nhdsWithin_le_nhds))
  have ht' := (hI.1.meromorphicOn.sub hR).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) ht
  exact (meromorphicOrderAt_congr (eventuallyEq_iff_sub.mpr (meromorphicOrderAt_eq_top_iff.mp ht'))).trans (hg s).2

open scoped ComplexConjugate in
/-- The completed functional equation and conjugation of the finite Euler product reflect the order across the critical line for this same character. -/
private theorem introTrace_single_character_reflected_order (χ : U𝔽) (s : ℂ) (h₁ : s.re < 1) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) (1 - conj s) =
      meromorphicOrderAt (continuedCompletedHeckeL χ) s := by
  obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation χ
    (continuedCompletedHeckeL χ) (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
  let r (z : ℂ) := 1 - z
  have hr : HasDerivAt r (-1) s := by simpa [r] using (hasDerivAt_id s).const_sub 1
  have e : continuedCompletedHeckeL χ⁻¹ ∘ r = fun z ↦ ε z * continuedCompletedHeckeL χ z := funext he
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
    (show AnalyticAt ℂ r s by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
  rw [e] at ho
  change meromorphicOrderAt (ε * continuedCompletedHeckeL χ) s = _ at ho
  rw [meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt s) (hne s)] at ho
  have hrpos : 0 < (1 - s).re := by simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr h₁
  calc
    _ = meromorphicOrderAt finiteL(χ) (conj (1 - s)) := by
      rw [map_sub, map_one]
      exact (introTrace_normalized_finite_order_eq_completed χ _ (by simpa using hrpos)).symm
    _ = meromorphicOrderAt finiteL(χ⁻¹) (1 - s) := (introTrace_finite_conj_order χ _).symm
    _ = meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - s) :=
      introTrace_normalized_finite_order_eq_completed χ⁻¹ _ hrpos
    _ = _ := ho.symm

private theorem introTrace_divisor_pos_iff_order_pos (χ : U𝔽) (s : ℂ) :
    0 < zeroOrder(χ, s) ↔ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s := by
  have hL := (continuedCompletedHeckeL_spec χ).1
  have hn : meromorphicOrderAt (continuedCompletedHeckeL χ) s ≠ ⊤ := by
    apply hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := 2) (mem_univ _) (mem_univ s)
    rw [← introTrace_normalized_finite_order_eq_completed χ 2 (by norm_num)]
    have hF := (finiteHeckeL_exists_continuation χ).choose_spec
    have hne : finiteL(χ) 2 ≠ 0 := by
      rw [hF.2 ⟨2, by norm_num⟩]
      exact finiteHeckeL_ne_zero_of_one_lt_re χ _
    rw [(hF.1 (mem_univ (2 : ℂ))).meromorphicOrderAt_eq_zero_iff.mpr hne]
    exact WithTop.zero_ne_top
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ s)]
  cases he : meromorphicOrderAt (continuedCompletedHeckeL χ) s with
  | top => exact (hn he).elim
  | coe k => simp

open scoped ComplexConjugate in
open Classical in
/-- Paper: §1.4.5, p. 30. At a fixed nonnegative half-width, the asserted holomorphic
continuation for a normalized character exists exactly when every positive-order zero of
its completed L-function belongs to the closed centered window. Zeros on either
boundary lie outside the open continuation domain or on its reflection. -/
theorem introTrace_continuation_iff_zeros_in_closed_window
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (a : ℝ) (ha : 0 ≤ a) :
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧ EqOn H
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1)) ↔
      ∀ s : ℂ, 0 < zeroOrder(χ, s) → |s.re - 1 / 2| ≤ a := by
  rw [introTrace_normalized_continuation_iff_no_right_zeros_in_strip τ hτ χ hχ a ha]
  constructor
  · intro h s hs
    have hb := abs_lt.mp (introTrace_positive_divisor_in_critical_strip χ s hs)
    have hs₀ : 0 < s.re := by linarith [hb.1]
    have hs₁ : s.re < 1 := by linarith [hb.2]
    have hp := (introTrace_divisor_pos_iff_order_pos χ s).mp hs
    have hright : s.re ≤ a + 1 / 2 := le_of_not_gt fun he ↦ h s he hs₁ hp
    have hre : (1 - conj s).re = 1 - s.re := by simp
    have href : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (1 - conj s) := by
      rwa [introTrace_single_character_reflected_order χ s hs₁]
    have hleft : (1 - conj s).re ≤ a + 1 / 2 :=
      le_of_not_gt fun he ↦ h _ he (by rw [hre]; linarith) href
    rw [hre] at hleft
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro hall s hs _ hp
    have h := (abs_le.mp (hall s ((introTrace_divisor_pos_iff_order_pos χ s).mpr hp))).2
    linarith

open Classical in
/-- Paper: §1.4.5, p. 30. For a single normalized character the continuation
asserted at every positive half-width exists exactly when the positive-order
zeros of its completed L-function all lie on the critical line. -/
theorem introTrace_single_character_all_continuations_iff_critical_line
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) :
    (∀ a : ℝ, 0 < a → ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧ EqOn H
      (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1)) ↔
      ∀ s : ℂ, 0 < zeroOrder(χ, s) → s.re = 1 / 2 := by
  constructor
  · intro h s hs
    by_contra hne
    let d := |s.re - 1 / 2|
    have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hw := (introTrace_continuation_iff_zeros_in_closed_window τ hτ χ hχ (d / 2)
      (half_pos hd).le).mp (h (d / 2) (half_pos hd)) s hs
    exact (not_le_of_gt (half_lt_self hd)) hw
  · intro h a ha
    apply (introTrace_continuation_iff_zeros_in_closed_window τ hτ χ hχ a ha.le).mpr
    intro s hs
    simpa only [h s hs, sub_self, abs_zero] using ha.le

open Classical in
/-- Paper: §1.4.5, p. 30. Continuation from every positive half-width gives
holomorphy of the shifted logarithmic derivative throughout the right half-plane
except for the possible shifted pole in the trivial character.
Deviation: The regularizing term has the sign dictated by the corrected Euler
sum. Meromorphic continuation on the overlap is used before concluding
holomorphy of the pointwise logarithmic derivative away from the pole. -/
theorem introTrace_logDeriv_analytic_of_extensions (χ : U𝔽)
    (_h : ∀ a : ℝ, 0 < a → ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧
      EqOn H (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1)) :
    AnalyticOnNhd ℂ (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2))
      {z : ℂ | 0 < z.re ∧ (χ ≠ 1 ∨ z ≠ 1 / 2)} := by
  let L := finiteL(χ)
  have hL : MeromorphicNFOn L univ := (finiteHeckeL_exists_continuation χ).choose_spec.1
  have hfinite (w : ℂ) : meromorphicOrderAt L w ≠ ⊤ := by
    apply hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (x := 2) (mem_univ _) (mem_univ w)
    have htwo : L 2 ≠ 0 := by
      rw [show L 2 = finiteHeckeL χ ⟨2, by norm_num⟩ from
        (finiteHeckeL_exists_continuation χ).choose_spec.2 ⟨2, by norm_num⟩]
      exact finiteHeckeL_ne_zero_of_one_lt_re χ ⟨2, by norm_num⟩
    rw [(hL (mem_univ (2 : ℂ))).meromorphicOrderAt_eq_zero_iff.mpr htwo]
    exact WithTop.zero_ne_top
  intro z hz
  obtain ⟨H, hH, hEq⟩ := _h (z.re / 2) (half_pos hz.1)
  let R : ℂ → ℂ := fun w ↦
    if χ = 1 then 1 / (w + 1 / 2) + 1 / (w - 1 / 2) else 0
  let D : ℂ → ℂ := fun w ↦ logDeriv L (w + 1 / 2)
  have hD : Meromorphic D := by
    intro w
    exact meromorphicAt_comp_add_const_iff_meromorphicAt.mpr
      (hL (mem_univ (w + 1 / 2))).meromorphicAt.logDeriv
  have hR : Meromorphic R := by
    intro w
    dsimp only [R]
    split_ifs <;> fun_prop
  let A := H - R
  have hA : MeromorphicOn A right(z.re / 2) :=
    hH.meromorphicOn.sub (fun w _ ↦ hR w)
  -- Continue equality of punctured germs, without assuming regularity at zeros or poles.
  let q : ℂ := (max (z.re / 2) 1 + 1 : ℝ)
  have hq : max (z.re / 2) 1 < q.re := by simp [q]
  have hbase : meromorphicOrderAt (D - A) q = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hnear : ∀ᶠ w : ℂ in 𝓝 q, max (z.re / 2) 1 < w.re :=
      Complex.continuous_re.continuousAt.eventually (eventually_gt_nhds hq)
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with w hw
    have he : H w = D w + R w := hEq hw
    change D w - (H w - R w) = 0
    rw [he]
    ring
  have hzhalf : z ∈ right(z.re / 2) := by change z.re / 2 < z.re; linarith [hz.1]
  have hqhalf : q ∈ right(z.re / 2) := (le_max_left _ _).trans_lt hq
  have hDm : MeromorphicOn D right(z.re / 2) := fun w _ ↦ hD w
  have horder := (hDm.sub hA).meromorphicOrderAt_eq_top_of_isPreconnected
    (convex_halfSpace_re_gt _).isPreconnected hqhalf hzhalf hbase
  have hnear : D =ᶠ[𝓝[≠] z] A :=
    (meromorphicOrderAt_eq_top_iff.mp horder).mono fun w hw ↦ sub_eq_zero.mp hw
  have hRz : AnalyticAt ℂ R z := by
    dsimp only [R]
    split_ifs with hχ
    · have hp : z + 1 / 2 ≠ 0 := by
        intro hzero
        have hre := congrArg Complex.re hzero
        norm_num at hre
        linarith [hz.1]
      have hm : z - 1 / 2 ≠ 0 := sub_ne_zero.mpr (hz.2.resolve_left (not_not.mpr hχ))
      have hpa : AnalyticAt ℂ (fun w : ℂ ↦ w + 1 / 2) z := by fun_prop
      have hma : AnalyticAt ℂ (fun w : ℂ ↦ w - 1 / 2) z := by fun_prop
      exact (analyticAt_const.div hpa hp).add (analyticAt_const.div hma hm)
    · exact analyticAt_const
  have hnonneg : 0 ≤ meromorphicOrderAt D z := by
    rw [meromorphicOrderAt_congr hnear]
    exact ((hH z hzhalf).sub hRz).meromorphicOrderAt_nonneg
  change 0 ≤ meromorphicOrderAt (logDeriv L ∘ (· + (1 / 2 : ℂ))) z at hnonneg
  rw [meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt] at hnonneg
  -- A zero or pole of L would give its logarithmic derivative a simple pole.
  have hzero : meromorphicOrderAt L (z + 1 / 2) = 0 := by
    by_contra hzero
    rw [meromorphicOrderAt_logDeriv_eq_neg_one hzero (hfinite _)] at hnonneg
    exact (by decide : ¬ (0 : WithTop ℤ) ≤ -1) hnonneg
  have hnormal := hL (mem_univ (z + 1 / 2))
  have ha := hnormal.meromorphicOrderAt_nonneg_iff_analyticAt.mp (le_of_eq hzero.symm)
  exact (ha.deriv.div ha (hnormal.meromorphicOrderAt_eq_zero_iff.mp hzero)).comp
    (f := fun w : ℂ ↦ w + 1 / 2) (x := z) (by fun_prop)

/-- Paper: §1.4.5, p. 30. A holomorphic shifted logarithmic derivative
excludes finite Hecke zeros to the right of one half. The exceptional point
for the trivial character is a pole of the finite L-function. -/
theorem introTrace_finiteL_no_right_zeros (χ : U𝔽)
    (_h : AnalyticOnNhd ℂ (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2))
      {z : ℂ | 0 < z.re ∧ (χ ≠ 1 ∨ z ≠ 1 / 2)}) (s : ℂ) (_hs : 1 / 2 < s.re) :
    meromorphicOrderAt finiteL(χ) s ≤ 0 := by
  let L := finiteL(χ)
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hr (z : ℂ) (hz : 1 ≤ z.re) : meromorphicOrderAt L z ≤ 0 := by
    obtain ⟨A, hA, h⟩ := finiteHeckeL_zeroFreeRegion
    obtain ⟨B, hB, hzero⟩ := h F χ
    have hl : 0 ≤ Real.log (B * (|z.im| + 3)) := Real.log_nonneg (by
      have := mul_nonneg (show 0 ≤ B by linarith) (abs_nonneg z.im)
      nlinarith)
    exact hzero L hL.1 hL.2 z ((sub_le_self _ (div_nonneg hA.le
      (mul_nonneg (by positivity) hl))).trans hz)
  by_cases he : s = 1
  · exact hr s (by simp [he])
  have hne : meromorphicOrderAt L s ≠ ⊤ := hL.1.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s)
    ((hr 2 (by norm_num)).trans_lt (show (0 : WithTop ℤ) < ⊤ by simp)).ne
  have hs : 0 < (s - 1 / 2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hx : s - 1 / 2 ≠ 1 / 2 := fun h ↦ he (by linear_combination h)
  have han := (_h (s - 1 / 2) ⟨hs, Or.inr hx⟩).comp (f := fun z : ℂ ↦ z - 1 / 2)
    (analyticAt_id.sub analyticAt_const)
  have ha : AnalyticAt ℂ (logDeriv L) s := by simpa [Function.comp_def, L] using han
  by_contra! hp
  have hn := ha.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_logDeriv_eq_neg_one hp.ne' hne] at hn
  have hi : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp hn
  omega

/-- Dividing by the restriction to the norm section gives a normalized character
and a purely imaginary translation of its exponent. -/
private theorem introTraceApprox_spectral_normalized_character
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) :
    ∃ (ψ : U𝔽) (a : ℂ), a.re = 0 ∧ (∀ t, ψ (τ t) = 1) ∧
      ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a) := by
  let n : C𝔽 →ₜ* ℝ≥0ˣ := continuousIdeleClassNorm F
  let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  obtain ⟨a, ⟨ha, hpower⟩, -⟩ :=
    existsUnique_unitaryComplexPower (j.comp (χ.comp τ)) (fun t ↦ Circle.norm_coe _)
  let η : U𝔽 := χ.comp (τ.comp n)
  let ψ : U𝔽 := χ / η
  have hnorm (t : ℝ≥0ˣ) : ψ (τ t) = 1 := by
    change χ (τ t) / χ (τ (ideleClassNorm F (τ t))) = 1
    rw [hτ t, div_self']
  have htwist : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a) := by
    ext1 g
    change ((χ g : ℂ) / (χ (τ (ideleClassNorm F g)) : ℂ)) *
      (N(g) : ℂ) ^ (0 : ℂ) = (χ g : ℂ) * (N(g) : ℂ) ^ (-a)
    rw [Complex.cpow_zero, mul_one, Complex.cpow_neg, div_eq_mul_inv]
    exact congrArg (fun w : ℂ ↦ (χ g : ℂ) * w⁻¹) (hpower (ideleClassNorm F g))
  exact ⟨ψ, a, ha, hnorm, htwist⟩

/-- Imaginary norm twists translate the finite L-function. The gamma factor is
regular and nonvanishing throughout the positive half-plane. -/
private theorem introTraceApprox_spectral_finiteOrder_twist (χ ψ : U𝔽) (a : ℂ) (ha : a.re = 0)
    (htwist : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a)) (s : ℂ) (hs : 0 < s.re) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s = meromorphicOrderAt finiteL(ψ) (s+a) := by
  let G (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let L := continuedCompletedHeckeL χ
  let H (z : ℂ) := finiteL(ψ) (z + a)
  have hG : Differentiable ℂ G := differentiable_inv_heckeGammaFactor χ
  have hL := continuedCompletedHeckeL_spec χ
  have hF := (finiteHeckeL_exists_continuation ψ).choose_spec
  have hH : MeromorphicOn H univ := fun z _ ↦
    ((hF.1 (mem_univ (z + a))).meromorphicAt).comp_analyticAt (g := fun w : ℂ ↦ w + a) (by fun_prop)
  have hGL : MeromorphicOn (fun z ↦ G z * L z) univ :=
    fun z hz ↦ (hG.analyticAt z).meromorphicAt.mul (hL.1 hz).meromorphicAt
  have hEq (z : ℂ) (hz : 1 < z.re) : H z = G z * L z := by
    have hw : 1 < (z + a).re := by rwa [Complex.add_re, ha, add_zero]
    let w : {z : ℂ // 1 < z.re} := ⟨z, hz⟩
    have ht : finiteHeckeL ψ ⟨z + a, hw⟩ = finiteHeckeL χ w := by
      simpa [w, add_assoc] using
        finiteHeckeL_imaginary_twist χ ψ (-a) (by simp [ha]) htwist ⟨z + a, hw⟩
    calc
      H z = finiteHeckeL ψ ⟨z + a, hw⟩ := hF.2 ⟨z + a, hw⟩
      _ = finiteHeckeL χ w := ht
      _ = G z * completedHeckeL χ w :=
        (inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)) _).symm
      _ = G z * L z := congrArg (G z * ·) (hL.2 w).symm
  have hnear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have htop : meromorphicOrderAt (H - fun z ↦ G z * L z) 2 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (eventuallyEq_iff_sub.mp
      ((hnear.mono hEq).filter_mono nhdsWithin_le_nhds))
  have ho := (hH.sub hGL).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) htop
  have hlocal : H =ᶠ[𝓝[≠] s] (fun z ↦ G z * L z) :=
    eventuallyEq_iff_sub.mpr (meromorphicOrderAt_eq_top_iff.mp ho)
  have hord : meromorphicOrderAt H s = meromorphicOrderAt L s := by
    rw [meromorphicOrderAt_congr hlocal]
    exact meromorphicOrderAt_mul_of_ne_zero (hG.analyticAt s)
      (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (by linarith)))
  rw [← hord]
  exact meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt

/-- Paper: §1.4.5, p. 30. Right-hand nonvanishing for the finite continuations
in the section-normalized characters implies right-hand nonvanishing for every
completed continuation. Imaginary norm twists translate the exponent, and the
gamma factors are regular and nonzero in the positive half-plane. -/
theorem introTrace_completedL_no_right_zeros (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F))
    (_h : ∀ (ψ : U𝔽), (∀ t, ψ (τ t) = 1) →
      ∀ s : ℂ, 1 / 2 < s.re → meromorphicOrderAt finiteL(ψ) s ≤ 0)
    (χ : U𝔽) (s : ℂ) (_hs : 1 / 2 < s.re) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s ≤ 0 := by
  obtain ⟨ψ, a, ha, hnorm, htwist⟩ := introTraceApprox_spectral_normalized_character τ _hτ χ
  rw [introTraceApprox_spectral_finiteOrder_twist χ ψ a ha htwist s (by linarith)]
  exact _h ψ hnorm (s + a) (by rwa [Complex.add_re, ha, add_zero])

/-- The completed divisors of imaginary twists agree after translation in the critical strip. -/
private theorem introTraceApprox_spectral_divisor_translate (χ ψ : U𝔽) (a : ℂ) (ha : a.re = 0)
    (htwist : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a)) (s : ℂ) (hs : 0 < s.re) :
    zeroOrder(χ, s) = zeroOrder(ψ, s+a) := by
  have hs' : 0 < (s + a).re := by simpa [Complex.add_re, ha] using hs
  have hχ := introTraceApprox_spectral_finiteOrder_twist χ ψ a ha htwist s hs
  have hψ := introTraceApprox_spectral_finiteOrder_twist ψ ψ 0 (by simp) (by simp) (s+a) hs'
  simp only [add_zero] at hψ
  simp only [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec _).1.meromorphicOn (mem_univ _), hχ, hψ]

/-- Imaginary translation bijects the two zero windows, preserves the orders, and
transfers the Mellin weight to the radial test. -/
private theorem introTraceApprox_spectral_translate (χ ψ : U𝔽) (a : ℂ) (ha : a.re = 0)
    (htwist : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a)) (f : ℝ → ℂ) :
    introTraceSpectralSum (F := F) χ f 1 =
      introTraceSpectralSum (F := F) ψ (fun t ↦ (t : ℂ)^(-a) * f t) 1 := by
  let Zχ := windowZeros(χ, (1 : ℝ))
  let Zψ := windowZeros(ψ, (1 : ℝ))
  have hpos (η : U𝔽) (s : ℂ) (hs : 0 < zeroOrder(η, s)) : 0 < s.re := by
    linarith [(abs_lt.mp (introTrace_positive_divisor_in_critical_strip η s hs)).1]
  have hplus (z : Zχ) : zeroOrder(χ, z.val) = zeroOrder(ψ, z.val+a) :=
    introTraceApprox_spectral_divisor_translate χ ψ a ha htwist z.val (hpos _ _ z.property.1)
  have hminus (w : Zψ) : zeroOrder(χ, w.val-a) = zeroOrder(ψ, w.val) := by
    simpa only [sub_add_cancel] using introTraceApprox_spectral_divisor_translate χ ψ a ha htwist (w.val-a)
      (by simpa only [Complex.sub_re, ha, sub_zero] using hpos _ _ w.property.1)
  let e : Zχ ≃ Zψ := {
    toFun := fun z ↦ ⟨z.val+a, (hplus z) ▸ z.property.1, by simpa [Complex.add_re, ha] using z.property.2⟩
    invFun := fun w ↦ ⟨w.val-a, (hminus w).symm ▸ w.property.1, by simpa [Complex.sub_re, ha] using w.property.2⟩
    left_inv := fun z ↦ Subtype.ext (add_sub_cancel_right z.val a)
    right_inv := fun w ↦ Subtype.ext (sub_add_cancel w.val a) }
  unfold introTraceSpectralSum
  rw [← e.tsum_eq]
  apply tsum_congr
  intro z
  change _ = (zeroOrder(ψ, z.val+a) : ℂ) * mellin _ (z.val+a-1/2)
  rw [hplus z, show (fun t : ℝ ↦ (t : ℂ)^(-a) * f t) = (fun t : ℝ ↦ (t : ℂ)^(-a) • f t) from rfl,
    mellin_cpow_smul]
  congr 2
  ring

/-- The norm twist of a character cancels the inverse phase on its radial profile. -/
private theorem introTraceApprox_spectral_twistTest (χ ψ : U𝔽) (a : ℂ)
    (htwist : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a)) (f : ℝ → ℂ) (g : C𝔽) :
    introTraceTest ψ (fun t ↦ (t : ℂ)^(-a) * f t) g = introTraceTest χ f g := by
  have hg := DFunLike.congr_fun htwist g
  change (ψ g : ℂ) * (N(g) : ℂ) ^ (0 : ℂ) = (χ g : ℂ) * (N(g) : ℂ) ^ (-a) at hg
  rw [Complex.cpow_zero, mul_one] at hg
  let u := χ g
  let v := ψ g
  have hu : (u : ℂ) ≠ 0 := by simp [u]
  have hv : (v : ℂ) ≠ 0 := by simp [v]
  have hp : (N(g) : ℂ)^(-a) = (v : ℂ) / (u : ℂ) :=
    (eq_div_iff hu).2 (by simpa [mul_comm] using hg.symm)
  simp only [introTraceTest, hp]
  change (starRingEnd ℂ) (v : ℂ) * ((v : ℂ)/(u : ℂ)*_) = (starRingEnd ℂ) (u : ℂ)*_
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_inv_eq_conj, Circle.coe_inv, Circle.coe_inv]
  field_simp

open Classical in
/-- The full-window trace identity for an arbitrary character follows by normalizing
on the norm section. The underlying adelic test and its local geometric terms are
unchanged. In the normalized trivial isotype the two polar moments are translated. -/
private theorem introTraceApprox_spectral_twistTrace (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ ψ : U𝔽) (hψ : ∀ t, ψ (τ t) = 1) (a : ℂ) (ha : a.re = 0)
    (htwist : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a)) (f : ℝ → ℂ)
    (hf : f 1 = 0) (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g, φ.val g = introTraceTest χ f g) :
    (∑ w, introTraceArchimedean χ f w) + introTraceSpectralSum χ f 1 =
      (if ψ = 1 then introTraceMellin f (1/2-a) + introTraceMellin f (-1/2-a) else 0) -
        ∑' p : HeightOneSpectrum (𝓞 F) × ℕ, introTracePrimePower χ f p.1 p.2 := by
  classical
  let g := fun t : ℝ ↦ (t : ℂ)^(-a) * f t
  have hg : g 1 = 0 := by simp [g, hf]
  have ht (x : C𝔽) : introTraceTest ψ g x = introTraceTest χ f x := introTraceApprox_spectral_twistTest χ ψ a htwist f x
  have hφ' (x : C𝔽) : φ.val x = introTraceTest ψ g x := (hφ x).trans (ht x).symm
  have hfull := traceFormula_exteriorZeros_of_half_le τ φ (by norm_num : (1/2:ℝ) ≤ 1)
  have hS := (introTrace_characterTrace_of_exteriorZeros τ hτ ψ hψ g hg φ hφ' 1 (fun _ ↦ by
    simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ, Set.indicator_univ] using hfull)).2.2.tsum_eq
  have hac : ∀ w, introTraceArchimedean ψ g w = introTraceArchimedean χ f w := by
    intro w
    simp only [introTraceArchimedean, ht]
  have (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (v.adicCompletion F)ˣ := by
    let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
    exact (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).locallyCompactSpace
  obtain ⟨_, B, _, hB, _, _⟩ := traceFormula_of_exteriorZeros τ hτ φ 1 hfull
  have hp' := introTrace_characterTrace_primes_summable τ hτ ψ g φ hφ'
  have hp := introTrace_characterTrace_primes_summable τ hτ χ f φ hφ
  have hprime : (∑' p : HeightOneSpectrum (𝓞 F) × ℕ, introTracePrimePower ψ g p.1 p.2) =
      ∑' p : HeightOneSpectrum (𝓞 F) × ℕ, introTracePrimePower χ f p.1 p.2 := by
    rw [hp'.tsum_prod, hp.tsum_prod]
    apply tsum_congr
    intro v
    exact (introTrace_characterTrace_finite ψ g hg v (B v) (fun u ↦ (hB v u).trans (hφ' _))).symm.trans
      (introTrace_characterTrace_finite χ f hf v (B v) (fun u ↦ (hB v u).trans (hφ _)))
  have hM (s : ℂ) : introTraceMellin g s = introTraceMellin f (s-a) := by
    simpa only [introTraceMellin, g, smul_eq_mul, sub_eq_add_neg] using mellin_cpow_smul f s (-a)
  change introTraceSpectralSum ψ g 1 = _ at hS
  rw [introTraceApprox_spectral_translate χ ψ a ha htwist f]
  change (∑ w, introTraceArchimedean χ f w) + introTraceSpectralSum ψ g 1 = _
  rw [hS, hprime]
  simp only [hac, hM]
  split <;> ring

/-- Paper: §1.4.3, p. 29. For every unitary character over every number field the
real part of the entire unit-window spectral sum at parameter two tends to minus
infinity along every admissible cutoff family. -/
theorem introTraceApprox_spectral_tendsto_atBot (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) :
    Tendsto (fun n ↦ (introTraceSpectralSum χ approx(h, ρ, n, (2 : ℂ)) 1).re) atTop atBot := by
  apply introTraceApprox_spectral_tendsto_atBot_of_primeBound χ h ρ hA
  have hQ := (introTraceApprox_primeSum_tendsto χ h ρ hA).tendsto_at (a := (2:ℂ)) (by norm_num)
  have hR := (Complex.continuous_re.tendsto _).comp hQ
  let q := -logDeriv finiteL(χ) ((2:ℂ)+1/2)
  refine ⟨-(q.re - 1), ?_⟩
  filter_upwards [hR.eventually (lt_mem_nhds (sub_one_lt q.re))] with n hn
  exact (neg_lt_neg hn).le

/-- Paper: §1.4.3, p. 29. For every full critical-strip window the real part of the
unregularized spectral sum at parameter two tends to negative infinity. -/
theorem introTraceApprox_full_window_spectral_tendsto_atBot (χ : U𝔽)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) (a : ℝ) (ha : 1 / 2 ≤ a) :
    Tendsto (fun n ↦ (introTraceSpectralSum χ approx(h, ρ, n, (2 : ℂ)) a).re) atTop atBot := by
  apply (introTraceApprox_spectral_tendsto_atBot χ h ρ hA).congr
  intro n
  exact congrArg Complex.re (introTrace_full_window_spectral_sum_eq χ _ a ha).symm

/-- Paper: §1.4.3, p. 29. At every point of the Euler half-plane `Re z > 1/2`, the
real part of the unregularized full-window spectral sum tends to minus infinity.
This holds for any unitary character and independently shrinking admissible cutoffs. -/
theorem introTraceApprox_full_window_spectral_euler_tendsto_atBot (χ : U𝔽)
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) (a : ℝ) (ha : 1/2 ≤ a)
    (z : ℂ) (hz : 1/2 < z.re) :
    Tendsto (fun n ↦ (introTraceSpectralSum χ (introTraceApprox (h n) (ρ n) z) a).re) atTop atBot := by
  have signed := introTraceApprox_spectral_atBot_of_local_digamma χ h ρ hA z
    (fun hk p q hp ↦ introTraceApprox_euler_gamma h ρ hA z (by linarith) hk p q hp)
  have hQ := (introTraceApprox_primeSum_tendsto χ h ρ hA).tendsto_at (a := z) hz
  have hR := (Complex.continuous_re.tendsto _).comp hQ
  let q := -logDeriv finiteL(χ) (z+1/2)
  have bound := (hR.eventually (lt_mem_nhds (sub_one_lt q.re))).mono
    (fun _ hh ↦ (neg_lt_neg hh).le)
  apply (introTraceApprox_spectral_atBot_of_bounds χ h ρ hA z hz signed ⟨-(q.re-1),bound⟩).congr
  intro n
  exact congrArg Complex.re (introTrace_full_window_spectral_sum_eq χ _ a ha).symm

open Classical in
/-- Paper: §1.4.3, p. 29. At every infinite place the real part of the
unregularized cutoff tends to positive infinity throughout the closed right
half-plane, for every admissible approximation family. -/
theorem introTraceApprox_archimedean_local_rightHalfPlane_atTop
    (χ : U𝔽) (w : InfinitePlace F) (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (z : ℂ) (hz : 0 ≤ z.re) :
    Tendsto (fun n ↦ (introTraceArchimedean χ (introTraceApprox (h n) (ρ n) z) w).re)
      atTop atTop := by
  classical
  let f (n : ℕ) := introTraceApprox (h n) (ρ n) z
  have hzero (n : ℕ) (x : ℝ) (hx : x ≤ 1) : f n x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hu ↦ hx.not_gt (introTraceApprox_support h ρ hA n z hu))
  have heq (n : ℕ) := introTraceArchimedean_eq_neg_digamma_of_supported_above_one χ w (f n)
    (introTraceApprox_rat_sub_shiftTwo_profile h ρ hA n z).1.measurable (hzero n)
    (introTraceApprox_archimedean_integrable χ w h ρ hA n z)
  by_cases hw : w.IsReal
  · let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    have hp := (realHeckeCharacter_parameters χ w hw).exists.choose_spec.1
    have hpos : 0 < ((1/2 + p.1 + p.2.val)/2 : ℂ).re := by
      simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re, Complex.natCast_re, p, hp, add_zero]
      positivity
    apply (tendsto_neg_atBot_atTop.comp (introTraceApprox_euler_gamma h ρ hA z hz (k := 1/2) (by norm_num)
      _ ((1/2 - p.1 + p.2.val)/2) hpos)).congr
    intro n
    simpa only [dite_eq_left hw, Complex.neg_re, comp_apply, p, f] using (congrArg Complex.re (heq n)).symm
  · let hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let p := (complexHeckeCharacter_parameters χ w hc).exists.choose
    have hp := (complexHeckeCharacter_parameters χ w hc).exists.choose_spec.1
    have hpos : 0 < (1/2 + p.1 + (p.2.natAbs : ℂ)/2).re := by
      simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re, Complex.natCast_re, p, hp, add_zero]
      positivity
    apply (tendsto_neg_atBot_atTop.comp (introTraceApprox_euler_gamma h ρ hA z hz (k := 1) zero_lt_one
      _ (1/2 - p.1 + (p.2.natAbs : ℂ)/2) hpos)).congr
    intro n
    simpa only [dite_eq_right hw, Complex.neg_re, comp_apply, p, f, hc] using (congrArg Complex.re (heq n)).symm

open Classical in
/-- The positive completed divisor has finite support below any fixed height. -/
private theorem introTrace_finite_zeros_of_bounded_height (χ : U𝔽) (T : ℝ) :
    {r : ℂ | 0 < zeroOrder(χ, r) ∧ |r.im| ≤ T}.Finite := by
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
  have hloc : LocallyFiniteSupport (fun r ↦ D r) := fun r ↦ D.supportLocallyFiniteWithinDomain r (mem_univ r)
  apply (hloc.finite_inter_support_of_isCompact (isCompact_closedBall (0:ℂ) (1 + T))).subset
  intro r hr
  obtain ⟨hr0,hrT⟩ := hr
  have hrs := abs_lt.mp (introTrace_positive_divisor_in_critical_strip χ r hr0)
  have hnn : 0 ≤ r.re := by linarith
  refine ⟨?_, hr0.ne'⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by rw [abs_of_nonneg hnn]; linarith)

open Classical in
/-- A positive horizontal separation between the Mellin variable and the cutoff
parameter bounds all Mellin moments uniformly in both imaginary parts. -/
private theorem introTraceApprox_mellin_uniform_halfplanes (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (σ b : ℝ) (hsep : σ < b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ z s : ℂ, b ≤ z.re → s.re ≤ σ →
      ‖introTraceMellin (introTraceApprox (h n) (ρ n) z) s‖ ≤ B := by
  let C := (1/2 : ℝ)^(-b) + 2^(-b)
  let g := (Ioi (1 : ℝ)).indicator (fun t : ℝ ↦ C * t^(σ-1-b))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi : Integrable g volume := (integrable_indicator_iff measurableSet_Ioi).2
    ((integrableOn_Ioi_rpow_of_lt (by linarith : σ-1-b < -1) zero_lt_one).const_mul C)
  have hg : 0 ≤ g := Set.indicator_nonneg fun t ht ↦
    mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans ht.le) _)
  refine ⟨∫ t in Ioi (0:ℝ), g t, integral_nonneg hg, ?_⟩
  filter_upwards [introTraceApprox_mellin_tendsto_cutoff_bound hA b] with n hbound
  intro z s hz hs
  apply norm_integral_le_of_norm_le hi.integrableOn
  filter_upwards with t
  by_cases ht : 1 < t
  · rw [show g t = C * t^(σ-1-b) from indicator_of_mem ht _, smul_eq_mul,
        norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht)]
    simp only [Complex.sub_re,Complex.one_re]
    calc
      _ ≤ t^(σ-1) * (C * t^(-b)) := mul_le_mul
        (Real.rpow_le_rpow_of_exponent_le ht.le (sub_le_sub_right hs 1))
        (hbound _ _ hz ht) (norm_nonneg _) (by positivity)
      _ = C * t^(σ-1-b) := by
        rw [sub_eq_add_neg (σ-1), Real.rpow_add (zero_lt_one.trans ht)]
        ring
  · have hzero : introTraceApprox (h n) (ρ n) z t = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hmem ↦ ht (introTraceApprox_support h ρ hA n z hmem))
    simp [hzero,g,ht]

open Classical in
/-- Paper: §§1.4.1–1.4.3, pp. 28–29. At each Euler point, the archimedean cutoff plus
any selection of zeros with bounded height or bounded total multiplicity tends to
positive infinity in real part. The remaining full-window spectral sum tends to
negative infinity in real part. Both bounds are uniform over the selections. -/
theorem introTraceApprox_bounded_truncation_escape (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (a : ℝ) (ha : 1 / 2 ≤ a)
    (z : ℂ) (hz : 1 / 2 < z.re) (T M : ℝ) :
    ∀ᶠ n in atTop, ∀ S : Finset ℂ, (∀ r ∈ S, 0 < zeroOrder(χ, r)) →
      ((∀ r ∈ S, |r.im| ≤ T) ∨ (∑ r ∈ S, (zeroOrder(χ, r) : ℝ)) ≤ T) →
      let f := introTraceApprox (h n) (ρ n) z
      let L := ∑ r ∈ S, (zeroOrder(χ, r) : ℂ) * introTraceMellin f (r - 1 / 2)
      M ≤ (archSum(χ, f) + L).re ∧ (introTraceSpectralSum χ f a - L).re ≤ -M := by
  classical
  have hfin := introTrace_finite_zeros_of_bounded_height χ T
  let P := hfin.toFinset
  let mass (S : Finset ℂ) := ∑ r ∈ S, (zeroOrder(χ, r) : ℝ)
  obtain ⟨C, hC, hm⟩ := introTraceApprox_mellin_uniform_halfplanes h ρ hA (1 / 2) z.re hz
  let B := max (mass P) T * C
  let f (n : ℕ) := introTraceApprox (h n) (ρ n) z
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have harch : ∀ᶠ n in atTop, ∀ w : InfinitePlace F,
      max (M + B) 0 ≤ (introTraceArchimedean χ (f n) w).re :=
    eventually_all.mpr fun w ↦ tendsto_atTop.mp
      (introTraceApprox_archimedean_local_rightHalfPlane_atTop χ w h ρ hA z (by linarith)) _
  have hsp := tendsto_atBot.mp (introTraceApprox_full_window_spectral_euler_tendsto_atBot χ h ρ hA a ha z hz) (-M - B)
  filter_upwards [hm, harch, hsp] with n hmoment hnw hns
  intro S hS hsize _ L
  have hmass : mass S ≤ max (mass P) T := by
    rcases hsize with hheight | hmass
    · apply LE.le.trans _ (le_max_left _ _)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact fun r hr ↦ hfin.mem_toFinset.mpr ⟨hS r hr, hheight r hr⟩
      · intro r hr _
        exact_mod_cast (hfin.mem_toFinset.mp hr).1.le
    · exact hmass.trans (le_max_right _ _)
  have hL : |L.re| ≤ B := by
    apply (Complex.abs_re_le_norm L).trans
    calc
      ‖L‖ ≤ ∑ r ∈ S, ‖(zeroOrder(χ, r) : ℂ) * introTraceMellin (f n) (r - 1 / 2)‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ S, (zeroOrder(χ, r) : ℝ) * C := by
        apply Finset.sum_le_sum
        intro r hr
        have hpos : 0 < (zeroOrder(χ, r) : ℝ) := by exact_mod_cast hS r hr
        have hrs := (abs_lt.mp (introTrace_positive_divisor_in_critical_strip χ r (hS r hr))).2
        rw [norm_mul, Complex.norm_intCast, abs_of_pos hpos]
        apply mul_le_mul_of_nonneg_left _ hpos.le
        apply hmoment _ _ le_rfl
        simpa only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] using hrs.le
      _ ≤ B := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hmass hC
  have hs : M + B ≤ (archSum(χ, f n)).re := by
    rw [Complex.re_sum]
    exact ((le_max_left _ _).trans (hnw v)).trans
      (Finset.single_le_sum (fun w _ ↦ (le_max_right _ _).trans (hnw w)) (Finset.mem_univ v))
  change M ≤ (archSum(χ, f n) + L).re ∧ (introTraceSpectralSum χ (f n) a - L).re ≤ -M
  change (introTraceSpectralSum χ (f n) a).re ≤ -M - B at hns
  simp only [Complex.add_re, Complex.sub_re]
  constructor <;> linarith [(abs_le.mp hL).1]

open Classical in
/-- Paper: §1.4.3, pp. 28–29. A single smooth family gives two separate holomorphic
limits after transferring the trivial-character archimedean term at two from the
archimedean sum to the spectral sum. Every full critical-strip window has the
same spectral limit on Re z > 1/2. At z = 2 the combined trace fixes the constant;
on Re z > 1 the two limits sum to the polar-corrected finite logarithmic derivative. -/
theorem introTraceApprox_exists_common_counterterm_limits :
    ∃ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ ∧
    ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽), RightInverse τ (ideleClassNorm F) →
    ∀ (χ : U𝔽), (∀ t, χ (τ t) = 1) →
      let L (z : ℂ) := logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0
      let A (z : ℂ) := archSubTrivialSum(χ, z)
      let G (z : ℂ) := (∑' r : windowZeros(χ, (1 / 2 : ℝ)), (zeroOrder(χ, r.val) : ℂ) *
        (1 / (z - (r.val - 1 / 2)) - 1 / (2 - (r.val - 1 / 2)))) + (L 2 - A 2)
      AnalyticOnNhd ℂ A right(-(1 / 2 : ℝ)) ∧
      AnalyticOnNhd ℂ G right(1 / 2) ∧
      TendstoLocallyUniformlyOn (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) -
        archSum((1 : U𝔽), approx(h, ρ, n, (2 : ℂ)))) A atTop right(-(1 / 2 : ℝ)) ∧
      (∀ a : ℝ, 1 / 2 ≤ a → TendstoLocallyUniformlyOn (fun n z ↦
        introTraceSpectralSum χ approx(h, ρ, n, z) a + archSum((1 : U𝔽), approx(h, ρ, n, (2 : ℂ))))
        G atTop right(1 / 2)) ∧
      EqOn (A + G) L right(1) := by
  classical
  obtain ⟨h, ρ, hA, hmatch, hs⟩ := introTraceApprox_exists_reference_spectral_matched (F := F)
  refine ⟨h, ρ, hA, ?_⟩
  intro τ hτ χ hχ L A G
  have hm : MapsTo (fun _ : ℂ ↦ (2 : ℂ)) right(1 / 2) right(1 / 2) := fun z _ ↦ by
    change (1 / 2 : ℝ) < (2 : ℂ).re
    norm_num
  have hR := hs χ (1 / 2) (by norm_num) (fun _ ↦ 2) hm (differentiableOn_const 2)
  have hRa := (introTrace_spectral_referenceSub χ (1 / 2) (fun _ ↦ 2) hm (differentiableOn_const 2)).2.2.2
  have ha := introTraceApprox_archimedean_common_matched_sum χ h ρ hA hmatch
  have hc := introTrace_combined_limit_of_fixed_identity χ h ρ hA
    (introTraceApprox_full_window_fixed_digamma τ hτ χ hχ le_rfl h ρ hA)
  have hz : (2 : ℂ) ∈ right(max (1 / 2 : ℝ) 1) := by change max (1 / 2 : ℝ) 1 < (2 : ℂ).re; norm_num
  have hz' : (2 : ℂ) ∈ right(-(1 / 2 : ℝ)) := by change -(1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  have hbase : Tendsto (fun n ↦ introTraceSpectralSum χ approx(h, ρ, n, (2 : ℂ)) (1 / 2) +
        archSum((1 : U𝔽), approx(h, ρ, n, (2 : ℂ)))) atTop (𝓝 (L 2 - A 2)) := by
    apply ((hc.tendsto_at hz).sub (ha.tendsto_at hz')).congr
    intro n
    ring
  have hhalf : TendstoLocallyUniformlyOn (fun n z ↦ introTraceSpectralSum χ approx(h, ρ, n, z) (1 / 2) +
      archSum((1 : U𝔽), approx(h, ρ, n, (2 : ℂ)))) G atTop right(1 / 2) := by
    have hconst := (hbase.tendstoUniformlyOn_const (s := right(1 / 2))).tendstoLocallyUniformlyOn
    apply (hR.add hconst).congr
    intro n z _
    simp only [Pi.add_apply]
    ring
  refine ⟨Finset.analyticOnNhd_fun_sum _ (fun v _ ↦
    (introTraceApprox_archimedean_common_matched χ v h ρ hA hmatch).2.1), hRa.add analyticOnNhd_const, ha, ?_, ?_⟩
  · intro a hwidth
    apply hhalf.congr
    intro n z _
    dsimp only
    rw [introTrace_full_window_spectral_sum_eq χ _ a hwidth,
      introTrace_full_window_spectral_sum_eq χ _ (1 / 2) le_rfl]
  · intro z hz
    have h₁ : (1 : ℝ) < z.re := hz
    have h₂ : z ∈ right(1 / 2) := by change (1 / 2 : ℝ) < z.re; linarith
    have h₃ : z ∈ right(-(1 / 2 : ℝ)) := by change -(1 / 2 : ℝ) < z.re; linarith
    have h₄ : z ∈ right(max (1 / 2 : ℝ) 1) := by
      change max (1 / 2 : ℝ) 1 < z.re
      exact max_lt h₂ h₁
    apply tendsto_nhds_unique ((ha.tendsto_at h₃).add (hhalf.tendsto_at h₂))
    apply (hc.tendsto_at h₄).congr
    intro n
    ring

open Classical in
/-- The real part of the resolvent at a real point to the right of the window
decays quadratically in the height of its pole. -/
private theorem introTrace_resolvent_real_anchor_summable
    (χ : U𝔽) {a b : ℝ} (hb : a < b) :
    Summable (fun r : windowZeros(χ, a) ↦ ((zeroOrder(χ, r.val) : ℂ) /
      ((b : ℂ) - (r.val - 1 / 2))).re) := by
  let B : ℝ := 1 + (1 + ‖(b : ℂ)‖) / (b - a)
  have hδ : 0 < b - a := sub_pos.mpr hb
  apply Summable.of_norm_bounded ((introTraceApprox_spectral_differentiable_zeroCount χ a).mul_left
    ((|b| + |a|) * B ^ 2))
  intro r
  let p := r.val - 1 / 2
  let m : ℝ := zeroOrder(χ, r.val)
  let W : ℝ := 1 + |r.val.im|
  have hm : 0 < m := Int.cast_pos.mpr r.property.1
  have hor : |p.re| < a := by simpa [p] using r.property.2
  have hsep : b-a ≤ ((b : ℂ) - p).re := by
    rw [Complex.sub_re,Complex.ofReal_re]
    linarith [(abs_lt.mp hor).2]
  have hreal : ((b : ℂ)-p).re ≤ |b|+|a| := by
    rw [Complex.sub_re,Complex.ofReal_re]
    linarith [(abs_lt.mp hor).1,le_abs_self b,le_abs_self a]
  have hinv : 1 / ‖(b : ℂ)-p‖ ≤ B / W := by
    have hh := introTrace_spectral_referenceSub_inv_bound (s := p) (z := (b : ℂ)) hδ
      (by simpa only [Complex.sub_re] using hsep) (le_refl _)
    simpa only [B,W,p,Complex.sub_im,Complex.div_ofNat_im,Complex.one_im,zero_div,sub_zero] using hh
  have hid : ((zeroOrder(χ,r.val) : ℂ) / ((b : ℂ) - p)).re =
      m * ((b : ℂ) - p).re * (1 / ‖(b : ℂ)-p‖)^2 := by
    simp only [Complex.div_re,Complex.intCast_re,Complex.intCast_im,zero_mul,zero_div,add_zero,
      one_div,inv_pow,Complex.sq_norm]
    rfl
  change ‖((zeroOrder(χ,r.val) : ℂ) / ((b : ℂ) - p)).re‖ ≤
    ((|b|+|a|)*B^2) * (m / W^2)
  rw [hid, Real.norm_of_nonneg (mul_nonneg (mul_nonneg hm.le (hδ.le.trans hsep)) (sq_nonneg _))]
  calc
    _ ≤ (m * (|b| + |a|)) * (B / W) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hreal hm.le)
        (pow_le_pow_left₀ (by positivity) hinv 2) (by positivity)
        (mul_nonneg hm.le (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = _ := by rw [div_pow]; ring

open Classical in
/-- Paper: §1.4.3, p. 29. Subtracting only the imaginary part of each resolvent
at a real reference point gives a locally uniformly convergent holomorphic sum.
Its real part is the sum of the original real parts throughout the chart, and
is strictly positive exactly when the window contains a zero. -/
theorem introTrace_resolvent_imaginary_subtraction
    (χ : U𝔽) {a b : ℝ} (hb : a < b) :
    let v (r : windowZeros(χ, a)) (z : ℂ) := (zeroOrder(χ, r.val) : ℂ) / (z - (r.val - 1 / 2))
    let k (r : windowZeros(χ, a)) (z : ℂ) := v r z - ((v r (b : ℂ)).im : ℂ) * Complex.I
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧ (H b).im = 0 ∧
      TendstoLocallyUniformlyOn (fun (T : Finset (windowZeros(χ, a))) z ↦ ∑ r ∈ T, k r z)
        H atTop right(a) ∧
      ∀ z ∈ right(a), HasSum (fun r ↦ (v r z).re) (H z).re ∧
        (0 < (H z).re ↔ Nonempty (windowZeros(χ, a))) := by
  classical
  intro v k
  let d (r : windowZeros(χ, a)) (z : ℂ) := (zeroOrder(χ, r.val) : ℂ) *
    (1 / (z - (r.val - 1 / 2)) - 1 / ((b : ℂ) - (r.val - 1 / 2)))
  let c (r : windowZeros(χ, a)) : ℂ := (v r b).re
  let H (z : ℂ) := (∑' r, d r z) + ∑' r, c r
  have hm : MapsTo (fun _ : ℂ ↦ (b : ℂ)) right(a) right(a) := fun _ _ ↦ hb
  obtain ⟨_, _, hdiff, han⟩ := introTrace_spectral_referenceSub χ a
    (fun _ ↦ (b : ℂ)) hm (differentiableOn_const _)
  have hc : Summable c := Complex.summable_ofReal.mpr (introTrace_resolvent_real_anchor_summable χ hb)
  have hd (r : windowZeros(χ, a)) (z : ℂ) : d r z + c r = k r z := by
    have he : d r z = v r z - v r b := by dsimp [d,v]; ring
    rw [he]
    dsimp only [c,k]
    linear_combination Complex.re_add_im (v r b)
  have hlim : TendstoLocallyUniformlyOn
      (fun (T : Finset (windowZeros(χ,a))) z ↦ ∑ r ∈ T, k r z) H atTop right(a) := by
    apply (hdiff.add (hc.hasSum.tendstoUniformlyOn_const (s := right(a))).tendstoLocallyUniformlyOn).congr
    intro T z _
    change (∑ r ∈ T, d r z) + (∑ r ∈ T, c r) = _
    simp only [← Finset.sum_add_distrib,hd]
  refine ⟨H,han.add analyticOnNhd_const,?_,hlim,?_⟩
  · have he : ((∑' r, (v r b).re : ℝ) : ℂ) = ∑' r, ((v r b).re : ℂ) := Complex.ofReal_tsum _
    dsimp [H,d]
    simp only [sub_self,mul_zero,tsum_zero,Complex.zero_im,zero_add]
    change (∑' r, ((v r b).re : ℂ)).im = 0
    rw [← he,Complex.ofReal_im]
  intro z hz
  have hs : HasSum (fun r ↦ k r z) (H z) := hlim.tendsto_at hz
  have hre : HasSum (fun r ↦ (v r z).re) (H z).re := by
    simpa only [k,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,sub_zero] using Complex.hasSum_re hs
  refine ⟨hre,?_⟩
  constructor
  · intro hpos
    by_contra he
    let _ : IsEmpty (windowZeros(χ,a)) := not_nonempty_iff.mp he
    have h := hre.tsum_eq
    simp only [tsum_empty] at h
    linarith
  · rintro ⟨r₀⟩
    have hpos (r : windowZeros(χ,a)) : 0 < (v r z).re := by
      let p := r.val-1/2
      have hp : p.re < a := by simpa [p] using (abs_lt.mp r.property.2).2
      have hx : 0 < (z-p).re := by rw [Complex.sub_re]; exact sub_pos.mpr (hp.trans hz)
      have hne : z-p ≠ 0 := fun e ↦ hx.ne' (congrArg Complex.re e)
      have hd := Int.cast_pos (R := ℝ) |>.mpr r.property.1
      change 0 < ((zeroOrder(χ,r.val) : ℂ)/(z-p)).re
      simp only [Complex.div_re,Complex.intCast_re,Complex.intCast_im,zero_mul,zero_div,add_zero]
      exact div_pos (mul_pos hd hx) (Complex.normSq_pos.mpr hne)
    rw [← hre.tsum_eq]
    exact hre.summable.tsum_pos (fun r ↦ (hpos r).le) r₀ (hpos r₀)

open Classical in
/-- There are finitely many window zeros below any fixed absolute imaginary height.
The resulting finite sets exhaust the window. -/
private theorem introTrace_window_zeros_height_exhaustion (χ : U𝔽) (a : ℝ) :
    ∃ T : ℝ → Finset (windowZeros(χ,a)),
      (∀ t r, r ∈ T t ↔ |r.val.im| ≤ t) ∧ Tendsto T atTop atTop := by
  classical
  have hfin (t : ℝ) : {r : windowZeros(χ,a) | |r.val.im| ≤ t}.Finite := by
    have ht : 0 < 1 / (1+|t|)^2 := by positivity
    have he := (introTraceApprox_spectral_differentiable_zeroCount χ a).tendsto_cofinite_zero.eventually
      (gt_mem_nhds ht)
    apply (Filter.mem_cofinite.mp he).subset
    intro r hr
    change ¬ (zeroOrder(χ,r.val) : ℝ) / (1+|r.val.im|)^2 < 1/(1+|t|)^2
    apply not_lt.mpr
    have hd : (1 : ℝ) ≤ zeroOrder(χ,r.val) := by exact_mod_cast Int.add_one_le_iff.mpr r.property.1
    have hi : |r.val.im| ≤ |t| := (show |r.val.im| ≤ t from hr).trans (le_abs_self t)
    exact div_le_div₀ (zero_le_one.trans hd) hd (by positivity) (by gcongr)
  let T (t : ℝ) := (hfin t).toFinset
  have hT (t : ℝ) (r : windowZeros(χ,a)) : r ∈ T t ↔ |r.val.im| ≤ t := Set.Finite.mem_toFinset _
  refine ⟨T,hT,tendsto_atTop.mpr fun U ↦ ?_⟩
  induction U using Finset.induction_on with
  | empty => exact Eventually.of_forall fun _ ↦ Finset.empty_subset _
  | insert r U hr ih =>
    filter_upwards [ih,eventually_ge_atTop |r.val.im|] with t hU ht
    exact Finset.insert_subset ((hT t r).mpr ht) hU

open scoped ComplexConjugate in
open Classical in
/-- Conjugating a positive zero of a completed Hecke character gives a zero
of the inverse character with the same multiplicity. -/
private theorem introTrace_inverse_character_conj_divisor (χ : U𝔽)
    (s : ℂ) (hs : 0 < zeroOrder(χ,s)) :
    zeroOrder(χ⁻¹, conj s) = zeroOrder(χ,s) := by
  have hp := (abs_lt.mp (introTrace_positive_divisor_in_critical_strip χ s hs)).1
  have hsre : 0 < s.re := by linarith
  have he := introTrace_finite_conj_order χ (conj s)
  rw [Complex.conj_conj] at he
  rw [introTrace_normalized_finite_order_eq_completed χ⁻¹ (conj s) hsre,
    introTrace_normalized_finite_order_eq_completed χ s hsre] at he
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec _).1.meromorphicOn (mem_univ _),
    MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec _).1.meromorphicOn (mem_univ _),he]

open scoped ComplexConjugate in
open Classical in
/-- For a character and its inverse the imaginary anchor terms cancel across
the two symmetric height truncations, with their multiplicities. -/
private theorem introTrace_dual_finite_height_balance
    (χ : U𝔽) (a b t : ℝ) (T : Finset (windowZeros(χ,a))) (U : Finset (windowZeros(χ⁻¹,a)))
    (hT : ∀ r, r ∈ T ↔ |r.val.im| ≤ t) (hU : ∀ r, r ∈ U ↔ |r.val.im| ≤ t) :
    (∑ r ∈ T, ((zeroOrder(χ,r.val) : ℂ)/((b : ℂ)-(r.val-1/2))).im) +
    (∑ r ∈ U, ((zeroOrder(χ⁻¹,r.val) : ℂ)/((b : ℂ)-(r.val-1/2))).im) = 0 := by
  classical
  let v (η : U𝔽) (r : windowZeros(η,a)) := (zeroOrder(η,r.val) : ℂ)/((b : ℂ)-(r.val-1/2))
  have ho (r : windowZeros(χ,a)) := introTrace_inverse_character_conj_divisor χ r.val r.property.1
  have hi (r : windowZeros(χ⁻¹,a)) : zeroOrder(χ,conj r.val) = zeroOrder(χ⁻¹,r.val) := by
    simpa only [inv_inv] using introTrace_inverse_character_conj_divisor χ⁻¹ r.val r.property.1
  let e : windowZeros(χ,a) ≃ windowZeros(χ⁻¹,a) :=
    { toFun := fun r ↦ ⟨conj r.val, (ho r).symm ▸ r.property.1, r.property.2⟩
      invFun := fun r ↦ ⟨conj r.val, (hi r).symm ▸ r.property.1, r.property.2⟩
      left_inv := fun r ↦ Subtype.ext (Complex.conj_conj r.val)
      right_inv := fun r ↦ Subtype.ext (Complex.conj_conj r.val) }
  have hmem (r : windowZeros(χ,a)) : r ∈ T ↔ e r ∈ U := by
    rw [hT r,hU (e r)]
    simp [e]
  have hv (r : windowZeros(χ,a)) : v χ⁻¹ (e r) = conj (v χ r) := by
    dsimp [v,e]
    rw [ho r]
    have htwo : conj (2 : ℂ) = 2 := by
      rw [show (2 : ℂ) = 1+1 by norm_num,map_add,map_one]
    simp [htwo]
  have hsum : (∑ r ∈ T, (v χ r).im) = ∑ r ∈ U, -(v χ⁻¹ r).im := by
    apply Finset.sum_equiv e hmem
    intro r _
    rw [hv,Complex.conj_im,neg_neg]
  rw [Finset.sum_neg_distrib] at hsum
  exact add_eq_zero_iff_eq_neg.mpr hsum

open Classical in
/-- The two imaginary anchor corrections cancel in each common height cutoff;
a locally uniform limit for each compensated series thus gives the ordinary
joint height limit for a character and its inverse. -/
private theorem introTrace_dual_height_truncation (a : ℝ) :
    let v (η : U𝔽) (r : windowZeros(η,a)) (z : ℂ) := (zeroOrder(η,r.val) : ℂ)/(z-(r.val-1/2))
    let k (η : U𝔽) (b : ℝ) (r : windowZeros(η,a)) (z : ℂ) :=
      v η r z - ((v η r b).im : ℂ)*Complex.I
    ∃ T : (η : U𝔽) → ℝ → Finset (windowZeros(η,a)), (∀ η t r, r ∈ T η t ↔ |r.val.im| ≤ t) ∧
      ∀ (χ : U𝔽) (b : ℝ) (H J : ℂ → ℂ),
        TendstoLocallyUniformlyOn (fun (U : Finset (windowZeros(χ,a))) z ↦ ∑ r ∈ U, k χ b r z) H atTop right(a) →
        TendstoLocallyUniformlyOn (fun (U : Finset (windowZeros(χ⁻¹,a))) z ↦ ∑ r ∈ U, k χ⁻¹ b r z) J atTop right(a) →
        (∀ x t : ℝ, (∑ r ∈ T χ t, (v χ r x).im) + (∑ r ∈ T χ⁻¹ t, (v χ⁻¹ r x).im) = 0) ∧
        TendstoLocallyUniformlyOn (fun t z ↦ (∑ r ∈ T χ t, v χ r z) + ∑ r ∈ T χ⁻¹ t, v χ⁻¹ r z)
          (fun z ↦ H z + J z) atTop right(a) := by
  classical
  intro v k
  choose T hT hcof using (fun η : U𝔽 ↦ introTrace_window_zeros_height_exhaustion η a)
  refine ⟨T,hT,?_⟩
  intro χ b H J hH hJ
  let c (η : U𝔽) (r : windowZeros(η,a)) := (v η r b).im
  have hc (η : U𝔽) (Q : ℂ → ℂ)
      (hQ : TendstoLocallyUniformlyOn (fun (U : Finset (windowZeros(η,a))) z ↦ ∑ r ∈ U, k η b r z) Q atTop right(a)) :
      TendstoLocallyUniformlyOn (fun t z ↦ ∑ r ∈ T η t, (v η r z - (c η r : ℂ)*Complex.I)) Q atTop right(a) := by
    intro u hu z hz
    obtain ⟨neighborhood,hV,hU⟩ := hQ u hu z hz
    exact ⟨neighborhood,hV,(hcof η).eventually hU⟩
  have hzero (x t : ℝ) : (∑ r ∈ T χ t, (v χ r x).im) + (∑ r ∈ T χ⁻¹ t, (v χ⁻¹ r x).im) = 0 :=
    introTrace_dual_finite_height_balance χ a x t _ _ (hT χ t) (hT χ⁻¹ t)
  refine ⟨hzero,?_⟩
  apply ((hc χ H hH).add (hc χ⁻¹ J hJ)).congr
  intro t z _
  simp only [Pi.add_apply, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum]
  have hb : (((∑ r ∈ T χ t, c χ r) : ℝ) : ℂ) +
      (((∑ r ∈ T χ⁻¹ t, c χ⁻¹ r) : ℝ) : ℂ) = 0 := by exact_mod_cast hzero b t
  linear_combination -Complex.I * hb

open Classical in
/-- Paper: §1.4.3, p. 29. For every character, the ordinary symmetric-height
resolvent sums for the character and its inverse converge jointly. The limit
is holomorphic and real on the real axis, and its real part is the sum of the
two unmodified real resolvent series. -/
theorem introTrace_dual_resolvent_height_limit (a : ℝ) :
    let v (η : U𝔽) (r : windowZeros(η,a)) (z : ℂ) := (zeroOrder(η,r.val) : ℂ)/(z-(r.val-1/2))
    ∃ T : (η : U𝔽) → ℝ → Finset (windowZeros(η,a)),
      (∀ η t r, r ∈ T η t ↔ |r.val.im| ≤ t) ∧ ∀ χ : U𝔽, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H right(a) ∧ TendstoLocallyUniformlyOn (fun t z ↦
        (∑ r ∈ T χ t, v χ r z) + ∑ r ∈ T χ⁻¹ t, v χ⁻¹ r z) H atTop right(a) ∧
      (∀ x : ℝ, a < x → (H x).im = 0) ∧ ∀ z ∈ right(a),
        (H z).re = (∑' r, (v χ r z).re) + ∑' r, (v χ⁻¹ r z).re := by
  classical
  intro v
  let b := a+1
  obtain ⟨T,hT,hjoint⟩ := introTrace_dual_height_truncation (F := F) a
  choose H han hreal hlim hpos using (fun η : U𝔽 ↦
    introTrace_resolvent_imaginary_subtraction η (b := b) (show a < b by dsimp [b]; linarith))
  refine ⟨T,hT,fun χ ↦ ?_⟩
  let L (z : ℂ) := H χ z + H χ⁻¹ z
  obtain ⟨hzero,hbare⟩ := hjoint χ b (H χ) (H χ⁻¹) (hlim χ) (hlim χ⁻¹)
  refine ⟨L,(han χ).add (han χ⁻¹),hbare,?_,?_⟩
  · intro x hx
    have hin := Complex.continuous_im.continuousAt.tendsto.comp (hbare.tendsto_at (a := (x : ℂ)) hx)
    have hconst : Tendsto (fun t : ℝ ↦ ((∑ r ∈ T χ t, v χ r x) +
        ∑ r ∈ T χ⁻¹ t, v χ⁻¹ r x).im) atTop (𝓝 0) := by
      have hconst (t : ℝ) : ((∑ r ∈ T χ t, v χ r x) + ∑ r ∈ T χ⁻¹ t, v χ⁻¹ r x).im = 0 := by
        rw [Complex.add_im,Complex.im_sum,Complex.im_sum]
        exact hzero x t
      simpa only [hconst] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique hin hconst
  · intro z hz
    exact congrArg₂ (· + ·) (hpos χ z hz).1.tsum_eq.symm (hpos χ⁻¹ z hz).1.tsum_eq.symm

open Classical in
/-- Along symmetric height truncations a self-dual character's imaginary parts
cancel at every real anchor. The compensated finite sums therefore have exactly
the same locally uniform limit as the bare finite sums. -/
private theorem introTrace_selfdual_height_truncation (χ : U𝔽) (hχ : χ⁻¹ = χ) (a : ℝ) :
    let v (r : windowZeros(χ,a)) (z : ℂ) := (zeroOrder(χ,r.val) : ℂ)/(z-(r.val-1/2))
    ∃ T : ℝ → Finset (windowZeros(χ,a)), (∀ t r, r ∈ T t ↔ |r.val.im| ≤ t) ∧
      (∀ x t : ℝ, ∑ r ∈ T t, (v r x).im = 0) ∧ ∀ (b : ℝ) (H : ℂ → ℂ),
      TendstoLocallyUniformlyOn (fun (U : Finset (windowZeros(χ,a))) z ↦
        ∑ r ∈ U, (v r z - ((v r b).im : ℂ)*Complex.I)) H atTop right(a) →
      TendstoLocallyUniformlyOn (fun t z ↦ ∑ r ∈ T t, v r z) H atTop right(a) := by
  classical
  intro v
  obtain ⟨T,hT,hcof⟩ := introTrace_window_zeros_height_exhaustion χ a
  have hzero (x t : ℝ) : ∑ r ∈ T t, (v r x).im = 0 := by
    have hpair := introTrace_dual_finite_height_balance χ a x t (T t)
    rw [hχ] at hpair
    have he := hpair (T t) (hT t) (hT t)
    change (∑ r ∈ T t, (v r x).im) + (∑ r ∈ T t, (v r x).im) = 0 at he
    linarith
  refine ⟨T,hT,hzero,?_⟩
  intro b H hlim
  have hfinite (t : ℝ) (z : ℂ) :
      (∑ r ∈ T t, (v r z - ((v r b).im : ℂ) * Complex.I)) = ∑ r ∈ T t, v r z := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, hzero b t]
    simp
  intro u hu z hz
  obtain ⟨neighborhood,hV,hU⟩ := hlim u hu z hz
  refine ⟨neighborhood,hV,?_⟩
  filter_upwards [hcof.eventually hU] with t ht
  intro y hy
  simpa only [← hfinite t y] using ht y hy

open Classical in
/-- Paper: §1.4.3, p. 29. For self-dual characters the ordinary resolvent sums
over symmetric height truncations converge locally uniformly. Their holomorphic
limit is real on the real axis and has positive real part wherever the window
is nonempty. -/
theorem introTrace_selfdual_resolvent_height_limit
    (χ : U𝔽) (hχ : χ⁻¹ = χ) (a : ℝ) :
    let v (r : windowZeros(χ,a)) (z : ℂ) := (zeroOrder(χ,r.val) : ℂ)/(z-(r.val-1/2))
    ∃ (T : ℝ → Finset (windowZeros(χ,a))) (H : ℂ → ℂ),
      (∀ t r, r ∈ T t ↔ |r.val.im| ≤ t) ∧ AnalyticOnNhd ℂ H right(a) ∧
      TendstoLocallyUniformlyOn (fun t z ↦ ∑ r ∈ T t, v r z) H atTop right(a) ∧
      (∀ x : ℝ, a < x → (H x).im = 0) ∧
      ∀ z ∈ right(a), HasSum (fun r ↦ (v r z).re) (H z).re ∧
        (0 < (H z).re ↔ Nonempty (windowZeros(χ,a))) := by
  classical
  intro v
  let b := a + 1
  obtain ⟨T,hT,hzero,htrunc⟩ := introTrace_selfdual_height_truncation χ hχ a
  obtain ⟨H,hH,_,hlim,hpos⟩ := introTrace_resolvent_imaginary_subtraction χ (b := b)
    (show a < b by dsimp [b]; linarith)
  have hbare := htrunc b H hlim
  refine ⟨T,H,hT,hH,hbare,?_,hpos⟩
  intro x hx
  have hin := Complex.continuous_im.continuousAt.tendsto.comp (hbare.tendsto_at (a := (x : ℂ)) hx)
  have hconst : Tendsto (fun t : ℝ ↦ (∑ r ∈ T t, v r x).im) atTop (𝓝 0) := by
    have hz (t : ℝ) : (∑ r ∈ T t, v r x).im = 0 := by
      rw [Complex.im_sum]; exact hzero x t
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hin hconst

open Classical in
/-- Paper: §1.4.3, p. 29. The two orders of taking the real spectral limit at
parameter two differ for every number field, character and admissible family.
Removing the cutoff on finite sets first gives a strictly positive sum. Summing
the absolutely convergent series at each cutoff first gives negative infinity. -/
theorem introTrace_real_spectral_iterated_limits
    (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ) :
    let E := windowZeros(χ, 1/2)
    let v (r : E) := (zeroOrder(χ,r.val) : ℂ) / (2 - (r.val - 1/2))
    let g (n : ℕ) (r : E) := (zeroOrder(χ,r.val) : ℂ) *
      introTraceMellin approx(h,ρ,n,(2:ℂ)) (r.val - 1/2)
    ∃ R : ℝ, 0 < R ∧
      (∀ T : Finset E, Tendsto (fun n ↦ ∑ r ∈ T, (g n r).re) atTop
        (𝓝 (∑ r ∈ T, (v r).re))) ∧ HasSum (fun r ↦ (v r).re) R ∧
      (∀ n, HasSum (fun r ↦ (g n r).re) (introTraceSpectralSum χ approx(h,ρ,n,(2:ℂ)) (1/2)).re) ∧
      Tendsto (fun n ↦ (introTraceSpectralSum χ approx(h,ρ,n,(2:ℂ)) (1/2)).re) atTop atBot := by
  classical
  intro E v g
  have hfull := introTraceApprox_full_window_spectral_tendsto_atBot χ h ρ hA (1/2) le_rfl
  have he : Nonempty E := by
    by_contra hempty
    let _ : IsEmpty (windowZeros(χ,1/2)) := not_nonempty_iff.mp hempty
    obtain ⟨n,hn⟩ := (tendsto_atBot.mp hfull (-1)).exists
    norm_num [introTraceSpectralSum] at hn
  obtain ⟨H,_,_,_,hs⟩ := introTrace_resolvent_imaginary_subtraction χ (a := 1/2) (b := 2) (by norm_num)
  obtain ⟨hR,hpos⟩ := hs 2 (by change (1/2:ℝ) < (2:ℂ).re; norm_num)
  refine ⟨(H 2).re,hpos.mpr he,?_,hR,?_,hfull⟩
  · intro T
    apply tendsto_finsetSum
    intro r _
    have hsep : (r.val - 1/2).re < (2:ℂ).re := by
      have h₁ : (r.val-1/2).re < 1/2 := by simpa using (abs_lt.mp r.property.2).2
      exact h₁.trans (by norm_num)
    have hM := (introTraceApprox_mellin_tendsto h ρ hA (r.val-1/2)).tendsto_at (a := (2:ℂ)) hsep
    rw [(introTracePower_mellin (2:ℂ) (r.val-1/2) hsep).2] at hM
    have hterm := Complex.continuous_re.continuousAt.tendsto.comp (hM.const_mul (zeroOrder(χ,r.val):ℂ))
    simpa only [g,v,mul_one_div,Function.comp_def] using hterm
  · intro n
    exact Complex.hasSum_re (introTraceApprox_spectral_summable χ h ρ hA n (1/2) (by norm_num) 2).hasSum

section CompletedSpectralContinuation

open Classical

local notation "completedSpectral(" χ ", " z ")" =>
  (logDeriv (continuedCompletedHeckeL (F := F) χ) ((z : ℂ) + 1 / 2) +
    (if χ = (1 : U𝔽) then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) -
    logDeriv (heckeGammaFactor (1 : U𝔽)) (5 / 2))

/-- In the shifted Euler half-plane each term of the renormalized completed logarithmic
derivative is analytic. -/
private theorem introTrace_completed_spectral_analytic (χ : U𝔽) :
    AnalyticOnNhd ℂ (fun z ↦ completedSpectral(χ, z)) right(1 / 2) := by
  classical
  intro z hz
  change (1 / 2 : ℝ) < z.re at hz
  have hs : 1 < (z + 1 / 2).re := by norm_num; linarith
  obtain ⟨hΛ, he⟩ := continuedCompletedHeckeL_spec χ
  have hn : continuedCompletedHeckeL χ (z + 1 / 2) ≠ 0 := by
    rw [he ⟨_, hs⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hs))
      (finiteHeckeL_ne_zero_of_one_lt_re χ _)
  have hnormal := hΛ (mem_univ (z + 1 / 2))
  have hΛa := hnormal.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (hnormal.meromorphicOrderAt_eq_zero_iff.mpr hn).ge
  have ha := (hΛa.deriv.div hΛa hn).comp (f := fun w : ℂ ↦ w + 1 / 2) (x := z) (by fun_prop)
  have hp : z + 1 / 2 ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hm : z - 1 / 2 ≠ 0 := by intro h; rw [sub_eq_zero.mp h] at hz; norm_num at hz
  apply AnalyticAt.sub _ analyticAt_const
  apply ha.add
  split_ifs
  · have hplus : AnalyticAt ℂ (fun w : ℂ ↦ w + 1 / 2) z := by fun_prop
    have hminus : AnalyticAt ℂ (fun w : ℂ ↦ w - 1 / 2) z := by fun_prop
    have hone : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) z := analyticAt_const
    exact (hone.div hplus hp).add (hone.div hminus hm)
  · exact analyticAt_const

/-- A logarithmic derivative has principal part equal to the order divided by the
local coordinate. This also covers a locally zero meromorphic function. -/
private theorem introTrace_logDeriv_principalPart {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ logDeriv f =ᶠ[𝓝[≠] p]
      fun z ↦ ((meromorphicOrderAt f p).untop₀ : ℂ) / (z - p) + g z := by
  by_cases ht : meromorphicOrderAt f p = ⊤
  · refine ⟨0, analyticAt_const, ?_⟩
    filter_upwards [logDeriv_congr_nhdsNE (meromorphicOrderAt_eq_top_iff.mp ht)] with z hz
    simpa [ht, logDeriv, Pi.div_apply] using hz
  obtain ⟨g, hg, hgp, he⟩ := (meromorphicOrderAt_ne_top_iff hf).mp ht
  set n := (meromorphicOrderAt f p).untop₀
  refine ⟨logDeriv g, hg.deriv.div hg hgp, ?_⟩
  filter_upwards [logDeriv_congr_nhdsNE he, (hg.continuousAt.eventually_ne hgp).filter_mono nhdsWithin_le_nhds,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hgz hga hzp
  have hd := sub_ne_zero.mpr hzp
  have hpow := logDeriv_comp (f := fun w : ℂ ↦ w ^ n) (g := fun w : ℂ ↦ w - p) (x := z)
    (differentiableAt_zpow.mpr (Or.inl hd)) (differentiableAt_id.sub_const p)
  simp only [Function.comp_def, logDeriv_zpow, deriv_sub_const, deriv_id'', mul_one] at hpow
  simp only [smul_eq_mul] at hz
  rw [hz, ← hpow]
  exact logDeriv_fun_mul z (zpow_ne_zero n hd) hgz
    ((differentiableAt_id.sub_const p).zpow (Or.inl hd)) hga.differentiableAt

/-- The polar correction with pole at a fixed point contributes residue one precisely there. -/
private theorem introTrace_reciprocal_principalPart (a p : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ z : ℂ,
      1 / (z - a) = (if p = a then 1 else 0) / (z - p) + g z := by
  by_cases h : p = a
  · exact ⟨0, analyticAt_const, by simp [h]⟩
  · have hone : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) p := analyticAt_const
    have hsub : AnalyticAt ℂ (fun z : ℂ ↦ z - a) p := by fun_prop
    exact ⟨fun z ↦ 1 / (z - a), hone.div hsub (sub_ne_zero.mpr h), by simp [h]⟩

/-- Adding the two polar corrections in the normalized trivial chart cancels its
simple poles at zero and one. In every chart the remaining residues are the
positive part of the completed divisor. -/
private theorem introTrace_completed_spectral_principalPart
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (p : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ (fun z ↦ completedSpectral(χ, z)) =ᶠ[𝓝[≠] p]
      fun z ↦ (max zeroOrder(χ, p + 1 / 2) 0 : ℤ) / (z - p) + g z := by
  classical
  let s := p + 1 / 2
  let m := zeroOrder(χ, s)
  have hΛ := (continuedCompletedHeckeL_spec χ).1
  obtain ⟨g, hg, he⟩ := introTrace_logDeriv_principalPart (hΛ (mem_univ s)).meromorphicAt
  have ht : Tendsto (fun w : ℂ ↦ w + 1 / 2) (𝓝[≠] p) (𝓝[≠] s) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuousAt_id.add_const _).continuousWithinAt,
      ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact fun h ↦ hz (add_right_cancel h)
  have he' : (fun z : ℂ ↦ logDeriv (continuedCompletedHeckeL χ) (z + 1 / 2)) =ᶠ[𝓝[≠] p]
      fun z ↦ (m : ℂ) / (z - p) + g (z + 1 / 2) := by
    filter_upwards [ht.eventually he] with z hz
    simpa [m, MeromorphicOn.divisor_apply hΛ.meromorphicOn (mem_univ s), s] using hz
  have hgt := hg.comp (f := fun z : ℂ ↦ z + 1 / 2) (x := p) (by fun_prop)
  set c := logDeriv (heckeGammaFactor (1 : U𝔽)) (5 / 2)
  by_cases hc : χ = 1
  · obtain ⟨u, hu, heu⟩ := introTrace_reciprocal_principalPart (-(1 / 2)) p
    obtain ⟨v, hv, hev⟩ := introTrace_reciprocal_principalPart (1 / 2) p
    refine ⟨fun z ↦ g (z + 1 / 2) + u z + v z - c, ((hgt.add hu).add hv).sub analyticAt_const, ?_⟩
    have hm : m + (if p = -(1 / 2) then 1 else 0) + (if p = 1 / 2 then 1 else 0) = max m 0 := by
      obtain ⟨h₀, h₁⟩ := idelicExplicitFormula_trivial_poles (F := F)
      by_cases h : p = -(1 / 2)
      · have hs : s = 0 := by dsimp [s]; rw [h]; ring
        have hm : m = -1 := by dsimp only [m]; rw [hc, hs]; exact h₀
        have hn : p ≠ 1 / 2 := by rw [h]; norm_num
        rw [ite_eq_left h, ite_eq_right hn, hm]; decide
      by_cases h' : p = 1 / 2
      · have hs : s = 1 := by dsimp [s]; rw [h']; norm_num
        have hm : m = -1 := by dsimp only [m]; rw [hc, hs]; exact h₁
        rw [ite_eq_right h, ite_eq_left h', hm]; decide
      have hm : 0 ≤ m := by
        by_contra! hn
        obtain ⟨_, hs | hs⟩ := idelicExplicitFormula_chart_poles τ hτ χ hχ s hn
        · exact h (by dsimp [s] at hs; linear_combination hs)
        · exact h' (by dsimp [s] at hs; linear_combination hs)
      rw [ite_eq_right h, ite_eq_right h', max_eq_left hm]; omega
    have hmc := congrArg (fun x : ℤ ↦ (x : ℂ)) hm
    push_cast at hmc
    filter_upwards [he'] with z hz
    rw [hz, ite_eq_left hc, ← sub_neg_eq_add z (1 / 2), heu z, hev z]
    change _ = (max m 0 : ℤ) / (z - p) + _
    rw [← hmc]
    ring
  · have hm : 0 ≤ m := by
      by_contra! hn
      exact hc (idelicExplicitFormula_chart_poles τ hτ χ hχ s hn).1
    refine ⟨fun z ↦ g (z + 1 / 2) - c, hgt.sub analyticAt_const, ?_⟩
    filter_upwards [he'] with z hz
    rw [hz, ite_eq_right hc]
    change _ = (max m 0 : ℤ) / (z - p) + _
    rw [max_eq_left hm]
    ring

/-- Circle residues depend only on the germ on a punctured neighborhood. -/
private theorem introTrace_complexResidue_congr {f g : ℂ → ℂ} {p : ℂ}
    (he : f =ᶠ[𝓝[≠] p] g) : complexResidue f p = complexResidue g p := by
  obtain ⟨R, hR, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  unfold complexResidue Filter.limUnder
  apply congrArg Filter.lim
  apply Filter.map_congr
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  congr 1
  apply circleIntegral.integral_congr hr.1.le
  intro z hz
  have hd := Metric.mem_sphere.mp hz
  refine hEq ⟨Metric.mem_ball.mpr (hd.trans_lt hr.2), mem_compl_singleton_iff.mpr ?_⟩
  rintro rfl
  exact hr.1.ne (by simpa using hd)

/-- Paper: §1.4.3, p. 29, and §B.4.2, pp. 614–615. Take the logarithmic derivative of
the completed Hecke function at `z + 1/2`, add the two polar fractions for the trivial
character, and subtract the trivial gamma logarithmic derivative at `5/2`. Its meromorphic
normal form agrees with this expression on `Re z > 1/2`. Its poles are simple, exactly at
the translated positive-order zeros, and the circle residues are the multiplicities.
The trivial chart's completed poles at zero and one cancel. -/
theorem introTrace_completed_logDeriv_poles_residues
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) :
    let R := toMeromorphicNFOn (fun z ↦ completedSpectral(χ, z)) univ
    MeromorphicNFOn R univ ∧ EqOn R (fun z ↦ completedSpectral(χ, z)) right(1 / 2) ∧
      ∀ p : ℂ, (AnalyticAt ℂ R p ↔ zeroOrder(χ, p + 1 / 2) ≤ 0) ∧
        (0 < zeroOrder(χ, p + 1 / 2) → meromorphicOrderAt R p = -1) ∧
        complexResidue R p = (max zeroOrder(χ, p + 1 / 2) 0 : ℤ) := by
  classical
  let H := fun z ↦ completedSpectral(χ, z)
  have herr := introTrace_completed_spectral_principalPart τ hτ χ hχ
  have hmer : MeromorphicOn H univ := by
    intro p _
    obtain ⟨g, hg, he⟩ := herr p
    apply MeromorphicAt.congr _ he.symm
    have hn : MeromorphicAt (fun _ : ℂ ↦ ((max zeroOrder(χ, p + 1/2) 0 : ℤ) : ℂ)) p := by fun_prop
    have hd : MeromorphicAt (fun z : ℂ ↦ z - p) p := by fun_prop
    exact (hn.div hd).add hg.meromorphicAt
  intro R
  have hnf : MeromorphicNFOn R univ := meromorphicNFOn_toMeromorphicNFOn _ _
  refine ⟨hnf, fun z hz ↦ ?_, fun p ↦ ?_⟩
  · exact (toMeromorphicNFOn_eq_toMeromorphicNFAt hmer (mem_univ z)).trans
      (congrFun (toMeromorphicNFAt_eq_self.mpr ((introTrace_completed_spectral_analytic χ z hz).meromorphicNFAt)) z)
  · let m := zeroOrder(χ, p + 1 / 2)
    let c : ℂ := (max m 0 : ℤ)
    obtain ⟨g, hg, he⟩ := herr p
    have he' : R =ᶠ[𝓝[≠] p] fun z ↦ c / (z - p) + g z :=
      (hmer.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ p)).trans he
    let B := fun z : ℂ ↦ c + (z - p) * g z
    have hB : AnalyticAt ℂ B p := analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hg)
    have hBp : B p = c := by simp [B]
    have hfrac : R =ᶠ[𝓝[≠] p] fun z ↦ B z / (z - p) := by
      filter_upwards [he', self_mem_nhdsWithin] with z hz hzp
      rw [hz]
      dsimp only [B]
      field_simp [sub_ne_zero.mpr hzp]
    have hpole (h : 0 < m) : meromorphicOrderAt R p = -1 := by
      have hc : c ≠ 0 := by
        dsimp [c]; rw [max_eq_left h.le]; exact_mod_cast h.ne'
      apply (meromorphicOrderAt_eq_int_iff (n := -1) (hnf (mem_univ p)).meromorphicAt).mpr
      refine ⟨B, hB, hBp ▸ hc, ?_⟩
      filter_upwards [hfrac] with z hz
      simpa [zpow_neg_one, smul_eq_mul, div_eq_inv_mul] using hz
    refine ⟨⟨fun ha ↦ ?_, fun hn ↦ ?_⟩, hpole, (introTrace_complexResidue_congr hfrac).trans
      ((complexResidue_div_sub hB).trans hBp)⟩
    · by_contra! hp
      have hoch := ha.meromorphicOrderAt_nonneg
      rw [hpole hp] at hoch
      exact (by decide : ¬ (0 : WithTop ℤ) ≤ -1) hoch
    · have hc : c = 0 := by simp [c, max_eq_right (show m ≤ 0 from hn)]
      have he₀ : R =ᶠ[𝓝[≠] p] g := by simpa [hc] using he'
      apply (hnf (mem_univ p)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_congr he₀]
      exact hg.meromorphicOrderAt_nonneg

/-- On the Euler half-plane the completed logarithmic derivative splits into the
logarithmic derivatives of the gamma factor and the finite continuation. -/
private theorem introTrace_completed_logDeriv_euler (χ : U𝔽) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (continuedCompletedHeckeL χ) s =
      logDeriv (heckeGammaFactor χ) s + logDeriv finiteL(χ) s := by
  have hΛeq := (continuedCompletedHeckeL_spec χ).2
  obtain ⟨hL, hLeq⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have he : continuedCompletedHeckeL χ =ᶠ[𝓝 s] fun w ↦ heckeGammaFactor χ w * finiteL(χ) w := by
    filter_upwards [(isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (show s ∈ right(1) from hs)] with w hw
    rw [hΛeq ⟨w, hw⟩, hLeq ⟨w, hw⟩]
    rfl
  have hG := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hs)
  have hF : finiteL(χ) s ≠ 0 := by
    rw [hLeq ⟨s, hs⟩]
    exact finiteHeckeL_ne_zero_of_one_lt_re χ _
  have hfa := (hL (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((hL (mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr hF).ge
  exact (logDeriv_congr_nhds he).eq_of_nhds.trans (logDeriv_fun_mul s hG hF
    (differentiableAt_heckeGammaFactor_of_re_pos χ (zero_lt_one.trans hs)) hfa.differentiableAt)

/-- On the shifted Euler half-plane the full reference-difference series, normalized
at two, equals the corrected completed logarithmic derivative. -/
private theorem introTrace_full_reference_series_eq_completed_logDeriv
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) :
    let L (z : ℂ) := logDeriv finiteL(χ) (z + 1 / 2) +
      if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0
    let A (z : ℂ) := archSubTrivialSum(χ, z)
    EqOn (fun z ↦ (∑' r : windowZeros(χ, (1 / 2 : ℝ)), (zeroOrder(χ, r.val) : ℂ) *
      (1 / (z - (r.val - 1 / 2)) - 1 / (2 - (r.val - 1 / 2)))) + (L 2 - A 2))
      (fun z ↦ completedSpectral(χ, z)) right(1 / 2) := by
  classical
  obtain ⟨_, _, _, hmatch⟩ := introTraceApprox_exists_common_counterterm_limits (F := F)
  obtain ⟨_, hG, _, _, hsum⟩ := hmatch τ hτ χ hχ
  dsimp only
  apply hG.eqOn_of_preconnected_of_eventuallyEq (introTrace_completed_spectral_analytic χ)
    (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected (z₀ := 2) (by change 1 / 2 < (2 : ℂ).re; norm_num)
  have hnear : ∀ᶠ z : ℂ in 𝓝 2, 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hnear] with z hz
  have hsum' := hsum hz
  simp only [Pi.add_apply] at hsum'
  rw [introTrace_archimedean_sub_sum_eq_heckeGamma_logDeriv χ z (by linarith)] at hsum'
  rw [introTrace_completed_logDeriv_euler χ (s := z + 1 / 2) (by norm_num; linarith)]
  linear_combination hsum'

/-- Paper: §1.4.3, p. 29. Every full spectral window, after adding the common
archimedean counterterm, converges locally uniformly on the shifted Euler half-plane
to the completed logarithmic derivative with its polar and reference corrections. -/
theorem introTraceApprox_exists_spectral_tendsto_completed_logDeriv :
    ∃ h ρ : ℕ → ℝ → ℝ, IsIntroTraceApproximation h ρ ∧
      ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽), RightInverse τ (ideleClassNorm F) →
      ∀ χ : U𝔽, (∀ t, χ (τ t) = 1) → ∀ a : ℝ, 1 / 2 ≤ a →
        TendstoLocallyUniformlyOn (fun n z ↦ introTraceSpectralSum χ approx(h, ρ, n, z) a +
          archSum((1 : U𝔽), approx(h, ρ, n, (2 : ℂ))))
          (fun z ↦ completedSpectral(χ, z)) atTop right(1 / 2) := by
  classical
  obtain ⟨h, ρ, hA, hχ⟩ := introTraceApprox_exists_common_counterterm_limits (F := F)
  refine ⟨h, ρ, hA, ?_⟩
  intro τ hτ χ hnorm a ha
  obtain ⟨_, _, _, hlim, _⟩ := hχ τ hτ χ hnorm
  exact (hlim a ha).congr_right (introTrace_full_reference_series_eq_completed_logDeriv τ hτ χ hnorm)

/-- A reference-difference expansion determines the positive-real-part
regularization exactly by the real anchor value. -/
private theorem introTrace_resolvent_limit_from_reference (χ : U𝔽) (P : ℂ → ℂ) (c : ℂ)
    (href : ∀ z ∈ right(1/2),
      (∑' r : windowZeros(χ,1/2), (zeroOrder(χ,r.val) : ℂ) *
        (1/(z-(r.val-1/2)) - 1/(2-(r.val-1/2)))) + c = P z) :
    let v (r : windowZeros(χ,1/2)) (z : ℂ) := (zeroOrder(χ,r.val) : ℂ)/(z-(r.val-1/2))
    let B := ∑' r, (v r 2).re
    let G (z : ℂ) := P z - P 2 + (B : ℂ)
    AnalyticOnNhd ℂ G right(1/2) ∧
      TendstoLocallyUniformlyOn (fun (T : Finset (windowZeros(χ,1/2))) z ↦
        ∑ r ∈ T, (v r z - ((v r 2).im : ℂ)*Complex.I)) G atTop right(1/2) ∧
      (∀ z ∈ right(1/2), HasSum (fun r ↦ (v r z).re) (G z).re ∧ 0 < (G z).re) ∧
      (χ⁻¹ = χ → ∃ T : ℝ → Finset (windowZeros(χ,1/2)), (∀ t r, r ∈ T t ↔ |r.val.im| ≤ t) ∧
        TendstoLocallyUniformlyOn (fun t z ↦ ∑ r ∈ T t, v r z) G atTop right(1/2)) := by
  classical
  intro v B G
  have h₂ : (2:ℂ) ∈ right(1/2) := by change (1/2:ℝ)<(2:ℂ).re; norm_num
  have hc : c = P 2 := by simpa only [sub_self,mul_zero,tsum_zero,zero_add] using href 2 h₂
  obtain ⟨H,han,hbase,hlim,hpos⟩ := introTrace_resolvent_imaginary_subtraction χ
    (a := 1/2) (b := 2) (by norm_num)
  have hcast : ((2 : ℝ) : ℂ) = 2 := by norm_num
  rw [hcast] at hbase hlim
  have hb : H 2 = (B : ℂ) := by
    apply Complex.ext
    · exact (hpos 2 h₂).1.tsum_eq.symm
    · simpa only [Complex.ofReal_im] using hbase
  have he (z : ℂ) (hz : z ∈ right(1/2)) : H z = G z := by
    let k (r : windowZeros(χ,1/2)) (z : ℂ) := v r z - ((v r 2).im : ℂ)*Complex.I
    have h1 : HasSum (fun r ↦ k r z) (H z) := hlim.tendsto_at hz
    have h2 : HasSum (fun r ↦ k r 2) (H 2) := hlim.tendsto_at h₂
    have hD : HasSum (fun r : windowZeros(χ,1/2) ↦ (zeroOrder(χ,r.val) : ℂ) *
        (1/(z-(r.val-1/2)) - 1/(2-(r.val-1/2)))) (H z-H 2) := by
      apply (h1.sub h2).congr_fun
      intro r
      dsimp [k,v]
      ring
    have eqn := href z hz
    rw [hD.tsum_eq,hb,hc] at eqn
    dsimp only [G]
    linear_combination eqn
  have hG := hlim.congr_right he
  refine ⟨han.congr (isOpen_Ioi.preimage Complex.continuous_re) he,hG,?_,?_⟩
  · intro z hz
    rw [← he z hz]
    have := introTrace_positive_divisor_infinite_from_digamma χ
    obtain ⟨r⟩ := (inferInstance : Nonempty {s : ℂ // 0 < zeroOrder(χ,s)})
    have hn : Nonempty (windowZeros(χ,1/2)) :=
      ⟨⟨r.val,r.property,introTrace_positive_divisor_in_critical_strip χ r.val r.property⟩⟩
    exact ⟨(hpos z hz).1,(hpos z hz).2.mpr hn⟩
  intro hχ
  obtain ⟨T,hT,_,htrunc⟩ := introTrace_selfdual_height_truncation χ hχ (1/2)
  exact ⟨T,hT,htrunc 2 G hG⟩

/-- Paper: §§1.4.3–1.4.5, pp. 29–30. The full zero resolvent with its imaginary
part subtracted at two is the polar-corrected completed logarithmic derivative,
normalized by its value at two and the ordinary real zero sum there. For a
self-dual character the same formula is the ordinary symmetric-height limit. -/
theorem introTrace_completed_logDeriv_resolvent_height_formula
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) :
    let P (z : ℂ) := logDeriv (continuedCompletedHeckeL χ) (z+1/2) +
      if χ = 1 then 1/(z+1/2)+1/(z-1/2) else 0
    let v (r : windowZeros(χ,1/2)) (z : ℂ) := (zeroOrder(χ,r.val) : ℂ)/(z-(r.val-1/2))
    let G (z : ℂ) := P z - P 2 + ((∑' r, (v r 2).re : ℝ) : ℂ)
    AnalyticOnNhd ℂ G right(1/2) ∧
      TendstoLocallyUniformlyOn (fun (T : Finset (windowZeros(χ,1/2))) z ↦
        ∑ r ∈ T, (v r z - ((v r 2).im : ℂ)*Complex.I)) G atTop right(1/2) ∧
      (∀ z ∈ right(1/2), HasSum (fun r ↦ (v r z).re) (G z).re ∧ 0 < (G z).re) ∧
      (χ⁻¹ = χ → ∃ T : ℝ → Finset (windowZeros(χ,1/2)), (∀ t r, r ∈ T t ↔ |r.val.im| ≤ t) ∧
        TendstoLocallyUniformlyOn (fun t z ↦ ∑ r ∈ T t, v r z) G atTop right(1/2)) := by
  classical
  intro P
  apply introTrace_resolvent_limit_from_reference χ P (P 2)
  intro z hz
  have he := introTrace_full_reference_series_eq_completed_logDeriv τ hτ χ hχ
  have h₂ : (2:ℂ) ∈ right(1/2) := by change (1/2:ℝ)<(2:ℂ).re; norm_num
  have h1 := he hz
  have h2 := he h₂
  dsimp only at h1 h2
  simp only [sub_self,mul_zero,tsum_zero,zero_add] at h2
  dsimp only [P]
  linear_combination h1-h2

/-- Paper: §1.4.3, p. 29. For a normalized character and its inverse, the
ordinary paired height sums give the sum of their explicitly normalized
completed logarithmic derivatives on the full shifted Euler half-plane. -/
theorem introTrace_dual_completed_logDeriv_height_formula
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) :
    let P (η : U𝔽) (z : ℂ) := logDeriv (continuedCompletedHeckeL η) (z+1/2) +
      if η = 1 then 1/(z+1/2)+1/(z-1/2) else 0
    let v (η : U𝔽) (r : windowZeros(η,1/2)) (z : ℂ) := (zeroOrder(η,r.val) : ℂ)/(z-(r.val-1/2))
    let G (η : U𝔽) (z : ℂ) := P η z - P η 2 + ((∑' r, (v η r 2).re : ℝ) : ℂ)
    ∃ (T : ℝ → Finset (windowZeros(χ,1/2))) (U : ℝ → Finset (windowZeros(χ⁻¹,1/2))),
      (∀ t r, r ∈ T t ↔ |r.val.im| ≤ t) ∧ (∀ t r, r ∈ U t ↔ |r.val.im| ≤ t) ∧
      TendstoLocallyUniformlyOn (fun t z ↦ (∑ r ∈ T t, v χ r z) + ∑ r ∈ U t, v χ⁻¹ r z)
        (fun z ↦ G χ z + G χ⁻¹ z) atTop right(1/2) ∧
      ∀ z ∈ right(1/2), 0 < (G χ z + G χ⁻¹ z).re := by
  classical
  intro P v G
  have hi (t : ℝ≥0ˣ) : χ⁻¹ (τ t) = 1 := by change (χ (τ t))⁻¹ = 1; rw [hχ,inv_one]
  obtain ⟨_,hL,hpos,_⟩ := introTrace_completed_logDeriv_resolvent_height_formula τ hτ χ hχ
  obtain ⟨_,hI,hipos,_⟩ := introTrace_completed_logDeriv_resolvent_height_formula τ hτ χ⁻¹ hi
  obtain ⟨T,hT,hjoint⟩ := introTrace_dual_height_truncation (F := F) (1/2)
  obtain ⟨_,hlim⟩ := hjoint χ 2 (G χ) (G χ⁻¹)
    (by simpa only [Complex.ofReal_ofNat] using hL) (by simpa only [Complex.ofReal_ofNat] using hI)
  refine ⟨T χ,T χ⁻¹,hT χ,hT χ⁻¹,hlim,?_⟩
  intro z hz
  exact add_pos (hpos z hz).2 (hipos z hz).2

/-- A self-dual character is trivial along any norm section: every positive
scale is a square and every value of the character squares to one. -/
private theorem introTrace_selfdual_trivial_on_section (χ : U𝔽) (hχ : χ⁻¹ = χ)
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (t : ℝ≥0ˣ) : χ (τ t) = 1 := by
  have hu : NNReal.sqrt t.val ≠ 0 := (NNReal.sqrt_pos.mpr (Units.zero_lt t)).ne'
  let u : ℝ≥0ˣ := Units.mk0 (NNReal.sqrt t.val) hu
  have ht : u*u = t := Units.ext (NNReal.mul_self_sqrt t.val)
  have hx : (χ (τ u))⁻¹ = χ (τ u) := congrArg (fun η : U𝔽 ↦ η (τ u)) hχ
  calc
    χ (τ t) = χ (τ u)*χ (τ u) := by rw [← ht,map_mul,map_mul]
    _ = (χ (τ u))⁻¹ * χ (τ u) := by rw [hx]
    _ = 1 := inv_mul_cancel _

/-- Paper: §1.4.3, p. 29. For every self-dual Hecke character of a number
field, the ordinary symmetric-height sums equal the completed logarithmic
derivative up to the explicit constant fixed by the real zero sum at two. -/
theorem introTrace_selfdual_completed_logDeriv_height_formula
    (χ : U𝔽) (hχ : χ⁻¹ = χ) :
    let P (z : ℂ) := logDeriv (continuedCompletedHeckeL χ) (z+1/2) +
      if χ = 1 then 1/(z+1/2)+1/(z-1/2) else 0
    let v (r : windowZeros(χ,1/2)) (z : ℂ) := (zeroOrder(χ,r.val) : ℂ)/(z-(r.val-1/2))
    let G (z : ℂ) := P z - P 2 + ((∑' r, (v r 2).re : ℝ) : ℂ)
    ∃ T : ℝ → Finset (windowZeros(χ,1/2)), (∀ t r, r ∈ T t ↔ |r.val.im| ≤ t) ∧
      TendstoLocallyUniformlyOn (fun t z ↦ ∑ r ∈ T t, v r z) G atTop right(1/2) ∧
      ∀ z ∈ right(1/2), HasSum (fun r ↦ (v r z).re) (G z).re ∧ 0 < (G z).re := by
  classical
  intro P v G
  have hsec := (ideleGroup_quotient.{_,0} F).2.2.2.2.2.2.2.2.2.2.1
  let τ : ℝ≥0ˣ →ₜ* C𝔽 := ⟨hsec.choose,hsec.choose_spec.1⟩
  have hτ : RightInverse τ (ideleClassNorm F) := hsec.choose_spec.2
  obtain ⟨_,_,hreal,hheight⟩ := introTrace_completed_logDeriv_resolvent_height_formula τ hτ χ
    (introTrace_selfdual_trivial_on_section χ hχ τ)
  obtain ⟨T,hT,hlim⟩ := hheight hχ
  exact ⟨T,hT,hlim,hreal⟩

/-- An imaginary norm twist translates the completed logarithmic derivative
throughout the half-plane of absolute convergence. -/
private theorem introTrace_completed_logDeriv_translate (χ ψ : U𝔽) (a : ℂ)
    (ha : a.re = 0) (htwist : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a))
    (s : ℂ) (hs : 1 < s.re) :
    logDeriv (continuedCompletedHeckeL χ) s = logDeriv (continuedCompletedHeckeL ψ) (s + a) := by
  have hy : ((-a.im : ℝ) : ℂ) * Complex.I = -a := Complex.ext (by simp [ha]) (by simp)
  have hγ (w : ℂ) : heckeGammaFactor ψ (w+a) = heckeGammaFactor χ w := by
    have hψ (g : C𝔽) : (ψ g : ℂ) = χ g * (N(g) : ℂ) ^ (((-a.im : ℝ) : ℂ) * Complex.I) := by
      have h := DFunLike.congr_fun htwist g
      change (ψ g : ℂ) * (N(g) : ℂ) ^ (0 : ℂ) = (χ g : ℂ) * (N(g) : ℂ) ^ (-a) at h
      simpa only [hy, Complex.cpow_zero, mul_one] using h
    simpa only [hy, add_neg_cancel_right] using introTraceApprox_spectral_summable_gamma χ ψ (-a.im) hψ (w+a)
  have he : continuedCompletedHeckeL χ =ᶠ[𝓝 s] fun w ↦ continuedCompletedHeckeL ψ (w+a) := by
    filter_upwards [(isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (show s ∈ right(1) from hs)] with w hw
    change 1 < w.re at hw
    have hw' : 1 < (w + a).re := by simpa only [Complex.add_re, ha, add_zero] using hw
    have hf : finiteHeckeL ψ ⟨w+a, hw'⟩ = finiteHeckeL χ ⟨w,hw⟩ := by
      simpa [add_assoc] using finiteHeckeL_imaginary_twist χ ψ (-a) (by simp [ha]) htwist ⟨w+a,hw'⟩
    rw [(continuedCompletedHeckeL_spec χ).2 ⟨w,hw⟩, (continuedCompletedHeckeL_spec ψ).2 ⟨w+a,hw'⟩]
    change _ * _ = heckeGammaFactor ψ (w+a) * finiteHeckeL ψ ⟨w+a,hw'⟩
    rw [hγ, hf]
    rfl
  rw [(logDeriv_congr_nhds he).eq_of_nhds]
  simp only [logDeriv_apply, deriv_comp_add_const]

/-- Translation by the norm frequency reindexes any multiplicity-weighted sum
over the full completed zero divisor. -/
private theorem introTrace_zero_window_twist_tsum (χ ψ : U𝔽) (a : ℂ)
    (ha : a.re = 0) (htwist : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a))
    (f : ℂ → ℤ → ℂ) :
    (∑' r : windowZeros(χ,1/2), f r.val (zeroOrder(χ,r.val))) =
      ∑' r : windowZeros(ψ,1/2), f (r.val-a) (zeroOrder(ψ,r.val)) := by
  have hpos (η : U𝔽) (s : ℂ) (hs : 0 < zeroOrder(η,s)) : 0 < s.re := by
    linarith [(abs_lt.mp (introTrace_positive_divisor_in_critical_strip η s hs)).1]
  have hp (r : windowZeros(χ,1/2)) : zeroOrder(χ,r.val) = zeroOrder(ψ,r.val+a) :=
    introTraceApprox_spectral_divisor_translate χ ψ a ha htwist r.val (hpos _ _ r.property.1)
  have hm (r : windowZeros(ψ,1/2)) : zeroOrder(χ,r.val-a) = zeroOrder(ψ,r.val) := by
    simpa only [sub_add_cancel] using introTraceApprox_spectral_divisor_translate χ ψ a ha htwist (r.val-a)
      (by simpa only [Complex.sub_re,ha,sub_zero] using hpos _ _ r.property.1)
  let e : windowZeros(χ,1/2) ≃ windowZeros(ψ,1/2) := {
    toFun := fun r ↦ ⟨r.val+a, (hp r) ▸ r.property.1, by simpa [Complex.add_re,ha] using r.property.2⟩
    invFun := fun r ↦ ⟨r.val-a, (hm r).symm ▸ r.property.1, by simpa [Complex.sub_re,ha] using r.property.2⟩
    left_inv := fun r ↦ Subtype.ext (add_sub_cancel_right r.val a)
    right_inv := fun r ↦ Subtype.ext (sub_add_cancel r.val a) }
  rw [← e.tsum_eq]
  apply tsum_congr
  intro r
  change _ = f (r.val+a-a) (zeroOrder(ψ,r.val+a))
  rw [add_sub_cancel_right, hp r]

open Classical in
/-- Removing the norm frequency shifts both the argument and the reference
point. Subtracting the two reference expansions cancels their common anchoring
constant and translates the exceptional poles in the trivial normalized isotype. -/
private theorem introTrace_translated_reference_eq_completed_logDeriv
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) (χ ψ : U𝔽) (a : ℂ)
    (ha : a.re = 0) (hψ : ∀ t, ψ (τ t) = 1)
    (htwist : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a)) :
    let P (w : ℂ) := logDeriv (continuedCompletedHeckeL χ) (w+1/2) +
      if ψ = 1 then 1/(w+a+1/2)+1/(w+a-1/2) else 0
    ∀ z ∈ right(1/2),
      (∑' r : windowZeros(χ,1/2), (zeroOrder(χ,r.val) : ℂ) *
        (1/(z-(r.val-1/2))-1/(2-(r.val-1/2)))) + P 2 = P z := by
  classical
  intro P z hz
  have h₂ : (2 : ℂ) ∈ right(1/2) := by change (1/2 : ℝ) < (2 : ℂ).re; norm_num
  have hshift (w : ℂ) (hw : w ∈ right(1/2)) : w+a ∈ right(1/2) := by
    change (1/2 : ℝ) < (w+a).re
    rwa [Complex.add_re,ha,add_zero]
  let u (w : ℂ) (r : windowZeros(ψ,1/2)) := (zeroOrder(ψ,r.val) : ℂ) *
    (1/(w-(r.val-1/2))-1/(2-(r.val-1/2)))
  have hs (w : ℂ) (hw : w ∈ right(1/2)) : HasSum (u w) (∑' r, u w r) :=
    (introTrace_spectral_referenceSub ψ (1/2) (fun _ ↦ 2)
      (fun _ _ ↦ h₂) (differentiableOn_const _)).2.2.1.tendsto_at hw
  have hreindex := introTrace_zero_window_twist_tsum χ ψ a ha htwist
    (fun s m ↦ (m : ℂ) * (1/(z-(s-1/2))-1/(2-(s-1/2))))
  have hdiff : (∑' r : windowZeros(ψ,1/2), (zeroOrder(ψ,r.val) : ℂ) *
      (1/(z-(r.val-a-1/2))-1/(2-(r.val-a-1/2)))) =
      (∑' r, u (z+a) r) - ∑' r, u (2+a) r := by
    apply HasSum.tsum_eq
    apply ((hs (z+a) (hshift z hz)).sub (hs (2+a) (hshift 2 h₂))).congr_fun
    intro r
    dsimp only [u]
    rw [show z-(r.val-a-1/2) = z+a-(r.val-1/2) by ring,
      show 2-(r.val-a-1/2) = 2+a-(r.val-1/2) by ring]
    ring
  have he := introTrace_full_reference_series_eq_completed_logDeriv τ hτ ψ hψ
  have h1 := he (hshift z hz)
  have h2 := he (hshift 2 h₂)
  have hL (w : ℂ) (hw : w ∈ right(1/2)) :
      logDeriv (continuedCompletedHeckeL χ) (w+1/2) =
        logDeriv (continuedCompletedHeckeL ψ) (w+a+1/2) := by
    change (1/2 : ℝ) < w.re at hw
    rw [introTrace_completed_logDeriv_translate χ ψ a ha htwist (w+1/2) (by norm_num; linarith),
      show w+1/2+a = w+a+1/2 by ring]
  rw [hreindex,hdiff]
  dsimp only [P,u] at *
  rw [hL z hz,hL 2 h₂]
  linear_combination h1 - h2

/-- The inverse character has the opposite norm frequency. -/
private theorem introTrace_inverse_normalized_twist (χ ψ : U𝔽) (a : ℂ)
    (htwist : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a)) :
    ideleClassNormTwist ψ⁻¹ 0 = ideleClassNormTwist χ⁻¹ (-(-a)) := by
  ext1 g
  have h := DFunLike.congr_fun htwist g
  change (ψ g : ℂ) * (N(g) : ℂ)^(0 : ℂ) = (χ g : ℂ) * (N(g) : ℂ)^(-a) at h
  change ((ψ g)⁻¹ : Circle) * (N(g) : ℂ)^(0 : ℂ) = ((χ g)⁻¹ : Circle) * (N(g) : ℂ)^(-(-a))
  simp only [Complex.cpow_zero,mul_one] at h ⊢
  rw [Circle.coe_inv,Circle.coe_inv,h,mul_inv_rev,Complex.cpow_neg,inv_inv,neg_neg,mul_comm]

open Classical in
/-- Paper: §§1.4.3–1.4.5, pp. 29–30. For every unitary character over a number
field the completed logarithmic derivative gives both the imaginary-subtracted
zero resolvent and the ordinary height sum paired with the inverse character.
A pure norm twist translates the two polar terms by its norm frequency. -/
theorem introTrace_all_characters_completed_resolvent_height_formula
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) :
    ∃ (ψ : U𝔽) (a : ℂ), a.re = 0 ∧ (∀ t, ψ (τ t) = 1) ∧
      ideleClassNormTwist ψ 0 = ideleClassNormTwist χ (-a) ∧
      let P (η : U𝔽) (b z : ℂ) := logDeriv (continuedCompletedHeckeL η) (z+1/2) +
        if ψ = 1 then 1/(z+b+1/2)+1/(z+b-1/2) else 0
      let v (η : U𝔽) (r : windowZeros(η,1/2)) (z : ℂ) :=
        (zeroOrder(η,r.val) : ℂ)/(z-(r.val-1/2))
      let G (η : U𝔽) (b z : ℂ) := P η b z - P η b 2 + ((∑' r, (v η r 2).re : ℝ) : ℂ)
      AnalyticOnNhd ℂ (G χ a) right(1/2) ∧
        TendstoLocallyUniformlyOn (fun (T : Finset (windowZeros(χ,1/2))) z ↦
          ∑ r ∈ T, (v χ r z - ((v χ r 2).im : ℂ)*Complex.I)) (G χ a) atTop right(1/2) ∧
        (∀ z ∈ right(1/2), HasSum (fun r ↦ (v χ r z).re) (G χ a z).re ∧ 0 < (G χ a z).re) ∧
        ∃ (T : ℝ → Finset (windowZeros(χ,1/2))) (U : ℝ → Finset (windowZeros(χ⁻¹,1/2))),
          (∀ t r, r ∈ T t ↔ |r.val.im| ≤ t) ∧ (∀ t r, r ∈ U t ↔ |r.val.im| ≤ t) ∧
          TendstoLocallyUniformlyOn (fun t z ↦ (∑ r ∈ T t, v χ r z) + ∑ r ∈ U t, v χ⁻¹ r z)
            (fun z ↦ G χ a z + G χ⁻¹ (-a) z) atTop right(1/2) := by
  classical
  obtain ⟨ψ,a,ha,hψ,htwist⟩ := introTraceApprox_spectral_normalized_character τ hτ χ
  refine ⟨ψ,a,ha,hψ,htwist,?_⟩
  intro P v G
  obtain ⟨han,hlim,hpos,_⟩ := introTrace_resolvent_limit_from_reference χ (P χ a) (P χ a 2)
    (introTrace_translated_reference_eq_completed_logDeriv τ hτ χ ψ a ha hψ htwist)
  have hi (t : ℝ≥0ˣ) : ψ⁻¹ (τ t) = 1 := by change (ψ (τ t))⁻¹ = 1; rw [hψ,inv_one]
  have hI := introTrace_translated_reference_eq_completed_logDeriv τ hτ χ⁻¹ ψ⁻¹ (-a)
    (by simp [ha]) hi (introTrace_inverse_normalized_twist χ ψ a htwist)
  obtain ⟨_,hilim,_,_⟩ := introTrace_resolvent_limit_from_reference χ⁻¹
    (P χ⁻¹ (-a)) (P χ⁻¹ (-a) 2) (by simpa only [inv_eq_one,P] using hI)
  obtain ⟨T,hT,hjoint⟩ := introTrace_dual_height_truncation (F := F) (1/2)
  obtain ⟨_,hsum⟩ := hjoint χ 2 (G χ a) (G χ⁻¹ (-a))
    (by simpa only [Complex.ofReal_ofNat] using hlim) (by simpa only [Complex.ofReal_ofNat] using hilim)
  exact ⟨han,hlim,hpos,T χ,T χ⁻¹,hT χ,hT χ⁻¹,hsum⟩

/-- Absolute convergence of the ideal logarithmic-derivative series gives a
uniform bound on every fixed vertical line in the Euler half-plane. -/
private theorem introTrace_finite_logDeriv_bounded_vertical (χ : U𝔽) (σ : ℝ) (hσ : 1 < σ) :
    ∃ B : ℝ, ∀ s : ℂ, s.re = σ → ‖logDeriv finiteL(χ) s‖ ≤ B := by
  let f (s : ℂ) (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) :=
    -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ)^s
  have hs (s : ℂ) (h : 1 < s.re) : HasSum (f s) (logDeriv finiteL(χ) s) :=
    (finiteHeckeL_logDeriv_hasSum_ideals χ _ (finiteHeckeL_exists_continuation χ).choose_spec.1
      (finiteHeckeL_exists_continuation χ).choose_spec.2 ⟨s,h⟩).2.2
  refine ⟨∑' I, ‖f (σ : ℂ) I‖,?_⟩
  intro s h
  have hsum := hs s (h ▸ hσ)
  rw [← hsum.tsum_eq]
  apply (norm_tsum_le_tsum_norm hsum.summable.norm).trans_eq
  apply tsum_congr
  intro I
  have hN : 0 < (I.val.absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr I.property)
  simp only [f,norm_div]
  congr 1
  change ‖((I.val.absNorm : ℝ) : ℂ)^s‖ = ‖((I.val.absNorm : ℝ) : ℂ)^(σ : ℂ)‖
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.norm_cpow_eq_rpow_re_of_pos hN,h,Complex.ofReal_re]

/-- Paper: Section 1.4.3, p. 29. The multiplicity-weighted real zero
resolvent on every fixed vertical line with real part at least two is
asymptotic at both height ends to half the field degree times the log height. -/
theorem introTrace_real_zero_resolvent_log_height (χ : U𝔽) (σ : ℝ) (hσ : 2 ≤ σ) :
    Tendsto (fun t : ℝ ↦ (∑' r : windowZeros(χ,1/2),
      ((zeroOrder(χ,r.val):ℂ)/(((σ:ℂ)+(t:ℂ)*Complex.I)-r.val)).re) / Real.log |t|)
      (cocompact ℝ) (𝓝 ((Module.finrank ℚ F : ℝ)/2)) := by
  classical
  have hsec := (ideleGroup_quotient.{_,0} F).2.2.2.2.2.2.2.2.2.2.1
  let τ : ℝ≥0ˣ →ₜ* C𝔽 := ⟨hsec.choose,hsec.choose_spec.1⟩
  have hτ : RightInverse τ (ideleClassNorm F) := hsec.choose_spec.2
  obtain ⟨ψ,a,ha,_,_,_,_,hreal,_⟩ := introTrace_all_characters_completed_resolvent_height_formula τ hτ χ
  let s (t : ℝ) := (σ:ℂ)+(t:ℂ)*Complex.I
  let z (t : ℝ) := s t-1/2
  let p (z : ℂ) := if ψ = 1 then 1/(z+a+1/2) + 1/(z+a-1/2) else 0
  let C := (∑' r : windowZeros(χ,1/2), ((zeroOrder(χ,r.val):ℂ)/(2-(r.val-1/2))).re) -
    (logDeriv (continuedCompletedHeckeL χ) (2+1/2) + p 2).re
  let d := (Module.finrank ℚ F : ℝ)/2
  let E (t : ℝ) := (logDeriv finiteL(χ) (s t)).re + (p (z t)).re + C
  have hs (t : ℝ) : (s t).re = σ := by simp [s]
  have hz (t : ℝ) : z t ∈ right(1/2) := by
    change 1/2 < (s t-1/2).re
    simp only [Complex.sub_re,hs,Complex.div_ofNat_re,Complex.one_re]
    linarith
  have hsum (t : ℝ) : (∑' r : windowZeros(χ,1/2),
        ((zeroOrder(χ,r.val):ℂ)/(s t-r.val)).re) =
      (logDeriv (heckeGammaFactor χ) (s t)).re + E t := by
    have he := ((hreal (z t) (hz t)).1).tsum_eq
    have hz₁ : z t + 1/2 = s t := by dsimp [z]; ring
    have hz₂ (r : windowZeros(χ,1/2)) : z t - (r.val-1/2) = s t-r.val := by dsimp [z]; ring
    dsimp only at he
    simp only [hz₁,hz₂,Complex.add_re,Complex.sub_re,Complex.ofReal_re] at he
    rw [he,introTrace_completed_logDeriv_euler χ (by rw [hs]; linarith)]
    dsimp only [E,C,p]
    simp only [Complex.add_re]
    ring
  obtain ⟨B,hB⟩ := introTrace_finite_logDeriv_bounded_vertical χ σ (by linarith)
  have hp (t : ℝ) : ‖p (z t)‖ ≤ 2 := by
    have hrec (w : ℂ) (hw : 1 ≤ w.re) : ‖1/w‖ ≤ 1 := by
      rw [one_div,norm_inv,inv_le_one₀]
      · exact hw.trans (Complex.re_le_norm _)
      · exact lt_of_lt_of_le zero_lt_one (hw.trans (Complex.re_le_norm _))
    dsimp only [p]
    split_ifs
    · apply (norm_add_le _ _).trans
      have h₁ : 1 ≤ (z t+a+1/2).re := by simp [z,hs,ha]; linarith
      have h₂ : 1 ≤ (z t+a-1/2).re := by simp [z,hs,ha]; linarith
      linarith [hrec _ h₁,hrec _ h₂]
    · norm_num
  let U := |B|+2+|C|
  have hE (t : ℝ) : |E t| ≤ U := by
    dsimp only [E,U]
    have h₁ := (Complex.abs_re_le_norm (logDeriv finiteL(χ) (s t))).trans ((hB _ (hs t)).trans (le_abs_self B))
    have h₂ := (Complex.abs_re_le_norm (p (z t))).trans (hp t)
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h₁ h₂)) (le_refl |C|))
  have hlo : Tendsto (fun t : ℝ ↦ Real.log |t|) (cocompact ℝ) atTop := by
    simpa only [Function.comp_def,Real.norm_eq_abs] using Real.tendsto_log_atTop.comp (tendsto_norm_cocompact_atTop (E := ℝ))
  have herr : Tendsto (fun t ↦ E t / Real.log |t|) (cocompact ℝ) (𝓝 0) := by
    apply squeeze_zero_norm' _ ((tendsto_const_nhds (x := U)).div_atTop hlo)
    filter_upwards [hlo.eventually_gt_atTop 0] with t ht
    simp only [Real.norm_eq_abs,abs_div,abs_of_pos ht]
    exact div_le_div_of_nonneg_right (hE t) ht.le
  have hg := introTrace_heckeGamma_vertical_main_term χ σ (by linarith)
  have hrem := hg.div_atTop hlo
  have hc := (tendsto_const_nhds (x := d * Real.log (2*Real.pi))).div_atTop hlo
  have h := ((tendsto_const_nhds (x := d)).add hrem).sub hc |>.add herr
  rw [add_zero,sub_zero,add_zero] at h
  apply h.congr'
  filter_upwards [hlo.eventually_gt_atTop 0] with t ht
  rw [hsum]
  dsimp only [s,d]
  field_simp [ht.ne']
  ring

/-- Outside a window of radius eight, half the Poisson kernel at real
part eight majorizes the kernel at real part two. Inside the window the
unweighted zero multiplicity majorizes the narrower kernel. -/
private theorem introTrace_compare_zero_count_kernels (χ : U𝔽) (r : windowZeros(χ,1/2)) (t : ℝ) :
    let K (σ : ℝ) := ((zeroOrder(χ,r.val):ℂ)/(((σ:ℂ)+(t:ℂ)*Complex.I)-r.val)).re
    K 2 ≤ (if |t-r.val.im| ≤ 8 then (zeroOrder(χ,r.val):ℝ) else 0) + K 8/2 := by
  intro K
  let u := 2-r.val.re
  let x := t-r.val.im
  let m : ℝ := zeroOrder(χ,r.val)
  have hm : 0 ≤ m := (Int.cast_pos.mpr r.property.1).le
  have hu : 1 ≤ u ∧ u ≤ 2 := by
    obtain ⟨hl,hr⟩ := abs_lt.mp r.property.2
    dsimp [u]; constructor <;> linarith
  have he (σ : ℝ) : K σ = m*((σ-r.val.re)/((σ-r.val.re)^2+x^2)) := by
    simp [K,m,x,Complex.div_re,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im]
    ring
  rw [he,he,show (8:ℝ)-r.val.re = u+6 by dsimp [u]; ring]
  change m*(u/(u^2+x^2)) ≤ (if |x| ≤ 8 then m else 0) + m*((u+6)/((u+6)^2+x^2))/2
  have h₁ : 0 < u^2+x^2 := by nlinarith [sq_nonneg x, sq_nonneg (u-1)]
  have h₂ : 0 < (u+6)^2+x^2 := by nlinarith [sq_nonneg x,sq_nonneg u]
  have hu₀ : 0 ≤ u := by linarith [hu.1]
  by_cases hx : |x| ≤ 8
  · simp only [hx,ite_true]
    have ha : u/(u^2+x^2) ≤ 1 := by
      rw [div_le_one h₁]
      nlinarith [sq_nonneg (u-1),sq_nonneg x]
    have hb : 0 ≤ m*((u+6)/((u+6)^2+x^2))/2 := by positivity
    linarith [mul_le_mul_of_nonneg_left ha hm]
  · simp only [hx,ite_false,zero_add]
    have hxs : 64 ≤ x^2 := by
      have h := le_of_not_ge hx
      nlinarith [sq_abs x,mul_nonneg (by linarith : 0 ≤ |x|-8) (by positivity : 0 ≤ |x|+8)]
    have huv : 2*u*(u+6)^2 ≤ 256 := by
      have hpos : 0 ≤ u := by linarith
      have hv : u+6 ≤ 8 := by linarith
      calc
        2*u*(u+6)^2 ≤ 2*2*(8:ℝ)^2 := by gcongr; linarith
        _ = 256 := by norm_num
    have ha : u/(u^2+x^2) ≤ ((u+6)/((u+6)^2+x^2))/2 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ)<2),div_mul_eq_mul_div,div_le_div_iff₀ h₁ h₂]
      nlinarith [mul_nonneg (show 0 ≤ 2-u by linarith) (sq_nonneg x),
        mul_nonneg (show 0 ≤ u+6 by linarith) (sq_nonneg u)]
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left ha hm

/-- Paper: Section 1.4.3, p. 29. Each interval of radius eight centered at
sufficiently large positive or negative height contains more than
`c * log |t|` completed zeros counted with multiplicity, for every
`c < [F : ℚ] / 4`. -/
theorem introTrace_completed_zero_count_height_lower (χ : U𝔽) {c : ℝ}
    (hc : c < (Module.finrank ℚ F : ℝ)/4) :
    ∀ᶠ t : ℝ in cocompact ℝ, ∃ T : Finset (windowZeros(χ,1/2)),
      (∀ r, r ∈ T ↔ |t-r.val.im| ≤ 8) ∧
      c*Real.log |t| < ∑ r ∈ T, (zeroOrder(χ,r.val):ℝ) := by
  classical
  let Z := windowZeros(χ,1/2)
  let K (σ t : ℝ) (r : Z) := ((zeroOrder(χ,r.val):ℂ)/(((σ:ℂ)+(t:ℂ)*Complex.I)-r.val)).re
  let S (σ t : ℝ) := ∑' r : Z, K σ t r
  have h (σ : ℝ) (hσ : 2 ≤ σ) :
      Tendsto (fun t : ℝ ↦ S σ t / Real.log |t|) (cocompact ℝ) (𝓝 ((Module.finrank ℚ F : ℝ)/2)) :=
    introTrace_real_zero_resolvent_log_height χ σ hσ
  have hd := (h 2 le_rfl).sub ((h 8 (by norm_num)).div_const 2)
  have he : (Module.finrank ℚ F : ℝ)/2-((Module.finrank ℚ F : ℝ)/2)/2 = (Module.finrank ℚ F : ℝ)/4 := by ring
  rw [he] at hd
  have hre := (introTrace_resolvent_imaginary_subtraction χ (a := 1/2) (b := 2) (by norm_num))
  obtain ⟨_,_,_,_,hR⟩ := hre
  have hs (σ t : ℝ) (hσ : 2 ≤ σ) : Summable (K σ t) := by
    let z := ((σ:ℂ)+(t:ℂ)*Complex.I)-1/2
    have hz : z ∈ right(1/2) := by
      change 1/2 < z.re
      simp [z]; linarith
    have hsub (r : Z) : z-(r.val-1/2) = ((σ:ℂ)+(t:ℂ)*Complex.I)-r.val := by dsimp [z]; ring
    simpa only [K,hsub] using ((hR z hz).1).summable
  obtain ⟨U,hU,_⟩ := introTrace_window_zeros_height_exhaustion χ (1/2)
  have hlog : Tendsto (fun t : ℝ ↦ Real.log |t|) (cocompact ℝ) atTop := by
    simpa only [Function.comp_def,Real.norm_eq_abs] using Real.tendsto_log_atTop.comp (tendsto_norm_cocompact_atTop (E := ℝ))
  filter_upwards [hd.eventually (lt_mem_nhds hc),hlog.eventually_gt_atTop 0] with t hmain ht
  let T := (U (|t|+8)).filter (fun r ↦ |t-r.val.im| ≤ 8)
  have hT (r : Z) : r ∈ T ↔ |t-r.val.im| ≤ 8 := by
    rw [Finset.mem_filter,hU,and_iff_right_iff_imp]
    intro hr
    calc
      |r.val.im| = |t-(t-r.val.im)| := by ring_nf
      _ ≤ |t|+|t-r.val.im| := abs_sub _ _
      _ ≤ _ := by linarith
  refine ⟨T,hT,?_⟩
  let M (r : Z) := if |t-r.val.im| ≤ 8 then (zeroOrder(χ,r.val):ℝ) else 0
  have hM (r : Z) (hr : r ∉ T) : M r = 0 := ite_eq_right (mt (hT r).mpr hr)
  have hMs : Summable M := summable_of_ne_finset_zero hM
  have hMt : ∑' r : Z, M r = ∑ r ∈ T, (zeroOrder(χ,r.val):ℝ) := by
    rw [tsum_eq_sum hM]
    exact Finset.sum_congr rfl fun r hr ↦ ite_eq_left ((hT r).mp hr)
  have hbound := (hs 2 t le_rfl).tsum_le_tsum (fun r ↦ introTrace_compare_zero_count_kernels χ r t)
    (hMs.add ((hs 8 t (by norm_num)).div_const 2))
  change S 2 t ≤ ∑' r : Z, (M r + K 8 t r / 2) at hbound
  rw [hMs.tsum_add ((hs 8 t (by norm_num)).div_const 2),hMt,tsum_div_const] at hbound
  change S 2 t ≤ (∑ r ∈ T, (zeroOrder(χ,r.val):ℝ)) + S 8 t/2 at hbound
  change c < S 2 t/Real.log |t| - (S 8 t/Real.log |t|)/2 at hmain
  have := (lt_div_iff₀ ht).mp (show c < (S 2 t-S 8 t/2)/Real.log |t| by
    convert hmain using 1
    ring)
  linarith

end CompletedSpectralContinuation

/-- Paper: §1.4.3, p. 29. Every unitary character over a number field has infinitely
many distinct positive-order zeros of its completed L-function. Finiteness would
make the spectral sum a finite sum of convergent Mellin moments. -/
theorem introTrace_positive_divisor_infinite (χ : U𝔽) :
    Infinite {z : ℂ // 0 < MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z} := by
  exact introTrace_positive_divisor_infinite_from_digamma χ

open Classical in
/-- Paper: §1.4.3, p. 29. For any selection of completed zeros, summability of
the unsubtracted resolvent at one complex parameter is equivalent to summability
of the multiplicity-weighted reciprocal heights. The criterion applies even at
a pole, where Lean assigns zero to the single zero-denominator term. -/
theorem introTrace_resolvent_summable_iff_reciprocal_height
    (χ : U𝔽) (P : ℂ → Prop) (z : ℂ) :
    let E := {r : ℂ // 0 < zeroOrder(χ, r) ∧ P r}
    Summable (fun r : E ↦ (zeroOrder(χ, r.val) : ℂ) / (z-(r.val-1/2))) ↔
      Summable (fun r : E ↦ (zeroOrder(χ, r.val) : ℝ) / (1+|r.val.im|)) := by
  classical
  intro E
  let v (r : E) := r.val-1/2
  let d (r : E) : ℝ := zeroOrder(χ,r.val)
  let W (r : E) := 1+|r.val.im|
  have hW (r : E) : 0 < W r := by dsimp [W]; positivity
  have hd (r : E) : 1 ≤ d r := by
    have hi : (1 : ℤ) ≤ zeroOrder(χ, r.val) := Int.add_one_le_iff.mpr r.property.1
    dsimp only [d]
    exact_mod_cast hi
  have hnorm (r : E) : ‖(zeroOrder(χ,r.val) : ℂ)/(z-v r)‖ = d r / ‖z-v r‖ := by
    rw [norm_div, Complex.norm_intCast, abs_of_pos (show 0 < d r by linarith [hd r])]
  have him (r : E) : (v r).im = r.val.im := by simp [v]
  constructor
  · intro h
    have he : {r : E | z = v r}.Subsingleton := by
      intro r hr t ht
      apply Subtype.ext
      exact sub_left_injective ((show z=v r from hr).symm.trans (show z=v t from ht))
    apply Summable.of_norm_bounded_eventually (h.norm.mul_left (‖z‖+1))
    filter_upwards [he.finite.eventually_cofinite_notMem] with r hr
    have hden : 0 < ‖z-v r‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hr)
    have hvr := introTrace_positive_divisor_in_critical_strip χ r.val r.property.1
    have hsup : ‖z-v r‖ ≤ (‖z‖+1) * W r := by
      have hvr' : |(v r).re| < 1/2 := by simpa [v] using hvr
      have h1 := Complex.norm_le_abs_re_add_abs_im (v r)
      rw [him] at h1
      have h2 := norm_sub_le z (v r)
      dsimp [W]
      nlinarith [mul_nonneg (norm_nonneg z) (abs_nonneg r.val.im)]
    rw [Real.norm_of_nonneg (show 0 ≤ (zeroOrder(χ,r.val) : ℝ)/(1+|r.val.im|) from
      div_nonneg (by linarith [hd r] : 0 ≤ d r) (hW r).le), hnorm]
    change d r / W r ≤ (‖z‖+1) * (d r / ‖z-v r‖)
    rw [← mul_div_assoc,div_le_div_iff₀ (hW r) hden]
    nlinarith [mul_le_mul_of_nonneg_left hsup (show 0 ≤ d r by linarith [hd r])]
  · intro h
    let T := 2*|z.im|+1
    have hT : 0 < 1+T := by dsimp [T]; positivity
    have hsmall := h.tendsto_cofinite_zero.eventually (gt_mem_nhds (one_div_pos.mpr hT))
    apply Summable.of_norm_bounded_eventually (h.mul_left 2)
    filter_upwards [hsmall] with r hr
    change d r / W r < 1/(1+T) at hr
    have ht : T < |r.val.im| := by
      have hone := (div_le_div_of_nonneg_right (hd r) (hW r).le).trans_lt hr
      have huu := (div_lt_div_iff₀ (hW r) hT).mp hone
      dsimp [W] at huu
      linarith
    have hdiff : |r.val.im| ≤ |z.im| + ‖z-v r‖ := by
      have he := Complex.abs_im_le_norm (z-v r)
      rw [Complex.sub_im,him] at he
      have ht' := abs_sub_abs_le_abs_sub r.val.im z.im
      rw [abs_sub_comm r.val.im z.im] at ht'
      linarith
    have hbelow : W r ≤ 2 * ‖z-v r‖ := by dsimp [T] at ht; dsimp [W]; linarith
    have hden : 0 < ‖z-v r‖ := by linarith [hW r]
    rw [hnorm]
    change d r / ‖z-v r‖ ≤ 2 * (d r / W r)
    rw [← mul_div_assoc,div_le_div_iff₀ hden (hW r)]
    nlinarith [mul_le_mul_of_nonneg_left hbelow (show 0 ≤ d r by linarith [hd r])]

/-- Multiplicity-weighted reciprocal heights are summable precisely when
the masses of successive dyadic height shells, divided by their lower
endpoints, form a summable numerical series. -/
private theorem introTrace_dyadic_reciprocal_mass {ι : Type*} (m H : ι → ℝ)
    (hm : ∀ r, 0 ≤ m r) (hH : ∀ r, 1 ≤ H r)
    (S : ℕ → Finset ι) (hS : ∀ n r, r ∈ S n ↔ (2:ℝ)^n ≤ H r ∧ H r < (2:ℝ)^(n+1)) :
    Summable (fun r ↦ m r / H r) ↔ Summable (fun n ↦ (∑ r ∈ S n, m r)/(2:ℝ)^n) := by
  classical
  let A (n : ℕ) : Set ι := ↑(S n)
  have hpart (r : ι) : ∃! n, r ∈ A n := by
    obtain ⟨n,hn⟩ := exists_nat_pow_near (hH r) (by norm_num : (1:ℝ)<2)
    refine ⟨n,(hS n r).mpr hn,?_⟩
    intro j hj
    have hj' := (hS j r).mp hj
    rcases lt_trichotomy j n with h | h | h
    · have e : (2:ℝ)^(j+1) ≤ 2^n := pow_le_pow_right₀ (by norm_num) h
      linarith [hn.1,hj'.2]
    · exact h
    · have e : (2:ℝ)^(n+1) ≤ 2^j := pow_le_pow_right₀ (by norm_num) h
      linarith [hn.2,hj'.1]
  let M (n : ℕ) := ∑ r ∈ S n, m r / H r
  let D (n : ℕ) := (∑ r ∈ S n, m r)/(2:ℝ)^n
  have hsum (n : ℕ) : ∑' r : A n, m r.val/H r.val = M n := by
    let : Fintype (A n) := (S n).fintypeCoeSort
    rw [tsum_fintype]
    exact Finset.sum_coe_sort (S n) (fun r ↦ m r/H r)
  have hbase : Summable (fun r ↦ m r/H r) ↔ Summable M := by
    rw [summable_partition (s:=A) (fun r ↦ div_nonneg (hm r) (by linarith [hH r])) hpart]
    simp_rw [hsum]
    apply and_iff_right
    intro n
    let : Fintype (A n) := (S n).fintypeCoeSort
    exact (hasSum_fintype _).summable
  have hMD (n : ℕ) : 0 ≤ M n ∧ M n ≤ D n ∧ D n ≤ 2*M n := by
    refine ⟨Finset.sum_nonneg (fun r _ ↦ div_nonneg (hm r) (by linarith [hH r])),?_,?_⟩
    · dsimp only [D,M]
      rw [Finset.sum_div]
      exact Finset.sum_le_sum fun r hr ↦ div_le_div_of_nonneg_left (hm r) (by positivity) ((hS n r).mp hr).1
    · dsimp only [D,M]
      rw [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      rw [mul_div_assoc',div_le_div_iff₀ (by positivity) (by linarith [hH r])]
      have h := ((hS n r).mp hr).2.le
      rw [pow_succ] at h
      nlinarith only [mul_le_mul_of_nonneg_left h (hm r)]
  rw [hbase]
  constructor
  · intro h
    exact Summable.of_nonneg_of_le (fun n ↦ (hMD n).1.trans (hMD n).2.1)
      (fun n ↦ (hMD n).2.2) (h.mul_left 2)
  · intro h
    exact Summable.of_nonneg_of_le (fun n ↦ (hMD n).1) (fun n ↦ (hMD n).2.1) h

open Classical in
/-- For any selection of completed Hecke zeros, the ordinary resolvent is
absolutely summable exactly when the dyadic shell multiplicities divided by
the shell heights are summable. In particular, a power saving in the
multiplicity on dyadic shells suffices at every complex parameter. -/
theorem introTrace_resolvent_dyadic_zero_density (χ : U𝔽) (P : ℂ → Prop) :
    let E := {r : ℂ // 0 < zeroOrder(χ,r) ∧ P r}
    ∃ S : ℕ → Finset E,
      (∀ n r, r ∈ S n ↔ (2:ℝ)^n ≤ 1+|r.val.im| ∧ 1+|r.val.im| < (2:ℝ)^(n+1)) ∧
      let M (n : ℕ) := ∑ r ∈ S n, (zeroOrder(χ,r.val):ℝ)
      (∀ z : ℂ, Summable (fun r : E ↦ (zeroOrder(χ,r.val):ℂ)/(z-(r.val-1/2))) ↔
        Summable (fun n ↦ M n/(2:ℝ)^n)) ∧
      (∀ q : ℝ, 0 ≤ q → q < 2 → ∀ C : ℝ, (∀ᶠ n : ℕ in atTop, M n ≤ C*q^n) →
        ∀ z : ℂ, Summable (fun r : E ↦ (zeroOrder(χ,r.val):ℂ)/(z-(r.val-1/2)))) := by
  classical
  intro E
  let H (r : E) := 1+|r.val.im|
  let m (r : E) : ℝ := zeroOrder(χ,r.val)
  have hm (r : E) : 0 ≤ m r := (Int.cast_pos.mpr r.property.1).le
  let f : E ↪ windowZeros(χ,1/2) := ⟨fun r ↦ ⟨r.val,r.property.1,
    introTrace_positive_divisor_in_critical_strip χ r.val r.property.1⟩,
    fun x y h ↦ Subtype.ext (congrArg (fun v : windowZeros(χ,1/2) ↦ v.val) h)⟩
  obtain ⟨U,hU,_⟩ := introTrace_window_zeros_height_exhaustion χ (1/2)
  let B (n : ℕ) := {r : E | (2:ℝ)^n ≤ H r ∧ H r < (2:ℝ)^(n+1)}
  have hfin (n : ℕ) : (B n).Finite := by
    apply ((U ((2:ℝ)^(n+1))).finite_toSet.preimage_embedding f).subset
    intro r hr
    change f r ∈ U _
    rw [hU]
    change |r.val.im| ≤ _
    have h := (show _ ∧ H r < (2:ℝ)^(n+1) from hr).2
    dsimp only [H] at h
    linarith
  let S (n : ℕ) := (hfin n).toFinset
  have hS (n : ℕ) (r : E) : r ∈ S n ↔ (2:ℝ)^n ≤ H r ∧ H r < (2:ℝ)^(n+1) :=
    Set.Finite.mem_toFinset _
  refine ⟨S,hS,?_⟩
  let M (n : ℕ) := ∑ r ∈ S n, m r
  have he (z : ℂ) := (introTrace_resolvent_summable_iff_reciprocal_height χ P z).trans
    (introTrace_dyadic_reciprocal_mass m H hm (fun r ↦ by dsimp only [H]; linarith [abs_nonneg r.val.im]) S hS)
  refine ⟨he,?_⟩
  intro q h₀ h₂ C hM z
  apply (he z).mpr
  have hg := (summable_geometric_of_lt_one (div_nonneg h₀ (by norm_num : (0:ℝ)≤2))
    (show q/2<1 by linarith)).mul_left C
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [hM] with n hn
  change ‖M n/(2:ℝ)^n‖ ≤ _
  rw [Real.norm_of_nonneg (div_nonneg (Finset.sum_nonneg (fun r _ ↦ hm r)) (by positivity)),div_pow,mul_div_assoc']
  exact div_le_div_of_nonneg_right hn (by positivity)

open Classical in
/-- Absolute convergence of the reciprocal-height majorant lets the smoothed
Mellin sum pass to its limiting resolvent, locally uniformly in the Euler chart. -/
private theorem introTraceApprox_sparse_moments_limit {ι : Type*}
    (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (hbound : ∀ a m Z : ℝ, 0 ≤ a → a < m → 0 ≤ Z → ∃ B : ℝ, 0 ≤ B ∧
      ∀ (n : ℕ) (z s : ℂ), m ≤ z.re → ‖z‖ ≤ Z → s.re ≤ a →
        ‖introTraceMellin approx(h, ρ, n, z) s‖ ≤ B / (1 + |s.im|))
    (v : ι → ℂ) (d : ι → ℤ) (hv : ∀ i, (v i).re ≤ 1/2) (hd : ∀ i, 0 ≤ d i)
    (hD : Summable (fun i ↦ (d i : ℝ) / (1 + |(v i).im|))) :
    (∀ z : ℂ, 1/2 < z.re → Summable (fun i ↦ (d i : ℂ) / (z-v i))) ∧
    TendstoLocallyUniformlyOn
      (fun n z ↦ ∑' i, (d i : ℂ) * introTraceMellin approx(h, ρ, n, z) (v i))
      (fun z ↦ ∑' i, (d i : ℂ) / (z-v i)) atTop right(1/2) := by
  let g (z : ℂ) (i : ι) := (d i : ℂ) / (z-v i)
  let f (n : ℕ) (z : ℂ) (i : ι) := (d i : ℂ) * introTraceMellin approx(h, ρ, n, z) (v i)
  have hopen : IsOpen right(1/2) := isOpen_Ioi.preimage Complex.continuous_re
  have hlim (z : ℂ) (hz : 1/2 < z.re) (i : ι) :
      Tendsto (fun p : ℕ × ℂ ↦ f p.1 p.2 i) (atTop ×ˢ 𝓝 z) (𝓝 (g z i)) := by
    let L := (atTop : Filter ℕ) ×ˢ 𝓝 z
    have hzi : (v i).re < z.re := (hv i).trans_lt hz
    have hne : z-v i ≠ 0 := sub_ne_zero.mpr (fun e ↦ hzi.ne (congrArg Complex.re e.symm))
    have hcont : ContinuousAt (fun y : ℂ ↦ 1 / (y-v i)) z :=
      continuousAt_const.div (continuousAt_id.sub_const _) hne
    have hl := (isOpen_Ioi.preimage Complex.continuous_re).tendstoLocallyUniformlyOn_iff_forall_tendsto.1
      (introTraceApprox_mellin_tendsto h ρ hA (v i)) z hzi
    have hpow : Tendsto (fun p : ℕ × ℂ ↦ introTraceMellin (introTracePower p.2) (v i))
        L (𝓝 (1/(z-v i))) := by
      apply (hcont.tendsto.comp tendsto_snd).congr'
      filter_upwards [tendsto_snd.eventually (Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hzi))]
        with p hp
      exact (introTracePower_mellin p.2 (v i) hp).2.symm
    simpa [f,g,div_eq_mul_inv] using (hpow.congr_uniformity hl).const_mul (d i : ℂ)
  have control (z : ℂ) (hz : 1/2 < z.re) :
      ∃ b : ι → ℝ, Summable b ∧ ∀ᶠ p : ℕ × ℂ in atTop ×ˢ 𝓝 z, ∀ i, ‖f p.1 p.2 i‖ ≤ b i := by
    obtain ⟨m, hm, hmz⟩ := exists_between hz
    obtain ⟨B,hB,h⟩ := hbound (1/2) m (‖z‖+1) (by norm_num) hm (by positivity)
    refine ⟨_,hD.mul_left B,?_⟩
    have hrez : ∀ᶠ w : ℂ in 𝓝 z, m ≤ w.re :=
      Complex.continuous_re.continuousAt.eventually (le_mem_nhds hmz)
    have hnorm : ∀ᶠ w : ℂ in 𝓝 z, ‖w‖ ≤ ‖z‖+1 :=
      continuous_norm.continuousAt.eventually (ge_mem_nhds (lt_add_one _))
    filter_upwards [tendsto_snd.eventually (hrez.and hnorm)] with p hp i
    have hdi : 0 ≤ (d i : ℝ) := by exact_mod_cast hd i
    dsimp only [f]
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hdi]
    exact (mul_le_mul_of_nonneg_left (h p.1 p.2 (v i) hp.1 hp.2 (hv i)) hdi).trans_eq (by ring)
  have hsum (z : ℂ) (hz : 1/2 < z.re) : Summable (g z) := by
    obtain ⟨b,hb,hf⟩ := control z hz
    apply Summable.of_norm_bounded hb
    intro i
    exact le_of_tendsto ((hlim z hz i).norm) (hf.mono fun p hp ↦ hp i)
  refine ⟨hsum, hopen.tendstoLocallyUniformlyOn_iff_forall_tendsto.2 ?_⟩
  intro z hz
  obtain ⟨b,hb,hf⟩ := control z hz
  have hl := tendsto_tsum_of_dominated_convergence hb (hlim z hz) hf
  have hc : Tendsto (fun p : ℕ × ℂ ↦ ∑' i, g p.2 i) (atTop ×ˢ 𝓝 z) (𝓝 (∑' i, g z i)) := by
    apply tendsto_tsum_of_dominated_convergence hb
    · intro i
      have hne : z-v i ≠ 0 := sub_ne_zero.mpr (fun e ↦ ((hv i).trans_lt hz).ne (congrArg Complex.re e.symm))
      exact ((continuousAt_const.div (continuousAt_id.sub_const _) hne).tendsto.comp tendsto_snd)
    · have hsnd : ∀ᶠ y : ℂ in 𝓝 z, ∀ i, ‖g y i‖ ≤ b i := by
        obtain ⟨indices,hU,neighborhood,hV,hUV⟩ := Filter.mem_prod_iff.mp hf
        filter_upwards [hV, hopen.mem_nhds hz] with y hy hyz i
        have hconv := (hlim y hyz i).comp (tendsto_id.prodMk tendsto_const_nhds)
        apply le_of_tendsto hconv.norm
        filter_upwards [hU] with n hn
        exact hUV (show (n,y) ∈ indices ×ˢ neighborhood from ⟨hn,hy⟩) i
      exact tendsto_snd.eventually hsnd
  exact (hc.prodMk_nhds hl).mono_right (nhds_le_uniformity _)

open Classical in
/-- Paper: §1.4.3, p. 29. One admissible family works for all characters and all
selections of completed zeros whose multiplicities divided by one plus height
are summable. On the Euler half-plane their unregularized cutoff moments
converge locally uniformly to the absolutely convergent resolvent series. -/
theorem introTrace_cutoff_limit_of_summable_reciprocal_heights :
    ∃ h ρ : ℕ → ℝ → ℝ, IsIntroTraceApproximation h ρ ∧
      ∀ (χ : U𝔽) (P : ℂ → Prop), let E := {r : ℂ // 0 < zeroOrder(χ,r) ∧ P r}
      Summable (fun r : E ↦ (zeroOrder(χ,r.val) : ℝ) / (1+|r.val.im|)) →
        (∀ z : ℂ, Summable (fun r : E ↦ (zeroOrder(χ,r.val) : ℂ) / (z-(r.val-1/2)))) ∧
        TendstoLocallyUniformlyOn (fun n z ↦ ∑' r : E, (zeroOrder(χ,r.val) : ℂ) *
          introTraceMellin approx(h,ρ,n,z) (r.val-1/2))
          (fun z ↦ ∑' r : E, (zeroOrder(χ,r.val) : ℂ) / (z-(r.val-1/2))) atTop right(1/2) := by
  obtain ⟨h,ρ,hA,_,hb,_⟩ := introTraceApprox_exists_reference_and_sparse_moments (F := F)
  refine ⟨h,ρ,hA,?_⟩
  intro χ P E hsum
  refine ⟨fun z ↦ (introTrace_resolvent_summable_iff_reciprocal_height χ P z).mpr hsum,?_⟩
  let v (r : E) := r.val-1/2
  let d (r : E) := zeroOrder(χ,r.val)
  have hv (r : E) : (v r).re ≤ 1/2 := by
    simpa only [v,Complex.sub_re,Complex.div_ofNat_re,Complex.one_re] using
      ((abs_lt.mp (introTrace_positive_divisor_in_critical_strip χ r.val r.property.1)).2.le)
  have hweight : Summable (fun r ↦ (d r : ℝ) / (1+|(v r).im|)) := by
    simpa only [d,v,Complex.sub_im,Complex.div_ofNat_im,Complex.one_im,zero_div,sub_zero] using hsum
  exact (introTraceApprox_sparse_moments_limit h ρ hA hb v d hv (fun r ↦ r.property.1.le) hweight).2

open Classical in
/-- Paper: §1.4.3, p. 29. For every number field and unitary Hecke character,
the inverse first powers of the zero heights, counted with multiplicity, have
divergent sum in every full window. -/
theorem introTrace_completed_zeros_not_summable_reciprocal_height (χ : U𝔽)
    (a : ℝ) (ha : 1/2 ≤ a) :
    ¬ Summable (fun r : windowZeros(χ, a) ↦ (zeroOrder(χ, r.val) : ℝ) / (1+|r.val.im|)) := by
  intro hsum
  obtain ⟨h,ρ,hA,_,hb,_⟩ := introTraceApprox_exists_reference_and_sparse_moments (F := F)
  let v (r : windowZeros(χ,a)) := r.val-1/2
  let d (r : windowZeros(χ,a)) := zeroOrder(χ,r.val)
  have hv (r : windowZeros(χ,a)) : (v r).re ≤ 1/2 := by
    simpa only [v,Complex.sub_re,Complex.div_ofNat_re,Complex.one_re] using
      ((abs_lt.mp (introTrace_positive_divisor_in_critical_strip χ r.val r.property.1)).2.le)
  have hweight : Summable (fun r ↦ (d r : ℝ)/(1+|(v r).im|)) := by
    simpa only [d,v,Complex.sub_im,Complex.div_ofNat_im,Complex.one_im,zero_div,sub_zero] using hsum
  have hs := (introTraceApprox_sparse_moments_limit h ρ hA hb v d hv
    (fun r ↦ r.property.1.le) hweight).2.tendsto_at (a := (2:ℂ)) (by norm_num)
  have hr := (Complex.continuous_re.tendsto _).comp hs
  exact not_tendsto_nhds_of_tendsto_atBot (introTraceApprox_full_window_spectral_tendsto_atBot χ h ρ hA a ha) _ hr

open Classical in
/-- Paper: §1.4.3, p. 29. The unsubtracted resolvent over a full critical-strip
window is never summable, at any complex parameter. -/
theorem introTrace_full_resolvent_not_summable (χ : U𝔽) (a : ℝ) (ha : 1/2 ≤ a) (z : ℂ) :
    ¬ Summable (fun r : windowZeros(χ,a) ↦ (zeroOrder(χ,r.val) : ℂ) / (z-(r.val-1/2))) :=
  fun h ↦ introTrace_completed_zeros_not_summable_reciprocal_height χ a ha
    ((introTrace_resolvent_summable_iff_reciprocal_height χ (fun r ↦ |r.re-1/2| < a) z).mp h)

/-- Termwise integration of an absolutely summable Fourier series keeps the primitive
uniformly bounded when its nonzero frequencies are bounded away from zero. -/
private theorem introTrace_vertical_series_bounded_primitive {ι : Type*} (a : ι → ℂ)
    (u : ι → ℝ) (ha : Summable a) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ i, a i = 0 ∨ d ≤ u i) :
    ∃ P : ℝ → ℝ, ∃ C : ℝ, (∀ t, |P t| ≤ C) ∧ ∀ t : ℝ,
      HasDerivAt P (∑' i, a i * Complex.exp (((-t * u i : ℝ) : ℂ) * Complex.I)).re t := by
  let k (i : ι) : ℂ := -(u i : ℂ) * Complex.I
  let E (i : ι) (t : ℝ) := Complex.exp (((-t * u i : ℝ) : ℂ) * Complex.I)
  let b (i : ι) (t : ℝ) := (a i / k i) * E i t
  have hE (i : ι) (t : ℝ) : ‖E i t‖ = 1 := by
    dsimp only [E]
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hkn (i : ι) : ‖k i‖ = |u i| := by simp [k]
  have hB (i : ι) (t : ℝ) : ‖b i t‖ ≤ ‖a i‖ / d := by
    simp only [b, norm_mul, hE, mul_one, norm_div, hkn]
    rcases hgap i with h | h
    · simp [h]
    · exact div_le_div_of_nonneg_left (norm_nonneg _) hd (h.trans (le_abs_self _))
  have hdE (i : ι) (t : ℝ) : HasDerivAt (E i) (E i t * k i) t := by
    have h := ((hasDerivAt_id (t : ℂ)).mul_const (k i)).cexp.comp_ofReal
    convert h using 1
    · ext y
      dsimp [E, k]
      push_cast
      ring_nf
    · dsimp [E, k]
      push_cast
      congr 1 <;> ring_nf
  have hdb (i : ι) (t : ℝ) : HasDerivAt (b i) (a i * E i t) t := by
    rcases hgap i with h | h
    · simpa [b, h] using (hasDerivAt_const t (0 : ℂ))
    have hk : k i ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hd.trans_le h).ne')) Complex.I_ne_zero
    convert (hdE i t).const_mul (a i / k i) using 1
    field_simp
  have hmaj := ha.norm.div_const d
  have hbsum (t : ℝ) := hmaj.of_norm_bounded (hB · t)
  refine ⟨fun t ↦ (∑' i, b i t).re, ∑' i, ‖a i‖ / d, fun t ↦ ?_, fun t ↦ ?_⟩
  · exact (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm (hbsum t).norm).trans
      ((hbsum t).norm.tsum_le_tsum (hB · t) hmaj))
  · apply Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    exact hasDerivAt_tsum ha.norm hdb (fun i y ↦ by rw [norm_mul, hE, mul_one])
      (hbsum 0) t

/-- Paper: §1.4.3, p. 29. On every vertical line in the Euler half-plane, the real part
of the finite Hecke logarithmic derivative has a bounded real primitive. -/
theorem introTrace_finite_logDeriv_vertical_re_bounded_primitive
    (χ : U𝔽) (σ : ℝ) (hσ : 1 < σ) :
    ∃ P : ℝ → ℝ, ∃ C : ℝ, (∀ t, |P t| ≤ C) ∧ ∀ t : ℝ,
      HasDerivAt P (logDeriv finiteL(χ) ((σ : ℂ) + t * Complex.I)).re t := by
  classical
  let J := {I : Ideal (𝓞 F) // I ≠ ⊥}
  let N (j : J) : ℝ := j.val.absNorm
  let w (j : J) := heckeIdealVonMangoldt (ideleClassNormTwist χ 0) j.val
  let a (j : J) := -w j / (N j : ℂ) ^ (σ : ℂ)
  let u (j : J) := Real.log (N j)
  have hN (j : J) : 0 < N j := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr j.property)
  have he (s : ℂ) (hs : 1 < s.re) := (finiteHeckeL_logDeriv_hasSum_ideals χ finiteL(χ)
    (finiteHeckeL_exists_continuation χ).choose_spec.1 (finiteHeckeL_exists_continuation χ).choose_spec.2 ⟨s, hs⟩).2.2
  have ha : Summable a := by
    simpa only [a, w, N, Complex.ofReal_natCast] using (he σ hσ).summable
  have hgap (j : J) : a j = 0 ∨ Real.log 2 ≤ u j := by
    by_cases h : 2 ≤ j.val.absNorm
    · exact Or.inr (Real.log_le_log (by norm_num) (by dsimp only [u, N]; exact_mod_cast h))
    have habs : j.val.absNorm = 1 := by
      have hj := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr j.property)
      omega
    have none : ¬ ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ j.val = v.asIdeal ^ k := by
      rintro ⟨v, k, hk, heq⟩
      have hn : 1 < v.asIdeal.absNorm ^ k := one_lt_pow₀ (NumberField.HeightOneSpectrum.one_lt_absNorm v) hk.ne'
      rw [← map_pow, ← heq, habs] at hn
      exact hn.false
    exact Or.inl (by simp [a, w, heckeIdealVonMangoldt, idealVonMangoldt, none])
  obtain ⟨P, C, hP, hD⟩ := introTrace_vertical_series_bounded_primitive a u ha (Real.log_pos (by norm_num)) hgap
  refine ⟨P, C, hP, fun t ↦ ?_⟩
  have h := he ((σ : ℂ) + t * Complex.I) (by simpa using hσ)
  have heq (j : J) : a j * Complex.exp (((-t * u j : ℝ) : ℂ) * Complex.I) =
      -w j / (N j : ℂ) ^ ((σ : ℂ) + t * Complex.I) := by
    have hn : (N j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hN j).ne'
    rw [Complex.cpow_add _ _ hn]
    have hu : (N j : ℂ) ^ ((t : ℂ) * Complex.I) =
        Complex.exp (-((((-t * u j : ℝ) : ℂ) * Complex.I))) := by
      rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (hN j).le]
      congr 1
      dsimp [u]
      push_cast
      ring
    rw [hu, Complex.exp_neg]
    dsimp only [a]
    rw [← div_div, div_inv_eq_mul]
  have hsum : (∑' j : J, a j * Complex.exp (((-t * u j : ℝ) : ℂ) * Complex.I)) =
      logDeriv finiteL(χ) ((σ : ℂ) + t * Complex.I) := by
    rw [tsum_congr heq]
    simpa only [w, N, Complex.ofReal_natCast] using h.tsum_eq
  rw [← hsum]
  exact hD t

private theorem introTrace_oddKernel_even_integral (f : ℝ → ℝ) (he : ∀ t, f (-t) = f t) (T : ℝ) :
    ∫ t in -T..T, t / (1 + t ^ 2) * f t = 0 := by
  let g (t : ℝ) := t / (1 + t ^ 2) * f t
  have e : (fun t ↦ g (-t)) = fun t ↦ -g t := by funext t; simp [g, he, neg_div]
  have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) g
  rw [e, intervalIntegral.integral_neg, neg_neg] at h
  change ∫ t in -T..T, g t = 0
  linarith

/-- An odd Cauchy kernel pairs convergently with a derivative whose primitive
grows at most as the square root of the absolute height. -/
private theorem introTrace_oddKernel_sublinear_primitive
    (f P : ℝ → ℝ) (hf : Continuous f) (C : ℝ)
    (hP : ∀ t, |P t| ≤ C * (1 + t ^ 2) ^ (1 / 4 : ℝ)) (hdP : ∀ t, HasDerivAt P (f t) t) :
    ∃ B : ℝ, Tendsto (fun T : ℝ ↦ ∫ t in -T..T, t / (1 + t ^ 2) * f t) atTop (𝓝 B) := by
  let D (t : ℝ) := 1 + t ^ 2
  let w (t : ℝ) := t / D t
  let v (t : ℝ) := (1 - t ^ 2) / (D t) ^ 2
  have hD (t : ℝ) : 0 < D t := by dsimp [D]; positivity
  have hderiv (t : ℝ) : HasDerivAt w (v t) t := by
    convert (hasDerivAt_id t).div ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).pow 2))
      (hD t).ne' using 1
    · rfl
    · dsimp [v, D]; ring
  have hw : Continuous w := continuous_iff_continuousAt.mpr fun t ↦ (hderiv t).continuousAt
  have hv : Continuous v := by dsimp [v, D]; fun_prop (disch := intro t; positivity)
  have hpc : Continuous P := continuous_iff_continuousAt.mpr fun t ↦ (hdP t).continuousAt
  have hit : Integrable (fun t : ℝ ↦ (D t) ^ (-(3 : ℝ) / 4)) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 3 / 2) (by norm_num)
    simpa [D, Real.norm_eq_abs, sq_abs, show -(3 / 2 : ℝ) / 2 = -3 / 4 by norm_num] using h
  have hi : Integrable (fun t ↦ v t * P t) := by
    apply (hit.const_mul C).mono' (hv.mul hpc).aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
    change ‖v t * P t‖ ≤ C * D t ^ (-3 / 4 : ℝ)
    rw [Real.norm_eq_abs, abs_mul]
    have hvb : |v t| ≤ (D t)⁻¹ := by
      dsimp only [v]
      rw [abs_div, abs_of_pos (sq_pos_of_pos (hD t)), div_le_iff₀ (sq_pos_of_pos (hD t))]
      rw [show (D t)⁻¹ * D t ^ 2 = D t by field_simp]
      exact abs_le.mpr ⟨by dsimp [D]; linarith, by dsimp [D]; linarith [sq_nonneg t]⟩
    calc
      _ ≤ (D t)⁻¹ * (C * (D t) ^ (1 / 4 : ℝ)) := mul_le_mul hvb (hP t) (abs_nonneg _) (inv_nonneg.mpr (hD t).le)
      _ = C * (D t) ^ (-(3 : ℝ) / 4) := by
        rw [← Real.rpow_neg_one, show -(3 : ℝ) / 4 = -1 + 1 / 4 by norm_num, Real.rpow_add (hD t)]
        ring
  have hbound (t : ℝ) : |w t * P t| ≤ C * (D t) ^ (-(1 : ℝ) / 4) := by
    have ht : |t| ≤ (D t) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.le_sqrt (abs_nonneg _) (hD t).le).mpr (by simp [D, sq_abs])
    have h := mul_le_mul (div_le_div_of_nonneg_right ht (hD t).le) (hP t)
      (abs_nonneg _) (div_nonneg (Real.rpow_nonneg (hD t).le _) (hD t).le)
    rw [abs_mul, show |w t| = |t|/(D t) by dsimp only [w]; rw [abs_div, abs_of_pos (hD t)]]
    apply h.trans_eq
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    calc
      _ = C * ((D t) ^ (1 / 2 : ℝ) * (D t) ^ (-1 : ℝ) * (D t) ^ (1 / 4 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add (hD t), ← Real.rpow_add (hD t)]; norm_num
  have hDt : Tendsto D atTop atTop := tendsto_atTop_mono (fun t ↦ (by dsimp [D]; linarith : t ^ 2 ≤ D t)) (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have hlim : Tendsto (fun t : ℝ ↦ C * (D t) ^ (-(1 : ℝ) / 4)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, neg_div, mul_zero] using (((tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp hDt).const_mul C)
  have hb (U : ℝ → ℝ) (hU : ∀ t, D (U t) = D t) :
      Tendsto (fun t ↦ w (U t) * P (U t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    exact Eventually.of_forall fun t ↦ by simpa [Real.norm_eq_abs, hU] using hbound (U t)
  have hR := hb id (fun _ ↦ rfl)
  have hL := hb Neg.neg (by intro t; simp [D])
  have hI := intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id
  refine ⟨-∫ t, v t * P t, (show Tendsto (fun T : ℝ ↦ w T * P T - w (-T) * P (-T) - ∫ t in -T..T, v t * P t)
      atTop (𝓝 (-∫ t, v t * P t)) by simpa using (hR.sub hL).sub hI).congr ?_⟩
  intro T
  exact (intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hw.continuousOn hpc.continuousOn
    (fun t _ ↦ hderiv t) (fun t _ ↦ hdP t) (hv.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm

/-- The odd-kernel pairing with the real finite logarithmic derivative converges
under symmetric truncation on every Euler line for every unitary character. -/
private theorem introTrace_finite_logDeriv_oddKernel_tendsto
    (χ : U𝔽) (σ : ℝ) (hσ : 1 < σ) :
    let f (t : ℝ) := (logDeriv finiteL(χ) ((σ : ℂ) + (t : ℂ) * Complex.I)).re
    Continuous f ∧ ∃ B : ℝ, Tendsto (fun T : ℝ ↦ ∫ t in -T..T, t / (1 + t ^ 2) * f t) atTop (𝓝 B) := by
  intro f
  have hc : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro t
    let s := (σ : ℂ) + (t : ℂ) * Complex.I
    have hs : 1 < s.re := by simpa [s] using hσ
    obtain ⟨hL, hn, _⟩ := finiteHeckeL_logDeriv_hasSum_ideals χ finiteL(χ)
      (finiteHeckeL_exists_continuation χ).choose_spec.1 (finiteHeckeL_exists_continuation χ).choose_spec.2 ⟨s, hs⟩
    exact Complex.continuous_re.continuousAt.comp ((hL.deriv.div hL hn).continuousAt.comp
      (f := fun t : ℝ ↦ (σ : ℂ) + (t : ℂ) * Complex.I) (by fun_prop))
  obtain ⟨P, C, hP, hdP⟩ := introTrace_finite_logDeriv_vertical_re_bounded_primitive χ σ hσ
  refine ⟨hc, introTrace_oddKernel_sublinear_primitive f P hc C (fun t ↦ ?_) hdP⟩
  have hC : 0 ≤ C := (abs_nonneg (P 0)).trans (hP 0)
  exact (hP t).trans (le_mul_of_one_le_right hC (Real.one_le_rpow (by nlinarith [sq_nonneg t]) (by norm_num)))

/-- Translating an even continuous profile of logarithmic growth has a convergent
symmetric pairing with the odd Cauchy kernel. -/
private theorem introTrace_oddKernel_log_even_translate (f : ℝ → ℝ) (hf : Continuous f)
    (he : ∀ t, f (-t) = f t) (A c : ℝ) (hA : ∀ t, |f t| ≤ A + 4 * Real.log (1 + |t|)) :
    ∃ B : ℝ, Tendsto (fun T : ℝ ↦ ∫ t in -T..T, t / (1 + t ^ 2) * f (t + c)) atTop (𝓝 B) := by
  let J (x : ℝ) := ∫ t in (0 : ℝ)..x, f t
  let P (t : ℝ) := J (t + c) - J t
  have hJ (t : ℝ) : HasDerivAt J (f t) t := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 t) hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hd (t : ℝ) : HasDerivAt P (f (t + c) - f t) t := by
    simpa [P, Function.comp_def] using ((hJ (t + c)).comp t ((hasDerivAt_id' t).add_const c)).fun_sub (hJ t)
  let C := |A|+4 * |Real.log (2 + |c|)|+16
  have hP (t : ℝ) : |P t| ≤ (C * |c|) * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    have hEq : P t = ∫ x in t..t + c, f x :=
      (eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 t) (hf.intervalIntegrable t (t + c)))).symm
    rw [hEq, ← Real.norm_eq_abs]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := t + c) (f := f)
      (C := C * (1 + t ^ 2) ^ (1 / 4 : ℝ)) (fun x hx ↦ ?_)
    · simpa [add_sub_cancel_left, mul_right_comm] using hh
    have hx' : |x| ≤ |t|+|c| := by
      rcases le_total t (t + c) with h|h
      · rw [Set.uIoc_of_le h] at hx
        exact abs_le.mpr ⟨by linarith [hx.1, neg_abs_le t, abs_nonneg c],
          by linarith [hx.2, le_abs_self t, le_abs_self c]⟩
      · rw [Set.uIoc_of_ge h] at hx
        exact abs_le.mpr ⟨by linarith [hx.1, neg_abs_le t, neg_abs_le c],
          by linarith [hx.2, le_abs_self t, abs_nonneg c]⟩
    have hbase : (1 : ℝ) ≤ 1 + t ^ 2 := by linarith [sq_nonneg t]
    have hmain : 1 + |x| ≤ (2 + |c|) * (1 + t ^ 2) := by
      have ht : |t| ≤ 1 + t ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t + 1), sq_nonneg (t - 1)]
      nlinarith [mul_nonneg (abs_nonneg c) (sq_nonneg t)]
    have hlog := Real.log_le_log (by positivity : 0 < 1 + |x|) hmain
    rw [Real.log_mul (by positivity) (by positivity)] at hlog
    have hr := Real.log_le_rpow_div (x := 1 + t ^ 2) (by positivity) (by norm_num : (0 : ℝ)<1 / 4)
    have ho := Real.one_le_rpow hbase (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [Real.norm_eq_abs]
    dsimp only [C]
    nlinarith [hA x, le_abs_self A, le_abs_self (Real.log (2 + |c|)),
      mul_nonneg (abs_nonneg A) (sub_nonneg.mpr ho),
      mul_nonneg (abs_nonneg (Real.log (2 + |c|))) (sub_nonneg.mpr ho)]
  have hc : Continuous (fun t ↦ f (t + c) - f t) := (hf.comp (continuous_id.add_const c)).sub hf
  obtain ⟨B, hB⟩ := introTrace_oddKernel_sublinear_primitive _ P hc _ hP hd
  refine ⟨B, hB.congr ?_⟩
  intro T
  simp_rw [mul_sub]
  have hq : Continuous (fun t : ℝ ↦ t / (1 + t ^ 2)) := by fun_prop (disch := intro t; positivity)
  rw [intervalIntegral.integral_sub (f := fun t : ℝ ↦ t / (1 + t ^ 2) * f (t + c)) (g := fun t : ℝ ↦ t / (1 + t ^ 2) * f t) ((hq.mul (hf.comp (continuous_id.add_const c))).intervalIntegrable _ _)
    ((hq.mul hf).intervalIntegrable _ _), introTrace_oddKernel_even_integral f he T, sub_zero]

/-- The positive Frullani kernel for a change of the real Laplace parameter is
integrable, and its mass is the logarithm of the ratio of the parameters. -/
private theorem introTrace_frullani_height_increment (u v : ℝ) (hu : 0 < u) (hV : 0 ≤ v) :
    let f (x : ℝ) := x⁻¹ * (Real.exp (-u * x) - Real.exp (-(u + v) * x))
    IntegrableOn f (Ioi 0) ∧ ∫ x in Ioi 0, f x = Real.log ((u + v) / u) := by
  intro f
  have hd : IntegrableOn (fun x : ℝ ↦ v * Real.exp (-u * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hu) 0).const_mul v
  have hf : IntegrableOn f (Ioi 0) := by
    apply hd.mono' (by dsimp [f]; fun_prop)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x (hx : 0 < x)
    have he := Real.add_one_le_exp (-v * x)
    have hp : Real.exp (-v * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hE := Real.exp_pos (-u * x)
    have hmul : Real.exp (-(u + v) * x) = Real.exp (-u * x) * Real.exp (-v * x) := by
      rw [← Real.exp_add]; congr 1; ring
    change ‖x⁻¹ * (Real.exp (-u * x) - Real.exp (-(u + v) * x))‖ ≤ _
    rw [hmul, ← mul_one_sub, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ hx]
    calc
      _ ≤ Real.exp (-u * x) * (v * x) := mul_le_mul_of_nonneg_left (by linarith) hE.le
      _ = _ := by ring
  refine ⟨hf, ?_⟩
  have h := Frullani.integral_Ioi_eq (f := fun x : ℝ ↦ Real.exp (-x)) (L := 1) (R := 0)
    ((by fun_prop : Continuous fun x : ℝ ↦ Real.exp (-x)).locallyIntegrable.locallyIntegrableOn _)
    hu (show 0 < u + v by linarith)
    (by simpa using ((by fun_prop : Continuous fun x : ℝ ↦ Real.exp (-x)).tendsto 0).mono_left nhdsWithin_le_nhds)
    (by simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
    (by simpa only [smul_eq_mul, neg_mul, f] using hf)
  simpa only [smul_eq_mul, sub_zero, mul_one, neg_mul, f] using h

/-- Uniformly in the frequency, an oscillatory difference is bounded by a
positive exponentially damped difference at the absolute frequency. -/
private theorem introTrace_norm_oscillation_le_exp_loss (y : ℝ) :
    ‖Complex.exp (Complex.I * (y : ℂ)) - 1‖ ≤ 4 * (1 - Real.exp (-|y|)) := by
  let q := Real.exp (-|y|)
  have hq : 0 < q := Real.exp_pos _
  have hq₁ : q ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg y))
  have he : (1 + |y|) * q ≤ 1 := by
    calc
      _ ≤ Real.exp |y| * q := mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp |y|]) hq.le
      _ = 1 := by rw [show q = Real.exp (-|y|) from rfl, ← Real.exp_add]; simp
  change _ ≤ 4 * (1 - q)
  by_cases h : |y| ≤ 1
  · have hle := mul_le_mul_of_nonneg_right (show 1 + |y| ≤ 2 by linarith) (sub_nonneg.mpr hq₁)
    exact (Real.norm_exp_I_mul_ofReal_sub_one_le (x := y)).trans (by rw [Real.norm_eq_abs]; nlinarith)
  have hb := mul_le_mul_of_nonneg_right (show 2 ≤ 1 + |y| by linarith) hq.le
  calc
    _ ≤ ‖Complex.exp (Complex.I * (y : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [Complex.norm_exp]
    _ ≤ _ := by linarith

/-- The difference between the vertical and real Gauss digamma kernels is
bounded by two positive Laplace kernels, one of Frullani type. -/
private theorem introTrace_digamma_vertical_kernel_bound (u v x : ℝ) (hx : 0 < x) :
    ‖gaussDigammaDifferenceKernel 1 ((u : ℂ) + (v : ℂ) * Complex.I) x -
      gaussDigammaDifferenceKernel 1 (u : ℂ) x‖ ≤
      4 * ((Real.exp (-u * x) - Real.exp (-(u + |v|) * x)) +
        x⁻¹ * (Real.exp (-u * x) - Real.exp (-(u + |v|) * x))) := by
  let E := Real.exp (-u * x)
  let D := 1 - Real.exp (-x)
  have hE : 0 < E := Real.exp_pos _
  have hD : 0 < D := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
  have hi : D⁻¹ ≤ 1 + x⁻¹ := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    rw [inv_le_iff_one_le_mul₀ hD, add_mul, one_mul]
    dsimp only [D]
    field_simp
    nlinarith
  have hf : E * (1 - Real.exp (-|v * x|)) =
      Real.exp (-u * x) - Real.exp (-(u + |v|) * x) := by
    dsimp only [E]
    rw [mul_sub, mul_one, ← Real.exp_add, abs_mul, abs_of_pos hx]
    congr 2
    ring_nf
  have hfactor : gaussDigammaDifferenceKernel 1 ((u : ℂ) + (v : ℂ) * Complex.I) x -
      gaussDigammaDifferenceKernel 1 (u : ℂ) x =
      (E : ℂ) * (1 - Complex.exp (Complex.I * ((-(v * x) : ℝ) : ℂ))) / (D : ℂ) := by
    dsimp only [gaussDigammaDifferenceKernel, E, D]
    push_cast
    rw [show -((u : ℂ) + (v : ℂ) * Complex.I) * (x : ℂ) =
        -(u : ℂ) * (x : ℂ) + Complex.I * (-((v : ℂ) * (x : ℂ))) by ring_nf, Complex.exp_add]
    ring_nf
  rw [hfactor, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hE.le, Real.norm_of_nonneg hD.le, norm_sub_rev, div_eq_mul_inv]
  have hp := introTrace_norm_oscillation_le_exp_loss (-(v * x))
  rw [abs_neg] at hp
  have hn := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg (v * x))))
  calc
    _ ≤ (E * (4 * (1 - Real.exp (-|v * x|)))) * (1 + x⁻¹) := by gcongr
    _ = 4 * (E * (1 - Real.exp (-|v * x|)) + x⁻¹ * (E * (1 - Real.exp (-|v * x|)))) := by ring_nf
    _ = _ := by rw [hf]

/-- A fixed vertical line in the right half-plane has an explicit logarithmic
digamma bound, uniform in both signs of the imaginary part. -/
private theorem introTrace_digamma_vertical_log_bound (u v : ℝ) (hu : 0 < u) :
    ‖Complex.digamma ((u : ℂ) + (v : ℂ) * Complex.I) - Complex.digamma (u : ℂ)‖ ≤
      4 * (u⁻¹ + Real.log ((u + |v|) / u)) := by
  let w : ℂ := (u : ℂ) + (v : ℂ) * Complex.I
  have hk (s : ℂ) (hs : 0 < s.re) : IntegrableOn (gaussDigammaDifferenceKernel 1 s) (Ioi 0) ∧
      (∫ x in Ioi 0, gaussDigammaDifferenceKernel 1 s x) = Complex.digamma s - Complex.digamma 1 := by
    simpa only [Complex.ofReal_one, div_one] using
      integral_gaussDigammaDifferenceKernel (d := 1) (w := s) one_pos (by simpa using hs)
  obtain ⟨hw, ew⟩ := hk w (by simpa [w] using hu)
  obtain ⟨hreal, er⟩ := hk (u : ℂ) (by simpa using hu)
  let f (x : ℝ) := x⁻¹ * (Real.exp (-u * x) - Real.exp (-(u + |v|) * x))
  obtain ⟨hf, ef⟩ := introTrace_frullani_height_increment u |v| hu (abs_nonneg _)
  have hU : IntegrableOn (fun x : ℝ ↦ Real.exp (-u * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hu) 0
  have eqn : Complex.digamma w - Complex.digamma (u : ℂ) =
      ∫ x in Ioi 0, gaussDigammaDifferenceKernel 1 w x - gaussDigammaDifferenceKernel 1 (u : ℂ) x := by
    rw [integral_sub hw hreal, ew, er]
    ring
  change ‖Complex.digamma w - Complex.digamma (u : ℂ)‖ ≤ _
  rw [eqn]
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), 4 * (Real.exp (-u * x) + f x) := by
      apply norm_integral_le_of_norm_le ((hU.add hf).const_mul 4)
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x (hx : 0 < x)
      apply (introTrace_digamma_vertical_kernel_bound u v x hx).trans
      exact mul_le_mul_of_nonneg_left (add_le_add_left (sub_le_self _ (Real.exp_pos _).le) _) (by norm_num)
    _ = _ := by
      rw [integral_const_mul, integral_add hU hf, ef, integral_exp_mul_Ioi (neg_neg_of_pos hu)]
      simp [div_eq_mul_inv]

/-- Fixed affine changes of height preserve the logarithmic bound on a
positive vertical line. -/
private theorem introTrace_digamma_affine_height_bound (u k b : ℝ) (hu : 0 < u) :
    ∃ A : ℝ, ∀ t : ℝ, ‖Complex.digamma ((u : ℂ) + ((k * t + b : ℝ) : ℂ) * Complex.I)‖ ≤
      A + 4 * Real.log (1 + |t|) := by
  let c := (u + |k|+|b|) / u
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨‖Complex.digamma (u : ℂ)‖ + 4 * (u⁻¹ + Real.log c), fun t ↦ ?_⟩
  have ht : 0 < 1 + |t| := by positivity
  have harg : (u + |k * t + b|) / u ≤ c * (1 + |t|) := by
    dsimp only [c]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hu]
    have hkb := abs_add_le (k * t) b
    rw [abs_mul] at hkb
    nlinarith [mul_nonneg hu.le (abs_nonneg t), mul_nonneg (abs_nonneg b) (abs_nonneg t), abs_nonneg k]
  have hlog := Real.log_le_log (by positivity : 0 < (u + |k * t + b|) / u) harg
  rw [Real.log_mul hc.ne' ht.ne'] at hlog
  have h := introTrace_digamma_vertical_log_bound u (k * t + b) hu
  calc
    _ ≤ ‖Complex.digamma ((u : ℂ) + ((k * t + b : ℝ) : ℂ) * Complex.I) - Complex.digamma (u : ℂ)‖ +
        ‖Complex.digamma (u : ℂ)‖ := (norm_le_insert' _ _).trans_eq (add_comm _ _)
    _ ≤ _ := by linarith

/-- The digamma function commutes with complex conjugation. -/
private theorem introTrace_digamma_conj (z : ℂ) :
    Complex.digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Complex.digamma z) := by
  have hg : (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) = Complex.Gamma := by
    funext w
    simp only [Function.comp_apply, Complex.Gamma_conj, Complex.conj_conj]
  have hd : deriv Complex.Gamma ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (deriv Complex.Gamma z) := by
    conv_lhs => rw [← hg, deriv_conj_conj]
    simp only [Function.comp_apply, Complex.conj_conj]
  simp only [Complex.digamma_def, logDeriv_apply, hd, Complex.Gamma_conj, map_div₀]

/-- Each affine shift of the real digamma profile has a symmetric odd-kernel
pairing on every fixed positive vertical line. -/
private theorem introTrace_oddKernel_affine_digamma (u k c : ℝ) (hu : 0 < u) :
    let f (t : ℝ) := (Complex.digamma ((u : ℂ) + ((k * (t + c) : ℝ) : ℂ) * Complex.I)).re
    Continuous f ∧ ∃ B : ℝ, Tendsto (fun T : ℝ ↦ ∫ t in -T..T, t / (1 + t ^ 2) * f t) atTop (𝓝 B) := by
  let f (t : ℝ) := (Complex.digamma ((u : ℂ) + ((k * t : ℝ) : ℂ) * Complex.I)).re
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro t
    let z (y : ℝ) : ℂ := (u : ℂ) + ((k * y : ℝ) : ℂ) * Complex.I
    have hz : 0 < (z t).re := by simpa [z] using hu
    have hGa : AnalyticOnNhd ℂ Complex.Gamma {z | 0 < z.re} :=
      (show DifferentiableOn ℂ Complex.Gamma {z | 0 < z.re} from fun s hs ↦
        (Complex.hasDerivAt_Gamma_of_re_pos hs).differentiableAt.differentiableWithinAt).analyticOnNhd
          (isOpen_lt continuous_const Complex.continuous_re)
    have hp : AnalyticAt ℂ Complex.digamma (z t) :=
      (hGa _ hz).deriv.div (hGa _ hz) (Complex.Gamma_ne_zero_of_re_pos hz)
    exact Complex.continuous_re.continuousAt.comp (hp.continuousAt.comp (show ContinuousAt z t by dsimp [z]; fun_prop))
  have he (t : ℝ) : f (-t) = f t := by
    have e : (u : ℂ) + ((k * (-t) : ℝ) : ℂ) * Complex.I =
        (starRingEnd ℂ) ((u : ℂ) + ((k * t : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    simp only [f, e, introTrace_digamma_conj, Complex.conj_re]
  obtain ⟨A, hA⟩ := introTrace_digamma_affine_height_bound u k 0 hu
  have hb (t : ℝ) : |f t| ≤ A + 4 * Real.log (1 + |t|) := by
    exact (Complex.abs_re_le_norm _).trans (by simpa [add_zero] using hA t)
  exact ⟨hf.comp (continuous_id.add_const c), introTrace_oddKernel_log_even_translate f hf he A c hb⟩

/-- The finite sum of all archimedean logarithmic derivatives has a convergent
symmetric odd-kernel integral on every positive vertical line. -/
private theorem introTrace_heckeGamma_oddKernel_tendsto (χ : U𝔽) (σ : ℝ) (hσ : 0 < σ) :
    let f (t : ℝ) := (logDeriv (heckeGammaFactor χ) ((σ : ℂ) + (t : ℂ) * Complex.I)).re
    Continuous f ∧ ∃ B : ℝ, Tendsto (fun T : ℝ ↦ ∫ t in -T..T, t / (1 + t ^ 2) * f t) atTop (𝓝 B) := by
  classical
  let q (t : ℝ) := t / (1 + t ^ 2)
  have hq : Continuous q := by dsimp [q]; fun_prop (disch := intro t; positivity)
  let s (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hs (t : ℝ) : 0 < (s t).re := by simpa [s] using hσ
  let shift (v : InfinitePlace F) : ℂ :=
    if hv : v.IsReal then
      let p := (realHeckeCharacter_parameters χ v hv).exists.choose
      p.1 + (p.2.val : ℂ)
    else
      let p := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      p.1 + (p.2.natAbs : ℂ) / 2
  let g (v : InfinitePlace F) (t : ℝ) :=
    (logDeriv (fun z ↦ if v.IsReal then Complex.Gammaℝ (z + shift v)
      else Complex.Gammaℂ (z + shift v) / 2) (s t)).re
  have hlocal (v : InfinitePlace F) : Continuous (g v) ∧ ∃ B : ℝ,
      Tendsto (fun T : ℝ ↦ ∫ t in -T..T, q t * g v t) atTop (𝓝 B) := by
    let k : ℝ := if v.IsReal then 1 / 2 else 1
    let b := shift v
    let D : ℂ := if v.IsReal then (Real.pi : ℂ) else 2 * (Real.pi : ℂ)
    have hk : 0 < k := by dsimp [k]; split_ifs <;> norm_num
    have hb : 0 ≤ b.re := by
      dsimp only [b, shift]; split_ifs with hv
      · have h := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
        simp only [Complex.add_re, h, zero_add, Complex.natCast_re]; positivity
      · have h := (complexHeckeCharacter_parameters χ v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose_spec.1
        simp only [Complex.add_re, h, zero_add, Complex.div_ofNat_re, Complex.natCast_re]; positivity
    let u := k * (σ + b.re)
    let d (t : ℝ) := (Complex.digamma ((u : ℂ) + ((k * (t + b.im) : ℝ) : ℂ) * Complex.I)).re
    let c := (Complex.log D).re
    obtain ⟨hd, B, hB⟩ := introTrace_oddKernel_affine_digamma u k b.im (mul_pos hk (add_pos_of_pos_of_nonneg hσ hb))
    change Continuous d at hd
    change Tendsto (fun T : ℝ ↦ ∫ t in -T..T, q t * d t) atTop (𝓝 B) at hB
    have e : g v = fun t ↦ k * (d t - c) := by
      funext t
      have he : (k : ℂ) * (s t + b) = (u : ℂ) + ((k * (t + b.im) : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [s, u, Complex.mul_re, Complex.mul_im]
      dsimp only [g]
      rw [introTrace_logDeriv_local_gamma χ v (s t) (hs t)]
      change ((k : ℂ) * (Complex.digamma ((k : ℂ) * (s t + b)) - Complex.log D)).re = _
      rw [Complex.re_ofReal_mul, he, Complex.sub_re]
    rw [e]
    refine ⟨continuous_const.mul (hd.sub continuous_const), k * B, (hB.const_mul k).congr ?_⟩
    intro T
    have hfun t : q t * (k * (d t - c)) = k * (q t * d t - q t * c) := by ring
    simp_rw [hfun, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub (f := fun t ↦ q t * d t) (g := fun t ↦ q t * c)
      ((hq.mul hd).intervalIntegrable _ _) ((hq.mul continuous_const).intervalIntegrable _ _),
      introTrace_oddKernel_even_integral (fun _ ↦ c) (fun _ ↦ rfl) T, sub_zero]
  have he : (fun t ↦ (logDeriv (heckeGammaFactor χ) (s t)).re) = fun t ↦ ∑ v, g v t := by
    funext t
    simp only [introTrace_heckeGamma_logDeriv_eq_sum χ (s t) (hs t), Complex.re_sum, g, shift]
  change Continuous (fun t ↦ (logDeriv (heckeGammaFactor χ) (s t)).re) ∧ _
  rw [he]
  choose B hB using fun v ↦ (hlocal v).2
  refine ⟨continuous_finsetSum _ (fun v _ ↦ (hlocal v).1), ∑ v, B v, (tendsto_finsetSum _ (fun v _ ↦ hB v)).congr ?_⟩
  intro T
  simp_rw [Finset.mul_sum]
  exact (intervalIntegral.integral_finsetSum
    (f := fun v t ↦ q t * g v t) (fun v _ ↦ (hq.mul (hlocal v).1).intervalIntegrable _ _)).symm

/-- The odd Cauchy kernel paired with a translated Poisson kernel increases
its width by one. -/
private theorem introTrace_oddKernel_poisson_single (δ γ : ℝ) (hδ : 0 < δ) :
    let f (t : ℝ) := t / (1 + t ^ 2) * (δ / (δ ^ 2 + (t - γ) ^ 2))
    Integrable f ∧ ∫ t, f t = Real.pi * γ / ((1 + δ) ^ 2 + γ ^ 2) := by
  intro f
  let p (t : ℝ) := 1 + t ^ 2
  let r (t : ℝ) := δ ^ 2 + (t - γ) ^ 2
  have hp (t : ℝ) : 0 < p t := by dsimp [p]; positivity
  have hr (t : ℝ) : 0 < r t := by dsimp [r]; positivity
  let d : ℝ≥0 := ⟨δ, hδ.le⟩
  have hK : Integrable (fun t ↦ δ / r t) := by
    refine ((ProbabilityTheory.integrable_cauchyPDFReal γ (γ := d)).const_mul Real.pi).congr
      (Eventually.of_forall fun t ↦ ?_)
    change Real.pi * ProbabilityTheory.cauchyPDFReal γ d t = _
    rw [ProbabilityTheory.cauchyPDFReal_def]
    change Real.pi * (Real.pi⁻¹ * δ * ((t - γ) ^ 2 + δ ^ 2)⁻¹) = δ / (δ ^ 2 + (t - γ) ^ 2)
    rw [add_comm ((t - γ) ^ 2)]
    field_simp [Real.pi_ne_zero, (hr t).ne']
  have hI : Integrable f := by
    apply hK.mono' (by dsimp [f]; fun_prop)
    apply Eventually.of_forall
    intro t
    change ‖(t / p t) * (δ / r t)‖ ≤ δ / r t
    rw [norm_mul, Real.norm_of_nonneg (div_nonneg hδ.le (hr t).le)]
    apply mul_le_of_le_one_left (div_nonneg hδ.le (hr t).le)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hp t), div_le_one (hp t)]
    dsimp [p]; rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t + 1), sq_nonneg (t - 1)]
  refine ⟨hI, ?_⟩
  by_cases hz : γ = 0
  · subst γ
    have e : (fun t ↦ f (-t)) = fun t ↦ -f t := by funext t; simp [f, neg_div]
    have h := integral_neg_eq_self (μ := volume) (f := f)
    rw [e, integral_neg] at h
    simp only [mul_zero, zero_div]
    linarith
  let X := γ ^ 2 + δ ^ 2 - 1
  let M := X ^ 2 + (2 * γ) ^ 2
  let A := δ * X / M
  let B := -δ * (2 * γ) / M
  let D := A * γ - B
  have hM : 0 < M := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hz))
  let H (t : ℝ) := (A / 2) * (Real.log (p t) - Real.log (r t)) +
    B * Real.arctan t + (D / δ) * Real.arctan ((t - γ) / δ)
  have hDer (t : ℝ) : HasDerivAt H (f t) t := by
    have dp : HasDerivAt p (2 * t) t := by
      simpa [p] using ((hasDerivAt_id' t).pow 2).const_add 1
    have dr : HasDerivAt r (2 * (t - γ)) t := by
      simpa [r] using (((hasDerivAt_id' t).sub_const γ).pow 2).const_add (δ ^ 2)
    have h := (((dp.log (hp t).ne').fun_sub (dr.log (hr t).ne')).const_mul (A / 2)).fun_add
      ((Real.hasDerivAt_arctan t).const_mul B)
    have he := h.fun_add ((((hasDerivAt_id' t).sub_const γ).div_const δ).arctan.const_mul (D / δ))
    convert he using 1
    dsimp only [H, f, p, r, A, B, D, M, X]
    have hstar : 0 < 1 + ((t - γ) / δ) ^ 2 := by positivity
    field_simp [hδ.ne', (hp t).ne', (hr t).ne', hstar.ne', hM.ne']
    ring
  have hrlim {l : Filter ℝ} (hinv : Tendsto (fun t : ℝ ↦ t⁻¹) l (𝓝 0)) (hne : ∀ᶠ t in l, t ≠ 0) :
      Tendsto (fun t ↦ Real.log (p t) - Real.log (r t)) l (𝓝 0) := by
    let R (u : ℝ) := (u ^ 2 + 1) / ((δ * u) ^ 2 + (1 - γ * u) ^ 2)
    have hR : ContinuousAt R 0 := by dsimp only [R]; fun_prop (disch := norm_num)
    have h₁ : Tendsto (fun t : ℝ ↦ p t / r t) l (𝓝 1) := by
      have h := hR.tendsto.comp hinv
      rw [show R 0 = 1 by simp [R]] at h
      apply h.congr'
      filter_upwards [hne] with t ht
      dsimp [R, p, r, Function.comp_apply]
      field_simp [ht]
    have hlog : Tendsto (fun t ↦ Real.log (p t / r t)) l (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp h₁
    exact hlog.congr (fun t ↦ Real.log_div (hp t).ne' (hr t).ne')
  have htop := hrlim (l := atTop) tendsto_inv_atTop_zero (eventually_ne_atTop 0)
  have hbot := hrlim (l := atBot) tendsto_inv_atBot_zero (eventually_ne_atBot 0)
  have haT : Tendsto (fun t : ℝ ↦ (t - γ) / δ) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-γ) tendsto_id).atTop_div_const hδ
  have haB : Tendsto (fun t : ℝ ↦ (t - γ) / δ) atBot atBot :=
    (tendsto_atBot_add_const_right atBot (-γ) tendsto_id).atBot_div_const hδ
  have hAT := tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have hAB := tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot
  have hplus := ((htop.const_mul (A / 2)).add (hAT.const_mul B)).add
    ((hAT.comp haT).const_mul (D / δ))
  have hminus := ((hbot.const_mul (A / 2)).add (hAB.const_mul B)).add
    ((hAB.comp haB).const_mul (D / δ))
  rw [integral_of_hasDerivAt_of_tendsto hDer hI hminus hplus]
  dsimp only [A, B, D]
  have hd' : 0 < (1 + δ) ^ 2 + γ ^ 2 := by positivity
  field_simp [hM.ne', hd'.ne', hδ.ne']
  dsimp only [M, X]
  ring

/-- The symmetric odd pairing with the real part of a pure-imaginary translate
of the two rational corrections is absolutely convergent, with an explicit value. -/
private theorem introTrace_oddKernel_shifted_poles (a : ℂ) (ha : a.re = 0) :
    let f (t : ℝ) := (t / (1 + t ^ 2)) * ((1 / ((2 : ℂ) + (t : ℂ) * Complex.I + a + 1 / 2) +
      1 / ((2 : ℂ) + (t : ℂ) * Complex.I + a - 1 / 2))).re
    Integrable f ∧ ∫ t, f t = (Real.pi * (-a.im) / ((7 / 2 : ℝ) ^ 2 + a.im ^ 2) +
        Real.pi * (-a.im) / ((5 / 2 : ℝ) ^ 2 + a.im ^ 2)) := by
  intro f
  let k (δ t : ℝ) := (t / (1 + t ^ 2)) * (δ / (δ ^ 2 + (t - (-a.im)) ^ 2))
  obtain ⟨h₁, e₁⟩ := introTrace_oddKernel_poisson_single (5 / 2) (-a.im) (by norm_num)
  obtain ⟨h₂, e₂⟩ := introTrace_oddKernel_poisson_single (3 / 2) (-a.im) (by norm_num)
  change Integrable (k (5 / 2)) at h₁
  change Integrable (k (3 / 2)) at h₂
  have he : f = fun t ↦ k (5 / 2) t + k (3 / 2) t := by
    funext t
    dsimp only [f, k]
    rw [Complex.add_re, mul_add]
    simp [Complex.normSq_apply, ha, Complex.mul_re, Complex.mul_im, sub_neg_eq_add]
    ring
  rw [he]
  refine ⟨h₁.add h₂, ?_⟩
  rw [integral_add h₁ h₂]
  change (∫ t, k (5 / 2) t) = _ at e₁
  change (∫ t, k (3 / 2) t) = _ at e₂
  rw [e₁, e₂]
  norm_num

open Classical in
/-- Paper: §1.4.3, p. 29. On the reference line the real part of the pole-corrected
completed logarithmic derivative has a convergent symmetric integral against
`t / (1 + t²)`. The two poles of a shifted trivial character contribute the displayed
correction to the common value of the uncorrected integral. -/
theorem introTrace_raw_completed_oddKernel_tendsto (χ : U𝔽) :
    ∃ B : ℝ, ∀ (ψ : U𝔽) (a : ℂ), a.re = 0 →
      let P (z : ℂ) := logDeriv (continuedCompletedHeckeL χ) (z + 1 / 2) +
        if ψ = 1 then 1 / (z + a + 1 / 2) + 1 / (z + a - 1 / 2) else 0
      Tendsto (fun T : ℝ ↦ ∫ t in -T..T, t / (1 + t ^ 2) * (P (2 + (t : ℂ) * Complex.I)).re)
        atTop (𝓝 (B + if ψ = 1 then
          Real.pi * (-a.im) / ((7 / 2 : ℝ) ^ 2 + a.im ^ 2) +
          Real.pi * (-a.im) / ((5 / 2 : ℝ) ^ 2 + a.im ^ 2) else 0)) := by
  classical
  let s (t : ℝ) := ((5 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let e (t : ℝ) := (logDeriv finiteL(χ) (s t)).re
  let g (t : ℝ) := (logDeriv (heckeGammaFactor χ) (s t)).re
  let q (t : ℝ) := t / (1 + t ^ 2)
  have hq : Continuous q := by dsimp only [q]; fun_prop (disch := intro t; positivity)
  obtain ⟨hg, G, hG⟩ := introTrace_heckeGamma_oddKernel_tendsto χ (5 / 2) (by norm_num)
  obtain ⟨hc, E, hE⟩ := introTrace_finite_logDeriv_oddKernel_tendsto χ (5 / 2) (by norm_num)
  change Continuous g at hg
  change Continuous e at hc
  change Tendsto (fun T : ℝ ↦ ∫ t in -T..T, q t * g t) atTop (𝓝 G) at hG
  change Tendsto (fun T : ℝ ↦ ∫ t in -T..T, q t * e t) atTop (𝓝 E) at hE
  refine ⟨G + E, fun ψ a ha ↦ ?_⟩
  intro P
  let b (t : ℝ) := q t * (if ψ = 1 then (1 / ((2 : ℂ) + (t : ℂ) * Complex.I + a + 1 / 2) +
      1 / ((2 : ℂ) + (t : ℂ) * Complex.I + a - 1 / 2)) else (0 : ℂ)).re
  have hb : Integrable b ∧ Tendsto (fun T : ℝ ↦ ∫ t in -T..T, b t) atTop
      (𝓝 (if ψ = 1 then
        Real.pi * (-a.im) / ((7 / 2 : ℝ) ^ 2 + a.im ^ 2) +
        Real.pi * (-a.im) / ((5 / 2 : ℝ) ^ 2 + a.im ^ 2) else 0)) := by
    by_cases h : ψ = 1
    · obtain ⟨hi, he⟩ := introTrace_oddKernel_shifted_poles a ha
      simp only [b, h, ite_true]
      refine ⟨hi, ?_⟩
      rw [← he]
      exact intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id
    · simp [b, h]
  apply ((hG.add hE).add hb.2).congr
  intro T
  rw [← intervalIntegral.integral_add (f := fun t ↦ q t * g t) (g := fun t ↦ q t * e t)
      ((hq.mul hg).intervalIntegrable _ _) ((hq.mul hc).intervalIntegrable _ _),
    ← intervalIntegral.integral_add (f := fun t ↦ q t * g t + q t * e t) (g := b)
      (((hq.mul hg).add (hq.mul hc)).intervalIntegrable _ _) hb.1.intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro t _
  have he : (2 + (t : ℂ) * Complex.I) + 1 / 2 = s t := by dsimp only [s]; push_cast; ring
  change q t * g t + q t * e t + b t = q t * (P (2 + (t : ℂ) * Complex.I)).re
  dsimp only [P, g, e, b]
  rw [he, introTrace_completed_logDeriv_euler χ (s := s t) (by norm_num [s, Complex.add_re, Complex.mul_re])]
  simp only [Complex.add_re]
  ring

open Classical in
/-- For a matched cutoff family the individual moments obey the reciprocal-height
bound, while subtracting the value at two gives a holomorphic limit throughout
each narrow chart. -/
private theorem introTraceApprox_sparse_moments_and_anchor :
    ∃ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ ∧
      (∀ a m Z : ℝ, 0 ≤ a → a < m → 0 ≤ Z → ∃ B : ℝ, 0 ≤ B ∧
        ∀ (n : ℕ) (z s : ℂ), m ≤ z.re → ‖z‖ ≤ Z → s.re ≤ a →
          ‖introTraceMellin approx(h, ρ, n, z) s‖ ≤ B / (1 + |s.im|)) ∧
      ∀ (χ : U𝔽) (a : ℝ), 0 ≤ a → a ≤ 1/2 →
        let C (n : ℕ) (z : ℂ) := archSum(χ, approx(h,ρ,n,z)) + introTraceSpectralSum χ approx(h,ρ,n,z) a
        ∃ K : ℂ → ℂ, AnalyticOnNhd ℂ K right(a) ∧
          TendstoLocallyUniformlyOn (fun n z ↦ C n z - C n 2) K atTop right(a) := by
  obtain ⟨h,ρ,hA,hmatch,hbound,hspec⟩ := introTraceApprox_exists_reference_and_sparse_moments (F := F)
  refine ⟨h,ρ,hA,hbound,?_⟩
  intro χ a ha hb C
  let K (z : ℂ) := archSum(χ, (fun t ↦ introTracePower z t - introTracePower 2 t)) +
    ∑' r : windowZeros(χ,a), (zeroOrder(χ,r.val) : ℂ) *
      (1/(z-(r.val-1/2)) - 1/(2-(r.val-1/2)))
  have hsub : right(a) ⊆ right(-(1/2:ℝ)) := fun z hz ↦ by
    change -(1/2:ℝ) < z.re; linarith [show a < z.re from hz]
  have hmap : MapsTo (fun _ : ℂ ↦ (2:ℂ)) right(a) right(a) := by
    intro z _; change a < (2:ℂ).re; norm_num; linarith
  have harch := (introTraceApprox_archimedean_reference_matched_sum χ h ρ hA 2 (by norm_num) hmatch).mono hsub
  have hsp := hspec χ a ha (fun _ ↦ 2) hmap (differentiableOn_const (2:ℂ))
  have hdiff : TendstoLocallyUniformlyOn (fun n z ↦ C n z-C n 2) K atTop right(a) := by
    apply (harch.add hsp).congr
    intro n z _; dsimp only [C,Pi.add_apply]; ring
  have harchA := Finset.analyticOnNhd_fun_sum Finset.univ (fun v _ ↦
    (introTraceApprox_archimedean_reference_matched χ v h ρ hA 2 (by norm_num) hmatch).1.mono hsub)
  have hspA := (introTrace_spectral_referenceSub χ a _ hmap (differentiableOn_const (2:ℂ))).2.2.2
  exact ⟨K,harchA.add hspA,hdiff⟩

open Classical in
/-- Paper: §§1.4.3–1.4.5, pp. 29–30. If the omitted zeros have summable
multiplicity-weighted reciprocal heights, a single matched family gives an actual
holomorphic cutoff limit throughout the narrow chart. Across the entire Euler
half-plane the discrepancy is the absolutely convergent omitted resolvent. -/
theorem introTrace_combined_limit_of_summable_exterior_heights :
    ∃ h ρ : ℕ → ℝ → ℝ, IsIntroTraceApproximation h ρ ∧
      ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽), RightInverse τ (ideleClassNorm F) → ∀ χ : U𝔽,
      (∀ t, χ (τ t) = 1) → ∀ a : ℝ, 0 ≤ a → a ≤ 1/2 →
      let E := {r : windowZeros(χ,1/2) // ¬ |r.val.re - 1/2| < a}
      Summable (fun r : E ↦ (zeroOrder(χ,r.val.val) : ℝ)/(1+|r.val.val.im|)) →
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧
        TendstoLocallyUniformlyOn (fun n z ↦ archSum(χ, approx(h,ρ,n,z)) +
          introTraceSpectralSum χ approx(h,ρ,n,z) a) H atTop right(a) ∧
        ∀ z : ℂ, 1/2 < z.re →
          let L := logDeriv finiteL(χ) (z+1/2) + if χ = 1 then 1/(z+1/2) + 1/(z-1/2) else 0
          HasSum (fun r : E ↦ (zeroOrder(χ,r.val.val) : ℂ)/(z-(r.val.val-1/2))) (L-H z) ∧
          (0 < (L-H z).re ↔ Nonempty E) := by
  obtain ⟨h,ρ,hA,hbound,hanchor⟩ := introTraceApprox_sparse_moments_and_anchor (F := F)
  refine ⟨h,ρ,hA,?_⟩
  intro τ hτ χ hχ a ha hb E hsum
  let v (r : E) := r.val.val-1/2
  let d (r : E) := zeroOrder(χ,r.val.val)
  let L (z : ℂ) := logDeriv finiteL(χ) (z+1/2) + if χ = 1 then 1/(z+1/2) + 1/(z-1/2) else 0
  let U (z : ℂ) := ∑' r : E, (d r : ℂ)/(z-v r)
  let C (n : ℕ) (z : ℂ) := archSum(χ, approx(h,ρ,n,z)) + introTraceSpectralSum χ approx(h,ρ,n,z) a
  have hv (r : E) : (v r).re ≤ 1/2 := by
    simpa only [v,Complex.sub_re,Complex.div_ofNat_re,Complex.one_re] using (abs_lt.mp r.val.property.2).2.le
  have hweight : Summable (fun r ↦ (d r : ℝ)/(1+|(v r).im|)) := by
    simpa only [d,v,Complex.sub_im,Complex.div_ofNat_im,Complex.one_im,zero_div,sub_zero] using hsum
  obtain ⟨hu,htail⟩ := introTraceApprox_sparse_moments_limit h ρ hA hbound v d hv
    (fun r ↦ r.val.property.1.le) hweight
  have hexact (z : ℂ) (hz : 1/2 < z.re) : Tendsto (fun n ↦ C n z) atTop (𝓝 (L z-U z)) := by
    apply (((introTrace_full_window_combined_euler_limit τ hτ χ hχ (a := 1/2) le_rfl h ρ hA).tendsto_at (a := z) hz).sub
      (htail.tendsto_at (a := z) hz)).congr
    intro n
    dsimp only [C,v,d]
    rw [← introTraceApprox_cutoff_omitted_sum χ a hb h ρ hA n z]
    ring
  obtain ⟨K,hK,hdiff⟩ := hanchor χ a ha hb
  let c := L 2-U 2
  let H (z : ℂ) := K z + c
  have hC : TendstoLocallyUniformlyOn C H atTop right(a) := by
    have hc := (hexact 2 (by norm_num)).tendstoUniformlyOn_const (s := right(a))
    apply (hdiff.add hc.tendstoLocallyUniformlyOn).congr
    intro n z _
    exact sub_add_cancel (C n z) (C n 2)
  refine ⟨H,hK.add analyticOnNhd_const,hC,?_⟩
  intro z hz
  have hp := tendsto_nhds_unique (hC.tendsto_at (a := z) (hb.trans_lt hz)) (hexact z hz)
  have hU : L z-H z = U z := by rw [hp]; ring
  change HasSum (fun r : E ↦ (d r : ℂ)/(z-v r)) (L z-H z) ∧ (0 < (L z-H z).re ↔ Nonempty E)
  rw [hU]
  refine ⟨(hu z hz).hasSum,?_⟩
  constructor
  · intro hh
    by_contra he
    let _ : IsEmpty E := not_nonempty_iff.mp he
    simp [U] at hh
  · rintro ⟨r₀⟩
    rw [show (U z).re = _ from Complex.re_tsum (hu z hz)]
    have hpos (r : E) : 0 < (((d r : ℂ)/(z-v r)).re) := by
      have hden : 0 < (z-v r).re := by rw [Complex.sub_re]; linarith [hv r]
      have hne : z-v r ≠ 0 := fun e ↦ hden.ne' (congrArg Complex.re e)
      have hd : 0 < (d r : ℝ) := by exact_mod_cast r.val.property.1
      simp only [Complex.div_re,Complex.intCast_re,Complex.intCast_im,zero_mul,zero_div,add_zero]
      exact div_pos (mul_pos hd hden) (Complex.normSq_pos.mpr hne)
    exact (Complex.hasSum_re (hu z hz).hasSum).summable.tsum_pos (fun r ↦ (hpos r).le) r₀ (hpos r₀)

open Classical in
/-- Paper: §§1.4.3–1.4.5, pp. 29–30. If the retained zeros have summable
multiplicity-weighted reciprocal heights, the real parts of the combined cutoffs
for a matched family tend uniformly to positive infinity on each compact subset
of the narrow chart. -/
theorem introTrace_combined_escape_of_summable_retained_heights :
    ∃ h ρ : ℕ → ℝ → ℝ, IsIntroTraceApproximation h ρ ∧
      ∀ (χ : U𝔽) (a : ℝ), 0 ≤ a → a ≤ 1/2 →
        Summable (fun r : windowZeros(χ,a) ↦ (zeroOrder(χ,r.val) : ℝ)/(1+|r.val.im|)) →
        ∀ K ⊆ right(a), IsCompact K → ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K,
          M ≤ (archSum(χ, approx(h,ρ,n,z)) + introTraceSpectralSum χ approx(h,ρ,n,z) a).re := by
  obtain ⟨h,ρ,hA,hbound,hanchor⟩ := introTraceApprox_sparse_moments_and_anchor (F := F)
  refine ⟨h,ρ,hA,?_⟩
  intro χ a ha hb hsum K hKsub hK M
  let v (r : windowZeros(χ,a)) := r.val-1/2
  let d (r : windowZeros(χ,a)) := zeroOrder(χ,r.val)
  let C (n : ℕ) (z : ℂ) := archSum(χ, approx(h,ρ,n,z)) + introTraceSpectralSum χ approx(h,ρ,n,z) a
  have hv (r : windowZeros(χ,a)) : (v r).re ≤ 1/2 := by
    suffices (v r).re ≤ a from this.trans hb
    simpa only [v,Complex.sub_re,Complex.div_ofNat_re,Complex.one_re] using (abs_lt.mp r.property.2).2.le
  have hweight : Summable (fun r ↦ (d r : ℝ)/(1+|(v r).im|)) := by
    simpa only [d,v,Complex.sub_im,Complex.div_ofNat_im,Complex.one_im,zero_div,sub_zero] using hsum
  have hs := (introTraceApprox_sparse_moments_limit h ρ hA hbound v d hv
    (fun r ↦ r.property.1.le) hweight).2.tendsto_at (a := (2:ℂ)) (by norm_num)
  let c := (∑' r, (d r : ℂ)/(2-v r)).re
  have hlim := (Complex.continuous_re.tendsto _).comp hs
  have hC2 : Tendsto (fun n ↦ (C n 2).re) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [tendsto_atTop.mp (introTraceApprox_archimedean_tendsto_atTop χ h ρ hA) (B-c+1),
      hlim.eventually (lt_mem_nhds (sub_one_lt c))] with n hn hr
    change c-1 < (introTraceSpectralSum χ approx(h,ρ,n,(2:ℂ)) a).re at hr
    dsimp only [C,Complex.add_re]
    linarith
  obtain ⟨K₀,han,hdiff⟩ := hanchor χ a ha hb
  obtain ⟨B,hB⟩ := (hK.image_of_continuousOn (han.continuousOn.mono hKsub)).isBounded.exists_norm_le
  have hun := (tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_Ioi.preimage Complex.continuous_re)).mp hdiff K hKsub hK
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hun 1 zero_lt_one, tendsto_atTop.mp hC2 (M+B+1)] with n hn hnc
  intro z hz
  have hk := (Complex.abs_re_le_norm (K₀ z)).trans (hB _ ⟨z,hz,rfl⟩)
  have he := hn z hz
  rw [dist_eq_norm] at he
  have herr := Complex.abs_re_le_norm (K₀ z - (C n z-C n 2))
  simp only [Complex.sub_re] at herr
  change M ≤ (C n z).re
  linarith [(abs_le.mp hk).1,le_abs_self ((K₀ z).re-((C n z).re-(C n 2).re))]

/-- Paper: §1.4.5, p. 30. The completed functional equation reflects the
zero-free region for the inverse character to the left of one half for the
original character. -/
theorem introTrace_completedL_no_left_zeros (χ : U𝔽)
    (_h : ∀ s : ℂ, 1 / 2 < s.re → meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) s ≤ 0)
    (s : ℂ) (_hs : s.re < 1 / 2) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s ≤ 0 := by
  obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation χ
    (continuedCompletedHeckeL χ) (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
  let r (z : ℂ) := 1 - z
  have hr : HasDerivAt r (-1) s := by simpa [r] using (hasDerivAt_id s).const_sub 1
  have e : continuedCompletedHeckeL χ⁻¹ ∘ r = fun z ↦ ε z * continuedCompletedHeckeL χ z :=
    funext he
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
    (show AnalyticAt ℂ r s by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
  rw [e] at ho
  change meromorphicOrderAt (ε * continuedCompletedHeckeL χ) s = _ at ho
  rw [meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt s) (hne s)] at ho
  exact ho.trans_le (_h (r s) (by change 1 / 2 < 1 - s.re; linarith))

end Limits

section NormOneTests

open scoped Distributions

/-- Paper: §1.4.6, p. 30. Every continuous functional on compact log-radial tests
which vanishes on tests supported away from zero is a finite linear combination of
derivatives at zero. Applied to a difference, this describes the undetermined terms
in extending an identity from the punctured line. -/
theorem introTrace_radial_defect_eq_finite_jet (T : StrongDual ℂ 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ))
    (hT : ∀ u : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ), (u : ℝ → ℂ) =ᶠ[𝓝 0] 0 → T u = 0) :
    ∃ (N : ℕ) (c : Fin (N + 1) → ℂ), ∀ u : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ),
      T u = ∑ j : Fin (N + 1), c j * iteratedDeriv j.val (u : ℝ → ℂ) 0 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let v : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ) := ⟨fun y ↦ ((b y : ℝ) : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left Complex.ofReal_zero, by simp⟩
  have hb : (v : ℝ → ℂ) =ᶠ[𝓝 0] 1 := by
    filter_upwards [b.eventuallyEq_one] with x hx
    change ((b x : ℝ) : ℂ) = 1
    exact_mod_cast (show (b x : ℝ) = 1 from hx)
  let B := schwartzToTestFunctionMulCLM v
  let L := T.comp B
  have hL : TemperedSupportedAtOrigin L := by
    intro x hx
    apply (Distribution.mem_dsupport_iff _).mp hx _ _ isClosed_singleton
    intro g hg
    apply hT (B g)
    have h0 : 0 ∉ tsupport (g : ℝ → ℂ) := fun h ↦ (hg h) (mem_singleton _)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp h0] with t ht
    change g t = 0 at ht
    change B g t = 0
    rw [show B g t = v t * g t from schwartzToTestFunctionMulCLM_apply _ _ _, ht, mul_zero]
  obtain ⟨N, c, hrepr⟩ := realTemperedDistribution_eq_sum_diracDerivative L hL
  refine ⟨N, fun j ↦ c j * (-1 : ℂ) ^ j.val, fun u ↦ ?_⟩
  have hdiff : T (u - B (testFunctionToSchwartzCLM u)) = 0 := by
    apply hT
    filter_upwards [hb] with t ht
    change u t - B (testFunctionToSchwartzCLM u) t = 0
    rw [show B (testFunctionToSchwartzCLM u) t = v t * u t from
      schwartzToTestFunctionMulCLM_apply _ _ _, ht, Pi.one_apply, one_mul, sub_self]
  rw [map_sub] at hdiff
  rw [sub_eq_zero.mp hdiff]
  change L (testFunctionToSchwartzCLM u) = _
  rw [hrepr, sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  let f := testFunctionToSchwartzCLM u
  have hd (k : ℕ) : ⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f) = iteratedDeriv k (u : ℝ → ℂ) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', iteratedDeriv_succ]
      change deriv (⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f)) = _
      rw [ih]
  change c j * ((-1 : ℂ) ^ j.val * ((SchwartzMap.derivCLM ℂ ℂ ^ j.val) f) 0) = _
  rw [congrFun (hd j.val) 0, mul_assoc]

/-- Paper: §1.4.6, p. 30. A compact log-radial test lies in the closure of the tests
vanishing near zero if and only if every derivative at zero vanishes. -/
theorem introTrace_radial_away_closure_iff_flat (u : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ)) :
    u ∈ closure {v : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ) | (v : ℝ → ℂ) =ᶠ[𝓝 0] 0} ↔
      ∀ k : ℕ, iteratedDeriv k (u : ℝ → ℂ) 0 = 0 := by
  have : ContinuousSMul ℂ 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ) := (testFunction_complex_polynormable (E := ℝ)).1
  let M : Submodule ℂ 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ) := {
    carrier := {v | (v : ℝ → ℂ) =ᶠ[𝓝 0] 0}
    zero_mem' := Filter.EventuallyEq.rfl
    add_mem' := fun hf hg ↦ (hf.add hg).trans (by simp)
    smul_mem' := fun c f hf ↦ (hf.const_smul c).trans (by simp) }
  change u ∈ M.topologicalClosure ↔ _
  have he (v : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ)) : testFunctionToSchwartzCLM v ∈ realSchwartzFlatAtOrigin ↔
      ∀ k : ℕ, iteratedDeriv k (v : ℝ → ℂ) 0 = 0 :=
    mem_realSchwartzFlatAtOrigin_iff _
  constructor
  · intro h
    apply (he u).1
    let J := realSchwartzFlatAtOrigin.comap testFunctionToSchwartzCLM.toLinearMap
    have hsub : M ≤ J := by
      intro v hv
      apply (he v).2
      intro k
      have e : (v : ℝ → ℂ) =ᶠ[𝓝 0] 0 := hv
      simpa using e.iteratedDeriv_eq k
    exact M.topologicalClosure_minimal hsub
      (realSchwartzFlatAtOrigin_isClosed.preimage testFunctionToSchwartzCLM.continuous) h
  · intro hu
    by_contra h
    let S := M.topologicalClosure
    obtain ⟨L, r, hr, hu'⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      (S.restrictScalars ℝ).convex M.isClosed_topologicalClosure h
    have hr0 : 0 < r := by simpa using hr 0 S.zero_mem
    have hL : ∀ v ∈ S, L v = 0 := by
      intro v hv
      by_contra hn
      let c : ℂ := ((r + 1 : ℝ) : ℂ) / L v
      have hc : c * L v = ((r + 1 : ℝ) : ℂ) := div_mul_cancel₀ _ hn
      have hh := hr (c • v) (S.smul_mem c hv)
      rw [map_smul, smul_eq_mul, hc] at hh
      change r + 1 < r at hh
      linarith
    obtain ⟨N, c, hc⟩ := introTrace_radial_defect_eq_finite_jet L
      (fun v hv ↦ hL v (M.le_topologicalClosure hv))
    have hv : L u = 0 := by simp [hc u, hu]
    rw [hv] at hu'
    exact (not_lt_of_ge hr0.le) hu'

private theorem introTrace_radial_section_jet (b : Multiplicative ℝ →ₜ* C𝔽) (k : ℕ) :
    ∃ J : D𝔽 →L[ℂ] ℂ, ∀ φ : D𝔽,
      J φ = iteratedDeriv k (fun t : ℝ ↦ φ.val (b (Multiplicative.ofAdd t))) 0 := by
  let m := continuousIdeleClassNorm F
  have hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hms : Surjective m := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  let I₀ : D𝔽 →L[ℂ] ModulatedExponentialDecay m {0} :=
    ⟨bruhatCompactSupportToModulatedExponentialDecay m {0} hm hms,
      bruhatCompactSupport_continuous_modulatedExponentialDecay m {0} hm hms
        ordConnected_singleton (singleton_nonempty _)⟩
  obtain ⟨e, he⟩ := modulatedExponentialDecay_singleton_schwartz m hm hms 0
  let I := e.toContinuousLinearMap.comp I₀
  have hI (φ : D𝔽) : (I φ : C𝔽 → ℂ) = φ.val :=
    (he (I₀ φ)).trans (modulationWeight_zero m _)
  let E : SchwartzBruhat C𝔽 →L[ℂ] ℂ :=
    { toFun f := f 1, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl,
      cont := continuous_schwartzBruhat_eval 1 }
  obtain ⟨A, hA⟩ := bruhatFirstOrder_schwartz b
  have h (n : ℕ) (f : SchwartzBruhat C𝔽) (x : ℝ) :
      ((A ^ n) f) (b (Multiplicative.ofAdd x)) =
        iteratedDeriv n (fun t : ℝ ↦ f (b (Multiplicative.ofAdd t))) x := by
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', iteratedDeriv_succ]
      change A ((A ^ n) f) (b (Multiplicative.ofAdd x)) = _
      rw [hA]
      change deriv (fun t : ℝ ↦ ((A ^ n) f)
        (b (Multiplicative.ofAdd x) * b (Multiplicative.ofAdd t))) 0 = _
      have he (t : ℝ) : ((A ^ n) f) (b (Multiplicative.ofAdd x) * b (Multiplicative.ofAdd t)) =
          iteratedDeriv n (fun t : ℝ ↦ f (b (Multiplicative.ofAdd t))) (x + t) := by
        rw [← map_mul]
        exact ih (x + t)
      simp only [he, deriv_comp_const_add, add_zero]
  refine ⟨E.comp ((A ^ k).comp I), fun φ ↦ ?_⟩
  change ((A ^ k) (I φ)) (1 : C𝔽) = _
  simpa [hI] using h k (I φ) 0

/-- Paper: §1.4.6, p. 30. For every positive order there is a compact idèle-class test
equal to that power of the log norm near norm one and outside the closure of tests
supported away from norm one. Even orders give inversion-invariant witnesses. -/
theorem introTrace_norm_one_jet_obstruction (k : ℕ) (hk : 0 < k) :
    ∃ φ : D𝔽,
      (∀ x, φ.val x⁻¹ = (-1 : ℂ) ^ k * φ.val x) ∧
      (∀ x, |Real.log (N(x))| ≤ 1 →
        φ.val x = (Real.log (N(x)) : ℂ) ^ k) ∧
      (∀ x, ideleClassNorm F x = 1 → φ.val x = 0) ∧
      φ ∉ closure {v : D𝔽 |
        ∃ U ∈ 𝓝 (1 : ℝ≥0ˣ), ∀ x, ideleClassNorm F x ∈ U → v.val x = 0} := by
  let a : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let g (t : ℝ) : ℂ := (t : ℂ) ^ k * (a t : ℝ)
  obtain ⟨φ, hφ⟩ := exists_normTest (F := F) g
    ((Complex.ofRealCLM.contDiff.pow k).mul (Complex.ofRealCLM.contDiff.comp a.contDiff))
    ((a.hasCompactSupport.comp_left Complex.ofReal_zero).mul_left)
  have hg (t : ℝ) (ht : |t| ≤ 1) : g t = (t : ℂ) ^ k := by
    have h1 := a.one_of_mem_closedBall (show t ∈ Metric.closedBall 0 a.rIn by
      simpa [Metric.mem_closedBall, Real.dist_eq, a] using ht)
    simp [g, h1]
  refine ⟨φ, ?_, fun x hx ↦ (hφ x).trans (hg _ hx), ?_, ?_⟩
  · intro x
    rw [hφ, hφ, map_inv]
    simp only [Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, g, a.neg, Complex.ofReal_neg]
    ring
  · intro x hx
    rw [hφ, hx]
    simp [g, hk.ne']
  · let m := ideleClassNorm F
    let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
    let τ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
      ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
    have hτ : RightInverse τ m := canonicalIdeleNormSection_rightInverse F
    let b := τ.comp (positiveRealLogEquiv.symm : Multiplicative ℝ →ₜ* ℝ≥0ˣ)
    have hb (t : ℝ) : m (b (Multiplicative.ofAdd t)) =
        positiveRealLogEquiv.symm (Multiplicative.ofAdd t) := hτ _
    have hlog (t : ℝ) : Real.log ((m (b (Multiplicative.ofAdd t))).val : ℝ) = t := by
      rw [hb, ← positiveRealLogEquiv_apply, positiveRealLogEquiv.apply_symm_apply]
      rfl
    obtain ⟨J, hJ⟩ := introTrace_radial_section_jet b k
    have hz : {v : D𝔽 |
        ∃ U ∈ 𝓝 (1 : ℝ≥0ˣ), ∀ x, m x ∈ U → v.val x = 0} ⊆ J ⁻¹' {0} := by
      rintro v ⟨U, hU, hv⟩
      change J v = 0
      rw [hJ]
      have hc : Tendsto (fun t : ℝ ↦ positiveRealLogEquiv.symm (Multiplicative.ofAdd t))
          (𝓝 0) (𝓝 1) := by
        have hcont : Continuous (fun t : ℝ ↦ positiveRealLogEquiv.symm (Multiplicative.ofAdd t)) :=
          positiveRealLogEquiv.symm.continuous.comp continuous_id
        simpa only [ofAdd_zero, map_one] using hcont.tendsto 0
      have hv' : (fun t : ℝ ↦ v.val (b (Multiplicative.ofAdd t))) =ᶠ[𝓝 0] 0 := by
        filter_upwards [hc hU] with t ht using hv _ ((hb t).symm ▸ ht)
      simpa using hv'.iteratedDeriv_eq k
    intro hmem
    have hj0 : J φ = 0 := closure_minimal hz (isClosed_singleton.preimage J.continuous) hmem
    have he : (fun t : ℝ ↦ φ.val (b (Multiplicative.ofAdd t))) =ᶠ[𝓝 0]
        (fun t : ℝ ↦ (t : ℂ) ^ k) := by
      filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
        (show (0 : ℝ) < 1 by norm_num)] with t ht
      rw [hφ, show Real.log ((ideleClassNorm F (b (Multiplicative.ofAdd t))).val : ℝ) = t from hlog t]
      exact hg t (abs_le.mpr ht)
    have hd (j : ℕ) : iteratedDeriv j (fun t : ℝ ↦ (t : ℂ) ^ k) =
        fun t : ℝ ↦ ((iteratedDeriv j (fun y : ℝ ↦ y ^ k) t : ℝ) : ℂ) := by
      induction j with
      | zero => funext t; simp
      | succ j ih =>
        rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
        funext t
        have h := (contDiff_id.pow k : ContDiff ℝ (j + 1 : ℕ) (fun y : ℝ ↦ y ^ k))
        exact ((h.differentiable_iteratedDeriv' j t).hasDerivAt.ofReal_comp).deriv
    rw [hJ, he.iteratedDeriv_eq k, hd] at hj0
    change ((iteratedDeriv k (fun y : ℝ ↦ y ^ k) 0 : ℝ) : ℂ) = 0 at hj0
    rw [iteratedDeriv_fun_pow_zero] at hj0
    exact (Nat.factorial_ne_zero k) (by simpa using hj0)

/-- Paper: §1.4.6, p. 30. In the uniform norm on a fixed compact support, tests
vanishing near norm one approximate precisely those vanishing on the norm-one classes. -/
theorem introTrace_norm_one_iff_uniform_approximation (φ : D𝔽) :
    (∀ x, ideleClassNorm F x = 1 → φ.val x = 0) ↔
      ∀ ε : ℝ, 0 < ε → ∃ v : D𝔽, tsupport v.val ⊆ tsupport φ.val ∧
        (∃ U ∈ 𝓝 (1 : ℝ≥0ˣ), ∀ x, ideleClassNorm F x ∈ U → v.val x = 0) ∧
        ∀ x, ‖φ.val x - v.val x‖ < ε := by
  constructor
  · intro hφ ε hε
    let m := continuousIdeleClassNorm F
    let L (x : C𝔽) : ℝ := (positiveRealLogEquiv (m x)).toAdd
    have hL : Continuous L := continuous_toAdd.comp (positiveRealLogEquiv.continuous.comp m.continuous)
    have hL0 (x : C𝔽) : L x = 0 ↔ m x = 1 := by
      change positiveRealLogEquiv (m x) = 1 ↔ _
      simp
    let K := tsupport φ.val ∩ {x | ε ≤ ‖φ.val x‖}
    have hc : Continuous φ.val :=
      continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 φ.property.1)
    have hK : IsCompact K := φ.property.2.inter_right (isClosed_le continuous_const hc.norm)
    have hz : 0 ∉ L '' K := by
      rintro ⟨x, hx, hx0⟩
      have he := hφ x ((hL0 x).1 hx0)
      have hn : ε ≤ ‖φ.val x‖ := hx.2
      simp [he, hε.not_ge] at hn
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      ((hK.image hL).isClosed.isOpen_compl.mem_nhds hz)
    let a : ContDiffBump (0 : ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
    obtain ⟨b, hb⟩ := exists_normTest (F := F) (fun t : ℝ ↦ (a t : ℂ))
      (Complex.ofRealCLM.contDiff.comp a.contDiff) (a.hasCompactSupport.comp_left Complex.ofReal_zero)
    have hb' (x : C𝔽) : b.val x = (a (L x) : ℂ) := by
      have hx : L x = Real.log (N(x)) := positiveRealLogEquiv_apply (m x)
      rw [hb, hx]
    let p : D𝔽 := ⟨φ.val * b.val, (mem_bruhatSmoothSubmodule_iff _).mpr
      (fun j ↦ isBruhatContDiff_mul ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 j)
        ((mem_bruhatSmoothSubmodule_iff _).mp b.property.1 j)), φ.property.2.mul_right⟩
    refine ⟨φ - p, ?_, ?_, ?_⟩
    · apply closure_mono
      intro x hx he
      apply hx
      change φ.val x - φ.val x * b.val x = 0
      simp [he]
    · let U := (fun u : ℝ≥0ˣ ↦ (positiveRealLogEquiv u).toAdd) ⁻¹' Metric.ball 0 (r/2)
      have hU : U ∈ 𝓝 (1 : ℝ≥0ˣ) := by
        have h := (continuous_toAdd.comp positiveRealLogEquiv.continuous).tendsto (1 : ℝ≥0ˣ)
        exact h (by simpa using Metric.ball_mem_nhds (0 : ℝ) (half_pos hr))
      refine ⟨U, hU, fun x hx ↦ ?_⟩
      have hx' : L x ∈ Metric.ball 0 a.rIn := hx
      change φ.val x - φ.val x * b.val x = 0
      rw [hb', a.one_of_mem_closedBall (Metric.ball_subset_closedBall hx')]
      simp
    · intro x
      change ‖φ.val x - (φ.val x - φ.val x * b.val x)‖ < ε
      rw [sub_sub_cancel, hb', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg a.nonneg]
      by_cases hx : L x ∈ Metric.ball (0 : ℝ) r
      · have hsmall : ‖φ.val x‖ < ε := by
          by_contra! hbad
          have hxφ : φ.val x ≠ 0 := fun he ↦ (not_le_of_gt hε) (by simpa [he] using hbad)
          exact hball hx ⟨x, ⟨subset_tsupport _ hxφ, hbad⟩, rfl⟩
        exact (mul_le_of_le_one_right (norm_nonneg _) a.le_one).trans_lt hsmall
      · have ha : a (L x) = 0 := by
          apply notMem_support.mp
          rwa [a.support_eq]
        simpa [ha] using hε
  · intro h x hx
    by_contra hn
    obtain ⟨v, _, ⟨U, hU, hv⟩, he⟩ := h _ (norm_pos_iff.mpr hn)
    have hvx := hv x (hx ▸ mem_of_mem_nhds hU)
    simpa [hvx] using he x

end NormOneTests

-- TODO(paper-gap): In §1.4.6, p. 30, continuity in the Bruhat test topology alone
-- cannot extend the identity from tests supported away from norm one. In the radial
-- log coordinate, first-derivative evaluation at zero annihilates every such test
-- but takes value one on x times a bump equal to one near zero. A bound in a weaker
-- topology, or control of the distributions supported at norm one, is needed.
-- Under GRH the full zero set of idelicExplicitFormula lies in every centered
-- open window of positive width, for all compactly supported Bruhat tests.
-- Section 1.4.2 fixes the profile as t^(-z) with midpoint value at t = 1.
-- For a convolution square the value at the identity is the squared L² norm.

section Boundary

section NormOneGeometric

open Classical

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b

private theorem introTrace_finite_norm_gap (v : V) (u : (v.adicCompletion F)ˣ) :
    ‖u.val‖ = 1 ∨ 1 / 2 ≤ |‖u.val‖ - 1| := by
  let q := (v.asIdeal.absNorm : ℝ)
  let k := WithZero.log (Valued.v u.val)
  have hq : (2 : ℝ) ≤ q := by
    change (2 : ℝ) ≤ (v.asIdeal.absNorm : ℝ)
    exact_mod_cast (show 2 ≤ v.asIdeal.absNorm from HeightOneSpectrum.one_lt_absNorm v)
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hN : ‖u.val‖ = q ^ k := norm_adicCompletion_eq_zpow F v u.ne_zero
  rcases lt_trichotomy k 0 with hk | hk | hk
  · right
    have hh := zpow_le_zpow_right₀ hq1 (show k ≤ -1 by omega)
    rw [zpow_neg_one] at hh
    have h' : q⁻¹ ≤ 1 / 2 := by simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hq
    rw [hN, abs_of_nonpos (by linarith : q ^ k - 1 ≤ 0)]
    linarith
  · left
    simp [hN, hk]
  · right
    have hh := zpow_le_zpow_right₀ hq1 (show (1 : ℤ) ≤ k by omega)
    rw [zpow_one] at hh
    rw [hN, abs_of_nonneg (by linarith : 0 ≤ q ^ k - 1)]
    linarith

/-- Paper: §1.4.6, p. 30. The shrinking norm-one residual vanishes identically on
the image of every finite completion. This gives exact equality of the finite-place
Connes–Weil terms at every cutoff. -/
theorem introTrace_cutoff_finite_restriction (φ : D𝔽)
    (hφ : ∀ g : (ideleClassNorm F).ker, φ.val g = 0)
    (b : ℝ → ℂ) (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1) (n : ℕ)
    (v : V) (u : (v.adicCompletion F)ˣ) :
    φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) * b (((n : ℝ) + 4) * (N(IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) - 1)) = 0 := by
  have hN : N(IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = ‖u.val‖ := by rw [ideleClassNorm_ofAdicCompletion]; rfl
  rcases introTrace_finite_norm_gap v u with hu | hu
  · have hm : ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = 1 := by
      apply Units.ext
      apply NNReal.eq
      exact hN.trans hu
    rw [hφ ⟨_, hm⟩, zero_mul]
  · apply mul_eq_zero_of_right
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hh := abs_lt.mpr (hs h)
    rw [abs_mul, hN, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 4)] at hh
    have hn : 0 ≤ (n : ℝ) * |‖u.val‖ - 1| := by positivity
    linarith [show ((n : ℝ) + 4) * |‖u.val‖ - 1| = (n : ℝ) * |‖u.val‖ - 1| + 4 * |‖u.val‖ - 1| by ring]

private theorem introTrace_cutoff_pointwise (b : ℝ → ℂ) (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {r : ℝ} (hr : r ≠ 1) : ∀ᶠ n : ℕ in atTop, b (((n : ℝ) + 4) * (r - 1)) = 0 := by
  obtain ⟨k : ℕ, hk⟩ := exists_nat_ge (1 / |r - 1|)
  filter_upwards [eventually_ge_atTop k] with n hn
  have hp := abs_pos.mpr (sub_ne_zero.mpr hr)
  have hk' : 1 ≤ (n : ℝ) * |r - 1| := (div_le_iff₀ hp).mp (hk.trans (by exact_mod_cast hn))
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have hm' := abs_lt.mpr (hs hm)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 4)] at hm'
  nlinarith

private theorem introTrace_cutoff_integral_norm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (R : X → ℝ) (hR : Measurable R) (K : X → ℂ) (hK : Integrable K μ)
    (hK1 : ∀ x, R x = 1 → K x = 0) (b : ℝ → ℂ) (hb : Measurable b)
    (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1) {Q : ℝ} (hQ : ∀ x, ‖b x‖ ≤ Q) :
    Tendsto (fun n : ℕ ↦ ∫ x, ‖K x * b (((n : ℝ) + 4) * (R x - 1))‖ ∂μ) atTop (𝓝 0) := by
  let s (n : ℕ) (x : X) := b (((n : ℝ) + 4) * (R x - 1))
  have hsm (n : ℕ) : Measurable (s n) := hb.comp (measurable_const.mul (hR.sub measurable_const))
  have hcon := tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖K x‖ * Q)
    (μ := μ) (l := atTop) (F := fun n x ↦ ‖K x * s n x‖) (f := fun _ ↦ (0 : ℝ))
    (.of_forall fun n ↦ (hK.aestronglyMeasurable.mul (hsm n).aestronglyMeasurable).norm)
    (.of_forall fun n ↦ .of_forall fun x ↦ by
      simp only [Real.norm_of_nonneg (norm_nonneg _), norm_mul]
      exact mul_le_mul_of_nonneg_left (hQ _) (norm_nonneg _))
    (hK.norm.mul_const Q) (.of_forall fun x ↦ ?_)
  · simpa only [s, integral_zero] using hcon
  · by_cases hx : R x = 1
    · simp [hK1 x hx]
    · apply tendsto_const_nhds.congr'
      filter_upwards [introTrace_cutoff_pointwise b hs hx] with n hn
      simp [s, hn]

private theorem introTrace_archimedean_test_kernel (w : InfinitePlace F)
    (f : BruhatCompactSupport w.Completionˣ) (hf : f.val 1 = 0) :
    let K := fun u : w.Completionˣ ↦ f.val u * (Real.sqrt (‖u.val‖ ^ w.mult) : ℂ) /
      ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)
    Integrable K (infiniteLocalMultiplicativeTamagawaMeasure F w) ∧
      infiniteConnesWeilPrincipalValue w f =
        (if w.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ))) *
          ∫ u, K u ∂infiniteLocalMultiplicativeTamagawaMeasure F w := by
  intro K
  by_cases hr : w.IsReal
  · simpa only [K, hr.mult_eq_one, pow_one, ite_eq_left hr] using
      And.intro (introTraceArchimedean_real_integrable w hr f hf)
        (realConnesWeilPrincipalValue_of_apply_one_zero w hr f hf)
  · simpa only [K, ite_eq_right hr] using
      introTrace_characterTrace_complex_place w (InfinitePlace.not_isReal_iff_isComplex.mp hr) f hf

/-- Paper: §1.4.6, p. 30. At every archimedean place the shrinking norm-one
residual tends to zero in the integral of the absolute value of the normalized
local kernel. The corresponding local Connes–Weil principal values converge. -/
theorem introTrace_cutoff_archimedean (φ : D𝔽) (hφ : ∀ g : (ideleClassNorm F).ker, φ.val g = 0)
    (b : ℝ → ℂ) (hb : Measurable b) (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {Q : ℝ} (hQ : ∀ x, ‖b x‖ ≤ Q) (v : ℕ → D𝔽)
    (hv : ∀ n g, (v n).val g = φ.val g * (1 - b (((n : ℝ) + 4) * (N(g) - 1))))
    (w : InfinitePlace F) :
    let R := (idelicExplicitFormula_infiniteTestMap (F := F) w).choose
    let μ := infiniteLocalMultiplicativeTamagawaMeasure F w
    let K := fun (f : D𝔽) (u : w.Completionˣ) ↦
      f.val (archClass(w) u) * (Real.sqrt (‖u.val‖ ^ w.mult) : ℂ) /
        ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)
    Tendsto (fun n ↦ ∫ u, ‖K φ u - K (v n) u‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ infiniteConnesWeilPrincipalValue w (R (v n))) atTop
        (𝓝 (infiniteConnesWeilPrincipalValue w (R φ))) := by
  intro R μ K
  let : MeasurableSpace w.Completion := instMeasurableSpaceCompletion_riemannMasullo F w
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let Nw := fun u : w.Completionˣ ↦ ‖u.val‖ ^ w.mult
  have hN (u : w.Completionˣ) : N(archClass(w) u) = Nw u := by
    rw [ideleClassNorm_ofCompletion]; rfl
  have hR (f : D𝔽) (u : w.Completionˣ) : (R f).val u = f.val (archClass(w) u) :=
    (idelicExplicitFormula_infiniteTestMap (F := F) w).choose_spec f u
  have hφ1 : φ.val 1 = 0 := hφ 1
  have hPV (f : D𝔽) (hf : f.val 1 = 0) : Integrable (K f) μ ∧
      infiniteConnesWeilPrincipalValue w (R f) =
        (if w.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ))) * ∫ u, K f u ∂μ := by
    simpa only [K, hR] using introTrace_archimedean_test_kernel w (R f) (by simp [hR, hf])
  have hK1 (u : w.Completionˣ) (hu : Nw u = 1) : K φ u = 0 := by
    have hmem : ideleClassNorm F (archClass(w) u) = 1 := by
      apply Units.ext
      apply NNReal.eq
      exact (hN u).trans hu
    simp only [K, hφ ⟨_, hmem⟩, zero_mul, zero_div]
  have hEq (n : ℕ) (u : w.Completionˣ) : K φ u - K (v n) u =
      K φ u * b (((n : ℝ) + 4) * (Nw u - 1)) := by
    simp only [K, hv, hN]
    ring
  have h := introTrace_cutoff_integral_norm μ Nw (by dsimp [Nw]; fun_prop) _ (hPV φ hφ1).1
    hK1 b hb hs hQ
  have habs : Tendsto (fun n ↦ ∫ u, ‖K φ u - K (v n) u‖ ∂μ) atTop (𝓝 0) := by
    simpa only [hEq] using h
  refine ⟨habs, ?_⟩
  have h0 : Tendsto (fun n ↦ ∫ u, K φ u - K (v n) u ∂μ) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun n ↦ norm_integral_le_integral_norm _) habs)
  have hV (n : ℕ) := hPV (v n) (by simp [hv, hφ1])
  have hV' := (tendsto_const_nhds (x := ∫ u, K φ u ∂μ)).sub h0
  simp only [integral_sub (hPV φ hφ1).1 (hV _).1, sub_sub_cancel, sub_zero] at hV'
  simpa only [(hPV φ hφ1).2, fun n ↦ (hV n).2] using
    hV'.const_mul (if w.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ)))

/-- Paper: §1.4.6, p. 30. The Mellin residual of the shrinking cutoff converges
absolutely at any fixed quasi-character. In particular this applies at both
polar characters in the geometric trace formula. -/
theorem introTrace_cutoff_mellin (φ : D𝔽) (hφ : ∀ g : (ideleClassNorm F).ker, φ.val g = 0)
    (b : ℝ → ℂ) (hb : Measurable b) (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {Q : ℝ} (hQ : ∀ x, ‖b x‖ ≤ Q) (c : C𝔽 → ℂ) (hc : Continuous c)
    (v : ℕ → D𝔽) (hv : ∀ n g, (v n).val g = φ.val g * (1 - b (((n : ℝ) + 4) * (N(g) - 1)))) :
    Tendsto (fun n ↦ ∫ g, ‖(φ.val g - (v n).val g) * c g‖ ∂ideleClassTamagawaMeasure F)
      atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ g, (v n).val g * c g ∂ideleClassTamagawaMeasure F) atTop
        (𝓝 (∫ g, φ.val g * c g ∂ideleClassTamagawaMeasure F)) := by
  let K (f : D𝔽) (g : C𝔽) := f.val g * c g
  have hI (f : D𝔽) : Integrable (K f) (ideleClassTamagawaMeasure F) :=
    ((schwartzBruhat_continuous (⟨f.val, bruhatCompactSupport_mem_schwartz f.property⟩ :
      SchwartzBruhat C𝔽)).mul hc).integrable_of_hasCompactSupport f.property.2.mul_right
  have hN : Measurable fun g : C𝔽 ↦ N(g) := (NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable
  have h1 (g : C𝔽) (hg : N(g) = 1) : K φ g = 0 := by
    have hm : ideleClassNorm F g = 1 := Units.ext (NNReal.eq hg)
    exact mul_eq_zero_of_left (hφ ⟨g, hm⟩) _
  have habs := introTrace_cutoff_integral_norm _ _ hN _ (hI φ) h1 b hb hs hQ
  have hEq (n : ℕ) (g : C𝔽) : (φ.val g - (v n).val g) * c g =
      K φ g * b (((n : ℝ) + 4) * (N(g) - 1)) := by rw [hv]; dsimp only [K]; ring
  refine ⟨by simpa only [hEq] using habs, ?_⟩
  have h0 : Tendsto (fun n ↦ ∫ g, K φ g - K (v n) g ∂ideleClassTamagawaMeasure F) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ norm_integral_le_integral_norm _)
    simpa only [K, ← sub_mul, hEq] using habs
  have h := (tendsto_const_nhds (x := ∫ g, K φ g ∂ideleClassTamagawaMeasure F)).sub h0
  simpa only [integral_sub (hI φ) (hI _), sub_sub_cancel, sub_zero] using h

/-- Paper: §1.4.6, p. 30, and Theorem 12.5.1.1, pp. 519–520. For a compact Bruhat
test vanishing on the norm-one subgroup, removing a shrinking neighborhood of that
subgroup preserves every finite-place term exactly. The two polar Mellin terms and
the normalized archimedean principal values converge to those of the original test,
so the entire geometric side converges. -/
theorem introTrace_norm_one_geometric_cutoff (φ : D𝔽) (hφ : ∀ g : (ideleClassNorm F).ker, φ.val g = 0)
    (b : ℝ → ℂ) (hb : Measurable b) (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {Q : ℝ} (hQ : ∀ x, ‖b x‖ ≤ Q) (v : ℕ → D𝔽)
    (hv : ∀ n g, (v n).val g = φ.val g * (1 - b (((n : ℝ) + 4) * (N(g) - 1)))) :
    let pole (f : D𝔽) (s : ℂ) := ∫ g, f.val g * ideleClassNormTwist 1 s g ∂ideleClassTamagawaMeasure F
    let arch (f : D𝔽) := ∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w
      ((idelicExplicitFormula_infiniteTestMap (F := F) w).choose f)
    let prime (f : D𝔽) (p : V) := ((Real.log (p.asIdeal.absNorm : ℝ) /
      ((finiteLocalMultiplicativeTamagawaMeasure F p) (p.adicCompletionIntegers F).units).toReal : ℝ) : ℂ) *
        finiteConnesWeilPrincipalValue p 1 ((idelicExplicitFormula_finiteTestMap (F := F) p).choose f)
    let geom (f : D𝔽) := pole f (1 / 2) + pole f (-1 / 2) -
      (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) * (arch f + ∑' p, prime f p)
    (∀ n p, prime (v n) p = prime φ p) ∧ Tendsto (geom ∘ v) atTop (𝓝 (geom φ)) := by
  intro pole arch prime geom
  have hP (n : ℕ) (p : V) : prime (v n) p = prime φ p := by
    let R := (idelicExplicitFormula_finiteTestMap (F := F) p).choose
    have he (f : D𝔽) (u : (p.adicCompletion F)ˣ) :
        (R f).val u = f.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F p u) :=
      (idelicExplicitFormula_finiteTestMap (F := F) p).choose_spec f u
    have hr : R (v n) = R φ := by
      apply Subtype.ext
      funext u
      rw [he, he, hv, mul_sub, mul_one, introTrace_cutoff_finite_restriction φ hφ b hs n p u, sub_zero]
    change _ * finiteConnesWeilPrincipalValue p 1 (R (v n)) =
      _ * finiteConnesWeilPrincipalValue p 1 (R φ)
    rw [hr]
  have hPole (s : ℂ) : Tendsto (fun n ↦ pole (v n) s) atTop (𝓝 (pole φ s)) :=
    (introTrace_cutoff_mellin φ hφ b hb hs hQ _ (ideleClassNormTwist (F := F) 1 s).continuous v hv).2
  have hA : Tendsto (fun n ↦ arch (v n)) atTop (𝓝 (arch φ)) := by
    apply tendsto_finsetSum
    intro w _
    exact (introTrace_cutoff_archimedean φ hφ b hb hs hQ v hv w).2
  refine ⟨hP, ?_⟩
  have hfin (n : ℕ) : (∑' p, prime (v n) p) = ∑' p, prime φ p := tsum_congr (hP n)
  change Tendsto (fun n ↦ geom (v n)) atTop (𝓝 (geom φ))
  simpa only [geom, hfin] using
    ((hPole (1 / 2)).add (hPole (-1 / 2))).sub ((hA.add_const (∑' p, prime φ p)).const_mul
      (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ))

end NormOneGeometric

local notation "outside(" χ ", " S ")" =>
  toMeromorphicNFOn (fun s ↦ reciprocalPartialHeckeEulerProduct χ S s * finiteL(χ) s) univ
local notation "outsideMass(" S ")" =>
  (∏ᶠ v : {v : V // v ∉ S},
    (((finiteLocalMultiplicativeTamagawaMeasure F v.val)
      (v.val.adicCompletionIntegers F).units).toReal : ℂ))

/-- Paper: §1.4.7, p. 30. Extension by the integer tests outside `S`
multiplies the local Mellin transform by the outside Euler product and
the product of the outside local integer-unit masses.
Section 1.1.4 (p. 12) defines the local character for χ unramified outside S.
Deviation: For the finite S in §1.4.7 retain the outside unit masses. If S contains
the different as on p. 25, their product is one. This is the meromorphic comparison in
`weilIdentity_unramifiedOutside_meromorphic`, with the normalized outside
Euler product of §6.3. The masses depend on the Haar convention. -/
theorem introTrace_transition_mellin (S : Finset V) (χ : U𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
    let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c
    (fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s))
      =ᶠ[codiscrete ℂ] (fun s ↦
        outsideMass(S) * sLocalIdelicZFunction f (twist s) * heckeEulerProductOutside S χ hχ s) :=
  by
  let L := finiteL(χ)
  obtain ⟨hL, hs⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hraw := weilIdentity_unramifiedOutside_meromorphic (F := F) S f χ hχ L hL
    (fun z hz ↦ hs ⟨z, hz⟩)
  have hm : MeromorphicOn (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z) univ :=
    fun z hz ↦ ((strongCoprimalityJetMatrix_det_ne_zero_euler χ S).1 z).meromorphicAt.mul
      (hL hz).meromorphicAt
  have he : (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z)
      =ᶠ[codiscrete ℂ] heckeEulerProductOutside S χ hχ := by
    rw [heckeEulerProductOutside_eq_finite S χ hχ L hL hs]
    simpa only [Filter.codiscrete] using toMeromorphicNFOn_eqOn_codiscrete hm
  filter_upwards [hraw, he] with z htrans heuler
  rw [htrans, ← heuler]
  simp only [reciprocalPartialHeckeEulerProduct, mul_assoc]

-- On theta classes this is the representative formula for sLocalThetaToGlobal_mk,
-- globalThetaMellin_mk and sLocalThetaMellin_mk from §§5.1–5.2.

/-- Paper: §1.4.7, pp. 30–31. The finite Hecke L-function has no zero on
the line of real part one.
Deviation: Meromorphic order allows the pole of a pure norm character on
this line. A normal-form point value at a pole would be zero in Lean. -/
theorem introTrace_finiteL_no_zeros_one_line (χ : U𝔽) (t : ℝ) :
    meromorphicOrderAt finiteL(χ) ⟨1, t⟩ ≤ 0 := by
  obtain ⟨A, hA, h⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B, hB, hzero⟩ := h F χ
  have hlog : 0 ≤ Real.log (B * (|t| + 3)) := Real.log_nonneg (by
    have hBt : 0 ≤ B * |t| := mul_nonneg (by linarith) (abs_nonneg t)
    nlinarith)
  apply hzero _ (finiteHeckeL_exists_continuation χ).choose_spec.1
    (finiteHeckeL_exists_continuation χ).choose_spec.2
  change 1 - A / ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|t| + 3))) ≤ 1
  exact sub_le_self _ (div_nonneg hA.le (mul_nonneg (by positivity) hlog))

/-- Paper: §1.4.7, pp. 30–31. The outside Euler product has no zero on the
line of real part one, so its reciprocal is holomorphic there.
Deviation: Multiplying by inverse local Euler factors creates no zeros
on this line. The reciprocal at a pole is interpreted in normal form. -/
theorem introTrace_outside_inv_analytic_one_line (χ : U𝔽) (S : Finset V) (t : ℝ) :
    AnalyticAt ℂ (fun s ↦ (outside(χ, S) s)⁻¹) ⟨1, t⟩ := by
  let L := finiteL(χ)
  let z : ℂ := ⟨1, t⟩
  obtain ⟨ha, hn⟩ := strongCoprimalityJetMatrix_det_ne_zero_euler χ S
  have hm : MeromorphicOn (fun w ↦ reciprocalPartialHeckeEulerProduct χ S w * L w) univ :=
    fun w hw ↦ (ha w).meromorphicAt.mul ((finiteHeckeL_exists_continuation χ).choose_spec.1 hw).meromorphicAt
  have hnf := meromorphicNFOn_toMeromorphicNFOn (fun w ↦ reciprocalPartialHeckeEulerProduct χ S w * L w) univ
  apply (hnf (mem_univ z)).inv.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_inv, meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ z)]
  change 0 ≤ -meromorphicOrderAt (reciprocalPartialHeckeEulerProduct χ S * L) z
  rw [meromorphicOrderAt_mul_of_ne_zero (ha z) (hn z (by norm_num [z]))]
  have hle : meromorphicOrderAt L z ≤ 0 := introTrace_finiteL_no_zeros_one_line χ t
  cases he : meromorphicOrderAt L z with
  | top => simp [he] at hle
  | coe k =>
    rw [he] at hle
    have hk : k ≤ 0 := by exact_mod_cast hle
    exact_mod_cast neg_nonneg.mpr hk

/-- Paper: §1.4.7, p. 31. Multiplication by the reciprocal of the outside
Euler product undoes the transition multiplier as a meromorphic identity.
Deviation: The reciprocal includes the measure normalization. Cancellation
holds on punctured neighborhoods, including at poles on the boundary. -/
theorem introTrace_transition_mellin_inv (S : Finset V) (χ : U𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (t : ℝ) :
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
    let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c
    (fun s ↦ (outsideMass(S) * heckeEulerProductOutside S χ hχ s)⁻¹ *
      globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s))
      =ᶠ[𝓝[≠] (⟨1, t⟩ : ℂ)] (fun s ↦ sLocalIdelicZFunction f (twist s)) := by
  let L := finiteL(χ)
  let E := reciprocalPartialHeckeEulerProduct χ S
  let z : ℂ := ⟨1, t⟩
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  obtain ⟨hE, hEn⟩ := strongCoprimalityJetMatrix_det_ne_zero_euler χ S
  have hm : MeromorphicOn (fun s ↦ E s * L s) univ :=
    fun s hs ↦ (hE s).meromorphicAt.mul ((hL.1 hs).meromorphicAt)
  have horder : meromorphicOrderAt (fun s ↦ E s * L s) z ≤ 0 := by
    change meromorphicOrderAt (E * L) z ≤ 0
    rw [meromorphicOrderAt_mul_of_ne_zero (hE z) (hEn z (by norm_num [z]))]
    exact introTrace_finiteL_no_zeros_one_line χ t
  have hnonzero : ∀ᶠ s in 𝓝[≠] z, E s * L s ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm z (mem_univ z))).mp
      (ne_top_of_le_ne_top (by simp) horder)
  have houtside : heckeEulerProductOutside S χ hχ =ᶠ[𝓝[≠] z] (fun s ↦ E s * L s) := by
    rw [heckeEulerProductOutside_eq_finite S χ hχ L hL.1 hL.2]
    exact hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)
  have hmass : outsideMass(S) ≠ 0 := by
    apply finprod_ne_zero
    intro v
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos_of_pos
      (pow_pos (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.val).pos) _)).ne')
  dsimp only
  filter_upwards [(introTrace_transition_mellin S χ hχ f).filter_mono (nhdsNE_le_codiscrete z),
    houtside, hnonzero] with s hEq hOut hNe
  have hProd := mul_ne_zero hmass (hOut.symm ▸ hNe)
  rw [hEq, mul_right_comm, inv_mul_cancel_left₀ hProd]

/-- Paper: §1.4.7, p. 31. The continued product recovers the local Mellin value
on the boundary after normalization at its removable singularities.
Deviation: At a pole of the outside factor the two separate normal-form point
values give zero when multiplied. The product is normalized as a whole. -/
theorem introTrace_transition_mellin_inv_boundaryValue (S : Finset V) (χ : U𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (t : ℝ) :
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
    let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c
    toMeromorphicNFOn (fun s ↦ (outsideMass(S) * heckeEulerProductOutside S χ hχ s)⁻¹ *
      globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s)) univ ⟨1, t⟩ =
        sLocalIdelicZFunction f (twist ⟨1, t⟩) := by
  let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
  let m := sIdeleQuotientNorm F S
  let hm := (isProperMap_sIdeleQuotientNorm F S).continuous
  let z : ℂ := ⟨1, t⟩
  let Z (s : ℂ) := sLocalIdelicZFunction f (quasiCharacterNormTwist m hm c s)
  let G (s : ℂ) := (outsideMass(S) * heckeEulerProductOutside S χ hχ s)⁻¹ *
    globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s)
  change toMeromorphicNFOn G univ z = Z z
  have hnorm (x : SIdeleQuotient F S) : ‖c x‖ = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    change ‖(χ (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) * _ ^ (0 : ℂ)‖ = 1
    simp
  let ψ : PontryaginDual (SIdeleQuotient F S) :=
    { toFun := fun x ↦ ⟨c x, mem_sphere_zero_iff_norm.mpr (hnorm x)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun x y ↦ Subtype.ext (map_mul c x y)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hbase : c = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ :=
    ContinuousMonoidHom.ext fun _ ↦ rfl
  have hZ : AnalyticAt ℂ Z z := by
    dsimp only [Z]
    rw [hbase]
    exact ((sLocalIdelicZetaIntegral_analyticOn f ψ).congr
      (isOpen_Ioi.preimage Complex.continuous_re)
      (fun s hs ↦ (sLocalIdelicZFunction_eq_integral f ⟨ψ, s, hs, rfl⟩).symm)) z
      (by norm_num [z])
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hOut : MeromorphicOn (heckeEulerProductOutside S χ hχ) univ := by
    rw [heckeEulerProductOutside_eq_finite S χ hχ _ hL.1 hL.2]
    exact (meromorphicNFOn_toMeromorphicNFOn _ _).meromorphicOn
  have hG : MeromorphicOn G univ := fun s hs ↦
    (analyticAt_const.meromorphicAt.mul (hOut s hs)).inv.mul
      ((globalIdelicZFunction_meromorphic (sAdeleSchwartzToGlobal F S f) χ) hs).meromorphicAt
  have hEq : G =ᶠ[𝓝[≠] z] Z := introTrace_transition_mellin_inv S χ hχ f t
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hG (mem_univ z)]
  exact (toMeromorphicNFAt_eventuallyEq_nhds_congr hEq).eq_of_nhds.trans
    (congrFun (toMeromorphicNFAt_eq_self.mpr hZ.meromorphicNFAt) z)

-- The first and third growth inputs on p. 31 are already stated as
-- finiteHeckeL_continuation_isBigO_rpow and finiteHeckeL_inv_isBigO_oneLine.

-- Helpers for `introTrace_finiteL_inv_horizontal_growth`. The continuation times a polynomial
-- clearing its poles is entire. Patel's disk factorization (External/Grh), rescaled by
-- `d = |a| + |b| + 1` about `3/2 + i(H + 1/2)`, bounds its zeros and the zero-free quotient,
-- and Patel's averaging of logarithmic losses picks a height in `(H, H + 1)`.

/-- The continuation has finitely many poles, all of order at most one.
Copied from the private helper of PR #6071 (AppB Sec6) with `S = ∅`. -/
private theorem introTrace_finiteL_inv_horizontal_growth_poles (χ : U𝔽) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : right(1), L s = finiteHeckeL χ s) :
    ∃ Z : Finset ℂ, (∀ s ∉ Z, AnalyticAt ℂ L s) ∧
      ∀ s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt L s := by
  classical
  obtain ⟨Λ, hΛ, hΛSeries⟩ := completedHeckeL_exists_continuation χ
  let R (s : ℂ) := (heckeGammaFactor χ s)⁻¹
  let H := Λ * R
  have hR := differentiable_inv_heckeGammaFactor χ
  have hH : MeromorphicOn H univ := fun s hs ↦
    (hΛ hs).meromorphicAt.mul (hR.analyticAt s).meromorphicAt
  have hAgree : ∀ s : right(1), (L - H) s = 0 := by
    intro s
    have hne := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property)
    change L s - Λ s * (heckeGammaFactor χ s)⁻¹ = 0
    rw [hSeries s, hΛSeries s, completedHeckeL, finiteHeckeL]
    rw [mul_comm (heckeGammaFactor χ s), mul_assoc, mul_inv_cancel₀ hne, mul_one, sub_self]
  have hAtTwo : meromorphicOrderAt (L - H) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun s hs ↦ hAgree ⟨s, hs⟩
  have hCompare (s : ℂ) : meromorphicOrderAt Λ s ≤ meromorphicOrderAt L s := by
    have ho := (hL.meromorphicOn.sub hH).meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) hAtTwo
    have he : L =ᶠ[𝓝[≠] s] H := (meromorphicOrderAt_eq_top_iff.mp ho).mono fun z hz ↦
      sub_eq_zero.mp hz
    rw [meromorphicOrderAt_congr he,
      meromorphicOrderAt_mul (hΛ (mem_univ s)).meromorphicAt (hR.analyticAt s).meromorphicAt]
    exact le_add_of_nonneg_right (hR.analyticAt s).meromorphicOrderAt_nonneg
  have hNeg : (-1 : WithTop ℤ) ≤ 0 := by decide
  have hPoles : ∃ Z : Finset ℂ,
      (∀ s ∉ Z, AnalyticAt ℂ Λ s) ∧ ∀ s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt Λ s := by
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t, ⟨_, hp, hq, ha⟩, _⟩ :=
        completedHeckeL_continuation_simplePoles χ Λ hΛ hΛSeries hχ
      refine ⟨{Complex.I * (t : ℂ), 1 + Complex.I * (t : ℂ)}, fun s hs ↦ ha s (by simpa using hs),
        fun s ↦ ?_⟩
      by_cases h : s = Complex.I * (t : ℂ)
      · rw [h, hp]
      by_cases h' : s = 1 + Complex.I * (t : ℂ)
      · rw [h', hq]
      exact hNeg.trans (ha s (by simp [h, h'])).meromorphicOrderAt_nonneg
    · have h := completedHeckeL_continuation_entire χ Λ hΛ hΛSeries hχ
      exact ⟨∅, fun s _ ↦ h.analyticAt s, fun s ↦
        hNeg.trans (h.analyticAt s).meromorphicOrderAt_nonneg⟩
  obtain ⟨Z, hAway, hLower⟩ := hPoles
  exact ⟨Z, fun s hs ↦ (hL (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((hAway s hs).meromorphicOrderAt_nonneg.trans (hCompare s)),
    fun s ↦ (hLower s).trans (hCompare s)⟩

/-- A polynomial clearing the finitely many poles makes the continuation entire.
Adapted from the private helper of PR #6071 (AppB Sec6) with `S = ∅`. -/
private theorem introTrace_finiteL_inv_horizontal_growth_entire (χ : U𝔽) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : right(1), L s = finiteHeckeL χ s) :
    ∃ (f : ℂ → ℂ) (Z : Finset ℂ), AnalyticOnNhd ℂ f univ ∧
      ∀ s ∉ Z, AnalyticAt ℂ L s ∧ f s = (∏ p ∈ Z, (s - p)) * L s := by
  classical
  obtain ⟨Z, hAway, hLower⟩ := introTrace_finiteL_inv_horizontal_growth_poles χ L hL hSeries
  let Q : ℂ → ℂ := fun s ↦ ∏ p ∈ Z, (s - p)
  let G : ℂ → ℂ := Q * L
  have hQ : Differentiable ℂ Q := by
    intro s; exact DifferentiableAt.fun_finsetProd fun p _ ↦ differentiableAt_id.sub_const p
  have hG : MeromorphicOn G univ := fun s _ ↦
    (hQ.analyticAt s).meromorphicAt.mul (hL (mem_univ s)).meromorphicAt
  have hGan (s : ℂ) (hs : s ∉ Z) : AnalyticAt ℂ G s := (hQ.analyticAt s).mul (hAway s hs)
  refine ⟨toMeromorphicNFOn G univ, Z, fun x _ ↦ ?_, fun s hs ↦ ⟨hAway s hs, ?_⟩⟩
  · apply ((meromorphicNFOn_toMeromorphicNFOn G univ)
      (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hG (mem_univ x)]
    by_cases hx : x ∈ Z
    · let Q' : ℂ → ℂ := fun s ↦ ∏ p ∈ Z.erase x, (s - p)
      have hQ' : Differentiable ℂ Q' := by
        intro s; exact DifferentiableAt.fun_finsetProd fun p _ ↦ differentiableAt_id.sub_const p
      have hGeq : G = (fun s ↦ s - x) * (Q' * L) := by
        funext s
        simp only [G, Q, Q', Pi.mul_apply, ← mul_assoc]
        rw [Finset.mul_prod_erase Z (fun p ↦ s - p) hx]
      rw [hGeq, meromorphicOrderAt_mul (by fun_prop) ((hQ'.analyticAt x).meromorphicAt.mul
          (hL (mem_univ x)).meromorphicAt),
        meromorphicOrderAt_id_sub_const,
        meromorphicOrderAt_mul (hQ'.analyticAt x).meromorphicAt (hL (mem_univ x)).meromorphicAt]
      have h1 := (hQ'.analyticAt x).meromorphicOrderAt_nonneg
      have h3 := hLower x
      have h4 : (0 : WithTop ℤ) ≤ 1 + meromorphicOrderAt L x := by
        have := add_le_add_right h3 (1 : WithTop ℤ)
        exact le_of_eq_of_le (by rfl) this
      calc (0 : WithTop ℤ) ≤ 1 + meromorphicOrderAt L x := h4
        _ ≤ 1 + (meromorphicOrderAt Q' x + meromorphicOrderAt L x) := by
          gcongr
          exact le_add_of_nonneg_left h1
    · exact (hGan x hx).meromorphicOrderAt_nonneg
  · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hG (mem_univ s),
      toMeromorphicNFAt_eq_self.mpr (hGan s hs).meromorphicNFAt]
    rfl

/-- Patel's disk factorization rescaled by `d ≥ 1`: some height in `(H, H + 1)` avoids the
ordinates of the zeros, and the logarithm of `‖f‖` is bounded below on that height in the
disk of radius `3 * d`. Adapted from the `_disk` helper of PR #6071. -/
private theorem introTrace_finiteL_inv_horizontal_growth_disk {f : ℂ → ℂ} {c : ℂ}
    {d M δ H : ℝ} (hf : AnalyticOnNhd ℂ f univ) (hd : 1 ≤ d) (hδ : 0 < δ) (hfc : δ ≤ ‖f c‖)
    (hM : 1 ≤ M)
    (hbd : ∀ z ∈ Metric.sphere c (6 * d), ‖f z‖ ≤ M) :
    ∃ t ∈ Ioo H (H + 1), ∀ z ∈ Metric.closedBall c (3 * d), z.im = t →
      f z ≠ 0 ∧ Real.log δ - 8 - ((8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ))) +
        (2 + Real.log d) / Real.log (6 / 5 : ℝ)) * Real.log (M / δ) ≤ Real.log ‖f z‖ := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  let f' : ℂ → ℂ := fun w ↦ f (c + d * w)
  have hf' : AnalyticOnNhd ℂ f' univ := fun w _ ↦
    (hf _ trivial).comp (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
  have hfc0 : 0 < ‖f c‖ := hδ.trans_le hfc
  have hf'0 : f' 0 = f c := by simp [f']
  have hbd' : ∀ z ∈ Metric.sphere (0 : ℂ) 6, ‖f' z‖ ≤ M := by
    intro z hz
    apply hbd
    rw [mem_sphere_zero_iff_norm] at hz
    rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_mul, hz, Complex.norm_real,
      Real.norm_of_nonneg hd0.le, mul_comm]
  obtain ⟨A, n, g, hfac, hN, hg⟩ := External.Grh.exists_goodHeight_disk_factorization hf'
    (by rw [hf'0]; exact norm_pos_iff.mp hfc0) hM hbd'
  rw [hf'0] at hN hg
  obtain ⟨t, ht, hne, hsum⟩ :=
    External.Grh.exists_goodHeight_sum_posLog A (fun ρ ↦ c.im + d * ρ.im) n H
  refine ⟨t, ht, fun z hz hzt ↦ ?_⟩
  set w : ℂ := (z - c) / d with hw
  have hzw : z = c + d * w := by rw [hw, mul_div_cancel₀ _ hdC]; ring
  have hwb : w ∈ Metric.closedBall (0 : ℂ) 3 := by
    rw [mem_closedBall_zero_iff, hw, norm_div, Complex.norm_real, Real.norm_of_nonneg hd0.le,
      div_le_iff₀ hd0]
    have := hz; rw [Metric.mem_closedBall, dist_eq_norm] at this; linarith
  have hwim : w.im = (t - c.im) / d := by
    rw [hw, Complex.div_ofReal_im, Complex.sub_im, hzt]
  have hρ (ρ : ℂ) (hρA : ρ ∈ A) : |t - (c.im + d * ρ.im)| ≤ d * ‖w - ρ‖ := by
    have h1 := Complex.abs_im_le_norm (w - ρ)
    rw [Complex.sub_im, hwim] at h1
    have : t - (c.im + d * ρ.im) = d * ((t - c.im) / d - ρ.im) := by field_simp; ring
    rw [this, abs_mul, abs_of_pos hd0]
    exact mul_le_mul_of_nonneg_left h1 hd0.le
  have hpos (ρ : ℂ) (hρA : ρ ∈ A) : 0 < |t - (c.im + d * ρ.im)| :=
    abs_pos.mpr (sub_ne_zero.mpr (hne ρ hρA))
  have hwρ (ρ : ℂ) (hρA : ρ ∈ A) : 0 < ‖w - ρ‖ := by
    have := (hpos ρ hρA).trans_le (hρ ρ hρA)
    exact pos_of_mul_pos_right this hd0.le
  obtain ⟨hgw, hgl⟩ := hg w hwb
  have hnorm : ‖f z‖ = (∏ ρ ∈ A, ‖w - ρ‖ ^ n ρ) * ‖g w‖ := by
    rw [hzw]
    change ‖f' w‖ = _
    rw [hfac w, norm_mul, norm_prod]
    simp only [norm_pow]
  have hprod : 0 < ∏ ρ ∈ A, ‖w - ρ‖ ^ n ρ := Finset.prod_pos fun ρ hρ ↦ pow_pos (hwρ ρ hρ) _
  have hgw0 : 0 < ‖g w‖ := norm_pos_iff.mpr hgw
  refine ⟨norm_pos_iff.mp (hnorm ▸ mul_pos hprod hgw0), ?_⟩
  rw [hnorm, Real.log_mul hprod.ne' hgw0.ne',
    Real.log_prod (fun ρ hρ ↦ (pow_pos (hwρ ρ hρ) _).ne')]
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd
  have hsum' : -∑ ρ ∈ A, (n ρ : ℝ) * (max 0 (-Real.log |t - (c.im + d * ρ.im)|) + Real.log d) ≤
      ∑ ρ ∈ A, Real.log (‖w - ρ‖ ^ n ρ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro ρ hρA
    rw [Real.log_pow, ← mul_neg]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h1 : Real.log |t - (c.im + d * ρ.im)| ≤ Real.log d + Real.log ‖w - ρ‖ := by
      rw [← Real.log_mul hd0.ne' (hwρ ρ hρA).ne']
      exact Real.log_le_log (hpos ρ hρA) (hρ ρ hρA)
    have h2 : -max 0 (-Real.log |t - (c.im + d * ρ.im)|) ≤ Real.log |t - (c.im + d * ρ.im)| := by
      rw [neg_le]; exact le_max_right _ _
    linarith
  have hsplit : ∑ ρ ∈ A, (n ρ : ℝ) * (max 0 (-Real.log |t - (c.im + d * ρ.im)|) + Real.log d) =
      ∑ ρ ∈ A, (n ρ : ℝ) * max 0 (-Real.log |t - (c.im + d * ρ.im)|) +
        (∑ ρ ∈ A, (n ρ : ℝ)) * Real.log d := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  set N : ℝ := ∑ ρ ∈ A, (n ρ : ℝ)
  have hratio : Real.log (M / ‖f c‖) ≤ Real.log (M / δ) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by linarith) hδ hfc)
  have hk1 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have hk2 : 0 ≤ 8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ)) := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)
    positivity
  have hN' : N ≤ Real.log (M / δ) / Real.log (6 / 5 : ℝ) :=
    hN.trans (div_le_div_of_nonneg_right hratio hk1.le)
  have hN2 : (2 + Real.log d) * N ≤
      (2 + Real.log d) / Real.log (6 / 5 : ℝ) * Real.log (M / δ) := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hN' (by linarith)
  have hlogfc : Real.log δ ≤ Real.log ‖f c‖ := Real.log_le_log hδ hfc
  have := mul_le_mul_of_nonneg_left hratio hk2
  nlinarith

/-- The final estimate: a lower bound for `log φ` linear in `log X` bounds `q / φ` by a
power of `1 + |t|` when `X` is comparable to `1 + |t|`. -/
private theorem introTrace_finiteL_inv_horizontal_growth_estimate {q φ X E t κ P A : ℝ}
    {n m : ℕ} (hX1 : 1 ≤ X) (hq : q ≤ X ^ n) (hφ : 0 < φ)
    (hlog : -A - Real.log X * (κ * P) ≤ Real.log φ) (hm : (n : ℝ) + κ * P ≤ m)
    (hXt : X ≤ 2 * E * (1 + |t|)) :
    q * φ⁻¹ ≤ Real.exp A * (2 * E) ^ m * (1 + |t|) ^ m := by
  have hX0 : 0 < X := by linarith
  have hfinv : φ⁻¹ ≤ Real.exp A * X ^ (κ * P) := by
    rw [Real.rpow_def_of_pos hX0, ← Real.exp_add, ← Real.exp_log hφ, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith
  calc q * φ⁻¹ ≤ X ^ n * (Real.exp A * X ^ (κ * P)) :=
        mul_le_mul hq hfinv (inv_nonneg.mpr hφ.le) (by positivity)
    _ = Real.exp A * X ^ ((n : ℝ) + κ * P) := by
      rw [Real.rpow_add hX0, Real.rpow_natCast]; ring
    _ ≤ Real.exp A * X ^ (m : ℝ) := by gcongr
    _ = Real.exp A * X ^ m := by rw [Real.rpow_natCast]
    _ ≤ Real.exp A * (2 * E * (1 + |t|)) ^ m := by gcongr
    _ = Real.exp A * (2 * E) ^ m * (1 + |t|) ^ m := by rw [mul_pow]; ring

/-- Every unit interval at large absolute height contains a height on which the
continuation is analytic, nonzero and has polynomially bounded reciprocal on `[a, b]`. -/
private theorem introTrace_finiteL_inv_horizontal_growth_heights (χ : U𝔽) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : right(1), L s = finiteHeckeL χ s) (a b : ℝ) :
    ∃ (C H₀ : ℝ) (m : ℕ), 0 < C ∧ ∀ H : ℝ, H₀ ≤ |H| → ∃ t ∈ Ioo H (H + 1), ∀ σ ∈ Icc a b,
      AnalyticAt ℂ L ⟨σ, t⟩ ∧ L ⟨σ, t⟩ ≠ 0 ∧ ‖(L ⟨σ, t⟩)⁻¹‖ ≤ C * (1 + |t|) ^ m := by
  classical
  obtain ⟨f, Z, hf, hfeq⟩ := introTrace_finiteL_inv_horizontal_growth_entire χ L hL hSeries
  set d : ℝ := |a| + |b| + 1 with hd
  have hd1 : 1 ≤ d := by have := abs_nonneg a; have := abs_nonneg b; linarith
  obtain ⟨M₀, hM₀, hO⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries
    (3 / 2 - 6 * d) (3 / 2 + 6 * d) (by linarith)
  obtain ⟨C₀, hC₀, hC₀'⟩ := Asymptotics.isBigO_iff'.mp hO
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hC₀'
  obtain ⟨T₁, hT₁⟩ := hC₀'
  have hLbd (z : ℂ) (hre : z.re ∈ Icc (3 / 2 - 6 * d) (3 / 2 + 6 * d)) (him : T₁ ≤ |z.im|) :
      ‖L z‖ ≤ C₀ * |z.im| ^ M₀ := by
    have h := hT₁ |z.im| him z rfl hre
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at h
  set R : ℝ := ∑ p ∈ Z, ‖p‖ with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hpR (p : ℂ) (hp : p ∈ Z) : ‖p‖ ≤ R :=
    Finset.single_le_sum (f := fun p ↦ ‖p‖) (fun _ _ ↦ norm_nonneg _) hp
  have hQlow (z : ℂ) (hz : R + 1 ≤ |z.im|) : z ∉ Z ∧ 1 ≤ ‖∏ p ∈ Z, (z - p)‖ := by
    have hzp (p : ℂ) (hp : p ∈ Z) : 1 ≤ ‖z - p‖ := by
      have h1 := Complex.abs_im_le_norm (z - p)
      have h2 := Complex.abs_im_le_norm p
      rw [Complex.sub_im] at h1
      have h3 := abs_sub_abs_le_abs_sub z.im p.im
      linarith [hpR p hp]
    refine ⟨fun hzZ ↦ ?_, ?_⟩
    · have := hzp z hzZ
      rw [sub_self, norm_zero] at this
      norm_num at this
    · rw [norm_prod]
      exact Finset.one_le_prod₀ fun p hp ↦ hzp p hp
  have hQup (z : ℂ) : ‖∏ p ∈ Z, (z - p)‖ ≤ (‖z‖ + R) ^ Z.card := by
    rw [norm_prod, ← Finset.prod_const]
    apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    intro p hp
    exact (norm_sub_le z p).trans (by linarith [hpR p hp])
  set n : ℕ := Z.card with hn
  set E : ℝ := 3 + 12 * d + R with hE
  have hE1 : 1 ≤ E := by linarith
  set ζ : ℝ := ‖dedekindZeta F (3 / 2 : ℝ)‖ with hζ
  have hLlow (z : ℂ) (hz : z.re = 3 / 2) : 1 ≤ ‖L z‖ * ζ := by
    have hs : z ∈ right(1) := show 1 < z.re by rw [hz]; norm_num
    rw [show L z = finiteHeckeL χ ⟨z, hs⟩ from hSeries ⟨z, hs⟩]
    exact (finiteHeckeL_zeroFreeRegion_euler F χ ⟨z, hs⟩ (y := 3 / 2) (by norm_num)
      (by rw [show ((⟨z, hs⟩ : right(1)) : ℂ) = z from rfl, hz])).2
  have hζ0 : 0 < ζ := by
    have h := hLlow ⟨3 / 2, 0⟩ rfl
    rcases (norm_nonneg (dedekindZeta F (3 / 2 : ℝ))).lt_or_eq with h' | h'
    · exact h'
    · rw [← hζ] at h'; rw [← h', mul_zero] at h; norm_num at h
  set δ : ℝ := 1 / ζ with hδ
  have hδ0 : 0 < δ := by positivity
  set C₁ : ℝ := max C₀ 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  set P : ℝ := (n : ℝ) + M₀ with hP
  have hP0 : 0 ≤ P := by positivity
  set κ : ℝ := (8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ))) +
    (2 + Real.log d) / Real.log (6 / 5 : ℝ) with hκ
  have hκ0 : 0 ≤ κ := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)
    have := Real.log_nonneg hd1
    have : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
    positivity
  set m : ℕ := ⌈(n : ℝ) + κ * P⌉₊ with hm
  refine ⟨Real.exp (8 - Real.log δ + κ * (Real.log C₁ - Real.log δ)) * (2 * E) ^ m,
    max (T₁ + 6 * d + 1) (R + 6 * d + 2), m, by positivity,
    fun H hH ↦ ?_⟩
  have hHT : T₁ + 6 * d + 1 ≤ |H| := (le_max_left _ _).trans hH
  have hHR : R + 6 * d + 2 ≤ |H| := (le_max_right _ _).trans hH
  set X : ℝ := E * (|H| + 1) with hX
  have hX1 : 1 ≤ X := by
    have : 1 ≤ |H| + 1 := by linarith [abs_nonneg H]
    nlinarith
  have hX0 : 0 < X := by linarith
  set c : ℂ := ⟨3 / 2, H + 1 / 2⟩ with hc
  set M : ℝ := C₁ * X ^ P with hM
  have hXP : 1 ≤ X ^ P := Real.one_le_rpow hX1 hP0
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le hC₁1 hXP
  -- norms on a neighbourhood of the centre
  have hnormz (z : ℂ) (hre : |z.re| ≤ 3 / 2 + 6 * d) (him : |z.im - (H + 1 / 2)| ≤ 6 * d) :
      ‖z‖ + R ≤ X ∧ |z.im| ≤ X ∧ |H| - 1 / 2 - 6 * d ≤ |z.im| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im z
    have h2 : |z.im| ≤ |H| + 1 / 2 + 6 * d := by
      have := abs_sub_abs_le_abs_sub z.im (H + 1 / 2)
      have := abs_add_le H (1 / 2)
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      linarith
    have h3 : |H| - 1 / 2 - 6 * d ≤ |z.im| := by
      have := abs_sub_abs_le_abs_sub (H + 1 / 2) z.im
      rw [abs_sub_comm] at this
      have := abs_sub_abs_le_abs_sub H (-(1 / 2))
      rw [sub_neg_eq_add, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      linarith
    have hEX : |H| + E ≤ X := by
      rw [hX]; nlinarith [abs_nonneg H]
    refine ⟨?_, ?_, h3⟩ <;> linarith
  have hsph : ∀ z ∈ Metric.sphere c (6 * d), ‖f z‖ ≤ M := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hre := Complex.abs_re_le_norm (z - c)
    have him := Complex.abs_im_le_norm (z - c)
    rw [hz, Complex.sub_re] at hre
    rw [hz, Complex.sub_im] at him
    have hcre : c.re = 3 / 2 := rfl
    have hcim : c.im = H + 1 / 2 := rfl
    rw [hcre] at hre
    rw [hcim] at him
    have hre' : |z.re| ≤ 3 / 2 + 6 * d := by
      have := abs_sub_abs_le_abs_sub z.re (3 / 2)
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at this
      linarith
    obtain ⟨hn1, hn2, hn3⟩ := hnormz z hre' him
    obtain ⟨hzZ, -⟩ := hQlow z (by linarith)
    obtain ⟨-, hfz⟩ := hfeq z hzZ
    rw [hfz, norm_mul]
    have hzre : z.re ∈ Icc (3 / 2 - 6 * d) (3 / 2 + 6 * d) := by
      constructor <;> linarith [(abs_le.mp hre).1, (abs_le.mp hre).2]
    have hLz := hLbd z hzre (by linarith)
    have hLz' : ‖L z‖ ≤ C₁ * X ^ M₀ :=
      hLz.trans (mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow (abs_nonneg _) hn2 hM₀.le) (by positivity) (by positivity))
    have hQz : ‖∏ p ∈ Z, (z - p)‖ ≤ X ^ n :=
      (hQup z).trans (pow_le_pow_left₀ (by positivity) hn1 n)
    calc ‖∏ p ∈ Z, (z - p)‖ * ‖L z‖ ≤ X ^ n * (C₁ * X ^ M₀) := by gcongr
      _ = M := by
        rw [hM, hP, Real.rpow_add hX0, Real.rpow_natCast]; ring
  have hfc : δ ≤ ‖f c‖ := by
    obtain ⟨hcZ, hQc⟩ := hQlow c (by
      have := hnormz c (by rw [show c.re = 3 / 2 from rfl, abs_of_pos (by norm_num)]; linarith)
        (by rw [show c.im = H + 1 / 2 from rfl, sub_self, abs_zero]; linarith)
      linarith [this.2.2])
    obtain ⟨-, hfz⟩ := hfeq c hcZ
    rw [hfz, norm_mul]
    have hLc : δ ≤ ‖L c‖ := by
      rw [hδ, div_le_iff₀ hζ0]; exact hLlow c rfl
    calc δ = 1 * δ := (one_mul δ).symm
      _ ≤ _ := by gcongr
  obtain ⟨t, ht, hgood⟩ :=
    introTrace_finiteL_inv_horizontal_growth_disk (H := H) hf hd1 hδ0 hfc hM1 hsph
  refine ⟨t, ht, fun σ hσ ↦ ?_⟩
  set z : ℂ := ⟨σ, t⟩ with hz
  have hzt : z.im = t := rfl
  have hzre : |z.re| ≤ |a| + |b| := by
    change |σ| ≤ _
    rcases abs_le.mp (le_refl |a|) with ⟨-, -⟩
    have h1 := neg_abs_le a
    have h2 := le_abs_self b
    rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2, abs_nonneg a, abs_nonneg b]
  have htH : |t - (H + 1 / 2)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hzball : z ∈ Metric.closedBall c (3 * d) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, show c.re = 3 / 2 from rfl, show c.im = H + 1 / 2 from rfl,
      hzt]
    have := abs_sub (z.re) (3 / 2)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at this
    linarith
  obtain ⟨hfz0, hlog⟩ := hgood z hzball hzt
  obtain ⟨hn1, hn2, hn3⟩ := hnormz z (by linarith) (by rw [hzt]; linarith)
  obtain ⟨hzZ, -⟩ := hQlow z (by linarith)
  obtain ⟨hLan, hfz⟩ := hfeq z hzZ
  have hQz0 : ∏ p ∈ Z, (z - p) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦
    sub_ne_zero.mpr fun h ↦ hzZ (h ▸ hp)
  have hLz0 : L z ≠ 0 := fun h ↦ hfz0 (by rw [hfz, h, mul_zero])
  refine ⟨hLan, hLz0, ?_⟩
  have hfpos : 0 < ‖f z‖ := norm_pos_iff.mpr hfz0
  have hinv : ‖(L z)⁻¹‖ = ‖∏ p ∈ Z, (z - p)‖ * ‖f z‖⁻¹ := by
    rw [hfz, norm_inv, norm_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hQz0),
      one_mul]
  have hQz : ‖∏ p ∈ Z, (z - p)‖ ≤ X ^ n :=
    (hQup z).trans (pow_le_pow_left₀ (by positivity) hn1 n)
  -- the lower bound in exponential form
  have hlogM : Real.log (M / δ) = Real.log C₁ - Real.log δ + P * Real.log X := by
    rw [Real.log_div (by positivity) hδ0.ne', hM, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hX0]
    ring
  have hlog' : -(8 - Real.log δ + κ * (Real.log C₁ - Real.log δ)) - Real.log X * (κ * P) ≤
      Real.log ‖f z‖ := by
    rw [hlogM] at hlog
    have e : κ * (Real.log C₁ - Real.log δ + P * Real.log X) =
        κ * (Real.log C₁ - Real.log δ) + Real.log X * (κ * P) := by ring
    linarith
  have hexp : (n : ℝ) + κ * P ≤ (m : ℝ) := Nat.le_ceil _
  have hXt : X ≤ 2 * E * (1 + |t|) := by
    have hHt : |H| ≤ |t| + 1 := by
      have := abs_sub_abs_le_abs_sub H t
      have : |H - t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
      linarith
    have hEt : 0 ≤ E * |t| := mul_nonneg (by linarith) (abs_nonneg t)
    calc X = E * (|H| + 1) := rfl
      _ ≤ E * (|t| + 2) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = 2 * E * (1 + |t|) - E * |t| := by ring
      _ ≤ 2 * E * (1 + |t|) := by linarith
  rw [hinv]
  exact introTrace_finiteL_inv_horizontal_growth_estimate hX1 hQz hfpos hlog'
    hexp hXt

/-- The statement of `introTrace_finiteL_inv_horizontal_growth` for any continuation. -/
private theorem introTrace_finiteL_inv_horizontal_growth_of_continuation (χ : U𝔽) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : right(1), L s = finiteHeckeL χ s) (a b : ℝ) :
    ∃ (T : ℤ → ℝ) (C : ℝ) (m : ℕ), 0 < C ∧ Tendsto T atTop atTop ∧ Tendsto T atBot atBot ∧
      ∀ k : ℤ, ∀ σ ∈ Icc a b,
        meromorphicOrderAt L ⟨σ, T k⟩ = 0 ∧ ‖(L ⟨σ, T k⟩)⁻¹‖ ≤ C * (1 + |T k|) ^ m := by
  obtain ⟨C, H₀, m, hC, hgood⟩ :=
    introTrace_finiteL_inv_horizontal_growth_heights χ L hL hSeries a b
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge H₀
  let φ : ℤ → ℤ := fun k ↦ if (K₀ : ℤ) ≤ |k| then k else K₀
  have hφ (k : ℤ) : H₀ ≤ |((φ k : ℤ) : ℝ)| := by
    dsimp only [φ]
    split_ifs with h
    · have h' : ((K₀ : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h
      rw [Int.cast_abs] at h'
      push_cast at h'
      linarith
    · push_cast
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact hK₀
  have hφeq (k : ℤ) (hk : (K₀ : ℤ) ≤ |k|) : φ k = k := ite_eq_left hk
  choose T hT hTgood using fun k ↦ hgood (φ k) (hφ k)
  refine ⟨T, C, m, hC, ?_, ?_, fun k σ hσ ↦ ?_⟩
  · refine tendsto_atTop_mono' atTop ?_ (tendsto_intCast_atTop_atTop (R := ℝ))
    filter_upwards [eventually_ge_atTop (K₀ : ℤ)] with k hk
    have h1 := (hT k).1
    rw [hφeq k (hk.trans (le_abs_self k))] at h1
    exact h1.le
  · refine tendsto_atBot_mono' atBot ?_
      (tendsto_atBot_add_const_right _ 1
        ((tendsto_intCast_atBot_iff (R := ℝ) (f := id)).mpr tendsto_id))
    filter_upwards [eventually_le_atBot (-(K₀ : ℤ))] with k hk
    have h1 := (hT k).2
    rw [hφeq k ((le_neg.mpr hk).trans (neg_le_abs k))] at h1
    exact h1.le
  · obtain ⟨han, hne, hbd⟩ := hTgood k σ hσ
    refine ⟨?_, hbd⟩
    rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr hne]
    rfl

/-- Paper: §1.4.7, p. 31. On both tails there are horizontal edges of
growing contour boxes on which the reciprocal finite L-function is regular,
nonzero, and polynomially bounded uniformly along the edge.
Deviation: The real parts range over the fixed width of the boxes in the
preceding sentence. The polynomial bounds concern large absolute heights. -/
theorem introTrace_finiteL_inv_horizontal_growth (χ : U𝔽) (a b : ℝ) (_hab : a < b) :
    ∃ (T : ℤ → ℝ) (C : ℝ) (m : ℕ), 0 < C ∧ Tendsto T atTop atTop ∧ Tendsto T atBot atBot ∧
      ∀ k : ℤ, ∀ σ ∈ Icc a b,
        meromorphicOrderAt finiteL(χ) ⟨σ, T k⟩ = 0 ∧
          ‖(finiteL(χ) ⟨σ, T k⟩)⁻¹‖ ≤ C * (1 + |T k|) ^ m := by
  exact introTrace_finiteL_inv_horizontal_growth_of_continuation χ _
    (finiteHeckeL_exists_continuation χ).choose_spec.1
    (finiteHeckeL_exists_continuation χ).choose_spec.2 a b

end Boundary

-- Section 1.4.8, p. 31. The full multiplicity in the open strip and the capped
-- edge multiplicity are spectralStripMultiplicity_interior and
-- spectralStripMultiplicity_boundary. The strict test for jet k is 2*k + 1 < s,
-- by lt_spectralBoundaryMultiplicity and scalarIntervalSobolev_eval_boundary_iff.
-- TODO(paper-gap): §§1.4.8–1.4.9, p. 31. Continuity of the surviving evaluations
-- does not compare the fixed geometric distribution across widths. The missing
-- orbital comparison is recorded by traceFormula_exteriorZeros in Chapter 12.

open Classical in
/-- Paper: §1.4.5, p. 30. Fix a norm section. The continuation asserted in all its
normalized charts and at every positive half-width is equivalent to the critical-line
assertion for the completed L-functions of all unitary characters of the number field. -/
theorem introTrace_all_continuations_iff_critical_line
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) :
    (∀ (χ : U𝔽), (∀ t, χ (τ t) = 1) → ∀ a : ℝ, 0 < a →
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧ EqOn H
        (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
          if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1)) ↔
      ∀ (χ : U𝔽) (s : ℂ), 0 < s.re → s.re < 1 →
        0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s → s.re = 1 / 2 := by
  constructor
  · intro hext
    have hr (χ : U𝔽) (s : ℂ) (hs : 1 / 2 < s.re) :
        meromorphicOrderAt (continuedCompletedHeckeL χ) s ≤ 0 := by
      apply introTrace_completedL_no_right_zeros τ hτ _ χ s hs
      intro η hη w hw
      let a := (w.re - 1 / 2) / 2
      have ha : 0 < a := by dsimp [a]; linarith
      have hw' : a + 1 / 2 < w.re := by dsimp [a]; linarith
      have h := (introTrace_continuation_iff_finiteL_orders η a ha.le).mp (hext η hη a ha) w hw'
      rw [h]
      split_ifs <;> decide
    intro χ s _ _ hz
    apply le_antisymm
    · exact le_of_not_gt fun h ↦ hz.not_ge (hr χ s h)
    · exact le_of_not_gt fun h ↦ hz.not_ge (introTrace_completedL_no_left_zeros χ (hr χ⁻¹) s h)
  · intro hline χ hχ a ha
    apply (introTrace_normalized_continuation_iff_no_right_zeros_in_strip τ hτ χ hχ a ha.le).mpr
    intro s hs hs₁ hz
    have he := hline χ s (by linarith) hs₁ hz
    linarith

open Classical in
/-- Paper: §1.4.5, p. 30 and Theorem 12.5.1.1, pp. 519–520. At a fixed
half-width the exterior-zero terms cancel for every test vanishing on the norm-one
classes exactly when every completed Hecke zero in the critical strip belongs to the
open centered window. This uses one norm section and tests every unitary character.
Normalizing the character translates its zeros by a purely imaginary number. -/
theorem introTrace_exterior_cancellation_iff_all_zeros_in_window
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (a : ℝ) :
    (∀ φ : D𝔽, (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
      HasSum (fun z : {p : {η : U𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1} × ℂ //
          0 < zeroOrder(p.1.val, p.2) ∧ a ≤ |p.2.re - 1 / 2|} ↦
        (zeroOrder(z.val.1.val, z.val.2) : ℂ) *
          ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2) g ∂ideleClassTamagawaMeasure F) 0) ↔
      ∀ (χ : U𝔽) (s : ℂ), 0 < s.re → s.re < 1 →
        0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s → |s.re - 1 / 2| < a := by
  have hdiv (χ : U𝔽) (s : ℂ) : 0 < zeroOrder(χ, s) ↔ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s := by
    have hL := (continuedCompletedHeckeL_spec χ).1.meromorphicOn
    have ht : meromorphicOrderAt (continuedCompletedHeckeL χ) 2 ≠ ⊤ := by
      intro h
      have hpos : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) 2 := by simp [h]
      have := introTrace_positive_order_re_lt_one χ hpos
      norm_num at this
    have hn := hL.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (x := 2)
      (mem_univ _) (mem_univ s) ht
    rw [MeromorphicOn.divisor_apply hL (mem_univ s)]
    cases e : meromorphicOrderAt (continuedCompletedHeckeL χ) s with
    | top => exact (hn e).elim
    | coe k => simp
  constructor
  · intro hcan χ s hs₀ _ hs
    have hempty := isEmpty_exteriorZeros_of_hasSum τ hτ a (fun φ hφ ↦ by
      simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ, Set.indicator_univ]
        using hcan φ hφ)
    obtain ⟨ψ, v, hv, hψ, htwist⟩ := introTraceApprox_spectral_normalized_character τ hτ χ
    have hre : (s + v).re = s.re := by rw [Complex.add_re, hv, add_zero]
    have horder := (introTraceApprox_spectral_finiteOrder_twist χ ψ v hv htwist s hs₀).trans
      (introTrace_normalized_finite_order_eq_completed ψ (s + v) (hre.symm ▸ hs₀))
    have hp := (hdiv ψ (s + v)).mpr (horder ▸ hs)
    by_contra! hout
    exact hempty.false ⟨(⟨ψ, hψ⟩, s + v), hp, by simpa only [hre] using hout⟩
  · intro hzeros φ hφ
    have hempty : IsEmpty {p : {η : U𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1} × ℂ //
        0 < zeroOrder(p.1.val, p.2) ∧ a ≤ |p.2.re - 1 / 2|} := by
      refine ⟨fun p ↦ ?_⟩
      obtain ⟨hleft, hright⟩ := abs_lt.mp
        (introTrace_positive_divisor_in_critical_strip p.val.1.val p.val.2 p.property.1)
      have h := hzeros p.val.1.val p.val.2 (by linarith) (by linarith)
        ((hdiv p.val.1.val p.val.2).mp p.property.1)
      exact (not_lt_of_ge p.property.2) h
    simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ, Set.indicator_univ] using
      (hasSum_exteriorZeros_iff_isEmpty τ hτ a).mpr hempty φ hφ

open Classical in
/-- Paper: §1.4.5, p. 30 and Theorem 12.5.1.1, pp. 519–520. Fix a number field
and one section of its idele class norm. If the positive half-widths in a set
come arbitrarily close to zero, cancellation for all tests at those widths
is equivalent to the critical-line assertion for every unitary Hecke character
of the field, including characters nontrivial on the section. -/
theorem introTrace_cofinal_exterior_cancellation_iff_critical_line
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (W : Set ℝ) (hW : ∀ a ∈ W, 0 < a) (hsmall : ∀ δ > 0, ∃ a ∈ W, a ≤ δ) :
    (∀ a ∈ W, ∀ φ : D𝔽, (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
      HasSum (fun z : {p : {η : U𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1} × ℂ //
          0 < zeroOrder(p.1.val, p.2) ∧ a ≤ |p.2.re - 1 / 2|} ↦
        (zeroOrder(z.val.1.val, z.val.2) : ℂ) *
          ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2) g ∂ideleClassTamagawaMeasure F) 0) ↔
      ∀ (χ : U𝔽) (s : ℂ), 0 < s.re → s.re < 1 →
        0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s → s.re = 1 / 2 := by
  constructor
  · intro hcan χ s hs₀ hs₁ hs
    by_contra hn
    obtain ⟨a, ha, hle⟩ := hsmall |s.re - 1 / 2| (abs_pos.mpr (sub_ne_zero.mpr hn))
    have h := (introTrace_exterior_cancellation_iff_all_zeros_in_window τ hτ a).mp
      (hcan a ha) χ s hs₀ hs₁ hs
    exact (not_lt_of_ge hle) h
  · intro hline a ha
    apply (introTrace_exterior_cancellation_iff_all_zeros_in_window τ hτ a).mpr
    intro χ s hs₀ hs₁ hs
    simpa only [hline χ s hs₀ hs₁ hs, sub_self, abs_zero] using hW a ha

/-- Paper: §1.4.5, p. 30. For every number field and every unitary character
of its idele class group, a zero of the continued completed Hecke L-function
in the open critical strip has real part one half. The paper gives no
numbered statement for this claim. Theorem 13.3.1.2 is a title. The deduction
uses the exterior-zero cancellation asserted in Theorem 12.5.1.1. That assertion, applied
at a cofinal set of positive half-widths, is the remaining unproved premise.
Deviation: Positive meromorphic order expresses a zero of the continuation
and distinguishes zeros from poles. -/
theorem heckeL_zero_re_eq_half (χ : U𝔽) (s : ℂ) (_hs₀ : 0 < s.re) (_hs₁ : s.re < 1)
    (_hzero : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s) :
    s.re = 1 / 2 := by
  classical
  let q : (AdeleRing (𝓞 F) F)ˣ →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  apply (introTrace_cofinal_exterior_cancellation_iff_critical_line τ hτ (Ioi 0)
    (fun _ ha ↦ ha) (fun δ hδ ↦ ⟨δ, hδ, le_rfl⟩)).mp _ χ s _hs₀ _hs₁ _hzero
  intro a ha φ hφ
  simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ, Set.indicator_univ] using
    traceFormula_exteriorZeros τ hτ φ hφ ha

end RiemannMasullo
