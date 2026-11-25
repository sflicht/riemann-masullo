module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a
public import RiemannMasullo.Ch02_AdelicTheta.Sec2b
public import RiemannMasullo.Ch03_IdelicZeta.Sec1
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.DedekindZeta

import RiemannMasullo.AppA_AlgebraicNT.Sec2
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Unique
import RiemannMasullo.ForMathlib.RingTheory.Trace.Defs
import all RiemannMasullo.Ch02_AdelicTheta.Sec1
import RiemannMasullo.ForMathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.VerticalStripRatio
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gaussian.Hecke
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.RingTheory.Complex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.HeckeLFunction
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Convergence

import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Global idelic zeta functions

Masullo, §3.2, pp. 122–128. This section uses the global adelic theta and Fourier
operators of §2.2 and the Tamagawa measures of §A.3.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "𝒳[" F "]" => HeckeCharacter (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[F])
local notation "classNormℝ" => fun (g : C[F]) ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
local notation "halfPlane" => Complex.re ⁻¹' Set.Ioi (1 : ℝ)

set_option quotPrecheck false in
local notation "finiteConductorLevels(" F ", " χ ", " v ")" =>
  setOf (fun j : ℕ ↦ ∀ u : (HeightOneSpectrum.adicCompletion F v)ˣ, ‖Units.val u‖ = 1 →
    ‖Units.val u - 1‖ ≤ (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ) ^ (-(j : ℤ)) →
      χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = 1)
local notation "finiteConductorLog(" F ", " n ")" =>
  (Real.log (Int.natAbs (NumberField.discr F)) + finsum (fun v : HeightOneSpectrum (𝓞 F) ↦
    Real.log (Ideal.absNorm (HeightOneSpectrum.asIdeal v)) * (n v : ℝ)) : ℝ)

section Hecke

/-- Paper: §3.2.1, p. 122. Raising the positive idele class norm to a fixed
complex power gives a continuous multiplicative function. -/
theorem ideleClassNorm_cpow_properties (s : ℂ) :
    (classNormℝ (1 : C[F]) : ℂ) ^ s = 1 ∧
    (∀ g h : C[F], (classNormℝ (g * h) : ℂ) ^ s =
      (classNormℝ g : ℂ) ^ s * (classNormℝ h : ℂ) ^ s) ∧
    Continuous (fun g : C[F] ↦ (classNormℝ g : ℂ) ^ s) := by
  have hcont : Continuous (ideleClassNorm F) :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (ideleGroup_topology F).2.2.2.2.1
  refine ⟨by simp, ?_, ?_⟩
  · intro g h
    dsimp only
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) s
  · have hr : Continuous classNormℝ := NNReal.continuous_coe.comp (Units.continuous_val.comp hcont)
    apply (Complex.continuous_ofReal.comp hr).cpow continuous_const
    intro g
    exact Complex.ofReal_mem_slitPlane.mpr (NNReal.coe_pos.mpr (Units.zero_lt _))

/-- Paper: §3.2.1, p. 122. The coordinate at a unitary character `χ`
sends `s` to the quasi-character `χ |·|^s`. -/
def ideleClassNormTwist (χ : U[F]) (s : ℂ) : 𝒳[F] :=
  let unitary : 𝒳[F] :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  let power : 𝒳[F] :=
    ⟨{ toFun := fun g ↦ (classNormℝ g : ℂ) ^ s
       map_one' := (ideleClassNorm_cpow_properties (F := F) s).1
       map_mul' := (ideleClassNorm_cpow_properties (F := F) s).2.1 },
     (ideleClassNorm_cpow_properties (F := F) s).2.2⟩
  unitary * power

/-- Paper: §3.2.1, p. 122. At exponent one the twist of the trivial character
takes the value of the idele class norm. -/
theorem ideleClassNormTwist_one_one (g : C[F]) :
    ideleClassNormTwist (1 : U[F]) 1 g = (classNormℝ g : ℂ) := by
  change (1 : ℂ) * (classNormℝ g : ℂ) ^ (1 : ℂ) = _
  rw [one_mul, Complex.cpow_one]

local notation "χ₀(" χ ")" => ideleClassNormTwist χ 0

/-- Paper: Equation (3.2.1.2), p. 123. At an unramified finite prime the Euler
factor is the reciprocal of `1 - χ(πᵥ) (N v)^(-s)`. A ramified place contributes one. -/
def finiteHeckeEulerFactor (χ : U[F]) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  open Classical in
  if χ₀(χ).IsUnramifiedAt v then
    (1 - χ₀(χ).localValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹
  else 1

/-- Paper: Equation (3.2.1.1), p. 122. At an unramified finite place and in the
half-plane of absolute convergence, the reciprocal Euler factor can be evaluated
on any uniformizer using the twisted quasi-character. -/
theorem finiteHeckeEulerFactor_inv_uniformizer (χ : U[F])
    (v : HeightOneSpectrum (𝓞 F)) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F)) (hχ : χ₀(χ).IsUnramifiedAt v)
    {s : ℂ} (hs : s ∈ halfPlane) :
    (finiteHeckeEulerFactor χ v s)⁻¹ =
      1 - finitePlaceRestriction F v (ideleClassNormTwist χ s) π := by
  classical
  rw [finiteHeckeEulerFactor, ite_eq_left hχ, inv_inv, hχ.localValue_eq _ hπ,
    HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
  change 1 - ((χ g : ℂ) * (classNormℝ g : ℂ) ^ (0 : ℂ)) * _ =
    1 - (χ g : ℂ) * (classNormℝ g : ℂ) ^ s
  have hn : classNormℝ g = (v.asIdeal.absNorm : ℝ)⁻¹ := by
    change ((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π) : ℝ≥0) : ℝ) = _
    rw [ideleClassNorm_ofAdicCompletion]
    exact norm_uniformizer_adicCompletion v _ hπ
  rw [Complex.cpow_zero, mul_one, hn, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg
    (Nat.cast_nonneg _) s, Complex.cpow_neg, Complex.ofReal_natCast]

/-- Paper: Equation (3.2.1.4), p. 123. A real local unitary character has a
unique imaginary radial exponent and a unique sign parity. -/
theorem realHeckeCharacter_parameters (χ : U[F]) (v : InfinitePlace F) (hv : v.IsReal) :
    ∃! a : ℂ × Fin 2, a.1.re = 0 ∧ ∀ x : ℝˣ,
      infinitePlaceRestriction F v χ₀(χ)
          (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom x) =
        (‖(x : ℝ)‖ : ℂ) ^ a.1 * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ a.2.val := by
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
  let i : ℝˣ →ₜ* v.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.units_map _⟩
  let c := (infinitePlaceRestriction F v χ₀(χ)).comp i
  apply existsUnique_realUnits_character_parameters c
  intro x
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v (i x)
  change ‖(χ g : ℂ) * (classNormℝ g : ℂ) ^ (0 : ℂ)‖ = 1
  simp

/-- Paper: Equation (3.2.1.5), p. 123. A complex local unitary character has a
unique imaginary radial exponent and integer angular weight.
Deviation: We take the radius in the paper to be the normalized absolute value `‖x‖²`. -/
theorem complexHeckeCharacter_parameters (χ : U[F]) (v : InfinitePlace F)
    (hv : v.IsComplex) :
    ∃! a : ℂ × ℤ, a.1.re = 0 ∧ ∀ x : ℂˣ,
      infinitePlaceRestriction F v χ₀(χ)
          (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toMonoidHom x) =
        ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ a.1 * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ a.2 := by
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
  let i : ℂˣ →ₜ* v.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous.units_map _⟩
  let c := (infinitePlaceRestriction F v χ₀(χ)).comp i
  apply existsUnique_complexUnits_character_parameters c
  intro x
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v (i x)
  change ‖(χ g : ℂ) * (classNormℝ g : ℂ) ^ (0 : ℂ)‖ = 1
  simp

/-- Paper: Equations (3.2.1.3)–(3.2.1.5), p. 123. The global gamma factor
multiplies the real and complex local gamma factors, using the local radial
exponent after twisting and the real sign parity or complex angular weight.
Deviation: The local argument explicitly includes any imaginary radial exponent of the fixed
unitary character. Mathlib's complex gamma factor includes a factor of two, which is divided out. -/
def heckeGammaFactor (χ : U[F]) (s : ℂ) : ℂ :=
  open Classical in
  ∏ v : InfinitePlace F, if hv : v.IsReal then
    let a := (realHeckeCharacter_parameters χ v hv).exists.choose
    Complex.Gammaℝ (s + a.1 + (a.2.val : ℂ))
  else
    let a := (complexHeckeCharacter_parameters χ v
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
    Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2

/-- Paper: Equations (3.2.1.3)–(3.2.1.5), p. 123. The trivial character contributes
one unshifted real or complex gamma factor at each infinite place. -/
theorem heckeGammaFactor_one (s : ℂ) :
    heckeGammaFactor (1 : U[F]) s =
      Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces F *
        (Complex.Gammaℂ s / 2) ^ InfinitePlace.nrComplexPlaces F := by
  classical
  have hR (v : InfinitePlace F) (hv : v.IsReal) :
      (realHeckeCharacter_parameters (1 : U[F]) v hv).exists.choose = (0, 0) := by
    apply (realHeckeCharacter_parameters (1 : U[F]) v hv).unique
      (realHeckeCharacter_parameters (1 : U[F]) v hv).exists.choose_spec
    refine ⟨rfl, fun x ↦ ?_⟩
    change (1 : ℂ) * _ ^ (0 : ℂ) = (‖(x : ℝ)‖ : ℂ) ^ (0 : ℂ) * _ ^ (0 : ℕ)
    simp
  have hC (v : InfinitePlace F) (hv : v.IsComplex) :
      (complexHeckeCharacter_parameters (1 : U[F]) v hv).exists.choose = (0, 0) := by
    apply (complexHeckeCharacter_parameters (1 : U[F]) v hv).unique
      (complexHeckeCharacter_parameters (1 : U[F]) v hv).exists.choose_spec
    refine ⟨rfl, fun x ↦ ?_⟩
    change (1 : ℂ) * _ ^ (0 : ℂ) = ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (0 : ℂ) * _ ^ (0 : ℤ)
    simp
  unfold heckeGammaFactor
  simp_rw [hR, hC]
  simp only [Fin.val_zero, Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, dite_eq_ite]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, ← Fintype.card_subtype, InfinitePlace.not_isReal_iff_isComplex]

/-- The value of a unitary Hecke character on a local uniformizer has norm one. -/
theorem norm_ideleClassNormTwist_zero_localValue (χ : U[F]) (v : HeightOneSpectrum (𝓞 F)) :
    ‖χ₀(χ).localValue v‖ = 1 := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let π := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose
  let u := Units.mk0 (π : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  change ‖χ₀(χ).restrict v (u : v.adicCompletion F)‖ = 1
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  change ‖(χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℂ) * _ ^ (0 : ℂ)‖ = 1
  simp

private theorem norm_finiteHeckeEulerFactor_sub_one_le (χ : U[F])
    (v : HeightOneSpectrum (𝓞 F)) {r : ℝ} (hr : 1 < r) {s : ℂ} (hs : r ≤ s.re) :
    ‖finiteHeckeEulerFactor χ v s - 1‖ ≤ 2 * (v.asIdeal.absNorm : ℝ) ^ (-r) := by
  classical
  let q : ℝ := v.asIdeal.absNorm
  have hq : 2 ≤ q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.two_le_absNorm_nnreal v
  have hq' : 1 ≤ q := by linarith
  have hqpos : 0 < q := by linarith
  rw [finiteHeckeEulerFactor]
  split_ifs with hχ
  · let z := χ₀(χ).localValue v * (q : ℂ) ^ (-s)
    change ‖(1 - z)⁻¹ - 1‖ ≤ 2 * q ^ (-r)
    have hz : ‖z‖ = q ^ (-s.re) := by
      simp [z, norm_ideleClassNormTwist_zero_localValue,
        Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    have hcomp : ‖z‖ ≤ q ^ (-r) :=
      hz.le.trans (Real.rpow_le_rpow_of_exponent_le hq' (by linarith))
    have hhalf : q ^ (-r) ≤ 1 / 2 := calc
      q ^ (-r) ≤ q ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq' (by linarith)
      _ = 1 / q := by rw [Real.rpow_neg hqpos.le, Real.rpow_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq
    have hd : 1 / 2 ≤ ‖1 - z‖ := by
      have ht := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one] at ht
      linarith
    have hn : 1 - z ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    rw [show (1 - z)⁻¹ - 1 = z / (1 - z) by field_simp; ring, norm_div]
    apply (div_le_iff₀ (by linarith : 0 < ‖1 - z‖)).mpr
    calc
      ‖z‖ ≤ q ^ (-r) := hcomp
      _ = (2 * q ^ (-r)) * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
  · simp only [sub_self, norm_zero]
    positivity

/-- Paper: Lemma 3.2.1.1, p. 123. On each compact subset of `Re(s) > 1`,
the deviations of the Euler factors from one are absolutely and uniformly summable. -/
theorem finiteHeckeEulerFactor_summableUniformlyOn (χ : U[F])
    (K : Set ℂ) (hK : IsCompact K) (h : K ⊆ halfPlane) :
    SummableUniformlyOn (fun v s ↦ ‖finiteHeckeEulerFactor χ v s - 1‖) K := by
  obtain ⟨r, hr, hmin⟩ : ∃ r : ℝ, 1 < r ∧ ∀ s ∈ K, r ≤ s.re := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨2, by norm_num, by simp⟩
    · obtain ⟨s, hs, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
      exact ⟨s.re, h hs, fun x hx ↦ hmin hx⟩
  have hu : Summable fun v : HeightOneSpectrum (𝓞 F) ↦ (v.asIdeal.absNorm : ℝ) ^ (-r) :=
    (summable_absNorm_rpow F hr).comp_injective (fun _ _ he ↦ HeightOneSpectrum.ext he)
  apply (HasSumUniformlyOn.of_norm_le_summable (hu.mul_left 2) _).summableUniformlyOn
  intro v s hs
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_finiteHeckeEulerFactor_sub_one_le χ v hr (hmin s hs)

/-- Paper: Definition 3.2.1.2, p. 123. The Hecke L-function on the half-plane
is the archimedean gamma factor times Mathlib's finite Hecke L-series. -/
def completedHeckeL (χ : U[F]) (s : halfPlane) : ℂ :=
  heckeGammaFactor χ s * χ₀(χ).LSeries s

/-- Paper: Definition 3.2.1.4, pp. 123–124. The finite Hecke L-function
uses Mathlib's Hecke L-series on the half-plane of absolute convergence. -/
def finiteHeckeL (χ : U[F]) (s : halfPlane) : ℂ :=
  χ₀(χ).LSeries s

/-- Paper: Definition 3.2.1.4, pp. 123–124. In the half-plane where the Euler
product is defined, Mathlib's finite Hecke Dirichlet series is absolutely summable. -/
theorem finiteHeckeL_seriesSummable (χ : U[F]) (s : halfPlane) :
    LSeriesSummable χ₀(χ).LFunction s := by
  exact LSeriesSummable_heckeLFunction _ s.property fun v _ ↦
    (norm_ideleClassNormTwist_zero_localValue χ v).le

/-- Each formal local Euler factor has a geometric Dirichlet series with the stated analytic
value in the half-plane of absolute convergence. -/
private theorem LSeriesHasSum_finiteHeckeEulerFactor (χ : U[F])
    (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (χ₀(χ).localEulerFactor v) s (finiteHeckeEulerFactor χ v s) := by
  classical
  let a := if χ₀(χ).IsUnramifiedAt v then χ₀(χ).localValue v else 0
  let q := v.asIdeal.absNorm
  let z := a * (q : ℂ) ^ (-s)
  have hq : 1 < q := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have ha : ‖a‖ ≤ 1 := by
    by_cases h : χ₀(χ).IsUnramifiedAt v <;> simp [a, h, norm_ideleClassNormTwist_zero_localValue]
  have hz : ‖z‖ < 1 := by
    change ‖a * ((q : ℝ) : ℂ) ^ (-s)‖ < 1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < (q : ℝ)) _,
      Complex.neg_re]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) ha).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hq' (by linarith))
  have hval : finiteHeckeEulerFactor χ v s = (1 - z)⁻¹ := by
    by_cases h : χ₀(χ).IsUnramifiedAt v <;> simp [finiteHeckeEulerFactor, z, a, q, h]
  rw [hval, HeckeCharacter.localEulerFactor, card_residueField_adicCompletion,
    hecke_localPowerSeries_eq_mk]
  obtain ⟨hpow, hout⟩ := LSeries_term_geometric_ofPowerSeries hq a s
  apply (Nat.pow_right_injective hq).hasSum_iff hout |>.mp
  exact (hasSum_geometric_of_norm_lt_one hz).congr_fun hpow

/-- Paper: Definition 3.2.1.4, pp. 123–124. The partial Hecke Euler products converge
uniformly to the Hecke Dirichlet series on every closed half-plane to the right of one. -/
theorem finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane (χ : U[F]) {a : ℝ} (ha : 1 < a) :
    TendstoUniformlyOn
      (fun S : Finset (HeightOneSpectrum (𝓞 F)) ↦ fun s ↦ ∏ v ∈ S, finiteHeckeEulerFactor χ v s)
      χ₀(χ).LSeries atTop {s : ℂ | a ≤ s.re} := by
  obtain ⟨r, hr, hra⟩ := exists_between ha
  let Places := HeightOneSpectrum (𝓞 F)
  let ψ := χ₀(χ)
  let f := ψ.localEulerFactor
  let u (v : Places) := 2 * (v.asIdeal.absNorm : ℝ) ^ (-r)
  have hu : Summable u := ((summable_absNorm_rpow F hr).comp_injective
    (fun v w (h : (v : Places).asIdeal = w.asIdeal) ↦ HeightOneSpectrum.ext h)).mul_left 2
  have hlocal (v : Places) := LSeries_heckeLocalEulerFactor_bound ψ v (s := (r : ℂ)) hr
    (fun _ ↦ (norm_ideleClassNormTwist_zero_localValue χ v).le)
  have hp := LSeries_finset_prod_bound f (r : ℂ) (u := u)
    (fun v ↦ (hlocal v).1) (fun v ↦ (hlocal v).2)
  have hu₀ (v : Places) : 0 ≤ u v :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hC (S : Finset Places) :
      (∑' n, ‖LSeries.term ⇑(∏ v ∈ S, f v) (r : ℂ) n‖) ≤ Real.exp (∑' v, u v) :=
    (hp S).2.trans (Real.exp_le_exp.mpr (hu.sum_le_tsum S (fun v _ ↦ hu₀ v)))
  have h := tendstoUniformlyOn_LSeries_of_eventuallyEq
    (fun S : Finset Places ↦ ⇑(∏ v ∈ S, f v)) ψ.LFunction hra (Real.exp_pos _).le
    (fun S ↦ (hp S).1) (finiteHeckeL_seriesSummable χ ⟨(r : ℂ), hr⟩) hC
    (heckeLocalEulerFactor_eventually_prod_eq ψ)
  apply h.congr
  exact Filter.Eventually.of_forall fun S s hs ↦
    (LSeriesHasSum_finset_prod f _ s (fun v ↦ LSeriesHasSum_finiteHeckeEulerFactor χ v
      (ha.trans_le hs)) S).LSeries_eq

/-- The reciprocal archimedean factor is entire, including at the poles of the gamma factors. -/
theorem differentiable_inv_heckeGammaFactor (χ : U[F]) :
    Differentiable ℂ (fun s ↦ (heckeGammaFactor χ s)⁻¹) := by
  classical
  unfold heckeGammaFactor
  simp_rw [← Finset.prod_inv_distrib]
  apply Differentiable.fun_finsetProd
  intro v _
  by_cases hv : v.IsReal
  · simp only [dite_eq_left hv]
    apply Complex.differentiable_Gammaℝ_inv.comp
    fun_prop
  · simp only [dite_eq_right hv, div_eq_mul_inv, mul_inv_rev, inv_inv]
    apply Differentiable.const_mul
    apply Complex.differentiable_Gammaℂ_inv.comp
    fun_prop

/-- No archimedean gamma factor vanishes on the positive half-plane. -/
theorem heckeGammaFactor_ne_zero_of_re_pos (χ : U[F]) {s : ℂ} (hs : 0 < s.re) :
    heckeGammaFactor χ s ≠ 0 := by
  classical
  unfold heckeGammaFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  by_cases hv : v.IsReal
  · simp only [dite_eq_left hv]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
    simp only [Complex.add_re, Complex.natCast_re, ha, add_zero]
    positivity
  · simp only [dite_eq_right hv]
    apply (div_ne_zero · two_ne_zero)
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let a := (complexHeckeCharacter_parameters χ v hv').exists.choose
    have ha : a.1.re = 0 := (complexHeckeCharacter_parameters χ v hv').exists.choose_spec.1
    have ht : 0 < (s + a.1 + (a.2.natAbs : ℂ) / 2).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, ha, add_zero]
      positivity
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos ht)
      (Complex.Gammaℝ_ne_zero_of_re_pos (by
        simpa only [Complex.add_re, Complex.one_re] using
          (add_pos ht zero_lt_one)))

/-- The archimedean factor is holomorphic on the positive half-plane. -/
theorem differentiableAt_heckeGammaFactor_of_re_pos (χ : U[F]) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (heckeGammaFactor χ) s := by
  have h := (differentiable_inv_heckeGammaFactor χ).differentiableAt (x := s)
  have hd : DifferentiableAt ℂ (fun t ↦ ((heckeGammaFactor χ t)⁻¹)⁻¹) s :=
    h.inv (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hs))
  simpa only [inv_inv] using hd

/-- Paper: Lemma 3.2.1.1, p. 123. The Euler product multiplied by the archimedean
gamma factor converges uniformly on compact subsets of the open half-plane. -/
theorem completedHeckeEulerProduct_hasProdUniformlyOn (χ : U[F])
    (K : Set ℂ) (hK : IsCompact K) (h : K ⊆ halfPlane) :
    TendstoUniformlyOn
      (fun S : Finset (HeightOneSpectrum (𝓞 F)) ↦
        fun s ↦ heckeGammaFactor χ s * ∏ v ∈ S, finiteHeckeEulerFactor χ v s)
      (fun s ↦ heckeGammaFactor χ s * χ₀(χ).LSeries s) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  have hu := (finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane χ (a := s₀.re) (h hs₀)).mono
    (fun s hs ↦ hmin hs : K ⊆ {s : ℂ | s₀.re ≤ s.re})
  have hc : ContinuousOn (fun s ↦ ‖heckeGammaFactor χ s‖) K := fun s hs ↦
    (differentiableAt_heckeGammaFactor_of_re_pos χ (zero_lt_one.trans (h hs))).continuousAt.norm.continuousWithinAt
  obtain ⟨b, _, hb⟩ := hK.exists_isMaxOn hne hc
  let B := ‖heckeGammaFactor χ b‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / B) (div_pos hε hB)] with T hT
  intro s hs
  have hbound : ‖heckeGammaFactor χ s‖ ≤ B := (hb hs).trans (by dsimp [B]; linarith)
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  have hsmall := hT s hs
  rw [dist_eq_norm] at hsmall
  exact (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)).trans_lt
    ((mul_lt_mul_of_pos_left hsmall hB).trans_eq (mul_div_cancel₀ _ hB.ne'))

/-- Paper: Definition 3.2.1.4, pp. 123–124. The finite Hecke L-function
is the value of the convergent Euler product with the ramified factors omitted. -/
theorem finiteHeckeL_hasProd (χ : U[F]) (s : halfPlane) :
    HasProd (fun v ↦ finiteHeckeEulerFactor χ v s) (finiteHeckeL χ s) := by
  have h := finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane χ (a := s.val.re) s.property
  exact h.tendsto_at (x := s.val) (Set.mem_ofPred.mpr (le_refl s.val.re))

/-- Paper: Definition 3.2.1.2, p. 123. For the trivial character the completed
L-function on the half-plane is the corresponding gamma product times Dedekind zeta. -/
theorem completedHeckeL_one_eq_dedekindZeta (s : halfPlane) :
    completedHeckeL (1 : U[F]) s =
      Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces F *
        (Complex.Gammaℂ s / 2) ^ InfinitePlace.nrComplexPlaces F * dedekindZeta F s := by
  classical
  have hχ : χ₀((1 : U[F])) = 1 := by
    ext1 g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hlocal (v : HeightOneSpectrum (𝓞 F)) :
      finiteHeckeEulerFactor (1 : U[F]) v s =
        (1 - (v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ)))⁻¹ := by
    have hunit (u : (v.adicCompletion F)ˣ) : (1 : 𝒳[F]).restrict v u = 1 := by
      rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
      rfl
    have hu : (1 : 𝒳[F]).IsUnramifiedAt v := HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦
      hunit (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x)
    let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
      val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
    have hval : (1 : 𝒳[F]).localValue v = 1 := hunit u
    rw [finiteHeckeEulerFactor, hχ, ite_eq_left hu, hval, one_mul]
  have h := (finiteHeckeL_hasProd (1 : U[F]) s).unique
    ((dedekindZeta_hasProd F s.property).congr_fun hlocal)
  exact congrArg₂ (· * ·) (heckeGammaFactor_one s) h

/-- A unitary character trivial on the norm-one subgroup is a unique imaginary power of the norm. -/
private theorem existsUnique_ideleClassNormTwist (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    ∃! t : ℝ, χ₀(χ) = ideleClassNormTwist (1 : U[F]) (-Complex.I * (t : ℂ)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨σ, hσ, hnorm⟩, _⟩ := ideleGroup_quotient.{_, 0} F
  let c : ℝ≥0ˣ →ₜ* ℂ := χ₀(χ).comp ⟨σ, hσ⟩
  have hunit (g : C[F]) : χ₀(χ) g = (χ g : ℂ) := by
    change (χ g : ℂ) * _ ^ (0 : ℂ) = _
    simp
  obtain ⟨z, ⟨hzre, hz⟩, huniq⟩ :=
    existsUnique_unitaryComplexPower c (fun u ↦ by
      change ‖χ₀(χ) (σ u)‖ = 1
      rw [hunit, Circle.norm_coe])
  have hparam : -Complex.I * ((-z.im : ℝ) : ℂ) = z := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hzre]
  refine ⟨-z.im, ?_, ?_⟩
  · change χ₀(χ) = ideleClassNormTwist (1 : U[F]) (-Complex.I * ((-z.im : ℝ) : ℂ))
    rw [hparam]
    ext1 g
    let u := ideleClassNorm F g
    have hk : g / σ u ∈ (ideleClassNorm F).ker := MonoidHom.mem_ker.mpr (by
      rw [map_div, hnorm u, div_self'])
    have hkχ : χ (g / σ u) = 1 :=
      DFunLike.congr_fun hχ (⟨g / σ u, hk⟩ : (ideleClassNorm F).ker)
    have he : χ₀(χ) (g / σ u) = 1 := by rw [hunit, hkχ, Circle.coe_one]
    calc
      χ₀(χ) g = χ₀(χ) (g / σ u) * c u := by
        change χ₀(χ) g = χ₀(χ) (g / σ u) * χ₀(χ) (σ u)
        rw [← map_mul, div_mul_cancel]
      _ = ideleClassNormTwist (1 : U[F]) z g := by
        change χ₀(χ) (g / σ u) * c u = 1 * (classNormℝ g : ℂ) ^ z
        rw [he, hz u]
  · intro t ht
    have he : -Complex.I * (t : ℂ) = z := huniq _ ⟨by simp [Complex.mul_re], fun u ↦ by
      change χ₀(χ) (σ u) = _
      rw [ht]
      change (1 : ℂ) * (classNormℝ (σ u) : ℂ) ^ (-Complex.I * (t : ℂ)) = _
      dsimp only
      rw [one_mul, hnorm u]⟩
    apply neg_eq_iff_eq_neg.mp
    simpa [Complex.mul_im] using congrArg Complex.im he

/-- An imaginary norm twist translates the argument of the archimedean product. -/
private theorem heckeGammaFactor_of_normTwist (χ : U[F]) (a : ℂ) (ha : a.re = 0)
    (hχ : χ₀(χ) = ideleClassNormTwist (1 : U[F]) a) (s : ℂ) :
    heckeGammaFactor χ s = heckeGammaFactor (1 : U[F]) (s + a) := by
  classical
  have hre (v : InfinitePlace F) (hv : v.IsReal) :
      (realHeckeCharacter_parameters χ v hv).exists.choose = (a, 0) := by
    apply (realHeckeCharacter_parameters χ v hv).unique
      (realHeckeCharacter_parameters χ v hv).exists.choose_spec
    refine ⟨ha, fun x ↦ ?_⟩
    rw [hχ]
    let u := Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom x
    change 1 * (classNormℝ (IdeleClassGroup.ofCompletion (𝓞 F) F v u) : ℂ) ^ a =
      (‖(x : ℝ)‖ : ℂ) ^ a * _ ^ (0 : ℕ)
    dsimp only
    rw [ideleClassNorm_ofCompletion, hv.mult_eq_one, pow_one]
    have hn : ((↑(Units.map nnNormHom.toMonoidHom u) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
      let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
      change ‖e (x : ℝ)‖ = ‖(x : ℝ)‖
      exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero
        (map_zero e) (x : ℝ)
    rw [hn, one_mul, pow_zero, mul_one]
  have hco (v : InfinitePlace F) (hv : v.IsComplex) :
      (complexHeckeCharacter_parameters χ v hv).exists.choose = (a, 0) := by
    apply (complexHeckeCharacter_parameters χ v hv).unique
      (complexHeckeCharacter_parameters χ v hv).exists.choose_spec
    refine ⟨ha, fun x ↦ ?_⟩
    rw [hχ]
    let u := Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toMonoidHom x
    change 1 * (classNormℝ (IdeleClassGroup.ofCompletion (𝓞 F) F v u) : ℂ) ^ a =
      ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ a * _ ^ (0 : ℤ)
    dsimp only
    rw [ideleClassNorm_ofCompletion, hv.mult_eq_two, Units.val_pow_eq_pow_val, NNReal.coe_pow]
    have hn : ((↑(Units.map nnNormHom.toMonoidHom u) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ := by
      let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
      change ‖e (x : ℂ)‖ = ‖(x : ℂ)‖
      exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.isometry.norm_map_of_map_zero
        (map_zero e) (x : ℂ)
    rw [hn, one_mul, zpow_zero, mul_one]
  rw [heckeGammaFactor_one, heckeGammaFactor]
  simp_rw [hre, hco]
  simp only [Fin.val_zero, Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, dite_eq_ite]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, ← Fintype.card_subtype, InfinitePlace.not_isReal_iff_isComplex]

/-- The finite Euler factor of a norm twist depends on the sum of the two exponents. -/
private theorem finiteHeckeEulerFactor_of_normTwist (χ : U[F]) (a : ℂ)
    (hχ : χ₀(χ) = ideleClassNormTwist (1 : U[F]) a)
    (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    finiteHeckeEulerFactor χ v s = finiteHeckeEulerFactor (1 : U[F]) v (s + a) := by
  classical
  have hval (z : ℂ) (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (1 : U[F]) z).restrict v u =
        (‖(u : v.adicCompletion F)‖ : ℂ) ^ z := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change 1 * (classNormℝ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℂ) ^ z = _
    dsimp only
    rw [one_mul, ideleClassNorm_ofAdicCompletion]
    rfl
  have hu (z : ℂ) : (ideleClassNormTwist (1 : U[F]) z).IsUnramifiedAt v := by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro x
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    change (ideleClassNormTwist (1 : U[F]) z).restrict v u = 1
    rw [hval z u, show ‖(u : v.adicCompletion F)‖ = 1 from ?_, Complex.ofReal_one, Complex.one_cpow]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show u ∈ (v.adicCompletionIntegers F).units from ⟨x.val.property, x.inv.property⟩)
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  have hnorm : ‖(u : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v _ hπ
  rw [finiteHeckeEulerFactor, finiteHeckeEulerFactor, hχ, ite_eq_left (hu a), ite_eq_left (hu 0),
    (hu a).localValue_eq u hπ, (hu 0).localValue_eq u hπ, hval, hval, hnorm, Complex.cpow_zero,
    one_mul, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) a,
    ← Complex.cpow_neg, Complex.ofReal_natCast,
    ← Complex.cpow_add _ _ (by exact_mod_cast ((zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))).ne'),
    neg_add, add_comm (-a)]

/-- On the half-plane of convergence, twisting the trivial character shifts the
completed L-function by the norm exponent. -/
private theorem completedHeckeL_of_normTwist (χ : U[F]) (a : ℂ) (ha : a.re = 0)
    (hχ : χ₀(χ) = ideleClassNormTwist (1 : U[F]) a) (s : halfPlane) :
    completedHeckeL χ s =
      completedHeckeL (1 : U[F]) ⟨(s : ℂ) + a, by
        change 1 < (s : ℂ).re + a.re
        rw [ha, add_zero]
        exact s.property⟩ := by
  let w : halfPlane := ⟨(s : ℂ) + a, by
    change 1 < (s : ℂ).re + a.re
    rw [ha, add_zero]
    exact s.property⟩
  have h := (finiteHeckeL_hasProd χ s).unique <|
    (finiteHeckeL_hasProd (1 : U[F]) w).congr_fun
      (fun v ↦ finiteHeckeEulerFactor_of_normTwist χ a hχ v s)
  exact congrArg₂ (· * ·) (heckeGammaFactor_of_normTwist χ a ha hχ s) h

/-- The class number formula gives a simple pole at one for a continuation
of the completed L-function of the trivial character. -/
private theorem completedHeckeL_one_order_one (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (h : ∀ s : halfPlane, L s = completedHeckeL (1 : U[F]) s) :
    meromorphicOrderAt L 1 = -1 := by
  let P (s : ℂ) := (s - 1) * L s
  let γ := heckeGammaFactor (1 : U[F])
  let c : ℂ := γ 1 * dedekindZeta_residue F
  have hγ : DifferentiableAt ℂ γ 1 :=
    differentiableAt_heckeGammaFactor_of_re_pos _ (by simp)
  have hc : c ≠ 0 := mul_ne_zero
    (heckeGammaFactor_ne_zero_of_re_pos _ (by simp))
    (Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero F))
  have hreal : Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using (show 1 < r from hr).ne'
  have hlim : Tendsto (fun r : ℝ ↦ P r) (𝓝[>] (1 : ℝ)) (𝓝 c) := by
    apply ((hγ.continuousAt.tendsto.comp (hreal.mono_right nhdsWithin_le_nhds)).mul
      (tendsto_sub_one_mul_dedekindZeta_nhdsGT F)).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (r : ℂ) ∈ halfPlane := by simpa using hr
    have he := h ⟨r, hr'⟩
    rw [completedHeckeL_one_eq_dedekindZeta, ← heckeGammaFactor_one] at he
    dsimp [P, γ]
    rw [show L r = heckeGammaFactor (1 : U[F]) r * dedekindZeta F r from he]
    ring
  have hsub : AnalyticAt ℂ (fun s : ℂ ↦ s - 1) 1 := by fun_prop
  have horder : meromorphicOrderAt P 1 = 0 := by
    rcases lt_trichotomy (meromorphicOrderAt P 1) 0 with hneg | he | hpos
    · have hinf := (tendsto_norm_atTop_iff_cobounded.mpr
        (tendsto_cobounded_of_meromorphicOrderAt_neg hneg)).comp hreal
      exact (not_tendsto_atTop_of_tendsto_nhds hlim.norm hinf).elim
    · exact he
    · exact (hc (tendsto_nhds_unique hlim
        ((tendsto_zero_of_meromorphicOrderAt_pos hpos).comp hreal))).elim
  have hsubOrder : meromorphicOrderAt (fun s : ℂ ↦ s - 1) 1 = 1 := by
    exact (meromorphicOrderAt_eq_int_iff hsub.meromorphicAt (n := 1)).mpr
      ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, by simp⟩
  change meromorphicOrderAt ((fun s : ℂ ↦ s - 1) * L) 1 = 0 at horder
  rw [meromorphicOrderAt_mul hsub.meromorphicAt (hL (mem_univ _)).meromorphicAt, hsubOrder]
    at horder
  have he : (-(1 : ℤ) : WithTop ℤ) + (1 : WithTop ℤ) = 0 := by norm_num
  simpa [← add_assoc, he] using congrArg (fun x : WithTop ℤ ↦ (-1) + x) horder

/-- Paper: Definition 3.2.1.4, pp. 123–124. The finite Euler product
converges uniformly on each compact subset of the half-plane. -/
theorem finiteHeckeL_hasProdUniformlyOn (χ : U[F]) (K : Set halfPlane) (hK : IsCompact K) :
    HasProdUniformlyOn (fun v (s : halfPlane) ↦ finiteHeckeEulerFactor χ v s) (finiteHeckeL χ) K := by
  apply hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  · obtain ⟨s₀, _, hmin⟩ := hK.exists_isMinOn hne
      (Complex.continuous_re.comp continuous_subtype_val).continuousOn
    have h := finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane χ (a := s₀.val.re) s₀.property
    exact (h.comp (fun s : halfPlane ↦ s.val)).mono fun s hs ↦ hmin hs

/-- Paper: Equation (3.2.1.9), p. 124. The reflection multiplier is the ratio
of the reflected and original gamma factors divided by the entire epsilon factor.
Deviation: Values at singularities use the meromorphic normal form. -/
def finiteHeckeReflectionFactor (χ : U[F]) (ε : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun s ↦ (ε s)⁻¹ * (heckeGammaFactor χ⁻¹ (1 - s) / heckeGammaFactor χ s)) univ

/-- The archimedean gamma factor is meromorphic on the plane. -/
theorem meromorphic_heckeGammaFactor (χ : U[F]) : Meromorphic (heckeGammaFactor χ) := by
  intro s
  have h : MeromorphicAt (fun t ↦ ((heckeGammaFactor χ t)⁻¹)⁻¹) s :=
    ((differentiable_inv_heckeGammaFactor χ).analyticAt s).meromorphicAt.inv
  simpa only [inv_inv] using h

/-- Paper: Equation (3.2.1.9), p. 124. At the midpoint for the trivial character
the gamma factors cancel, leaving the reciprocal epsilon factor. -/
theorem finiteHeckeReflectionFactor_one_half (ε : ℂ → ℂ) (hε : Differentiable ℂ ε)
    (hn : ∀ s, ε s ≠ 0) :
    finiteHeckeReflectionFactor (1 : U[F]) ε (1 / 2) = (ε (1 / 2))⁻¹ := by
  let G := heckeGammaFactor (1 : U[F])
  let p : ℂ := 1 / 2
  let f (s : ℂ) := (ε s)⁻¹ * (G (1 - s) / G s)
  have hG := meromorphic_heckeGammaFactor (1 : U[F])
  have hf : Meromorphic f := fun z ↦ (hε.analyticAt z).meromorphicAt.inv.mul
    (((hG (1 - z)).comp_analyticAt (analyticAt_const.sub analyticAt_id)).div (hG z))
  have hp : 0 < p.re := by norm_num [p]
  have hsym : 1 - p = p := by dsimp [p]; ring
  have hG₀ : G p ≠ 0 := heckeGammaFactor_ne_zero_of_re_pos _ hp
  have haG : AnalyticAt ℂ G p := by
    apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
      (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos (1 : U[F]) hz).differentiableWithinAt)
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp
  have hfa : AnalyticAt ℂ f p := (hε.analyticAt p).inv (hn p) |>.mul
    (((hsym.symm ▸ haG : AnalyticAt ℂ G (1 - p)).comp (analyticAt_const.sub analyticAt_id)).div haG hG₀)
  change toMeromorphicNFOn _ univ p = _
  simp only [inv_one]
  change toMeromorphicNFOn f univ p = _
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf.meromorphicOn (Set.mem_univ p),
    toMeromorphicNFAt_eq_self.mpr hfa.meromorphicNFAt]
  change f p = (ε p)⁻¹
  simp [f, hsym, hG₀]

end Hecke

section Zeta

local instance globalZetaIdeleMeasurableSpace : MeasurableSpace 𝕀[F] := borel _
local instance globalZetaIdeleClassMeasurableSpace : MeasurableSpace C[F] := borel _

/-- Paper: §3.2.2, p. 124. An idele belongs to the closed norm band if its norm
lies between the two endpoints. -/
def ideleNormBand (F : Type*) [Field F] [NumberField F] (a b : ℝ) : Set 𝕀[F] :=
  {g | ((ideleNorm F g : ℝ≥0) : ℝ) ∈ Icc a b}

/-- Paper: §3.2.2, p. 124. The identity lies in a closed norm band precisely
when the band contains one. -/
theorem one_mem_ideleNormBand (a b : ℝ) :
    (1 : 𝕀[F]) ∈ ideleNormBand F a b ↔ a ≤ 1 ∧ 1 ≤ b := by
  simp [ideleNormBand]

/-- Paper: §3.2.2, p. 124. The surjective idele class norm takes values
other than one, so its abscissa is defined. -/
theorem ideleClassNorm_ne_one : ∃ g : C[F], ideleClassNorm F g ≠ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  let t := Units.mk0 (2 : ℝ≥0) (by norm_num)
  obtain ⟨g, hg⟩ := hsurj t
  refine ⟨g, fun h ↦ ?_⟩
  have ht := congrArg Units.val (hg.symm.trans h)
  norm_num [t] at ht

local notation "rightHalf" =>
  (relativeRightHalfPlane (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) 1 : Set 𝒳[F])

/-- Paper: Equation (3.2.2.1), p. 124. The global zeta integral is the
multiplicative Tamagawa integral of the test function against the quasi-character
pulled back to the ideles. The convergence statements give its domain of use. -/
def globalIdelicZetaIntegral (f : ℬ[F]) (c : 𝒳[F]) : ℂ :=
  ∫ g : 𝕀[F], f (Multiplicative.ofAdd g.val) * c (classOf g) ∂multiplicativeTamagawaMeasure F

/-- Paper: Equation (3.2.2.1), p. 124. At the squared norm character, the
zeta integral weights the test function by the square of the idelic norm. -/
theorem globalIdelicZetaIntegral_normSquared (f : ℬ[F]) :
    globalIdelicZetaIntegral f (ideleClassNormTwist (1 : U[F]) 2) =
      ∫ g : 𝕀[F], f (Multiplicative.ofAdd g.val) * ((ideleNorm F g : ℝ≥0) : ℂ) ^ (2 : ℕ)
        ∂multiplicativeTamagawaMeasure F := by
  unfold globalIdelicZetaIntegral
  congr 1
  funext g
  congr 1
  change (((1 : U[F]) (classOf g) : Circle) : ℂ) * (classNormℝ (classOf g) : ℂ) ^ (2 : ℂ) = _
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_ofNat]
  rfl

section AbsoluteConvergence

local instance globalZetaIdeleClassBorelSpaceAbs : BorelSpace C[F] := ⟨rfl⟩

private theorem tate_classNormReal_pos (g : C[F]) : 0 < classNormℝ g :=
  NNReal.coe_pos.mpr (Units.zero_lt _)

private theorem tate_continuous_classNormReal : Continuous (fun g : C[F] ↦ classNormℝ g) :=
  NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)

/-- The logarithmic norm sends the class Haar measure to a multiple of Lebesgue
measure, since the class norm is proper and surjective. -/
private theorem tate_exists_map_logClassNorm_eq_smul_volume :
    ∃ c : ℝ≥0, (ideleClassTamagawaMeasure F).map (fun g ↦ Real.log (classNormℝ g)) =
      c • (volume : Measure ℝ) := by
  let μ := ideleClassTamagawaMeasure F
  let ν : Measure (Multiplicative ℝ) := (volume : Measure ℝ)
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil (F := F)).1
  let : ν.IsHaarMeasure := by
    have : IsFiniteMeasureOnCompacts ν :=
      inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
    have : Measure.IsOpenPosMeasure ν :=
      inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
    have : ν.IsMulLeftInvariant :=
      ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
    constructor
  let e : ℝ≥0ˣ ≃ₜ ℝ :=
    (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))).symm
  let m : C[F] →* Multiplicative ℝ :=
    { toFun := fun g ↦ Multiplicative.ofAdd (e (ideleClassNorm F g))
      map_one' := by
        change e (ideleClassNorm F 1) = 0
        simp [he]
      map_mul' := fun g h ↦ by
        change e (ideleClassNorm F (g * h)) = e (ideleClassNorm F g) + e (ideleClassNorm F h)
        rw [he, map_mul, Units.val_mul, NNReal.coe_mul, he, he]
        exact Real.log_mul (tate_classNormReal_pos g).ne' (tate_classNormReal_pos h).ne' }
  have hm : IsProperMap m :=
    e.isProperMap.comp (isProperMap_ideleClassNorm F)
  obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  have hsurj : Surjective m := e.surjective.comp hsurj
  let : (μ.map m).IsHaarMeasure :=
    Measure.isHaarMeasure_map μ m hm.continuous hsurj (isProperMap_iff_tendsto_cocompact.mp hm).2
  refine ⟨Measure.haarScalarFactor (μ.map m) ν, ?_⟩
  have hMap := Measure.isMulLeftInvariant_eq_smul (μ.map m) ν
  have hFun : (m : C[F] → ℝ) = fun g ↦ Real.log (classNormℝ g) :=
    funext fun g ↦ he (ideleClassNorm F g)
  rw [← hFun]
  exact hMap

/-- The idele group is σ-compact: the idele class group is a countable union of the
compact norm bands, each band lifts to a compact set of ideles, and the principal
ideles are countable. -/
private theorem ideleGroup_sigmaCompactSpace : SigmaCompactSpace 𝕀[F] := by
  obtain ⟨-, hGlc, -⟩ := ideleGroup_topology F
  let : LocallyCompactSpace 𝕀[F] := hGlc
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable Fˣ := Units.val_injective.countable
  let : Countable P := (Set.countable_range (IdeleGroup.unitEmbedding (𝓞 F) F)).to_subtype
  let e : ℝ≥0ˣ ≃ₜ ℝ :=
    (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  let K (n : ℕ) : Set C[F] := ideleClassNorm F ⁻¹' (e ⁻¹' Icc (-(n : ℝ)) n)
  have hK (n : ℕ) : IsCompact (K n) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage (e.isCompact_preimage.mpr isCompact_Icc)
  -- Every compact set of classes is covered by the image of a compact set of ideles.
  have hLift (A : Set C[F]) (hA : IsCompact A) :
      ∃ L : Set 𝕀[F], IsCompact L ∧ A ⊆ classOf '' L := by
    choose U hUc hU using fun k : 𝕀[F] ↦ exists_compact_mem_nhds k
    let V (k : 𝕀[F]) : Set C[F] := classOf '' interior (U k)
    have hVo (k : 𝕀[F]) : IsOpen (V k) := QuotientGroup.isOpenMap_coe _ isOpen_interior
    have hCover : A ⊆ ⋃ k, V k := by
      intro g _
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
      exact mem_iUnion.mpr ⟨k, mem_image_of_mem _ (mem_interior_iff_mem_nhds.mpr (hU k))⟩
    obtain ⟨s, hs⟩ := hA.elim_finite_subcover V hVo hCover
    refine ⟨⋃ k : s, U k, isCompact_iUnion fun k ↦ hUc k, fun g hg ↦ ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hg)
    obtain ⟨hi', k, hk, rfl⟩ := mem_iUnion.mp hi
    exact ⟨k, mem_iUnion.mpr ⟨⟨i, hi'⟩, interior_subset hk⟩, rfl⟩
  choose L hLc hL using fun n ↦ hLift (K n) (hK n)
  refine SigmaCompactSpace.of_countable
    (Set.range fun np : ℕ × P ↦ (fun x : 𝕀[F] ↦ x * (np.2 : 𝕀[F])) '' L np.1)
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨np, rfl⟩
    exact (hLc np.1).image (continuous_id.mul continuous_const)
  · refine eq_univ_of_forall fun g ↦ ?_
    let n := ⌈|e (ideleClassNorm F (classOf g))|⌉₊
    have hn : classOf g ∈ K n := by
      change e (ideleClassNorm F (classOf g)) ∈ Icc (-(n : ℝ)) n
      exact abs_le.mp (Nat.le_ceil _)
    obtain ⟨l, hl, hlg⟩ := hL n hn
    have hmem : l⁻¹ * g ∈ P := QuotientGroup.eq.mp hlg
    refine mem_sUnion.mpr ⟨_, ⟨(n, ⟨l⁻¹ * g, hmem⟩), rfl⟩, l, hl, ?_⟩
    change l * (l⁻¹ * g) = g
    exact mul_inv_cancel_left l g

end AbsoluteConvergence

/-- Paper: Theorem 3.2.2.1(1), p. 124. The global zeta integral converges
absolutely for every quasi-character with abscissa greater than one. -/
theorem globalIdelicZetaIntegral_integrable (f : ℬ[F]) (c : 𝒳[F]) (hc : c ∈ rightHalf) :
    Integrable (fun g : 𝕀[F] ↦ f (Multiplicative.ofAdd g.val) * c (classOf g))
      (multiplicativeTamagawaMeasure F) := by
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  obtain ⟨hG₂, hGlc, -⟩ := ideleGroup_topology F
  obtain ⟨hinj, hP, hPd, -, -, hC₂, -, hqn, -⟩ := ideleGroup_quotient.{_, 0} F
  let : T2Space 𝕀[F] := hG₂
  let : LocallyCompactSpace 𝕀[F] := hGlc
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : BorelSpace C[F] := ⟨rfl⟩
  let : T2Space C[F] := hC₂
  let : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp hPd
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable Fˣ := Units.val_injective.countable
  let : Countable P := (Set.countable_range (IdeleGroup.unitEmbedding (𝓞 F) F)).to_subtype
  let : SigmaCompactSpace 𝕀[F] := ideleGroup_sigmaCompactSpace
  have hspec := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : (multiplicativeTamagawaMeasure F).IsHaarMeasure := hspec.1
  let : (multiplicativeTamagawaMeasure F).Regular := hspec.2.1
  let count : Measure P := Measure.count
  let : count.IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ h ↦ Measure.count_apply_lt_top.mpr h.finite_of_discrete
      open_pos := fun _ _ h ↦ Measure.count_ne_zero h }
  let e : Fˣ ≃ P := (MonoidHom.ofInjective hinj).toEquiv
  have he (ξ : Fˣ) : ((e ξ : 𝕀[F]) : 𝔸[F]) = algebraMap F 𝔸[F] (ξ : F) := rfl
  let Φ : 𝕀[F] → ℂ := fun g ↦ f (Multiplicative.ofAdd g.val) * c (classOf g)
  have hΦ : Continuous Φ :=
    ((schwartzBruhat_continuous f).comp (continuous_ofAdd.comp Units.continuous_val)).mul
      (c.continuous.comp continuous_quotient_mk')
  -- The absolute theta series and the modulus of the quasi-character.
  let Θ (g : 𝕀[F]) : ℝ :=
    ∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd (g.val * algebraMap F 𝔸[F] (ξ : F)))‖
  have hΘsum (g : 𝕀[F]) : Summable (fun ξ : Fˣ ↦
      ‖f (Multiplicative.ofAdd (g.val * algebraMap F 𝔸[F] (ξ : F)))‖) := by
    simpa only [add_zero] using
      (adelicAverage_summableUniformlyOn f {(g, 0)} isCompact_singleton).summable rfl
  let σ := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) c
  have hσ : 1 < σ := hc
  have hcnorm (q : C[F]) : ‖c q‖ = classNormℝ q ^ σ :=
    norm_quasiCharacter_eq_rpow_abscissa _ _ _ c q
  -- Each fibre integral of the norm is the absolute theta series times the modulus.
  have hfibre (q : C[F]) :
      (∫⁻ h : P, ‖Φ (q.out * (h : 𝕀[F]))‖₊ ∂count) =
        ENNReal.ofReal (Θ q.out * classNormℝ q ^ σ) := by
    rw [lintegral_count, ← e.tsum_eq]
    have hterm (ξ : Fˣ) : (‖Φ (q.out * (e ξ : 𝕀[F]))‖₊ : ENNReal) =
        ENNReal.ofReal (‖f (Multiplicative.ofAdd (q.out.val * algebraMap F 𝔸[F] (ξ : F)))‖ *
          classNormℝ q ^ σ) := by
      have hcl : classOf (q.out * (e ξ : 𝕀[F])) = q := by
        rw [QuotientGroup.mk_mul_of_mem _ (e ξ).property, QuotientGroup.out_eq']
      have hΦe : Φ (q.out * (e ξ : 𝕀[F])) =
          f (Multiplicative.ofAdd (q.out.val * algebraMap F 𝔸[F] (ξ : F))) * c q := by
        simp only [Φ, hcl, Units.val_mul, he]
      rw [← hcnorm, ← norm_mul, ofReal_norm, eNorm_eq_nnNorm, hΦe]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity)
      ((hΘsum q.out).mul_right _), tsum_mul_right]
  -- The pointwise majorant in the logarithmic norm coordinate.
  obtain ⟨C₁, hC₁, hlarge⟩ := adelicTheta_normSum_decay_large f (⌈σ⌉₊ + 1)
  obtain ⟨C₂, hC₂', hsmall⟩ := adelicTheta_normSum_le_small f
  let a := min (σ - 1) 1
  have ha : 0 < a := lt_min (by linarith) one_pos
  let C := max C₁ C₂
  have hbound (q : C[F]) :
      Θ q.out * classNormℝ q ^ σ ≤ C * Real.exp (-(a * |Real.log (classNormℝ q)|)) := by
    have hn : ((ideleNorm F q.out : ℝ≥0) : ℝ) = classNormℝ q := by
      rw [← hqn q.out, QuotientGroup.mk'_apply, QuotientGroup.out_eq']
    have ht := tate_classNormReal_pos q
    set t := classNormℝ q
    rcases le_total t 1 with ht1 | ht1
    · have hΘ := hsmall q.out (hn ▸ ht1)
      rw [hn] at hΘ
      have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
      calc
        _ ≤ C₂ * t⁻¹ * t ^ σ := mul_le_mul_of_nonneg_right hΘ (by positivity)
        _ = C₂ * Real.exp (-((σ - 1) * |Real.log t|)) := by
          rw [abs_of_nonpos hlog, mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add ht,
            Real.rpow_def_of_pos ht]
          congr 2
          ring
        _ ≤ _ := by
          gcongr
          · exact le_max_right _ _
          · exact min_le_left _ _
    · have hΘ := hlarge q.out (hn ▸ ht1)
      rw [hn] at hΘ
      have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
      have hpow : t ^ σ ≤ t ^ (⌈σ⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (Nat.le_ceil σ)
      calc
        _ ≤ C₁ * (t ^ (⌈σ⌉₊ + 1))⁻¹ * t ^ (⌈σ⌉₊ : ℝ) :=
          mul_le_mul hΘ hpow (by positivity) (by positivity)
        _ = C₁ * Real.exp (-(1 * |Real.log t|)) := by
          rw [abs_of_nonneg hlog, one_mul, Real.exp_neg, Real.exp_log ht, Real.rpow_natCast,
            pow_succ]
          field_simp
        _ ≤ _ := by
          gcongr
          · exact le_max_left _ _
          · exact min_le_right _ _
  -- The majorant is integrable, through the logarithmic norm.
  obtain ⟨κ, hκ⟩ := tate_exists_map_logClassNorm_eq_smul_volume (F := F)
  let l (q : C[F]) := Real.log (classNormℝ q)
  have hl : Continuous l :=
    tate_continuous_classNormReal.log fun q ↦ (tate_classNormReal_pos q).ne'
  let M (x : ℝ) : ℝ := C * Real.exp (-(a * |x|))
  have hM : Continuous M :=
    continuous_const.mul (Real.continuous_exp.comp ((continuous_const.mul continuous_abs).neg))
  have hMint : Integrable M := by
    have hIic : IntegrableOn M (Iic 0) := by
      refine IntegrableOn.congr_fun (Integrable.const_mul (integrableOn_exp_mul_Iic ha 0) C)
        (fun x hx ↦ ?_) measurableSet_Iic
      change C * Real.exp (a * x) = C * Real.exp (-(a * |x|))
      rw [abs_of_nonpos hx, mul_neg, neg_neg]
    have hIoi : IntegrableOn M (Ioi 0) := by
      refine IntegrableOn.congr_fun
        (Integrable.const_mul (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0) C)
        (fun x hx ↦ ?_) measurableSet_Ioi
      change C * Real.exp (-a * x) = C * Real.exp (-(a * |x|))
      rw [abs_of_pos hx, neg_mul]
    have := hIic.union hIoi
    rwa [Iic_union_Ioi, integrableOn_univ] at this
  refine (integrable_of_weilNormIntegral P hP (multiplicativeTamagawaMeasure F) count
    (ideleClassTamagawaMeasure F) (ideleClassTamagawaMeasure_isWeil F) hΦ.measurable ?_).1
  calc
    _ = ∫⁻ q, ENNReal.ofReal (Θ q.out * classNormℝ q ^ σ) ∂ideleClassTamagawaMeasure F :=
      lintegral_congr fun q ↦ hfibre q
    _ ≤ ∫⁻ q, ENNReal.ofReal (M (l q)) ∂ideleClassTamagawaMeasure F :=
      lintegral_mono fun q ↦ ENNReal.ofReal_le_ofReal (hbound q)
    _ = ∫⁻ x, ENNReal.ofReal (M x) ∂((ideleClassTamagawaMeasure F).map l) :=
      (lintegral_map (ENNReal.measurable_ofReal.comp hM.measurable) hl.measurable).symm
    _ = κ * ∫⁻ x, ENNReal.ofReal (M x) := by
      rw [hκ, lintegral_smul_measure]
      rfl
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hMint.lintegral_lt_top

/-- The extreme abscissas on a compact family give a common integrable bound.
Its integral outside the expanding bands tends to zero by dominated convergence. -/
private theorem tendstoUniformlyOn_character_normBands {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (q : X → C[F]) (φ : X → ℂ) (K : Set 𝒳[F]) (hK : IsCompact K)
    (hInt : ∀ c ∈ K, Integrable (fun x ↦ φ x * c (q x)) μ)
    (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop)
    (hN : Measurable (fun x ↦ classNormℝ (q x))) :
    TendstoUniformlyOn (fun n c ↦ ∫ x in {x | classNormℝ (q x) ∈ Icc (a n)⁻¹ (a n)},
      φ x * c (q x) ∂μ) (fun c ↦ ∫ x, φ x * c (q x) ∂μ) atTop K := by
  classical
  let : T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  let σ := quasiCharacterAbscissa (G := C[F]) (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F))
  have hσ : Continuous σ := continuous_quasiCharacterAbscissa _ _ _
  obtain ⟨lo, hlo, hmin⟩ := hK.exists_isMinOn hne hσ.continuousOn
  obtain ⟨hi, hhi, hmax⟩ := hK.exists_isMaxOn hne hσ.continuousOn
  let M (x : X) := ‖φ x * lo (q x)‖ + ‖φ x * hi (q x)‖
  have hM : Integrable M μ := (hInt lo hlo).norm.add (hInt hi hhi).norm
  have hbound (c : 𝒳[F]) (hc : c ∈ K) (x : X) : ‖φ x * c (q x)‖ ≤ M x := by
    have hpos := tate_classNormReal_pos (q x)
    have hnorm (d : 𝒳[F]) : ‖d (q x)‖ = classNormℝ (q x) ^ σ d :=
      norm_quasiCharacter_eq_rpow_abscissa (G := C[F]) (ideleClassNorm F) _ _ d (q x)
    simp only [M, norm_mul, hnorm, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rcases le_total (classNormℝ (q x)) 1 with hx | hx
    · exact (Real.rpow_le_rpow_of_exponent_ge hpos hx (hmin hc)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hpos.le _))
    · exact (Real.rpow_le_rpow_of_exponent_le hx (hmax hc)).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hpos.le _))
  let S (n : ℕ) := {x | classNormℝ (q x) ∈ Icc (a n)⁻¹ (a n)}
  have hS (n : ℕ) : MeasurableSet (S n) := hN measurableSet_Icc
  have htail : Tendsto (fun n ↦ ∫ x in (S n)ᶜ, M x ∂μ) atTop (𝓝 0) := by
    simp_rw [← integral_indicator (hS _).compl]
    rw [← integral_zero X ℝ (μ := μ)]
    apply tendsto_integral_of_dominated_convergence M
    · exact fun n ↦ hM.aestronglyMeasurable.indicator (hS n).compl
    · exact hM
    · intro n
      apply Eventually.of_forall
      intro x
      have hx : 0 ≤ M x := add_nonneg (norm_nonneg _) (norm_nonneg _)
      by_cases h : x ∈ (S n)ᶜ <;> simp [h, Real.norm_of_nonneg hx, hx]
    · refine Eventually.of_forall fun x ↦ tendsto_const_nhds.congr' ?_
      filter_upwards [haTop.eventually_ge_atTop (classNormℝ (q x))⁻¹,
        haTop.eventually_ge_atTop (classNormℝ (q x))] with n hl hu
      have hx : x ∈ S n := ⟨(inv_le_comm₀ (zero_lt_one.trans_le (ha n))
        (tate_classNormReal_pos (q x))).2 hl, hu⟩
      simp [hx]
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [htail.eventually_lt_const hε] with n hn c hc
  rw [dist_eq_norm, ← integral_add_compl (hS n) (hInt c hc), add_sub_cancel_left]
  exact (norm_integral_le_integral_norm _).trans_lt ((integral_mono
    (hInt c hc).norm.integrableOn hM.integrableOn (hbound c hc)).trans_lt hn)

/-- Paper: Theorem 3.2.2.1(1) and Remark 3.2.2.2, pp. 124–125.
Norm-band truncations of the zeta integral converge uniformly on compact subsets
of the half-plane as the outer bound tends to infinity. -/
theorem globalIdelicZetaIntegral_tendstoUniformlyOn (f : ℬ[F]) (K : Set 𝒳[F])
    (hK : IsCompact K) (h : K ⊆ rightHalf) (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n c ↦
      ∫ g in ideleNormBand F (a n)⁻¹ (a n), f (Multiplicative.ofAdd g.val) * c (classOf g)
        ∂multiplicativeTamagawaMeasure F)
      (globalIdelicZetaIntegral f) atTop K := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  exact tendstoUniformlyOn_character_normBands (multiplicativeTamagawaMeasure F) classOf
    (fun g ↦ f (Multiplicative.ofAdd g.val)) K hK
    (fun c hc ↦ globalIdelicZetaIntegral_integrable f c (h hc)) a ha haTop
    (tate_continuous_classNormReal.comp continuous_quotient_mk').measurable

-- TODO(paper-gap): In Remark 3.2.2.2 the truncated idele domain is not compact.
-- It contains the closed infinite discrete subgroup of principal ideles.

/-- On a bounded norm band, the ratio to any integrable reference twist and
its exponent derivative are bounded on each compact disk of exponents. -/
private theorem differentiable_integral_twist_normBand {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (q : X → C[F]) (φ : X → ℂ) (χ : U[F]) (r : ℂ)
    (hInt : Integrable (fun x ↦ φ x * ideleClassNormTwist χ r (q x)) μ)
    (hN : Measurable (fun x ↦ classNormℝ (q x))) (a : ℝ) (ha : 1 ≤ a) :
    Differentiable ℂ (fun z ↦ ∫ x in {x | classNormℝ (q x) ∈ Icc a⁻¹ a},
      φ x * ideleClassNormTwist χ z (q x) ∂μ) := by
  let S := {x | classNormℝ (q x) ∈ Icc a⁻¹ a}
  let ν := μ.restrict S
  let l (x : X) := Real.log (classNormℝ (q x))
  let W (x : X) := φ x * ideleClassNormTwist χ r (q x)
  let P (z : ℂ) (t : ℝ) := Complex.exp ((t : ℂ) * (z - r))
  have hl : Measurable l := Real.measurable_log.comp hN
  have hW : Integrable W ν := hInt.integrableOn
  have hEq (z : ℂ) (x : X) : φ x * ideleClassNormTwist χ z (q x) = W x * P z (l x) := by
    have hp := tate_classNormReal_pos (q x)
    change φ x * ((χ (q x) : ℂ) * (classNormℝ (q x) : ℂ) ^ z) =
      (φ x * ((χ (q x) : ℂ) * (classNormℝ (q x) : ℂ) ^ r)) * _
    simp only [P, l, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
      ← Complex.ofReal_log hp.le, mul_assoc, ← Complex.exp_add]
    ring_nf
  simp_rw [hEq]
  intro z
  let D := Metric.closedBall z 1
  let J := Icc (Real.log a⁻¹) (Real.log a)
  have hJ : ∀ᵐ x ∂ν, l x ∈ J := by
    filter_upwards [ae_restrict_mem (μ := μ) (hN (measurableSet_Icc (a := a⁻¹) (b := a)))]
      with x hx
    exact ⟨Real.log_le_log (inv_pos.mpr (zero_lt_one.trans_le ha)) hx.1,
      Real.log_le_log (tate_classNormReal_pos _) hx.2⟩
  let B (p : ℂ × ℝ) := ‖P p.1 p.2‖ + ‖P p.1 p.2 * (p.2 : ℂ)‖
  have hB : Continuous B := by dsimp [B, P]; fun_prop
  obtain ⟨b, hb⟩ := ((isCompact_closedBall z 1).prod (isCompact_Icc (a := Real.log a⁻¹)
    (b := Real.log a))).bddAbove_image hB.continuousOn
  have hBnd {w : ℂ} (hw : w ∈ D) {t : ℝ} (ht : t ∈ J) : B (w, t) ≤ b :=
    hb ⟨(w, t), ⟨hw, ht⟩, rfl⟩
  have hP (w : ℂ) : Measurable (fun x ↦ P w (l x)) :=
    (show Continuous (P w) by dsimp [P]; fun_prop).measurable.comp hl
  have hmeas (w : ℂ) := hW.aestronglyMeasurable.mul (hP w).aestronglyMeasurable
  have hM := hW.norm.mul_const b
  have hzInt : Integrable (fun x ↦ W x * P z (l x)) ν := by
    refine hM.mono' (hmeas z) (hJ.mono fun x hx ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right (norm_nonneg _)).trans
      (hBnd (Metric.mem_closedBall_self zero_le_one) hx)) (norm_nonneg _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w x ↦ W x * P w (l x)) (F' := fun w x ↦ W x * P w (l x) * (l x : ℂ))
    (Metric.closedBall_mem_nhds z zero_lt_one) (Eventually.of_forall hmeas) hzInt
    ((hmeas z).mul (Complex.measurable_ofReal.comp hl).aestronglyMeasurable)
    (hJ.mono fun x hx w hw ↦ ?_) hM (Eventually.of_forall fun x w _ ↦ ?_)).2.differentiableAt
  · rw [mul_assoc, norm_mul]
    exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left (norm_nonneg _)).trans
      (hBnd hw hx)) (norm_nonneg _)
  · simpa [P, mul_assoc] using
      ((((hasDerivAt_id w).sub_const r).const_mul (l x : ℂ)).cexp.const_mul (W x))

/-- Paper: Remark 3.2.2.2, p. 125. Each fixed norm-band truncation of the zeta
integral is holomorphic in the complex norm-twist coordinate.
Deviation: The norm bound controls the variation in the exponent on the band. -/
theorem globalIdelicZetaIntegral_normBand_entire (f : ℬ[F]) (χ : U[F])
    (a : ℝ) (ha : 1 ≤ a) :
    Differentiable ℂ (fun s ↦
      ∫ g in ideleNormBand F a⁻¹ a, f (Multiplicative.ofAdd g.val) *
        ideleClassNormTwist χ s (classOf g) ∂multiplicativeTamagawaMeasure F) := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  have hmem : ideleClassNormTwist χ 2 ∈ rightHalf := by
    change 1 < quasiCharacterAbscissa (G := C[F]) (ideleClassNorm F) _ _ _
    rw [quasiCharacterAbscissa_of_unitary_twist (G := C[F]) _ _ _ _ χ 2 (fun _ ↦ rfl)]
    norm_num
  exact differentiable_integral_twist_normBand (multiplicativeTamagawaMeasure F) classOf
    (fun g ↦ f (Multiplicative.ofAdd g.val)) χ 2
    (globalIdelicZetaIntegral_integrable f _ hmem)
    (tate_continuous_classNormReal.comp continuous_quotient_mk').measurable a ha

/-- The Mellin integral is holomorphic on an open chart domain of absolute
convergence, by locally uniform approximation by entire band integrals. -/
private theorem analyticOnNhd_integral_twist {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (q : X → C[F]) (φ : X → ℂ) (χ : U[F]) (U : Set ℂ) (hU : IsOpen U)
    (hInt : ∀ z ∈ U, Integrable (fun x ↦ φ x * ideleClassNormTwist χ z (q x)) μ)
    (hN : Measurable (fun x ↦ classNormℝ (q x))) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ x, φ x * ideleClassNormTwist χ z (q x) ∂μ) U := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
  · exact fun _ h ↦ h.elim
  have hχ : Continuous (ideleClassNormTwist χ) := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact (continuous_subtype_val.comp (χ.continuous.comp continuous_snd)).mul
      ((Complex.continuous_ofReal.comp (tate_continuous_classNormReal.comp continuous_snd)).cpow
        continuous_fst fun p ↦ Complex.ofReal_mem_slitPlane.mpr (tate_classNormReal_pos p.2))
  let a (n : ℕ) := (n : ℝ) + 1
  have ha (n : ℕ) : 1 ≤ a n := by simp [a]
  have haTop : Tendsto a atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  let H (n : ℕ) (z : ℂ) := ∫ x in {x | classNormℝ (q x) ∈ Icc (a n)⁻¹ (a n)},
    φ x * ideleClassNormTwist χ z (q x) ∂μ
  have hloc : TendstoLocallyUniformlyOn H
      (fun z ↦ ∫ x, φ x * ideleClassNormTwist χ z (q x) ∂μ) atTop U := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).2
    intro K hKU hK
    have h := tendstoUniformlyOn_character_normBands μ q φ _ (hK.image hχ)
      (fun _ ⟨z, hz, he⟩ ↦ he ▸ hInt z (hKU hz)) a ha haTop hN
    exact (h.comp (ideleClassNormTwist χ)).mono (subset_preimage_image _ _)
  apply DifferentiableOn.analyticOnNhd _ hU
  exact hloc.differentiableOn (Eventually.of_forall fun n ↦
    (differentiable_integral_twist_normBand μ q φ χ r (hInt r hr) hN (a n) (ha n)).differentiableOn) hU

/-- Paper: Theorem 3.2.2.1(1), p. 124. The zeta integral is holomorphic on the
right half-plane, expressed in the complex norm-twist coordinates of §3.1. -/
theorem globalIdelicZetaIntegral_analyticOn (f : ℬ[F]) (χ : U[F]) :
    AnalyticOnNhd ℂ (fun s ↦ globalIdelicZetaIntegral f (ideleClassNormTwist χ s)) halfPlane := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  apply analyticOnNhd_integral_twist (multiplicativeTamagawaMeasure F) classOf
    (fun g ↦ f (Multiplicative.ofAdd g.val)) χ _ (isOpen_Ioi.preimage Complex.continuous_re)
    _ (tate_continuous_classNormReal.comp continuous_quotient_mk').measurable
  intro z hz
  apply globalIdelicZetaIntegral_integrable
  change 1 < quasiCharacterAbscissa (G := C[F]) (ideleClassNorm F) _ _ _
  rwa [quasiCharacterAbscissa_of_unitary_twist (G := C[F]) _ _ _ _ χ z (fun _ ↦ rfl)]

/-- Paper: Equation (3.2.2.11), p. 127. On the half-plane of absolute convergence
the zeta integral unfolds over the principal ideles. The theta integrand is integrable
on the idele classes, and its integral is the idelic zeta integral. -/
theorem globalIdelicZetaIntegral_eq_thetaIntegral (f : ℬ[F]) (c : 𝒳[F]) (hc : c ∈ rightHalf) :
    Integrable (fun g : C[F] ↦ adelicTheta f g * c g) (ideleClassTamagawaMeasure F) ∧
      globalIdelicZetaIntegral f c =
        ∫ g : C[F], adelicTheta f g * c g ∂ideleClassTamagawaMeasure F := by
  have hφ := globalIdelicZetaIntegral_integrable f c hc
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  obtain ⟨hG₂, hGlc, -⟩ := ideleGroup_topology F
  obtain ⟨hinj, hP, hPd, -⟩ := ideleGroup_quotient.{_, 0} F
  let : T2Space 𝕀[F] := hG₂
  let : LocallyCompactSpace 𝕀[F] := hGlc
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp hPd
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable Fˣ := Units.val_injective.countable
  let : Countable P := (Set.countable_range (IdeleGroup.unitEmbedding (𝓞 F) F)).to_subtype
  have hspec := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : (multiplicativeTamagawaMeasure F).IsHaarMeasure := hspec.1
  let : (multiplicativeTamagawaMeasure F).Regular := hspec.2.1
  let count : Measure P := Measure.count
  let : count.IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ h ↦ Measure.count_apply_lt_top.mpr h.finite_of_discrete
      open_pos := fun _ _ h ↦ Measure.count_ne_zero h }
  have hW := weilQuotientIntegral_L1 P hP (multiplicativeTamagawaMeasure F) count
    (ideleClassTamagawaMeasure F) (ideleClassTamagawaMeasure_isWeil F) hφ
  let e : Fˣ ≃ P := (MonoidHom.ofInjective hinj).toEquiv
  have he (ξ : Fˣ) : ((e ξ : 𝕀[F]) : 𝔸[F]) = algebraMap F 𝔸[F] (ξ : F) := rfl
  -- Each fibre integral is a theta sum, reindexed by the principal units.
  have hcoset (x : 𝕀[F]) :
      (∫ h : P, f (Multiplicative.ofAdd (x * (h : 𝕀[F])).val) * c (classOf (x * (h : 𝕀[F])))
        ∂count) = adelicTheta f (classOf x) * c (classOf x) := by
    have hcl (h : P) : classOf (x * (h : 𝕀[F])) = classOf x :=
      QuotientGroup.mk_mul_of_mem x h.property
    simp_rw [hcl]
    have hsum : Summable (fun ξ : Fˣ ↦
        ‖f (Multiplicative.ofAdd (x.val * algebraMap F 𝔸[F] (ξ : F)))‖) := by
      simpa only [add_zero] using
        (adelicAverage_summableUniformlyOn f {(x, 0)} isCompact_singleton).summable rfl
    have hsumP : Summable (fun h : P ↦
        ‖f (Multiplicative.ofAdd (x * (h : 𝕀[F])).val) * c (classOf x)‖) := by
      rw [← e.summable_iff]
      simpa only [Function.comp_def, norm_mul, Units.val_mul, he] using
        hsum.mul_right ‖c (classOf x)‖
    rw [integral_countable (integrable_count_iff.mpr hsumP)]
    simp only [count_real_singleton, one_smul]
    rw [tsum_mul_right, adelicTheta_mk, ← e.tsum_eq]
    congr 1
    refine tsum_congr fun ξ ↦ ?_
    rw [Units.val_mul, he, mul_comm]
  have hlca : lcaCosetIntegral P count
      (fun g : 𝕀[F] ↦ f (Multiplicative.ofAdd g.val) * c (classOf g)) =
      fun q : C[F] ↦ adelicTheta f q * c q := by
    funext q
    rw [lcaCosetIntegral, hcoset, QuotientGroup.out_eq']
  rw [hlca] at hW
  exact ⟨hW.2.1, hW.2.2⟩

section TateSplit

local instance globalZetaIdeleClassBorelSpace : BorelSpace C[F] := ⟨rfl⟩

/-- The absolute value of the theta integrand depends on the exponent only through
its real part. -/
private theorem tate_norm_theta_twist (f : ℬ[F]) (χ : U[F]) (s : ℂ) (g : C[F]) :
    ‖adelicTheta f g * ideleClassNormTwist χ s g‖ =
      ‖adelicTheta f g‖ * classNormℝ g ^ s.re := by
  change ‖adelicTheta f g * ((χ g : ℂ) * (classNormℝ g : ℂ) ^ s)‖ = _
  rw [norm_mul, norm_mul, Circle.norm_coe, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]

/-- Paper: Equation (3.1.1.2), p. 119. A norm twist of a unitary character lies
in the absolute convergence half-plane when the real exponent is greater than one. -/
private theorem tate_twist_mem_rightHalf (χ : U[F]) (s : ℂ) (hs : 1 < s.re) :
    ideleClassNormTwist χ s ∈
      (↑(relativeRightHalfPlane (G := C[F]) (ideleClassNorm F) (isProperMap_ideleClassNorm F)
        (ideleClassNorm_ne_one (F := F)) 1) : Set (HeckeCharacter (𝓞 F) F)) := by
  change 1 < quasiCharacterAbscissa (G := C[F]) (ideleClassNorm F) _ _ (ideleClassNormTwist χ s)
  rw [quasiCharacterAbscissa_of_unitary_twist (G := C[F]) _ _ _ _ χ s (fun _ ↦ rfl)]
  exact hs

/-- Absolute convergence of the theta integral at any real exponent greater than one
provides an integrable majorant on the large-norm domain. -/
private theorem tate_integrableOn_norm_theta_twist (f : ℬ[F]) (r : ℝ) (hr : 1 < r)
    (S : Set C[F]) :
    IntegrableOn (fun g ↦ ‖adelicTheta f g‖ * classNormℝ g ^ r) S
      (ideleClassTamagawaMeasure F) := by
  let c := ideleClassNormTwist (1 : U[F]) (r : ℂ)
  have hc := tate_twist_mem_rightHalf (1 : U[F]) (r : ℂ) (by simpa using hr)
  have h := (globalIdelicZetaIntegral_eq_thetaIntegral f c hc).1.norm.integrableOn (s := S)
  simpa only [c, tate_norm_theta_twist, Complex.ofReal_re] using h

/-- Paper: Equation (3.2.2.3), p. 124. The theta Mellin integral restricted to
a specified set of idele classes. -/
private def tateThetaMellinOn (f : ℬ[F]) (χ : U[F]) (S : Set C[F]) (s : ℂ) : ℂ :=
  ∫ g in S, adelicTheta f g * ideleClassNormTwist χ s g ∂ideleClassTamagawaMeasure F

/-- The large-norm theta integral is entire. On a neighborhood of a given exponent,
one larger real exponent dominates both the integrand and its derivative. -/
private theorem tate_differentiable_thetaMellinOn (f : ℬ[F]) (χ : U[F]) {S : Set C[F]}
    (hS : MeasurableSet S) (hNorm : ∀ g ∈ S, 1 ≤ classNormℝ g) :
    Differentiable ℂ (tateThetaMellinOn f χ S) := by
  intro s
  let μ := (ideleClassTamagawaMeasure F).restrict S
  let W (z : ℂ) (g : C[F]) := adelicTheta f g * ideleClassNormTwist χ z g
  let D (z : ℂ) (g : C[F]) := W z g * Complex.log (classNormℝ g : ℂ)
  let r := max (s.re + 2) 2
  let V := {z : ℂ | z.re < s.re + 1}
  have hr : 1 < r := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_right _ _)
  have hV : V ∈ 𝓝 s :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by
      change s.re < s.re + 1
      linarith)
  have hW (z : ℂ) : Continuous (W z) :=
    (adelicTheta f).continuous.mul (ideleClassNormTwist χ z).continuous
  have hμ := ae_restrict_mem (μ := ideleClassTamagawaMeasure F) hS
  have hMajorant := tate_integrableOn_norm_theta_twist f r hr S
  have hsInt : Integrable (W s) μ := by
    refine hMajorant.mono' (hW s).aestronglyMeasurable (hμ.mono fun g hg ↦ ?_)
    change ‖adelicTheta f g * ideleClassNormTwist χ s g‖ ≤ _
    rw [tate_norm_theta_twist]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hNorm g hg) ?_)
      (norm_nonneg _)
    exact (by linarith : s.re ≤ s.re + 2).trans (le_max_left _ _)
  have hDMeas : AEStronglyMeasurable (D s) μ :=
    (hW s).aestronglyMeasurable.mul
      (Complex.measurable_log.comp
        (Complex.continuous_ofReal.comp tate_continuous_classNormReal).measurable).aestronglyMeasurable
  have hDBound : ∀ᵐ g ∂μ, ∀ z ∈ V, ‖D z g‖ ≤ ‖adelicTheta f g‖ * classNormℝ g ^ r := by
    refine hμ.mono fun g hg z hz ↦ ?_
    have hg₁ := hNorm g hg
    have hgPos := zero_lt_one.trans_le hg₁
    change z.re < s.re + 1 at hz
    change ‖(adelicTheta f g * ideleClassNormTwist χ z g) * _‖ ≤ _
    rw [norm_mul, tate_norm_theta_twist, ← Complex.ofReal_log hgPos.le,
      Complex.norm_of_nonneg (Real.log_nonneg hg₁)]
    calc
      _ ≤ (‖adelicTheta f g‖ * classNormℝ g ^ z.re) * classNormℝ g :=
        mul_le_mul_of_nonneg_left (Real.log_le_self hgPos.le) (by positivity)
      _ = ‖adelicTheta f g‖ * classNormℝ g ^ (z.re + 1) := by
        rw [Real.rpow_add hgPos, Real.rpow_one, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hg₁
          ((by linarith : z.re + 1 ≤ s.re + 2).trans (le_max_left _ _))) (norm_nonneg _)
  have hDiff : ∀ᵐ g ∂μ, ∀ z ∈ V, HasDerivAt (fun w ↦ W w g) (D z g) z := by
    refine Eventually.of_forall fun g z _ ↦ ?_
    have hg : (classNormℝ g : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    change HasDerivAt (fun w : ℂ ↦ adelicTheta f g * ((χ g : ℂ) * (classNormℝ g : ℂ) ^ w))
      ((adelicTheta f g * ((χ g : ℂ) * (classNormℝ g : ℂ) ^ z)) *
        Complex.log (classNormℝ g : ℂ)) z
    simpa only [id_eq, mul_assoc, mul_one] using
      (((hasDerivAt_id z).const_cpow (Or.inl hg)).const_mul (χ g : ℂ)).const_mul (adelicTheta f g)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV
    (Eventually.of_forall fun z ↦ (hW z).aestronglyMeasurable) hsInt hDMeas hDBound hMajorant
    hDiff).2.differentiableAt

local notation "largeNorm[" F "]" => ((classNormℝ : C[F] → ℝ) ⁻¹' Ici 1)
local notation "strictLargeNorm[" F "]" => ((classNormℝ : C[F] → ℝ) ⁻¹' Ioi 1)

local notation "smallNorm[" F "]" => ((classNormℝ : C[F] → ℝ) ⁻¹' Iio 1)

/-- The small-norm Mellin integral, with the scalar in logarithmic coordinates specified. -/
private theorem tate_integral_classNorm_cpow_smallNorm_of_map (c : ℝ≥0)
    (hc : (ideleClassTamagawaMeasure F).map (fun g ↦ Real.log (classNormℝ g)) = c • volume)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun g ↦ (classNormℝ g : ℂ) ^ s) smallNorm[F] (ideleClassTamagawaMeasure F) ∧
      (∫ g in smallNorm[F], (classNormℝ g : ℂ) ^ s ∂ideleClassTamagawaMeasure F) =
        (c : ℝ) / s := by
  let μ := ideleClassTamagawaMeasure F
  let l (g : C[F]) := Real.log (classNormℝ g)
  let E (t : ℝ) := Complex.exp (s * (t : ℂ))
  have hl : Continuous l :=
    tate_continuous_classNormReal.log fun g ↦ (tate_classNormReal_pos g).ne'
  have hSmall : l ⁻¹' Iio 0 = smallNorm[F] := by
    ext g
    exact Real.log_neg_iff (tate_classNormReal_pos g)
  have hmap : (μ.restrict smallNorm[F]).map l = c • (volume.restrict (Iio 0)) := by
    rw [← hSmall, ← Measure.restrict_map hl.measurable measurableSet_Iio, hc, Measure.restrict_smul]
  have hE : Continuous E := Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hInt : Integrable E ((μ.restrict smallNorm[F]).map l) := by
    rw [hmap]
    exact ((integrableOn_exp_mul_complex_Iic hs 0).mono_set Iio_subset_Iic_self).smul_measure
      ENNReal.coe_ne_top
  have hPow (g : C[F]) : E (l g) = (classNormℝ g : ℂ) ^ s := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (tate_classNormReal_pos g).ne'),
      ← Complex.ofReal_log (tate_classNormReal_pos g).le, mul_comm]
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, hPow, IntegrableOn, μ] using
      (integrable_map_measure hE.aestronglyMeasurable hl.measurable.aemeasurable).mp hInt
  · simp_rw [← hPow]
    rw [← integral_map hl.measurable.aemeasurable hE.aestronglyMeasurable, hmap,
      integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
      ← integral_Iic_eq_integral_Iio]
    simp only [E, integral_exp_mul_complex_Iic hs, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      div_eq_mul_inv, one_mul]

/-- On the norm-below-one domain a pure power has Mellin integral equal to a
constant divided by the exponent. -/
private theorem tate_integral_classNorm_cpow_smallNorm :
    ∃ c : ℝ≥0, ∀ s : ℂ, 0 < s.re →
      IntegrableOn (fun g ↦ (classNormℝ g : ℂ) ^ s) smallNorm[F] (ideleClassTamagawaMeasure F) ∧
      (∫ g in smallNorm[F], (classNormℝ g : ℂ) ^ s ∂ideleClassTamagawaMeasure F) =
        (c : ℝ) / s := by
  obtain ⟨c, hc⟩ := tate_exists_map_logClassNorm_eq_smul_volume (F := F)
  exact ⟨c, tate_integral_classNorm_cpow_smallNorm_of_map c hc⟩

/-- A nonzero residue in the small-norm Mellin integral forces the twist at its pole
to be the trivial character. -/
private theorem tate_integral_twist_smallNorm_pole (χ : U[F]) :
    ∃ p c : ℂ, p.re = 0 ∧ (c = 0 ∨ ideleClassNormTwist χ p = 1) ∧ ∀ s : ℂ, 0 < s.re →
      IntegrableOn (ideleClassNormTwist χ s) smallNorm[F] (ideleClassTamagawaMeasure F) ∧
      (∫ g in smallNorm[F], ideleClassNormTwist χ s g ∂ideleClassTamagawaMeasure F) =
        c / (s - p) := by
  obtain ⟨c, hc⟩ := tate_integral_classNorm_cpow_smallNorm (F := F)
  let μ := ideleClassTamagawaMeasure F
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil (F := F)).1
  by_cases hχ : ∃ g : C[F], ideleClassNorm F g = 1 ∧ χ g ≠ 1
  · obtain ⟨g, hg, hne⟩ := hχ
    refine ⟨0, 0, Complex.zero_re, Or.inl rfl, fun s hs ↦ ?_⟩
    obtain ⟨hPow, -⟩ := hc s hs
    let W : C[F] → ℂ := ideleClassNormTwist χ s
    have hInt : IntegrableOn W smallNorm[F] μ := by
      refine hPow.norm.mono' (ideleClassNormTwist χ s).continuous.aestronglyMeasurable
        (Eventually.of_forall fun x ↦ ?_)
      change ‖(χ x : ℂ) * (classNormℝ x : ℂ) ^ s‖ ≤ ‖(classNormℝ x : ℂ) ^ s‖
      rw [norm_mul, Circle.norm_coe, one_mul]
    refine ⟨hInt, ?_⟩
    have hPre : (fun x : C[F] ↦ g * x) ⁻¹' smallNorm[F] = smallNorm[F] := by
      ext x
      change classNormℝ (g * x) < 1 ↔ classNormℝ x < 1
      dsimp only
      rw [map_mul, hg, one_mul]
    have hInv := (measurePreserving_mul_left μ g).setIntegral_preimage_emb
      (Homeomorph.mulLeft g).toMeasurableEquiv.measurableEmbedding W smallNorm[F]
    rw [hPre] at hInv
    have hWg : W g = (χ g : ℂ) := by
      change (χ g : ℂ) * (classNormℝ g : ℂ) ^ s = _
      simp [hg]
    change (∫ x in smallNorm[F], W (g * x) ∂μ) = (∫ x in smallNorm[F], W x ∂μ) at hInv
    have hMul (x : C[F]) : W (g * x) = (χ g : ℂ) * W x := by
      rw [← hWg]
      exact (ideleClassNormTwist χ s).map_mul g x
    simp_rw [hMul] at hInv
    rw [integral_const_mul, ← sub_eq_zero, ← sub_one_mul] at hInv
    have : (χ g : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ hne (Subtype.ext h)
    rw [zero_div]
    exact (mul_eq_zero.mp hInv).resolve_left this
  · have hTriv (g : C[F]) (hg : ideleClassNorm F g = 1) : χ g = 1 := by
      by_contra h
      exact hχ ⟨g, hg, h⟩
    let q : IdeleGroup (𝓞 F) F →ₜ* C[F] := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
    let σ : ℝ≥0ˣ →ₜ* C[F] := q.comp
      ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
    have hσ : RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
    let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    obtain ⟨w, hw, -⟩ := existsUnique_complexPower (j.comp (χ.comp σ))
    have hParam (t : ℝ≥0ˣ) : (χ (σ t) : ℂ) = ((t.val : ℝ) : ℂ) ^ w := hw t
    have hwRe : w.re = 0 := by
      let t := Units.mk0 (2 : ℝ≥0) (by norm_num)
      have h := congrArg norm (hParam t)
      rw [Circle.norm_coe, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num [t])] at h
      change 1 = (2 : ℝ) ^ w.re at h
      rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_zero] at h
      exact (mul_eq_zero.mp (Real.exp_injective h.symm)).resolve_left
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    have hTwist (s : ℂ) (g : C[F]) : ideleClassNormTwist χ s g = (classNormℝ g : ℂ) ^ (s + w) := by
      have hn : ideleClassNorm F (g * (σ (ideleClassNorm F g))⁻¹) = 1 := by
        rw [map_mul, map_inv, hσ _, mul_inv_cancel]
      have h := hTriv _ hn
      rw [map_mul, map_inv, mul_inv_eq_one] at h
      change (χ g : ℂ) * (classNormℝ g : ℂ) ^ s = _
      rw [h, hParam, add_comm s w, Complex.cpow_add _ _
        (Complex.ofReal_ne_zero.mpr (tate_classNormReal_pos g).ne')]
    refine ⟨-w, (c : ℝ), by simpa using hwRe, Or.inr ?_, fun s hs ↦ ?_⟩
    · ext1 g
      change ideleClassNormTwist χ (-w) g = 1
      simp [hTwist]
    have hs' : 0 < (s + w).re := by simpa only [Complex.add_re, hwRe, add_zero] using hs
    rw [show (ideleClassNormTwist χ s : C[F] → ℂ) = _ from funext (hTwist s), sub_neg_eq_add]
    exact hc (s + w) hs'

/-- The Mellin transform of the cut-off quasi-character on the norm-below-one
domain is a simple polar term. Integration over the norm-one subgroup kills a
nontrivial restriction of the character. For a norm character, the logarithmic
norm coordinate reduces the integral to an exponential integral on `(-∞, 0)`. -/
private theorem tate_integral_twist_smallNorm (χ : U[F]) :
    ∃ p c : ℂ, p.re = 0 ∧ ∀ s : ℂ, 0 < s.re →
      IntegrableOn (ideleClassNormTwist χ s) smallNorm[F] (ideleClassTamagawaMeasure F) ∧
      (∫ g in smallNorm[F], ideleClassNormTwist χ s g ∂ideleClassTamagawaMeasure F) =
        c / (s - p) := by
  obtain ⟨p, c, hp, _, h⟩ := tate_integral_twist_smallNorm_pole χ
  exact ⟨p, c, hp, h⟩

/-- Multiplication by the inverse class norm subtracts one from the twist exponent. -/
private theorem tate_inv_norm_mul_twist (χ : U[F]) (s : ℂ) (g : C[F]) :
    (classNormℝ g : ℂ)⁻¹ * ideleClassNormTwist χ s g = ideleClassNormTwist χ (s - 1) g := by
  have hn : (classNormℝ g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  change _ * ((χ g : ℂ) * (classNormℝ g : ℂ) ^ s) =
    (χ g : ℂ) * (classNormℝ g : ℂ) ^ (s - 1)
  rw [Complex.cpow_sub _ _ hn, Complex.cpow_one, div_eq_mul_inv]
  ring

/-- Evaluating the reflected twist on the inverse class supplies the inverse norm
factor in adelic Riemann–Roch. -/
private theorem tate_twist_inv_apply (χ : U[F]) (s : ℂ) (g : C[F]) :
    ideleClassNormTwist χ⁻¹ (1 - s) g⁻¹ = ideleClassNormTwist χ (s - 1) g := by
  change (((χ⁻¹) g⁻¹ : Circle) : ℂ) * (classNormℝ g⁻¹ : ℂ) ^ (1 - s) =
    (χ g : ℂ) * (classNormℝ g : ℂ) ^ (s - 1)
  have hχ : (χ⁻¹) g⁻¹ = χ g := by
    rw [map_inv]
    change (χ g)⁻¹⁻¹ = χ g
    exact inv_inv _
  rw [hχ]
  simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (NNReal.coe_nonneg _),
    ← Complex.cpow_neg, neg_sub]

/-- The two large-norm integrals form the entire part of the chart.
The coefficients of the remaining two simple fractions come from the small-norm integral. -/
private theorem tate_chart_polar_model (f : ℬ[F]) (χ : U[F]) (p c : ℂ) (hp : p.re = 0)
    (hpol : ∀ s : ℂ, 0 < s.re →
      IntegrableOn (ideleClassNormTwist χ s) smallNorm[F] (ideleClassTamagawaMeasure F) ∧
      (∫ g in smallNorm[F], ideleClassNormTwist χ s g ∂ideleClassTamagawaMeasure F) = c / (s - p)) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧
      let M (s : ℂ) := E s + (adeleSchwartzFourier f zeroAdele * c) / (s - (1 + p)) +
        (-(f zeroAdele * c)) / (s - p)
      MeromorphicOn M univ ∧ ∀ s : ℂ, 1 < s.re →
        toMeromorphicNFOn M univ s = globalIdelicZetaIntegral f (ideleClassNormTwist χ s) := by
  let μ := ideleClassTamagawaMeasure F
  let f₀ := f (Multiplicative.ofAdd (0 : 𝔸[F]))
  let fFourier := adeleSchwartzFourier f
  let fFourier₀ := fFourier (Multiplicative.ofAdd (0 : 𝔸[F]))
  let A := fFourier₀ * c
  let B := -(f₀ * c)
  let Z (s : ℂ) := globalIdelicZetaIntegral f (ideleClassNormTwist χ s)
  let M (s : ℂ) :=
    tateThetaMellinOn f χ largeNorm[F] s +
      tateThetaMellinOn fFourier χ⁻¹ strictLargeNorm[F] (1 - s) +
      A / (s - (1 + p)) + B / (s - p)
  have hBig : MeasurableSet largeNorm[F] :=
    (tate_continuous_classNormReal (F := F)).measurable measurableSet_Ici
  have hStrictBig : MeasurableSet strictLargeNorm[F] :=
    (tate_continuous_classNormReal (F := F)).measurable measurableSet_Ioi
  have hSmall : MeasurableSet smallNorm[F] :=
    (tate_continuous_classNormReal (F := F)).measurable measurableSet_Iio
  have hComp : (largeNorm[F])ᶜ = smallNorm[F] := by
    ext g
    exact not_le
  have hInv : (fun g : C[F] ↦ g⁻¹) ⁻¹' strictLargeNorm[F] = smallNorm[F] := by
    ext g
    change 1 < classNormℝ g⁻¹ ↔ classNormℝ g < 1
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
    exact one_lt_inv₀ (NNReal.coe_pos.mpr (Units.zero_lt _))
  have hWeil := ideleClassTamagawaMeasure_isWeil (F := F)
  let : μ.IsHaarMeasure := hWeil.1
  let : μ.Regular := hWeil.2.1
  let : T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  -- On the half-plane of convergence, split at norm one and apply Riemann–Roch below it.
  have hAgree (s : ℂ) (hs : 1 < s.re) : Z s = M s := by
    let W (z : ℂ) (g : C[F]) := ideleClassNormTwist χ z g
    let D (g : C[F]) := adelicTheta fFourier g⁻¹ * W (s - 1) g
    have hc := tate_twist_mem_rightHalf χ s hs
    obtain ⟨hInt, hWhole⟩ := globalIdelicZetaIntegral_eq_thetaIntegral f (ideleClassNormTwist χ s) hc
    have hRiemann (g : C[F]) :
        adelicTheta f g * W s g = D g + fFourier₀ * W (s - 1) g - f₀ * W s g := by
      change adelicTheta f g * ideleClassNormTwist χ s g =
        adelicTheta fFourier g⁻¹ * ideleClassNormTwist χ (s - 1) g +
          fFourier₀ * ideleClassNormTwist χ (s - 1) g - f₀ * ideleClassNormTwist χ s g
      rw [← tate_inv_norm_mul_twist, adelicTheta_riemannRoch]
      simp only [Complex.real_smul, Complex.ofReal_inv]
      ring
    have hs' : 0 < (s - 1).re := by simpa only [Complex.sub_re, Complex.one_re, sub_pos] using hs
    obtain ⟨hInt₀, hPolar₀⟩ := hpol s (zero_lt_one.trans hs)
    obtain ⟨hInt₁, hPolar₁⟩ := hpol (s - 1) hs'
    have hD : IntegrableOn D smallNorm[F] μ := by
      refine (integrableOn_congr_fun (g := D) (fun g _ ↦ ?_) hSmall).mp
        ((hInt.integrableOn.add (hInt₀.const_mul f₀)).sub (hInt₁.const_mul fFourier₀))
      change adelicTheta f g * W s g + f₀ * W s g - fFourier₀ * W (s - 1) g = D g
      rw [hRiemann]
      ring
    have hInvInt : (∫ g in smallNorm[F], D g ∂μ) =
        tateThetaMellinOn fFourier χ⁻¹ strictLargeNorm[F] (1 - s) := by
      have h := (Measure.measurePreserving_inv μ).setIntegral_preimage_emb
        (Homeomorph.inv (C[F])).toMeasurableEquiv.measurableEmbedding
        (fun g ↦ adelicTheta fFourier g * ideleClassNormTwist χ⁻¹ (1 - s) g) strictLargeNorm[F]
      rw [hInv] at h
      refine Eq.trans (setIntegral_congr_fun hSmall fun g _ ↦ ?_) h
      dsimp [D, W]
      rw [tate_twist_inv_apply]
    calc
      Z s = tateThetaMellinOn f χ largeNorm[F] s +
          (∫ g in smallNorm[F], adelicTheta f g * W s g ∂μ) := by
        change globalIdelicZetaIntegral f (ideleClassNormTwist χ s) = _
        rw [hWhole, tateThetaMellinOn, ← hComp]
        exact (integral_add_compl hBig hInt).symm
      _ = M s := by
        simp_rw [hRiemann]
        have hAdd := integral_add hD (hInt₁.const_mul fFourier₀)
        have hSub := integral_sub (hD.add (hInt₁.const_mul fFourier₀)) (hInt₀.const_mul f₀)
        simp only [Pi.add_apply] at hSub
        rw [hSub, hAdd, integral_const_mul, integral_const_mul, hInvInt, hPolar₁, hPolar₀]
        dsimp only [M, W, A, B]
        rw [show s - 1 - p = s - (1 + p) by ring]
        ring
  have h₁ := tate_differentiable_thetaMellinOn f χ hBig (fun _ hg ↦ hg)
  have h₂ := tate_differentiable_thetaMellinOn fFourier χ⁻¹ hStrictBig (fun _ hg ↦ le_of_lt hg)
  have hG₁ := h₁.analyticAt
  have hG₂ (s : ℂ) :
      AnalyticAt ℂ (fun z ↦ tateThetaMellinOn fFourier χ⁻¹ strictLargeNorm[F] (1 - z)) s :=
    (h₂.analyticAt (1 - s)).comp (by fun_prop)
  have hDen₁ (s : ℂ) : AnalyticAt ℂ (fun z : ℂ ↦ z - (1 + p)) s := by fun_prop
  have hDen₀ (s : ℂ) : AnalyticAt ℂ (fun z : ℂ ↦ z - p) s := by fun_prop
  have hM : MeromorphicOn M univ := by
    intro s _
    exact (((hG₁ s).meromorphicAt.add (hG₂ s).meromorphicAt).add
      (analyticAt_const.meromorphicAt.div (hDen₁ s).meromorphicAt)).add
      (analyticAt_const.meromorphicAt.div (hDen₀ s).meromorphicAt)
  -- Both poles lie on or left of the line `Re s = 1`.
  have hMan (s : ℂ) (hs : 1 < s.re) : AnalyticAt ℂ M s := by
    have hs₁ : s ≠ 1 + p := fun h ↦ by
      have h' := congrArg Complex.re h
      rw [Complex.add_re, Complex.one_re, hp, add_zero] at h'
      linarith
    have hs₀ : s ≠ p := fun h ↦ by
      have h' := congrArg Complex.re h
      rw [hp] at h'
      linarith
    exact (((hG₁ s).add (hG₂ s)).add
      (analyticAt_const.div (hDen₁ s) (sub_ne_zero.mpr hs₁))).add
      (analyticAt_const.div (hDen₀ s) (sub_ne_zero.mpr hs₀))
  let E (s : ℂ) := tateThetaMellinOn f χ largeNorm[F] s +
    tateThetaMellinOn fFourier χ⁻¹ strictLargeNorm[F] (1 - s)
  refine ⟨E, h₁.add (h₂.comp (differentiable_const 1 |>.sub differentiable_id)), hM, fun s hs ↦ ?_⟩
  change toMeromorphicNFOn M univ s = _
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ s),
    toMeromorphicNFAt_eq_self.mpr (hMan s hs).meromorphicNFAt]
  exact (hAgree s hs).symm

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. In each complex norm-twist chart the zeta
integral on the half-plane `Re s > 1` extends to a meromorphic function in normal form on the
whole plane. The proof normalizes the sum of the two large-norm theta integrals of the test
function and its Fourier transform and the two simple polar terms from adelic Riemann–Roch. -/
theorem globalIdelicZetaIntegral_exists_chartContinuation (f : ℬ[F]) (χ : U[F]) :
    ∃ G : ℂ → ℂ, MeromorphicNFOn G univ ∧
      ∀ s : ℂ, 1 < s.re → G s = globalIdelicZetaIntegral f (ideleClassNormTwist χ s) := by
  obtain ⟨p, c, hp, hpol⟩ := tate_integral_twist_smallNorm χ
  obtain ⟨E, _, _, hEq⟩ := tate_chart_polar_model f χ p c hp hpol
  exact ⟨_, meromorphicNFOn_toMeromorphicNFOn _ _, hEq⟩

end TateSplit

/-- Paper: §3.1.1, p. 119. If two norm-twist charts pass through the same
quasi-character, then adding the same increment to both coordinates gives the same
quasi-character again. -/
theorem ideleClassNormTwist_add_of_eq {χ χ' : U[F]} {s s' : ℂ}
    (h : ideleClassNormTwist χ s = ideleClassNormTwist χ' s') (z : ℂ) :
    ideleClassNormTwist χ (s + z) = ideleClassNormTwist χ' (s' + z) := by
  ext1 g
  have hg := DFunLike.congr_fun h g
  have hn : (classNormℝ g : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  change (χ g : ℂ) * (classNormℝ g : ℂ) ^ s = (χ' g : ℂ) * (classNormℝ g : ℂ) ^ s' at hg
  change (χ g : ℂ) * (classNormℝ g : ℂ) ^ (s + z) = (χ' g : ℂ) * (classNormℝ g : ℂ) ^ (s' + z)
  rw [Complex.cpow_add _ _ hn, Complex.cpow_add _ _ hn, ← mul_assoc, ← mul_assoc, hg]

/-- Paper: Equation (3.1.1.2), p. 119. The abscissa of a norm twist of a unitary
character is the real part of the exponent. -/
theorem quasiCharacterAbscissa_ideleClassNormTwist (χ : U[F]) (s : ℂ) :
    quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) (ideleClassNormTwist χ s) = s.re :=
  quasiCharacterAbscissa_of_unitary_twist (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) (ideleClassNormTwist χ s) χ s (fun _ ↦ rfl)

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. Chart continuations of the zeta integral
agree wherever two norm-twist charts pass through the same quasi-character. -/
theorem globalIdelicZetaIntegral_chartContinuation_eq (f : ℬ[F]) {χ χ' : U[F]}
    {G G' : ℂ → ℂ} (hG : MeromorphicNFOn G univ) (hG' : MeromorphicNFOn G' univ)
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = globalIdelicZetaIntegral f (ideleClassNormTwist χ s))
    (hG'eq : ∀ s : ℂ, 1 < s.re → G' s = globalIdelicZetaIntegral f (ideleClassNormTwist χ' s))
    {s s' : ℂ} (h : ideleClassNormTwist χ s = ideleClassNormTwist χ' s') : G s = G' s' := by
  let d := s' - s
  let H := fun z ↦ G' (z + d)
  have hRe : s.re = s'.re := by
    rw [← quasiCharacterAbscissa_ideleClassNormTwist χ s, h,
      quasiCharacterAbscissa_ideleClassNormTwist]
  have htw (z : ℂ) : ideleClassNormTwist χ' (z + d) = ideleClassNormTwist χ z := by
    have := (ideleClassNormTwist_add_of_eq h (z - s)).symm
    rwa [add_sub_cancel, show s' + (z - s) = z + d by ring] at this
  have hH : MeromorphicNFOn H univ := fun z _ ↦
    (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt (f := G')).mpr (hG' (mem_univ _))
  have hAgree (z : ℂ) (hz : 1 < z.re) : G z = H z := by
    have hzd : 1 < (z + d).re := by
      simpa only [d, Complex.add_re, Complex.sub_re, hRe, sub_self, add_zero] using hz
    rw [hGeq z hz]
    change _ = G' (z + d)
    rw [hG'eq _ hzd, htw]
  have hAtTwo : meromorphicOrderAt (G - H) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦ sub_eq_zero.mpr (hAgree z hz)
  have hOrd := (hG.meromorphicOn.sub hH.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) hAtTwo
  have hNear : G =ᶠ[𝓝[≠] s] H :=
    (meromorphicOrderAt_eq_top_iff.mp hOrd).mono fun _ h ↦ sub_eq_zero.mp h
  have hs : G s = H s :=
    (((hG (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hH (mem_univ s))).mp
      hNear).eq_of_nhds
  rw [hs]
  change G' (s + (s' - s)) = G' s'
  rw [add_sub_cancel]

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. The zeta integral admits a
meromorphic continuation, in normal form on every complex norm-twist chart. -/
theorem globalIdelicZetaIntegral_exists_continuation (f : ℬ[F]) :
    ∃ Z : 𝒳[F] → ℂ, (∀ χ : U[F],
      MeromorphicNFOn (fun s ↦ Z (ideleClassNormTwist χ s)) univ) ∧
      EqOn Z (globalIdelicZetaIntegral f) rightHalf := by
  classical
  choose G hGNF hGeq using globalIdelicZetaIntegral_exists_chartContinuation f
  let Z : 𝒳[F] → ℂ := fun c ↦
    if h : ∃ p : U[F] × ℂ, ideleClassNormTwist p.1 p.2 = c then G h.choose.1 h.choose.2
    else globalIdelicZetaIntegral f c
  have hZ (χ : U[F]) (s : ℂ) : Z (ideleClassNormTwist χ s) = G χ s := by
    have h : ∃ p : U[F] × ℂ, ideleClassNormTwist p.1 p.2 = ideleClassNormTwist χ s :=
      ⟨(χ, s), rfl⟩
    simp only [Z, dite_eq_left h]
    exact globalIdelicZetaIntegral_chartContinuation_eq f (hGNF _) (hGNF χ) (hGeq _) (hGeq χ)
      h.choose_spec
  refine ⟨Z, fun χ ↦ ?_, fun c hc ↦ ?_⟩
  · simpa only [hZ] using hGNF χ
  · by_cases h : ∃ p : U[F] × ℂ, ideleClassNormTwist p.1 p.2 = c
    · obtain ⟨⟨χ, s⟩, rfl⟩ := h
      have hs : 1 < s.re := by
        have hc' : 1 < quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
            (ideleClassNorm_ne_one (F := F)) (ideleClassNormTwist χ s) := hc
        rwa [quasiCharacterAbscissa_ideleClassNormTwist] at hc'
      exact (hZ χ s).trans (hGeq χ s hs)
    · simp only [Z, dite_eq_right h]

/-- Paper: Definition 3.2.2.5, p. 128. The global idelic Z-function is the
meromorphic continuation of the zeta integral.
Deviation: This definition is placed next to its existence theorem so that the
remaining statements can use it. At poles we use Mathlib's meromorphic normal form. -/
def globalIdelicZFunction (f : ℬ[F]) : 𝒳[F] → ℂ :=
  (globalIdelicZetaIntegral_exists_continuation f).choose

/-- Paper: Definition 3.2.2.5, p. 128. On the half-plane of convergence the
global idelic Z-function agrees with its defining integral. -/
theorem globalIdelicZFunction_eq_integral (f : ℬ[F]) :
    EqOn (globalIdelicZFunction f) (globalIdelicZetaIntegral f) rightHalf :=
  (globalIdelicZetaIntegral_exists_continuation f).choose_spec.2

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. In every norm-twist coordinate
the global Z-function is in meromorphic normal form. -/
theorem globalIdelicZFunction_meromorphic (f : ℬ[F]) (χ : U[F]) :
    MeromorphicNFOn (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)) univ :=
  (globalIdelicZetaIntegral_exists_continuation f).choose_spec.1 χ

local notation "archimedeanZeta" =>
  fun (f : SchwartzBruhat (Multiplicative (SAdeleRing F ∅))) (c : 𝒳[F]) ↦
    ∫ g : (SAdeleRing F ∅)ˣ, f (Multiplicative.ofAdd (Units.val g)) *
      c (classOf (sIdeleInsertion F ∅ g)) ∂sMultiplicativeTamagawaMeasure F ∅

local notation "archimedeanFourier" =>
  fun (f : SchwartzBruhat (Multiplicative (SAdeleRing F ∅))) (y : SAdeleRing F ∅) ↦
    @tamagawaFourier _ _ (instMeasurableSpaceSAdeleRing (F := F) (S := ∅))
      (sAdditiveTamagawaMeasure F ∅) (sAdeleStandardCharacter F ∅)
      (fun x ↦ f (Multiplicative.ofAdd x)) y

/-- Taking the inverse character inverts its restriction to the completion. -/
private theorem infinitePlaceRestriction_inverse (χ : U[F]) (v : InfinitePlace F)
    (x : v.Completionˣ) :
    infinitePlaceRestriction F v (ideleClassNormTwist χ⁻¹ 0) x =
      (infinitePlaceRestriction F v (ideleClassNormTwist χ 0) x)⁻¹ := by
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v x
  change ((χ⁻¹ g : Circle) : ℂ) * _ ^ (0 : ℂ) = ((χ g : ℂ) * _ ^ (0 : ℂ))⁻¹
  simp only [Complex.cpow_zero, mul_one]
  rfl

/-- Inversion negates the real place's radial exponent and preserves its sign parity. -/
private theorem realHecke_inverse_parameters (χ : U[F]) (v : InfinitePlace F)
    (hv : v.IsReal) :
    (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose =
      (-(realHeckeCharacter_parameters χ v hv).exists.choose.1,
        (realHeckeCharacter_parameters χ v hv).exists.choose.2) := by
  have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec
  apply (realHeckeCharacter_parameters χ⁻¹ v hv).unique
    (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose_spec
  refine ⟨by simpa using ha.1, fun x ↦ ?_⟩
  dsimp only
  rw [infinitePlaceRestriction_inverse, ha.2 x, mul_inv, Complex.cpow_neg]
  congr 1
  rw [← inv_pow]
  split <;> simp

/-- Inversion negates both the radial exponent and the angular weight at a complex place. -/
private theorem complexHecke_inverse_parameters (χ : U[F]) (v : InfinitePlace F)
    (hv : v.IsComplex) :
    (complexHeckeCharacter_parameters χ⁻¹ v hv).exists.choose =
      (-(complexHeckeCharacter_parameters χ v hv).exists.choose.1,
        -(complexHeckeCharacter_parameters χ v hv).exists.choose.2) := by
  have ha := (complexHeckeCharacter_parameters χ v hv).exists.choose_spec
  apply (complexHeckeCharacter_parameters χ⁻¹ v hv).unique
    (complexHeckeCharacter_parameters χ⁻¹ v hv).exists.choose_spec
  refine ⟨by simpa using ha.1, fun x ↦ ?_⟩
  dsimp only
  rw [infinitePlaceRestriction_inverse, ha.2 x, mul_inv, Complex.cpow_neg, zpow_neg]

section ArchimedeanHeckeTest

open InfinitePlace.Completion HeckeGaussian
open scoped ENNReal

local notation "S₀" => (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
local notation "A₀" => SAdeleRing F S₀
local notation "μ₀" => sAdditiveTamagawaMeasure F S₀
local notation "ν₀" => sMultiplicativeTamagawaMeasure F S₀
private local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
private local instance (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
private local instance (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
  (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
private local instance (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
private local instance (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ := Units.isEmbedding_val₀.secondCountableTopology
private local instance (w : InfinitePlace F) : LocallyCompactSpace w.Completionˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).locallyCompactSpace
private local instance (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
  infiniteLocalAdditiveTamagawaMeasure_haar F w
private local instance (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
  infiniteLocalMultiplicative_isHaar F w
private local instance (v : S₀) : MeasurableSpace (v.val.adicCompletion F) := borel _
private local instance (v : S₀) : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
private local instance (v : S₀) : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
private local instance (v : S₀) : SecondCountableTopology (v.val.adicCompletion F)ˣ := isEmptyElim v
private local instance (v : S₀) : IsProbabilityMeasure (finiteLocalAdditiveTamagawaMeasure F v.val) := isEmptyElim v
private local instance (v : S₀) : IsProbabilityMeasure (finiteLocalMultiplicativeTamagawaMeasure F v.val) := isEmptyElim v

private local instance : MeasurableSpace A₀ := instMeasurableSpaceSAdeleRing F S₀
private local instance (v:S₀) : SecondCountableTopology (v.val.adicCompletion F) := isEmptyElim v
private local instance : BorelSpace A₀ˣ := sIdele_borelSpace F S₀

variable (F)

open Classical in
/-- The trace of a single archimedean summand is the ordinary real or complex field trace.
The rational archimedean idempotent kills all finite components of its trace. -/
private theorem arch_single_trace {B : Type*} [NormedField B] [NormedAlgebra ℝ B]
    (v : InfinitePlace F) (e : v.Completion ≃+* B) (he : Continuous e)
    (x : v.Completion) :
    adeleStandardCharacter F (Pi.single v x, 0) =
      Circle.exp (2 * Real.pi * Algebra.trace ℝ B (e x)) := by
  classical
  let := (rationalAdeleEmbedding F).toAlgebra
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let d : InfiniteAdeleRing ℚ ≃ₜ ℝ :=
    (Homeomorph.piUnique InfinitePlace.Completion).trans
      (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph
  let p : 𝔸[ℚ] →+* ℝ :=
    (ringEquivRealOfIsReal Rat.isReal_infinitePlace).toRingHom.comp
      ((Pi.evalRingHom _ Rat.infinitePlace).comp (RingHom.fst _ _))
  let q : 𝔸[F] →+* B := e.toRingHom.comp ((Pi.evalRingHom _ v).comp (RingHom.fst _ _))
  let s : B →+ 𝔸[F] :=
    { toFun := fun z ↦ (Pi.single v (e.symm z), 0)
      map_zero' := by apply Prod.ext; change Pi.single v (e.symm 0) = 0; simp; rfl
      map_add' := by
        intro a b
        apply Prod.ext
        · change Pi.single v (e.symm (a + b)) = Pi.single v (e.symm a) + Pi.single v (e.symm b)
          simp [Pi.single_add]
        · change (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) = 0 + 0
          simp }
  have hp (r : ℝ) : p (d.symm r, 0) = r := d.apply_symm_apply r
  have hqs (z : B) : q (s z) = z := by change e (Pi.single v (e.symm z) v) = z; simp
  have hs (a : 𝔸[F]) (z : B) : s (q a * z) = a * s z := by
    apply Prod.ext
    · funext i
      change Pi.single v (e.symm (e (a.1 v) * z)) i = a.1 i * Pi.single v (e.symm z) i
      by_cases h : i = v
      · subst i; simp
      · simp [Pi.single_eq_of_ne h]
    · change 0 = a.2 * 0; simp
  let j (r : ℝ) := q (rationalAdeleEmbedding F (d.symm r, 0))
  have hj : Continuous j := he.comp ((continuous_apply v).comp
    (continuous_fst.comp ((rationalAdeleEmbedding_spec F).1.comp
      (d.symm.continuous.prodMk continuous_const))))
  have hj' : j = algebraMap ℝ B := by
    apply (Rat.denseRange_cast (𝕜 := ℝ)).equalizer hj (continuous_algebraMap ℝ B)
    funext r
    have harg : d.symm (r : ℝ) = (algebraMap ℚ 𝔸[ℚ] r).1 := by
      apply d.symm_apply_eq.mpr
      change (r : ℝ) = extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        (algebraMap ℚ Rat.infinitePlace.Completion r)
      simp
    have h := rationalAdeleEmbedding_fst_eq F (d.symm (r : ℝ), 0) (algebraMap ℚ 𝔸[ℚ] r) harg
    change e ((rationalAdeleEmbedding F _).1 v) = _
    rw [h, (rationalAdeleEmbedding_spec F).2.1]
    exact DFunLike.congr_fun (Subsingleton.elim
      (q.comp ((algebraMap F 𝔸[F]).comp (algebraMap ℚ F)))
      ((algebraMap ℝ B).comp (algebraMap ℚ ℝ))) r
  have hq (r : 𝔸[ℚ]) : q (algebraMap 𝔸[ℚ] 𝔸[F] r) = algebraMap ℝ B (p r) := by
    have h := rationalAdeleEmbedding_fst_eq F r (d.symm (p r), 0) (d.symm_apply_apply r.1).symm
    change e ((rationalAdeleEmbedding F r).1 v) = _
    rw [h]
    exact congrFun hj' (p r)
  obtain ⟨basis⟩ := rationalAdeleEmbedding_hasBasis F
  obtain ⟨_, htrace⟩ := trace_of_algebra_projection basis p (fun r ↦ ⟨_, hp r⟩) q s hqs hq hs
  let a : 𝔸[ℚ] := (1, 0)
  let t := Algebra.trace 𝔸[ℚ] 𝔸[F] (s (e x))
  have ha : a • s (e x) = s (e x) := by
    change algebraMap 𝔸[ℚ] 𝔸[F] a * _ = _
    rw [← hs, hq, show p a = 1 from map_one (ringEquivRealOfIsReal Rat.isReal_infinitePlace),
      map_one, one_mul]
  have ht : a * t = t := by
    change a • Algebra.trace 𝔸[ℚ] 𝔸[F] _ = _
    rw [← map_smul, ha]
  have hfin : t.2 = 0 := by
    have h := congrArg Prod.snd ht
    change 0 * t.2 = t.2 at h
    simpa using h.symm
  have hsingle : s (e x) = (Pi.single v x, 0) := by change (Pi.single v (e.symm (e x)), _) = _; simp
  change ratAdeleStandardCharacter (Algebra.trace 𝔸[ℚ] 𝔸[F] (Pi.single v x, 0)) = _
  rw [← hsingle, ← htrace]
  apply ratAdeleStandardCharacter_of_integral t
  apply (mem_ratIntegralAdeles t).mpr
  intro w
  rw [hfin]
  exact (w.adicCompletionIntegers ℚ).zero_mem



open Classical in
/-- Integrating a radial function on the local units gives a constant multiple of dr/r.
The constants are two at a real place and four pi at a complex place. -/
private theorem localUnit_radial (w : InfinitePlace F) (φ : ℝ → ℂ) :
    (∫ u : w.Completionˣ, φ ‖u.val‖ ∂infiniteLocalMultiplicativeTamagawaMeasure F w) =
      (if w.IsReal then 2 else 4 * Real.pi : ℝ) • ∫ r in Ioi (0 : ℝ), r⁻¹ • φ r := by
  let d := w.mult
  let ν := infiniteLocalAdditiveTamagawaMeasure F w
  let D (x : w.Completion) := (↑(‖x‖₊ ^ d) : ℝ≥0∞)⁻¹
  let U : Set w.Completion := {0}ᶜ
  have hU : U = range (Units.val : w.Completionˣ → w.Completion) := by
    ext x
    simpa [U] using (Units.exists_iff_ne_zero (p := (· = x))).symm
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  have hmU : MeasurableSet U := (measurableSet_singleton (0 : w.Completion)).compl
  have he := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  have hD : Measurable D := by dsimp [D]; fun_prop
  have hDf : ∀ᵐ x ∂ν.restrict U, D x < ⊤ := by
    apply (ae_restrict_iff' hmU).mpr (ae_of_all _ fun x hx ↦ ?_)
    have hp : 0 < ‖x‖₊ := NNReal.coe_pos.mp (norm_pos_iff.mpr hx)
    exact ENNReal.inv_lt_top.mpr (by positivity)
  have hmap : Measure.map Units.val (infiniteLocalMultiplicativeTamagawaMeasure F w) =
      (ν.restrict U).withDensity D := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure, he.map_comap, ← hU, restrict_withDensity hmU]
  rw [← he.integral_map (fun x : w.Completion ↦ φ ‖x‖), hmap,
    integral_withDensity_eq_integral_toReal_smul hD hDf]
  simp only [D, ENNReal.toReal_inv, ENNReal.coe_toReal, NNReal.coe_pow, coe_nnNorm]
  have hRad {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
      [μ.IsAddHaarMeasure] (hd : Module.finrank ℝ E = d) :
      (∫ x : E, (‖x‖ ^ d)⁻¹ • φ ‖x‖ ∂μ) =
        (d : ℝ) • μ.real (Metric.ball 0 1) • ∫ r in Ioi (0 : ℝ), r⁻¹ • φ r := by
    rw [integral_fun_norm_addHaar μ (fun r : ℝ ↦ (r ^ d)⁻¹ • φ r), hd, ← Nat.cast_smul_eq_nsmul ℝ]
    congr 2
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
    have hd' : d - 1 + 1 = d := Nat.sub_add_cancel w.mult_pos
    rw [smul_smul]
    congr 1
    have hn : r ≠ 0 := ne_of_gt hr
    rw [← hd', pow_succ]
    field_simp [hn, hd']
    simp
  have htransport {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
      [μ.IsAddHaarMeasure] (e : E ≃ᵢ w.Completion) (he0 : e 0 = 0) (hmeas : ν = μ.map e)
      (hd : Module.finrank ℝ E = d) :
      (∫ x in U, (‖x‖ ^ d)⁻¹ • φ ‖x‖ ∂ν) =
        (d : ℝ) • μ.real (Metric.ball 0 1) • ∫ r in Ioi (0 : ℝ), r⁻¹ • φ r := by
    let h := e.toHomeomorph.toMeasurableEquiv
    change ν = μ.map h at hmeas
    rw [hmeas, h.restrict_map, h.measurableEmbedding.integral_map]
    have hU' : h ⁻¹' U = {0}ᶜ := by
      ext x
      change (e x ≠ 0) ↔ x ≠ 0
      rw [← he0, e.injective.ne_iff]
    rw [hU', restrict_compl_singleton]
    exact (integral_congr_ae (ae_of_all _ fun x ↦ congrArg (fun r : ℝ ↦ (r ^ d)⁻¹ • φ r)
      (e.isometry.norm_map_of_map_zero he0 x))).trans (hRad μ hd)
  by_cases hw : w.IsReal
  · let e := isometryEquivRealOfIsReal hw
    have h := htransport volume e.symm (map_zero (ringEquivRealOfIsReal hw).symm)
      (by simp [ν, infiniteLocalAdditiveTamagawaMeasure, hw]; rfl) (by simp [d, hw.mult_eq_one])
    simpa [hw, d, hw.mult_eq_one, Real.volume_real_ball] using h
  · have hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let e := isometryEquivComplexOfIsComplex hw'
    let μ : Measure ℂ := (2 : ℕ) • volume
    let : μ.IsAddHaarMeasure := by
      have hμ : μ = (2 : ℝ≥0∞) • volume := by simp [μ, two_smul]
      rw [hμ]
      exact Measure.IsAddHaarMeasure.smul volume (by norm_num) (by norm_num)
    have h := htransport μ e.symm (map_zero (ringEquivComplexOfIsComplex hw').symm)
      (by simp [ν, infiniteLocalAdditiveTamagawaMeasure, hw]; rfl) (by simp [d, hw'.mult_eq_two])
    simp [hw, d, hw'.mult_eq_two, μ, Measure.real, two_smul, ENNReal.toReal_add] at h ⊢
    rw [h]
    ring

variable {F}
open Classical in
/-- The parity or angular Gaussian at an infinite place. -/
private def localArchTest (χ : U[F]) (w : InfinitePlace F) (x : w.Completion) : ℂ :=
  if h : w.IsReal then
    realTest (realHeckeCharacter_parameters χ w h).exists.choose.2 ((ringEquivRealOfIsReal h) x)
  else
    let h' := InfinitePlace.not_isReal_iff_isComplex.mp h
    complexTest (complexHeckeCharacter_parameters χ w h').exists.choose.2 ((ringEquivComplexOfIsComplex h') x)

/-- The parity of the test cancels the sign of the character. -/
private theorem realWeight_cancel (n : ℕ) (x : ℝ) :
    (x : ℂ) ^ n * (if 0 < x then 1 else (-1 : ℂ)) ^ n = (‖x‖:ℂ) ^ n := by
  rw [← mul_pow]
  congr 1
  by_cases hx : 0 < x
  · simp [hx, abs_of_pos hx, Real.norm_eq_abs]
  · simp [hx, abs_of_nonpos (le_of_not_gt hx), Real.norm_eq_abs]

/-- The monomial of opposite angular weight cancels the unit-circle character. -/
private theorem complexWeight_cancel (m : ℤ) {z : ℂ} (hz : z ≠ 0) :
    (if 0 ≤ m then star z else z) ^ m.natAbs * (z / (‖z‖:ℂ)) ^ m = (‖z‖:ℂ) ^ m.natAbs := by
  have hn : (‖z‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  cases m with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, Int.natCast_nonneg, ite_true, Int.natAbs_natCast, zpow_natCast, ← mul_pow]
    congr 1
    rw [← mul_div_assoc, show star z * z = (‖z‖:ℂ) ^ 2 from Complex.conj_mul' z]
    field_simp
  | negSucc n =>
    simp only [Int.negSucc_not_nonneg, ite_false, Int.natAbs_negSucc, zpow_negSucc, ← inv_pow, ← mul_pow]
    congr 1
    field_simp

/-- Twisting the restricted unitary character contributes the normalized local norm power. -/
private theorem localCharacter_radial (χ : U[F]) (w : InfinitePlace F) (s : ℂ) (u : w.Completionˣ) :
    ideleClassNormTwist χ s (IdeleClassGroup.ofCompletion (𝓞 F) F w u) =
      infinitePlaceRestriction F w (ideleClassNormTwist χ 0) u * (((‖u.val‖ ^ w.mult : ℝ) : ℂ) ^ s) := by
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F w u
  change (χ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ s =
    ((χ g : ℂ) * _ ^ (0 : ℂ)) * _
  rw [Complex.cpow_zero, mul_one]
  dsimp only [g]
  rw [ideleClassNorm_ofCompletion]
  rfl

/-- At a real place the product of the test and the character is radial. -/
private theorem realCharacter_local (χ : U[F]) (w : InfinitePlace F) (h : w.IsReal) (s : ℂ)
    (u : w.Completionˣ) :
    let a := (realHeckeCharacter_parameters χ w h).exists.choose
    localArchTest χ w u.val * ideleClassNormTwist χ s (IdeleClassGroup.ofCompletion (𝓞 F) F w u) =
      (‖u.val‖:ℂ) ^ a.2.val * (Real.exp (-(Real.pi * ‖u.val‖ ^ 2)) : ℂ) *
        (((‖u.val‖ ^ 1 : ℝ) : ℂ) ^ (s + a.1)) := by
  let e := ringEquivRealOfIsReal h
  let x := Units.map e.toMonoidHom u
  let a := (realHeckeCharacter_parameters χ w h).exists.choose
  have hpar := (realHeckeCharacter_parameters χ w h).exists.choose_spec.2 x
  have he : Units.map e.symm.toMonoidHom x = u := by apply Units.ext; exact e.symm_apply_apply _
  have hnorm : ‖x.val‖ = ‖u.val‖ := (isometryEquivRealOfIsReal h).isometry.norm_map_of_map_zero (map_zero e) _
  change infinitePlaceRestriction F w (ideleClassNormTwist χ 0) (Units.map e.symm.toMonoidHom x) =
    (‖x.val‖:ℂ) ^ a.1 * (if 0 < x.val then 1 else (-1 : ℂ)) ^ a.2.val at hpar
  rw [he] at hpar
  have hx : (x.val : ℂ) ^ a.2.val * (if 0 < x.val then 1 else (-1 : ℂ)) ^ a.2.val =
      (‖u.val‖:ℂ) ^ a.2.val := (realWeight_cancel a.2.val x.val).trans (by rw [hnorm])
  change localArchTest χ w u.val * _ = (‖u.val‖:ℂ) ^ a.2.val * _ * _ ^ (s + a.1)
  rw [show localArchTest χ w u.val = realTest a.2 x.val by simp [localArchTest, h, realTest, a, e, x],
    localCharacter_radial, hpar, h.mult_eq_one, pow_one, Complex.cpow_add _ _ (by
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero))]
  dsimp only [realTest]
  rw [hnorm, ← hx]
  ring

/-- At a complex place the product of the test and the character is radial. -/
private theorem complexCharacter_local (χ : U[F]) (w : InfinitePlace F) (h : w.IsComplex) (s : ℂ)
    (u : w.Completionˣ) :
    let a := (complexHeckeCharacter_parameters χ w h).exists.choose
    localArchTest χ w u.val * ideleClassNormTwist χ s (IdeleClassGroup.ofCompletion (𝓞 F) F w u) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((‖u.val‖:ℂ) ^ a.2.natAbs *
        (Real.exp (-(2 * Real.pi * ‖u.val‖ ^ 2)) : ℂ) * (((‖u.val‖ ^ 2 : ℝ) : ℂ) ^ (s + a.1))) := by
  let e := ringEquivComplexOfIsComplex h
  let x := Units.map e.toMonoidHom u
  let a := (complexHeckeCharacter_parameters χ w h).exists.choose
  have hpar := (complexHeckeCharacter_parameters χ w h).exists.choose_spec.2 x
  have he : Units.map e.symm.toMonoidHom x = u := by apply Units.ext; exact e.symm_apply_apply _
  have hnorm : ‖x.val‖ = ‖u.val‖ := (isometryEquivComplexOfIsComplex h).isometry.norm_map_of_map_zero (map_zero e) _
  change infinitePlaceRestriction F w (ideleClassNormTwist χ 0) (Units.map e.symm.toMonoidHom x) =
    ((‖x.val‖ ^ 2 : ℝ) : ℂ) ^ a.1 * (x.val / (‖x.val‖:ℂ)) ^ a.2 at hpar
  rw [he] at hpar
  have hx := complexWeight_cancel a.2 x.ne_zero
  rw [hnorm] at hx
  change localArchTest χ w u.val * _ = _ * ((‖u.val‖:ℂ) ^ a.2.natAbs * _ * _ ^ (s + a.1))
  rw [show localArchTest χ w u.val = complexTest a.2 x.val by
      simp [localArchTest, InfinitePlace.not_isReal_iff_isComplex.mpr h, complexTest, a, e, x],
    localCharacter_radial, hpar, h.mult_eq_two, Complex.cpow_add _ _ (by
      exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr u.ne_zero)))]
  dsimp only [complexTest, complexTestPoly]
  rw [hnorm, ← hx]
  ring


open Classical in
/-- The local Mellin integral of the normalized test is the corresponding gamma factor. -/
private theorem archTest_local_zeta (χ : U[F]) (w : InfinitePlace F)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ u : w.Completionˣ, localArchTest χ w u.val *
      ideleClassNormTwist χ s (IdeleClassGroup.ofCompletion (𝓞 F) F w u)
      ∂infiniteLocalMultiplicativeTamagawaMeasure F w) =
      if h : w.IsReal then
        let a := (realHeckeCharacter_parameters χ w h).exists.choose
        Complex.Gammaℝ (s + a.1 + a.2.val)
      else
        let a := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp h)).exists.choose
        Complex.Gammaℂ (s + a.1 + a.2.natAbs / 2) / 2 := by
  by_cases hw : w.IsReal
  · let a := (realHeckeCharacter_parameters χ w hw).exists.choose
    have ha : a.1.re = 0 := (realHeckeCharacter_parameters χ w hw).exists.choose_spec.1
    rw [dite_eq_left hw, show (fun u : w.Completionˣ ↦ localArchTest χ w u.val * _) = _
        from funext (realCharacter_local χ w hw s)]
    rw [localUnit_radial F w (fun r : ℝ ↦ (r : ℂ) ^ a.2.val * (Real.exp (-(Real.pi * r ^ 2)) : ℂ) * ((r ^ 1 : ℝ) : ℂ) ^ (s + a.1)), ite_eq_left hw]
    exact realMellin_gamma _ _ (by simpa [ha] using hs)
  · let hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let a := (complexHeckeCharacter_parameters χ w hw').exists.choose
    have ha : a.1.re = 0 := (complexHeckeCharacter_parameters χ w hw').exists.choose_spec.1
    rw [dite_eq_right hw, show (fun u : w.Completionˣ ↦ localArchTest χ w u.val * _) = _
        from funext (complexCharacter_local χ w hw' s)]
    rw [localUnit_radial F w (fun r : ℝ ↦ ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((r : ℂ) ^ a.2.natAbs *
        (Real.exp (-(2 * Real.pi * r ^ 2)) : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ (s + a.1))), ite_eq_right hw]
    exact complexMellin_gamma _ _ (by simpa [ha] using hs)

open Classical in
/-- The degree of the polynomial multiplying the local Gaussian. -/
private def archTest_degree (χ : U[F]) (w : InfinitePlace F) : ℕ :=
  if h : w.IsReal then (realHeckeCharacter_parameters χ w h).exists.choose.2.val
  else (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp h)).exists.choose.2.natAbs

open Classical in
/-- The local trace Fourier transform exchanges the tests for a character and its inverse. -/
private theorem archTest_local_fourier (χ : U[F]) (w : InfinitePlace F) (y : w.Completion) :
    (∫ x, localArchTest χ w x * star (adeleStandardCharacter F (Pi.single w (x * y), 0) : ℂ)
      ∂infiniteLocalAdditiveTamagawaMeasure F w) =
      (-Complex.I) ^ archTest_degree χ w * localArchTest χ⁻¹ w y := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  by_cases hw : w.IsReal
  · let e := ringEquivRealOfIsReal hw
    let i := isometryEquivRealOfIsReal hw
    let a := (realHeckeCharacter_parameters χ w hw).exists.choose
    have ht := arch_single_trace F w e i.continuous
    simp_rw [ht, Algebra.trace_self_apply, map_mul]
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left hw]
    change (∫ x, _ ∂volume.map i.symm.toHomeomorph) = _
    rw [i.symm.toHomeomorph.measurableEmbedding.integral_map]
    simp only [localArchTest, archTest_degree, dite_eq_left hw, realHecke_inverse_parameters]
    change (∫ x : ℝ, realTest a.2 (e (e.symm x)) * star (Circle.exp (2 * Real.pi * (e (e.symm x) * e y)) : ℂ)) =
      (-Complex.I) ^ a.2.val * realTest a.2 (e y)
    simpa only [RingEquiv.apply_symm_apply, realTest] using realGaussianFourier a.2 (e y)
  · let hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let e := ringEquivComplexOfIsComplex hw'
    let i := isometryEquivComplexOfIsComplex hw'
    let a := (complexHeckeCharacter_parameters χ w hw').exists.choose
    have ht := arch_single_trace F w e i.continuous
    simp_rw [ht, Algebra.trace_complex_apply, map_mul]
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right hw]
    change (∫ x, _ ∂((2 : ℕ) • (volume : Measure ℂ)).map i.symm.toHomeomorph) = _
    rw [i.symm.toHomeomorph.measurableEmbedding.integral_map, ← Nat.cast_smul_eq_nsmul ENNReal,
      integral_smul_measure]
    simp only [localArchTest, archTest_degree, dite_eq_right hw, complexHecke_inverse_parameters]
    change _ • (∫ x : ℂ, complexTest a.2 (e (e.symm x)) * star (Circle.exp (2 * Real.pi * (2 * (e (e.symm x) * e y).re)) : ℂ)) =
      (-Complex.I) ^ a.2.natAbs * complexTest (-a.2) (e y)
    simpa only [RingEquiv.apply_symm_apply, Nat.cast_ofNat, ENNReal.toReal_ofNat] using complexGaussianFourier a.2 (e y)
open Classical in
/-- The Fourier integral of a product over the infinite places factors into its local transforms. -/
private theorem arch_Fourier_prod (P : (w : InfinitePlace F) → w.Completion → ℂ) (y : A₀) :
    @tamagawaFourier _ _ (instMeasurableSpaceSAdeleRing F S₀) μ₀ (sAdeleStandardCharacter F S₀)
      (fun x ↦ ∏ w, P w (x.1 w)) y =
      ∏ w, ∫ x, P w x * star (adeleStandardCharacter F (Pi.single w (x * y.1 w), 0) : ℂ)
        ∂infiniteLocalAdditiveTamagawaMeasure F w := by
  classical
  let H (x : (w : InfinitePlace F) → w.Completion) :=
    ∏ w, P w (x w) * star (adeleStandardCharacter F (Pi.single w (x w * y.1 w), 0) : ℂ)
  let μ := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
  let ν := Measure.pi (fun v : S₀ ↦ finiteLocalAdditiveTamagawaMeasure F v.val)
  change (∫ x : A₀, (∏ w, P w (x.1 w)) * star (sAdeleStandardCharacter F S₀ (x * y) : ℂ) ∂μ.prod ν) = _
  have h (x : A₀) : (∏ w, P w (x.1 w)) * star (sAdeleStandardCharacter F S₀ (x * y) : ℂ) = H x.1 := by
    simp only [sAdeleStandardCharacter, Fintype.prod_empty, mul_one,
      H, Finset.prod_mul_distrib]
    congr 1
    change (starRingEnd ℂ) (Circle.coeHom (∏ w, adeleStandardCharacter F (Pi.single w (x.1 w * y.1 w), 0))) = _
    rw [map_prod, map_prod]
    rfl
  rw [show (fun x : A₀ ↦ _) = _ from funext h]
  have hf := integral_fun_fst (μ := μ) (ν := ν) H
  have hν : ν.real univ = 1 := by simp [ν, Measure.real]
  rw [hν, one_smul] at hf
  refine hf.trans ?_
  exact integral_fintype_prod_eq_prod (μ := infiniteLocalAdditiveTamagawaMeasure F)
    (fun w x ↦ P w x * star (adeleStandardCharacter F (Pi.single w (x * y.1 w), 0) : ℂ))

/-- The archimedean zeta integral of a product factors into local Mellin integrals. -/
private theorem arch_zeta_prod (P : (w : InfinitePlace F) → w.Completion → ℂ)
    (χ : HeckeCharacter (𝓞 F) F) :
    (∫ u : A₀ˣ, (∏ w, P w (u.val.1 w)) * χ (classOf (sIdeleInsertion F S₀ u)) ∂ν₀) =
      ∏ w, ∫ u : w.Completionˣ, P w u.val * χ (IdeleClassGroup.ofCompletion (𝓞 F) F w u)
        ∂infiniteLocalMultiplicativeTamagawaMeasure F w := by
  classical
  let e := (sIdeleUnitsEquiv F S₀).toHomeomorph.toMeasurableEquiv
  let μ := Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)
  let ν := Measure.pi (fun v : S₀ ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val)
  let G (u : A₀ˣ) := (∏ w, P w (u.val.1 w)) * χ (classOf (sIdeleInsertion F S₀ u))
  let H (x : (w : InfinitePlace F) → w.Completionˣ) :=
    ∏ w, P w (x w).val * χ (IdeleClassGroup.ofCompletion (𝓞 F) F w (x w))
  change (∫ u, G u ∂(μ.prod ν).map e) = _
  rw [e.measurableEmbedding.integral_map]
  have h (x) : G (e x) = H x.1 := by
    simp only [G, sIdeleInsertion, MonoidHom.finsetProd_apply,
      Fintype.prod_empty, mul_one, H, Finset.prod_mul_distrib]
    change _ * χ ((QuotientGroup.mk' _) _) = _
    rw [map_prod, map_prod]
    rfl
  rw [show (fun x ↦ G (e x)) = _ from funext h]
  have hf := integral_fun_fst (μ := μ) (ν := ν) H
  have hν : ν.real univ = 1 := by simp [ν, Measure.real]
  rw [hν, one_smul] at hf
  refine hf.trans ?_
  exact integral_fintype_prod_eq_prod (μ := infiniteLocalMultiplicativeTamagawaMeasure F)
    (fun w u ↦ P w u.val * χ (IdeleClassGroup.ofCompletion (𝓞 F) F w u))

/-- The product of the local polynomial Gaussians is Schwartz in mixed coordinates. -/
private theorem archTest_mem (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    (fun x : Multiplicative A₀ ↦ ∏ w, localArchTest χ w (x.toAdd.1 w)) ∈
      schwartzBruhatSubmodule (Multiplicative A₀) := by
  classical
  let G := Multiplicative (InfiniteAdeleRing F)
  let : T2Space G := inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))
  let : LocallyCompactSpace G := InfiniteAdeleRing.locallyCompactSpace F
  let : T2Space (Multiplicative A₀) := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S₀) → v.val.adicCompletion F)))
  let : LocallyCompactSpace (Multiplicative A₀) := inferInstanceAs (LocallyCompactSpace A₀)
  let e : Multiplicative A₀ ≃ₜ* G :=
    { toMulEquiv := (AddEquiv.prodUnique (M := InfiniteAdeleRing F)
        (N := (v : S₀) → v.val.adicCompletion F)).toMultiplicative
      continuous_toFun := continuous_fst
      continuous_invFun := continuous_id.prodMk continuous_const }
  let g (x : InfiniteAdeleRing F) := ∏ w, localArchTest χ w (x w)
  apply schwartzBruhat_mem_comp_equiv e (g := g ∘ Multiplicative.toAdd)
  apply (mem_archimedeanSchwartzBruhat_iff g).mpr
  let p (v : {w : InfinitePlace F // w.IsReal}) (x : ℝ) :=
    (x : ℂ) ^ (realHeckeCharacter_parameters χ v.val v.property).exists.choose.2.val
  let q (v : {w : InfinitePlace F // w.IsComplex}) :=
    complexTestPoly (complexHeckeCharacter_parameters χ v.val v.property).exists.choose.2
  have hp (v) : (p v).HasTemperateGrowth :=
    (Complex.ofRealCLM.hasTemperateGrowth).pow _
  have hq (v) : (q v).HasTemperateGrowth := by
    let m := (complexHeckeCharacter_parameters χ v.val v.property).exists.choose.2
    change (fun z : ℂ ↦ ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (if 0 ≤ m then star z else z) ^ m.natAbs).HasTemperateGrowth
    by_cases hm : 0 ≤ m
    · simp only [ite_eq_left hm]
      exact (Function.HasTemperateGrowth.const _).mul (Complex.conjCLE.hasTemperateGrowth.pow _)
    · simp only [ite_eq_right hm]
      exact (Function.HasTemperateGrowth.const _).mul (Function.HasTemperateGrowth.id.pow _)
  obtain ⟨f, hf⟩ := mixedGaussian_schwartz p q hp hq
  refine ⟨f, fun x ↦ ?_⟩
  rw [hf]
  dsimp only [g]
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    simp only [localArchTest, dite_eq_left v.property]
    rfl
  · apply Finset.prod_congr rfl
    intro v _
    simp only [localArchTest, dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr v.property)]
    rfl

end ArchimedeanHeckeTest

/-- Paper: Equations (3.4.3.3)–(3.4.3.6), p. 152. There are archimedean tests
for a unitary character and its inverse whose zeta integrals equal their gamma factors.
The trace-pairing Fourier transform sends the first test to a nonzero multiple of the second.
The proof chooses products of local Gaussians.
Deviation: The complex monomials have angular weight opposite to the character. -/
theorem exists_archimedeanHeckeTest_fourier (χ : U[F]) :
    ∃ (f fdual : SchwartzBruhat (Multiplicative (SAdeleRing F ∅))) (c : ℂ), c ≠ 0 ∧
      (∀ y, archimedeanFourier f y = c * fdual (Multiplicative.ofAdd y)) ∧
      (∀ s : halfPlane, archimedeanZeta f (ideleClassNormTwist χ s) = heckeGammaFactor χ s) ∧
      (∀ s : halfPlane,
        archimedeanZeta fdual (ideleClassNormTwist χ⁻¹ s) = heckeGammaFactor χ⁻¹ s) := by
  let f (ψ : U[F]) : SchwartzBruhat (Multiplicative (SAdeleRing F ∅)) :=
    ⟨_, archTest_mem ψ⟩
  have hz (ψ : U[F]) (s : Complex.re ⁻¹' Set.Ioi (1 : ℝ)) :
      (∫ u : (SAdeleRing F ∅)ˣ, f ψ (Multiplicative.ofAdd u.val) *
        ideleClassNormTwist ψ s (classOf (sIdeleInsertion F ∅ u)) ∂sMultiplicativeTamagawaMeasure F ∅) = heckeGammaFactor ψ s := by
    change (∫ u : (SAdeleRing F ∅)ˣ, (∏ w, localArchTest ψ w (u.val.1 w)) * _ ∂sMultiplicativeTamagawaMeasure F ∅) = _
    rw [arch_zeta_prod]
    exact Finset.prod_congr rfl fun w _ ↦ archTest_local_zeta ψ w (zero_lt_one.trans s.property)
  refine ⟨f χ, f χ⁻¹, ∏ w, (-Complex.I) ^ archTest_degree χ w,
    Finset.prod_ne_zero_iff.mpr (fun _ _ ↦ pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)), ?_, hz χ, hz χ⁻¹⟩
  intro y
  change @tamagawaFourier _ _ (instMeasurableSpaceSAdeleRing F ∅)
    (sAdditiveTamagawaMeasure F ∅) (sAdeleStandardCharacter F ∅) (fun x ↦ ∏ w, localArchTest χ w (x.1 w)) y = _
  rw [arch_Fourier_prod]
  simpa only [Finset.prod_mul_distrib] using! Finset.prod_congr (s₂ := Finset.univ) rfl (fun w _ ↦ archTest_local_fourier χ w (y.1 w))

section FinitePlaceHeckeTests

open Function Filter Set MeasureTheory NumberField IsDedekindDomain Topology InfinitePlace.Completion
open scoped NNReal ENNReal NumberField.AdeleRing Pointwise

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
local notation "K" => v.adicCompletion F
local notation "O" => v.adicCompletionIntegers F
local notation "μv" => finiteLocalAdditiveTamagawaMeasure F v
local notation "νv" => finiteLocalMultiplicativeTamagawaMeasure F v
local notation "ψ" => finiteLocalStandardCharacter F v
private local instance : MeasurableSpace K := borel _
private local instance : BorelSpace K := ⟨rfl⟩
private local instance : MeasurableSpace Kˣ := borel _
private local instance : BorelSpace Kˣ := ⟨rfl⟩
private local instance : ProperSpace K := properSpace_adicCompletion v
private local instance : LocallyCompactSpace Kˣ := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).locallyCompactSpace
private local instance : TotallyDisconnectedSpace Kˣ := ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
  Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
private local instance : (μv).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
private local instance : (νv).IsHaarMeasure := finiteLocalMultiplicative_isHaar F v

/-- Integer units in a finite completion have normalized absolute value one. -/
private theorem finiteUnit_norm (u : Kˣ) : u ∈ (O).units ↔ ‖u.val‖ = 1 :=
  HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.trans
    Valued.toNormedField.norm_eq_one_iff.symm

/-- A circle character is locally constant on the units of a nonarchimedean local field. -/
private theorem unitWeight_lc (χ : PontryaginDual Kˣ) : IsLocallyConstant χ := by
  have hArc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  have hU := χ.continuous.continuousAt.preimage_mem_nhds (x := (1 : Kˣ)) (by simpa using hArc)
  obtain ⟨H, _, hH⟩ := exists_compact_openSubgroup_sub_mem_nhds hU
  have hk {g : Kˣ} (hg : g ∈ H) : χ g = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro k _
    rw [← map_pow]
    exact hH (H.pow_mem hg k)
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have ht : Tendsto (fun y : Kˣ ↦ y / x) (𝓝 x) (𝓝 1) := by
    simpa only [id_eq, div_self'] using (continuous_id.div_const x).tendsto x
  filter_upwards [ht (H.isOpen.mem_nhds H.one_mem)] with y hy
  exact div_eq_one.mp ((map_div χ y x).symm.trans (hk hy))

open Classical in
/-- The inverse character on the integer units, extended by zero to the completion. -/
private def finiteUnitTest (χ : PontryaginDual Kˣ) (x : K) : ℂ :=
  if h : ‖x‖ = 1 then
    ((χ (Units.mk0 x (by intro hx; subst x; simp at h)) : Circle) : ℂ)⁻¹
  else 0

private theorem finiteUnitTest_unit (χ : PontryaginDual Kˣ) (u : Kˣ) :
    finiteUnitTest v χ u.val = if ‖u.val‖ = 1 then (χ u : ℂ)⁻¹ else 0 := by
  by_cases h : ‖u.val‖ = 1 <;> simp [finiteUnitTest, h]

/-- The ramified unit test is locally constant with compact support. -/
private theorem finiteUnitTest_regularity (χ : PontryaginDual Kˣ) :
    IsLocallyConstant (finiteUnitTest v χ) ∧ HasCompactSupport (finiteUnitTest v χ) := by
  let A := {x : K | ‖x‖ = 1}
  have hA : (Units.val : Kˣ → K) '' ((O).units : Set Kˣ) = A := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩; exact (finiteUnit_norm v u).mp hu
    · intro hx
      have hx' : x ≠ 0 := by intro h; subst x; simp [A] at hx
      let u := Units.mk0 x hx'
      exact ⟨u, (finiteUnit_norm v u).mpr hx, rfl⟩
  let e := IsOpenUnits.isOpenEmbedding_unitsVal (M := K)
  have hAopen : IsOpen A := hA ▸ e.isOpenMap _ (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _))
  have hAcompact : IsCompact A := hA ▸ (Submonoid.units_isCompact
      (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))).image Units.continuous_val
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦ ?_, hAcompact.of_isClosed_subset
    (isClosed_tsupport _) (closure_minimal (fun x hx ↦ by
      by_contra hc
      exact hx (by simp [finiteUnitTest, show ‖x‖ ≠ 1 from hc])) hAcompact.isClosed)⟩
  by_cases hx : x ∈ A
  · obtain ⟨u, hu, rfl⟩ := hA.symm ▸ hx
    rw [← e.map_nhds_eq u, Filter.eventually_map]
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp (unitWeight_lc v χ) u,
      (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).mem_nhds hu] with z hz hz'
    rw [finiteUnitTest_unit, finiteUnitTest_unit, ite_eq_left ((finiteUnit_norm v _).mp hz'),
      ite_eq_left ((finiteUnit_norm v _).mp hu), hz]
  · filter_upwards [hAcompact.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [finiteUnitTest, show ‖y‖ ≠ 1 from hy, show ‖x‖ ≠ 1 from hx]

private theorem finiteUnitTest_mul (χ : PontryaginDual Kˣ) (u : Kˣ) (hu : ‖u.val‖ = 1) (x : K) :
    finiteUnitTest v χ (u.val * x) = (χ u : ℂ)⁻¹ * finiteUnitTest v χ x := by
  by_cases hx : x = 0
  · subst x; simp [finiteUnitTest]
  let t := Units.mk0 x hx
  change finiteUnitTest v χ (u * t).val = _ * finiteUnitTest v χ t.val
  rw [finiteUnitTest_unit, finiteUnitTest_unit, Units.val_mul, norm_mul, hu, one_mul]
  split_ifs <;> simp [mul_comm]

/-- An integer unit preserves additive Haar measure, since it preserves the integer ring. -/
private theorem finiteUnit_measurePreserving (u : Kˣ) (hu : ‖u.val‖ = 1) :
    MeasurePreserving (fun x : K ↦ u.val * x) μv μv := by
  have hO : (O : Set K) = Metric.closedBall 0 1 := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
    rfl
  have hopen := Valued.isOpen_valuationSubring K
  have hpos : μv (O : Set K) ≠ 0 := (hopen.measure_pos μv ⟨0, (O).zero_mem⟩).ne'
  have hfinite : μv (O : Set K) ≠ ⊤ := hO ▸ (isCompact_closedBall (0 : K) 1).measure_ne_top
  have hmod (t : Kˣ) (ht : ‖t.val‖ = 1) : distribHaarChar K t = 1 := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul hpos hfinite
    have hset : t • (O : Set K) = O := by
      rw [hO, ← preimage_smul_inv]
      ext x
      simp [Metric.mem_closedBall, dist_zero_right, Units.smul_def, norm_mul, ht]
    simp [hset]
  refine ⟨by fun_prop, ?_⟩
  ext s hs
  change (μv).map (u • · : K → K) s = _
  rw [Measure.map_apply (measurableEmbedding_const_smul u).measurable hs,
    preimage_smul, ← distribHaarChar_mul μv, hmod u⁻¹ (by simpa using inv_eq_one.mpr hu)]
  simp

/-- Plancherel and the value of the unit test at one give a nonzero Fourier coefficient. -/
private theorem finiteFourier_unit_ne_zero (χ : PontryaginDual Kˣ) :
    ∃ y : K, tamagawaFourier μv ψ (finiteUnitTest v χ) y ≠ 0 := by
  classical
  obtain ⟨e, he, hP⟩ := finiteLocalAdditiveTamagawaMeasure_selfDual F v
  let G := Multiplicative K
  let f : G → ℂ := fun x ↦ finiteUnitTest v χ x.toAdd
  have hfc : Continuous f := (finiteUnitTest_regularity v χ).1.continuous
  have hfs : HasCompactSupport f := (finiteUnitTest_regularity v χ).2
  let μ' : Measure G := μv
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let : μ'.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := (finiteLocalAdditiveTamagawaMeasure_isAddHaar F v).toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := (finiteLocalAdditiveTamagawaMeasure_isAddHaar F v).toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ (finiteLocalAdditiveTamagawaMeasure_isAddHaar F v).map_add_left_eq_self x.toAdd }
  have hi := hfc.integrable_of_hasCompactSupport (μ := μ') hfs
  have h₂ := hfc.memLp_of_hasCompactSupport (μ := μ') (p := 2) hfs
  have hnorm := (hP.2.2 f hi h₂).2
  by_contra! h
  have hzero : lcaFourier μ' f = 0 := by
    funext γ
    obtain ⟨y, rfl⟩ := e.surjective γ
    have hy := tamagawaFourier_eq_lcaFourier μv ψ (finiteUnitTest v χ) y.toAdd (e y) (fun x ↦ by
      simpa [mul_comm] using he y.toAdd x)
    exact hy.symm.trans (h y.toAdd)
  change eLpNorm (lcaFourier μ' f) 2 _ = eLpNorm f 2 μ' at hnorm
  rw [hzero, eLpNorm_zero] at hnorm
  have hf0 := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞)≠0)).mp hnorm.symm
  have hval := congrFun ((hfc.ae_eq_iff_eq μ' continuous_zero).mp hf0) (Multiplicative.ofAdd (1 : K))
  change finiteUnitTest v χ 1 = 0 at hval
  simp [finiteUnitTest] at hval

/-- The Fourier transform of the inverse-character test transforms by the character on units. -/
private theorem finiteFourier_unit_covariant (χ : PontryaginDual Kˣ) (u : Kˣ) (hu : ‖u.val‖ = 1) (y : K) :
    tamagawaFourier μv ψ (finiteUnitTest v χ) (u.val * y) =
      (χ u : ℂ) * tamagawaFourier μv ψ (finiteUnitTest v χ) y := by
  let f := finiteUnitTest v χ
  let g (x : K) := f x * star (ψ (x * y) : ℂ)
  have hm := finiteUnit_measurePreserving v u hu
  have hchg := hm.integral_comp (measurableEmbedding_const_smul u) g
  unfold tamagawaFourier
  change (∫ x, f x * star (ψ (x * (u.val * y)) : ℂ) ∂μv) = (χ u : ℂ) * ∫ x, g x ∂μv
  rw [← hchg, ← integral_const_mul]
  apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only [g]
  rw [show f (u.val * x) = (χ u : ℂ)⁻¹ * f x from finiteUnitTest_mul v χ u hu x,
    mul_assoc u.val x y, mul_left_comm u.val x y]
  field_simp

private theorem standardChar_add (x y : K) : ψ (x + y) = ψ x * ψ y := by
  obtain ⟨c, hc, _⟩ := finiteLocalStandardCharacter_exists_continuousMonoidHom F v
  exact (hc _).symm.trans ((map_mul c (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)).trans
    (congrArg₂ (· * ·) (hc x) (hc y)))

/-- A nonzero Fourier coefficient annihilates every additive period of the test. -/
private theorem finiteFourier_translate_kernel {f : K → ℂ} {t y : K} (hf : ∀ x, f (t + x) = f x)
    (hy : tamagawaFourier μv ψ f y ≠ 0) : ψ (t * y) = 1 := by
  let g (x : K) := f x * star (ψ (x * y) : ℂ)
  have ha (x : K) : g (t + x) = star (ψ (t * y) : ℂ) * g x := by
    simp [g, hf, add_mul, standardChar_add, Circle.coe_mul, mul_left_comm]
  have hi : star (ψ (t * y) : ℂ) * (∫ x, g x ∂μv) = 1 * (∫ x, g x ∂μv) := by
    rw [one_mul, ← integral_const_mul, ← integral_add_left_eq_self (μ := μv) g t]
    exact integral_congr_ae (ae_of_all _ fun x ↦ (ha x).symm)
  have h := mul_right_cancel₀ hy hi
  apply Circle.coe_injective
  exact star_injective (h.trans (star_one ℂ).symm)

local notation "radius" => ((v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))

/-- The annihilator of the integer ring is the inverse-different ball. -/
private theorem trace_ball (z : K) : (∀ x ∈ (O : Set K), ψ (x * z) = 1) ↔ ‖z‖ ≤ radius :=
  Set.ext_iff.mp (finiteLocalStandardCharacter_annihilator_integers F v) z

/-- A nonzero Fourier coefficient forces the character to be trivial on sufficiently small principal units. -/
private theorem finiteFourier_implies_unit_trivial (χ : PontryaginDual Kˣ) {y : K}
    (hy : tamagawaFourier μv ψ (finiteUnitTest v χ) y ≠ 0) (u : Kˣ) (hu : ‖u.val‖ = 1)
    (hus : ‖u.val - 1‖ * ‖y‖ ≤ radius) : χ u = 1 := by
  have hphase {x : K} (hx : ‖x‖ = 1) : ψ (x * (u.val * y)) = ψ (x * y) := by
    have hxO : x ∈ O := (Valued.toNormedField.norm_le_one_iff.mp hx.le)
    have h := (trace_ball v ((u.val - 1) * y)).mpr (by simpa only [norm_mul] using hus) x hxO
    rw [show x * (u.val * y) = x * ((u.val - 1) * y) + (x * y) by ring, standardChar_add, h, one_mul]
  have heq : tamagawaFourier μv ψ (finiteUnitTest v χ) (u.val * y) = tamagawaFourier μv ψ (finiteUnitTest v χ) y := by
    apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    by_cases hx : ‖x‖ = 1
    · rw [hphase hx]
    · simp [finiteUnitTest, hx]
  rw [finiteFourier_unit_covariant v χ u hu y] at heq
  apply Circle.coe_injective
  exact mul_right_cancel₀ hy (heq.trans (one_mul _).symm)

/-- Principal units on which the character is trivial give additive periods of its unit test. -/
private theorem finiteUnitTest_add_period (χ : PontryaginDual Kˣ) {r : ℝ} (hbl : r < 1)
    (hunit : ∀ u : Kˣ, ‖u.val‖ = 1 → ‖u.val - 1‖ ≤ r → χ u = 1)
    {t : K} (ht : ‖t‖ ≤ r) : ∀ x, finiteUnitTest v χ (t + x) = finiteUnitTest v χ x := by
  intro x
  have ht' := ht.trans_lt hbl
  have heq : ‖t + x‖ = 1 ↔ ‖x‖ = 1 := by
    constructor
    · intro h
      have he := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := -t) (y := t + x)
        (by rw [norm_neg, h]; exact ht'.ne)
      simpa [h, norm_neg, max_eq_right ht'.le] using he
    · intro h
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h]; exact ht'.ne), h, max_eq_right ht'.le]
  by_cases hx : ‖x‖ = 1
  · have hx0 : x ≠ 0 := by intro hh; simp [hh] at hx
    have hx' := heq.mpr hx
    have hx0' : t + x ≠ 0 := by intro hh; simp [hh] at hx'
    let u := Units.mk0 (t + x) hx0' / Units.mk0 x hx0
    have hn : ‖u.val‖ = 1 := by change ‖(t + x) / x‖ = 1; rw [norm_div, hx', hx, div_one]
    have hdiff : ‖u.val - 1‖ ≤ r := by
      change ‖(t + x) / x - 1‖ ≤ _
      rwa [div_sub_one hx0, add_sub_cancel_right, norm_div, hx, div_one]
    have hχ := hunit u hn hdiff
    have he : u.val * x = t + x := div_mul_cancel₀ _ hx0
    rw [← he, finiteUnitTest_mul v χ u hn, hχ, Circle.coe_one, inv_one, one_mul]
  · simp [finiteUnitTest, hx, heq.not.mpr hx]

/-- For a ramified character the local conductor condition is equivalent to a
bound for the radius of any nonzero Fourier coefficient of its unit test. -/
private theorem finiteFourier_conductor_iff (χ : PontryaginDual Kˣ)
    (hram : ∃ u : Kˣ, ‖u.val‖ = 1 ∧ χ u ≠ 1) {y : K}
    (hy : tamagawaFourier μv ψ (finiteUnitTest v χ) y ≠ 0) (n : ℕ) :
    (∀ u : Kˣ, ‖u.val‖ = 1 → ‖u.val - 1‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-(n : ℤ)) → χ u = 1) ↔
      ‖y‖ ≤ radius * (v.asIdeal.absNorm : ℝ) ^ n := by
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  change (∀ u : Kˣ, ‖u.val‖ = 1 → ‖u.val - 1‖ ≤ q ^ (-(n : ℤ)) → χ u = 1) ↔ ‖y‖ ≤ radius * q ^ n
  rw [zpow_neg, zpow_natCast]
  constructor
  · intro h
    have hn : 0 < n := by
      by_contra! hzero
      obtain rfl := Nat.eq_zero_of_le_zero hzero
      obtain ⟨u, hu, hne⟩ := hram
      apply hne (h u hu ?_)
      simpa [sub_eq_add_neg, hu] using IsUltrametricDist.norm_add_le_max u.val (-(1 : K))
    let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    let b := (π : K) ^ n
    have hb : ‖b‖ = (q ^ n)⁻¹ := by
      simp [b, q, norm_pow, norm_uniformizer_adicCompletion v _ hπ]
    have hb₁ : ‖b‖ < 1 := by rw [hb]; exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq hn.ne')
    have hAnn : ∀ x ∈ (O : Set K), ψ (x * (b * y)) = 1 := by
      intro x hx
      have hx₁ : ‖x‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hx
      have ht : ‖x * b‖ ≤ ‖b‖ := by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hx₁
      have he := finiteFourier_translate_kernel v
        (finiteUnitTest_add_period v χ hb₁ (fun u hu hus ↦ h u hu (hus.trans_eq hb)) ht) hy
      rwa [mul_assoc] at he
    have h' := (trace_ball v _).mp hAnn
    rw [norm_mul, hb, ← div_eq_inv_mul, div_le_iff₀ (pow_pos hq₀ n)] at h'
    exact h'
  · intro h u hu hus
    apply finiteFourier_implies_unit_trivial v χ hy u hu
    calc
      ‖u.val - 1‖ * ‖y‖ ≤ (q ^ n)⁻¹ * (radius * q ^ n) :=
        mul_le_mul hus h (norm_nonneg _) (by positivity)
      _ = radius := by field_simp

/-- Paper: Equation (3.3.2.24), p. 141. For a ramified unit character the Fourier
shell has radius equal to the norm of the product of the different and its conductor. -/
private theorem finiteFourier_conductor_radius (χ : PontryaginDual Kˣ)
    (hram : ∃ u : Kˣ, ‖u.val‖ = 1 ∧ χ u ≠ 1) {y : K}
    (hy : tamagawaFourier μv ψ (finiteUnitTest v χ) y ≠ 0) (n : ℕ)
    (hn : IsLeast {m : ℕ | ∀ u : Kˣ, ‖u.val‖ = 1 →
      ‖u.val - 1‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-(m : ℤ)) → χ u = 1} n) :
    ‖y‖ = (v.asIdeal.absNorm : ℝ) ^ (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) + n) := by
  let q : ℝ := v.asIdeal.absNorm
  let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  have hq : 1 < q := by dsimp [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := (zero_lt_one.trans hq).ne'
  have hy₀ : y ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu, hne⟩ := hram
    exact hne (finiteFourier_implies_unit_trivial v χ hy u hu (by simp))
  have hval : (Valued.v y) ≠ 0 := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).ne_zero_iff.mpr hy₀
  let j : ℤ := WithZero.log (Valued.v y)
  have hj : ‖y‖ = q ^ j := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hval]
    norm_cast
  have hp (k : ℕ) : radius * q ^ k = q ^ ((d : ℤ) + k) := by
    rw [zpow_add₀ hq₀, zpow_natCast, zpow_natCast]
  have hUpper := (finiteFourier_conductor_iff v χ hram hy n).mp hn.1
  change ‖y‖ ≤ radius * q ^ n at hUpper
  rw [hj, hp, zpow_le_zpow_iff_right₀ hq] at hUpper
  cases n with
  | zero =>
    obtain ⟨u, hu, hne⟩ := hram
    exfalso
    apply hne (hn.1 u hu ?_)
    simpa [sub_eq_add_neg, hu] using IsUltrametricDist.norm_add_le_max u.val (-(1 : K))
  | succ k =>
    have hLower : ¬ ‖y‖ ≤ radius * q ^ k := fun h ↦
      (Nat.not_succ_le_self k) (hn.2 ((finiteFourier_conductor_iff v χ hram hy k).mpr h))
    rw [hj, hp, zpow_le_zpow_iff_right₀ hq] at hLower
    have he : j = ((d + (k + 1) : ℕ) : ℤ) := by omega
    rw [hj, he, zpow_natCast]

/-- The ramified unit test has Fourier support on a single valuation shell. A nonzero coefficient gives
an additive period ball for the test, whose annihilator bounds every other nonzero coefficient. -/
private theorem finiteFourier_common_radius (χ : PontryaginDual Kˣ)
    (hram : ∃ u : Kˣ, ‖u.val‖ = 1 ∧ χ u ≠ 1) {y z : K}
    (hy : tamagawaFourier μv ψ (finiteUnitTest v χ) y ≠ 0)
    (hz : tamagawaFourier μv ψ (finiteUnitTest v χ) z ≠ 0) : ‖z‖ ≤ ‖y‖ := by
  have hMpos : 0 < radius := pow_pos (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).trans' Nat.zero_lt_one) _
  have hbound : radius < ‖y‖ := by
    by_contra! hy'
    obtain ⟨u, hu, hn⟩ := hram
    apply hn (finiteFourier_implies_unit_trivial v χ hy u hu ?_)
    have hd := IsUltrametricDist.norm_add_le_max u.val (-(1 : K))
    rw [← sub_eq_add_neg, hu, norm_neg, norm_one, max_self] at hd
    exact (mul_le_of_le_one_left (norm_nonneg _) hd).trans hy'
  have hy0 := norm_pos_iff.mp (hMpos.trans hbound)
  let val := (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  have hnπ := norm_uniformizer_adicCompletion v (π : K) hπ
  let b : K := (π : K)⁻¹ ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) / y
  have hbn : ‖b‖ = radius / ‖y‖ := by simp [b, norm_div, norm_pow, norm_inv, hnπ]
  have hbl : ‖b‖ < 1 := by rw [hbn]; exact (div_lt_one (norm_pos_iff.mpr hy0)).mpr hbound
  have hadd {t : K} (ht : ‖t‖ ≤ ‖b‖) :=
    finiteUnitTest_add_period v χ hbl (fun u hu hus ↦ finiteFourier_implies_unit_trivial v χ hy u hu
      ((le_div_iff₀ (norm_pos_iff.mpr hy0)).mp (hus.trans_eq hbn))) ht
  have hAnn : ∀ x ∈ (O : Set K), ψ (x * (b * z)) = 1 := by
    intro x hx
    have hx' : ‖x‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hx
    have h := finiteFourier_translate_kernel v (t := x * b) (hadd (by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hx')) hz
    rwa [mul_assoc] at h
  have h := (trace_ball v _).mp hAnn
  rw [norm_mul, hbn, div_mul_eq_mul_div, div_le_iff₀ (norm_pos_iff.mpr hy0)] at h
  exact le_of_mul_le_mul_left h hMpos

private abbrev localIntegerUnits : Set Kˣ := (v.adicCompletionIntegers F).units
local notation "U" => localIntegerUnits v
local notation "Unitary" => PontryaginDual (IdeleClassGroup (𝓞 F) F)

/-- The compact open integer-unit group has finite positive multiplicative Haar mass. -/
private theorem unitMass_pos : 0 < (νv).real U := by
  let : CompactSpace O := compactSpace_adicCompletionIntegers v
  exact ENNReal.toReal_pos ((Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measure_pos νv ⟨1, (O).units.one_mem⟩).ne'
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))).measure_ne_top

private def finiteUnitary (χ : Unitary) : PontryaginDual Kˣ :=
  χ.comp ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v, continuous_ideleClass_ofAdicCompletion F v⟩

private theorem finiteUnitary_eval (χ : Unitary) (u : Kˣ) (s : ℂ) :
    finitePlaceRestriction F v (ideleClassNormTwist χ s) u = (finiteUnitary v χ u : ℂ) * (‖u.val‖ : ℂ) ^ s := by
  change (χ _ : ℂ) * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℝ≥0) : ℝ) : ℂ) ^ s = _
  rw [ideleClassNorm_ofAdicCompletion]
  rfl

private theorem finiteUnitary_unramified (χ : Unitary) :
    (ideleClassNormTwist χ 0).IsUnramifiedAt v ↔ ∀ u : Kˣ, ‖u.val‖ = 1 → finiteUnitary v χ u = 1 := by
  have hunit (z : Oˣ) :
      (ideleClassNormTwist χ 0).restrict v (z.val : K) = (finiteUnitary v χ (Units.map (O).subtype.toMonoidHom z) : ℂ) := by
    change (ideleClassNormTwist χ 0).restrict v ↑(Units.map (O).subtype.toMonoidHom z) = _
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change finitePlaceRestriction F v (ideleClassNormTwist χ 0) _ = _
    simp [finiteUnitary_eval]
  rw [HeckeCharacter.isUnramifiedAt_iff]
  simp_rw [hunit, ← Circle.coe_one, Circle.coe_inj]
  constructor
  · intro h u hu
    let z := (O).toSubmonoid.unitsEquivUnitsType ⟨u, (finiteUnit_norm v u).mpr hu⟩
    exact h z
  · intro h z
    exact h _ ((finiteUnit_norm v _).mp ⟨z.val.property, z.inv.property⟩)

/-- On a single valuation shell the Mellin transform of an equivariant test is a single complex power. -/
private theorem shell_zeta (χ : Unitary) (f : K → ℂ) (y : Kˣ)
    (hout : ∀ u : Kˣ, ‖u.val‖ ≠ ‖y.val‖ → f u.val = 0)
    (hunit : ∀ u : Kˣ, ‖u.val‖ = 1 → f (y.val * u.val) = (finiteUnitary v χ u : ℂ)⁻¹ * f y.val)
    (s : ℂ) :
    (∫ u : Kˣ, f u.val * finitePlaceRestriction F v (ideleClassNormTwist χ s) u ∂νv) =
      ((νv).real U * f y.val * (finiteUnitary v χ y : ℂ)) * (‖y.val‖ : ℂ) ^ s := by
  rw [← integral_mul_left_eq_self (μ := νv) _ y]
  let c := f y.val * (finiteUnitary v χ y : ℂ) * (‖y.val‖ : ℂ) ^ s
  have hh (u : Kˣ) : f (y * u).val * finitePlaceRestriction F v (ideleClassNormTwist χ s) (y * u) =
      (U).indicator (fun _ ↦ c) u := by
    rw [finiteUnitary_eval, Units.val_mul, norm_mul, map_mul, Circle.coe_mul]
    by_cases hu : u ∈ U
    · have hn := (finiteUnit_norm v u).mp hu
      rw [indicator_of_mem hu, hunit u hn, hn, mul_one]
      dsimp [c]
      field_simp
    · have hn := (finiteUnit_norm v u).not.mp hu
      rw [indicator_of_notMem hu, show f (y.val * u.val) = 0 from hout (y * u) (by
        rw [Units.val_mul, norm_mul]; simpa [norm_ne_zero_iff.mpr y.ne_zero] using hn), zero_mul]
  have hUo : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring K)
  rw [show (fun u : Kˣ ↦ _) = _ from funext hh]
  change (∫ u, (U).indicator (fun _ ↦ c) u ∂νv) = _
  rw [integral_indicator hUo.measurableSet, setIntegral_const]
  simp [c, Complex.real_smul, mul_assoc]

/-- Summing the Mellin integrals of the uniformizer shells of the integer ring gives its Euler factor. -/
private theorem unramified_disk_zeta (χ : Unitary)
    (hχ : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (s : Complex.re ⁻¹' Ioi (1 : ℝ)) :
    (∫ u : Kˣ, (O : Set K).indicator (fun _ ↦ (1 : ℂ)) u.val *
        finitePlaceRestriction F v (ideleClassNormTwist χ s) u ∂νv) =
      ((νv).real U : ℂ) * finiteHeckeEulerFactor χ v s := by
  classical
  let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨p, hp⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (p : K) hp.ne_zero
  have hπ : ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := norm_uniformizer_adicCompletion v _ hp
  have hπ0 := norm_pos_iff.mpr π.ne_zero
  have hπ1 : ‖π.val‖ < 1 := by rw [hπ]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)
  let i := Units.map (O).subtype.toMonoidHom
  obtain ⟨e, hep, hei⟩ := finitePlace_unitDecomposition v π hπ
  let c := finitePlaceRestriction F v (ideleClassNormTwist χ s)
  let a := c π
  have ha : ‖a‖ < 1 := by
    rw [show a = _ from finiteUnitary_eval v χ π s, norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hπ0]
    exact Real.rpow_lt_one hπ0.le hπ1 (zero_lt_one.trans s.property)
  let W (n : ℕ) : Set Kˣ := (fun u : Kˣ ↦ π ^ n * u) '' U
  have hU := Submonoid.isOpen_units (Valued.isOpen_valuationSubring K)
  have hW (n : ℕ) : MeasurableSet (W n) := (Homeomorph.mulLeft (π ^ n)).isOpenMap _ hU |>.measurableSet
  have hm (n : ℕ) : νv (W n) = νv U := measure_smul νv (π ^ n) U
  have hmem (n : ℕ) (u : Kˣ) : u ∈ W n ↔ ‖u.val‖ = ‖π.val‖ ^ n := by
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp [Units.val_pow_eq_pow_val, (finiteUnit_norm v w).mp hw]
    · intro h
      refine ⟨u / π ^ n, (finiteUnit_norm v _).mpr ?_, by simp⟩
      simp [Units.val_pow_eq_pow_val, h, norm_ne_zero_iff.mpr π.ne_zero]
  let B (n : ℕ) : Kˣ → ℂ := (W n).indicator (fun _ ↦ a ^ n)
  have hmass : νv U ≠ ⊤ := (ENNReal.toReal_pos_iff.mp (unitMass_pos v)).2.ne
  have hB (n : ℕ) : Integrable (B n) νv :=
    (integrableOn_const ((hm n).trans_ne hmass)).integrable_indicator (hW n)
  have hBn (n : ℕ) : (∫ u, ‖B n u‖ ∂νv) = (νv).real U * ‖a‖ ^ n := by
    simp only [B, norm_indicator_eq_indicator_norm]
    rw [integral_indicator (hW n), setIntegral_const]
    simp [Measure.real, hm, norm_pow, smul_eq_mul]
  have hsum := hasSum_integral_of_summable_integral_norm hB (by
    simp_rw [hBn]
    exact (summable_geometric_of_lt_one (norm_nonneg _) ha).mul_left _)
  have eval (u : Kˣ) : (∑' n, B n u) = (O : Set K).indicator (fun _ ↦ (1 : ℂ)) u.val * c u := by
    let k := (e u).1.toAdd
    let t := i (e u).2
    have ht : t ∈ U := ⟨(e u).2.val.property, (e u).2.inv.property⟩
    have hu : u = π ^ k * t := by
      apply e.injective
      rw [map_mul, map_zpow, hep, hei]
      apply Prod.ext <;> simp [k]
      change _ = Multiplicative.ofAdd (Multiplicative.toAdd (e u).1 * 1)
      simp
    have hn : ‖u.val‖ = ‖π.val‖ ^ k := by
      conv_lhs => rw [hu]
      simp [Units.val_zpow_eq_zpow_val, (finiteUnit_norm v t).mp ht]
    have huO : u.val ∈ O ↔ 0 ≤ k := by
      change Valued.v u.val ≤ 1 ↔ _
      rw [← Valued.toNormedField.norm_le_one_iff, hn]
      exact zpow_le_one_iff_right_of_lt_one₀ hπ0 hπ1
    by_cases hk : 0 ≤ k
    · lift k to ℕ using hk with n hn'
      rw [Set.indicator_of_mem (huO.mpr (by exact_mod_cast Nat.zero_le n)), one_mul]
      have hnp : ‖u.val‖ = ‖π.val‖ ^ n := by simpa using hn
      have hw : u ∈ W n := (hmem n u).mpr hnp
      rw [tsum_eq_single n (fun m hmn ↦ Set.indicator_of_notMem (mt (hmem m u).mp
        (fun eq ↦ hmn ((pow_right_injective₀ hπ0 hπ1.ne) (eq.symm.trans hnp)))) _),
        Set.indicator_of_mem hw]
      conv_rhs => rw [hu, map_mul, map_zpow]
      have hct : c t = 1 := by rw [finiteUnitary_eval v χ, ((finiteUnitary_unramified v χ).mp hχ t ((finiteUnit_norm v t).mp ht)), (finiteUnit_norm v t).mp ht]; simp
      simp [a, hct]
    · rw [Set.indicator_of_notMem (huO.not.mpr hk), zero_mul]
      apply (tsum_congr (g := fun _ ↦ (0 : ℂ)) ?_).trans (by simp)
      intro n
      apply Set.indicator_of_notMem
      intro hw
      have hux := (hmem n u).mp hw
      apply hk (huO.mp (Valued.toNormedField.norm_le_one_iff.mp (hux ▸ pow_le_one₀ hπ0.le hπ1.le)))
  simp_rw [eval] at hsum
  have hI (n : ℕ) : (∫ u, B n u ∂νv) = ((νv).real U : ℂ) * a ^ n := by
    rw [show B n = _ from rfl, integral_indicator (hW n), setIntegral_const]
    simp [Measure.real, hm, Complex.real_smul]
  simp_rw [hI] at hsum
  apply hsum.unique
  have hE := finiteHeckeEulerFactor_inv_uniformizer χ v π hp hχ s.property
  rw [← inv_inv (finiteHeckeEulerFactor χ v s), hE]
  exact (hasSum_geometric_of_norm_lt_one ha).mul_left _

local notation "ψv" => finiteLocalStandardCharacter F v

private def diskTest : K → ℂ := (O : Set K).indicator (fun _ ↦ 1)

private def primeMellin (χ : Unitary) (p : K → ℂ) (s : ℂ) :=
  ∫ u : Kˣ, p u.val * finitePlaceRestriction F v (ideleClassNormTwist χ s) u ∂νv

private theorem inverse_unramified (χ : Unitary) :
    (ideleClassNormTwist χ⁻¹ 0).IsUnramifiedAt v ↔ (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
  rw [finiteUnitary_unramified, finiteUnitary_unramified]
  apply forall_congr' fun u ↦ imp_congr_right fun _ ↦ ?_
  change (finiteUnitary v χ u)⁻¹ = 1 ↔ _
  exact inv_eq_one

private theorem diskTest_regular : IsLocallyConstant (diskTest v) ∧ HasCompactSupport (diskTest v) := by
  have ho : IsOpen (O : Set K) := Valued.isOpen_valuationSubring K
  have hc : IsCompact (O : Set K) := isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦ ?_,
    HasCompactSupport.of_support_subset_isCompact hc (support_indicator_subset ..)⟩
  by_cases hx : x ∈ O
  · filter_upwards [ho.mem_nhds hx] with y hy
    simp [diskTest, hx, hy]
  · filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [diskTest, hx, show y ∉ O from hy]

/-- The Mellin transforms of the local test and its Fourier transform expose
the different and conductor in their radial scale. -/
private theorem finite_pair_with_conductor (χ : Unitary) :
    ∃ (f : K → ℂ) (a b : ℂ) (q : ℝ), IsLocallyConstant f ∧ HasCompactSupport f ∧
      a ≠ 0 ∧ b ≠ 0 ∧ 0 < q ∧
      (∀ n : ℕ, IsLeast (finiteConductorLevels(F, χ, v)) n →
        q = (v.asIdeal.absNorm : ℝ) ^ (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) + n)) ∧
      (∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), primeMellin v χ f s = a * finiteHeckeEulerFactor χ v s) ∧
      (∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), primeMellin v χ⁻¹ (tamagawaFourier μv ψv f) s =
        b * (q : ℂ) ^ (s : ℂ) * finiteHeckeEulerFactor χ⁻¹ v s) := by
  let m : ℂ := (νv).real U
  have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr (unitMass_pos v).ne'
  by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · let d := multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
    let D := (v.asIdeal.absNorm : ℝ) ^ d
    let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨p, hp⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    let t := (Units.mk0 (p : K) hp.ne_zero)⁻¹ ^ d
    have ht : ‖t.val‖ = D := by simp [t, D, Units.val_pow_eq_pow_val, norm_pow, norm_inv,
      norm_uniformizer_adicCompletion v _ hp]
    have hD := ht ▸ norm_pos_iff.mpr t.ne_zero
    let M : ℂ := (μv).real (O : Set K)
    have hmass : M ≠ 0 := by
      have hμ : (μv).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
      let := hμ
      apply Complex.ofReal_ne_zero.mpr
      exact (ENNReal.toReal_pos ((Valued.isOpen_valuationSubring K).measure_pos μv ⟨0, (O).zero_mem⟩).ne'
        (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)).measure_ne_top).ne'
    have hraw (u : Kˣ) : tamagawaFourier μv ψv (diskTest v) (t * u).val = M * diskTest v u.val := by
      rw [diskTest, finiteLocalTamagawaFourier_integers]
      change _ * ({z : K | ‖z‖ ≤ D}.indicator _ (t * u).val) = M * _
      have hm' : M = _ := congrArg (fun x : ℝ≥0∞ ↦ (x.toReal : ℂ)) (finiteLocalAdditiveTamagawaMeasure_integers F v)
      rw [← hm']
      congr 1
      by_cases hu : u.val ∈ O
      · rw [indicator_of_mem hu, indicator_of_mem]
        exact (show ‖(t * u).val‖ ≤ D by rw [Units.val_mul, norm_mul, ht]; exact mul_le_of_le_one_right hD.le (Valued.toNormedField.norm_le_one_iff.mpr hu))
      · rw [indicator_of_notMem hu, indicator_of_notMem]
        change ¬ ‖(t * u).val‖ ≤ D
        rw [Units.val_mul, norm_mul, ht]
        exact (lt_mul_of_one_lt_right hD (lt_of_not_ge (hu ∘ Valued.toNormedField.norm_le_one_iff.mp))).not_ge
    have hscale (n : ℕ) (hn : IsLeast (finiteConductorLevels(F, χ, v)) n) :
        D = (v.asIdeal.absNorm : ℝ) ^ (d + n) := by
      have hz : 0 ∈ finiteConductorLevels(F, χ, v) :=
        fun u hu _ ↦ (finiteUnitary_unramified v χ).mp h u hu
      simp [Nat.eq_zero_of_le_zero (hn.2 hz), D]
    refine ⟨diskTest v, m, M * (finiteUnitary v χ⁻¹ t : ℂ) * m, D, (diskTest_regular v).1, (diskTest_regular v).2, hm,
      mul_ne_zero (mul_ne_zero hmass (Circle.coe_ne_zero _)) hm, hD, hscale, unramified_disk_zeta v χ h, ?_⟩
    intro s
    unfold primeMellin
    rw [← integral_mul_left_eq_self (μ := νv) _ t]
    simp_rw [hraw, map_mul]
    let C := M * finitePlaceRestriction F v (ideleClassNormTwist χ⁻¹ s) t
    have hprod (u : Kˣ) : M * diskTest v u.val * (finitePlaceRestriction F v (ideleClassNormTwist χ⁻¹ s) t * finitePlaceRestriction F v (ideleClassNormTwist χ⁻¹ s) u) =
        C * (diskTest v u.val * finitePlaceRestriction F v (ideleClassNormTwist χ⁻¹ s) u) := by dsimp [C]; ring
    rw [show (fun _ ↦ _) = _ from funext hprod, integral_const_mul]
    rw [show (∫ u : Kˣ, diskTest v u.val * _ ∂νv) = _ from unramified_disk_zeta v χ⁻¹ ((inverse_unramified v χ).mpr h) s]
    dsimp only [C, m]
    rw [finiteUnitary_eval, ht]
    ring
  · let ρ := finiteUnitary v χ
    have hram : ∃ u : Kˣ, ‖u.val‖ = 1 ∧ ρ u ≠ 1 := by
      by_contra! hn
      exact h ((finiteUnitary_unramified v χ).mpr hn)
    let f := finiteUnitTest v ρ
    let g := tamagawaFourier μv ψv f
    obtain ⟨y, hy⟩ := finiteFourier_unit_ne_zero v ρ
    have hy0 : y ≠ 0 := by
      rintro rfl
      obtain ⟨u, hu, hne⟩ := hram
      exact hne (finiteFourier_implies_unit_trivial v ρ hy u hu (by simp))
    let t := Units.mk0 y hy0
    have hdual (u : Kˣ) : (finiteUnitary v χ⁻¹ u : ℂ) = (ρ u : ℂ)⁻¹ := rfl
    refine ⟨f, m, m * g y * (finiteUnitary v χ⁻¹ t : ℂ), ‖y‖, (finiteUnitTest_regularity v ρ).1,
      (finiteUnitTest_regularity v ρ).2, hm, mul_ne_zero (mul_ne_zero hm hy) (Circle.coe_ne_zero _),
      norm_pos_iff.mpr hy0, fun n hn ↦ finiteFourier_conductor_radius v ρ hram hy n hn, ?_, ?_⟩
    · intro s
      have hz := shell_zeta v χ f 1 (fun u hu ↦ by simp [f, finiteUnitTest_unit] at hu ⊢; exact fun h ↦ (hu h).elim)
        (fun u hu ↦ by simp [f, ρ, finiteUnitTest_unit, hu, finiteUnitTest]) (s : ℂ)
      simpa [primeMellin, f, finiteUnitTest, m, finiteHeckeEulerFactor, h] using hz
    · intro s
      have hz := shell_zeta v χ⁻¹ g t (fun u hne ↦ by
        by_contra hn
        exact hne (le_antisymm (finiteFourier_common_radius v ρ hram hy hn)
          (finiteFourier_common_radius v ρ hram hn hy)))
        (fun u hu ↦ by rw [mul_comm, hdual, inv_inv]; exact finiteFourier_unit_covariant v ρ u hu y) (s : ℂ)
      simpa only [primeMellin, m, g, f, t, Units.val_mk0, finiteHeckeEulerFactor, ite_eq_right ((inverse_unramified v χ).not.mpr h), mul_one] using hz

/-- The two finite-place Mellin transforms are Euler factors times nonzero constants,
with one positive radial scale for the Fourier transform. -/
private theorem finite_pair (χ : Unitary) :
    ∃ (f : K → ℂ) (a b : ℂ) (q : ℝ), IsLocallyConstant f ∧ HasCompactSupport f ∧
      a ≠ 0 ∧ b ≠ 0 ∧ 0 < q ∧
      (∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), primeMellin v χ f s = a * finiteHeckeEulerFactor χ v s) ∧
      (∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), primeMellin v χ⁻¹ (tamagawaFourier μv ψv f) s =
        b * (q : ℂ) ^ (s : ℂ) * finiteHeckeEulerFactor χ⁻¹ v s) := by
  obtain ⟨f, a, b, q, hf, hfc, ha, hb, hq, _, hM, hN⟩ := finite_pair_with_conductor v χ
  exact ⟨f, a, b, q, hf, hfc, ha, hb, hq, hM, hN⟩

end FinitePlaceHeckeTests

section HeckeProductIntegral

open Function Filter Set MeasureTheory NumberField IsDedekindDomain Topology InfinitePlace.Completion
open scoped NNReal ENNReal NumberField.AdeleRing Pointwise Classical

variable (F : Type*) [Field F] [NumberField F]
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "I" => IdeleGroup (𝓞 F) F
private local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
private local instance (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
private local instance (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
  (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
private local instance (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
private local instance (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ := Units.isEmbedding_val₀.secondCountableTopology
private local instance (w : InfinitePlace F) : LocallyCompactSpace w.Completionˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).locallyCompactSpace
private local instance (v : V) : MeasurableSpace (v.adicCompletion F)ˣ := borel _
private local instance (v : V) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
private local instance (v : V) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
private local instance (v : V) : SecondCountableTopology (v.adicCompletion F)ˣ := Units.isEmbedding_val₀.secondCountableTopology
private local instance (v : V) : LocallyCompactSpace (v.adicCompletion F)ˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).locallyCompactSpace
private local instance (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
  infiniteLocalMultiplicativeTamagawaMeasure_haar F w
private local instance (v : V) : (finiteLocalMultiplicativeTamagawaMeasure F v).IsHaarMeasure :=
  finiteLocalMultiplicativeTamagawaMeasure_haar F v
private local instance : MeasurableSpace I := borel _
private local instance : BorelSpace I := ⟨rfl⟩
private local instance : Countable V := finitePlaces_countable F

private abbrev infiniteCoord (w : InfinitePlace F) :=
  Units.map ((Pi.evalRingHom _ w).comp (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom

private abbrev finiteCoord (v : V) :=
  Units.map ((RestrictedProduct.evalRingHom (fun w : V ↦ w.adicCompletion F) v).comp
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom

/-- The subgroup of ideles which are integer units outside the selected places. -/
private def stageTail (S : Finset V) : Set I := {g | ∀ v ∉ S, finiteCoord F v g ∈ (v.adicCompletionIntegers F).units}

private def stageCoords (S : Finset V) (g : I) : IdeleCoordinates F S :=
  (fun w ↦ infiniteCoord F w g, fun v ↦ finiteCoord F v.val g)

private theorem stageCoord_continuous (v : V) : Continuous (finiteCoord F v) :=
  (RestrictedProduct.continuous_eval v |>.comp continuous_snd).units_map _

private theorem stageCoords_continuous (S : Finset V) : Continuous (stageCoords F S) :=
  (continuous_pi (fun w ↦ ((continuous_apply w).comp continuous_fst).units_map _)).prodMk
    (continuous_pi fun v ↦ stageCoord_continuous F v.val)

private theorem stageTail_measurable (S : Finset V) : MeasurableSet (stageTail F S) := by
  unfold stageTail
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter; intro v
  apply MeasurableSet.iInter; intro _
  apply IsOpen.measurableSet
  exact (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _) |>.preimage (stageCoord_continuous F v))

private abbrev stageProductMeasure (S : Finset V) : Measure (IdeleCoordinates F S) :=
  (Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).prod
    (Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val)

/-- After including all primes of the different, projecting the subgroup of ideles integral and
invertible outside the selected places gives exactly the product of the local Haar measures. -/
private theorem stage_measurePreserving (S : Finset V)
    (hd : ∀ v ∉ S, multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) = 0) :
    MeasurePreserving (stageCoords F S) ((multiplicativeTamagawaMeasure F).restrict (stageTail F S))
      (stageProductMeasure F S) := by
  let μ := stageProductMeasure F S
  let μ₁ := Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)
  let μ₂ := Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val
  let : μ₁.IsHaarMeasure := Measure.pi.isHaarMeasure _
  let : μ₂.IsHaarMeasure := Measure.pi.isHaarMeasure _
  let : μ.IsHaarMeasure := Measure.prod.instIsHaarMeasure μ₁ μ₂
  obtain ⟨ν, hν, he⟩ := multiplicativeTamagawaMeasure_projected_haar F S
  let : ν.IsHaarMeasure := hν
  have hμ : ν = μ := by
    let c := ν.haarScalarFactor μ
    have hscale : ν = c • μ := Measure.isMulLeftInvariant_eq_smul ν μ
    choose B hBc hB using fun w : InfinitePlace F ↦ exists_compact_mem_nhds (1 : w.Completionˣ)
    choose E hEc hE using fun v : S ↦ exists_compact_mem_nhds (1 : (v.val.adicCompletion F)ˣ)
    let W := univ.pi B ×ˢ univ.pi E
    have hW : MeasurableSet W := (MeasurableSet.univ_pi fun w ↦ (hBc w).measurableSet).prod
      (MeasurableSet.univ_pi fun v ↦ (hEc v).measurableSet)
    have h0 : μ W ≠ 0 := (μ.measure_pos_of_mem_nhds <| prod_mem_nhds
      (set_pi_mem_nhds finite_univ fun w _ ↦ hB w)
      (set_pi_mem_nhds finite_univ fun v _ ↦ hE v)).ne'
    have htop : μ W ≠ ⊤ := ((isCompact_univ_pi hBc).prod (isCompact_univ_pi hEc)).measure_ne_top
    have hrect := he W hW
    simp only [W, mem_prod, mem_univ_pi, and_assoc] at hrect
    rw [multiplicativeTamagawaMeasure_restrictedProduct F S B (fun w ↦ (hBc w).measurableSet)
      E (fun v ↦ (hEc v).measurableSet)] at hrect
    have hdz (v : {v : V // v ∉ S}) := hd v.val v.property
    simp only [hdz, pow_zero, Real.sqrt_one, ENNReal.ofReal_one, inv_one,
      finprod_one, mul_one] at hrect
    have hrect' : ν W = μ W := by
      rw [hrect]
      change _ = (μ₁.prod μ₂) (univ.pi B ×ˢ univ.pi E)
      rw [Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
    have hc : (c : ℝ≥0∞) * μ W = 1 * μ W := by simpa [hscale] using hrect'
    have hc1 : c = 1 := ENNReal.coe_injective ((ENNReal.mul_left_inj h0 htop).mp hc)
    simpa [hc1] using hscale
  refine ⟨(stageCoords_continuous F S).measurable, ?_⟩
  ext W hW
  rw [Measure.map_apply (stageCoords_continuous F S).measurable hW,
    Measure.restrict_apply ((stageCoords_continuous F S).measurable hW)]
  change _ = μ W
  rw [← hμ, he _ hW]
  rfl

local notation "Unitary" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "Arch" => SchwartzBruhat (Multiplicative (SAdeleRing F ∅))
local notation "Global" => SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))
local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 F)))
private local instance (v : S₀) : MeasurableSpace (v.val.adicCompletion F) := borel _
private local instance (v : S₀) : IsProbabilityMeasure (finiteLocalMultiplicativeTamagawaMeasure F v.val) := isEmptyElim v
private local instance : MeasurableSpace (SAdeleRing F S₀) := instMeasurableSpaceSAdeleRing F S₀
private local instance : BorelSpace (SAdeleRing F S₀)ˣ := sIdele_borelSpace F S₀

private def archMellin (A : Arch) (c : HeckeCharacter (𝓞 F) F) :=
  ∫ g : (SAdeleRing F ∅)ˣ, A (Multiplicative.ofAdd g.val) *
    c (QuotientGroup.mk (sIdeleInsertion F ∅ g)) ∂sMultiplicativeTamagawaMeasure F ∅

private def archIntegrand (A : Arch) (c : HeckeCharacter (𝓞 F) F)
    (x : (w : InfinitePlace F) → w.Completionˣ) : ℂ :=
  A (Multiplicative.ofAdd (fun w ↦ (x w).val, 0)) * ∏ w, infinitePlaceRestriction F w c (x w)

/-- The archimedean Mellin integral in the coordinates of the infinite places. -/
private theorem archMellin_on_coordinates (A : Arch) (c : HeckeCharacter (𝓞 F) F) :
    archMellin F A c = ∫ x, archIntegrand F A c x ∂Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F) := by
  let e := (sIdeleUnitsEquiv F ∅).toHomeomorph.toMeasurableEquiv
  let μ := Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)
  let ν := Measure.pi (fun v : (∅ : Finset V) ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val)
  let G (g : (SAdeleRing F ∅)ˣ) := A (Multiplicative.ofAdd g.val) *
    c (QuotientGroup.mk (sIdeleInsertion F ∅ g))
  change (∫ u, G u ∂(μ.prod ν).map e) = _
  rw [e.measurableEmbedding.integral_map]
  have h (x) : G (e x) = archIntegrand F A c x.1 := by
    simp only [G, archIntegrand, sIdeleInsertion, MonoidHom.finsetProd_apply, Fintype.prod_empty, mul_one]
    change _ * c ((QuotientGroup.mk' _) _) = _
    rw [map_prod, map_prod]
    apply congrArg₂ (· * ·)
    · apply congrArg (fun z : SAdeleRing F ∅ ↦ A (Multiplicative.ofAdd z))
      exact Prod.ext rfl (Subsingleton.elim _ _)
    · rfl
  rw [show (fun x ↦ G (e x)) = _ from funext h, integral_fun_fst]
  simp [μ, ν, Measure.real]

/-- Every idele belongs to a stage with integer units outside finitely many places. -/
private theorem stageTail_iUnion : (⋃ T : Finset V, stageTail F T) = univ := by
  apply eq_univ_of_forall
  intro g
  have h := g.val.2.cofinite_mem_adicCompletionIntegers.and g.inv.2.cofinite_mem_adicCompletionIntegers
  let T := (Filter.eventually_cofinite.mp h).toFinset
  refine mem_iUnion.mpr ⟨T, ?_⟩
  intro v hv
  have hmem : g.val.2 v ∈ v.adicCompletionIntegers F ∧ g.inv.2 v ∈ v.adicCompletionIntegers F := by
    by_contra hn
    exact hv (by simpa [T] using hn)
  exact hmem

/-- Exhaust the ideles by their open finite stages. The product formula for the character and
Fubini factor the stage integrals, whose limit is the finite Hecke Euler product. -/
private theorem tensorZeta (S : Finset V)
    (hd : ∀ v ∉ S, multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) = 0)
    (A : Arch) (f : Global) (χ : Unitary) (s : Complex.re ⁻¹' Ioi (1 : ℝ))
    (p : (v : V) → v.adicCompletion F → ℂ) (hp : ∀ v, Continuous (p v))
    (wgt : V → ℂ) (hwgt : ∀ v ∉ S, wgt v = 1)
    (hχ : ∀ v ∉ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (hM : ∀ v, primeMellin v χ (p v) s = wgt v * finiteHeckeEulerFactor χ v s)
    (hf : ∀ T : Finset V, S ⊆ T → ∀ g ∈ stageTail F T,
      f (Multiplicative.ofAdd g.val) = A (Multiplicative.ofAdd (g.val.1, 0)) *
        ∏ v ∈ T, p v (g.val.2 v)) :
    globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
      (∏ v ∈ S, wgt v) * (archMellin F A (ideleClassNormTwist χ s) * finiteHeckeL χ s) := by
  let c := ideleClassNormTwist χ (s : ℂ)
  let μ := multiplicativeTamagawaMeasure F
  let z (g : I) := f (Multiplicative.ofAdd g.val) * c (QuotientGroup.mk g)
  have hInt : Integrable z μ := globalIdelicZetaIntegral_integrable f c (tate_twist_mem_rightHalf χ s s.property)
  have hlim := tendsto_setIntegral_of_monotone (stageTail_measurable F)
    (show Monotone (stageTail F) from fun T T' h g hg v hv ↦ hg v (fun h' ↦ hv (h h')))
    (hInt.integrableOn (s := ⋃ T : Finset V, stageTail F T))
  rw [stageTail_iUnion, setIntegral_univ] at hlim
  have hprod := (finiteHeckeL_hasProd χ s).const_mul (archMellin F A c * ∏ v ∈ S, wgt v)
  have he : (fun T : Finset V ↦ ∫ g in stageTail F T, z g ∂μ) =ᶠ[atTop]
      fun T ↦ (archMellin F A c * ∏ v ∈ S, wgt v) * ∏ v ∈ T, finiteHeckeEulerFactor χ v s := by
    filter_upwards [eventually_ge_atTop S] with T hST
    let R (v : V) (u : (v.adicCompletion F)ˣ) := p v u.val * finitePlaceRestriction F v c u
    let H (x : IdeleCoordinates F T) := archIntegrand F A c x.1 * ∏ v : T, R v.val (x.2 v)
    have hpres := stage_measurePreserving F T (fun v hv ↦ hd v (fun h ↦ hv (hST h)))
    have hH : Continuous H := by
      apply Continuous.mul
      · apply Continuous.comp (g := archIntegrand F A c) _ continuous_fst
        apply Continuous.mul
        · exact (schwartzBruhat_continuous A).comp <| continuous_ofAdd.comp <|
            (continuous_pi fun w ↦ Units.continuous_val.comp (continuous_apply w)).prodMk continuous_const
        · exact continuous_finsetProd _ fun w _ ↦ (infinitePlaceRestriction F w c).continuous.comp (continuous_apply w)
      · exact continuous_finsetProd _ fun v _ ↦ (((hp v.val).comp Units.continuous_val).mul
          (finitePlaceRestriction F v.val c).continuous).comp ((continuous_apply v).comp continuous_snd)
    have hz (g : I) (hg : g ∈ stageTail F T) : z g = H (stageCoords F T g) := by
      have hloc (v : V) (hv : v ∉ T) : finitePlaceRestriction F v c (finiteCoord F v g) = 1 := by
        have hn := (finiteUnit_norm v _).mp (hg v hv)
        rw [show c = _ from rfl, finiteUnitary_eval, (finiteUnitary_unramified v χ).mp (hχ v (fun h ↦ hv (hST h))) _ hn, hn]
        simp
      have hch := (heckeCharacter_eq_prod_restrictions F c g).2
      rw [finprod_eq_prod_of_mulSupport_subset (s := T) _ (fun v hv ↦ by
        by_contra h; exact hv (hloc v h))] at hch
      dsimp only [z, H, archIntegrand, stageCoords, R]
      rw [hf T hST g hg, hch, Finset.prod_mul_distrib]
      rw [← Finset.prod_subtype T (fun _ ↦ Iff.rfl) (fun v ↦ p v ((finiteCoord F v g).val)),
        ← Finset.prod_subtype T (fun _ ↦ Iff.rfl) (fun v ↦ finitePlaceRestriction F v c (finiteCoord F v g))]
      change (_ * _) * (_ * _) = (_ * _) * (_ * _)
      exact mul_mul_mul_comm _ _ _ _
    rw [setIntegral_congr_fun (stageTail_measurable F T) hz]
    rw [← integral_map hpres.measurable.aemeasurable (hH.aestronglyMeasurable), hpres.map_eq]
    change (∫ x : IdeleCoordinates F T, archIntegrand F A c x.1 * (∏ v : T, R v.val (x.2 v))
      ∂(Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).prod
        (Measure.pi fun v : T ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val)) = _
    rw [integral_prod_mul (archIntegrand F A c) (fun x : ((v : T) → (v.val.adicCompletion F)ˣ) ↦ ∏ v : T, R v.val (x v)),
      ← archMellin_on_coordinates, integral_fintype_prod_eq_prod (fun v : T ↦ R v.val)]
    have hv (v : T) : (∫ u, R v.val u ∂finiteLocalMultiplicativeTamagawaMeasure F v.val) =
        wgt v.val * finiteHeckeEulerFactor χ v.val s := hM _
    simp_rw [hv]
    rw [Finset.prod_mul_distrib, ← Finset.prod_subtype T (fun _ ↦ Iff.rfl) wgt,
      ← Finset.prod_subtype T (fun _ ↦ Iff.rfl) (fun v ↦ finiteHeckeEulerFactor χ v s)]
    rw [← Finset.prod_subset hST (fun v _ hn ↦ hwgt v hn)]
    ring
  have hfinal := tendsto_nhds_unique (hlim.congr' he) hprod
  change (∫ g, z g ∂μ) = _
  rw [hfinal]
  ring

end HeckeProductIntegral

section PartialHeckeTensor

open Function Filter Set MeasureTheory NumberField IsDedekindDomain Topology InfinitePlace.Completion
open scoped NNReal ENNReal NumberField.AdeleRing Pointwise Classical TensorProduct PiTensorProduct

variable (F : Type*) [Field F] [NumberField F]
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "Arch" => SchwartzBruhat (Multiplicative (SAdeleRing F ∅))
local notation "Global" => SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))
private local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
private local instance (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
private local instance (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
  (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
private local instance (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
  infiniteLocalAdditiveTamagawaMeasure_haar F w
private local instance (v : V) : MeasurableSpace (v.adicCompletion F) := borel _
private local instance (v : V) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
private local instance (v : V) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
private local instance (v : V) : (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
  finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
private local instance (v : S₀) : IsProbabilityMeasure (finiteLocalAdditiveTamagawaMeasure F v.val) := isEmptyElim v
private local instance (S : Finset V) : MeasurableSpace (SAdeleRing F S) := instMeasurableSpaceSAdeleRing F S
private local instance (S : Finset V) : BorelSpace (SAdeleRing F S) := inferInstanceAs (BorelSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
private local instance (S : Finset V) : T2Space (SAdeleRing F S) := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
private local instance (S : Finset V) : T2Space (Multiplicative (SAdeleRing F S)) := inferInstanceAs (T2Space (SAdeleRing F S))
private local instance (S : Finset V) : LocallyCompactSpace (Multiplicative (SAdeleRing F S)) := inferInstanceAs (LocallyCompactSpace (SAdeleRing F S))
private local instance (S : Finset V) : BorelSpace (Multiplicative (SAdeleRing F S)) := inferInstanceAs (BorelSpace (SAdeleRing F S))

private def archFT (A : Arch) := tamagawaFourier (sAdditiveTamagawaMeasure F ∅) (sAdeleStandardCharacter F ∅)
      (fun x ↦ A (Multiplicative.ofAdd x))

private def finiteFT (v : V) (p : v.adicCompletion F → ℂ) :=
  tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v) (finiteLocalStandardCharacter F v) p

private def partialTensor (S : Finset V) (A : Arch) (p : (v : S) → v.val.adicCompletion F → ℂ)
    (x : SAdeleRing F S) :=
  A (Multiplicative.ofAdd (x.1, 0)) * ∏ v : S, p v (x.2 v)

/-- The tensor of the archimedean test and the selected compactly supported locally constant
functions is Schwartz–Bruhat on the partial adeles. -/
private theorem partialTensor_schwartz (S : Finset V) (A : Arch) (p : (v : S) → v.val.adicCompletion F → ℂ)
    (hp : ∀ v, IsLocallyConstant (p v) ∧ HasCompactSupport (p v)) :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)), ∀ x, f (Multiplicative.ofAdd x) = partialTensor F S A p x := by
  let G := Multiplicative (InfiniteAdeleRing F)
  let : T2Space G := inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))
  let : LocallyCompactSpace G := InfiniteAdeleRing.locallyCompactSpace F
  let e : Multiplicative (SAdeleRing F ∅) ≃ₜ* G :=
    { toMulEquiv := (AddEquiv.prodUnique (M := InfiniteAdeleRing F)
        (N := (v : S₀) → v.val.adicCompletion F)).toMultiplicative
      continuous_toFun := continuous_fst
      continuous_invFun := continuous_id.prodMk continuous_const }
  let A' : SchwartzBruhat G := ⟨_, schwartzBruhat_mem_comp_equiv e.symm A.property⟩
  choose g hg using fun v : S ↦ (mem_finitePlaceSchwartz_iff F v.val (p v)).mpr (hp v)
  obtain ⟨E, hE⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  refine ⟨E (A' ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)), fun x ↦ ?_⟩
  rw [hE]
  simp_rw [hg]
  apply congrArg (· * ∏ v, p v (x.2 v))
  apply congrArg (fun z : SAdeleRing F ∅ ↦ A (Multiplicative.ofAdd z))
  exact Prod.ext rfl (Subsingleton.elim _ _)

/-- A Schwartz-Bruhat function on the `S`-adeles is integrable for the additive Tamagawa measure. -/
theorem partialTensor_integrable (S : Finset V) (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    Integrable (fun x ↦ f (Multiplicative.ofAdd x)) (sAdditiveTamagawaMeasure F S) := by
  let G := Multiplicative (SAdeleRing F S)
  let m : Measure G := sAdditiveTamagawaMeasure F S
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hm : (sAdditiveTamagawaMeasure F S).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let : m.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hm.toIsFiniteMeasureOnCompacts, toIsOpenPosMeasure := hm.toIsOpenPosMeasure,
      map_mul_left_eq_self := fun x ↦ hm.map_add_left_eq_self x.toAdd }
  exact schwartzBruhat_integrable m f

private def archFourierIntegrand (A : Arch) (y x : InfiniteAdeleRing F) : ℂ :=
  A (Multiplicative.ofAdd (x, 0)) * star (sAdeleStandardCharacter F ∅ (x * y, 0) : ℂ)

private def finiteFourierIntegrand (v : V) (p : v.adicCompletion F → ℂ)
    (y x : v.adicCompletion F) : ℂ := p x * star (finiteLocalStandardCharacter F v (x * y) : ℂ)

private theorem archFT_on_coordinates (A : Arch) (y : InfiniteAdeleRing F) :
    archFT F A (y, 0) = ∫ x, archFourierIntegrand F A y x ∂Measure.pi (infiniteLocalAdditiveTamagawaMeasure F) := by
  let μ := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
  let ν := Measure.pi (fun v : S₀ ↦ finiteLocalAdditiveTamagawaMeasure F v.val)
  have h (x : SAdeleRing F ∅) : A (Multiplicative.ofAdd x) *
      star (sAdeleStandardCharacter F ∅ (x * (y, 0)) : ℂ) = archFourierIntegrand F A y x.1 := by
    have hx : x = (x.1, 0) := Prod.ext rfl (Subsingleton.elim _ _)
    have hxy : x * (y, 0) = (x.1 * y, 0) := Prod.ext rfl (Subsingleton.elim _ _)
    exact congrArg₂ (· * ·) (congrArg (fun z : SAdeleRing F ∅ ↦ A (Multiplicative.ofAdd z)) hx)
      (congrArg (fun z : SAdeleRing F ∅ ↦ star (sAdeleStandardCharacter F ∅ z : ℂ)) hxy)
  refine (integral_congr_ae (μ := μ.prod ν) (ae_of_all _ h)).trans ?_
  rw [integral_fun_fst]
  simp [ν, Measure.real, μ]

private theorem partialTensor_fourierIntegrand (S : Finset V) (A : Arch)
    (p : (v : S) → v.val.adicCompletion F → ℂ) (y x : SAdeleRing F S) :
    partialTensor F S A p x * star (sAdeleStandardCharacter F S (x * y) : ℂ) =
      archFourierIntegrand F A y.1 x.1 * ∏ v : S, finiteFourierIntegrand F v.val (p v) (y.2 v) (x.2 v) := by
  simp only [partialTensor, archFourierIntegrand, finiteFourierIntegrand, sAdeleStandardCharacter,
    Fintype.prod_empty, mul_one, Circle.coe_mul, star_mul', Finset.prod_mul_distrib]
  rw [show (star ((∏ v : S, finiteLocalStandardCharacter F v.val ((x * y).2 v) : Circle) : ℂ)) =
    ∏ v : S, star (finiteLocalStandardCharacter F v.val (x.2 v * y.2 v) : ℂ) by
      change (starRingEnd ℂ) (Circle.coeHom _) = _
      rw [map_prod, map_prod]; rfl]
  exact mul_mul_mul_comm _ _ _ _

/-- The trace Fourier transform of the finite tensor is the product of the local transforms. -/
private theorem partialTensor_fourier (S : Finset V) (A : Arch) (p : (v : S) → v.val.adicCompletion F → ℂ)
    (y : SAdeleRing F S) :
    tamagawaFourier (sAdditiveTamagawaMeasure F S) (sAdeleStandardCharacter F S) (partialTensor F S A p) y =
      archFT F A (y.1, 0) * ∏ v : S, finiteFT F v.val (p v) (y.2 v) := by
  let μ := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
  let ν := Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)
  let Q (v : S) := finiteFourierIntegrand F v.val (p v) (y.2 v)
  refine (integral_congr_ae (μ := μ.prod ν) (ae_of_all _ (partialTensor_fourierIntegrand F S A p y))).trans ?_
  refine (integral_prod_mul (μ := μ) (ν := ν) (archFourierIntegrand F A y.1)
    (fun z : ((v : S) → v.val.adicCompletion F) ↦ ∏ v, Q v (z v))).trans ?_
  exact congrArg₂ (· * ·) (archFT_on_coordinates F A y.1).symm
    (integral_fintype_prod_eq_prod (μ := fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val) Q)


private local instance : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _

private theorem finiteFT_continuous (v : V) (f : v.adicCompletion F → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) : Continuous (finiteFT F v f) := by
  let μ := finiteLocalAdditiveTamagawaMeasure F v
  obtain ⟨ρ, hρ, -⟩ := finiteLocalStandardCharacter_exists_continuousMonoidHom F v
  have hψ : Continuous (finiteLocalStandardCharacter F v) := (ρ.continuous.comp continuous_ofAdd).congr hρ
  let ψ (x : v.adicCompletion F) := (finiteLocalStandardCharacter F v x : ℂ)
  have hcont : Continuous ψ := continuous_subtype_val.comp hψ
  apply continuous_of_dominated (μ := μ) (bound := fun x ↦ ‖f x‖)
  · intro y
    exact (hf.mul (hcont.comp (continuous_id.mul_const y)).star).aestronglyMeasurable
  · exact fun y ↦ ae_of_all μ (fun x ↦ by simp)
  · exact (hf.integrable_of_hasCompactSupport (μ := μ) hc).norm
  · exact ae_of_all μ fun x ↦ continuous_const.mul (hcont.comp (continuous_const.mul continuous_id)).star

/-- An adele lies in `integralAdelesOutside F S` exactly when each of its components outside `S` is
a local integer. -/
theorem integralTail_iff (S : Finset V) (x : AdeleRing (𝓞 F) F) :
    x ∈ integralAdelesOutside F S ↔ ∀ v ∉ S, x.2 v ∈ v.adicCompletionIntegers F := by
  simp only [integralAdelesOutside, Subring.mem_iInf]
  rfl

private def integerTailTensor (S : Finset V) (A : Arch) (p : (v : S) → v.val.adicCompletion F → ℂ)
    (x : AdeleRing (𝓞 F) F) :=
  (integralAdelesOutside F S : Set (AdeleRing (𝓞 F) F)).indicator
    (fun x ↦ partialTensor F S A p (adeleProjection F S x)) x

private theorem tailDual_eq_integers (S : Finset V)
    (hd : ∀ v ∉ S, multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) = 0) :
    sAdeleTailDual F S = (integralAdelesOutside F S : Set (AdeleRing (𝓞 F) F)) := by
  ext y
  refine Iff.trans ?_ (integralTail_iff F S y).symm
  change (∀ v ∉ S, ‖y.2 v‖ ≤ _) ↔ _
  apply forall_congr' fun v ↦ imp_congr_right fun hv ↦ ?_
  rw [hd v hv, pow_zero]
  exact Valued.toNormedField.norm_le_one_iff

/-- At a stage containing the different, the Fourier lift formula has the same
integer tail on both sides and no factor from the omitted places. -/
theorem adeleSchwartzFourier_sAdeleSchwartzToGlobal_of_different (S : Finset V)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f g : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (hg :
      letI : MeasurableSpace (SAdeleRing F S) :=
        (@MeasurableSpace.pi _ _ (fun w : InfinitePlace F ↦ borel w.Completion)).prod
          (@MeasurableSpace.pi _ _ (fun v : S ↦ borel (v.val.adicCompletion F)))
      tamagawaFourier (sAdditiveTamagawaMeasure F S) (sAdeleStandardCharacter F S)
        (fun x ↦ f (Multiplicative.ofAdd x)) = fun y ↦ g (Multiplicative.ofAdd y)) :
    adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f) =
      sAdeleSchwartzToGlobal F S g := by
  classical
  have hd (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) = 0 :=
    multiplicity_eq_zero_of_not_dvd (fun h ↦ hv (hgood v h))
  have hp := sAdeleProjection_restrict F S ∅ (Finset.disjoint_empty_right _)
    (by simpa only [Finset.union_empty] using hd) (fun _ ↦ Set.univ)
    (fun _ ↦ MeasurableSet.univ) 1 (by simp)
  have hft := tamagawaFourier_sAdeleLift F S 1 (by simpa using hp)
    (fun x ↦ f (Multiplicative.ofAdd x)) (partialTensor_integrable F S f)
  dsimp only at hft
  rw [tailDual_eq_integers F S hd, NNReal.coe_one, one_smul, hg] at hft
  let I : Set 𝔸[F] := integralAdelesOutside F S
  have hlift (g : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (x : 𝔸[F]) :
      sAdeleSchwartzToGlobal F S g (Multiplicative.ofAdd x) =
      I.indicator ((fun z ↦ g (Multiplicative.ofAdd z)) ∘ adeleProjection F S) x := by
    rw [sAdeleSchwartzToGlobal_apply]
    by_cases hx : x ∈ integralAdelesOutside F S
    · rw [Set.indicator_of_mem hx, ite_eq_left ((integralTail_iff F S x).mp hx)]; rfl
    · rw [Set.indicator_of_notMem hx, ite_eq_right ((integralTail_iff F S x).not.mp hx)]
  apply Subtype.ext
  funext y
  let : MeasurableSpace 𝔸[F] := borel _
  let ft : (𝔸[F] → ℂ) → 𝔸[F] → ℂ := tamagawaFourier (additiveTamagawaMeasure F) (adeleStandardCharacter F)
  change ft (fun x ↦ sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd x)) y.toAdd = _
  exact (congrArg (fun g ↦ ft g y.toAdd) (funext (hlift f))).trans
    ((congrFun hft y.toAdd).trans (hlift g y.toAdd).symm)

private theorem partialTensor_lift_apply (S : Finset V) (A : Arch)
    (p : (v : S) → v.val.adicCompletion F → ℂ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (hf : ∀ x, f (Multiplicative.ofAdd x) = partialTensor F S A p x) (x : AdeleRing (𝓞 F) F) :
    sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd x) = integerTailTensor F S A p x := by
  refine (sAdeleSchwartzToGlobal_apply F S f x).trans ?_
  by_cases h : x ∈ integralAdelesOutside F S
  · exact ((ite_eq_left ((integralTail_iff F S x).mp h)).trans (hf _)).trans
      (indicator_of_mem h (partialTensor F S A p ∘ adeleProjection F S)).symm
  · exact (ite_eq_right ((integralTail_iff F S x).not.mp h)).trans
      (indicator_of_notMem h (partialTensor F S A p ∘ adeleProjection F S)).symm

/-- Extending the partial tensor by the integer indicators commutes up to a nonzero scalar
with the Fourier transform when all primes of the different are retained. -/
private theorem globalTensor_fourier (S : Finset V)
    (hd : ∀ v ∉ S, multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) = 0)
    (A B : Arch) (c : ℂ) (hc : c ≠ 0)
    (hFourier : ∀ y, archFT F A y = c * B (Multiplicative.ofAdd y))
    (p : (v : S) → v.val.adicCompletion F → ℂ)
    (hp : ∀ v, IsLocallyConstant (p v) ∧ HasCompactSupport (p v)) :
    ∃ (f : Global) (k : ℂ), k ≠ 0 ∧
      (∀ x, f (Multiplicative.ofAdd x) = integerTailTensor F S A p x) ∧
      (∀ x, adeleSchwartzFourier f (Multiplicative.ofAdd x) =
          integerTailTensor F S (k • B) (fun v ↦ finiteFT F v.val (p v)) x) := by
  let hpartial := partialTensor_schwartz F S A p hp
  let fS := hpartial.choose
  have hfS := hpartial.choose_spec
  let f := sAdeleSchwartzToGlobal F S fS
  have hf := partialTensor_lift_apply F S A p fS hfS
  let hmasses := sAdeleProjection_dual_masses F S
  let m := hmasses.choose
  have hm := hmasses.choose_spec.1
  have hpres := hmasses.choose_spec.2.2.1
  refine ⟨f, ((m : ℝ) : ℂ) * c, mul_ne_zero (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hm)) hc, hf, ?_⟩
  intro x
  have hfun : (fun x ↦ fS (Multiplicative.ofAdd x)) = partialTensor F S A p := funext hfS
  have hraw := tamagawaFourier_sAdeleLift F S m hpres (partialTensor F S A p)
    (hfun ▸ partialTensor_integrable F S fS)
  have htail := tailDual_eq_integers F S hd
  let ft := tamagawaFourier (additiveTamagawaMeasure F) (adeleStandardCharacter F)
  change ft (fun x ↦ f (Multiplicative.ofAdd x)) x = _
  refine (congrArg (fun h : AdeleRing (𝓞 F) F → ℂ ↦ ft h x) (funext hf)).trans ?_
  refine (congrFun hraw x).trans ?_
  let L (y : SAdeleRing F S) := (m : ℝ) • tamagawaFourier (sAdditiveTamagawaMeasure F S)
    (sAdeleStandardCharacter F S) (partialTensor F S A p) y
  let P (v : S) := finiteFT F v.val (p v)
  let R := partialTensor F S ((((m : ℝ) : ℂ) * c) • B) P
  refine (congrArg (fun T : Set (AdeleRing (𝓞 F) F) ↦ T.indicator (L ∘ adeleProjection F S) x) htail).trans ?_
  by_cases hx : x ∈ integralAdelesOutside F S
  · refine (indicator_of_mem hx (L ∘ adeleProjection F S)).trans (Eq.trans ?_
      (indicator_of_mem hx (R ∘ adeleProjection F S)).symm)
    let y := adeleProjection F S x
    let W := ∏ v : S, P v (y.2 v)
    have hloc := partialTensor_fourier F S A p y
    have hA := hFourier (y.1, 0)
    have hmul (a b c d : ℂ) : a * ((b * c) * d) = ((a * b) * c) * d :=
      (mul_assoc _ _ _).symm.trans (congrArg (· * d) (mul_assoc _ _ _).symm)
    exact (congrArg (fun z : ℂ ↦ ((m : ℝ) : ℂ) * z) hloc).trans
      ((congrArg (fun z : ℂ ↦ ((m : ℝ) : ℂ) * (z * W)) hA).trans (hmul _ _ _ _))
  · exact (indicator_of_notMem hx (L ∘ adeleProjection F S)).trans
      (indicator_of_notMem hx (R ∘ adeleProjection F S)).symm

/-- On a finite idelic stage the omitted integer-ring indicators give just the missing finite factors. -/
private theorem integerTail_on_stage (S : Finset V) (A : Arch)
    (p : (v : V) → v.adicCompletion F → ℂ) (hp : ∀ v ∉ S, p v = diskTest v)
    (T : Finset V) (hST : S ⊆ T) (g : IdeleGroup (𝓞 F) F) (hg : g ∈ stageTail F T) :
    integerTailTensor F S A (fun v ↦ p v.val) g.val =
      A (Multiplicative.ofAdd (g.val.1, 0)) * ∏ v ∈ T, p v (g.val.2 v) := by
  by_cases h : g.val ∈ integralAdelesOutside F S
  · rw [integerTailTensor, indicator_of_mem h, partialTensor]
    change _ * (∏ v : S, p v.val (g.val.2 v.val)) = _
    rw [← Finset.prod_subtype S (fun _ ↦ Iff.rfl) (fun v ↦ p v (g.val.2 v)),
      Finset.prod_subset hST (fun v _ hn ↦ by
        rw [hp v hn, diskTest, indicator_of_mem ((integralTail_iff F S _).mp h v hn)])]
    rfl
  · rw [integerTailTensor, indicator_of_notMem h]
    obtain ⟨v, hv, hnv⟩ : ∃ v ∉ S, g.val.2 v ∉ v.adicCompletionIntegers F := by
      by_contra! hh
      exact h ((integralTail_iff F S _).mpr hh)
    have hvT : v ∈ T := by by_contra hc; exact hnv (hg v hc).1
    rw [Finset.prod_eq_zero hvT (by rw [hp v hv, diskTest, indicator_of_notMem hnv]), mul_zero]

private theorem primeMellin_good (v : V) (hd : multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) = 0)
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (hχ : (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (s : Complex.re ⁻¹' Ioi (1 : ℝ)) :
    primeMellin v χ (diskTest v) s = finiteHeckeEulerFactor χ v s := by
  have h := unramified_disk_zeta v χ hχ s
  simpa only [primeMellin, diskTest, localIntegerUnits, Measure.real, finiteLocalMultiplicativeTamagawaMeasure_integerUnits,
    hd, pow_zero, Real.sqrt_one, ENNReal.ofReal_one, inv_one, ENNReal.toReal_one, Complex.ofReal_one, one_mul] using h

private theorem archMellin_scale (B : Arch) (k : ℂ) (c : HeckeCharacter (𝓞 F) F) :
    archMellin F (k • B) c = k * archMellin F B c := by
  let G (u : (SAdeleRing F ∅)ˣ) := B (Multiplicative.ofAdd u.val) * c (QuotientGroup.mk (sIdeleInsertion F ∅ u))
  have h (u : (SAdeleRing F ∅)ˣ) : (k • B) (Multiplicative.ofAdd u.val) * c (QuotientGroup.mk (sIdeleInsertion F ∅ u)) = k * G u :=
    mul_assoc k _ _
  exact (integral_congr_ae (μ := sMultiplicativeTamagawaMeasure F ∅) (ae_of_all _ h)).trans
    (integral_const_mul k G)

private theorem prod_real_cpow {ι : Type*} (S : Finset ι) (q : ι → ℝ) (hq : ∀ v, 0 < q v) (s : ℂ) :
    (∏ v ∈ S, (q v : ℂ) ^ s) = ((∏ v ∈ S, q v) : ℝ) ^ s := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hq i).le (Finset.prod_nonneg (fun v _ ↦ (hq v).le)) s]
end PartialHeckeTensor

section

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Arch" => SchwartzBruhat (Multiplicative (SAdeleRing F ∅))
local notation "Global" => SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))

/-- Multiplying the local Fourier scales adds the logarithms of the absolute
discriminant and of the finite conductor. -/
private theorem hecke_log_prod_conductor_scale (S : Finset (HeightOneSpectrum (𝓞 F)))
    (n : HeightOneSpectrum (𝓞 F) → ℕ) (q : HeightOneSpectrum (𝓞 F) → ℝ)
    (hd : ∀ v ∉ S, multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) = 0)
    (hn : ∀ v ∉ S, n v = 0)
    (hq : ∀ v ∈ S, q v = (v.asIdeal.absNorm : ℝ) ^ (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) + n v)) :
    Real.log (∏ v ∈ S, q v) = Real.log ((NumberField.discr F).natAbs : ℝ) +
      ∑ᶠ v, Real.log (v.asIdeal.absNorm : ℝ) * (n v : ℝ) := by
  classical
  let J := differentIdeal ℤ (𝓞 F)
  let d (v : HeightOneSpectrum (𝓞 F)) := multiplicity v.asIdeal J
  have hnorm (v : HeightOneSpectrum (𝓞 F)) : 0 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).trans' Nat.zero_lt_one
  have hfactor : ∏ v ∈ S, v.asIdeal ^ d v = J := by
    rw [← finprod_eq_finsetProd_of_mulSupport_subset (f := fun v ↦ v.asIdeal ^ d v)]
    · exact Ideal.finprod_heightOneSpectrum_pow_multiplicity differentIdeal_ne_bot
    · intro v hv
      by_contra hx
      exact hv (by simp [d, J, hd v hx])
  have hD : (∏ v ∈ S, (v.asIdeal.absNorm : ℝ) ^ d v) = ((NumberField.discr F).natAbs : ℝ) := by
    exact_mod_cast (by
      simpa only [map_prod, map_pow, J, NumberField.absNorm_differentIdeal F (𝓞 F)] using
        congrArg (fun I : Ideal (𝓞 F) ↦ Ideal.absNorm I) hfactor :
        (∏ v ∈ S, v.asIdeal.absNorm ^ d v) = (NumberField.discr F).natAbs)
  have hs : Function.support (fun v : HeightOneSpectrum (𝓞 F) ↦ Real.log (v.asIdeal.absNorm : ℝ) *
      (n v : ℝ)) ⊆ S := by
    intro v hv
    by_contra hx
    exact hv (by simp [hn v hx])
  rw [← hD, Real.log_prod (fun v hv ↦ (hq v hv).symm ▸ pow_ne_zero _ (hnorm v).ne'),
    Real.log_prod (fun v _ ↦ pow_ne_zero _ (hnorm v).ne'), finsum_eq_sum_of_support_subset _ hs,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v hv ↦ ?_
  rw [hq v hv, Real.log_pow, Real.log_pow, Nat.cast_add, add_mul, mul_comm (n v : ℝ)]

/-- The explicit finite Fourier scales multiply to the discriminant times the conductor. -/
private theorem exists_globalHeckeTest_fourier_with_conductor (χ : U[F])
    (fArch fArchDual : SchwartzBruhat (Multiplicative (SAdeleRing F ∅)))
    (c : ℂ) (hc : c ≠ 0)
    (hFourier : ∀ y, archimedeanFourier fArch y = c * fArchDual (Multiplicative.ofAdd y)) :
    ∃ (f : ℬ[F]) (a b : ℂ) (q : ℝ), a ≠ 0 ∧ b ≠ 0 ∧ 0 < q ∧
      (∀ n : V → ℕ, (∀ v, IsLeast (finiteConductorLevels(F, χ, v)) (n v)) →
        Real.log q = finiteConductorLog(F, n)) ∧
      (∀ s : halfPlane, globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
        a * (archimedeanZeta fArch (ideleClassNormTwist χ s) * finiteHeckeL χ s)) ∧
      (∀ s : halfPlane,
        globalIdelicZetaIntegral (adeleSchwartzFourier f) (ideleClassNormTwist χ⁻¹ s) =
          (b * (q : ℂ) ^ (s : ℂ)) *
            (archimedeanZeta fArchDual (ideleClassNormTwist χ⁻¹ s) * finiteHeckeL χ⁻¹ s)) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T, ideleClassNormTwist χ 0 ∈ unramifiedOutside F T :=
    mem_iUnion.mp ((iUnion_unramifiedOutside F).symm ▸ mem_univ _)
  let D := (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).toFinset
  let S := T ∪ D
  have hd (v : V) (hv : v ∉ S) : multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    intro h
    exact hv (Finset.mem_union_right T (by simpa [D] using h))
  have hχ (v : V) (hv : v ∉ S) : (ideleClassNormTwist χ 0).IsUnramifiedAt v :=
    hT v (fun h ↦ hv (Finset.mem_union_left _ h))
  choose p a b q hp hpc ha hb hq hscale hM hN using fun v : V ↦ finite_pair_with_conductor v χ
  let r (v : V) := finiteFT F v (p v)
  obtain ⟨f, k, hk, hf, hg⟩ := globalTensor_fourier F S hd fArch fArchDual c hc hFourier
    (fun v ↦ p v.val) (fun v ↦ ⟨hp v.val, hpc v.val⟩)
  let extend (p : (v : V) → v.adicCompletion F → ℂ) (v : V) := if v ∈ S then p v else diskTest v
  let weight (m : V → ℂ) (v : V) := if v ∈ S then m v else 1
  have hExt (Q : (v : V) → v.adicCompletion F → ℂ) (v : V) (hv : v ∉ S) :
      extend Q v = diskTest v := ite_eq_right hv
  have hpc' (Q : (v : V) → v.adicCompletion F → ℂ) (h : ∀ v, Continuous (Q v)) (v : V) : Continuous (extend Q v) := by
    by_cases hv : v ∈ S
    · simpa [extend, hv] using h v
    · rw [hExt Q v hv]; exact (diskTest_regular v).1.continuous
  have hStage (A' : Arch) (g : Global) (P : (v : V) → v.adicCompletion F → ℂ)
      (h : ∀ x, g (Multiplicative.ofAdd x) = integerTailTensor F S A' (fun v ↦ P v.val) x)
      (T' : Finset V) (hST : S ⊆ T') (u : IdeleGroup (𝓞 F) F) (hu : u ∈ stageTail F T') :
      g (Multiplicative.ofAdd u.val) = A' (Multiplicative.ofAdd (u.val.1, 0)) * ∏ v ∈ T', extend P v (u.val.2 v) := by
    rw [h]
    have he : (fun v : S ↦ extend P v.val) = fun v : S ↦ P v.val := funext fun v ↦ ite_eq_left v.property
    simpa only [he] using integerTail_on_stage F S A' (extend P) (hExt P) T' hST u hu
  have hwgt (m : V → ℂ) (v : V) (hv : v ∉ S) : weight m v = 1 := ite_eq_right hv
  have hwp (m : V → ℂ) : (∏ v ∈ S, weight m v) = ∏ v ∈ S, m v :=
    Finset.prod_congr rfl fun v hv ↦ ite_eq_left hv
  refine ⟨f, ∏ v ∈ S, a v, (∏ v ∈ S, b v) * k, ∏ v ∈ S, q v,
    Finset.prod_ne_zero_iff.mpr (fun v _ ↦ ha v),
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun v _ ↦ hb v)) hk, Finset.prod_pos (fun v _ ↦ hq v), ?_, ?_, ?_⟩
  · intro n hn
    apply hecke_log_prod_conductor_scale S n q hd _ (fun v _ ↦ hscale v (n v) (hn v))
    intro v hv
    exact Nat.eq_zero_of_le_zero ((hn v).2
      (fun u hu _ ↦ (finiteUnitary_unramified v χ).mp (hχ v hv) u hu))
  · intro s
    have hloc (v : V) : primeMellin v χ (extend p v) s = weight a v * finiteHeckeEulerFactor χ v s := by
      by_cases hv : v ∈ S
      · simpa [extend, weight, hv] using hM v s
      · simpa [extend, weight, hv] using primeMellin_good F v (hd v hv) χ (hχ v hv) s
    exact (tensorZeta F S hd fArch f χ s (extend p) (hpc' p (fun v ↦ (hp v).continuous))
      (weight a) (hwgt a) hχ hloc (hStage fArch f p hf)).trans (congrArg (· * _) (hwp a))
  · intro s
    let m (v : V) := b v * (q v : ℂ) ^ (s : ℂ)
    have hχ' (v : V) (hv : v ∉ S) := (inverse_unramified v χ).mpr (hχ v hv)
    have hloc (v : V) : primeMellin v χ⁻¹ (extend r v) s = weight m v * finiteHeckeEulerFactor χ⁻¹ v s := by
      by_cases hv : v ∈ S
      · simpa only [extend, weight, ite_eq_left hv, m, r, finiteFT] using hN v s
      · simpa [extend, weight, hv] using primeMellin_good F v (hd v hv) χ⁻¹ (hχ' v hv) s
    have hrc (v) := finiteFT_continuous F v (p v) (hp v).continuous (hpc v)
    refine (tensorZeta F S hd (k • fArchDual) _ χ⁻¹ s (extend r) (hpc' r hrc) _ (hwgt m) hχ' hloc
      (hStage (k • fArchDual) _ r hg)).trans ?_
    let t : ℂ := ((∏ v ∈ S, q v : ℝ) : ℂ)
    let β := ∏ v ∈ S, b v
    have hm : (∏ v ∈ S, weight m v) = β * t ^ (s : ℂ) :=
      (hwp m).trans ((Finset.prod_mul_distrib (s := S) (f := b) (g := fun v ↦ (q v : ℂ) ^ (s : ℂ))).trans
        (congrArg (β * ·) (prod_real_cpow S q hq (s : ℂ))))
    have harch := archMellin_scale F fArchDual k (ideleClassNormTwist χ⁻¹ s)
    have rearrange (a b c d e : ℂ) : a * b * ((c * d) * e) = a * c * b * (d * e) := by ring
    exact (congrArg₂ (· * ·) hm (congrArg (· * finiteHeckeL χ⁻¹ s) harch)).trans (rearrange _ _ _ _ _)

/-- Paper: Equations (3.4.3.7)–(3.4.3.9), p. 152. Given two archimedean tests
related by Fourier transform up to a nonzero scalar, there is a global test whose zeta
integral and whose Fourier transform's zeta integral have the respective archimedean
zeta factors and finite Euler products on the right half-plane. The equalities allow
nonzero scalar factors and, on the Fourier side, a positive scale raised to the exponent.
The proof tensors the first test with integer-ring indicators at unramified places and
inverse character weights on integer units at ramified places. The different and the
character conductor determine the Fourier-side scale. See also Proposition 3.2.1.3(3), p. 123. -/
theorem exists_globalHeckeTest_fourier (χ : U[F])
    (fArch fArchDual : SchwartzBruhat (Multiplicative (SAdeleRing F ∅)))
    (c : ℂ) (hc : c ≠ 0)
    (hFourier : ∀ y, archimedeanFourier fArch y = c * fArchDual (Multiplicative.ofAdd y)) :
    ∃ (f : ℬ[F]) (a b : ℂ) (q : ℝ), a ≠ 0 ∧ b ≠ 0 ∧ 0 < q ∧
      (∀ s : halfPlane, globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
        a * (archimedeanZeta fArch (ideleClassNormTwist χ s) * finiteHeckeL χ s)) ∧
      (∀ s : halfPlane,
        globalIdelicZetaIntegral (adeleSchwartzFourier f) (ideleClassNormTwist χ⁻¹ s) =
          (b * (q : ℂ) ^ (s : ℂ)) *
            (archimedeanZeta fArchDual (ideleClassNormTwist χ⁻¹ s) * finiteHeckeL χ⁻¹ s)) := by
  obtain ⟨f, a, b, q, ha, hb, hq, _, hM, hN⟩ :=
    exists_globalHeckeTest_fourier_with_conductor χ fArch fArchDual c hc hFourier
  exact ⟨f, a, b, q, ha, hb, hq, hM, hN⟩

end



/-- Paper: Equations (3.4.3.3)–(3.4.3.6), p. 152. There is an archimedean test
function whose zeta integral equals the gamma factor of the unitary character in the
half-plane of absolute convergence. The proof uses a product of local Gaussians.
Deviation: The complex monomial is chosen with angular weight opposite to the character. -/
theorem exists_archimedeanHeckeTest (χ : U[F]) :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing F ∅)), ∀ s : halfPlane,
      archimedeanZeta f (ideleClassNormTwist χ s) = heckeGammaFactor χ s := by
  obtain ⟨f, _, _, _, _, hf, _⟩ := exists_archimedeanHeckeTest_fourier χ
  exact ⟨f, hf⟩

/-- Paper: Equations (3.4.3.7)–(3.4.3.9), p. 152. For a given archimedean test
there is a global test whose zeta integral is the archimedean zeta integral times the finite
Euler product and a nonzero constant. The proof uses a tensor with integer-ring indicators
at unramified places and inverse character weights on integer units at ramified places.
Deviation: The finite integer-unit Tamagawa masses give a nonzero scalar independent of `s`. -/
theorem exists_globalHeckeTest (χ : U[F])
    (fArch : SchwartzBruhat (Multiplicative (SAdeleRing F ∅))) :
    ∃ (f : ℬ[F]) (a : ℂ), a ≠ 0 ∧ ∀ s : halfPlane,
      globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
        a * (archimedeanZeta fArch (ideleClassNormTwist χ s) * finiteHeckeL χ s) := by
  let S : Finset (HeightOneSpectrum (𝓞 F)) := ∅
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let : MeasurableSpace (SAdeleRing F S) := instMeasurableSpaceSAdeleRing F S
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let G := Multiplicative (SAdeleRing F S)
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace (SAdeleRing F S))
  let : T2Space (SAdeleRing F S) := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space G := ‹T2Space (SAdeleRing F S)›
  let : SigmaCompactSpace (SAdeleRing F S) := inferInstanceAs (SigmaCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace (SAdeleRing F S) := inferInstanceAs (BorelSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace G := ‹BorelSpace (SAdeleRing F S)›
  let μ : Measure G := sAdditiveTamagawaMeasure F S
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let hμ : (sAdditiveTamagawaMeasure F S).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.map_add_left_eq_self x.toAdd }
  let : μ.Regular := addHaar_regular_of_sigmaCompactSpace (sAdditiveTamagawaMeasure F S)
  obtain ⟨e, he, -⟩ := sAdditiveTamagawaMeasure_selfDual F S
  obtain ⟨fourier, hfourier⟩ := schwartzBruhat_fourier_equiv μ
  let g : schwartzBruhatSubmodule (PontryaginDual G) := fourier fArch
  have hEq (y : G) : tamagawaFourier (sAdditiveTamagawaMeasure F S)
      (sAdeleStandardCharacter F S) (fun x ↦ fArch (Multiplicative.ofAdd x)) y.toAdd = g.val (e y) := by
    rw [tamagawaFourier_eq_lcaFourier _ _ _ _ (e y) (fun x ↦ by
      rw [mul_comm x y.toAdd]
      exact he y.toAdd x)]
    exact ((hfourier fArch).2 (e y)).symm
  let fDual : SchwartzBruhat G := ⟨fun y ↦ g.val (e y), schwartzBruhat_mem_comp_equiv e g.property⟩
  have hFourier (y : SAdeleRing F ∅) : archimedeanFourier fArch y = 1 * fDual (Multiplicative.ofAdd y) := by
    rw [one_mul]
    exact hEq (Multiplicative.ofAdd y)
  obtain ⟨f, a, _, _, ha, _, _, hf, _⟩ :=
    exists_globalHeckeTest_fourier χ fArch fDual 1 one_ne_zero hFourier
  exact ⟨f, a, ha, hf⟩

/-- Paper: Proposition 3.2.1.3, p. 123. The completed Hecke L-function extends
meromorphically to the complex plane. We use Mathlib's normal form at poles. -/
theorem completedHeckeL_exists_continuation (χ : U[F]) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧ ∀ s : halfPlane, L s = completedHeckeL χ s := by
  obtain ⟨fArch, hArch⟩ := exists_archimedeanHeckeTest χ
  obtain ⟨f, a, ha, hf⟩ := exists_globalHeckeTest χ fArch
  refine ⟨fun s ↦ a⁻¹ * globalIdelicZFunction f (ideleClassNormTwist χ s), ?_, ?_⟩
  · exact (meromorphicNFOn_fun_const_smul_iff_meromorphicNFOn (inv_ne_zero ha)).2
      (globalIdelicZFunction_meromorphic f χ)
  · intro s
    have hσ := quasiCharacterAbscissa_of_unitary_twist (ideleClassNorm F)
      (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
      (ideleClassNormTwist χ s) χ s (fun _ ↦ rfl)
    have hs : ideleClassNormTwist χ s ∈ rightHalf := by
      change 1 < quasiCharacterAbscissa (ideleClassNorm F) _ _ _
      rw [hσ]
      exact s.property
    change a⁻¹ * globalIdelicZFunction f (ideleClassNormTwist χ s) = completedHeckeL χ s
    rw [globalIdelicZFunction_eq_integral f hs, hf s, hArch s, ← mul_assoc,
      inv_mul_cancel₀ ha, one_mul]
    rfl

/-- Paper: Definition 3.2.1.4, p. 124. The finite Hecke L-function admits
a meromorphic continuation to the complex plane. -/
theorem finiteHeckeL_exists_continuation (χ : U[F]) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧ ∀ s : halfPlane, L s = finiteHeckeL χ s := by
  obtain ⟨Λ, hΛ, hEq⟩ := completedHeckeL_exists_continuation χ
  let M (z : ℂ) := (heckeGammaFactor χ z)⁻¹ * Λ z
  have hm : MeromorphicOn M univ := fun z hz ↦
    ((differentiable_inv_heckeGammaFactor χ).analyticAt z).meromorphicAt.mul (hΛ hz).meromorphicAt
  refine ⟨toMeromorphicNFOn M univ, meromorphicNFOn_toMeromorphicNFOn _ _, fun s ↦ ?_⟩
  have hγ := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property)
  have hNF : MeromorphicNFAt M s :=
    (meromorphicNFAt_mul_iff_right ((differentiable_inv_heckeGammaFactor χ).analyticAt s)
      (inv_ne_zero hγ)).2 (hΛ (mem_univ _))
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _), toMeromorphicNFAt_eq_self.mpr hNF]
  simp [M, hEq s, completedHeckeL, finiteHeckeL, hγ]

/-- Meromorphic uniqueness identifies the germ of the global Z-function with
Tate's explicit polar expression, including in charts containing a pole. -/
private theorem globalIdelicZFunction_polar_germ (f : ℬ[F]) (χ : U[F]) (p c : ℂ) (hp : p.re = 0)
    (hpol : ∀ s : ℂ, 0 < s.re →
      IntegrableOn (ideleClassNormTwist χ s) {g : C[F] | classNormℝ g < 1} (ideleClassTamagawaMeasure F) ∧
      (∫ g in {g : C[F] | classNormℝ g < 1}, ideleClassNormTwist χ s g ∂ideleClassTamagawaMeasure F) =
        c / (s - p)) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ ∀ x : ℂ,
      (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)) =ᶠ[𝓝[≠] x]
        fun s ↦ E s + (adeleSchwartzFourier f zeroAdele * c) / (s - (1 + p)) +
          (-(f zeroAdele * c)) / (s - p) := by
  obtain ⟨E, hE, hM, hEq⟩ := tate_chart_polar_model f χ p c hp hpol
  refine ⟨E, hE, fun x ↦ ?_⟩
  have hZ (s : ℂ) (hs : 1 < s.re) := globalIdelicZFunction_eq_integral f (tate_twist_mem_rightHalf χ s hs)
  have heq := fun s ↦ globalIdelicZetaIntegral_chartContinuation_eq f (globalIdelicZFunction_meromorphic f χ)
    (meromorphicNFOn_toMeromorphicNFOn _ _) hZ hEq (χ' := χ) (s := s) (s' := s) rfl
  exact EventuallyEq.trans (Eventually.of_forall heq) (hM.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ x))

/-- A constant divided by a linear factor has order at least minus one everywhere. -/
private theorem simpleFraction_order (A p x : ℂ) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun w : ℂ ↦ A / (w - p)) x := by
  have hD : AnalyticAt ℂ (fun w : ℂ ↦ w - p) x := by fun_prop
  by_cases hx : x = p
  · subst x
    change -1 ≤ meromorphicOrderAt ((fun _ : ℂ ↦ A) / (fun w ↦ w - p)) p
    rw [meromorphicOrderAt_div analyticAt_const.meromorphicAt hD.meromorphicAt,
      meromorphicOrderAt_id_sub_const, meromorphicOrderAt_const]
    split_ifs <;> norm_num
  · exact le_trans (by decide : (-1 : WithTop ℤ) ≤ 0)
      ((analyticAt_const.div hD (sub_ne_zero.mpr hx)).meromorphicOrderAt_nonneg)

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. The global Z-function is analytic
away from the trivial character and the norm, where it has at most simple poles. -/
theorem globalIdelicZFunction_poles (f : ℬ[F]) (χ : U[F]) :
    let Z := fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)
    AnalyticOnNhd ℂ Z {s | ideleClassNormTwist χ s ≠ 1 ∧
      ideleClassNormTwist χ s ≠ ideleClassNormTwist (1 : U[F]) 1} ∧
    ∀ s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt Z s := by
  obtain ⟨p, c, hp, hχ, hpol⟩ := tate_integral_twist_smallNorm_pole χ
  obtain ⟨E, hE, hEq⟩ := globalIdelicZFunction_polar_germ f χ p c hp hpol
  let A := adeleSchwartzFourier f zeroAdele * c
  let B := -(f zeroAdele * c)
  let P (x : ℂ) := A / (x - (1 + p))
  let Q (x : ℂ) := B / (x - p)
  have hP (x : ℂ) : MeromorphicAt P x := analyticAt_const.meromorphicAt.div (by fun_prop)
  have hQ (x : ℂ) : MeromorphicAt Q x := analyticAt_const.meromorphicAt.div (by fun_prop)
  constructor
  · intro x hx
    apply ((globalIdelicZFunction_meromorphic f χ (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt).mp
    rw [meromorphicOrderAt_congr (hEq x)]
    rcases hχ with rfl | hχ
    · simpa using (hE.analyticAt x).meromorphicOrderAt_nonneg
    · have h₀ : ideleClassNormTwist (1 : U[F]) 0 = 1 := by
        ext1 g
        change (1 : ℂ) * _ ^ (0 : ℂ) = 1
        simp
      have hp₁ : ideleClassNormTwist χ (1 + p) = ideleClassNormTwist (1 : U[F]) 1 := by
        simpa [add_comm p] using ideleClassNormTwist_add_of_eq (hχ.trans h₀.symm) 1
      have hx₁ : x ≠ 1 + p := fun he ↦ hx.2 (he ▸ hp₁)
      have hx₀ : x ≠ p := fun he ↦ hx.1 (he ▸ hχ)
      have ha : AnalyticAt ℂ P x := analyticAt_const.div (by fun_prop) (sub_ne_zero.mpr hx₁)
      have hb : AnalyticAt ℂ Q x := analyticAt_const.div (by fun_prop) (sub_ne_zero.mpr hx₀)
      exact (((hE.analyticAt x).add ha).add hb).meromorphicOrderAt_nonneg
  · intro x
    rw [meromorphicOrderAt_congr (hEq x)]
    have hE₀ := (hE.analyticAt x).meromorphicOrderAt_nonneg
    have hEP : (-1 : WithTop ℤ) ≤ meromorphicOrderAt (E + P) x :=
      (le_min ((by decide : (-1 : WithTop ℤ) ≤ 0).trans hE₀)
        (simpleFraction_order A (1 + p) x)).trans
        (meromorphicOrderAt_add (hE.analyticAt x).meromorphicAt (hP x))
    exact (le_min hEP (simpleFraction_order B p x)).trans
      (meromorphicOrderAt_add ((hE.analyticAt x).meromorphicAt.add (hP x)) (hQ x))

/-- Product decomposition of the class Haar measure for a section of the norm. -/
private theorem classTamagawa_normProduct (σ : ℝ≥0ˣ → C[F]) (hσ : Continuous σ)
    (hr : RightInverse σ (ideleClassNorm F)) :
    (positiveRealHaar.prod (normOneIdeleClassTamagawaMeasure F)).map
      (fun p : ℝ≥0ˣ × (ideleClassNorm F).ker ↦ σ p.1 * p.2.val) = ideleClassTamagawaMeasure F := by
  let : T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  let : BorelSpace C[F] := ⟨rfl⟩
  let : SecondCountableTopology 𝕀[F] := idele_secondCountable F
  let : SecondCountableTopology C[F] := inferInstanceAs
    (SecondCountableTopology (𝕀[F] ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  have hw := ideleClassTamagawaMeasure_isWeil F
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := hw.1
  have hν := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure := hν.1
  apply normProduct_of_isWeil (G := C[F]) (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous
    σ hσ hr (ideleClassTamagawaMeasure F) hw.2.1 (normOneIdeleClassTamagawaMeasure F) hν.2.1
  exact normOneIdeleClassTamagawaMeasure_isWeil F

/-- In logarithmic norm coordinates the Haar scalar is exactly the mass of
the norm-one classes, since the measure on the norm quotient is dt/t. -/
private theorem classTamagawa_map_log_norm :
    (ideleClassTamagawaMeasure F).map (fun g ↦ Real.log (classNormℝ g)) =
      (normOneIdeleClassTamagawaMeasure F univ).toNNReal • volume := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let ν := normOneIdeleClassTamagawaMeasure F
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let σ (t : ℝ≥0ˣ) : C[F] := classOf (canonicalIdeleNormSection F t)
  have hσ : Continuous σ := continuous_quotient_mk'.comp (canonicalIdeleNormSection_continuous F)
  have hr : RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let j (p : ℝ≥0ˣ × (ideleClassNorm F).ker) := σ p.1 * p.2.val
  have hj : Measurable j :=
    ((hσ.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).measurable
  let l (t : ℝ≥0ˣ) := Real.log (t.val : ℝ)
  have hl : Measurable l := Real.measurable_log.comp (NNReal.continuous_coe.comp Units.continuous_val).measurable
  have hmap : positiveRealHaar.map l = volume := by
    let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    have hE : positiveRealHaar = volume.map E := by
      apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
      funext y
      exact Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos y).le))
    rw [hE, Measure.map_map hl E.continuous.measurable]
    have hcomp : l ∘ E = id := funext fun y ↦ Real.log_exp y
    rw [hcomp, Measure.map_id]
  have hcomp : (l ∘ ideleClassNorm F) ∘ j = l ∘ Prod.fst := by
    funext p
    change l (ideleClassNorm F (σ p.1 * p.2.val)) = l p.1
    rw [map_mul, hr, MonoidHom.mem_ker.mp p.2.property, mul_one]
  change (ideleClassTamagawaMeasure F).map (l ∘ ideleClassNorm F) = (ν univ).toNNReal • volume
  rw [← classTamagawa_normProduct σ hσ hr, Measure.map_map
    (hl.comp (isProperMap_ideleClassNorm F).continuous.measurable) hj, hcomp,
    ← Measure.map_map hl measurable_fst, Measure.map_fst_prod, Measure.map_smul, hmap,
    ← Measure.coe_nnreal_smul, ENNReal.coe_toNNReal (measure_ne_top ν univ)]
  exact hl.aemeasurable

/-- Under the logarithm of the idèle class norm, Tamagawa measure pushes forward
to Lebesgue measure times the mass of the norm-one class group. -/
theorem ideleClassTamagawaMeasure_map_logNorm :
    (ideleClassTamagawaMeasure F).map (fun g ↦ Real.log (classNormℝ g)) =
      (normOneIdeleClassTamagawaMeasure F univ).toNNReal • volume :=
  classTamagawa_map_log_norm


/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. The residue at the trivial character
is minus the norm-one class volume times the test function evaluated at zero. -/
theorem globalIdelicZFunction_residue_zero (f : ℬ[F]) :
    Tendsto (fun s : ℂ ↦ s * globalIdelicZFunction f (ideleClassNormTwist (1 : U[F]) s))
      (𝓝[≠] 0)
      (𝓝 (-((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ) * f zeroAdele)) := by
  let k : ℝ≥0 := (normOneIdeleClassTamagawaMeasure F univ).toNNReal
  have hp (s : ℂ) (hs : 0 < s.re) := tate_integral_classNorm_cpow_smallNorm_of_map k
    (classTamagawa_map_log_norm (F := F)) s hs
  have htw (s : ℂ) (g : C[F]) : ideleClassNormTwist (1 : U[F]) s g = (classNormℝ g : ℂ) ^ s :=
    one_mul _
  obtain ⟨E, hE, hEq⟩ := globalIdelicZFunction_polar_germ f (1 : U[F]) 0 (k : ℝ) rfl (by
    intro s hs
    change IntegrableOn _ ((classNormℝ : C[F] → ℝ) ⁻¹' Iio 1) _ ∧
      (∫ g in ((classNormℝ : C[F] → ℝ) ⁻¹' Iio 1), _ ∂_) = _
    simpa only [show (ideleClassNormTwist (1 : U[F]) s : C[F] → ℂ) = _ from funext (htw s),
      sub_zero] using hp s hs)
  let A := adeleSchwartzFourier f zeroAdele * (k : ℝ)
  let B := -(f zeroAdele * (k : ℝ))
  have hlim : Tendsto (fun s : ℂ ↦ s * (E s + A / (s - 1)) + B) (𝓝[≠] 0) (𝓝 B) := by
    have hcont : ContinuousAt (fun s : ℂ ↦ s * (E s + A / (s - 1)) + B) 0 :=
      (continuousAt_id.mul ((hE.continuous.continuousAt).add
        (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by norm_num)))).add continuousAt_const
    simpa only [zero_mul, zero_add] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hB : B = -((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ) * f zeroAdele := by
    change -(f zeroAdele * _) = _
    rw [neg_mul, mul_comm]
    rfl
  rw [← hB]
  apply hlim.congr'
  filter_upwards [hEq 0, self_mem_nhdsWithin] with s he hs
  rw [he]
  simp only [add_zero, sub_zero]
  change s * (E s + A / (s - 1)) + B = s * (E s + A / (s - 1) + B / s)
  field_simp [show s ≠ 0 from hs]

/-- Split off the power of the class norm using its section. The unitary character
left over is either trivial or already nontrivial on a norm-one element. -/
private theorem tate_exists_normalized_twist (c : 𝒳[F]) :
    ∃ (χ : U[F]) (s : ℂ), c = ideleClassNormTwist χ s ∧
      (χ = 1 ∨ ∃ u : C[F], ideleClassNorm F u = 1 ∧ χ u ≠ 1) := by
  let m := ideleClassNorm F
  let q : 𝕀[F] →ₜ* C[F] := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C[F] := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : RightInverse σ m := canonicalIdeleNormSection_rightInverse F
  have hm := (isProperMap_ideleClassNorm F).continuous
  let : LocallyCompactSpace C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  let : CompactSpace m.ker := (ideleClassGroup_finiteness F).2.1
  obtain ⟨e, he⟩ := quasiCharacterParametrization_of_split (G := C[F]) m hm σ hσ
  have hr (x : C[F]) : x / σ (m x) ∈ m.ker := by
    simp [MonoidHom.mem_ker, hσ (m x)]
  let r : C[F] →ₜ* m.ker :=
    { toFun := fun x ↦ ⟨_, hr x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y ↦ Subtype.ext (by
        simp
        exact (div_mul_div_comm x (σ (m x)) y (σ (m y))).symm)
      continuous_toFun := (continuous_id.div' (σ.continuous.comp hm)).subtype_mk hr }
  let χ := (e c).2.comp r
  refine ⟨χ, (e c).1, ?_, ?_⟩
  · ext1 x
    change c x = ((e c).2 (r x) : ℂ) * (classNormℝ x : ℂ) ^ (e c).1
    rw [(he c).2, ← (he c).1 (m x), ← map_mul]
    exact congrArg c (div_mul_cancel x _).symm
  · by_cases h : χ = 1
    · exact Or.inl h
    · obtain ⟨x, hx⟩ := not_forall.mp (mt PontryaginDual.ext_iff.mpr h)
      refine Or.inr ⟨r x, (r x).property, ?_⟩
      have hrr : r (r x) = r x := Subtype.ext (by
        change (r x).val / σ (m (r x)) = (r x).val
        rw [show m (r x) = 1 from (r x).property, map_one, div_one])
      change (e c).2 (r (r x)) ≠ 1
      rwa [hrr]

/-- The cutoff Mellin integral has the same coefficient for a normalized unitary
character and its inverse. Translation by a norm-one class kills both integrals
in the nontrivial case. -/
private theorem tate_paired_polar_terms (χ : U[F])
    (hχ : χ = 1 ∨ ∃ u : C[F], ideleClassNorm F u = 1 ∧ χ u ≠ 1) :
    ∃ k : ℂ, ∀ η : U[F], η = χ ∨ η = χ⁻¹ → ∀ s : ℂ, 0 < s.re →
      (∫ x in {g : C[F] | classNormℝ g < 1}, ideleClassNormTwist η s x
        ∂ideleClassTamagawaMeasure F) = k / s := by
  let S := {g : C[F] | classNormℝ g < 1}
  rcases hχ with rfl | ⟨u, hu, hne⟩
  · obtain ⟨k, hk⟩ := tate_integral_classNorm_cpow_smallNorm (F := F)
    refine ⟨(k : ℝ), fun η hη s hs ↦ ?_⟩
    have h : η = 1 := by simpa using hη
    subst η
    change (∫ x in S, (1 : ℂ) * (classNormℝ x : ℂ) ^ s ∂ideleClassTamagawaMeasure F) = _
    simp only [one_mul]
    exact (hk s hs).2
  · refine ⟨0, fun η hη s _ ↦ ?_⟩
    have hηu : η u ≠ 1 := by
      rcases hη with rfl | rfl
      · exact hne
      · change (χ u)⁻¹ ≠ 1
        simpa using hne
    let μ := ideleClassTamagawaMeasure F
    let : BorelSpace C[F] := ⟨rfl⟩
    let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil (F := F)).1
    let W := ideleClassNormTwist η s
    have hPre : (fun x : C[F] ↦ u * x) ⁻¹' S = S := by
      ext x
      change classNormℝ (u * x) < 1 ↔ classNormℝ x < 1
      dsimp only
      rw [map_mul, hu, one_mul]
    have h := (measurePreserving_mul_left μ u).setIntegral_preimage_emb
      (Homeomorph.mulLeft u).toMeasurableEquiv.measurableEmbedding W S
    rw [hPre] at h
    change (∫ x in S, W (u * x) ∂μ) = _ at h
    simp_rw [map_mul] at h
    rw [integral_const_mul, ← sub_eq_zero, ← sub_one_mul] at h
    have hWu : W u = (η u : ℂ) := by
      change (η u : ℂ) * (classNormℝ u : ℂ) ^ s = _
      simp [hu]
    rw [hWu] at h
    rw [zero_div]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr fun he ↦ hηu (Subtype.ext he))

/-- The boundary of the Tate splitting domain has zero measure: logarithmic
norm pushes Haar measure forward to a multiple of Lebesgue measure. -/
private theorem tate_large_norm_ae :
    {g : C[F] | 1 < classNormℝ g} =ᵐ[ideleClassTamagawaMeasure F]
      {g : C[F] | 1 ≤ classNormℝ g} := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let l := fun g : C[F] ↦ Real.log (classNormℝ g)
  have hl : Continuous l :=
    tate_continuous_classNormReal.log fun g ↦ (tate_classNormReal_pos g).ne'
  obtain ⟨k, hk⟩ := tate_exists_map_logClassNorm_eq_smul_volume (F := F)
  have hnull : ideleClassTamagawaMeasure F (l ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply hl.measurable (measurableSet_singleton 0)]
    change (Measure.map (fun g : C[F] ↦ Real.log (classNormℝ g)) _) _ = 0
    rw [hk]
    simp
  filter_upwards [compl_mem_ae_iff.mpr hnull] with g hg
  have hn : classNormℝ g ≠ 1 := fun h ↦ hg (by
    change Real.log (classNormℝ g) = 0
    rw [h, Real.log_one])
  exact lt_iff_le_and_ne.trans (and_iff_left hn.symm)

/-- Split the convergent integral for either member of a Riemann–Roch pair.
The two large-norm integrals interchange on reflecting the character. -/
private theorem tate_zeta_pair_split (f φ : ℬ[F]) (χ : U[F]) (k : ℂ)
    (hRR : ∀ g : C[F], adelicTheta f g + f zeroAdele =
      (classNormℝ g : ℂ)⁻¹ * (adelicTheta φ g⁻¹ + φ zeroAdele))
    (hpol : ∀ s : ℂ, 0 < s.re → (∫ x in {g : C[F] | classNormℝ g < 1},
      ideleClassNormTwist χ s x ∂ideleClassTamagawaMeasure F) = k / s)
    (s : ℂ) (hs : 1 < s.re) :
    let L := {g : C[F] | 1 ≤ classNormℝ g}
    globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
      tateThetaMellinOn f χ L s + tateThetaMellinOn φ χ⁻¹ L (1 - s) +
        φ zeroAdele * (k / (s - 1)) - f zeroAdele * (k / s) := by
  let L := {g : C[F] | 1 ≤ classNormℝ g}
  let S := {g : C[F] | classNormℝ g < 1}
  let T := {g : C[F] | 1 < classNormℝ g}
  let μ := ideleClassTamagawaMeasure F
  let W := fun z : ℂ ↦ ideleClassNormTwist χ z
  let D := fun g : C[F] ↦ adelicTheta φ g⁻¹ * W (s - 1) g
  let a := f zeroAdele
  let b := φ zeroAdele
  let : BorelSpace C[F] := ⟨rfl⟩
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil (F := F)).1
  let : μ.Regular := (ideleClassTamagawaMeasure_isWeil (F := F)).2.1
  let : T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  have hL : MeasurableSet L := tate_continuous_classNormReal.measurable measurableSet_Ici
  have hS : MeasurableSet S := tate_continuous_classNormReal.measurable measurableSet_Iio
  have hc : Lᶜ = S := Set.ext fun g ↦ (not_le : ¬1 ≤ classNormℝ g ↔ _)
  have hi : (fun g : C[F] ↦ g⁻¹) ⁻¹' T = S := by
    ext g
    change 1 < classNormℝ g⁻¹ ↔ classNormℝ g < 1
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
    exact one_lt_inv₀ (tate_classNormReal_pos g)
  obtain ⟨hInt, hWhole⟩ := globalIdelicZetaIntegral_eq_thetaIntegral f (W s)
    (tate_twist_mem_rightHalf χ s hs)
  have hDform (g : C[F]) : adelicTheta f g * W s g = D g + b * W (s - 1) g - a * W s g := by
    dsimp only [D, a, b, W]
    rw [← tate_inv_norm_mul_twist]
    linear_combination (ideleClassNormTwist χ s g) * hRR g
  have hs₀ := zero_lt_one.trans hs
  have hs₁ : 0 < (s - 1).re := by simpa only [Complex.sub_re, Complex.one_re, sub_pos] using hs
  obtain ⟨_, _, _, h⟩ := tate_integral_twist_smallNorm χ
  have h₀ := (h s hs₀).1.const_mul a
  have h₁ := (h (s - 1) hs₁).1.const_mul b
  have hD : IntegrableOn D S μ := by
    refine (integrableOn_congr_fun (g := D) (fun g _ ↦ ?_) hS).mp
      ((hInt.integrableOn.add h₀).sub h₁)
    change adelicTheta f g * W s g + a * W s g - b * W (s - 1) g = D g
    rw [hDform]
    ring
  have hDual : (∫ g in S, D g ∂μ) = tateThetaMellinOn φ χ⁻¹ L (1 - s) := by
    have hinv := (Measure.measurePreserving_inv μ).setIntegral_preimage_emb
      (Homeomorph.inv (C[F])).toMeasurableEquiv.measurableEmbedding
      (fun g ↦ adelicTheta φ g * ideleClassNormTwist χ⁻¹ (1 - s) g) T
    rw [hi] at hinv
    refine (setIntegral_congr_fun hS fun g _ ↦ ?_).trans (hinv.trans ?_)
    · dsimp [D, W]
      rw [tate_twist_inv_apply]
    · exact setIntegral_congr_set tate_large_norm_ae
  change _ = tateThetaMellinOn f χ L s + _ + _ - _
  rw [hWhole, ← integral_add_compl hL hInt, hc]
  change tateThetaMellinOn f χ L s + (∫ g in S, adelicTheta f g * W s g ∂μ) = _
  simp_rw [hDform]
  have hSub := integral_sub (hD.add h₁) h₀
  simp only [Pi.add_apply] at hSub
  rw [hSub, integral_add hD h₁, integral_const_mul, integral_const_mul, hDual,
    hpol _ hs₁, hpol _ hs₀]
  dsimp only [a, b]
  ring

/-- Paper: Theorem 3.2.2.1(1)(b), p. 124. Fourier transforming the test function
and taking the norm times the inverse character preserves its global Z-function value. -/
theorem globalIdelicZFunction_functionalEquation (f : ℬ[F]) (c : 𝒳[F]) :
    globalIdelicZFunction f c = globalIdelicZFunction (adeleSchwartzFourier f)
      (dualQuasiCharacter (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous c) := by
  obtain ⟨χ, s, rfl, hχ⟩ := tate_exists_normalized_twist c
  obtain ⟨k, hk⟩ := tate_paired_polar_terms χ hχ
  let φ := adeleSchwartzFourier f
  have hRR (g : C[F]) : adelicTheta f g + f zeroAdele =
      (classNormℝ g : ℂ)⁻¹ * (adelicTheta φ g⁻¹ + φ zeroAdele) := by
    rw [adelicTheta_riemannRoch]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    dsimp only [φ]
    ring
  have hRR' (g : C[F]) : adelicTheta φ g + φ zeroAdele =
      (classNormℝ g : ℂ)⁻¹ * (adelicTheta f g⁻¹ + f zeroAdele) := by
    rw [hRR, inv_inv g]
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Complex.ofReal_inv, inv_inv]
    rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (tate_classNormReal_pos g).ne'),
      one_mul]
  let L := {g : C[F] | 1 ≤ classNormℝ g}
  let P := tateThetaMellinOn f χ L
  let Q := tateThetaMellinOn φ χ⁻¹ L
  let M (z : ℂ) := P z + Q (1 - z) + φ zeroAdele * (k / (z - 1)) - f zeroAdele * (k / z)
  let : BorelSpace C[F] := ⟨rfl⟩
  have hL : MeasurableSet L := tate_continuous_classNormReal.measurable measurableSet_Ici
  have hP := (tate_differentiable_thetaMellinOn f χ hL (fun _ hg ↦ hg)).analyticAt
  have hQ := (tate_differentiable_thetaMellinOn φ χ⁻¹ hL (fun _ hg ↦ hg)).analyticAt
  have hSum (z : ℂ) : AnalyticAt ℂ (fun t ↦ P t + Q (1 - t)) z :=
    (hP z).add ((hQ (1 - z)).comp (by fun_prop))
  have hM : MeromorphicOn M univ := by
    intro z _
    have h := (hSum z).meromorphicAt
    dsimp only [M]
    fun_prop
  let G := toMeromorphicNFOn M univ
  have hG : MeromorphicNFOn G univ := meromorphicNFOn_toMeromorphicNFOn M univ
  have hReg (z : ℂ) (hz : z ≠ 0) (hz₁ : z ≠ 1) : G z = M z := by
    have h : AnalyticAt ℂ M z := by
      have := hSum z
      have h₁ := sub_ne_zero.mpr hz₁
      dsimp only [M]
      fun_prop
    exact (toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ z)).trans
      (congrFun (toMeromorphicNFAt_eq_self.mpr h.meromorphicNFAt) z)
  have hAgree (z : ℂ) (hz : 1 < z.re) :
      G z = globalIdelicZetaIntegral f (ideleClassNormTwist χ z) := by
    rw [hReg z (by rintro rfl; norm_num at hz) (by rintro rfl; norm_num at hz)]
    exact (tate_zeta_pair_split f φ χ k hRR (hk χ (Or.inl rfl)) z hz).symm
  have hDual (z : ℂ) (hz : 1 < z.re) : G (1 - z) =
      globalIdelicZetaIntegral φ (ideleClassNormTwist χ⁻¹ z) := by
    rw [hReg (1 - z) (sub_ne_zero.mpr (by rintro rfl; norm_num at hz))
      (by intro h; have := congrArg Complex.re h; simp at this; linarith),
      tate_zeta_pair_split φ f χ⁻¹ k hRR' (hk χ⁻¹ (Or.inr rfl)) z hz]
    dsimp only [M, P, Q]
    rw [inv_inv, sub_sub_cancel, sub_right_comm, sub_self, zero_sub, div_neg,
      show 1 - z = -(z - 1) by ring, div_neg]
    ring
  have hReflect : MeromorphicNFOn (fun z ↦ G (1 - z)) univ := fun z _ ↦
    (hG (mem_univ (1 - z))).comp_analyticAt (g := fun t : ℂ ↦ 1 - t) (by fun_prop)
  have hChart (u : ℬ[F]) (η : U[F]) (H : ℂ → ℂ) (hNF : MeromorphicNFOn H univ)
      (hA : ∀ z : ℂ, 1 < z.re → H z = globalIdelicZetaIntegral u (ideleClassNormTwist η z))
      (z : ℂ) : globalIdelicZFunction u (ideleClassNormTwist η z) = H z :=
    globalIdelicZetaIntegral_chartContinuation_eq u (globalIdelicZFunction_meromorphic u η) hNF
      (fun t ht ↦ globalIdelicZFunction_eq_integral u (tate_twist_mem_rightHalf η t ht)) hA
      (s := z) rfl
  have hdualChar : dualQuasiCharacter (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous
      (ideleClassNormTwist χ s) = ideleClassNormTwist χ⁻¹ (1 - s) := by
    ext1 g
    change (classNormℝ g : ℂ) * ideleClassNormTwist χ s g⁻¹ = _
    have h := tate_twist_inv_apply χ s g⁻¹
    rw [inv_inv g, ← tate_inv_norm_mul_twist] at h
    simpa only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Complex.ofReal_inv, inv_inv]
      using h.symm
  rw [hdualChar, hChart f χ G hG hAgree s,
    hChart φ χ⁻¹ (fun z ↦ G (1 - z)) hReflect hDual (1 - s), sub_sub_cancel]

/-- An entire nonzero multiple of the completed series determines the corresponding
global idelic Z-function whenever it agrees with the zeta integral on the right half-plane. -/
private theorem globalIdelicZFunction_eq_mul_completedHeckeL_of_integral
    (f : ℬ[F]) (χ : U[F]) (L A : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hA : Differentiable ℂ A) (hA₀ : ∀ s, A s ≠ 0)
    (hIntegral : ∀ s : halfPlane, globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
      A s * completedHeckeL χ s) (s : ℂ) :
    globalIdelicZFunction f (ideleClassNormTwist χ s) = A s * L s := by
  let Z (z : ℂ) := globalIdelicZFunction f (ideleClassNormTwist χ z)
  have hZ : MeromorphicNFOn Z univ := globalIdelicZFunction_meromorphic f χ
  have hAL : MeromorphicNFOn (A * L) univ := fun z hz ↦
    (meromorphicNFAt_mul_iff_right (hA.analyticAt z) (hA₀ z)).2 (hL hz)
  have hAgree (z : halfPlane) : Z z = (A * L) z := by
    have hz : ideleClassNormTwist χ z ∈ rightHalf := by
      change 1 < quasiCharacterAbscissa (ideleClassNorm F) _ _ _
      rw [quasiCharacterAbscissa_of_unitary_twist (ideleClassNorm F)
        (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
        (ideleClassNormTwist χ z) χ z (fun _ ↦ rfl)]
      exact z.property
    change globalIdelicZFunction f (ideleClassNormTwist χ z) = A z * L z
    rw [globalIdelicZFunction_eq_integral f hz, hIntegral z, h z]
  have hAtTwo : meromorphicOrderAt (Z - A * L) 2 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hNear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hNear.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr (hAgree ⟨z, hz⟩)
  have hOrder := (hZ.meromorphicOn.sub hAL.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) hAtTwo
  have hPunctured : Z =ᶠ[𝓝[≠] s] A * L :=
    (meromorphicOrderAt_eq_top_iff.mp hOrder).mono fun _ hz ↦ sub_eq_zero.mp hz
  exact (((hZ (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hAL (mem_univ s))).mp hPunctured).eq_of_nhds

/-- The pure norm-twist chart is injective since the norm has a section. -/
private theorem trivial_normTwist_injective : Injective (ideleClassNormTwist (1 : U[F])) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨σ, hσ, hnorm⟩, _⟩ := ideleGroup_quotient.{_, 0} F
  intro z w he
  let c : ℝ≥0ˣ →ₜ* ℂ := (ideleClassNormTwist (1 : U[F]) z).comp ⟨σ, hσ⟩
  let valℝ (u : ℝ≥0ˣ) : ℝ := u.val
  obtain ⟨v, _, hv⟩ := existsUnique_complexPower c
  have hz (u : ℝ≥0ˣ) : c u = (valℝ u : ℂ) ^ z := by
    change 1 * (classNormℝ (σ u) : ℂ) ^ z = _
    rw [one_mul, show classNormℝ (σ u) = valℝ u from congrArg valℝ (hnorm u)]
  have hw (u : ℝ≥0ˣ) : c u = (valℝ u : ℂ) ^ w := by
    change ideleClassNormTwist (1 : U[F]) z (σ u) = _
    rw [he]
    change 1 * (classNormℝ (σ u) : ℂ) ^ w = _
    rw [one_mul, show classNormℝ (σ u) = valℝ u from congrArg valℝ (hnorm u)]
  exact (hv z hz).trans (hv w hw).symm

/-- Paper: Proposition 3.2.1.3(2), p. 123. A continuation of the completed
Dedekind zeta function in the trivial Hecke character normalization is
holomorphic away from zero and one. -/
theorem completedHeckeL_one_analyticOnNhd (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (h : ∀ s : halfPlane, L s = completedHeckeL (1 : U[F]) s) :
    AnalyticOnNhd ℂ L ({0, 1}ᶜ : Set ℂ) := by
  have hinj := trivial_normTwist_injective (F := F)
  have hzero : ideleClassNormTwist (1 : U[F]) 0 = 1 := by
    ext1 g
    change 1 * (classNormℝ g : ℂ) ^ (0 : ℂ) = 1
    simp
  obtain ⟨fArch, hArch⟩ := exists_archimedeanHeckeTest (1 : U[F])
  obtain ⟨f, a, ha, hf⟩ := exists_globalHeckeTest (1 : U[F]) fArch
  have hZ (s : ℂ) : globalIdelicZFunction f (ideleClassNormTwist (1 : U[F]) s) = a * L s :=
    globalIdelicZFunction_eq_mul_completedHeckeL_of_integral f _ L (fun _ ↦ a)
      hL h (differentiable_const a) (fun _ ↦ ha) (fun z ↦ by
        rw [hf z, hArch z]
        rfl) s
  intro s hs
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
  have han := (globalIdelicZFunction_poles f (1 : U[F])).1 s
    ⟨fun he ↦ hs.1 (hinj (he.trans hzero.symm)), fun he ↦ hs.2 (hinj he)⟩
  have he : (fun z ↦ a⁻¹ * globalIdelicZFunction f (ideleClassNormTwist (1 : U[F]) z)) = L := by
    funext z
    rw [hZ, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  rw [← he]
  exact analyticAt_const.mul han

/-- Paper: Equation (3.1.1.4), p. 119. Duality in the norm-twist coordinate
takes the inverse unitary character and reflects the exponent. -/
private theorem dualQuasiCharacter_ideleClassNormTwist (χ : U[F]) (s : ℂ) :
    dualQuasiCharacter (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous
      (ideleClassNormTwist χ s) = ideleClassNormTwist χ⁻¹ (1 - s) := by
  ext1 g
  let N : ℂ := (classNormℝ g : ℂ)
  have hN : N ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero)
  change N * ideleClassNormTwist χ s g⁻¹ = ideleClassNormTwist χ⁻¹ (1 - s) g
  rw [map_inv]
  change N * ((χ g : ℂ) * N ^ s)⁻¹ = (χ g : ℂ)⁻¹ * N ^ (1 - s)
  rw [mul_inv_rev, Complex.cpow_sub 1 s hN, Complex.cpow_one, div_eq_mul_inv]
  ac_rfl

/-- Paper: Theorem 3.2.2.1(1)(a), p. 124. The residue at the norm character
is the norm-one class volume times the Fourier transform evaluated at zero. -/
theorem globalIdelicZFunction_residue_one (f : ℬ[F]) :
    Tendsto (fun s : ℂ ↦ (s - 1) * globalIdelicZFunction f (ideleClassNormTwist (1 : U[F]) s))
      (𝓝[≠] 1)
      (𝓝 (((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ) *
        adeleSchwartzFourier f zeroAdele)) := by
  have hreflect : Tendsto (fun s : ℂ ↦ 1 - s) (𝓝[≠] 1) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun s : ℂ ↦ 1 - s) 1 :=
        (continuous_const.sub continuous_id).continuousAt
      have ht : Tendsto (fun s : ℂ ↦ 1 - s) (𝓝 1) (𝓝 (1 - 1)) := hc.tendsto
      simpa only [sub_self] using ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact fun he ↦ hs (sub_eq_zero.mp he).symm
  have h := ((globalIdelicZFunction_residue_zero (adeleSchwartzFourier f)).comp hreflect).neg
  rw [neg_mul, neg_neg] at h
  refine h.congr fun s ↦ ?_
  have hZ := globalIdelicZFunction_functionalEquation f (ideleClassNormTwist (1 : U[F]) s)
  rw [dualQuasiCharacter_ideleClassNormTwist, inv_one] at hZ
  change -((1 - s) * globalIdelicZFunction (adeleSchwartzFourier f)
    (ideleClassNormTwist (1 : U[F]) (1 - s))) = _
  rw [← hZ, ← neg_mul, neg_sub]

/-- Before centering the functional equation, its scale comes from the
Fourier transform of the finite part of the global test. -/
private theorem completedHeckeL_conductor_data (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hdual : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s) :
    ∃ (a b : ℂ) (q : ℝ), a ≠ 0 ∧ b ≠ 0 ∧ 0 < q ∧
      (∀ n : HeightOneSpectrum (𝓞 F) → ℕ, (∀ v, IsLeast (finiteConductorLevels(F, χ, v)) (n v)) →
        Real.log q = finiteConductorLog(F, n)) ∧
      ∀ s, Ldual (1 - s) = (b * (q : ℂ) ^ (1 - s))⁻¹ * a * L s := by
  obtain ⟨fArch, fArchDual, c, hc, hFourier, hArch, hArchDual⟩ :=
    exists_archimedeanHeckeTest_fourier χ
  obtain ⟨f, a, b, q, ha, hb, hq, hscale, hf, hFourierIntegral⟩ :=
    exists_globalHeckeTest_fourier_with_conductor χ fArch fArchDual c hc hFourier
  let B (s : ℂ) := b * (q : ℂ) ^ s
  have hq₀ : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hB : Differentiable ℂ B :=
    (differentiable_id.const_cpow (Or.inl hq₀)).const_mul b
  have hB₀ (s : ℂ) : B s ≠ 0 :=
    mul_ne_zero hb (fun hz ↦ hq₀ ((Complex.cpow_eq_zero_iff _ _).mp hz).1)
  have hZ := globalIdelicZFunction_eq_mul_completedHeckeL_of_integral f χ L (fun _ ↦ a)
    hL h (differentiable_const a) (fun _ ↦ ha) (fun s ↦ by
      rw [hf s, hArch s]
      rfl)
  have hZdual := globalIdelicZFunction_eq_mul_completedHeckeL_of_integral
    (adeleSchwartzFourier f) χ⁻¹ Ldual B hLdual hdual hB hB₀ (fun s ↦ by
      rw [hFourierIntegral s, hArchDual s]
      rfl)
  refine ⟨a, b, q, ha, hb, hq, hscale, fun s ↦ ?_⟩
  change Ldual (1 - s) = (B (1 - s))⁻¹ * a * L s
  have hEq := globalIdelicZFunction_functionalEquation f (ideleClassNormTwist χ s)
  rw [dualQuasiCharacter_ideleClassNormTwist, hZ s, hZdual (1 - s)] at hEq
  rw [mul_assoc, hEq, ← mul_assoc, inv_mul_cancel₀ (hB₀ (1 - s)), one_mul]

/-- Center the radial scale at the fixed point of the reflection. -/
private theorem hecke_scale_center (a b : ℂ) (hb : b ≠ 0) (q : ℝ) (hq : 0 < q) (s : ℂ) :
    (b * (q : ℂ) ^ (1 - s))⁻¹ * a =
      ((b * (q : ℂ) ^ (1 / 2 : ℂ))⁻¹ * a) * Complex.exp ((Real.log q : ℂ) * (s - 1 / 2)) := by
  have hq' := Complex.ofReal_ne_zero.mpr hq.ne'
  rw [Complex.ofReal_log hq.le, ← Complex.cpow_def_of_ne_zero hq']
  have he : (q : ℂ) ^ (1 / 2 : ℂ) = (q : ℂ) ^ (1 - s) * (q : ℂ) ^ (s - 1 / 2) := by
    rw [← Complex.cpow_add _ _ hq']
    ring_nf
  rw [he]
  field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl hq')]

/-- Paper: Proposition 3.2.1.3(3), p. 123, and Equation (3.3.2.24), p. 141.
The epsilon factor of the completed functional equation is a nonzero constant
times the discriminant–conductor scale to the exponent `s - 1/2`.
Deviation: Equation (3.3.1.30), p. 136, omits the conductor power that
appears in (3.3.2.24). The finite exponents use the local principal-unit filtration. -/
theorem completedHeckeL_continuation_conductor_of_isLeast (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ) (hdual : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s)
    (n : HeightOneSpectrum (𝓞 F) → ℕ) (hn : ∀ v, IsLeast (finiteConductorLevels(F, χ, v)) (n v)) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ, Ldual (1 - s) =
      C * Complex.exp ((finiteConductorLog(F, n) : ℂ) * (s - 1 / 2)) * L s := by
  obtain ⟨a, b, q, ha, hb, hq, hscale, hEq⟩ := completedHeckeL_conductor_data χ L Ldual hL h hLdual hdual
  refine ⟨(b * (q : ℂ) ^ (1 / 2 : ℂ))⁻¹ * a, mul_ne_zero (inv_ne_zero (mul_ne_zero hb
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hq.ne'))))) ha, fun s ↦ ?_⟩
  rw [hEq, ← hscale n hn, hecke_scale_center a b hb q hq]

/-- The test functions give an epsilon factor whose reciprocal is bounded on every fixed vertical strip. -/
private theorem completedHeckeL_bounded_epsilon (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hdual : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s) :
    ∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s, ε s ≠ 0) ∧
      (∀ u v : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ, u ≤ z.re → z.re ≤ v → ‖(ε z)⁻¹‖ ≤ K) ∧
      ∀ s, Ldual (1 - s) = ε s * L s := by
  obtain ⟨a, b, q, ha, hb, hq, _, hEq⟩ := completedHeckeL_conductor_data χ L Ldual hL h hLdual hdual
  let B (s : ℂ) := b * (q : ℂ) ^ s
  have hq₀ : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hB : Differentiable ℂ B :=
    (differentiable_id.const_cpow (Or.inl hq₀)).const_mul b
  have hB₀ (s : ℂ) : B s ≠ 0 :=
    mul_ne_zero hb (fun hz ↦ hq₀ ((Complex.cpow_eq_zero_iff _ _).mp hz).1)
  have hReflect : Differentiable ℂ (fun s : ℂ ↦ 1 - s) :=
    (differentiable_const (1 : ℂ)).sub differentiable_id
  refine ⟨fun s ↦ (B (1 - s))⁻¹ * a,
    ((hB.comp hReflect).inv (fun s ↦ hB₀ (1 - s))).mul_const a,
    fun s ↦ mul_ne_zero (inv_ne_zero (hB₀ (1 - s))) ha, ?_, hEq⟩
  intro u v
  let bnd (x : ℝ) := ‖b‖ * q ^ (1 - x) * ‖a‖⁻¹
  have hcont : Continuous bnd := by dsimp [bnd]; fun_prop (disch := positivity)
  obtain ⟨K, hK⟩ := isCompact_Icc (a := u) (b := v) |>.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun z hu hv ↦ ?_⟩
  have hp : 0 ≤ bnd z.re := by dsimp [bnd]; positivity
  have hbnd := hK z.re ⟨hu, hv⟩
  rw [Real.norm_of_nonneg hp] at hbnd
  simpa only [norm_inv, norm_mul, mul_inv, inv_inv, B, Complex.norm_cpow_eq_rpow_re_of_pos hq,
    Complex.sub_re, Complex.one_re, mul_comm ‖a‖⁻¹, bnd] using hbnd.trans (le_max_right 1 K)

/-- Paper: Proposition 3.2.1.3(3), p. 123. Reflecting the continuation of the
inverse unitary character gives the original continuation times a nowhere-vanishing
entire function. Inversion agrees with complex conjugation for a unitary character. -/
theorem completedHeckeL_continuation_functionalEquation (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hdual : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s) :
    ∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s, ε s ≠ 0) ∧
      ∀ s, Ldual (1 - s) = ε s * L s := by
  obtain ⟨ε, hε, hn, _, hEq⟩ := completedHeckeL_bounded_epsilon χ L Ldual hL h hLdual hdual
  exact ⟨ε, hε, hn, hEq⟩

/-- Removing the gamma factors preserves the same epsilon factor and its strip bound. -/
private theorem finiteHeckeL_bounded_epsilon (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hdual : ∀ s : halfPlane, Ldual s = finiteHeckeL χ⁻¹ s) :
    ∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s, ε s ≠ 0) ∧
      (∀ u v : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ, u ≤ z.re → z.re ≤ v → ‖(ε z)⁻¹‖ ≤ K) ∧
      L =ᶠ[codiscreteWithin univ] (fun s ↦ finiteHeckeReflectionFactor χ ε s * Ldual (1 - s)) := by
  let G (ψ : U[F]) := heckeGammaFactor ψ
  let Λ (ψ : U[F]) (A : ℂ → ℂ) := toMeromorphicNFOn (G ψ * A) univ
  have hm (ψ : U[F]) (A : ℂ → ℂ) (hA : MeromorphicNFOn A univ) :
      MeromorphicOn (G ψ * A) univ := (meromorphic_heckeGammaFactor ψ).meromorphicOn.mul hA.meromorphicOn
  have hNF (ψ : U[F]) (A : ℂ → ℂ) : MeromorphicNFOn (Λ ψ A) univ :=
    meromorphicNFOn_toMeromorphicNFOn _ _
  have hAgree (ψ : U[F]) (A : ℂ → ℂ) (hA : MeromorphicNFOn A univ)
      (hEq : ∀ s : halfPlane, A s = finiteHeckeL ψ s) (s : halfPlane) :
      Λ ψ A s = completedHeckeL ψ s := by
    have hs := zero_lt_one.trans s.property
    have han : AnalyticAt ℂ (G ψ) s := DifferentiableOn.analyticAt
      (s := {z : ℂ | 0 < z.re})
      (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos ψ hz).differentiableWithinAt)
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
    change toMeromorphicNFOn (G ψ * A) univ s = _
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (hm ψ A hA) (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr ((meromorphicNFAt_mul_iff_right han
        (heckeGammaFactor_ne_zero_of_re_pos ψ hs)).2 (hA (mem_univ _))), Pi.mul_apply, hEq]
    rfl
  obtain ⟨ε, hε, hε₀, hBound, hFE⟩ := completedHeckeL_bounded_epsilon χ
    (Λ χ L) (Λ χ⁻¹ Ldual) (hNF _ _) (hAgree _ _ hL h) (hNF _ _) (hAgree _ _ hLdual hdual)
  refine ⟨ε, hε, hε₀, hBound, ?_⟩
  have hγ := meromorphic_heckeGammaFactor χ
  have hRaw : MeromorphicOn (fun z ↦ (ε z)⁻¹ * (G χ⁻¹ (1 - z) / G χ z)) univ :=
    fun z _ ↦ (hε.analyticAt z).meromorphicAt.inv.mul
      ((((meromorphic_heckeGammaFactor χ⁻¹) (1 - z)).comp_analyticAt
        (analyticAt_const.sub analyticAt_id)).div (hγ z))
  have hγne : ∀ᶠ z in codiscreteWithin univ, G χ z ≠ 0 := by
    apply hγ.meromorphicOn.eventually_codiscreteWithin_apply_ne_zero
    intro z hz htop
    have he := hγ.meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ hz (mem_univ (2 : ℂ)) htop
    have hpos : ∀ᶠ w : ℂ in 𝓝 (2 : ℂ), 0 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    obtain ⟨w, hw, hw'⟩ := ((hpos.filter_mono nhdsWithin_le_nhds).and
      (meromorphicOrderAt_eq_top_iff.mp he)).exists
    exact heckeGammaFactor_ne_zero_of_re_pos χ hw hw'
  apply eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mpr
  intro z
  have href : Tendsto (fun w : ℂ ↦ 1 - w) (𝓝[≠] z) (𝓝[≠] (1 - z)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨((continuous_const.sub continuous_id).continuousAt.tendsto).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact fun he ↦ hw (sub_right_inj.mp he)
  have hdualNF := (toMeromorphicNFOn_eqOn_codiscrete (hm χ⁻¹ Ldual hLdual)).filter_mono
    (nhdsNE_le_codiscrete (1 - z))
  filter_upwards [(toMeromorphicNFOn_eqOn_codiscrete (hm χ L hL)).filter_mono (nhdsNE_le_codiscrete z),
    href.eventually hdualNF, (toMeromorphicNFOn_eqOn_codiscrete hRaw).filter_mono (nhdsNE_le_codiscrete z),
    hγne.filter_mono (nhdsNE_le_codiscrete z)] with w h₁ h₂ h₃ hw
  change (ε w)⁻¹ * (G χ⁻¹ (1 - w) / G χ w) = finiteHeckeReflectionFactor χ ε w at h₃
  have he := hFE w
  change G χ w * L w = Λ χ L w at h₁
  change G χ⁻¹ (1 - w) * Ldual (1 - w) = Λ χ⁻¹ Ldual (1 - w) at h₂
  rw [← h₁, ← h₂] at he
  rw [← h₃]
  field_simp [hw, hε₀]
  linear_combination -he

/-- Paper: Equation (3.2.1.8), p. 124. The finite continuations satisfy the
reflection equation with the displayed gamma ratio and a nowhere-vanishing entire
epsilon factor. Equality is taken off a discrete set, as an identity of meromorphic functions. -/
theorem finiteHeckeL_continuation_functionalEquation (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hdual : ∀ s : halfPlane, Ldual s = finiteHeckeL χ⁻¹ s) :
    ∃ ε : ℂ → ℂ, Differentiable ℂ ε ∧ (∀ s, ε s ≠ 0) ∧
      L =ᶠ[codiscreteWithin univ] (fun s ↦ finiteHeckeReflectionFactor χ ε s * Ldual (1 - s)) := by
  obtain ⟨ε, hε, hn, _, hEq⟩ := finiteHeckeL_bounded_epsilon χ L Ldual hL h hLdual hdual
  exact ⟨ε, hε, hn, hEq⟩

/-- At the trivial character, reflection in the functional equation transfers the
simple pole at one to a simple pole at zero. -/
private theorem completedHeckeL_one_order_zero (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (h : ∀ s : halfPlane, L s = completedHeckeL (1 : U[F]) s) :
    meromorphicOrderAt L 0 = -1 := by
  obtain ⟨ε, hε, hεne, hfun⟩ := completedHeckeL_continuation_functionalEquation
    (1 : U[F]) L L hL h hL (by simpa using h)
  have hcomp : meromorphicOrderAt (fun s ↦ L (1 - s)) 0 = meromorphicOrderAt L 1 := by
    have ha : AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) 0 := by fun_prop
    have hd : deriv (fun s : ℂ ↦ 1 - s) 0 ≠ 0 := by simp
    simpa [Function.comp_def] using meromorphicOrderAt_comp_of_deriv_ne_zero (f := L) ha hd
  have hεan := hε.analyticAt (z := 0)
  have hεord : meromorphicOrderAt ε 0 = 0 :=
    (hεan.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr (hεne 0)
  rw [show (fun s ↦ L (1 - s)) = ε * L from funext hfun,
    meromorphicOrderAt_mul hεan.meromorphicAt (hL (mem_univ _)).meromorphicAt,
    hεord, zero_add, completedHeckeL_one_order_one L hL h] at hcomp
  exact hcomp

/-- Paper: Proposition 3.2.1.3(2), p. 123. If the character is trivial on norm-one
classes, there is a unique real norm-twist parameter and the two indicated poles
are simple. The continuation is analytic elsewhere.
Deviation: The printed residue formulas have a normalization conflict described below. -/
theorem completedHeckeL_continuation_simplePoles (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    ∃! t : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * (t : ℂ)) ∧
      meromorphicOrderAt L (Complex.I * (t : ℂ)) = -1 ∧
      meromorphicOrderAt L (1 + Complex.I * (t : ℂ)) = -1 ∧
      AnalyticOnNhd ℂ L ({Complex.I * (t : ℂ), 1 + Complex.I * (t : ℂ)}ᶜ) := by
  obtain ⟨t, ht, huniq⟩ := existsUnique_ideleClassNormTwist χ hχ
  let b : ℂ := Complex.I * (t : ℂ)
  have hbre : b.re = 0 := by simp [b, Complex.mul_re]
  have hχ' : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-b) := by simpa [b] using ht
  let L₀ (s : ℂ) := L (s + b)
  have hL₀ : MeromorphicNFOn L₀ univ :=
    fun _ _ ↦ meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt.mpr (hL (mem_univ _))
  have h₀ (s : halfPlane) : L₀ s = completedHeckeL (1 : U[F]) s := by
    let w : halfPlane := ⟨(s : ℂ) + b, by
      change 1 < (s : ℂ).re + b.re
      rw [hbre, add_zero]
      exact s.property⟩
    change L w = _
    rw [h w, completedHeckeL_of_normTwist χ (-b) (by simp [hbre]) hχ' w]
    congr 1
    apply Subtype.ext
    change (s : ℂ) + b + -b = s
    simp
  refine ⟨t, ⟨ht, ?_, ?_, ?_⟩, fun u hu ↦ huniq u hu.1⟩
  · have ho := completedHeckeL_one_order_zero L₀ hL₀ h₀
    simpa [L₀, b, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt] using ho
  · have ho := completedHeckeL_one_order_one L₀ hL₀ h₀
    simpa [L₀, b, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt] using ho
  · intro s hs
    have hs₀ : s - b ∈ ({0, 1}ᶜ : Set ℂ) := by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs ⊢
      exact ⟨fun he ↦ hs.1 (sub_eq_zero.mp he), fun he ↦ hs.2 (sub_eq_iff_eq_add.mp he)⟩
    have ha := completedHeckeL_one_analyticOnNhd L₀ hL₀ h₀ (s - b) hs₀
    have hb := ha.comp (f := fun z : ℂ ↦ z - b) (show AnalyticAt ℂ (fun z : ℂ ↦ z - b) s by fun_prop)
    simpa [L₀, Function.comp_def] using hb

-- TODO(paper-gap): The residues printed in Proposition 3.2.1.3(2) disagree with the
-- Euler product normalization. For the trivial character of ℚ(√5), the residue at 1
-- is already the Appendix A.3.2.1 class volume, since both real gamma factors equal 1.

/-- Paper: Equation (3.2.2.3), p. 124. The theta Mellin integral is the idele-class
Tamagawa integral of the global theta function against the quasi-character. -/
def globalThetaMellinIntegral (f : ℬ[F]) (c : 𝒳[F]) : ℂ :=
  ∫ g : C[F], adelicTheta f g * c g ∂ideleClassTamagawaMeasure F

/-- Paper: Theorem 3.2.2.1(2), p. 124. The theta Mellin integral is absolutely
convergent on the right half-plane. -/
theorem globalThetaMellinIntegral_integrable (f : ℬ[F]) (c : 𝒳[F]) (hc : c ∈ rightHalf) :
    Integrable (fun g : C[F] ↦ adelicTheta f g * c g) (ideleClassTamagawaMeasure F) := by
  exact (globalIdelicZetaIntegral_eq_thetaIntegral f c hc).1

/-- Paper: Theorem 3.2.2.1(2), p. 124. Truncating the theta Mellin integral to
norm bands converges uniformly on every compact subset of the right half-plane. -/
theorem globalThetaMellinIntegral_tendstoUniformlyOn (f : ℬ[F]) (K : Set 𝒳[F])
    (hK : IsCompact K) (h : K ⊆ rightHalf) (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n c ↦
      ∫ g in {g : C[F] | classNormℝ g ∈ Icc (a n)⁻¹ (a n)}, adelicTheta f g * c g
        ∂ideleClassTamagawaMeasure F)
      (globalThetaMellinIntegral f) atTop K := by
  let : BorelSpace C[F] := ⟨rfl⟩
  exact tendstoUniformlyOn_character_normBands (ideleClassTamagawaMeasure F) id
    (adelicTheta f) K hK (fun c hc ↦ (globalIdelicZetaIntegral_eq_thetaIntegral f c (h hc)).1)
    a ha haTop tate_continuous_classNormReal.measurable

/-- Paper: Equation (3.2.2.11), p. 127. Unfolding theta on the right half-plane
identifies its Mellin integral with the zeta integral on the ideles. -/
theorem globalThetaMellinIntegral_eq_idelic (f : ℬ[F]) :
    EqOn (globalThetaMellinIntegral f) (globalIdelicZetaIntegral f) rightHalf := by
  intro c hc
  exact (globalIdelicZetaIntegral_eq_thetaIntegral f c hc).2.symm

/-- Rapid decay in absolute logarithmic norm absorbs any quasi-character.
Outside a compact band the weighted integrand is bounded by an integrable
multiple of the exponential of minus the absolute logarithmic norm. -/
private theorem integrable_twist_of_log_decay {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (q : X → C[F]) (hq : Continuous q) (φ : X → ℂ) (hφ : Continuous φ)
    (l : X → ℝ) (hl : IsProperMap l) (hlog : ∀ x, l x = Real.log (classNormℝ (q x)))
    (k : ℝ≥0) (hmap : μ.map l = k • volume)
    (hdecay : ∀ N : ℕ, ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ x, T < |l x| →
      ‖φ x‖ ≤ C * Real.exp (-(N : ℝ) * |l x|)) (c : 𝒳[F]) :
    Integrable (fun x ↦ φ x * c (q x)) μ := by
  let : T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  let σ := quasiCharacterAbscissa (G := C[F]) (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) c
  let N := ⌈|σ| + 1⌉₊
  obtain ⟨C, T, hC, _, hdec⟩ := hdecay N
  let S := l ⁻¹' Icc (-T) T
  let M (y : ℝ) := C * Real.exp (-|y|)
  have hM : Continuous M := continuous_const.mul (Real.continuous_exp.comp continuous_abs.neg)
  have hInt : Integrable M := by
    have h₁ : IntegrableOn M (Iic 0) := by
      refine IntegrableOn.congr_fun (Integrable.const_mul (integrableOn_exp_mul_Iic zero_lt_one 0) C)
        (fun y hy ↦ ?_) measurableSet_Iic
      simp [M, abs_of_nonpos (show y ≤ 0 from hy)]
    have h₂ : IntegrableOn M (Ioi 0) := by
      refine IntegrableOn.congr_fun (Integrable.const_mul (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr zero_lt_one) 0) C)
        (fun y hy ↦ ?_) measurableSet_Ioi
      simp [M, abs_of_pos (show 0 < y from hy)]
    simpa using h₁.union h₂
  have hIntMap : Integrable M (μ.map l) := by
    rw [hmap]
    exact hInt.smul_measure ENNReal.coe_ne_top
  have hmajor := (integrable_map_measure hM.aestronglyMeasurable
    hl.continuous.measurable.aemeasurable).mp hIntMap
  have hcont := hφ.mul (c.continuous.comp hq)
  have hS : MeasurableSet S := hl.continuous.measurable measurableSet_Icc
  rw [← integrableOn_univ, ← union_compl_self S, integrableOn_union]
  refine ⟨hcont.continuousOn.integrableOn_compact (hl.isCompact_preimage isCompact_Icc), ?_⟩
  refine hmajor.integrableOn.mono' hcont.aestronglyMeasurable
    ((ae_restrict_mem (μ := μ) hS.compl).mono fun x hx ↦ ?_)
  have hxT : T < |l x| := lt_of_not_ge fun h ↦ hx (abs_le.mp h)
  have hc : ‖c (q x)‖ = Real.exp (l x * σ) := by
    rw [hlog, ← Real.rpow_def_of_pos (tate_classNormReal_pos (q x))]
    exact norm_quasiCharacter_eq_rpow_abscissa (G := C[F]) (ideleClassNorm F) _ _ _ _
  rw [norm_mul, hc]
  calc
    _ ≤ (C * Real.exp (-(N : ℝ) * |l x|)) * Real.exp (l x * σ) :=
      mul_le_mul_of_nonneg_right (hdec x hxT) (Real.exp_pos _).le
    _ = C * Real.exp (-(N : ℝ) * |l x| + l x * σ) := by rw [Real.exp_add, mul_assoc]
    _ ≤ M (l x) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
      have h₁ : l x * σ ≤ |l x| * |σ| := (le_abs_self _).trans_eq (abs_mul _ _)
      have h₂ := mul_le_mul_of_nonneg_right (Nat.le_ceil (|σ| + 1)) (abs_nonneg (l x))
      dsimp only [N]
      linarith

/-- Paper: Theorem 3.2.2.1(2)(a), p. 124. If the test function and its Fourier
transform vanish at zero, the theta Mellin integral converges absolutely everywhere. -/
theorem globalThetaMellinIntegral_integrable_of_vanishing (f : ℬ[F])
    (hf : f zeroAdele = 0) (hFourier : adeleSchwartzFourier f zeroAdele = 0) (c : 𝒳[F]) :
    Integrable (fun g : C[F] ↦ adelicTheta f g * c g) (ideleClassTamagawaMeasure F) := by
  let : T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : BorelSpace C[F] := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))).symm
  obtain ⟨k, hk⟩ := tate_exists_map_logClassNorm_eq_smul_volume (F := F)
  apply integrable_twist_of_log_decay (ideleClassTamagawaMeasure F) id continuous_id
    (adelicTheta f) (adelicTheta f).continuous (e ∘ ideleClassNorm F)
    (e.isProperMap.comp (isProperMap_ideleClassNorm F)) (fun x ↦ he _) k
  · simpa only [Function.comp_def, he] using hk
  · simpa only [Function.comp_def, he, id_eq] using adelicTheta_decay_both f hf hFourier

/-- Paper: Theorem 3.2.2.1(2)(a), p. 124. If both zero terms vanish, norm-band
truncations of the theta Mellin integral converge uniformly on every compact set. -/
theorem globalThetaMellinIntegral_tendstoUniformlyOn_of_vanishing (f : ℬ[F])
    (hf : f zeroAdele = 0) (hFourier : adeleSchwartzFourier f zeroAdele = 0)
    (K : Set 𝒳[F]) (hK : IsCompact K) (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n c ↦
      ∫ g in {g : C[F] | classNormℝ g ∈ Icc (a n)⁻¹ (a n)}, adelicTheta f g * c g
        ∂ideleClassTamagawaMeasure F)
      (globalThetaMellinIntegral f) atTop K := by
  let : BorelSpace C[F] := ⟨rfl⟩
  exact tendstoUniformlyOn_character_normBands (ideleClassTamagawaMeasure F) id
    (adelicTheta f) K hK (fun c _ ↦ globalThetaMellinIntegral_integrable_of_vanishing f hf hFourier c)
    a ha haTop tate_continuous_classNormReal.measurable

/-- Paper: Theorem 3.2.2.1(2)(a), p. 124. With both zero terms vanishing, the
theta Mellin integral is entire in every complex norm-twist coordinate. -/
theorem globalThetaMellinIntegral_entire_of_vanishing (f : ℬ[F])
    (hf : f zeroAdele = 0) (hFourier : adeleSchwartzFourier f zeroAdele = 0) (χ : U[F]) :
    Differentiable ℂ (fun s ↦ globalThetaMellinIntegral f (ideleClassNormTwist χ s)) := by
  let : BorelSpace C[F] := ⟨rfl⟩
  apply differentiableOn_univ.mp
  exact (analyticOnNhd_integral_twist (ideleClassTamagawaMeasure F) id (adelicTheta f) χ
    univ isOpen_univ (fun z _ ↦ globalThetaMellinIntegral_integrable_of_vanishing f hf hFourier _)
    tate_continuous_classNormReal.measurable).differentiableOn

/-- Paper: Theorem 3.2.2.1(2)(a) and (3), pp. 124–125. When both zero terms
vanish, the entire theta Mellin transform agrees everywhere with the global Z-function. -/
theorem globalThetaMellinIntegral_eq_continuation_of_vanishing (f : ℬ[F])
    (hf : f zeroAdele = 0) (hFourier : adeleSchwartzFourier f zeroAdele = 0) :
    globalThetaMellinIntegral f = globalIdelicZFunction f := by
  let : T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  funext c
  let s := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F)) c
  let d := c * ideleClassNormTwist (1 : U[F]) (-(s : ℂ))
  have hpos (g : C[F]) : 0 < classNormℝ g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hd (g : C[F]) : ‖d g‖ = 1 := by
    change ‖c g * (1 * (classNormℝ g : ℂ) ^ (-(s : ℂ)))‖ = 1
    rw [one_mul, norm_mul, norm_quasiCharacter_eq_rpow_abscissa _
      (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)),
      Complex.norm_cpow_eq_rpow_re_of_pos (hpos g), Complex.neg_re, Complex.ofReal_re]
    change classNormℝ g ^ s * classNormℝ g ^ (-s) = 1
    rw [← Real.rpow_add (hpos g), add_neg_cancel, Real.rpow_zero]
  let χ : U[F] :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (hd g)⟩
      map_one' := Circle.ext (map_one d)
      map_mul' := fun g h ↦ Circle.ext (map_mul d g h)
      continuous_toFun := d.continuous.subtype_mk _ }
  have hc : ideleClassNormTwist χ s = c := by
    ext1 g
    change (c g * (1 * (classNormℝ g : ℂ) ^ (-(s : ℂ)))) *
      (classNormℝ g : ℂ) ^ (s : ℂ) = c g
    rw [one_mul, mul_assoc, ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr (hpos g).ne'), neg_add_cancel, Complex.cpow_zero, mul_one]
  let A (z : ℂ) := globalThetaMellinIntegral f (ideleClassNormTwist χ z)
  let Z (z : ℂ) := globalIdelicZFunction f (ideleClassNormTwist χ z)
  have hA : Differentiable ℂ A := globalThetaMellinIntegral_entire_of_vanishing f hf hFourier χ
  have hZ : MeromorphicNFOn Z univ := globalIdelicZFunction_meromorphic f χ
  have hEq (z : ℂ) (hz : 1 < z.re) : A z = Z z := by
    have hm : ideleClassNormTwist χ z ∈ rightHalf := by
      change 1 < quasiCharacterAbscissa _ _ _ _
      rwa [quasiCharacterAbscissa_ideleClassNormTwist]
    exact (globalThetaMellinIntegral_eq_idelic f hm).trans
      (globalIdelicZFunction_eq_integral f hm).symm
  have hnear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have htop : meromorphicOrderAt (A - Z) 2 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (eventuallyEq_iff_sub.mp
      ((hnear.mono hEq).filter_mono nhdsWithin_le_nhds))
  have hmA : MeromorphicNFOn A univ := fun z _ ↦ (hA.analyticAt z).meromorphicNFAt
  have ho := (hmA.meromorphicOn.sub hZ.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ (s : ℂ)) htop
  have hlocal : A =ᶠ[𝓝[≠] (s : ℂ)] Z :=
    eventuallyEq_iff_sub.mpr (meromorphicOrderAt_eq_top_iff.mp ho)
  rw [← hc]
  exact (((hmA (mem_univ _)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hZ (mem_univ _))).mp hlocal).eq_of_nhds

-- TODO(paper-gap): The absolute convergence asserted in Theorem 3.2.2.1(2)(b)
-- fails for nontrivial norm-one characters. The modulus of the quasi-character is
-- the same on every component at fixed abscissa, and the small-norm polar term persists.

/-- Paper: Theorem 3.2.2.1(2)(b), p. 125. The continuation of the theta Mellin
integral is the global Z-function and is entire on every nontrivial norm-one component.
Deviation: Entireness concerns the continuation of the integral from its region of convergence. -/
theorem globalIdelicZFunction_entire_of_nontrivial (f : ℬ[F]) (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    Differentiable ℂ (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)) := by
  have hrestrict (s w : ℂ)
      (he : ideleClassNormTwist χ s = ideleClassNormTwist (1 : U[F]) w) :
      χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext g
    have hg := DFunLike.congr_fun he g.val
    change (χ g.val : ℂ) * (classNormℝ g.val : ℂ) ^ s =
      1 * (classNormℝ g.val : ℂ) ^ w at hg
    have hn : classNormℝ g.val = 1 := by
      change (((ideleClassNorm F g.val).val : ℝ≥0) : ℝ) = 1
      rw [MonoidHom.mem_ker.mp g.property]
      rfl
    change (χ g.val : ℂ) = 1
    simpa [hn] using hg
  intro s
  apply ((globalIdelicZFunction_poles f χ).1 s ?_).differentiableAt
  refine ⟨fun he ↦ hχ (hrestrict s 0 (he.trans ?_)), fun he ↦ hχ (hrestrict s 1 he)⟩
  ext1 g
  change (1 : ℂ) = 1 * (classNormℝ g : ℂ) ^ (0 : ℂ)
  simp

set_option maxHeartbeats 1000000 in
/-- Paper: §3.4.3.1, p. 152. There is an adelic test function whose idelic zeta
integral equals the completed Euler product on the half-plane of absolute convergence.
The proof chooses a normalized adelic Gaussian.
Deviation: The finite Tamagawa unit masses are absorbed by scaling the test function.
The complex Gaussian uses the opposite angular weight to the character. -/
theorem exists_globalIdelicZetaIntegral_eq_completedHeckeL (χ : U[F]) :
    ∃ f : ℬ[F], ∀ s : halfPlane,
      globalIdelicZetaIntegral f (ideleClassNormTwist χ s) = completedHeckeL χ s := by
  obtain ⟨fArch, hArch⟩ := exists_archimedeanHeckeTest χ
  obtain ⟨f, a, ha, hf⟩ := exists_globalHeckeTest χ fArch
  refine ⟨a⁻¹ • f, fun s ↦ ?_⟩
  have hscale : globalIdelicZetaIntegral (a⁻¹ • f) (ideleClassNormTwist χ s) =
      a⁻¹ * globalIdelicZetaIntegral f (ideleClassNormTwist χ s) := by
    let integrand (g : 𝕀[F]) := f (Multiplicative.ofAdd g.val) * (ideleClassNormTwist χ s) (classOf g)
    calc
      _ = ∫ g, a⁻¹ * integrand g ∂multiplicativeTamagawaMeasure F := by
        apply integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
        change (a⁻¹ * f (Multiplicative.ofAdd g.val)) * (ideleClassNormTwist χ s) (classOf g) =
          a⁻¹ * (f (Multiplicative.ofAdd g.val) * (ideleClassNormTwist χ s) (classOf g))
        exact mul_assoc _ _ _
      _ = _ := integral_const_mul (μ := multiplicativeTamagawaMeasure F) a⁻¹ integrand
  rw [hscale, hf s, hArch s, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  rfl

/-- Paper: Proposition 3.2.1.3(1), p. 123. When the restriction to norm-one
classes is nontrivial, the continuation is entire. -/
theorem completedHeckeL_continuation_entire (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    Differentiable ℂ L := by
  obtain ⟨f, hf⟩ := exists_globalIdelicZetaIntegral_eq_completedHeckeL χ
  let Z (s : ℂ) := globalIdelicZFunction f (ideleClassNormTwist χ s)
  have hZ : Differentiable ℂ Z := globalIdelicZFunction_entire_of_nontrivial f χ hχ
  have hZNF : MeromorphicNFOn Z univ := globalIdelicZFunction_meromorphic f χ
  have hEq : EqOn L Z halfPlane := by
    intro s hs
    have habs : quasiCharacterAbscissa (ideleClassNorm F)
        (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F))
        (ideleClassNormTwist χ s) = s.re :=
      quasiCharacterAbscissa_of_unitary_twist (ideleClassNorm F) _ _ _ χ s (fun _ ↦ rfl)
    have hmem : ideleClassNormTwist χ s ∈ rightHalf := by
      change 1 < quasiCharacterAbscissa _ _ _ _
      rwa [habs]
    exact (h ⟨s, hs⟩).trans
      ((globalIdelicZFunction_eq_integral f hmem).trans (hf ⟨s, hs⟩)).symm
  have h₂ : ∀ᶠ s in 𝓝 (2 : ℂ), s ∈ halfPlane :=
    (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (by norm_num)
  have hnear : L =ᶠ[𝓝[≠] (2 : ℂ)] Z :=
    (h₂.mono hEq).filter_mono nhdsWithin_le_nhds
  have htop : meromorphicOrderAt (L - Z) (2 : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (eventuallyEq_iff_sub.mp hnear)
  have hsub := hL.meromorphicOn.sub hZNF.meromorphicOn
  -- The difference vanishes as a meromorphic germ everywhere by connectedness.
  have hident : L = Z := by
    funext s
    have horder := hsub.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (mem_univ (2 : ℂ)) (mem_univ s) htop
    have hlocal : L =ᶠ[𝓝[≠] s] Z :=
      eventuallyEq_iff_sub.mpr (meromorphicOrderAt_eq_top_iff.mp horder)
    exact (((hL (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (hZNF (mem_univ s))).mp hlocal).eq_of_nhds
  rwa [hident]

section HeckeZeros

local notation "χ₀(" χ ")" => ideleClassNormTwist χ 0

/-- The Euler product gives a nonzero value in its half-plane of absolute convergence. -/
theorem finiteHeckeL_ne_zero_of_one_lt_re (χ : U[F]) (s : halfPlane) :
    finiteHeckeL χ s ≠ 0 := by
  have hs : 1 < (s : ℂ).re := s.property
  rw [← (finiteHeckeL_hasProd χ s).tprod_eq]
  have hsum : Summable (fun v ↦ ‖finiteHeckeEulerFactor χ v s - 1‖) := by
    have hq : Summable (fun v : HeightOneSpectrum (𝓞 F) ↦
        (v.asIdeal.absNorm : ℝ) ^ (-(s : ℂ).re)) :=
      (summable_absNorm_rpow F hs).comp_injective (fun _ _ he ↦ HeightOneSpectrum.ext he)
    exact (hq.mul_left 2).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun v ↦ norm_finiteHeckeEulerFactor_sub_one_le χ v hs le_rfl)
  have hn (v : HeightOneSpectrum (𝓞 F)) : finiteHeckeEulerFactor χ v s ≠ 0 := by
    classical
    unfold finiteHeckeEulerFactor
    split_ifs
    · apply inv_ne_zero
      have hq : (1 : ℝ) < v.asIdeal.absNorm := by
        exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hlt : ‖χ₀(χ).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ))‖ < 1 := by
        rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul, ← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re]
        exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
      exact fun he ↦ hlt.ne (by rw [← sub_eq_zero.mp he, norm_one])
    · exact one_ne_zero
  simpa only [add_sub_cancel] using
    (tprod_one_add_ne_zero_of_summable
      (f := fun v ↦ finiteHeckeEulerFactor χ v s - 1)
      (fun v ↦ by simpa only [add_sub_cancel] using hn v) hsum)

/-- A single real or complex gamma factor, with its Deligne exponential prefactor. -/
private def scaledArchGamma (q d : ℝ) (z : ℂ) :=
  (q : ℂ) ^ (-(z / d)) * Complex.Gamma (z / d)

/-- Reflection reverses the height of the gamma argument. The fixed imaginary
translation and dilation change its power bound by a bounded factor on a strip. -/
private theorem scaledArchGamma_reflection_bound (q d : ℝ) (hq : 0 < q) (hd : 0 < d)
    (p : ℂ) (hp : p.re = 0) (m a b : ℝ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| →
      ‖scaledArchGamma q d (1 - s - p + m) / scaledArchGamma q d (s + p + m)‖ ≤
        C * |s.im| ^ ((1 - 2 * s.re) / d) := by
  let M := max 1 ((1 + |a| + |b| + |m|) / d)
  obtain ⟨C, hC, hΓ⟩ := norm_Gamma_div_le_rpow_on_strip (le_max_left 1 ((1 + |a| + |b| + |m|) / d))
  let K := Icc (1 / (2 * d)) (2 / d) ×ˢ Icc a b
  let e (r : ℝ) := (1 - 2 * r) / d
  let weight (z : ℝ × ℝ) := q ^ (-e z.2) * z.1 ^ e z.2
  have hw : ContinuousOn weight K := by
    apply ContinuousOn.mul
    · exact (continuous_const.rpow (by dsimp [e]; fun_prop) (fun _ ↦ Or.inl hq.ne')).continuousOn
    · apply continuous_fst.continuousOn.rpow (by dsimp [e]; fun_prop)
      intro z hz
      exact Or.inl ((show 0 < 1 / (2 * d) by positivity).trans_le hz.1.1).ne'
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hw
  refine ⟨C * max 1 B, 2 * (d + |p.im|), mul_pos hC (lt_of_lt_of_le zero_lt_one (le_max_left _ _)),
    by positivity, fun s hs₁ hs₂ hsT ↦ ?_⟩
  let x := (1 - s.re + m) / d
  let y := (s.re + m) / d
  let t := (s.im + p.im) / d
  let v := |t| / |s.im|
  have hsabs : |s.re| ≤ |a| + |b| := abs_le.mpr
    ⟨by linarith [neg_abs_le a, abs_nonneg b], by linarith [le_abs_self b, abs_nonneg a]⟩
  have hx : |x| ≤ M := by
    apply le_trans _ (le_max_right _ _)
    rw [abs_div, abs_of_pos hd]
    apply div_le_div_of_nonneg_right _ hd.le
    rw [abs_le] at hsabs ⊢
    constructor <;> linarith [neg_abs_le m, le_abs_self m]
  have hy : |y| ≤ M := by
    apply le_trans _ (le_max_right _ _)
    rw [abs_div, abs_of_pos hd]
    apply div_le_div_of_nonneg_right _ hd.le
    linarith [abs_add_le s.re m]
  have hspos : 0 < |s.im| := by linarith [abs_nonneg p.im]
  have habs : |s.im| - |p.im| ≤ |s.im + p.im| := by
    have h := abs_add_le (s.im + p.im) (-p.im)
    simpa only [add_neg_cancel_right, abs_neg, sub_le_iff_le_add] using h
  have ht : 1 ≤ |t| := by
    rw [abs_div, abs_of_pos hd, le_div_iff₀ hd]
    linarith [abs_nonneg p.im]
  have hv : v ∈ Icc (1 / (2 * d)) (2 / d) := by
    dsimp only [v,t]
    rw [abs_div, abs_of_pos hd, div_div]
    constructor
    · rw [div_le_div_iff₀ (by positivity) (mul_pos hd hspos)]
      nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ 2 * |s.im + p.im| - |s.im|)]
    · rw [div_le_div_iff₀ (mul_pos hd hspos) hd]
      nlinarith [mul_nonneg hd.le (by linarith [abs_add_le s.im p.im, abs_nonneg p.im] :
        0 ≤ 2 * |s.im| - |s.im + p.im|)]
  have hE : x - y = e s.re := by dsimp [x,y,e]; ring
  have hnum : (1 - s - p + m) / (d : ℂ) = (starRingEnd ℂ) (⟨x,t⟩ : ℂ) := by
    apply Complex.ext <;> simp [Complex.div_ofReal_re, Complex.div_ofReal_im, x, t, hp]
    ring
  have hden : (s + p + m) / (d : ℂ) = (⟨y,t⟩ : ℂ) := by
    apply Complex.ext <;> simp [Complex.div_ofReal_re, Complex.div_ofReal_im, y, t, hp]
  have hnorm : ‖scaledArchGamma q d (1 - s - p + m) / scaledArchGamma q d (s + p + m)‖ =
      q ^ (-e s.re) * ‖Complex.Gamma ⟨x,t⟩ / Complex.Gamma ⟨y,t⟩‖ := by
    simp only [scaledArchGamma, hnum, hden, mul_div_mul_comm, norm_mul, norm_div,
      Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re, Complex.conj_re,
      Complex.Gamma_conj, Complex.norm_conj]
    rw [← Real.rpow_sub hq, ← hE]
    congr 2
    ring
  have hweight := hB (v, s.re) (show (v, s.re) ∈ K from ⟨hv, hs₁, hs₂⟩)
  rw [Real.norm_of_nonneg (show 0 ≤ weight (v,s.re) from
    mul_nonneg (Real.rpow_pos_of_pos hq _).le (Real.rpow_nonneg ((by positivity : 0 < 1 / (2 * d)).le.trans hv.1) _))] at hweight
  have hfactor : |t| = v * |s.im| := (div_mul_cancel₀ _ hspos.ne').symm
  rw [hnorm]
  calc
    _ ≤ q ^ (-e s.re) * (C * |t| ^ (x - y)) :=
      mul_le_mul_of_nonneg_left (hΓ x y t hx hy ht) (Real.rpow_pos_of_pos hq _).le
    _ = (C * weight (v,s.re)) * |s.im| ^ e s.re := by
      rw [hE, hfactor, Real.mul_rpow (div_nonneg (abs_nonneg _) hspos.le) hspos.le]
      dsimp [weight]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hweight.trans (le_max_right _ _)) hC.le) (Real.rpow_nonneg hspos.le _)

/-- On a closed vertical strip at large absolute height, the reflected Hecke gamma
ratio has polynomial bound with exponent `[F : ℚ] * (1 / 2 - Re(s))`. -/
theorem heckeGamma_reflection_bound (χ : U[F]) (a b : ℝ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| →
      ‖heckeGammaFactor χ⁻¹ (1 - s) / heckeGammaFactor χ s‖ ≤
        C * |s.im| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) := by
  classical
  let localΓ (ψ : U[F]) (v : InfinitePlace F) (z : ℂ) :=
    if hv : v.IsReal then
      let p := (realHeckeCharacter_parameters ψ v hv).exists.choose
      Complex.Gammaℝ (z + p.1 + (p.2.val : ℂ))
    else
      let p := (complexHeckeCharacter_parameters ψ v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      Complex.Gammaℂ (z + p.1 + (p.2.natAbs : ℂ) / 2) / 2
  have hlocal (v : InfinitePlace F) :
      ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| →
        ‖localΓ χ⁻¹ v (1 - s) / localΓ χ v s‖ ≤ C * |s.im| ^ ((v.mult : ℝ) * (1 / 2 - s.re)) := by
    by_cases hv : v.IsReal
    · let p := (realHeckeCharacter_parameters χ v hv).exists.choose
      obtain ⟨C,T,hC,hT,h⟩ := scaledArchGamma_reflection_bound Real.pi 2 Real.pi_pos (by norm_num)
        p.1 (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1 p.2.val a b
      refine ⟨C,T,hC,hT, fun s hs₁ hs₂ ht ↦ ?_⟩
      simpa only [localΓ, dite_eq_left hv, realHecke_inverse_parameters, scaledArchGamma, Complex.Gammaℝ_def,
        Complex.ofReal_ofNat, Complex.ofReal_natCast, ← sub_eq_add_neg, neg_div, hv.mult_eq_one,
        Nat.cast_one, one_mul, p, show (1 - 2 * s.re) / 2 = 1 / 2 - s.re by ring]
        using h s hs₁ hs₂ ht
    · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let p := (complexHeckeCharacter_parameters χ v hv').exists.choose
      obtain ⟨C,T,hC,hT,h⟩ := scaledArchGamma_reflection_bound (2 * Real.pi) 1 (by positivity) zero_lt_one
        p.1 (complexHeckeCharacter_parameters χ v hv').exists.choose_spec.1 (p.2.natAbs / 2) a b
      have hform (z : ℂ) : Complex.Gammaℂ z / 2 = scaledArchGamma (2 * Real.pi) 1 z := by
        rw [Complex.Gammaℂ_def]
        simp only [scaledArchGamma, Complex.ofReal_one, div_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
        ring
      refine ⟨C,T,hC,hT, fun s hs₁ hs₂ ht ↦ ?_⟩
      simpa only [localΓ, dite_eq_right hv, complexHecke_inverse_parameters, Int.natAbs_neg, hform,
        Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat, ← sub_eq_add_neg,
        hv'.mult_eq_two, Nat.cast_ofNat, div_one, p, show 2 * (1 / 2 - s.re) = 1 - 2 * s.re by ring]
        using h s hs₁ hs₂ ht
  choose C T hC hT h using hlocal
  let T₀ := 1 + ∑ v, T v
  have hTv (v : InfinitePlace F) : T v ≤ T₀ := by
    have := Finset.single_le_sum (f := T) (fun w _ ↦ (hT w).le) (Finset.mem_univ v)
    dsimp [T₀]
    linarith
  refine ⟨∏ v, C v, T₀, Finset.prod_pos (fun v _ ↦ hC v), by exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun v _ ↦ (hT v).le)), fun s hs₁ hs₂ ht ↦ ?_⟩
  have hpos : 0 < |s.im| := (hT (Classical.arbitrary (InfinitePlace F))).trans_le
    ((hTv _).trans ht)
  change ‖(∏ v, localΓ χ⁻¹ v (1 - s)) / ∏ v, localΓ χ v s‖ ≤ _
  rw [← Finset.prod_div_distrib, norm_prod]
  calc
    _ ≤ ∏ v, C v * |s.im| ^ ((v.mult : ℝ) * (1 / 2 - s.re)) :=
      Finset.prod_le_prod₀ (fun v _ ↦ norm_nonneg _) (fun v _ ↦ h v s hs₁ hs₂ ((hTv v).trans ht))
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hpos, ← Finset.sum_mul,
        ← Nat.cast_sum, InfinitePlace.sum_mult_eq]

/-- The reflected Hecke gamma ratio has polynomial growth on every closed vertical strip. -/
alias heckeGammaFactor_reflection_bound_on_strip := heckeGamma_reflection_bound

/-- Paper: Equation (3.2.1.10), p. 124. On a fixed closed vertical strip with
nonnegative real part, the reflection multiplier satisfies the stated power bound
as the absolute imaginary part tends to infinity. -/
theorem finiteHeckeReflectionFactor_bound (χ : U[F]) (L Ldual ε : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ) (hdual : ∀ s : halfPlane, Ldual s = finiteHeckeL χ⁻¹ s)
    (hε : Differentiable ℂ ε) (hn : ∀ s, ε s ≠ 0)
    (hEq : L =ᶠ[codiscreteWithin univ] (fun s ↦ finiteHeckeReflectionFactor χ ε s * Ldual (1 - s)))
    (α β : ℝ) (hα : 0 ≤ α) (hβ : α ≤ β) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ s : ℂ, α ≤ s.re → s.re ≤ β → T ≤ |s.im| →
      ‖finiteHeckeReflectionFactor χ ε s‖ ≤ C * |s.im| ^
        ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) := by
  clear hε hn hα hβ
  obtain ⟨δ, hδ, hδne, hδB, hδeq⟩ := finiteHeckeL_bounded_epsilon χ L Ldual hL h hLdual hdual
  let D (z : ℂ) := Ldual (1 - z)
  have hD : MeromorphicOn D univ := fun z _ ↦ (hLdual (mem_univ _)).meromorphicAt.comp_analyticAt
    (analyticAt_const.sub analyticAt_id)
  have hD₂ : Ldual 2 ≠ 0 := by
    have u : (2 : ℂ) ∈ halfPlane := by norm_num
    rw [hdual ⟨2,u⟩]
    exact finiteHeckeL_ne_zero_of_one_lt_re _ _
  have ha₂ : AnalyticAt ℂ Ldual 2 := (hLdual (mem_univ _)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((hLdual (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr hD₂).ge
  have hD₁ : meromorphicOrderAt D (-1) ≠ ⊤ := by
    have ha : AnalyticAt ℂ D (-1) := ha₂.comp_of_eq (analyticAt_const.sub analyticAt_id) (by norm_num)
    have hn : D (-1) ≠ 0 := by norm_num [D, hD₂]
    rw [ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn]
    exact WithTop.zero_ne_top
  have hDne := hD.eventually_codiscreteWithin_apply_ne_zero fun z hz ↦
    hD.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ _) hz hD₁
  let R (z : ℂ) := heckeGammaFactor χ⁻¹ (1 - z) / heckeGammaFactor χ z
  have hm : MeromorphicOn (fun z ↦ (δ z)⁻¹ * R z) univ := fun z _ ↦
    (hδ.analyticAt z).meromorphicAt.inv.mul
      ((((meromorphic_heckeGammaFactor χ⁻¹) _).comp_analyticAt (analyticAt_const.sub analyticAt_id)).div
        ((meromorphic_heckeGammaFactor χ) z))
  have heq : finiteHeckeReflectionFactor χ ε =ᶠ[codiscreteWithin univ] fun z ↦ (δ z)⁻¹ * R z := by
    filter_upwards [hEq, hδeq, hDne, toMeromorphicNFOn_eqOn_codiscrete hm] with z hz hδz hDz hR
    exact (mul_right_cancel₀ hDz (hz.symm.trans hδz)).trans hR.symm
  obtain ⟨K, hK, hk⟩ := hδB (α - 1) (β + 1)
  obtain ⟨C, T, hC, hT, hb⟩ := heckeGamma_reflection_bound χ (α - 1) (β + 1)
  let power (z : ℂ) := |z.im| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - z.re))
  refine ⟨K * C, T + 1, mul_pos hK hC, by linarith, fun s hsα hsβ hsT ↦ ?_⟩
  by_cases hzero : finiteHeckeReflectionFactor χ ε s = 0
  · rw [hzero, norm_zero]
    positivity
  have hW : MeromorphicNFAt (finiteHeckeReflectionFactor χ ε) s := meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ s)
  have hWcont := (hW.meromorphicOrderAt_nonneg_iff_analyticAt.mp (hW.meromorphicOrderAt_eq_zero_iff.mpr hzero).ge).continuousAt
  have hp : ContinuousAt power s := Complex.continuous_im.abs.continuousAt.rpow
    (by fun_prop) (Or.inl (by linarith : |s.im| ≠ 0))
  apply le_of_tendsto_of_tendsto (b := 𝓝[≠] s) (hWcont.norm.tendsto.mono_left nhdsWithin_le_nhds)
    ((continuousAt_const.mul hp).tendsto.mono_left nhdsWithin_le_nhds)
  have hnear : ∀ᶠ z : ℂ in 𝓝 s, α - 1 < z.re ∧ z.re < β + 1 ∧ T < |z.im| :=
    ((Complex.continuous_re.tendsto s).eventually (eventually_gt_nhds (by linarith))).and
      (((Complex.continuous_re.tendsto s).eventually (eventually_lt_nhds (by linarith))).and
        ((Complex.continuous_im.abs.tendsto s).eventually (eventually_gt_nhds (by linarith))))
  filter_upwards [heq.filter_mono (nhdsNE_le_codiscrete s), hnear.filter_mono nhdsWithin_le_nhds] with z hz hzt
  rw [hz, norm_mul]
  exact (mul_le_mul (hk z hzt.1.le hzt.2.1.le) (hb z hzt.1.le hzt.2.1.le hzt.2.2.le)
    (norm_nonneg _) hK.le).trans_eq (mul_assoc _ _ _).symm

open Complex in
/-- The inequality for the three Euler factors with a common radius and a unit phase. -/
private theorem one_le_norm_eulerFactor_product {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    1 ≤ ‖(1 - (r : ℂ))⁻¹ ^ 3 * (1 - (r : ℂ) * z)⁻¹ ^ 4 *
      (1 - (r : ℂ) * z ^ 2)⁻¹‖ := by
  have h₀ : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_of_nonneg hr]; exact hr₁
  have h₁ : ‖(r : ℂ) * z‖ < 1 := by simpa [norm_mul, hz] using h₀
  have h₂ : ‖(r : ℂ) * z ^ 2‖ < 1 := by simpa [norm_mul, norm_pow, hz] using h₀
  have hinv {w : ℂ} (hw : ‖w‖ < 1) : (1 - w)⁻¹ = exp (-log (1 - w)) := by
    rw [exp_neg, exp_log (fun h ↦ hw.ne (by rw [← sub_eq_zero.mp h, norm_one]))]
  rw [hinv h₀, hinv h₁, hinv h₂, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add,
    norm_exp, Real.one_le_exp_iff]
  simp only [add_re, mul_re, re_ofNat, im_ofNat, Nat.cast_ofNat, zero_mul, sub_zero]
  rw [← ((hasSum_re (hasSum_taylorSeries_neg_log h₀)).mul_left 3 |>.add
    ((hasSum_re (hasSum_taylorSeries_neg_log h₁)).mul_left 4) |>.add
    (hasSum_re (hasSum_taylorSeries_neg_log h₂))).tsum_eq]
  apply tsum_nonneg
  intro n
  simp only [mul_pow, ← ofReal_pow, div_natCast_re, ofReal_re, mul_re, ofReal_im, zero_mul,
    sub_zero, ← mul_div_assoc, ← add_div]
  apply div_nonneg _ (Nat.cast_nonneg _)
  have hnorm : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  have him := sq_norm_sub_sq_re (z ^ n)
  rw [hnorm, one_pow] at him
  rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, pow_two (z ^ n), mul_re]
  have hident :
      3 * r ^ n + 4 * (r ^ n * (z ^ n).re) + r ^ n *
        ((z ^ n).re * (z ^ n).re - (z ^ n).im * (z ^ n).im) =
      2 * r ^ n * ((z ^ n).re + 1) ^ 2 := by
    rw [← sq ((z ^ n).im), ← him]
    ring
  rw [hident]
  positivity

/-- The de la Vallée Poussin Euler-product inequality for the trivial character, a unitary
character, and its square at ordinates in the ratio zero, one, and two. -/
private theorem norm_finiteHeckeL_product_ge_one (χ : U[F]) {x : ℝ} (hx : 1 < x)
    (a : ℂ) (ha : a.re = 0) :
    1 ≤ ‖χ₀((1 : U[F])).LSeries (x : ℂ) ^ 3 * χ₀(χ).LSeries ((x : ℂ) + a) ^ 4 *
      χ₀(χ ^ 2).LSeries ((x : ℂ) + 2 * a)‖ := by
  classical
  have h₂a : (2 * a).re = 0 := by simp [Complex.mul_re, ha]
  let s₀ : halfPlane := ⟨(x : ℂ), hx⟩
  let s₁ : halfPlane := ⟨(x : ℂ) + a, by simpa [mem_preimage, Complex.add_re, ha]⟩
  let s₂ : halfPlane := ⟨(x : ℂ) + 2 * a, by simpa [mem_preimage, Complex.add_re, h₂a]⟩
  have hp := (((finiteHeckeL_hasProd (1 : U[F]) s₀).pow 3).mul
    ((finiteHeckeL_hasProd χ s₁).pow 4)).mul (finiteHeckeL_hasProd (χ ^ 2) s₂)
  apply ge_of_tendsto' hp.norm
  intro T
  rw [norm_prod]
  refine Finset.one_le_prod₀ fun v _ ↦ ?_
  change 1 ≤ ‖finiteHeckeEulerFactor (1 : U[F]) v x ^ 3 *
    finiteHeckeEulerFactor χ v ((x : ℂ) + a) ^ 4 *
    finiteHeckeEulerFactor (χ ^ 2) v ((x : ℂ) + 2 * a)‖
  have hres (ψ : U[F]) (u : (v.adicCompletion F)ˣ) :
      χ₀(ψ).restrict v (u : v.adicCompletion F) =
        (ψ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℂ) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (ψ _ : ℂ) * _ ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
  have hres_one (u : (v.adicCompletion F)ˣ) :
      χ₀((1 : U[F])).restrict v (u : v.adicCompletion F) = 1 := by
    rw [hres, PontryaginDual.one_apply, Circle.coe_one]
  have hres_sq (u : (v.adicCompletion F)ˣ) :
      χ₀(χ ^ 2).restrict v (u : v.adicCompletion F) =
        (χ₀(χ).restrict v (u : v.adicCompletion F)) ^ 2 := by
    rw [hres, hres]
    rfl
  have hu₀ : χ₀((1 : U[F])).IsUnramifiedAt v := HeckeCharacter.isUnramifiedAt_iff.mpr
    fun u ↦ hres_one (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u)
  have hu₂ (hu : χ₀(χ).IsUnramifiedAt v) : χ₀(χ ^ 2).IsUnramifiedAt v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun u ↦ by
      rw [show χ₀(χ ^ 2).restrict v u = (χ₀(χ).restrict v u) ^ 2 from
        hres_sq (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u),
        hu.restrict_apply_unit_eq_one, one_pow]
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hv₀ : χ₀((1 : U[F])).localValue v = 1 := hres_one u
  have hv₂ : χ₀(χ ^ 2).localValue v = (χ₀(χ).localValue v) ^ 2 := hres_sq u
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.ne'
  let r := q ^ (-x)
  have hr : 0 ≤ r := Real.rpow_nonneg hq₀.le _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  let z (ψ : U[F]) (b : ℂ) := χ₀(ψ).localValue v * (q : ℂ) ^ (-b)
  have hz (ψ : U[F]) (b : ℂ) (hb : b.re = 0) : ‖z ψ b‖ = 1 := by
    simp [z, norm_ideleClassNormTwist_zero_localValue,
      Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.neg_re, hb]
  have hphase (ψ : U[F]) (b : ℂ) :
      χ₀(ψ).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-((x : ℂ) + b)) =
        (r : ℂ) * z ψ b := by
    change χ₀(ψ).localValue v * (q : ℂ) ^ (-((x : ℂ) + b)) = _
    rw [neg_add, Complex.cpow_add _ _ hqC, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow hq₀.le]
    exact mul_left_comm ..
  have hsq : z (χ ^ 2) (2 * a) = z χ a ^ 2 := by
    simp only [z, hv₂, mul_pow, neg_mul_eq_mul_neg]
    rw [show (2 : ℂ) = (↑(2 : ℕ) : ℂ) by norm_num, Complex.cpow_nat_mul]
  rw [finiteHeckeEulerFactor, ite_eq_left hu₀, hv₀, one_mul]
  change 1 ≤ ‖(1 - (q : ℂ) ^ (-(x : ℂ)))⁻¹ ^ 3 * _ * _‖
  rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hq₀.le]
  by_cases hu : χ₀(χ).IsUnramifiedAt v
  · rw [finiteHeckeEulerFactor, ite_eq_left hu, finiteHeckeEulerFactor, ite_eq_left (hu₂ hu),
      hphase χ a, hphase (χ ^ 2) (2 * a), hsq]
    exact one_le_norm_eulerFactor_product hr hr₁ (hz χ a ha)
  · rw [finiteHeckeEulerFactor, ite_eq_right hu, one_pow, mul_one, finiteHeckeEulerFactor]
    have hrnorm : ‖(1 : ℂ) - (r : ℂ)‖ = 1 - r := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (sub_nonneg.mpr hr₁.le)]
    split_ifs
    · rw [hphase (χ ^ 2) (2 * a)]
      let w := (r : ℂ) * z (χ ^ 2) (2 * a)
      change 1 ≤ ‖(1 - (r : ℂ))⁻¹ ^ 3 * (1 - w)⁻¹‖
      have hw : ‖w‖ = r := by
        rw [show ‖w‖ = ‖(r : ℂ)‖ * ‖z (χ ^ 2) (2 * a)‖ from norm_mul _ _,
          hz _ _ h₂a, Complex.norm_of_nonneg hr, mul_one]
      have hpos : 0 < ‖(1 : ℂ) - w‖ := norm_pos_iff.mpr fun h ↦
        hr₁.ne (by rw [← hw, ← sub_eq_zero.mp h, norm_one])
      rw [norm_mul, norm_pow, norm_inv, norm_inv, hrnorm, inv_pow, ← mul_inv,
        one_le_inv₀ (mul_pos (pow_pos (sub_pos.mpr hr₁) 3) hpos)]
      have hle : ‖(1 : ℂ) - w‖ ≤ 1 + r := by
        simpa only [hw, norm_one] using norm_sub_le (1 : ℂ) w
      calc
        (1 - r) ^ 3 * ‖(1 : ℂ) - w‖ ≤ (1 - r) ^ 3 * (1 + r) :=
          mul_le_mul_of_nonneg_left hle (pow_nonneg (sub_nonneg.mpr hr₁.le) _)
        _ = (1 - r) ^ 2 * (1 - r ^ 2) := by ring
        _ ≤ (1 - r) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg r]) (sq_nonneg _)
        _ ≤ 1 := by
          rw [mul_one]
          exact pow_le_one₀ (sub_nonneg.mpr hr₁.le) (by linarith)
    · rw [mul_one, norm_pow, norm_inv, hrnorm, inv_pow,
        one_le_inv₀ (pow_pos (sub_pos.mpr hr₁) 3)]
      exact pow_le_one₀ (sub_nonneg.mpr hr₁.le) (by linarith)

open scoped ComplexOrder in
/-- Pairing the trivial and a quadratic local Euler series gives nonnegative coefficients.
When the uniformizer has value minus one, the coefficients alternate between one and zero. -/
private theorem quadratic_localEulerFactor_nonneg (ψ : 𝒳[F]) (hψ : ∀ g, ψ g ^ 2 = 1)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    0 ≤ ((1 : 𝒳[F]).localEulerFactor v * ψ.localEulerFactor v) n := by
  classical
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hres (c : 𝒳[F]) (t : (v.adicCompletion F)ˣ) :
      c.restrict v t = c (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v t) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hunit (t : (v.adicCompletion F)ˣ) : (1 : 𝒳[F]).restrict v t = 1 := hres 1 t
  have hu : (1 : 𝒳[F]).IsUnramifiedAt v := HeckeCharacter.isUnramifiedAt_iff.mpr
    fun t ↦ hunit (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom t)
  have hv : (1 : 𝒳[F]).localValue v = 1 := hunit u
  have hs : ψ.localValue v ^ 2 = 1 := by
    change ψ.restrict v u ^ 2 = 1
    rw [hres]
    exact hψ _
  let b := if ψ.IsUnramifiedAt v then ψ.localValue v else 0
  have hb : b = 0 ∨ b = 1 ∨ b = -1 := by
    by_cases h : ψ.IsUnramifiedAt v
    · exact Or.inr (by simpa only [b, ite_eq_left h] using (sq_eq_one_iff.mp hs))
    · exact Or.inl (ite_eq_right h)
  have hq := HeightOneSpectrum.one_lt_absNorm v
  rw [HeckeCharacter.localEulerFactor, HeckeCharacter.localEulerFactor,
    card_residueField_adicCompletion, ← map_mul, hecke_localPowerSeries_eq_mk,
    hecke_localPowerSeries_eq_mk, ite_eq_left hu, hv]
  change 0 ≤ ArithmeticFunction.ofPowerSeries v.asIdeal.absNorm
    (PowerSeries.mk (fun k ↦ (1 : ℂ) ^ k) * PowerSeries.mk (fun k ↦ b ^ k)) n
  by_cases hn : n ∈ range (v.asIdeal.absNorm ^ · : ℕ → ℕ)
  · obtain ⟨k, rfl⟩ := hn
    rw [ArithmeticFunction.ofPowerSeries_apply_pow hq, mul_comm (PowerSeries.mk _) _, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk, one_pow, mul_one]
    rcases hb with h | h | h
    · rw [h]
      exact Finset.sum_nonneg fun i _ ↦ pow_nonneg le_rfl _
    · rw [h]
      exact Finset.sum_nonneg fun i _ ↦ by simp
    · rw [h, neg_one_geom_sum]
      split <;> simp
  · rw [ArithmeticFunction.ofPowerSeries_apply hq, Function.extend_apply' _ _ _ hn]
    exact le_rfl

open scoped ComplexOrder in
/-- Coefficients of the product of the two global Dirichlet series are limits of the
coefficients of their paired local factors. -/
private theorem quadratic_LFunction_coefficients (ψ : 𝒳[F]) (hψ : ∀ g, ψ g ^ 2 = 1) :
    let A := (1 : 𝒳[F]).LFunction * ψ.LFunction
    (∀ n, 0 ≤ A n) ∧ A 1 = 1 := by
  classical
  let P (c : 𝒳[F]) (S : Finset (HeightOneSpectrum (𝓞 F))) := ∏ v ∈ S, c.localEulerFactor v
  have hlim (n : ℕ) : ∀ᶠ S in atTop, (P 1 S * P ψ S) n = ((1 : 𝒳[F]).LFunction * ψ.LFunction) n := by
    filter_upwards [(Filter.eventually_all_finset n.divisorsAntidiagonal).mpr
      (fun p _ ↦ (heckeLocalEulerFactor_eventually_prod_eq (1 : 𝒳[F]) p.1).and
        (heckeLocalEulerFactor_eventually_prod_eq ψ p.2))] with S hS
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    exact Finset.sum_congr rfl fun p hp ↦ congrArg₂ (· * ·) (hS p hp).1 (hS p hp).2
  constructor
  · intro n
    obtain ⟨S, hS⟩ := (hlim n).exists
    rw [← hS]
    dsimp only [P]
    rw [← Finset.prod_mul_distrib]
    suffices ∀ m, 0 ≤ (∏ v ∈ S, (1 : 𝒳[F]).localEulerFactor v * ψ.localEulerFactor v) m from this n
    clear hS
    induction S using Finset.induction_on with
    | empty =>
      intro m
      simp only [Finset.prod_empty, ArithmeticFunction.one_apply]
      split <;> simp
    | @insert v S hv ih =>
      intro m
      rw [Finset.prod_insert hv, ArithmeticFunction.mul_apply]
      exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (quadratic_localEulerFactor_nonneg ψ hψ v _) (ih _)
  · obtain ⟨S, hS⟩ := (hlim 1).exists
    rw [← hS, ArithmeticFunction.mul_apply_one]
    have hone (c : 𝒳[F]) : P c S 1 = 1 := by
      clear hS
      induction S using Finset.induction_on with
      | empty => simp [P]
      | @insert v S hv ih =>
        dsimp only [P] at *
        rw [Finset.prod_insert hv, ArithmeticFunction.mul_apply_one, ih, mul_one,
          HeckeCharacter.localEulerFactor, ArithmeticFunction.ofPowerSeries_apply_one,
          HeckeCharacter.localPowerSeries, PowerSeries.constantCoeff_invOfUnit]
        rfl
    rw [hone, hone, one_mul]

/-- An imaginary translation of the Euler product is the Euler product of the translated
unitary character. -/
private theorem finiteHeckeL_imaginary_twist (χ ψ : U[F]) (a : ℂ) (ha : a.re = 0)
    (hψ : χ₀(ψ) = ideleClassNormTwist χ a) (s : halfPlane) :
    finiteHeckeL ψ s = finiteHeckeL χ ⟨(s : ℂ) + a, by
      change 1 < (s : ℂ).re + a.re
      rw [ha, add_zero]
      exact s.property⟩ := by
  let w : halfPlane := ⟨(s : ℂ) + a, by
    change 1 < (s : ℂ).re + a.re
    rw [ha, add_zero]
    exact s.property⟩
  apply (finiteHeckeL_hasProd ψ s).unique ((finiteHeckeL_hasProd χ w).congr_fun ?_)
  intro v
  have hval (t : (v.adicCompletion F)ˣ) :
      χ₀(ψ).restrict v t = χ₀(χ).restrict v t * (‖(t : v.adicCompletion F)‖ : ℂ) ^ a := by
    rw [hψ, HeckeCharacter.restrict, HeckeCharacter.restrict,
      MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    change _ * (classNormℝ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v t) : ℂ) ^ a =
      (_ * _ ^ (0 : ℂ)) * _
    dsimp only
    rw [Complex.cpow_zero, mul_one, ideleClassNorm_ofAdicCompletion]
    rfl
  have hu : χ₀(ψ).IsUnramifiedAt v ↔ χ₀(χ).IsUnramifiedAt v := by
    rw [HeckeCharacter.isUnramifiedAt_iff, HeckeCharacter.isUnramifiedAt_iff]
    apply forall_congr'
    intro t
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom t
    have hn : ‖(u : v.adicCompletion F)‖ = 1 := by
      apply Valued.toNormedField.norm_eq_one_iff.mpr
      exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
        (show u ∈ (v.adicCompletionIntegers F).units from ⟨t.val.property, t.inv.property⟩)
    change χ₀(ψ).restrict v u = 1 ↔ χ₀(χ).restrict v u = 1
    rw [hval, hn, Complex.ofReal_one, Complex.one_cpow, mul_one]
  by_cases hx : χ₀(χ).IsUnramifiedAt v
  · let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
    have hn := norm_uniformizer_adicCompletion v _ hπ
    have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    rw [finiteHeckeEulerFactor, finiteHeckeEulerFactor, ite_eq_left hx, ite_eq_left (hu.mpr hx),
      hx.localValue_eq u hπ, (hu.mpr hx).localValue_eq u hπ, hval]
    change (1 - (_ * (‖(π : v.adicCompletion F)‖ : ℂ) ^ a) * _)⁻¹ = (1 - _ * _ ^ (-((s : ℂ) + a)))⁻¹
    rw [hn, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) a,
      ← Complex.cpow_neg, Complex.ofReal_natCast, mul_assoc, ← Complex.cpow_add _ _ hq]
    rw [show -a + -(s : ℂ) = -((s : ℂ) + a) by ring]
  · simp [finiteHeckeEulerFactor, hx, hu.not.mpr hx]

/-- The shift prescribed by the squared-character hypothesis is quadratic. -/
private theorem exists_quadratic_normTwist (χ : U[F]) (a : ℂ) (ha : a.re = 0)
    (hχ : χ₀(χ ^ 2) = ideleClassNormTwist (1 : U[F]) (-(2 * a))) :
    ∃ ψ : U[F], χ₀(ψ) = ideleClassNormTwist χ a ∧ ∀ g, χ₀(ψ) g ^ 2 = 1 := by
  let c := ideleClassNormTwist χ a
  have hnorm (g : C[F]) : ‖c g‖ = 1 := by
    change ‖(χ g : ℂ) * (classNormℝ g : ℂ) ^ a‖ = 1
    rw [norm_mul, Circle.norm_coe, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt _)), ha, Real.rpow_zero, one_mul]
  let ψ : U[F] :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hnorm g)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun x y ↦ Subtype.ext (map_mul c x y)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hψ : χ₀(ψ) = c := by
    ext1 g
    change c g * _ ^ (0 : ℂ) = c g
    simp
  refine ⟨ψ, hψ, fun g ↦ ?_⟩
  rw [hψ]
  change ((χ g : ℂ) * (classNormℝ g : ℂ) ^ a) ^ 2 = 1
  have he := DFunLike.congr_fun hχ g
  change (χ g : ℂ) ^ 2 * _ ^ (0 : ℂ) = 1 * (classNormℝ g : ℂ) ^ (-(2 * a)) at he
  rw [Complex.cpow_zero, mul_one, one_mul] at he
  rw [mul_pow, he, ← Complex.cpow_nat_mul, Complex.cpow_neg]
  apply inv_mul_cancel₀
  apply Complex.cpow_ne_zero_iff.mpr ∘ Or.inl
  exact Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'

/-- The reciprocal trivial gamma factor vanishes at every nonpositive even integer. -/
private theorem inv_heckeGammaFactor_one_neg_even (n : ℕ) :
    (heckeGammaFactor (1 : U[F]) (-(2 * n)))⁻¹ = 0 := by
  have hR := Complex.Gammaℝ_eq_zero_iff.mpr (⟨n, rfl⟩ : ∃ m : ℕ, -(2 * (n : ℂ)) = -(2 * m))
  have hC : Complex.Gammaℂ (-(2 * (n : ℂ))) = 0 := by
    rw [Complex.Gammaℂ_def, ← Nat.cast_ofNat (R := ℂ) (n := 2), ← Nat.cast_mul,
      Complex.Gamma_neg_nat_eq_zero, mul_zero]
  have hc := InfinitePlace.card_add_two_mul_card_eq_rank F
  have hd := Module.finrank_pos (R := ℚ) (M := F)
  rw [heckeGammaFactor_one, hR, hC, zero_div]
  by_cases hr : InfinitePlace.nrRealPlaces F = 0
  · have hcomp : InfinitePlace.nrComplexPlaces F ≠ 0 := by omega
    simp [hr, hcomp]
  · simp [hr]

/-- Multiplying the completed trivial function by an entire factor vanishing at both
poles gives an entire function after normalization. -/
private theorem completedHeckeL_cancel_poles (Z H : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hz : ∀ z : halfPlane, Z z = completedHeckeL (1 : U[F]) z) (hH : Differentiable ℂ H)
    (h₀ : H 0 = 0) (h₁ : H 1 = 0) :
    Differentiable ℂ (toMeromorphicNFOn (Z * H) univ) := by
  have hm : MeromorphicOn (Z * H) univ := fun z _ ↦
    (hZ (mem_univ z)).meromorphicAt.mul (hH.analyticAt z).meromorphicAt
  intro z
  apply AnalyticAt.differentiableAt
  apply (meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ z)]
  by_cases hbad : z ∈ ({0, 1} : Set ℂ)
  · have hord : meromorphicOrderAt Z z = -1 := by
      rcases hbad with hz' | hz'
      · rw [hz', completedHeckeL_one_order_zero Z hZ hz]
      · rw [mem_singleton_iff.mp hz', completedHeckeL_one_order_one Z hZ hz]
    have hv : H z = 0 := by
      rcases hbad with hz' | hz'
      · exact hz' ▸ h₀
      · exact (mem_singleton_iff.mp hz') ▸ h₁
    have hp : 0 < meromorphicOrderAt H z := lt_of_le_of_ne
      (hH.analyticAt z).meromorphicOrderAt_nonneg (fun he ↦
        (hH.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp he.symm hv)
    rw [meromorphicOrderAt_mul (hZ (mem_univ z)).meromorphicAt (hH.analyticAt z).meromorphicAt, hord]
    cases h : meromorphicOrderAt H z with
    | top => simp
    | coe i =>
      rw [h] at hp
      change 0 ≤ ((-1 + i : ℤ) : WithTop ℤ)
      have hi : (0 : ℤ) < i := by exact_mod_cast hp
      exact_mod_cast (show 0 ≤ -1 + i by omega)
  · exact ((completedHeckeL_one_analyticOnNhd Z hZ hz z hbad).mul (hH.analyticAt z)).meromorphicOrderAt_nonneg

/-- At any point where the trivial completion is analytic the normalized product has
its ordinary product value. -/
private theorem completedHeckeL_cancel_poles_apply {Z H : ℂ → ℂ} (hZ : MeromorphicNFOn Z univ)
    (hH : Differentiable ℂ H) {z : ℂ} (ha : AnalyticAt ℂ Z z) :
    toMeromorphicNFOn (Z * H) univ z = Z z * H z := by
  have hm : MeromorphicOn (Z * H) univ := fun w _ ↦
    (hZ (mem_univ w)).meromorphicAt.mul (hH.analyticAt w).meromorphicAt
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _),
    toMeromorphicNFAt_eq_self.mpr (ha.mul (hH.analyticAt z)).meromorphicNFAt]
  rfl

open scoped ComplexOrder in
/-- The exceptional case of boundary nonvanishing. The square of the character is the
norm twist whose continuation has a pole at the doubled ordinate. Translating the ordinate
to zero replaces the character by its twist by the norm to the power `s - 1`, which has
order dividing two. -/
private theorem completedHeckeL_order_nonpos_of_square_normTwist (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    {s : ℂ} (hs : s.re = 1)
    (hχ : χ₀(χ ^ 2) = ideleClassNormTwist (1 : U[F]) (-(2 * (s - 1)))) :
    meromorphicOrderAt L s ≤ 0 := by
  let a := s - 1
  have ha : a.re = 0 := by simp [a, hs]
  have h₁a : 1 + a = s := by simp [a]
  by_cases hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨t, ⟨ht, _, hPole, _⟩, _⟩ := completedHeckeL_continuation_simplePoles χ L hL h hk
    let b := Complex.I * (t : ℂ)
    have hpow : ideleClassNormTwist (1 : U[F]) (-(2 * b)) = ideleClassNormTwist (1 : U[F]) (-(2 * a)) := by
      rw [← hχ]
      ext1 g
      have he := DFunLike.congr_fun ht g
      change (χ g : ℂ) * _ ^ (0 : ℂ) = 1 * (classNormℝ g : ℂ) ^ (-Complex.I * (t : ℂ)) at he
      rw [Complex.cpow_zero, mul_one, one_mul, neg_mul] at he
      change 1 * _ ^ (-(2 * b)) = (χ g : ℂ) ^ 2 * _ ^ (0 : ℂ)
      rw [Complex.cpow_zero, mul_one, one_mul, he, ← Complex.cpow_nat_mul]
      congr 1
      dsimp only [b]
      push_cast
      ring
    have hab : b = a := by
      have he := trivial_normTwist_injective hpow
      linear_combination -he / 2
    rw [← h₁a, ← hab, hPole]
    decide
  by_contra! hpos
  have hzero : L s = 0 := by
    by_contra hn
    exact hpos.ne' ((hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr hn)
  obtain ⟨ψ, hψ, hsq⟩ := exists_quadratic_normTwist χ a ha hχ
  obtain ⟨Z, hZ, hz⟩ := completedHeckeL_exists_continuation (1 : U[F])
  let H (w : ℂ) := (heckeGammaFactor (1 : U[F]) w)⁻¹ *
    ((heckeGammaFactor χ (w + a))⁻¹ * L (w + a))
  have hH : Differentiable ℂ H := (differentiable_inv_heckeGammaFactor (1 : U[F])).mul
    (((differentiable_inv_heckeGammaFactor χ).comp (differentiable_id.add_const a)).mul
      ((completedHeckeL_continuation_entire χ L hL h hk).comp (differentiable_id.add_const a)))
  let P := toMeromorphicNFOn (Z * H) univ
  have hγ₀ : (heckeGammaFactor (1 : U[F]) 0)⁻¹ = 0 := by simpa using inv_heckeGammaFactor_one_neg_even (F := F) 0
  have hγ₂ : (heckeGammaFactor (1 : U[F]) (-2))⁻¹ = 0 := by simpa using inv_heckeGammaFactor_one_neg_even (F := F) 1
  have hP : Differentiable ℂ P := completedHeckeL_cancel_poles Z H hZ hz hH
    (by simp [H, hγ₀]) (by simp [H, h₁a, hzero])
  have hA (z : ℂ) (hz' : z ≠ 0 ∧ z ≠ 1) : P z = Z z * H z :=
    completedHeckeL_cancel_poles_apply hZ hH (completedHeckeL_one_analyticOnNhd Z hZ hz z (by simpa using hz'))
  have hP₂ : P (-2) = 0 := by rw [hA _ (by norm_num)]; simp [H, hγ₂]
  let A := (1 : 𝒳[F]).LFunction * χ₀(ψ).LFunction
  have htriv : χ₀((1 : U[F])) = 1 := by
    ext1 g
    change (1 : ℂ) * (classNormℝ g : ℂ) ^ (0 : ℂ) = 1
    simp
  have hsum (z : halfPlane) : LSeriesSummable (1 : 𝒳[F]).LFunction z := by
    rw [← htriv]
    exact finiteHeckeL_seriesSummable 1 z
  obtain ⟨hcoeff, hone⟩ := quadratic_LFunction_coefficients _ hsq
  have hpos₂ := ArithmeticFunction.LSeries_positive_of_differentiable_of_eqOn
    (a := A) hcoeff (by rw [show A 1 = 1 from hone]; exact zero_lt_one) hP (x := 1)
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun r hr ↦
      ArithmeticFunction.LSeriesSummable_mul (hsum ⟨(r : ℂ), hr⟩) (finiteHeckeL_seriesSummable ψ ⟨(r : ℂ), hr⟩))) (fun z hz' ↦ ?_) (-2)
  · simp only [Complex.ofReal_neg, Complex.ofReal_ofNat, hP₂, lt_self_iff_false] at hpos₂
  · let u : halfPlane := ⟨z, hz'⟩
    let w : halfPlane := ⟨z + a, by change 1 < z.re + a.re; rw [ha, add_zero]; exact hz'⟩
    have hne : z ≠ 0 ∧ z ≠ 1 := by
      constructor <;> rintro rfl <;> norm_num at hz'
    rw [hA z hne, hz u, ArithmeticFunction.LSeries_mul' (hsum u) (finiteHeckeL_seriesSummable ψ u)]
    change heckeGammaFactor (1 : U[F]) z * finiteHeckeL 1 u *
      ((heckeGammaFactor (1 : U[F]) z)⁻¹ * ((heckeGammaFactor χ (z + a))⁻¹ * L w)) =
      (1 : 𝒳[F]).LSeries z * finiteHeckeL ψ u
    rw [h w, finiteHeckeL_imaginary_twist χ ψ a ha hψ u]
    change _ * _ * (_ * (_ * (heckeGammaFactor χ (z + a) * finiteHeckeL χ w))) = _
    rw [show (1 : 𝒳[F]).LSeries z = finiteHeckeL 1 u from congrArg (fun c : 𝒳[F] ↦ c.LSeries z) htriv.symm]
    have hg : heckeGammaFactor (1 : U[F]) z ≠ 0 :=
      heckeGammaFactor_ne_zero_of_re_pos _ (zero_lt_one.trans u.property)
    have hg' : heckeGammaFactor χ (z + a) ≠ 0 :=
      heckeGammaFactor_ne_zero_of_re_pos _ (zero_lt_one.trans w.property)
    change _ = finiteHeckeL 1 u * finiteHeckeL χ w
    field_simp [hg, hg']

/-- Removing the gamma factor preserves meromorphic order in the positive half-plane. -/
private theorem meromorphicOrderAt_inv_gamma_mul (χ : U[F]) {L : ℂ → ℂ} {s : ℂ}
    (hs : 0 < s.re) :
    meromorphicOrderAt (fun w ↦ (heckeGammaFactor χ w)⁻¹ * L w) s =
      meromorphicOrderAt L s := by
  exact meromorphicOrderAt_mul_of_ne_zero
    ((differentiable_inv_heckeGammaFactor χ).analyticAt s)
    (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hs))

/-- On the line of real part one, a zero would make the product in the Euler-product
inequality tend to zero unless the squared character has a pole at the doubled ordinate. -/
private theorem completedHeckeL_order_nonpos_on_one_line (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    {s : ℂ} (hs : s.re = 1) :
    meromorphicOrderAt L s ≤ 0 := by
  let a := s - 1
  have ha : a.re = 0 := by simp [a, hs]
  have h₂a : (2 * a).re = 0 := by simp [Complex.mul_re, ha]
  have h₁ : 1 + a = s := by simp [a]
  by_cases hχ : χ₀(χ ^ 2) = ideleClassNormTwist (1 : U[F]) (-(2 * a))
  · exact completedHeckeL_order_nonpos_of_square_normTwist χ L hL h hs hχ
  by_contra! hzero
  obtain ⟨L₀, hL₀, h₀⟩ := completedHeckeL_exists_continuation (1 : U[F])
  obtain ⟨L₂, hL₂, h₂⟩ := completedHeckeL_exists_continuation (χ ^ 2)
  have han₂ : AnalyticAt ℂ L₂ (1 + 2 * a) := by
    by_cases hk : (χ ^ 2).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t, ⟨ht, _, _, han⟩, _⟩ := completedHeckeL_continuation_simplePoles _ L₂ hL₂ h₂ hk
      apply han
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro he
        have hre := congrArg Complex.re he
        simp [Complex.add_re, h₂a, Complex.mul_re] at hre
      · intro he
        apply hχ
        rw [add_right_inj] at he
        simpa only [he, neg_mul] using ht
    · exact (completedHeckeL_continuation_entire _ L₂ hL₂ h₂ hk).analyticAt _
  let G (ψ : U[F]) (M : ℂ → ℂ) (w : ℂ) := (heckeGammaFactor ψ w)⁻¹ * M w
  let G₀ := G (1 : U[F]) L₀
  let G₁ (w : ℂ) := G χ L (w + a)
  let G₂ (w : ℂ) := G (χ ^ 2) L₂ (w + 2 * a)
  have hG (ψ : U[F]) (M : ℂ → ℂ) (hM : MeromorphicNFOn M univ) (w : ℂ) :
      MeromorphicAt (G ψ M) w :=
    ((differentiable_inv_heckeGammaFactor ψ).analyticAt w).meromorphicAt.mul
      (hM (mem_univ w)).meromorphicAt
  have hG₀ := hG (1 : U[F]) L₀ hL₀ 1
  have hG₁ : MeromorphicAt G₁ 1 :=
    (hG χ L hL (1 + a)).comp_analyticAt (g := fun w ↦ w + a) (by fun_prop)
  have hG₂ : MeromorphicAt G₂ 1 :=
    (hG (χ ^ 2) L₂ hL₂ (1 + 2 * a)).comp_analyticAt (g := fun w ↦ w + 2 * a)
      (by fun_prop)
  have ho₀ : meromorphicOrderAt G₀ 1 = -1 := by
    exact (meromorphicOrderAt_inv_gamma_mul (1 : U[F])
      (s := 1) (by simp)).trans (completedHeckeL_one_order_one L₀ hL₀ h₀)
  have ho₁ : 1 ≤ meromorphicOrderAt G₁ 1 := by
    have hp : 0 < meromorphicOrderAt G₁ 1 := by
      change 0 < meromorphicOrderAt (fun w ↦ G χ L (w + a)) 1
      rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt, h₁,
        meromorphicOrderAt_inv_gamma_mul χ (by rw [hs]; exact zero_lt_one)]
      exact hzero
    cases horder : meromorphicOrderAt G₁ 1 with
    | top => exact le_top
    | coe n =>
      rw [horder] at hp
      exact_mod_cast (show (1 : ℤ) ≤ n by exact Int.add_one_le_of_lt (by exact_mod_cast hp))
  have ho₂ : 0 ≤ meromorphicOrderAt G₂ 1 := by
    change 0 ≤ meromorphicOrderAt (fun w ↦ G (χ ^ 2) L₂ (w + 2 * a)) 1
    rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt,
      meromorphicOrderAt_inv_gamma_mul (χ ^ 2) (by simp [Complex.add_re, h₂a])]
    exact han₂.meromorphicOrderAt_nonneg
  let P : ℂ → ℂ := G₀ ^ 3 * G₁ ^ 4 * G₂
  have hp : 0 < meromorphicOrderAt P 1 := by
    dsimp only [P]
    rw [meromorphicOrderAt_mul ((hG₀.pow 3).mul (hG₁.pow 4)) hG₂,
      meromorphicOrderAt_mul (hG₀.pow 3) (hG₁.pow 4),
      meromorphicOrderAt_pow hG₀, meromorphicOrderAt_pow hG₁, ho₀]
    simp only [Nat.cast_ofNat]
    have hlo : (0 : WithTop ℤ) < 3 * -1 + 4 * 1 + 0 := by
      change ((0 : ℤ) : WithTop ℤ) < ((3 * -1 + 4 * 1 + 0 : ℤ) : WithTop ℤ)
      exact WithTop.coe_lt_coe.mpr (by norm_num)
    apply hlo.trans_le
    gcongr
    apply (WithTop.mul_right_strictMono (a := (4 : WithTop ℤ)) _ (by decide)).monotone ho₁
    exact WithTop.coe_lt_coe.mpr (by norm_num : (0 : ℤ) < 4)
  have hpath : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousWithinAt (s := Ioi 1) (x := (1 : ℝ))).tendsto_nhdsWithin
        (fun x hx ↦ by simpa using hx.ne')
  have hlim := (tendsto_zero_of_meromorphicOrderAt_pos hp).comp hpath
  have hval (ψ : U[F]) (M : ℂ → ℂ)
      (hM : ∀ w : halfPlane, M w = completedHeckeL ψ w) (w : halfPlane) :
      G ψ M w = χ₀(ψ).LSeries w := by
    dsimp only [G]
    rw [hM w, completedHeckeL, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact heckeGammaFactor_ne_zero_of_re_pos ψ (zero_lt_one.trans w.property)
  have hbound : ∀ᶠ x : ℝ in 𝓝[>] 1, 1 ≤ ‖P (x : ℂ)‖ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx : 1 < x := hx
    have hx₀ : (x : ℂ) ∈ halfPlane := hx
    have hx₁ : (x : ℂ) + a ∈ halfPlane := by simpa [mem_preimage, Complex.add_re, ha]
    have hx₂ : (x : ℂ) + 2 * a ∈ halfPlane := by simpa [mem_preimage, Complex.add_re, h₂a]
    change 1 ≤ ‖G (1 : U[F]) L₀ x ^ 3 * G χ L ((x : ℂ) + a) ^ 4 *
      G (χ ^ 2) L₂ ((x : ℂ) + 2 * a)‖
    rw [hval _ L₀ h₀ ⟨_, hx₀⟩, hval _ L h ⟨_, hx₁⟩, hval _ L₂ h₂ ⟨_, hx₂⟩]
    exact norm_finiteHeckeL_product_ge_one χ hx a ha
  have hbad : (1 : ℝ) ≤ ‖(0 : ℂ)‖ := ge_of_tendsto hlim.norm hbound
  exact (by norm_num : ¬ (1 : ℝ) ≤ ‖(0 : ℂ)‖) hbad

/-- Paper: Proposition 3.2.1.3(4), p. 123. A zero of the continuation in
the positive half-plane lies strictly to the left of `Re(s) = 1`. -/
theorem completedHeckeL_continuation_zeros (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (h : ∀ s : halfPlane, L s = completedHeckeL χ s)
    {s : ℂ} (hs : 0 < s.re) (hzero : 0 < meromorphicOrderAt L s) :
    s.re < 1 := by
  by_contra! hge
  rcases hge.eq_or_lt with he | hgt
  · exact (not_lt_of_ge (completedHeckeL_order_nonpos_on_one_line χ L hL h he.symm)) hzero
  · have hn : L s ≠ 0 := by
      rw [show L s = completedHeckeL χ ⟨s, hgt⟩ from h ⟨s, hgt⟩, completedHeckeL]
      exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hs)
        (finiteHeckeL_ne_zero_of_one_lt_re χ ⟨s, hgt⟩)
    have ho := (hL (mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr hn
    exact (not_lt_of_ge ho.le) hzero

end HeckeZeros

section HomogeneousMellin

local notation "χ₁[" F "]" => PontryaginDual (MonoidHom.ker (ideleClassNorm F))
local notation "componentStrip" =>
  componentVerticalStrip (ideleClassNorm F) (isProperMap_ideleClassNorm F)
    (ideleClassNorm_ne_one (F := F))
local notation "mellinIntegrand" =>
  fun (τ : ℝ≥0ˣ →ₜ* 𝕀[F]) (ω : χ₁[F]) (f : ℬ[F]) (c : 𝒳[F]) (t : ℝ≥0ˣ) ↦
    homogeneousAdelicTheta ω f (classOf (τ t)) * c (classOf (τ t))

/-- Paper: Equation (3.2.2.4), p. 125. The homogeneous theta Mellin integral
uses a continuous homomorphic section of the idelic norm and the measure `dt/t`. -/
def homogeneousThetaMellinIntegral (τ : ℝ≥0ˣ →ₜ* 𝕀[F]) (ω : χ₁[F])
    (f : ℬ[F]) (c : 𝒳[F]) : ℂ :=
  ∫ t, mellinIntegrand τ ω f c t ∂positiveRealHaar

variable (τ : ℝ≥0ˣ →ₜ* 𝕀[F])
variable (ω : χ₁[F]) (f : ℬ[F])

/-- Paper: Equation (3.2.2.4), p. 125. For the squared norm character, the
Mellin weight on the section is the square of the positive real parameter. -/
theorem homogeneousThetaMellinIntegral_normSquared (hτ : RightInverse τ (ideleNorm F)) :
    homogeneousThetaMellinIntegral τ (1 : χ₁[F]) f (ideleClassNormTwist (1 : U[F]) 2) =
      ∫ t : ℝ≥0ˣ, homogeneousAdelicTheta (1 : χ₁[F]) f (classOf (τ t)) *
        (t.val : ℂ) ^ (2 : ℕ) ∂positiveRealHaar := by
  unfold homogeneousThetaMellinIntegral
  congr 1
  funext t
  beta_reduce
  congr 1
  change (((1 : U[F]) (classOf (τ t)) : Circle) : ℂ) *
    (classNormℝ (classOf (τ t)) : ℂ) ^ (2 : ℂ) = _
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_ofNat]
  change (((ideleNorm F (τ t) : ℝ≥0) : ℝ) : ℂ) ^ 2 = _
  rw [hτ t]

/-- Fubini in norm and norm-one coordinates. The component condition gives
the character weight in the inner integral. -/
private theorem homogeneousThetaMellin_weil (hτ : RightInverse τ (ideleNorm F)) (c : 𝒳[F])
    (hc : c ∈ componentStrip ω (Ioi 1)) :
    Integrable (mellinIntegrand τ ω f c) positiveRealHaar ∧
      globalThetaMellinIntegral f c = homogeneousThetaMellinIntegral τ ω f c := by
  let σ (t : ℝ≥0ˣ) : C[F] := classOf (τ t)
  have hσ : Continuous σ := continuous_quotient_mk'.comp τ.continuous
  let ν := normOneIdeleClassTamagawaMeasure F
  let : BorelSpace C[F] := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let j (p : ℝ≥0ˣ × (ideleClassNorm F).ker) := σ p.1 * p.2.val
  have hj : Measurable j :=
    ((hσ.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).measurable
  let W (g : C[F]) := adelicTheta f g * c g
  have hw : AEStronglyMeasurable W (ideleClassTamagawaMeasure F) :=
    ((adelicTheta f).continuous.mul c.continuous).aestronglyMeasurable
  have hmap : (positiveRealHaar.prod ν).map j = ideleClassTamagawaMeasure F :=
    classTamagawa_normProduct σ hσ hτ
  rw [← hmap] at hw
  have hi : Integrable (W ∘ j) (positiveRealHaar.prod ν) := by
    apply (integrable_map_measure hw hj.aemeasurable).mp
    rw [hmap]
    exact (globalIdelicZetaIntegral_eq_thetaIntegral f c hc.1).1
  have hfibre (t : ℝ≥0ˣ) : (∫ u, (W ∘ j) (t, u) ∂ν) = mellinIntegrand τ ω f c t := by
    have he (u : (ideleClassNorm F).ker) :
        (W ∘ j) (t, u) = (adelicTheta f (u.val * σ t) * (ω u : ℂ)) * c (σ t) := by
      change adelicTheta f (σ t * u.val) * c (σ t * u.val) = _
      rw [show c (σ t * u.val) = c (σ t) * c u.val from map_mul c _ _, show c u.val = (ω u : ℂ) from hc.2 u, mul_comm (σ t) u.val]
      ring
    simp_rw [he, integral_mul_const]
    rfl
  refine ⟨hi.integral_prod_left.congr (.of_forall hfibre), ?_⟩
  change (∫ g, W g ∂ideleClassTamagawaMeasure F) = _
  rw [← hmap, integral_map hj.aemeasurable hw]
  exact (integral_prod (W ∘ j) hi).trans (integral_congr_ae (.of_forall hfibre))

/-- Paper: Theorem 3.2.2.1(3), p. 125. The homogeneous theta Mellin integral
converges absolutely on the right half-plane of the component indexed by ω. -/
theorem homogeneousThetaMellinIntegral_integrable (hτ : RightInverse τ (ideleNorm F)) (c : 𝒳[F])
    (hc : c ∈ componentStrip ω (Ioi 1)) :
    Integrable (mellinIntegrand τ ω f c) positiveRealHaar := by
  exact (homogeneousThetaMellin_weil τ ω f hτ c hc).1

private theorem homogeneousThetaMellin_tendstoUniformlyOn_of_integrable
    (hτ : RightInverse τ (ideleNorm F)) (K : Set 𝒳[F]) (hK : IsCompact K)
    (hInt : ∀ c ∈ K, Integrable (mellinIntegrand τ ω f c) positiveRealHaar)
    (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n c ↦
      ∫ t in {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc (a n)⁻¹ (a n)}, mellinIntegrand τ ω f c t
        ∂positiveRealHaar) (homogeneousThetaMellinIntegral τ ω f) atTop K := by
  let q (t : ℝ≥0ˣ) : C[F] := classOf (τ t)
  have hq : Continuous q := continuous_quotient_mk'.comp τ.continuous
  have hn (t : ℝ≥0ˣ) : classNormℝ (q t) = (t.val : ℝ) := congrArg (fun u : ℝ≥0ˣ ↦ (u.val : ℝ)) (hτ t)
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  unfold homogeneousThetaMellinIntegral
  simpa only [hn, q] using tendstoUniformlyOn_character_normBands positiveRealHaar q
    (fun t ↦ homogeneousAdelicTheta ω f (q t)) K hK hInt a ha haTop
    (tate_continuous_classNormReal.comp hq).measurable

/-- Paper: Theorem 3.2.2.1(3), p. 125. Norm-band truncations of the homogeneous
theta Mellin integral converge uniformly on compact subsets of that right half-plane. -/
theorem homogeneousThetaMellinIntegral_tendstoUniformlyOn
    (hτ : RightInverse τ (ideleNorm F))
    (K : Set 𝒳[F]) (hK : IsCompact K) (h : K ⊆ componentStrip ω (Ioi 1))
    (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n c ↦
      ∫ t in {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc (a n)⁻¹ (a n)},
        mellinIntegrand τ ω f c t ∂positiveRealHaar)
      (homogeneousThetaMellinIntegral τ ω f) atTop K := by
  exact homogeneousThetaMellin_tendstoUniformlyOn_of_integrable τ ω f hτ K hK
    (fun c hc ↦ homogeneousThetaMellinIntegral_integrable τ ω f hτ c (h hc)) a ha haTop

/-- Paper: Theorem 3.2.2.1(3)(a) and (b), p. 125. The homogeneous theta Mellin
integral converges absolutely throughout the component when both zero terms
vanish or when the norm-one character is nontrivial. -/
theorem homogeneousThetaMellinIntegral_integrable_on_component
    (hτ : RightInverse τ (ideleNorm F))
    (h : f ∈ adelePolarSubspace F ∨ ω ≠ 1) (c : 𝒳[F]) (hc : c ∈ componentStrip ω univ) :
    Integrable (mellinIntegrand τ ω f c) positiveRealHaar := by
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let q (y : ℝ) : C[F] := classOf (τ (E y))
  have hq : Continuous q := continuous_quotient_mk'.comp (τ.continuous.comp E.continuous)
  have hn (y : ℝ) : classNormℝ (q y) = Real.exp y := by
    change ((ideleNorm F (τ (E y)) : ℝ≥0) : ℝ) = _
    rw [hτ]
    rfl
  have hl (y : ℝ) : id y = Real.log (classNormℝ (q y)) := by simp [hn]
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  have hμ : positiveRealHaar = volume.map E := by
    unfold positiveRealHaar
    congr 1
    funext y
    apply Units.ext
    exact NNReal.coe_inj.mp (Real.coe_toNNReal _ (Real.exp_pos y).le)
  rw [hμ]
  apply E.toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mpr
  apply integrable_twist_of_log_decay volume q hq (fun y ↦ homogeneousAdelicTheta ω f (q y))
    ((homogeneousAdelicTheta ω f).continuous.comp hq) id isProperMap_id hl 1 (by simp)
  intro N
  obtain ⟨C, T, hC, hT, hbound⟩ := homogeneousAdelicTheta_decay_both ω f h N
  exact ⟨C, T, hC, hT, fun y hy ↦ by simpa only [← hl] using hbound (q y) ((hl y) ▸ hy)⟩

/-- Paper: Theorem 3.2.2.1(3)(a) and (b), p. 125. When both zero terms vanish
or the norm-one character is nontrivial, norm-band truncations converge
uniformly on every compact subset of the component. -/
theorem homogeneousThetaMellinIntegral_tendstoUniformlyOn_component
    (hτ : RightInverse τ (ideleNorm F))
    (h : f ∈ adelePolarSubspace F ∨ ω ≠ 1)
    (K : Set 𝒳[F]) (hK : IsCompact K) (hcomponent : K ⊆ componentStrip ω univ)
    (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n) (haTop : Tendsto a atTop atTop) :
    TendstoUniformlyOn (fun n c ↦
      ∫ t in {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc (a n)⁻¹ (a n)},
        mellinIntegrand τ ω f c t ∂positiveRealHaar)
      (homogeneousThetaMellinIntegral τ ω f) atTop K := by
  exact homogeneousThetaMellin_tendstoUniformlyOn_of_integrable τ ω f hτ K hK
    (fun c hc ↦ homogeneousThetaMellinIntegral_integrable_on_component τ ω f hτ h c (hcomponent hc))
    a ha haTop

/-- Paper: Theorem 3.2.2.1(3)(a) and (b), p. 125. In either case of
convergence throughout the component, the integral is entire in its
complex norm-twist coordinate. -/
theorem homogeneousThetaMellinIntegral_entire_on_component
    (hτ : RightInverse τ (ideleNorm F))
    (h : f ∈ adelePolarSubspace F ∨ ω ≠ 1) (χ : U[F])
    (hχ : ∀ g : (ideleClassNorm F).ker, χ g.val = ω g) :
    Differentiable ℂ (fun s ↦
      homogeneousThetaMellinIntegral τ ω f (ideleClassNormTwist χ s)) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let q (t : ℝ≥0ˣ) : C[F] := classOf (τ t)
  have hq : Continuous q := continuous_quotient_mk'.comp τ.continuous
  apply differentiableOn_univ.mp
  apply AnalyticOnNhd.differentiableOn
  apply analyticOnNhd_integral_twist positiveRealHaar q (fun t ↦ homogeneousAdelicTheta ω f (q t))
    χ univ isOpen_univ _ (tate_continuous_classNormReal.comp hq).measurable
  intro z _
  apply homogeneousThetaMellinIntegral_integrable_on_component τ ω f hτ h
  refine ⟨mem_univ _, fun g ↦ ?_⟩
  change (χ g.val : ℂ) * (classNormℝ g.val : ℂ) ^ z = (ω g : ℂ)
  simp [MonoidHom.mem_ker.mp g.property, hχ g]

-- The fiber integral in the proof on p. 127 needs the character weight ω(h).
-- Definition 2.2.5.1 includes this weight in homogeneousAdelicTheta.

/-- Paper: Equation (3.2.2.5), p. 125. On the right half-plane of a component,
Weil integration identifies the theta Mellin integral with the homogeneous integral. -/
theorem globalThetaMellinIntegral_eq_homogeneous (hτ : RightInverse τ (ideleNorm F)) :
    EqOn (globalThetaMellinIntegral f) (homogeneousThetaMellinIntegral τ ω f)
      (componentStrip ω (Ioi 1)) := by
  exact fun c hc ↦ (homogeneousThetaMellin_weil τ ω f hτ c hc).2

/-- Paper: Equation (3.2.2.5), p. 125. The global Z-function in the component's
norm-twist coordinate is the unique meromorphic continuation of the homogeneous
theta Mellin integral. The theta Mellin integral has the same continuation by
its equality with the homogeneous integral on the right half-plane.
Deviation: Meromorphic continuation is expressed in Mathlib's normal form. -/
theorem homogeneousThetaMellinIntegral_meromorphicContinuation
    (hτ : RightInverse τ (ideleNorm F)) (χ : U[F])
    (hχ : ∀ g : (ideleClassNorm F).ker, χ g.val = ω g) (M : ℂ → ℂ) :
    (MeromorphicNFOn M univ ∧ EqOn M (fun s ↦
      homogeneousThetaMellinIntegral τ ω f (ideleClassNormTwist χ s)) halfPlane) ↔
    M = fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s) := by
  have hstrip (s : ℂ) (hs : 1 < s.re) :
      ideleClassNormTwist χ s ∈ componentStrip ω (Ioi 1) := by
    constructor
    · change 1 < quasiCharacterAbscissa _ _ _ _
      rwa [quasiCharacterAbscissa_ideleClassNormTwist]
    · intro g
      change (χ g.val : ℂ) * (classNormℝ g.val : ℂ) ^ s = (ω g : ℂ)
      have hn : classNormℝ g.val = 1 := by
        change (((ideleClassNorm F g.val).val : ℝ≥0) : ℝ) = 1
        rw [MonoidHom.mem_ker.mp g.property]
        rfl
      simp [hn, hχ g]
  have hZ (s : ℂ) (hs : 1 < s.re) :
      globalIdelicZFunction f (ideleClassNormTwist χ s) =
        globalIdelicZetaIntegral f (ideleClassNormTwist χ s) :=
    globalIdelicZFunction_eq_integral f (hstrip s hs).1
  have hHom (s : ℂ) (hs : 1 < s.re) :
      homogeneousThetaMellinIntegral τ ω f (ideleClassNormTwist χ s) =
        globalIdelicZetaIntegral f (ideleClassNormTwist χ s) :=
    ((globalThetaMellinIntegral_eq_homogeneous τ ω f hτ) (hstrip s hs)).symm.trans
      (globalThetaMellinIntegral_eq_idelic f (hstrip s hs).1)
  constructor
  · rintro ⟨hM, hEq⟩
    funext s
    exact globalIdelicZetaIntegral_chartContinuation_eq f hM
      (globalIdelicZFunction_meromorphic f χ) (fun z hz ↦ (hEq hz).trans (hHom z hz))
      hZ (show ideleClassNormTwist χ s = ideleClassNormTwist χ s from rfl)
  · rintro rfl
    exact ⟨globalIdelicZFunction_meromorphic f χ, fun s hs ↦ (hZ s hs).trans (hHom s hs).symm⟩

/-- Paper: Theorem 3.2.2.1(3), p. 125. If both zero terms vanish, the global
Z-function is entire in the norm-twist coordinate of every component. -/
theorem globalIdelicZFunction_entire_of_vanishing
    (h : f ∈ adelePolarSubspace F) (χ : U[F]) :
    Differentiable ℂ (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)) := by
  obtain ⟨hf, hFourier⟩ := (mem_adelePolarSubspace f).mp h
  rw [← globalThetaMellinIntegral_eq_continuation_of_vanishing f hf hFourier]
  exact globalThetaMellinIntegral_entire_of_vanishing f hf hFourier χ

end HomogeneousMellin

/-- Paper: Lemma 3.2.2.3, p. 125. For fixed quasi-character of abscissa
greater than one, the zeta integral is continuous in the Schwartz–Bruhat topology. -/
theorem continuous_globalIdelicZetaIntegral (c : 𝒳[F]) (hc : c ∈ rightHalf) :
    Continuous (fun f : ℬ[F] ↦ globalIdelicZetaIntegral f c) := by
  classical
  let μ := multiplicativeTamagawaMeasure F
  let : T2Space 𝕀[F] := (ideleGroup_topology F).1
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : SigmaCompactSpace 𝕀[F] := ideleGroup_sigmaCompactSpace
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.1
  let : BarrelledSpace ℂ ℬ[F] := (adeleSchwartz_montel (F := F)).2.1
  let Φ (f : ℬ[F]) (g : 𝕀[F]) := f (Multiplicative.ofAdd g.val) * c (classOf g)
  have hi (f : ℬ[F]) : Integrable (Φ f) μ := globalIdelicZetaIntegral_integrable f c hc
  have hlin (g : 𝕀[F]) : IsLinearMap ℂ (fun f ↦ Φ f g) :=
    ⟨fun f f' ↦ add_mul _ _ _, fun a f ↦ mul_assoc _ _ _⟩
  have hcont (f : ℬ[F]) : Continuous (Φ f) :=
    ((schwartzBruhat_continuous f).comp (continuous_ofAdd.comp Units.continuous_val)).mul
      (c.continuous.comp continuous_quotient_mk')
  let I (K : Set 𝕀[F]) : ℬ[F] →ₗ[ℂ] ℂ :=
    IsLinearMap.mk' (fun f ↦ ∫ g in K, Φ f g ∂μ)
      ⟨fun f f' ↦ (integral_congr_ae (.of_forall fun g ↦ (hlin g).map_add f f')).trans
          (integral_add (hi f).integrableOn (hi f').integrableOn),
        fun a f ↦ (integral_congr_ae (.of_forall fun g ↦ (hlin g).map_smul a f)).trans
          (integral_smul a _)⟩
  -- On a compact subset, Banach–Steinhaus makes the supremum of the
  -- evaluation seminorms continuous; it bounds the truncated integral.
  have hI (K : Set 𝕀[F]) (hK : IsCompact K) : Continuous (I K) := by
    let p (g : K) := (normSeminorm ℂ ℂ).comp (IsLinearMap.mk' _ (hlin g.val))
    have hp (g : K) : Continuous (p g) := by
      change Continuous (fun f : ℬ[F] ↦ ‖f (Multiplicative.ofAdd g.val.val) * c (classOf g.val)‖)
      simp_rw [norm_mul]
      exact (schwartzBruhat_evalNorm_continuous _).mul continuous_const
    have hpt (f : ℬ[F]) : BddAbove (range fun g ↦ p g f) := by
      let : CompactSpace K := isCompact_iff_compactSpace.mp hK
      exact (isCompact_range ((hcont f).norm.comp (continuous_subtype_val (p := (· ∈ K))))).bddAbove
    have hb := Seminorm.bddAbove_range_iff.mpr hpt
    have hs : Continuous (⨆ g, p g : Seminorm ℂ ℬ[F]) :=
      (congrArg Continuous (Seminorm.coe_iSup_eq hb)).mpr (Seminorm.continuous_iSup p hp hb)
    have hM : Continuous ((μ K).toNNReal • ⨆ g, p g : Seminorm ℂ ℬ[F]) := hs.const_smul _
    apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp (I K)
    intro _
    apply Seminorm.continuous_of_le hM
    intro f
    change ‖∫ g in K, Φ f g ∂μ‖ ≤ μ.real K * (⨆ g, p g : Seminorm ℂ ℬ[F]) f
    refine (norm_setIntegral_le_of_norm_le_const (hK.measure_lt_top (μ := μ))
      (C := (⨆ g, p g : Seminorm ℂ ℬ[F]) f) (fun g hg ↦ ?_)).trans_eq (mul_comm _ _)
    rw [Seminorm.coe_iSup_eq hb, iSup_apply]
    exact le_ciSup (hpt f) (⟨g, hg⟩ : K)
  let K := compactCovering 𝕀[F]
  let L (n : ℕ) : ℬ[F] →L[ℂ] ℂ := ⟨I (K n), hI _ (isCompact_compactCovering _ n)⟩
  have hlim : Tendsto (fun n f ↦ L n f) atTop (𝓝 (fun f ↦ globalIdelicZetaIntegral f c)) := by
    apply tendsto_pi_nhds.mpr
    intro f
    have ht := tendsto_setIntegral_of_monotone
      (fun n ↦ (isCompact_compactCovering 𝕀[F] n).measurableSet)
      (fun _ _ h ↦ compactCovering_subset 𝕀[F] h) (hi f).integrableOn
    change Tendsto (fun n ↦ ∫ g in compactCovering 𝕀[F] n, Φ f g ∂μ) atTop (𝓝 (∫ g, Φ f g ∂μ))
    simpa only [iUnion_compactCovering, setIntegral_univ] using ht
  exact (continuousLinearMapOfTendsto L hlim).continuous

-- TODO(paper-gap): In Example 3.2.2.4 the displayed Euler multiplier has the
-- exponent reversed. The Fourier transform of 1_{ℤ₂ˣ} gives the factor 1 - 2^(s-1),
-- which cancels the pole at s = 1 but leaves the pole at s = 0.

end Zeta

end RiemannMasullo
