module

public import RiemannMasullo.Ch09_HardySobolev.Sec2
public import RiemannMasullo.AppC_LCTVS.Sec3b
public import RiemannMasullo.AppC_LCTVS.Sec4
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Separation
import all RiemannMasullo.AppC_LCTVS.Sec3a
import all RiemannMasullo.AppC_LCTVS.Sec3a_part2
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import all RiemannMasullo.Ch09_HardySobolev.Sec1
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Seminorm
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactGroup
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Convex.TotallyBounded
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space.Integral

/-!
# Module structures over test functions and approximate units

Masullo, §9.3, pp. 419–432.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal UniformConvergenceCLM SchwartzMap

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

section RegularizedAction

-- TODO(paper-gap): On I = [0,∞) a log-coordinate bump supported in (−2,−1)
-- has finite intervalSobolevENorm. Its translate by 3 has infinite norm.
-- Full left translation therefore fails on the finite-norm domain of §9.2.

variable [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false in
local notation "logMod" => (fun x ↦ Real.log ((m x).val : ℝ))
local notation "W" => (fun a b s ↦ CompactIntervalSobolev μ logMod a b s)
set_option quotPrecheck false in
local notation "Lβ" E => E →Lᵤ[ℂ, {s : Set E | Bornology.IsVonNBounded ℂ s}] E

/-- The Hardy–Sobolev density on a compact base interval is positive. -/
private theorem intervalSobolevDensity_pos' (a b s t : ℝ) : 0 < intervalSobolevDensity a b s t := by
  unfold intervalSobolevDensity
  exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

/-- The Hardy–Sobolev density on a compact base interval is continuous. -/
private theorem continuous_intervalSobolevDensity (a b s : ℝ) :
    Continuous (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
  positivity

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- The logarithm of the module is continuous. -/
private theorem continuous_logModule' (m : G →ₜ* ℝ≥0ˣ) :
    Continuous (fun x ↦ Real.log ((m x).val : ℝ)) :=
  Real.continuousOn_log.comp_continuous
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous))
    fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'

/-- The compact-interval density of a shifted logarithmic coordinate is at most the square of
the endpoint twist times the polynomial factor of the shift, times the density. -/
private theorem intervalSobolevDensity_add_le (a b s : ℝ) (hs : 0 ≤ s) (L t : ℝ) :
    intervalSobolevDensity a b s (L + t) ≤
      (max (Real.exp (a * L)) (Real.exp (b * L)) * (1 + |L|) ^ (s / 2)) ^ 2 *
        intervalSobolevDensity a b s t := by
  unfold intervalSobolevDensity
  have key : ∀ c : ℝ,
      Real.exp (2 * c * (L + t)) = Real.exp (c * L) ^ 2 * Real.exp (2 * c * t) := fun c ↦ by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hM : ∀ c : ℝ, Real.exp (c * L) ≤ max (Real.exp (a * L)) (Real.exp (b * L)) →
      Real.exp (2 * c * t) ≤ max (Real.exp (2 * a * t)) (Real.exp (2 * b * t)) →
      Real.exp (2 * c * (L + t)) ≤ max (Real.exp (a * L)) (Real.exp (b * L)) ^ 2 *
        max (Real.exp (2 * a * t)) (Real.exp (2 * b * t)) := fun c h1 h2 ↦ by
    rw [key]
    exact mul_le_mul (pow_le_pow_left₀ (Real.exp_pos _).le h1 2) h2 (Real.exp_pos _).le
      (sq_nonneg _)
  have h1 : max (Real.exp (2 * a * (L + t))) (Real.exp (2 * b * (L + t))) ≤
      max (Real.exp (a * L)) (Real.exp (b * L)) ^ 2 *
        max (Real.exp (2 * a * t)) (Real.exp (2 * b * t)) :=
    max_le (hM a (le_max_left _ _) (le_max_left _ _))
      (hM b (le_max_right _ _) (le_max_right _ _))
  have hL0 : 0 ≤ 1 + |L| := by positivity
  have hbase : 1 + (L + t) ^ 2 ≤ (1 + |L|) ^ 2 * (1 + t ^ 2) := by
    rcases le_total 0 L with hL | hL
    · rw [abs_of_nonneg hL]
      nlinarith [mul_nonneg hL (sq_nonneg (t - 1)), mul_nonneg hL (sq_nonneg t),
        sq_nonneg (L * t)]
    · rw [abs_of_nonpos hL]
      nlinarith [mul_nonneg (neg_nonneg.2 hL) (sq_nonneg (t + 1)),
        mul_nonneg (neg_nonneg.2 hL) (sq_nonneg t), sq_nonneg (L * t)]
  have hpow : ((1 + |L|) ^ 2) ^ (s / 2) = ((1 + |L|) ^ (s / 2)) ^ 2 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hL0,
      ← Real.rpow_mul hL0, mul_comm]
  have h2 : (1 + (L + t) ^ 2) ^ (s / 2) ≤
      ((1 + |L|) ^ (s / 2)) ^ 2 * (1 + t ^ 2) ^ (s / 2) :=
    calc (1 + (L + t) ^ 2) ^ (s / 2) ≤ ((1 + |L|) ^ 2 * (1 + t ^ 2)) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith)
      _ = ((1 + |L|) ^ 2) ^ (s / 2) * (1 + t ^ 2) ^ (s / 2) :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = ((1 + |L|) ^ (s / 2)) ^ 2 * (1 + t ^ 2) ^ (s / 2) := by rw [hpow]
  have hmax : 0 ≤ max (Real.exp (a * L)) (Real.exp (b * L)) ^ 2 *
      max (Real.exp (2 * a * t)) (Real.exp (2 * b * t)) :=
    mul_nonneg (sq_nonneg _) (le_max_of_le_left (Real.exp_pos _).le)
  calc max (Real.exp (2 * a * (L + t))) (Real.exp (2 * b * (L + t))) *
        (1 + (L + t) ^ 2) ^ (s / 2)
      ≤ max (Real.exp (a * L)) (Real.exp (b * L)) ^ 2 *
          max (Real.exp (2 * a * t)) (Real.exp (2 * b * t)) *
        (((1 + |L|) ^ (s / 2)) ^ 2 * (1 + t ^ 2) ^ (s / 2)) :=
        mul_le_mul h1 h2 (by positivity) hmax
    _ = _ := by ring

/-- A pointwise bound for the translated density bounds translation in L². -/
private theorem translate_eLpNorm_le {H : Type*} [Group H] [MeasurableSpace H]
    [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] {d : H → ℝ≥0∞}
    (hd : Measurable d) (hd' : ∀ x, d x < ⊤) (g : H) {C : ℝ}
    (hle : ∀ x, d (g * x) ≤ ENNReal.ofReal C ^ 2 * d x)
    (u : H → ℂ) (hu : AEStronglyMeasurable u (ν.withDensity d))
    (ht : AEStronglyMeasurable (fun x ↦ u (g⁻¹ * x)) (ν.withDensity d)) :
    eLpNorm (fun x ↦ u (g⁻¹ * x)) 2 (ν.withDensity d) ≤
      ENNReal.ofReal C * eLpNorm u 2 (ν.withDensity d) := by
  have hI : ∀ v : H → ℂ, ∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d) =
      ∫⁻ x, d x * ‖v x‖ₑ ^ (2 : ℝ) ∂ν := fun v ↦
    lintegral_withDensity_eq_lintegral_mul_non_measurable ν hd (ae_of_all _ hd') _
  have hmain : ∫⁻ x, ‖u (g⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d) ≤
      ENNReal.ofReal C ^ 2 * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d) :=
    calc ∫⁻ x, ‖u (g⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d)
        = ∫⁻ x, d x * ‖u (g⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂ν := hI fun x ↦ u (g⁻¹ * x)
      _ = ∫⁻ x, d (g * x) * ‖u (g⁻¹ * (g * x))‖ₑ ^ (2 : ℝ) ∂ν :=
          (lintegral_mul_left_eq_self (fun x ↦ d x * ‖u (g⁻¹ * x)‖ₑ ^ (2 : ℝ)) g).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal C ^ 2 * (d x * ‖u x‖ₑ ^ (2 : ℝ)) ∂ν :=
          lintegral_mono fun x ↦ by
            show d (g * x) * ‖u (g⁻¹ * (g * x))‖ₑ ^ (2 : ℝ) ≤
              ENNReal.ofReal C ^ 2 * (d x * ‖u x‖ₑ ^ (2 : ℝ))
            rw [inv_mul_cancel_left, ← mul_assoc]
            exact mul_le_mul' (hle x) le_rfl
      _ = ENNReal.ofReal C ^ 2 * ∫⁻ x, d x * ‖u x‖ₑ ^ (2 : ℝ) ∂ν :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      _ = ENNReal.ofReal C ^ 2 * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d) := by rw [hI u]
  have h2 : ((2 : ℕ) : ℝ) * (1 / 2) = 1 := by norm_num
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top ht,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hu,
    ENNReal.toReal_ofNat]
  calc (∫⁻ x, ‖u (g⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d)) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal C ^ 2 *
          ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hmain hhalf
    _ = ENNReal.ofReal C *
          (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d)) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf, ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul, h2, ENNReal.rpow_one]

/-- On a compactly supported continuous representative, translation is continuous
in L² for any locally finite measure. Near a fixed translate a single compact
set contains all the translated supports. -/
private theorem continuous_translate_compact_L2 (ν : Measure G) [IsLocallyFiniteMeasure ν]
    (f : G → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (v : G → Lp ℂ 2 ν) (hv : ∀ g, (v g : G → ℂ) =ᵐ[ν] fun x ↦ f (g⁻¹ * x)) :
    Continuous v := by
  classical
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨K, hK, hK₀⟩ := exists_compact_mem_nhds g₀
  let S := (fun p : G × G ↦ p.1 * p.2) '' (K ×ˢ tsupport f)
  have hS : IsCompact S := (hK.prod hc).image (by fun_prop)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hf.continuousOn
  have hbound (y : G) : ‖f y‖ ≤ max M 0 := by
    by_cases hy : f y = 0
    · simp [hy]
    · exact (hM y (subset_tsupport _ hy)).trans (le_max_left _ _)
  have hout {g x : G} (hg : g ∈ K) (hx : x ∉ S) : f (g⁻¹ * x) = 0 := by
    by_contra hn
    exact hx ⟨(g, g⁻¹ * x), ⟨hg, subset_tsupport _ hn⟩, mul_inv_cancel_left _ _⟩
  let D (g x : G) := ‖f (g⁻¹ * x) - f (g₀⁻¹ * x)‖ ^ 2
  have hint : Tendsto (fun g ↦ ∫ x, D g x ∂ν) (𝓝 g₀) (𝓝 (∫ _ : G, (0 : ℝ) ∂ν)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (S.indicator (fun _ ↦ (2 * max M 0) ^ 2))
    · exact .of_forall fun g ↦ (show Continuous (D g) by dsimp [D]; fun_prop).aestronglyMeasurable
    · filter_upwards [hK₀] with g hg
      refine .of_forall fun x ↦ ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        exact (norm_sub_le _ _).trans (by linarith [hbound (g⁻¹ * x), hbound (g₀⁻¹ * x)])
      · simp [indicator_of_notMem hx, hout hg hx, hout (mem_of_mem_nhds hK₀) hx]
    · exact (integrableOn_const hS.measure_lt_top.ne).integrable_indicator hS.measurableSet
    · refine .of_forall fun x ↦ ?_
      have hcont : Continuous (fun g ↦ D g x) := by dsimp [D]; fun_prop
      simpa [D] using hcont.tendsto g₀
  have hsq (g : G) : ‖v g - v g₀‖ ^ 2 = ∫ x, D g x ∂ν := by
    rw [← L2.integral_sq_norm (𝕜 := ℂ)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (v g) (v g₀), hv g, hv g₀] with x h hg h₀
    simp only [h, Pi.sub_apply, hg, h₀, D]
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simpa only [integral_zero, comp_def, ← hsq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero]
    using (Real.continuous_sqrt.tendsto _).comp hint

/-- A continuous positive density whose translates obey a locally uniform bound
gives a strongly continuous left regular representation on weighted L². -/
private theorem exists_translate_weighted_L2 (w C : G → ℝ) (hw : Continuous w)
    (hwpos : ∀ x, 0 < w x) (hC : Continuous C) (hCpos : ∀ g, 0 ≤ C g)
    (hshift : ∀ g x, w (g * x) ≤ C g ^ 2 * w x) :
    let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (w x))
    ∃ T : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν),
      (∀ g u, (T g u : G → ℂ) =ᵐ[μ] fun x ↦ u (g⁻¹ * x)) ∧
      Continuous (fun p : G × Lp ℂ 2 ν ↦ T p.1 p.2) := by
  classical
  intro ν
  have hνμ : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hμν : μ ≪ ν := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hwpos x)).ne')
  have : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  let S (g : G) (u : Lp ℂ 2 ν) (x : G) := u (g⁻¹ * x)
  have hS (g : G) (u : Lp ℂ 2 ν) : AEStronglyMeasurable (S g u) ν :=
    ((Lp.stronglyMeasurable u).comp_measurable (measurable_const.mul measurable_id)).aestronglyMeasurable
  have hbound (g : G) (u : Lp ℂ 2 ν) :
      eLpNorm (S g u) 2 ν ≤ ENNReal.ofReal (C g) * eLpNorm u 2 ν := by
    apply translate_eLpNorm_le μ hw.measurable.ennreal_ofReal (fun _ ↦ ENNReal.ofReal_lt_top)
      g _ _ (Lp.aestronglyMeasurable u) (hS g u)
    intro x
    rw [← ENNReal.ofReal_pow (hCpos g), ← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hshift g x)
  have hmem (g : G) (u : Lp ℂ 2 ν) : MemLp (S g u) 2 ν :=
    (hbound g u).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp u))
  let U (g : G) (u : Lp ℂ 2 ν) := (hmem g u).toLp (S g u)
  have hU (g : G) (u : Lp ℂ 2 ν) : (U g u : G → ℂ) =ᵐ[μ] S g u :=
    hμν.ae_eq (hmem g u).coeFn_toLp
  let L (g : G) : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := U g
      map_add' := fun u v ↦ by
        apply Lp.ext
        apply hνμ.ae_eq
        filter_upwards [hU g (u + v), hU g u, hU g v, hμν.ae_eq (Lp.coeFn_add (U g u) (U g v)),
          (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp
            (hμν.ae_eq (Lp.coeFn_add u v))] with x h h₁ h₂ h₃ h₄
        exact h.trans (h₄.trans (by simpa [Pi.add_apply, h₁, h₂] using h₃.symm))
      map_smul' := fun c u ↦ by
        apply Lp.ext
        apply hνμ.ae_eq
        filter_upwards [hU g (c • u), hU g u, hμν.ae_eq (Lp.coeFn_smul c (U g u)),
          (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp
            (hμν.ae_eq (Lp.coeFn_smul c u))] with x h h₁ h₂ h₃
        exact h.trans (h₃.trans (by simpa [Pi.smul_apply, h₁] using h₂.symm)) }
  have hnorm (g : G) (u : Lp ℂ 2 ν) : ‖L g u‖ ≤ C g * ‖u‖ := by
    change ‖(hmem g u).toLp _‖ ≤ _
    rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_ofReal (hCpos g), ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u))
      (hbound g u)
  let T (g : G) := (L g).mkContinuous (C g) (hnorm g)
  let ρ : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :=
    { toFun := T
      map_one' := by
        ext u
        apply hνμ.ae_eq
        filter_upwards [hU 1 u] with x h
        simpa [T, L, S] using h
      map_mul' := fun g k ↦ by
        ext u
        apply hνμ.ae_eq
        filter_upwards [hU (g * k) u, hU g (T k u),
          (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp (hU k u)]
          with x h h₁ h₂
        change U (g * k) u x = U g (T k u) x
        rw [h, h₁]
        exact (by simpa [S, T, L, Function.comp_def, mul_assoc] using h₂.symm) }
  refine ⟨ρ, hU, ?_⟩
  let D := {u : Lp ℂ 2 ν | ∃ f : G → ℂ, Continuous f ∧ HasCompactSupport f ∧ (u : G → ℂ) =ᵐ[ν] f}
  have hdense : Dense D := by
    intro u
    apply EMetric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    obtain ⟨f, hc, he, hf, hm⟩ := (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le (by simp) hδ.ne'
    refine ⟨hm.toLp f, ⟨f, hf, hc, hm.coeFn_toLp⟩, ?_⟩
    rw [Lp.edist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub hm.coeFn_toLp)]
    exact he.trans_lt hδε
  have horbit (u : Lp ℂ 2 ν) (hu : u ∈ D) : Continuous (fun g ↦ ρ g u) := by
    obtain ⟨f, hf, hc, hu⟩ := hu
    apply continuous_translate_compact_L2 ν f hf hc
    intro g
    exact hνμ.ae_eq ((hU g u).trans ((measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp
      (hμν.ae_eq hu)))
  rw [continuous_iff_continuousAt]
  intro p
  let K : ℝ≥0 := ⟨C p.1 + 1, by linarith [hCpos p.1]⟩
  let V := {g : G | C g < K}
  have hV : IsOpen V := isOpen_lt hC continuous_const
  have hp : p ∈ V ×ˢ (univ : Set (Lp ℂ 2 ν)) := ⟨by change C p.1 < C p.1 + 1; linarith, trivial⟩
  apply ContinuousOn.continuousAt _ ((hV.prod isOpen_univ).mem_nhds hp)
  apply continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith' _
    (subset_univ D) (fun u _ ↦ hdense u) K
  · intro g hg
    apply LipschitzWith.lipschitzOnWith
    apply (T g).lipschitzWith.weaken
    exact_mod_cast ((T g).opNorm_le_bound (hCpos g) (hnorm g)).trans hg.le
  · exact fun u hu ↦ (horbit u hu).continuousOn

/-- Paper: Definition 9.3.1.1, p. 419. Left translation acts jointly continuously
on the compact-interval Hardy–Sobolev Hilbert space, with the translated function
as its almost-everywhere representative.
Deviation: This records the regular representation used in the definition, in the
weighted L² model of §9.2. -/
theorem exists_hardySobolevTranslation (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) :
    ∃ ρ : G →* (W a b s →L[ℂ] W a b s),
      (∀ g u, (ρ g u : G → ℂ) =ᵐ[μ] fun x ↦ u (g⁻¹ * x)) ∧
      Continuous (fun p : G × W a b s ↦ ρ p.1 p.2) := by
  let w (x : G) := intervalSobolevDensity a b s (logMod x)
  let C (g : G) := max (Real.exp (a * logMod g)) (Real.exp (b * logMod g)) *
    (1 + |logMod g|) ^ (s / 2)
  have hlog := continuous_logModule' m
  have hw : Continuous w := (continuous_intervalSobolevDensity a b s).comp hlog
  have hC : Continuous C := by
    refine Continuous.mul ((Real.continuous_exp.comp (continuous_const.mul hlog)).max
      (Real.continuous_exp.comp (continuous_const.mul hlog))) ?_
    exact (continuous_const.add hlog.abs).rpow_const fun g ↦ Or.inl (ne_of_gt (by positivity : 0 < 1 + |logMod g|))
  apply exists_translate_weighted_L2 μ w C hw (fun _ ↦ intervalSobolevDensity_pos' ..) hC
    (fun _ ↦ mul_nonneg (le_max_of_le_left (Real.exp_pos _).le) (Real.rpow_nonneg (by positivity) _))
  intro g x
  have hlogmul : logMod (g * x) = logMod g + logMod x := by
    dsimp only
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (m g).ne_zero) (NNReal.coe_ne_zero.2 (m x).ne_zero)]
  simpa only [w, C, hlogmul] using intervalSobolevDensity_add_le a b s _hs (logMod g) (logMod x)

/-- Paper: Definition 9.3.1.1, p. 419. Choose the regular representation characterized
by the left-translation formula. -/
def hardySobolevTranslation (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    G →* (W a b s →L[ℂ] W a b s) :=
  (exists_hardySobolevTranslation μ m a b s hab hs).choose

/-- Paper: Definition 9.3.1.1, p. 419. The action has the left-translation formula
on representatives almost everywhere. -/
theorem hardySobolevTranslation_apply (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (g : G) (u : W a b s) :
    (hardySobolevTranslation μ m a b s hab hs g u : G → ℂ) =ᵐ[μ]
      fun x ↦ u (g⁻¹ * x) :=
  (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.1 g u

/-- Continuity of a Bruhat-smooth function follows already from order zero.
Around each point its restriction factors through an elementary quotient. -/
theorem continuous_of_bruhatSmooth {f : G → ℂ} (hf : IsBruhatSmooth f) : Continuous f := by
  classical
  obtain ⟨k, hk, _, hdesc⟩ := hf 0
  have hkc := hk.isCompact
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hU₁⟩ := exists_compact_mem_nhds (1 : G)
  let K := insert x (U ∪ (k : Set G))
  let H := Subgroup.closure K
  have hK : K ⊆ (H : Set G) := Subgroup.subset_closure
  have hK₁ : K ∈ 𝓝 (1 : G) := mem_of_superset hU₁ (subset_union_left.trans (subset_insert ..))
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds (mem_of_superset hK₁ hK)
  let a : BruhatStructuralPair G :=
    ⟨(H, OrderDual.toDual k), hH,
      ⟨Subtype.val ⁻¹' K, continuous_subtype_val.continuousAt.preimage_mem_nhds hK₁,
        (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage
          ((hU.union hkc).insert x), Subgroup.closure_preimage_eq_top K⟩,
      hk, subset_union_right.trans ((subset_insert ..).trans hK)⟩
  let e := Classical.choice a.elementary
  obtain ⟨f₀, hval, hsm⟩ := hdesc a rfl
  let q : EuclideanSpace ℝ (Fin e.torusDim) → (Fin e.torusDim → AddCircle (1 : ℝ)) :=
    fun t i ↦ (t i : AddCircle (1 : ℝ))
  have hq : IsOpenQuotientMap q :=
    (IsOpenQuotientMap.piMap (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin e.torusDim ↦ ℝ)).toHomeomorph.isOpenQuotientMap
  have hmodel : Continuous (fun y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor ↦
      f₀ (e.equiv.symm (Multiplicative.ofAdd y))) := by
    rw [← (Homeomorph.prodAssoc _ _ _).isOpenQuotientMap.continuous_comp_iff]
    refine continuous_prod_of_discrete_right.mpr fun zd ↦ ?_
    rw [← ((IsOpenQuotientMap.id (X := EuclideanSpace ℝ (Fin e.realDim))).prodMap hq).continuous_comp_iff]
    exact (hsm e zd.1 zd.2).continuous
  have hf₀ : Continuous f₀ := by
    simpa only [Function.comp_def, ofAdd_toAdd, ContinuousMulEquiv.symm_apply_apply]
      using hmodel.comp (show Continuous (fun z : a.quotient ↦ (e.equiv z).toAdd) from e.equiv.continuous)
  have hcont : Continuous (fun z : H ↦ f (z : G)) :=
    (hf₀.comp (QuotientGroup.continuous_mk (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))).congr hval
  exact hH.isOpenEmbedding_subtypeVal.continuousAt_iff.mp (hcont.continuousAt (x := ⟨x, hK (mem_insert ..)⟩))

/-- Testing a positive Pettis integral by a continuous functional gives the
ordinary scalar integral. -/
private theorem eval_pettis_positive {V : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] {f : G → V} {v : V}
    (h : HasPettisIntegral (.positive μ) f v) (δ : StrongDual ℂ V) :
    δ v = ∫ g, δ (f g) ∂μ :=
  congrArg (fun z : PettisWeakCompletion V ↦ (show Module.Dual ℂ (StrongDual ℂ V) from z) δ) h.2

section Pettis

-- TODO(paper-gap): Norm-continuous functionals on the bounded operators need
-- not be measurable on translations. The Pettis formula below tests each orbit
-- in the representation space, as in Lemma C.4.3.11.

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
variable (ρ : G →* (E →L[ℂ] E))

open scoped Pointwise in
/-- Compact support reduces the positive Haar integral to a finite measure.
The closed convex hull of a compact orbit is compact by completeness. -/
private theorem exists_test_kernel_operator [CompleteSpace E]
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (φ : BruhatCompactSupport G) :
    ∃ T : E →L[ℂ] E, ∀ u, HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • ρ g u) (T u) := by
  classical
  have : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  have : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  let K := tsupport φ.val
  have hK : IsCompact K := φ.property.2
  let ν := μ.restrict K
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hK.measure_lt_top⟩
  have hφ : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 φ.property.1)
  let v (g : G) (u : E) := φ.val g • ρ g u
  have hv : Continuous (fun z : G × E ↦ v z.1 z.2) := (hφ.comp continuous_fst).smul hρ
  have horbit (u : E) : Continuous (v · u) := hv.comp (Continuous.prodMk_left u)
  have hsupp (u : E) : HasCompactSupport (v · u) := hK.of_isClosed_subset isClosed_closure
    (closure_minimal (fun g hg ↦ subset_tsupport _ (fun h ↦ hg (by simp [v, h]))) isClosed_closure)
  have hi (u : E) (δ : StrongDual ℂ E) : Integrable (fun g ↦ δ (v g u)) μ :=
    (δ.continuous.comp (horbit u)).integrable_of_hasCompactSupport ((hsupp u).comp_left δ.map_zero)
  let C (u : E) := closure (convexHull ℝ (insert 0 ((v · u) '' K)))
  have hP (u : E) : ∃ y ∈ ν.real univ • C u, HasPettisIntegral (.positive μ) (v · u) y := by
    have hc := (hK.image (horbit u)).insert (0 : E)
    obtain ⟨y, hy, _, he⟩ := exists_hasPettisIntegral_mem_smul_of_isCompact_convex ν
      (f := (v · u)) (fun δ ↦ (hi u δ).integrableOn)
      (hc.totallyBounded.convexHull.closure.isCompact_of_isClosed isClosed_closure)
      (convex_convexHull ..).closure (subset_closure (subset_convexHull _ _ (mem_insert ..)))
      ((ae_restrict_mem hK.measurableSet).mono fun g hg ↦
        subset_closure (subset_convexHull _ _ (mem_insert_of_mem _ ⟨g, hg, rfl⟩)))
    refine ⟨y, hy, hi u, LinearMap.ext fun δ ↦ ?_⟩
    change δ y = ∫ g, δ (v g u) ∂μ
    exact (LinearMap.congr_fun he δ).trans (setIntegral_eq_integral_of_forall_compl_eq_zero
      fun g hg ↦ by simp [v, image_eq_zero_of_notMem_tsupport (f := φ.val) hg])
  choose P hbound hP using hP
  let L : E →ₗ[ℂ] E :=
    { toFun := P
      map_add' := fun u w ↦ by
        apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
        intro δ
        rw [map_add, eval_pettis_positive μ (hP (u + w)), eval_pettis_positive μ (hP u),
          eval_pettis_positive μ (hP w), ← integral_add (hi u δ) (hi w δ)]
        simp only [v, map_add, smul_add]
      map_smul' := fun c u ↦ by
        apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
        intro δ
        rw [RingHom.id_apply, map_smul, eval_pettis_positive μ (hP (c • u)),
          eval_pettis_positive μ (hP u), ← integral_smul]
        simp only [v, map_smul, smul_comm (φ.val _) c] }
  refine ⟨⟨L, ?_⟩, hP⟩
  apply continuous_of_tendsto_nhds_zero L
  apply (nhds_hasBasis_absConvex_closed ℝ E).tendsto_right_iff.2
  intro V hV
  let d := ν.real univ
  obtain ⟨U, N, _, hopen, hU, hW, hprod⟩ := generalized_tube_lemma hK
    (isCompact_singleton (x := (0 : E))) (isOpen_interior.preimage (hv.const_smul d)) (by
      rintro ⟨g, u⟩ ⟨_, hu : u = 0⟩
      simpa [v, hu] using mem_interior_iff_mem_nhds.mpr hV.1)
  filter_upwards [hopen.mem_nhds (hW (mem_singleton _))] with u hu
  obtain ⟨y, hy, he⟩ := hbound u
  change P u ∈ V
  rw [← he]
  apply (closure_minimal (t := (fun z : E ↦ d • z) ⁻¹' V) _
    (hV.2.1.preimage (continuous_const_smul d))) hy
  apply convexHull_min _ (hV.2.2.2.smul_preimage d)
  rintro _ (rfl | ⟨g, hg, rfl⟩)
  · simpa using mem_of_mem_nhds hV.1
  · exact interior_subset (s := V) (hprod (show (g, u) ∈ U ×ˢ N from ⟨hU hg, hu⟩))

/-- Paper: Remark 9.3.1.2, p. 419. Integrating a test function against continuous
left translation gives a continuous endomorphism and is linear in the test function.
Deviation: The operator integral is taken on each vector, as in (9.3.2.2) and §C.4.3.
The complete representation space is a parameter. -/
theorem exists_bruhatRegularizedAction [CompleteSpace E]
    (_hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    ∃ A : BruhatCompactSupport G →ₗ[ℂ] Lβ E,
      ∀ φ u, HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • ρ g u) (A φ u) := by
  have : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  choose T hT using exists_test_kernel_operator μ ρ _hρ
  refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_ }, hT⟩
  · intro φ ψ
    ext u
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro δ
    change δ (T (φ + ψ) u) = δ (T φ u + T ψ u)
    calc
      _ = ∫ g, δ ((φ + ψ).val g • ρ g u) ∂μ := eval_pettis_positive μ (hT (φ + ψ) u) δ
      _ = ∫ g, (δ (φ.val g • ρ g u) + δ (ψ.val g • ρ g u)) ∂μ :=
        integral_congr_ae (.of_forall fun g ↦ by change δ ((φ.val g + ψ.val g) • ρ g u) = _; rw [add_smul, map_add])
      _ = _ := (integral_add ((hT φ u).1 δ) ((hT ψ u).1 δ)).trans
        ((congrArg₂ (· + ·) (eval_pettis_positive μ (hT φ u) δ).symm
          (eval_pettis_positive μ (hT ψ u) δ).symm).trans (δ.map_add _ _).symm)
  · intro c φ
    ext u
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro δ
    change δ (T (c • φ) u) = δ (c • T φ u)
    calc
      _ = ∫ g, δ ((c • φ).val g • ρ g u) ∂μ := eval_pettis_positive μ (hT (c • φ) u) δ
      _ = ∫ g, c • δ (φ.val g • ρ g u) ∂μ :=
        integral_congr_ae (.of_forall fun g ↦ by change δ ((c * φ.val g) • ρ g u) = _; rw [mul_smul, map_smul])
      _ = _ := (integral_smul c _).trans ((congrArg (c • ·)
        (eval_pettis_positive μ (hT φ u) δ).symm).trans (δ.map_smul c _).symm)

/-- Paper: Definition 9.3.1.1, p. 419. A test function acts by integrating
its scalar multiples of left translations against Haar measure.
Deviation: The Pettis integral is specified on each input vector. Instantiate the
representation with the action on the decay space or the Hardy–Sobolev space.

Deviation: Equation (9.3.1.2) specifies an operator-valued Pettis integral in $\mathcal
L_\beta(E)$, which may fail to exist. We construct the operator by taking a Pettis integral in
$E$ for each input vector.
-/
def bruhatRegularizedAction [CompleteSpace E]
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    BruhatCompactSupport G →ₗ[ℂ] Lβ E :=
  (exists_bruhatRegularizedAction μ ρ hρ).choose

/-- Paper: Definition 9.3.1.1, p. 419. The action on each vector represents
the Pettis integral of the test function times its orbit.

Deviation: The Pettis identity in Definition 9.3.1.1 can fail against a continuous functional on
the full operator space. We state the Pettis identity in $E$ for each vector.
-/
theorem bruhatRegularizedAction_apply [CompleteSpace E]
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (φ : BruhatCompactSupport G) (u : E) :
    HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • ρ g u)
      (bruhatRegularizedAction μ ρ hρ φ u) :=
  (exists_bruhatRegularizedAction μ ρ hρ).choose_spec φ u

/-- A finite weighted average of translates of a Cᵖ function is Cᵖ when the
translations and coefficients range over a compact parameter set. -/
private theorem contDiff_translate_average {V Y : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    {p : ℕ∞} {f : V → ℂ} (hf : ContDiff ℝ p f)
    (q : Y → V) (c : Y → ℂ) (hq : Measurable q) (hc : Measurable c)
    {K : Set (V × ℂ)} (hK : IsCompact K) (hqc : ∀ y, (q y, c y) ∈ K) :
    (∀ u, Integrable (fun y ↦ c y * f (q y + u)) ν) ∧
      ContDiff ℝ p (fun u ↦ ∫ y, c y * f (q y + u) ∂ν) := by
  let k (y : Y) := (q y, c y)
  let η := ν.map k
  have hm : Measurable k := hq.prodMk hc
  let F (u : V) (z : V × ℂ) := z.2 * f (z.1 + u)
  have hF : ContDiff ℝ p F.uncurry :=
    contDiff_snd.snd.mul (hf.comp (contDiff_snd.fst.add contDiff_fst))
  have hmem : ∀ᵐ z ∂η, z ∈ K := (ae_map_iff hm.aemeasurable hK.measurableSet).mpr (.of_forall hqc)
  have hKU : K =ᵐ[η] (univ : Set (V × ℂ)) := ae_eq_univ.mpr hmem
  have hcont (u) : Continuous (F u) :=
    continuous_snd.mul (hf.continuous.comp (continuous_fst.add continuous_const))
  have hset (u) : (∫ z in K, F u z ∂η) = ∫ y, c y * f (q y + u) ∂ν := by
    rw [setIntegral_congr_set hKU, setIntegral_univ, integral_map hm.aemeasurable
      (hcont u).aestronglyMeasurable]
  refine ⟨fun u ↦ ?_, ?_⟩
  · apply (integrable_map_measure (hcont u).aestronglyMeasurable hm.aemeasurable).mp
    have hi := (hcont u).continuousOn.integrableOn_compact (μ := η) hK
    exact integrableOn_univ.mp (hi.congr_set_ae hKU.symm)
  · simpa only [← hset] using hF.parametric_integral (μ := η) hK (Subset.rfl) (measure_ne_top η K)

/-- On an elementary group, lift the torus parameter to a bounded fundamental
cube and sum over the finitely many discrete fibers in the averaging set. -/
private theorem elementary_average_contDiff {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    {m n r : ℕ} {D : Type*} [AddCommGroup D] [TopologicalSpace D] [DiscreteTopology D]
    (v : Y → ElementaryLieGroup m n r D) (hv : Continuous v)
    (c : Y → ℂ) (hc : Continuous c) {p : ℕ∞} (f : ElementaryLieGroup m n r D → ℂ)
    (hf : ∀ z d, ContDiff ℝ p (fun u ↦ f (elementaryCover u z d))) (z : Fin r → ℤ) (d : D) :
    ContDiff ℝ p (fun u ↦ ∫ y, c y * f (v y + elementaryCover u z d) ∂ν) := by
  classical
  let V := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let t (y : Y) (i : Fin n) := ((AddCircle.measurableEquivIco (1 : ℝ) 0 ((v y).2.1 i)).val)
  let q (y : Y) : V := ((v y).1, WithLp.toLp 2 (t y))
  have hq : Measurable q := hv.fst.measurable.prodMk <| (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_iff.mpr fun i ↦ measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp
        (((continuous_apply i).comp hv.snd.fst).measurable)))
  let j (y : Y) := (v y).2.2
  have hj : Continuous j := hv.snd.snd
  let J := (isCompact_range hj).finite_of_discrete.toFinset
  let box : Set (Fin n → ℝ) := univ.pi (fun _ ↦ Icc 0 1)
  have hbox : IsCompact box := isCompact_univ_pi fun _ ↦ isCompact_Icc
  let K := (range (fun y ↦ (v y).1)) ×ˢ ((WithLp.toLp 2) '' box)
  have hK : IsCompact K := (isCompact_range hv.fst).prod (hbox.image (PiLp.continuous_toLp 2 _))
  have hqK (y) : q y ∈ K := by
    refine ⟨⟨y, rfl⟩, ⟨t y, fun i _ ↦ ?_, rfl⟩⟩
    have hi := (AddCircle.measurableEquivIco (1 : ℝ) 0 ((v y).2.1 i)).property
    exact ⟨hi.1, by simpa using hi.2.le⟩
  let a (i : (Fin r → ℤ) × D) (y) := if j y = i then c y else 0
  have ha (i) : Continuous (a i) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hloc : ∀ᶠ x in 𝓝 y, j x = j y := hj.continuousAt
      ((isOpen_discrete ({j y} : Set ((Fin r → ℤ) × D))).mem_nhds rfl)
    by_cases h : j y = i
    · apply hc.continuousAt.congr_of_eventuallyEq
      exact hloc.mono fun x hx ↦ ite_eq_left (hx.trans h)
    · apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      exact hloc.mono fun x hx ↦ ite_eq_right (hx ▸ h)
  let g (i : (Fin r → ℤ) × D) (u : V) := f (elementaryCover u (i.1 + z) (i.2 + d))
  have hpiece (i) := contDiff_translate_average ν (hf (i.1 + z) (i.2 + d)) q (a i) hq
    (ha i).measurable (hK.prod (isCompact_range (ha i))) (fun y ↦ ⟨hqK y, y, rfl⟩)
  have eq (u : V) (y : Y) : c y * f (v y + elementaryCover u z d) =
      ∑ i ∈ J, a i y * g i (q y + u) := by
    have hy : j y ∈ J := by simpa only [J, Set.Finite.mem_toFinset] using (mem_range_self y : j y ∈ range j)
    rw [Finset.sum_eq_single_of_mem (j y) hy (fun i _ hi ↦ by simp [a, hi.symm])]
    simp only [a, ite_true, g]
    apply congrArg (c y * ·) (congrArg f ?_)
    refine Prod.ext rfl (Prod.ext (funext fun i ↦ ?_) rfl)
    change (v y).2.1 i + (u.2 i : AddCircle (1 : ℝ)) = ((t y i + u.2 i : ℝ) : AddCircle (1 : ℝ))
    rw [AddCircle.coe_add]
    exact congrArg (· + (u.2 i : AddCircle (1 : ℝ))) AddCircle.coe_equivIco.symm
  have hsum (u : V) : (∫ y, c y * f (v y + elementaryCover u z d) ∂ν) =
      ∑ i ∈ J, ∫ y, a i y * g i (q y + u) ∂ν := by
    simp_rw [eq]
    exact integral_finsetSum _ fun i _ ↦ (hpiece i).1 u
  simpa only [hsum] using (ContDiff.sum (s := J) fun i _ ↦ (hpiece i).2)

/-- Convolution with a continuous compactly supported kernel preserves each
finite order of Bruhat differentiability. All translations in its support
can be computed inside one larger compactly generated open subgroup. -/
private theorem bruhatContDiff_convolution {p : ℕ} {f g : G → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hg : IsBruhatContDiff p g) :
    IsBruhatContDiff p (lcaConvolution μ f g) := by
  classical
  obtain ⟨k, hk, hinv, hdesc⟩ := hg
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · apply integral_congr_ae
    exact .of_forall fun t ↦ by
      change f t * g (t⁻¹ * (h.val * x)) = _
      rw [mul_left_comm, hinv]
  let K := tsupport f
  let σ := μ.comap (Subtype.val : K → G)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hfc
  let : IsFiniteMeasure σ := ⟨by
    change (μ.comap (Subtype.val : K → G)) univ < (⊤ : ℝ≥0∞)
    rw [(MeasurableEmbedding.subtype_coe hfc.measurableSet).comap_apply, image_univ, Subtype.range_coe]
    exact hfc.measure_lt_top⟩
  obtain ⟨J, hJ⟩ := exists_openCompactlyGeneratedSubgroup_contains hfc
  obtain ⟨H, haH, hJH⟩ := (openCompactlyGeneratedSubgroups_colimit (G := G)).1.directed
    ⟨a.val.1, a.property.1, a.property.2.1⟩ J
  have hkA : k ≤ a.val.1 := ha ▸ a.property.2.2.2
  let b : BruhatStructuralPair G :=
    ⟨(H.val, OrderDual.toDual k), H.property.1, H.property.2, hk, hkA.trans haH⟩
  let i := Subgroup.inclusion (show a.val.1 ≤ H.val from haH)
  let j : a.quotient →* b.quotient := QuotientGroup.map _ _ i (by
    intro x hx
    change (x : G) ∈ OrderDual.ofDual a.val.2 at hx
    change (x : G) ∈ k
    rwa [ha] at hx)
  have hι : Continuous i := (continuous_subtype_val : Continuous ((↑) : a.val.1 → G)).subtype_mk _
  have hj : Continuous j := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hι)
  let t (y : K) : b.val.1 := ⟨y, hJH (hJ y.property)⟩
  let q (y : K) := (QuotientGroup.mk (t y) : b.quotient)⁻¹
  have ht : Continuous t := continuous_subtype_val.subtype_mk _
  have hq : Continuous q := (QuotientGroup.continuous_mk.comp ht).inv
  obtain ⟨g₀, hg₀, hgS⟩ := hdesc b rfl
  let F (z : b.quotient) := ∫ y : K, f y * g₀ (q y * z) ∂σ
  refine ⟨F ∘ j, fun x ↦ ?_, fun e z d ↦ ?_⟩
  · have heq (y : K) : g₀ (q y * j (QuotientGroup.mk x)) = g (y.val⁻¹ * x.val) :=
      hg₀ ((t y)⁻¹ * i x)
    change (∫ y : K, f y * g₀ (q y * j (QuotientGroup.mk x)) ∂σ) = _
    simp_rw [heq]
    rw [integral_subtype_comap hfc.measurableSet (fun y ↦ f y * g (y⁻¹ * x.val))]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
      by simp [image_eq_zero_of_notMem_tsupport hy]
  · obtain ⟨e'⟩ := b.elementary
    let L := AddMonoidHom.toMultiplicative.symm
      (e'.equiv.toMulEquiv.toMonoidHom.comp (j.comp e.equiv.symm.toMulEquiv.toMonoidHom))
    have hL : Continuous L := e'.equiv.continuous.comp (hj.comp e.equiv.symm.continuous)
    let v (y : K) := (e'.equiv (q y)).toAdd
    let P := fun x ↦ g₀ (e'.equiv.symm (Multiplicative.ofAdd x))
    have hsm (z' d') := elementary_average_contDiff σ v (e'.equiv.continuous.comp hq)
      (fun y : K ↦ f y) (hf.comp continuous_subtype_val) P (hgS e') z' d'
    have h' : ∀ z' d', ContDiff ℝ (p : ℕ∞) (fun u ↦ F (e'.equiv.symm
        (Multiplicative.ofAdd (elementaryCover u z' d')))) := by
      intro z' d'
      convert hsm z' d' using 1
      funext u
      apply integral_congr_ae
      refine .of_forall fun y ↦ congrArg (f y * ·) (congrArg g₀ ?_)
      change q y * e'.equiv.symm _ = e'.equiv.symm (e'.equiv (q y) * _)
      exact ((congrArg (· * e'.equiv.symm (Multiplicative.ofAdd (elementaryCover u z' d')))
        (e'.equiv.symm_apply_apply (q y))).symm).trans
        (e'.equiv.symm.map_mul _ (Multiplicative.ofAdd (elementaryCover u z' d'))).symm
    let Q (w) := F (e'.equiv.symm (Multiplicative.ofAdd w))
    have hcomp := contDiff_comp_elementaryHom L hL (f := Q) h' z d
    have hEq (u) : Q (L (elementaryCover u z d)) =
        F (j (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d)))) :=
      congrArg F (e'.equiv.symm_apply_apply _)
    exact Eq.subst (motive := fun h ↦ ContDiff ℝ (p : ℕ∞) h) (funext hEq) hcomp

/-- Haar invariance and Fubini give the convolution pairing, even against
an unbounded continuous coefficient, since both kernels have compact support. -/
private theorem test_convolution_pairing {f g : G → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    HasCompactSupport (lcaConvolution μ f g) ∧ ∀ (D : G → ℂ), Continuous D →
      (∫ x, lcaConvolution μ f g x * D x ∂μ) = ∫ t, f t * (∫ y, g y * D (t * y) ∂μ) ∂μ := by
  let S := (fun p : G × G ↦ p.1 * p.2) '' (tsupport f ×ˢ tsupport g)
  have hS : IsCompact S := (hfc.prod hgc).image (by fun_prop)
  have hs {t x : G} (h : f t * g (t⁻¹ * x) ≠ 0) : t ∈ tsupport f ∧ x ∈ S :=
    ⟨subset_tsupport _ (left_ne_zero_of_mul h), ⟨(t, t⁻¹ * x),
      ⟨subset_tsupport _ (left_ne_zero_of_mul h), subset_tsupport _ (right_ne_zero_of_mul h)⟩,
      mul_inv_cancel_left _ _⟩⟩
  constructor
  · apply HasCompactSupport.intro hS
    intro x hx
    exact integral_eq_zero_of_ae (.of_forall fun t ↦ by_contra fun h ↦ hx (hs h).2)
  · intro D hD
    let Q (x t : G) := f t * g (t⁻¹ * x) * D x
    have hQc : Continuous (uncurry Q) :=
      ((hf.comp continuous_snd).mul (hg.comp (continuous_snd.inv.mul continuous_fst))).mul
        (hD.comp continuous_fst)
    have hQk : HasCompactSupport (uncurry Q) := by
      apply HasCompactSupport.of_support_subset_isCompact (hS.prod hfc)
      intro p hp
      have h : f p.2 * g (p.2⁻¹ * p.1) ≠ 0 := left_ne_zero_of_mul hp
      exact ⟨(hs h).2, (hs h).1⟩
    calc
      _ = ∫ x, ∫ t, Q x t ∂μ ∂μ := by simp only [Q, integral_mul_const, lcaConvolution]
      _ = ∫ t, ∫ x, Q x t ∂μ ∂μ := integral_integral_swap (hQc.integrable_of_hasCompactSupport hQk)
      _ = _ := by
        congr with t
        rw [← integral_mul_left_eq_self (fun x ↦ Q x t) t, ← integral_const_mul]
        congr with y
        simp [Q, mul_assoc]

/-- The scalar convolution pairing determines composition of the integrated
operators by separation by the continuous dual. -/
private theorem compose_test_operators {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (f g k : G → ℂ) (S T U : E → E)
    (hS : ∀ v (ℓ : StrongDual ℂ E), ℓ (S v) = ∫ x, f x * ℓ (ρ x v) ∂μ)
    (hT : ∀ v (ℓ : StrongDual ℂ E), ℓ (T v) = ∫ x, g x * ℓ (ρ x v) ∂μ)
    (hU : ∀ v (ℓ : StrongDual ℂ E), ℓ (U v) = ∫ x, k x * ℓ (ρ x v) ∂μ)
    (hpair : ∀ (D : G → ℂ), Continuous D → (∫ x, k x * D x ∂μ) =
      ∫ t, f t * (∫ y, g y * D (t * y) ∂μ) ∂μ) (u : E) : U u = S (T u) := by
  have : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro δ
  have hp := hpair (fun x ↦ δ (ρ x u)) (δ.continuous.comp (hρ.comp (Continuous.prodMk_left u)))
  refine (hU u δ).trans (hp.trans ((integral_congr_ae ?_).trans (hS (T u) δ).symm))
  refine .of_forall fun t ↦ congrArg (f t * ·) ?_
  refine (integral_congr_ae (.of_forall fun y ↦ ?_)).trans (hT u (δ.comp (ρ t))).symm
  change g y * δ (ρ (t * y) u) = g y * δ (ρ t (ρ y u))
  rw [map_mul, mul_apply_eq_comp]

/-- Paper: Definition 9.3.1.1, p. 419. Convolution of test kernels acts as
composition of their integrated endomorphisms.
Deviation: The convolution is represented by its pointwise formula in the test space. -/
theorem bruhatRegularizedAction_convolution [CompleteSpace E]
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (φ ψ : BruhatCompactSupport G) :
    ∃ θ : BruhatCompactSupport G, θ.val = lcaConvolution μ φ.val ψ.val ∧
      ∀ u, bruhatRegularizedAction μ ρ hρ θ u =
        bruhatRegularizedAction μ ρ hρ φ (bruhatRegularizedAction μ ρ hρ ψ u) := by
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hψs : IsBruhatSmooth ψ.val := (mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1
  have hf : Continuous φ.val := continuous_of_bruhatSmooth hφs
  have hg : Continuous ψ.val := continuous_of_bruhatSmooth hψs
  let h :=  test_convolution_pairing μ hf hg φ.property.2 ψ.property.2
  let θ : BruhatCompactSupport G := (⟨lcaConvolution μ φ.val ψ.val,
    (mem_bruhatSmoothSubmodule_iff _).mpr (fun p ↦ bruhatContDiff_convolution μ hf φ.property.2 (hψs p)),
    h.1⟩ : bruhatCompactSupportSubmodule G)
  let A := bruhatRegularizedAction μ ρ hρ
  have ev (κ : BruhatCompactSupport G) (v : E) (ℓ : StrongDual ℂ E) :
      ℓ (A κ v) = ∫ x, κ.val x * ℓ (ρ x v) ∂μ :=
    (eval_pettis_positive μ (bruhatRegularizedAction_apply μ ρ hρ κ v) ℓ).trans
      (integral_congr_ae (.of_forall fun x ↦ ℓ.map_smul _ _))
  have eq := compose_test_operators μ ρ hρ φ.val ψ.val θ.val (A φ) (A ψ) (A θ)
    (ev φ) (ev ψ) (ev θ) h.2
  with_reducible exact ⟨θ, rfl, eq⟩

end Pettis

/-- Paper: Definition 9.3.1.1, p. 419. The regularized action on the
Hardy–Sobolev space integrates the left translation of its square-integrable classes.
Deviation: Use the compact-interval weighted model of §9.2. -/
def hardySobolevTestAction (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    BruhatCompactSupport G →ₗ[ℂ] Lβ (W a b s) :=
  bruhatRegularizedAction μ (hardySobolevTranslation μ m a b s hab hs)
    (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2

/-- Compactly supported L¹ kernels are Bochner integrable along each continuous
orbit. The orbit norm only has to be bounded on the support of the kernel. -/
private theorem integrable_smul_orbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {φ : G → ℂ} (hi : Integrable φ μ) (hc : HasCompactSupport φ)
    {v : G → E} (hv : Continuous v) : Integrable (fun g ↦ φ g • v g) μ := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hv.continuousOn
  apply (hi.norm.mul_const C).mono' (hi.1.smul hv.aestronglyMeasurable)
  refine .of_forall fun g ↦ ?_
  change ‖φ g • v g‖ ≤ _
  rw [norm_smul]
  by_cases h : φ g = 0
  · simp [h]
  · exact mul_le_mul_of_nonneg_left (hC g (subset_tsupport _ h)) (norm_nonneg _)

/-- Passing the orbit integral through an L² representative gives Haar convolution.
Positivity of the density transfers the resulting equality back to Haar measure. -/
private theorem hardySobolev_orbit_integral (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    {φ : G → ℂ} (hi : Integrable φ μ) (hc : HasCompactSupport φ) (u : W a b s) :
    let τ := hardySobolevTranslation μ m a b s hab hs
    ∀ᵐ x ∂μ, Integrable (fun g ↦ φ g * u (g⁻¹ * x)) μ ∧
      (∫ g, φ g • τ g u ∂μ) x = lcaConvolution μ φ u x := by
  intro τ
  let d (x : G) := ENNReal.ofReal (intervalSobolevDensity a b s (logMod x))
  let ν := μ.withDensity d
  have hν : ν ≪ μ := withDensity_absolutelyContinuous μ d
  have hd : Measurable d := by
    have hlog : Measurable (fun x : G ↦ Real.log ((m x).val : ℝ)) := Real.measurable_log.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable
    have hD : Measurable (intervalSobolevDensity a b s) := by unfold intervalSobolevDensity; fun_prop
    exact (hD.comp hlog).ennreal_ofReal
  have hμ : μ ≪ ν := withDensity_absolutelyContinuous' hd.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (mul_pos (lt_max_of_lt_left (Real.exp_pos _))
      (Real.rpow_pos_of_pos (by positivity) _))).ne')
  have : SigmaFinite ν := MeasureTheory.SigmaFinite.withDensity_ofReal _
  have horbit : Continuous (fun g ↦ τ g u) :=
    (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2.comp (Continuous.prodMk_left u)
  have hmeas : AEStronglyMeasurable (fun p : G × G ↦ φ p.1 * u (p.1⁻¹ * p.2)) (μ.prod ν) :=
    hi.1.comp_fst.mul ((Lp.stronglyMeasurable u).comp_measurable
      (measurable_fst.inv.mul measurable_snd)).aestronglyMeasurable
  apply hμ.ae_le
  apply integral_L2_representative (integrable_smul_orbit μ hi hc horbit) hmeas
  refine .of_forall fun g ↦ ?_
  filter_upwards [Lp.coeFn_smul (φ g) (τ g u),
    hν.ae_le (hardySobolevTranslation_apply μ m a b s hab hs g u)] with x hx hy
  rw [hx, Pi.smul_apply, hy, smul_eq_mul]

/-- A compact integrable kernel acting by Haar convolution on weighted representatives
also acts by the Bochner integral of the translations. -/
theorem hardySobolev_eq_integral_translation_of_convolution
    (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) {φ : G → ℂ}
    (hi : Integrable φ μ) (hc : HasCompactSupport φ)
    (A : W a b s →L[ℂ] W a b s) (hA : ∀ u, (A u : G → ℂ) =ᵐ[μ] lcaConvolution μ φ u) (u : W a b s) :
    A u = ∫ g, φ g • hardySobolevTranslation μ m a b s hab hs g u ∂μ := by
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ _).ae_eq
  exact (hA u).trans ((hardySobolev_orbit_integral μ m a b s hab hs hi hc u).mono fun _ hx ↦ hx.2.symm)

/-- Paper: (9.3.1.2), p. 419. The test action on the weighted Hilbert space
acts by the Haar convolution formula almost everywhere. -/
theorem hardySobolevTestAction_apply (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) (u : W a b s) :
    (hardySobolevTestAction μ m a b s hab hs φ u : G → ℂ) =ᵐ[μ]
      lcaConvolution μ φ.val u := by
  let τ := hardySobolevTranslation μ m a b s hab hs
  have hτ := (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2
  have hi : Integrable φ.val μ :=
    (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 φ.property.1)).integrable_of_hasCompactSupport
      φ.property.2
  have hB := integrable_smul_orbit μ hi φ.property.2 (hτ.comp (Continuous.prodMk_left u))
  have heq := (bruhatRegularizedAction_apply μ τ hτ φ u).unique (Integrable.hasPettisIntegral hB)
  change ((bruhatRegularizedAction μ τ hτ φ u : W a b s) : G → ℂ) =ᵐ[μ] _
  rw [heq]
  exact (hardySobolev_orbit_integral μ m a b s hab hs hi φ.property.2 u).mono fun x hx ↦ hx.2

/-- A surjective modulation admits a section over all positive reals. -/
private theorem exists_fullModulationSection (hm : IsModulation m) (hms : Surjective m) :
    ∃ j : ℝ≥0ˣ →ₜ* G, RightInverse j m := by
  obtain ⟨j, hj⟩ := hm.exists_section
  let i : ℝ≥0ˣ →ₜ* m.toMonoidHom.range :=
    ⟨(MonoidHom.id _).codRestrict _ (fun t ↦ hms t), continuous_id.subtype_mk _⟩
  exact ⟨j.comp i, fun t ↦ hj (i t)⟩

/-- A single twist expresses point evaluation as a continuous Schwartz evaluation. -/
private theorem continuous_decay_eval (hm : IsModulation m) (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (j : ℝ≥0ˣ →ₜ* G) (hj : RightInverse j m) (x : G) :
    Continuous (fun f : ModulatedExponentialDecay m I ↦ f.val x) := by
  let E := ModulatedExponentialDecay m I
  let b : I := ⟨hne.choose, hne.choose_spec⟩
  have htwist : Continuous (fun f : E ↦ modulatedExponentialDecayTwist m I b f) :=
    (continuous_apply b).comp (modulatedExponentialDecay_twists_continuous m I hm hInt hne j hj)
  let δ := (schwartzBruhat_dirac_support x).choose
  have hδ := (schwartzBruhat_dirac_support x).choose_spec.1
  let w : ℂ := (((m x).val : ℝ) ^ (b : ℝ) : ℝ)
  have hw : w ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)) _).ne'
  refine (continuous_const (y := w⁻¹).mul (δ.continuous.comp htwist)).congr fun f ↦ ?_
  change w⁻¹ * δ (modulatedExponentialDecayTwist m I b f) = f.val x
  rw [hδ]
  change w⁻¹ * (w * f.val x) = f.val x
  exact inv_mul_cancel_left₀ hw _

/-- Pointwise evaluation of each Pettis integral recovers a represented function. -/
private theorem exists_pettis_function_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    [UniformSpace V] [IsUniformAddGroup V] [PolynormableSpace ℂ V] [T2Space V] [CompleteSpace V]
    (F : V → G → ℂ) (hF : ∀ x, ∃ δ : StrongDual ℂ V, ∀ u, δ u = F u x)
    (τ : G →* (V →L[ℂ] V)) (hτ : ∀ g u x, F (τ g u) x = F u (g⁻¹ * x))
    (hcτ : Continuous fun p : G × V ↦ τ p.1 p.2) :
    ∃ A : BruhatCompactSupport G →ₗ[ℂ] Lβ V, ∀ φ u,
      F (A φ u) = lcaConvolution μ φ.val (F u) ∧
      HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • τ g u) (A φ u) := by
  have formula (φ : G → ℂ) (u v : V)
      (h : HasPettisIntegral (.positive μ) (fun g ↦ φ g • τ g u) v) :
      F v = lcaConvolution μ φ (F u) := by
    funext x
    obtain ⟨δ, hδ⟩ := hF x
    calc
      F v x = δ v := (hδ v).symm
      _ = ∫ g, δ (φ g • τ g u) ∂μ := eval_pettis_positive μ h δ
      _ = _ := integral_congr_ae (.of_forall fun g ↦ by
        change δ (φ g • τ g u) = φ g * F u (g⁻¹ * x)
        rw [map_smul, hδ, hτ, smul_eq_mul])
  let A := bruhatRegularizedAction μ τ hcτ
  have h (φ : BruhatCompactSupport G) (u : V) := bruhatRegularizedAction_apply μ τ hcτ φ u
  have both (φ : BruhatCompactSupport G) (u : V) :=
    And.intro (formula φ.val u _ (h φ u)) (h φ u)
  with_reducible exact ⟨A, both⟩

/-- Continuous point evaluations as elements of the strong dual. -/
private theorem exists_decay_eval (hm : IsModulation m) (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (j : ℝ≥0ˣ →ₜ* G) (hj : RightInverse j m) (x : G) :
    ∃ δ : StrongDual ℂ (ModulatedExponentialDecay m I), ∀ u, δ u = u.val x := by
  let δ : StrongDual ℂ (ModulatedExponentialDecay m I) :=
    ⟨(LinearMap.proj x).comp (modulatedExponentialDecaySubmodule m I).subtype,
      continuous_decay_eval m hm I hInt hne j hj x⟩
  exact ⟨δ, fun _ ↦ rfl⟩

/-- Point evaluations on the decay space recover the convolution represented by the
orbitwise Pettis integral. -/
private theorem exists_decayAction_pettis (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)
    (τ : G →* (ModulatedExponentialDecay m I →L[ℂ] ModulatedExponentialDecay m I))
    (hτ : ∀ g (u : ModulatedExponentialDecay m I) x, (τ g u).val x = u.val (g⁻¹ * x))
    (hcτ : Continuous (fun p : G × ModulatedExponentialDecay m I ↦ τ p.1 p.2)) :
    ∃ A : BruhatCompactSupport G →ₗ[ℂ] Lβ (ModulatedExponentialDecay m I), ∀ φ u,
      (A φ u).val = lcaConvolution μ φ.val u.val ∧
      HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • τ g u) (A φ u) := by
  let E := ModulatedExponentialDecay m I
  let j := (exists_fullModulationSection m hm hms).choose
  have hj := (exists_fullModulationSection m hm hms).choose_spec
  have : CompleteSpace E := modulatedExponentialDecay_complete m I hm hInt hne j hj
  have : T2Space E := (modulatedExponentialDecay_strictLF m I hm hInt hne j hj).1
  let F (u : ModulatedExponentialDecay m I) : G → ℂ := u.val
  with_reducible
    exact exists_pettis_function_action (V := E) μ F
      (exists_decay_eval m hm I hInt hne j hj) τ hτ hcτ

/-- Paper: Remark 9.3.1.2, p. 419. Convolution by a test function defines
a continuous endomorphism of the exponential-decay space and depends linearly on the test.
Deviation: Evaluating the Pettis integral at each group element gives this pointwise formula. -/
theorem exists_modulatedExponentialDecayTestAction
    (_hm : IsModulation m) (_hms : Surjective m)
    (I : Set ℝ) (_hInt : OrdConnected I) (_hne : I.Nonempty) :
    ∃ A : BruhatCompactSupport G →ₗ[ℂ] Lβ (ModulatedExponentialDecay m I),
      ∀ φ u, (A φ u).val = lcaConvolution μ φ.val u.val := by
  let t := exists_modulatedExponentialDecay_translationAction m I _hm _hms _hInt _hne
  let h := exists_decayAction_pettis μ m _hm _hms I _hInt _hne t.choose t.choose_spec.1 t.choose_spec.2
  with_reducible exact ⟨h.choose, fun φ u ↦ (h.choose_spec φ u).1⟩

/-- Paper: Definition 9.3.1.1, p. 419. The regularized action on the
exponential-decay space acts by convolution of the test function with the input. -/
def modulatedExponentialDecayTestAction (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty) :
    BruhatCompactSupport G →ₗ[ℂ] Lβ (ModulatedExponentialDecay m I) :=
  (exists_modulatedExponentialDecayTestAction μ m hm hms I hInt hne).choose

/-- Paper: (9.3.1.2), p. 419. The test action on the exponential-decay space
has the usual pointwise Haar convolution formula. -/
theorem modulatedExponentialDecayTestAction_apply (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)
    (φ : BruhatCompactSupport G) (u : ModulatedExponentialDecay m I) :
    (modulatedExponentialDecayTestAction μ m hm hms I hInt hne φ u).val =
      lcaConvolution μ φ.val u.val := by
  delta modulatedExponentialDecayTestAction
  with_reducible exact (exists_modulatedExponentialDecayTestAction μ m hm hms I hInt hne).choose_spec φ u

/-- Paper: Definition 9.3.1.1, p. 419. The decay-space convolution integrates
the orbits of the left-translation representation of Proposition D.3.3.12. -/
theorem modulatedExponentialDecayTestAction_pettis (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)
    (φ : BruhatCompactSupport G) (u : ModulatedExponentialDecay m I) :
    let τ := (exists_modulatedExponentialDecay_translationAction m I hm hms hInt hne).choose
    HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • τ g u)
      (modulatedExponentialDecayTestAction μ m hm hms I hInt hne φ u) := by
  intro τ
  let t := exists_modulatedExponentialDecay_translationAction m I hm hms hInt hne
  let h := exists_decayAction_pettis μ m hm hms I hInt hne t.choose t.choose_spec.1 t.choose_spec.2
  have heq : h.choose φ u = modulatedExponentialDecayTestAction μ m hm hms I hInt hne φ u :=
    Subtype.ext ((h.choose_spec φ u).1.trans
      (modulatedExponentialDecayTestAction_apply μ m hm hms I hInt hne φ u).symm)
  let P (v : ModulatedExponentialDecay m I) := HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • τ g u) v
  with_reducible exact Eq.subst (motive := P) heq (h.choose_spec φ u).2

open scoped Pointwise in
/-- On a compact set of group elements a jointly continuous action carries a bounded
family of vectors to a family bounded for each continuous seminorm. -/
private theorem bounded_compact_orbits {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous fun z : G × E ↦ ρ z.1 z.2)
    (K : TopologicalSpace.Compacts G) {B : Set E} (hB : Bornology.IsVonNBounded ℂ B)
    (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ C : ℝ≥0, ∀ g ∈ (K : Set G), ∀ x ∈ B, p (ρ g x) ≤ C := by
  let N := {z : G × E | p (ρ z.1 z.2) < 1}
  have hN : IsOpen N := isOpen_lt (hp.comp hρ) continuous_const
  have hsub : (K : Set G) ×ˢ {(0 : E)} ⊆ N := by
    rintro ⟨g, x⟩ ⟨_, rfl : x = 0⟩
    change p (ρ g 0) < 1
    simp
  obtain ⟨V, U, -, hU, hKV, h0U, hVU⟩ :=
    generalized_tube_lemma K.isCompact isCompact_singleton hN hsub
  obtain ⟨r, hr, h⟩ := (hB (hU.mem_nhds (h0U (mem_singleton 0)))).exists_pos
  have hnorm : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  refine ⟨⟨r, hr.le⟩, fun g hg x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := h (r : ℂ) hnorm.ge hx
  have hsmall : p (ρ g y) < 1 := hVU (show (g,y) ∈ V ×ˢ U from ⟨hKV hg, hy⟩)
  change p (ρ g ((r : ℂ) • y)) ≤ r
  rw [map_smul, map_smul_eq_mul, hnorm]
  exact mul_le_of_le_one_right hr.le hsmall.le

/-- The order-zero seminorm of an elementary stage bounds all its realized values. -/
private theorem stage_value_le (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (f : SchwartzBruhatStage e) (x : G) :
    ‖schwartzBruhatStageRealization a e f x‖ ≤ elementarySchwartzSeminorm (0, 0, 0, 0) f := by
  rw [schwartzBruhatStageRealization_apply]
  split_ifs with hx
  · change (‖f _‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
    apply ENNReal.toReal_mono (f.property.2 _).ne
    rw [elementarySchwartzBound_zero]
    exact le_iSup (fun y ↦ (‖f y‖₊ : ENNReal)) _
  · exact norm_zero.trans_le (apply_nonneg _ _)

/-- A support and a uniform bound for a scalar kernel control each mapping
seminorm of its Pettis operator. -/
private theorem mappingSeminorm_pettis_bound {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    (ρ : G →* (E →L[ℂ] E)) (K : TopologicalSpace.Compacts G)
    (B : {B : Set E // Bornology.IsVonNBounded ℂ B}) (p : {p : Seminorm ℂ E // Continuous p})
    {C M : ℝ≥0} (hC : ∀ g ∈ (K : Set G), ∀ u ∈ B.val, p.val (ρ g u) ≤ C)
    (φ : G → ℂ) (hoff : ∀ g ∉ (K : Set G), φ g = 0) (hM : ∀ g, ‖φ g‖ ≤ M)
    (T : E →L[ℂ] E) (hT : ∀ u, HasPettisIntegral (.positive μ) (fun g ↦ φ g • ρ g u) (T u)) :
    mappingSeminorm B p T ≤ (M * C) * μ.real (K : Set G) := by
  rw [mappingSeminorm_apply]
  apply Real.iSup_le _ (by positivity)
  intro u
  obtain ⟨δ, hδ, heq⟩ := exists_dual_norm_eq_seminorm p.val p.property (T u.val)
  rw [← heq, eval_pettis_positive μ (hT u.val) δ]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) (s := (K : Set G))
    (fun g hg ↦ by rw [hoff g hg, zero_smul, map_zero])]
  apply norm_setIntegral_le_of_norm_le_const K.isCompact.measure_lt_top
  intro g hg
  rw [map_smul, norm_smul]
  exact mul_le_mul (hM g) ((hδ _).trans (hC g hg u.val u.property)) (norm_nonneg _) M.coe_nonneg

/-- An orbitwise Pettis action is continuous for uniform convergence on bounded
sets. On each fixed-support stage its mapping seminorms are controlled by the
zero-order Schwartz seminorm times the Haar mass of the support. -/
private theorem continuous_pettis_test_action {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous fun z : G × E ↦ ρ z.1 z.2)
    (A : BruhatCompactSupport G →ₗ[ℂ] Lβ E)
    (hA : ∀ φ u, HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • ρ g u) (A φ u)) :
    Continuous A := by
  classical
  let S := {B : Set E | Bornology.IsVonNBounded ℂ B}
  have hd : Dense (Submodule.span ℂ (⋃₀ S) : Set E) := by
    have he : ⋃₀ S = univ := eq_univ_of_forall fun x ↦
      mem_sUnion.mpr ⟨{x}, Bornology.isVonNBounded_singleton (𝕜 := ℂ) x, mem_singleton x⟩
    rw [he, Submodule.span_univ, Submodule.top_coe]
    exact dense_univ
  apply (uniformConvergenceCLM_withSeminorms S (fun _ h ↦ h) hd _
    (PolynormableSpace.withSeminorms ℂ E)).continuous_of_continuous_comp A
  rintro ⟨B, p⟩
  let Q := (mappingSeminorm B p).comp A
  have hstage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) (K : TopologicalSpace.Compacts G) :
      Continuous (Q ∘ bruhatCompactSupportStageInclusion a e K) := by
    let hb := bounded_compact_orbits ρ hρ K B.property p.val p.property
    let C := hb.choose
    have hC := hb.choose_spec
    let q₀ : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    let q : Seminorm ℂ (bruhatCompactSupportStage a e K) := q₀.comp (bruhatCompactSupportStage a e K).subtype
    have hq : Continuous q := (elementarySchwartz_withSeminorms.continuous_seminorm
      (0, 0, 0, 0)).comp continuous_subtype_val
    let c : ℝ≥0 := C * (μ (K : Set G)).toNNReal
    change Continuous ((Q.comp (bruhatCompactSupportStageInclusion a e K)) : Seminorm ℂ _)
    apply Seminorm.continuous_of_le (q := c • q) (hq.const_smul c)
    intro f
    let φ : BruhatCompactSupport G := bruhatCompactSupportStageInclusion a e K f
    change mappingSeminorm B p (A φ) ≤ (c : ℝ) * q f
    have hoff (g : G) (hg : g ∉ (K : Set G)) : φ.val g = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h ↦ hg ((mem_bruhatCompactSupportStage_iff a e K f.val).mp f.property h)
    let M : ℝ≥0 := ⟨q f, apply_nonneg _ _⟩
    have hh := mappingSeminorm_pettis_bound μ ρ K B p (M := M) hC φ.val hoff
      (stage_value_le a e f.val) (A φ) (hA φ)
    exact hh.trans_eq (by change (q f * C) * (μ (K : Set G)).toReal =
      (C * (μ (K : Set G)).toReal) * q f; ring)
  let J := {q : Seminorm ℂ (bruhatCompactSupportSubmodule G) //
    ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) (K : TopologicalSpace.Compacts G),
      Continuous (q ∘ bruhatCompactSupportStageInclusion a e K)}
  let j : J := ⟨Q, hstage⟩
  have hj := (withGeneratingSeminorms_spec (bruhatCompactSupportSubmodule G)
    (Subtype.val : J → Seminorm ℂ (bruhatCompactSupportSubmodule G))).continuous_seminorm j
  exact hj.congr (fun _ ↦ rfl)

/-- Paper: Lemma 9.3.1.3, p. 419. The test action on the Hardy–Sobolev
space is continuous into the topology of uniform convergence on bounded sets.
Deviation: The weighted Hilbert model is for a compact base interval. -/
theorem continuous_hardySobolevTestAction (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    Continuous (hardySobolevTestAction μ m a b s hab hs) := by
  let τ := hardySobolevTranslation μ m a b s hab hs
  have hτ := (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2
  exact continuous_pettis_test_action μ τ hτ (hardySobolevTestAction μ m a b s hab hs)
    (bruhatRegularizedAction_apply μ τ hτ)

/-- Paper: Lemma 9.3.1.3, p. 419. The test action on the exponential-decay
space is continuous into the topology of uniform convergence on bounded sets. -/
theorem continuous_modulatedExponentialDecayTestAction (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty) :
    Continuous (modulatedExponentialDecayTestAction μ m hm hms I hInt hne) := by
  let t := exists_modulatedExponentialDecay_translationAction m I hm hms hInt hne
  let j := (exists_fullModulationSection m hm hms).choose
  have : T2Space (ModulatedExponentialDecay m I) :=
    (modulatedExponentialDecay_strictLF m I hm hInt hne j
      (exists_fullModulationSection m hm hms).choose_spec).1
  with_reducible
    exact continuous_pettis_test_action μ t.choose t.choose_spec.2
      (modulatedExponentialDecayTestAction μ m hm hms I hInt hne)
      (modulatedExponentialDecayTestAction_pettis μ m hm hms I hInt hne)

-- TODO(later): Remark 9.3.1.4, p. 420, restricts the regularized action to
-- the global theta closure of §10.1 and to the S-local theta action of §5.4.

-- TODO(paper-gap): Lemma 9.3.1.5's bound is zero at the identity for s > 0.
-- The singleton polynomial-growth claim also omits the exponential twist for b ≠ 0.
-- Borel measurability need not hold for arbitrary continuous operator seminorms.

/-- A continuous endomorphism of a weighted L² space of a left-invariant measure that acts
by left translation on representatives has norm at most `C` when the translated density is
at most `C ^ 2` times the density. -/
private theorem opNorm_le_of_translate_density {H : Type*} [Group H] [MeasurableSpace H]
    [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] {d : H → ℝ≥0∞}
    (hd : Measurable d) (hd' : ∀ x, d x < ⊤) (g : H) {C : ℝ} (hC : 0 ≤ C)
    (hle : ∀ x, d (g * x) ≤ ENNReal.ofReal C ^ 2 * d x)
    (T : Lp ℂ 2 (ν.withDensity d) →L[ℂ] Lp ℂ 2 (ν.withDensity d))
    (hT : ∀ u, (T u : H → ℂ) =ᵐ[ν] fun x ↦ u (g⁻¹ * x)) : ‖T‖ ≤ C := by
  refine T.opNorm_le_bound hC fun u ↦ ?_
  have hae : (T u : H → ℂ) =ᵐ[ν.withDensity d] fun x ↦ u (g⁻¹ * x) :=
    (withDensity_absolutelyContinuous ν d).ae_eq (hT u)
  have hnorm : eLpNorm (T u) 2 (ν.withDensity d) ≤
      ENNReal.ofReal C * eLpNorm u 2 (ν.withDensity d) := by
    rw [eLpNorm_congr_ae hae]
    exact translate_eLpNorm_le ν hd hd' g hle u (Lp.aestronglyMeasurable u)
      ((Lp.aestronglyMeasurable (T u)).congr hae)
  rw [Lp.norm_def, Lp.norm_def]
  calc (eLpNorm (T u) 2 (ν.withDensity d)).toReal
      ≤ (ENNReal.ofReal C * eLpNorm u 2 (ν.withDensity d)).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u)) hnorm
    _ = C * (eLpNorm u 2 (ν.withDensity d)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]

/-- Paper: Lemma 9.3.1.5, p. 421. Left translation is bounded by the maximum
endpoint twist times a polynomial in the absolute log-module.
Deviation: The factor at the identity is one. On a nonzero singleton base
the endpoint twist still occurs. -/
theorem norm_hardySobolevTranslation_le (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) (g : G) :
    ‖hardySobolevTranslation μ m a b s hab hs g‖ ≤
      max (Real.exp (a * logMod g)) (Real.exp (b * logMod g)) *
        (1 + |logMod g|) ^ (s / 2) := by
  have hD : Measurable fun t : ℝ ↦ intervalSobolevDensity a b s t := by
    unfold intervalSobolevDensity
    fun_prop
  have hmeas : Measurable fun x : G ↦ Real.log ((m x).val : ℝ) :=
    Real.measurable_log.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (map_continuous m))).measurable
  have hlog : ∀ x : G, Real.log ((m (g * x)).val : ℝ) =
      Real.log ((m g).val : ℝ) + Real.log ((m x).val : ℝ) := fun x ↦ by
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (m g).ne_zero) (NNReal.coe_ne_zero.2 (m x).ne_zero)]
  have hC : 0 ≤ max (Real.exp (a * Real.log ((m g).val : ℝ)))
      (Real.exp (b * Real.log ((m g).val : ℝ))) *
      (1 + |Real.log ((m g).val : ℝ)|) ^ (s / 2) :=
    mul_nonneg (le_max_of_le_left (Real.exp_pos _).le) (Real.rpow_nonneg (by positivity) _)
  have key := opNorm_le_of_translate_density μ
    (d := fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ))))
    (hD.comp hmeas).ennreal_ofReal (fun _ ↦ ENNReal.ofReal_lt_top) g hC fun x ↦ by
      show ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m (g * x)).val : ℝ))) ≤
        ENNReal.ofReal _ ^ 2 * ENNReal.ofReal _
      rw [hlog x, ← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (intervalSobolevDensity_add_le a b s hs _ _)
  exact key (hardySobolevTranslation μ m a b s hab hs g)
    (hardySobolevTranslation_apply μ m a b s hab hs g)

/-- Paper: Lemma 9.3.1.5, p. 421. The operator norm of left translation is a
measurable function of the translating element.
Deviation: This retains the measurable operator-norm case established on p. 422. -/
theorem measurable_hardySobolevTranslation_norm (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    Measurable (fun g ↦ ‖hardySobolevTranslation μ m a b s hab hs g‖) := by
  have hcont (u : W a b s) : Continuous (fun g ↦ hardySobolevTranslation μ m a b s hab hs g u) :=
    (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2.comp
      (Continuous.prodMk_left u)
  have hEq : (fun g ↦ ‖hardySobolevTranslation μ m a b s hab hs g‖) =
      fun g ↦ ⨆ u : Metric.closedBall (0 : W a b s) 1,
        ‖hardySobolevTranslation μ m a b s hab hs g u‖ := by
    funext g
    rw [← ContinuousLinearMap.sSup_unitClosedBall_eq_norm, sSup_image', iSup]
  rw [hEq]
  refine LowerSemicontinuous.measurable (lowerSemicontinuous_ciSup (fun g ↦ ?_) fun u ↦ ?_)
  · refine ⟨‖hardySobolevTranslation μ m a b s hab hs g‖, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact ((hardySobolevTranslation μ m a b s hab hs g).le_opNorm_of_le
      (mem_closedBall_zero_iff.mp u.2)).trans_eq (mul_one _)
  · exact ((hcont u).norm).lowerSemicontinuous

end RegularizedAction

section ApproximateUnits

variable [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (m : G →ₜ* ℝ≥0ˣ)

-- TODO(paper-gap): Lemma 9.3.2.1 does not extend from ordinary Schwartz–Bruhat kernels for
-- b ≠ 0. Its single-isotype family cannot converge strongly to the identity on two isotypes.

/-- The logarithm of a positive character is a Fourier multiplier on Schwartz–Bruhat
functions. On the dual it is a constant multiple of a first derivative. -/
private theorem log_mul_schwartz (f : SchwartzBruhat G) :
    (fun x ↦ (Real.log ((m x).val : ℝ) : ℂ) * f x) ∈ schwartzBruhatSubmodule G := by
  let ℓ : G →ₜ* Multiplicative ℝ := (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp m
  let H := PontryaginDual G
  let : MeasurableSpace H := borel _
  let : BorelSpace H := ⟨rfl⟩
  obtain ⟨b, _⟩ := pontryaginDual_bidual (G := G)
  obtain ⟨σ, _, _, hχ⟩ := bruhatDiffDegreeOne_frequency (G := H)
  let d := σ.symm (ℓ.comp (b.symm : PontryaginDual H →ₜ* G))
  obtain ⟨a, ha⟩ := (mem_bruhatDiffDegreeOneReal_iff d.val).mp d.property
  let P := bruhatDiffGenerator a
  let c : ℂ := 2 * ↑Real.pi * Complex.I
  have hc : c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hP (x : G) : bruhatDiffSymbol P (b x) = c * (Real.log ((m x).val : ℝ) : ℂ) := by
    apply bruhatDiffSymbol_generator
    have h := hχ a d ha (b x)
    have hdx : σ d (b x) = ℓ x := by
      rw [show σ d = ℓ.comp (b.symm : PontryaginDual H →ₜ* G) from σ.apply_symm_apply _]
      exact congrArg ℓ (b.symm_apply_apply x)
    rw [hdx, show (ℓ x).toAdd = Real.log ((m x).val : ℝ) from positiveRealLogEquiv_apply _] at h
    exact h
  let ν : Measure H := Measure.haar
  obtain ⟨F, hF⟩ := schwartzBruhat_fourier_equiv ν
  let T := (exists_schwartzBruhat_pullback b.symm).choose
  let U := (exists_schwartzBruhat_pullback b).choose
  have hT := (exists_schwartzBruhat_pullback b.symm).choose_spec
  have hU := (exists_schwartzBruhat_pullback b).choose_spec
  let u := F.symm (T f)
  obtain ⟨_, v, _, _, _, hv⟩ := lcaFourier_bruhatDiff ν P u
  have heq : (fun x ↦ (Real.log ((m x).val : ℝ) : ℂ) * f x) =
      c⁻¹ • (U (F v)).val := by
    funext x
    change _ = c⁻¹ * U (F v) x
    have hfu : F u = T f := F.apply_symm_apply _
    calc
      _ = c⁻¹ * ((c * (Real.log ((m x).val : ℝ) : ℂ)) * f x) := by rw [mul_assoc, inv_mul_cancel_left₀ hc]
      _ = c⁻¹ * (bruhatDiffSymbol P (b x) * F u (b x)) := by
        have eqval : F u (b x) = f x := (congrArg (fun z : SchwartzBruhat (PontryaginDual H) ↦ z (b x)) hfu).trans
          ((hT f (b x)).trans (congrArg f (b.symm_apply_apply x)))
        exact congrArg (c⁻¹ * ·) (congrArg₂ (· * ·) (hP x).symm eqval.symm)
      _ = c⁻¹ * lcaFourier ν v (b x) := congrArg (c⁻¹ * ·) (by
        exact (congrArg (bruhatDiffSymbol P (b x) * ·) ((hF u).2 (b x))).trans (congrFun hv (b x)).symm)
      _ = _ := congrArg (c⁻¹ * ·) (((hF v).2 (b x)).symm.trans (hU (F v) x).symm)
  exact Eq.subst (motive := (· ∈ schwartzBruhatSubmodule G)) heq.symm (show c⁻¹ • (U (F v)).val ∈ schwartzBruhatSubmodule G from
    (schwartzBruhatSubmodule G).smul_mem c⁻¹ (U (F v)).property)

/-- Integrability of Schwartz functions persists under every polynomial weight in
the logarithm of a continuous positive character. -/
private theorem integrable_schwartz_log_weight (f : SchwartzBruhat G) (r : ℝ) :
    Integrable (fun x ↦ ‖f x‖ * (1 + |Real.log ((m x).val : ℝ)|) ^ r) μ := by
  let t (x : G) := Real.log ((m x).val : ℝ)
  have ht : Continuous t := (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
    fun x ↦ NNReal.coe_ne_zero.2 (m x).ne_zero
  have hpoly (n : ℕ) : (fun x ↦ (t x : ℂ) ^ n * f x) ∈ schwartzBruhatSubmodule G := by
    induction n with
    | zero => simpa using f.property
    | succ n ih =>
      have h := log_mul_schwartz m (⟨_, ih⟩ : SchwartzBruhat G)
      convert h using 1
      funext x
      change (t x : ℂ) ^ (n + 1) * f x = (t x : ℂ) * ((t x : ℂ) ^ n * f x)
      ring
  obtain ⟨n, hn⟩ := exists_nat_ge r
  have hI := (schwartzBruhat_fourier_equiv μ).choose_spec
  have hf := (hI f).1.norm
  have hp := (hI (⟨_, hpoly n⟩ : SchwartzBruhat G)).1.norm
  have H := (hf.add hp).const_mul ((2 : ℝ) ^ n)
  refine H.mono' ((continuous_schwartzBruhat f).norm.mul
    ((continuous_const.add ht.abs).rpow_const fun x ↦ Or.inl (ne_of_gt (by positivity : 0 < 1 + |t x|)))).aestronglyMeasurable ?_
  apply Eventually.of_forall
  intro x
  change ‖‖f x‖ * (1 + |t x|) ^ r‖ ≤ 2 ^ n * (‖f x‖ + ‖(t x : ℂ) ^ n * f x‖)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)),
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h := Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (t x)] : 1 ≤ 1 + |t x|) hn
  rw [Real.rpow_natCast] at h
  apply (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans
  rcases le_total |t x| 1 with hsmall | hlarge
  · have h' := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |t x|) (by linarith : 1 + |t x| ≤ 2) n
    nlinarith [mul_le_mul_of_nonneg_left h' (norm_nonneg (f x)),
      mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n) (mul_nonneg (pow_nonneg (abs_nonneg (t x)) n) (norm_nonneg (f x)))]
  · have h' := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |t x|) (by linarith : 1 + |t x| ≤ 2 * |t x|) n
    rw [mul_pow] at h'
    nlinarith [mul_le_mul_of_nonneg_left h' (norm_nonneg (f x)),
      mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n) (norm_nonneg (f x))]

/-- A weighted L¹ seminorm finite on Schwartz–Bruhat functions is continuous.
On each metrizable barrelled stage its sublevel sets are closed by Fatou's lemma. -/
private theorem schwartz_integral_seminorm (w : G → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hi : ∀ f : SchwartzBruhat G, Integrable (fun x ↦ ‖f x‖ * w x) μ) :
    ∃ q : Seminorm ℂ (SchwartzBruhat G), Continuous q ∧
      ∀ f, q f = ∫ x, ‖f x‖ * w x ∂μ := by
  let j : SchwartzBruhat G →ₗ[ℂ] (G → ℂ) := (schwartzBruhatSubmodule G).subtype
  let h := exists_integral_seminorm μ j w hw (fun f ↦ hi f)
  let q := h.choose
  have hq := h.choose_spec
  refine ⟨q, ?_, hq⟩
  have hstage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (q.comp (schwartzBruhatStageInclusion a e)) := by
    let : FirstCountableTopology (SchwartzBruhatStage e) :=
      elementarySchwartz_withSeminorms.firstCountableTopology
    let : BarrelledSpace ℂ (SchwartzBruhatStage e) := elementarySchwartz_barrelled
    let i := schwartzBruhatStageInclusion a e
    exact continuous_integral_seminorm μ (fun u x ↦ schwartzBruhatStageRealization a e u x)
      (continuous_schwartzBruhatStage_eval a e) w hw (fun u ↦ hi (i u)) (q.comp i) (fun u ↦ hq (i u))
  let J := {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
    ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion a e)}
  let z : J := ⟨q, fun a e ↦ hstage a e⟩
  have hc := (withGeneratingSeminorms_spec (schwartzBruhatSubmodule G)
    (Subtype.val : J → Seminorm ℂ (schwartzBruhatSubmodule G))).continuous_seminorm z
  exact hc.congr fun _ ↦ rfl

omit [CommGroup G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [μ.IsHaarMeasure] in
/-- Integrating the orbits of a strongly continuous operator family gives a
continuous map into bounded operators when a continuous seminorm controls its
weighted kernel integrals. -/
private theorem integrated_kernel_family {V E : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (j : V →ₗ[ℂ] (G → ℂ)) (T : G → E →L[ℂ] E)
    (hj : ∀ f, Continuous (j f)) (hT : ∀ u, Continuous fun g ↦ T g u)
    (w : G → ℝ) (hw : ∀ g, ‖T g‖ ≤ w g)
    (hi : ∀ f, Integrable (fun g ↦ ‖j f g‖ * w g) μ)
    (q : Seminorm ℂ V) (hc : Continuous q) (hq : ∀ f, q f = ∫ g, ‖j f g‖ * w g ∂μ) :
    ∃ A : V →L[ℂ] (E →L[ℂ] E), ∀ f u,
      HasPettisIntegral (.positive μ) (fun g ↦ j f g • T g u) (A f u) := by
  have hb (f u g) : ‖j f g • T g u‖ ≤ (‖j f g‖ * w g) * ‖u‖ := by
    rw [norm_smul, mul_assoc]
    gcongr
    exact ((T g).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hw g) (norm_nonneg _))
  have hI (f u) : Integrable (fun g ↦ j f g • T g u) μ :=
    ((hi f).mul_const ‖u‖).mono' ((hj f).smul (hT u)).aestronglyMeasurable
      (.of_forall (hb f u))
  let L (f : V) : E →ₗ[ℂ] E :=
    { toFun := fun u ↦ ∫ g, j f g • T g u ∂μ
      map_add' := fun u v ↦ by simp only [map_add, smul_add]; exact integral_add (hI f u) (hI f v)
      map_smul' := fun c u ↦ by simp only [map_smul, smul_comm (j f _) c, integral_smul, RingHom.id_apply] }
  have hB (f u) : ‖L f u‖ ≤ q f * ‖u‖ := calc
    _ ≤ ∫ g, ‖j f g • T g u‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ g, (‖j f g‖ * w g) * ‖u‖ ∂μ := integral_mono (hI f u).norm ((hi f).mul_const _) (hb f u)
    _ = _ := by rw [integral_mul_const, hq]
  let B (f : V) := (L f).mkContinuous (q f) (hB f)
  let A : V →ₗ[ℂ] (E →L[ℂ] E) :=
    { toFun := B
      map_add' := fun f k ↦ by
        ext u
        change (∫ g, j (f + k) g • T g u ∂μ) = _ + _
        simp only [map_add, Pi.add_apply, add_smul]
        exact integral_add (hI f u) (hI k u)
      map_smul' := fun c f ↦ by
        ext u
        change (∫ g, j (c • f) g • T g u ∂μ) = c • _
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_smul, integral_smul]
        rfl }
  have hAc : Continuous A := by
    refine (norm_withSeminorms ℂ (E →L[ℂ] E)).continuous_of_continuous_comp A fun _ ↦ ?_
    exact Seminorm.continuous_of_le hc fun f ↦ (B f).opNorm_le_bound (apply_nonneg q f) (hB f)
  exact ⟨⟨A, hAc⟩, fun f u ↦ Integrable.hasPettisIntegral (hI f u)⟩

/-- On a singleton line, division by the endpoint character leaves only the
polynomial translation bound. The normalized orbits therefore act on Schwartz kernels. -/
private theorem exists_normalized_line_action (b s : ℝ) (hs : 0 ≤ s) :
    let W := CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) b b s
    ∃ A : SchwartzBruhat G →L[ℂ] (W →L[ℂ] W), ∀ (f : SchwartzBruhat G) u,
      HasPettisIntegral (.positive μ) (fun g ↦
        (f g * (Real.exp (b * Real.log ((m g).val : ℝ)) : ℂ)⁻¹) •
          hardySobolevTranslation μ m b b s le_rfl hs g u) (A f u) := by
  intro W
  let τ := hardySobolevTranslation μ m b b s le_rfl hs
  let t (g : G) := Real.log ((m g).val : ℝ)
  let d (g : G) := Real.exp (b * t g)
  let w (g : G) := (1 + |t g|) ^ (s / 2)
  let T (g : G) : W →L[ℂ] W := (d g : ℂ)⁻¹ • τ g
  have hcont : Continuous (fun g ↦ (d g : ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (continuous_logModule' m)))).inv₀ (fun _ ↦
        Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  have hT (u : W) : Continuous (fun g ↦ T g u) :=
    hcont.smul ((exists_hardySobolevTranslation μ m b b s le_rfl hs).choose_spec.2.comp
      (Continuous.prodMk_left u))
  have hB (g) : ‖T g‖ ≤ w g := by
    have h0 := norm_hardySobolevTranslation_le μ m b b s le_rfl hs g
    rw [max_self] at h0
    change ‖(d g : ℂ)⁻¹ • τ g‖ ≤ _
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (inv_mul_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm (w g)] using h0)
  let j : SchwartzBruhat G →ₗ[ℂ] (G → ℂ) := (schwartzBruhatSubmodule G).subtype
  have hi := integrable_schwartz_log_weight μ m
  let hq := schwartz_integral_seminorm μ w (fun g ↦ Real.rpow_nonneg (by positivity) _)
    (fun f ↦ hi f (s / 2))
  let h := integrated_kernel_family μ j T (fun f ↦ continuous_schwartzBruhat f) hT w hB
    (fun f ↦ hi f (s / 2)) hq.choose hq.choose_spec.1 hq.choose_spec.2
  refine ⟨h.choose, fun f u ↦ ?_⟩
  have he (g) : j f g • T g u = (f g * (d g : ℂ)⁻¹) • τ g u := (mul_smul _ _ _).symm
  let P (z : G → W) := HasPettisIntegral (.positive μ) z (h.choose f u)
  exact Eq.subst (motive := P) (funext he) (h.choose_spec f u)

/-- Paper: Lemma 9.3.2.1, p. 422. On the zero line there is a unique
operator-norm-continuous extension from test functions to Schwartz–Bruhat kernels,
given on each vector by integration of its left translates.
Deviation: This is the separately stated zero-line case of (9.3.2.2) in the proof on
pp. 422–423. The test-space restriction is specified by the same Pettis formula as (9.3.1.2). -/
theorem existsUnique_schwartzBruhat_zeroLineAction (s : ℝ) (hs : 0 ≤ s) :
    let W := CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 0 0 s
    ∃! A : SchwartzBruhat G →L[ℂ] (W →L[ℂ] W),
      ∀ φ u, HasPettisIntegral (.positive μ)
        (fun g ↦ φ.val g • hardySobolevTranslation μ m 0 0 s le_rfl hs g u) (A φ u) := by
  intro W
  let h := exists_normalized_line_action μ m 0 s hs
  have hA (f : SchwartzBruhat G) (u : W) :
      HasPettisIntegral (.positive μ) (fun g ↦ f.val g •
        hardySobolevTranslation μ m 0 0 s le_rfl hs g u) (h.choose f u) := by
    simpa only [zero_mul, Real.exp_zero, Complex.ofReal_one, inv_one, mul_one] using h.choose_spec f u
  exact ⟨h.choose, hA, fun A hA' ↦ ContinuousLinearMap.ext fun f ↦
    ContinuousLinearMap.ext fun u ↦ (hA' f u).unique (hA f u)⟩

/-- Paper: Lemma 9.3.2.1, p. 422. On the b-line, kernels whose b-twist is
Schwartz act continuously and extend the test action.
Deviation: The source is the singleton decay space from Example D.3.3.5,
as required by the conjugation in the proof on p. 422.

Deviation: Equation (9.3.2.1) takes ordinary Schwartz–Bruhat kernels for arbitrary $b$, and the
proof prints the twist with the wrong sign on the arrow out of that space. Multiplication by
$m^b$ sends the singleton decay kernels used here to Schwartz–Bruhat kernels.
-/
theorem existsUnique_singletonDecay_lineAction (hm : IsModulation m) (hms : Surjective m)
    (b s : ℝ) (hs : 0 ≤ s) :
    let W := CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) b b s
    ∃! A : ModulatedExponentialDecay m {b} →L[ℂ] (W →L[ℂ] W),
      (∀ φ u, HasPettisIntegral (.positive μ)
        (fun g ↦ φ.val g • hardySobolevTranslation μ m b b s le_rfl hs g u) (A φ u)) ∧
      ∀ (φ : BruhatCompactSupport G) u,
        A (bruhatCompactSupportToModulatedExponentialDecay m {b} hm hms φ) u =
          hardySobolevTestAction μ m b b s le_rfl hs φ u := by
  intro W
  let h := exists_normalized_line_action μ m b s hs
  let e := (modulatedExponentialDecay_singleton_schwartz m hm hms b).choose
  have he := (modulatedExponentialDecay_singleton_schwartz m hm hms b).choose_spec
  let A := h.choose.comp e.toContinuousLinearMap
  have hA (f : ModulatedExponentialDecay m {b}) (u : W) :
      HasPettisIntegral (.positive μ) (fun g ↦ f.val g •
        hardySobolevTranslation μ m b b s le_rfl hs g u) (A f u) := by
    have hpoint (g : G) : e f g * (Real.exp (b * Real.log ((m g).val : ℝ)) : ℂ)⁻¹ = f.val g := by
      have hval := congrFun (he f) g
      change e f g = ((((m g).val : ℝ) ^ b : ℝ) : ℂ) * f.val g at hval
      rw [hval, Real.rpow_def_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)), mul_comm (Real.log _)]
      field_simp
    have eqf := funext fun g ↦ congrArg (· • hardySobolevTranslation μ m b b s le_rfl hs g u) (hpoint g)
    let P (z : G → W) := HasPettisIntegral (.positive μ) z (h.choose (e f) u)
    exact Eq.subst (motive := P) eqf (h.choose_spec (e f) u)
  refine ⟨A, ⟨hA, fun φ u ↦ ?_⟩, fun B hB ↦ ?_⟩
  · exact (hA (bruhatCompactSupportToModulatedExponentialDecay m {b} hm hms φ) u).unique
      (bruhatRegularizedAction_apply μ _ _ φ u)
  · exact ContinuousLinearMap.ext fun f ↦ ContinuousLinearMap.ext fun u ↦ (hB.1 f u).unique (hA f u)

-- Remark 9.3.2.2, p. 422, distinguishes the integral approximations from
-- the metric approximation property of a Hilbert space.

/-- Paper: Corollary 9.3.2.3(1), p. 425. The frequency band attached to a character
consists of its twists by imaginary powers of the module with exponents in the given interval.
Deviation: The band is a subset of the full dual, as in the construction in the proof.

Deviation: Corollary 9.3.2.3(1) places the band containing the Fourier support in the dual of
$G^1$. This band is in the full dual of $G$, and all its characters restrict to the same
character on $G^1$.
-/
def modulatedFrequencyBand (m : G →ₜ* ℝ≥0ˣ) (χ : PontryaginDual G) (α β : ℝ) :
    Set (PontryaginDual G) :=
  {ψ | ∃ t ∈ Icc α β, ∀ g, ψ g = χ g * Circle.exp (t * Real.log ((m g).val : ℝ))}

/-- Paper: Corollary 9.3.2.3(1), p. 425. A band consisting of exponent zero
contains exactly its starting character.
Deviation: Sanity check on the frequency band. -/
theorem modulatedFrequencyBand_zero (χ : PontryaginDual G) :
    modulatedFrequencyBand m χ 0 0 = {χ} := by
  ext ψ
  simp only [modulatedFrequencyBand, Icc_self, mem_singleton_iff, mem_ofPred_eq,
    exists_eq_left, zero_mul, Circle.exp_zero, mul_one]
  exact ⟨fun h ↦ ContinuousMonoidHom.ext h, fun h ↦ h ▸ fun _ ↦ rfl⟩

/-- Paper: Corollary 9.3.2.3(1), p. 425. Inclusion of circle characters
into complex quasi-characters identifies the band with the imaginary
norm twists of §3.1.1. -/
theorem mem_modulatedFrequencyBand_iff_normTwist (χ ψ : PontryaginDual G) (α β : ℝ) :
    let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    ψ ∈ modulatedFrequencyBand m χ α β ↔ ∃ t ∈ Icc α β,
      j.comp ψ = quasiCharacterNormTwist m.toMonoidHom m.continuous (j.comp χ) ((t : ℂ) * Complex.I) :=
  by
  intro j
  have key : ∀ (g : G) (t : ℝ), ((((m g).val : ℝ≥0) : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) =
      ((Circle.exp (t * Real.log ((m g).val : ℝ)) : Circle) : ℂ) := by
    intro g t
    have hpos : (0 : ℝ) < (((m g).val : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
      ← Complex.ofReal_log hpos.le, Circle.coe_exp]
    congr 1
    push_cast
    ring
  have hv : ∀ (c : QuasiCharacter G) (z : ℂ) (g : G),
      (quasiCharacterNormTwist m.toMonoidHom m.continuous c z) g =
        c g * ((((m g).val : ℝ≥0) : ℝ) : ℂ) ^ z := fun _ _ _ => rfl
  have hg : ∀ (t : ℝ), j.comp ψ = quasiCharacterNormTwist m.toMonoidHom m.continuous (j.comp χ)
      ((t : ℂ) * Complex.I) ↔ ∀ g, ψ g = χ g * Circle.exp (t * Real.log ((m g).val : ℝ)) := by
    intro t
    constructor
    · intro h g
      have := DFunLike.congr_fun h g
      rw [hv, key] at this
      apply Subtype.ext
      rw [Circle.coe_mul]
      exact this
    · intro h
      ext g
      rw [hv, key]
      have := congrArg (fun z : Circle => (z : ℂ)) (h g)
      rw [Circle.coe_mul] at this
      exact this
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, (hg t).2 h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, (hg t).1 h⟩

/-- Compact Fourier support is dense in the Schwartz topology on the positive
real group. In logarithmic frequency coordinates this is the usual density
of compactly supported Schwartz functions on the real line. -/
private theorem dense_bandlimited_profiles (η : Measure ℝ≥0ˣ) [η.IsHaarMeasure] :
    Dense {f : SchwartzBruhat ℝ≥0ˣ | HasCompactSupport (lcaFourier η f)} := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : LocallyCompactSpace ℝ≥0ˣ := positiveRealLogEquiv.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let R := exists_realPontryaginDualEquiv.choose
  let d : PontryaginDual ℝ≥0ˣ ≃ₜ* PontryaginDual (Multiplicative ℝ) :=
    { toFun := PontryaginDual.map (positiveRealLogEquiv.symm : Multiplicative ℝ →ₜ* ℝ≥0ˣ)
      invFun := PontryaginDual.map (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ)
      map_mul' := (PontryaginDual.map _).map_mul
      left_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (positiveRealLogEquiv.symm_apply_apply x)
      right_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (positiveRealLogEquiv.apply_symm_apply x)
      continuous_toFun := (PontryaginDual.map _).continuous
      continuous_invFun := (PontryaginDual.map _).continuous }
  let c := d.trans R.symm
  let U := (schwartzBruhat_realCoordinate_equiv c).choose
  have hU := (schwartzBruhat_realCoordinate_equiv c).choose_spec
  let F := (schwartzBruhat_fourier_equiv η).choose
  have hF := (schwartzBruhat_fourier_equiv η).choose_spec
  let L := U.trans F.symm
  have hd := L.surjective.denseRange.dense_image L.continuous
    (SchwartzMap.dense_hasCompactSupport (E := ℝ) (F := ℂ))
  apply hd.mono
  rintro _ ⟨f, hf, rfl⟩
  have he (χ) : lcaFourier η (L f) χ = f (c χ).toAdd :=
    ((hF (L f)).2 χ).symm.trans ((congrArg (fun v : SchwartzBruhat (PontryaginDual ℝ≥0ˣ) ↦ v χ)
      (F.apply_symm_apply (U f))).trans (hU f χ))
  change HasCompactSupport _
  rw [funext he]
  exact hf.comp_homeomorph (c.toHomeomorph.trans (Homeomorph.refl ℝ))

/-- A character times a pulled-back profile has Fourier support on the
corresponding translated line. On that line its transform is the transform
of the profile for the pushforward Haar measure. -/
private theorem support_fourier_character_profile (j : ℝ≥0ˣ →ₜ* G) (hj : RightInverse j m)
    (χ : PontryaginDual G) (f : ℝ≥0ˣ → ℂ) (hf : Continuous f) :
    support (lcaFourier μ (fun g ↦ (χ g : ℂ) * f (m g))) ⊆
      (fun ξ : PontryaginDual ℝ≥0ˣ ↦ χ * PontryaginDual.map m ξ) ''
        support (lcaFourier (μ.map m) f) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  intro γ hγ
  let δ := χ⁻¹ * γ
  let v (x : G) := f (m x) * star (δ x : ℂ)
  have hv (x) : (χ x : ℂ) * f (m x) * star (γ x : ℂ) = v x := by
    change _ = f (m x) * star (((χ x)⁻¹ * γ x : Circle) : ℂ)
    rw [Circle.coe_mul, Circle.coe_inv_eq_conj, ← Complex.star_def, star_mul, star_star]
    ring
  have hz : (∫ x, v x ∂μ) ≠ 0 := by
    change (∫ x, (χ x : ℂ) * f (m x) * star (γ x : ℂ) ∂μ) ≠ 0 at hγ
    simpa only [hv] using hγ
  have hk (k : m.toMonoidHom.ker) : δ (k : G) = 1 := by
    have heq (x) : v ((k : G) * x) = v x * star (δ (k : G) : ℂ) := by
      simp [v, map_mul, show m k = 1 from k.property, Circle.coe_mul, mul_comm, mul_left_comm]
    have hi := integral_mul_left_eq_self v (k : G) (μ := μ)
    simp_rw [heq, integral_mul_const] at hi
    have h1 := mul_left_cancel₀ hz (hi.trans (mul_one _).symm)
    exact Circle.coe_eq_one.mp (by simpa only [star_star, star_one] using congrArg star h1)
  let ξ := PontryaginDual.map j δ
  have hj' (x) : δ x = ξ (m x) := by
    have h : x / j (m x) ∈ m.toMonoidHom.ker := by change m (x / j (m x)) = 1; rw [map_div, hj, div_self']
    exact div_eq_one.mp ((map_div δ ..).symm.trans (hk ⟨_, h⟩))
  refine ⟨ξ, ?_, ?_⟩
  · change (∫ t, f t * star (ξ t : ℂ) ∂(μ.map m)) ≠ 0
    have hct : Continuous (fun t ↦ f t * star (ξ t : ℂ)) :=
      hf.mul (continuous_subtype_val.comp ξ.continuous).star
    rw [integral_map (φ := (m : G → ℝ≥0ˣ)) m.continuous.measurable.aemeasurable hct.aestronglyMeasurable]
    simpa only [v, hj'] using hz
  · exact PontryaginDual.ext fun x ↦ by
      change χ x * ξ (m x) = γ x
      rw [← hj']; exact mul_inv_cancel_left _ _

/-- Character multiplication of a profile on the modulus is a continuous
linear map on Schwartz–Bruhat spaces. -/
private theorem exists_character_profile_lift (hm : IsModulation m)
    (j : ℝ≥0ˣ →ₜ* G) (hj : RightInverse j m) (χ : PontryaginDual G) :
    ∃ L : SchwartzBruhat ℝ≥0ˣ →L[ℂ] SchwartzBruhat G,
      ∀ f x, L f x = (χ x : ℂ) * f (m x) := by
  let K := m.toMonoidHom.ker
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let κ : Measure K := Measure.haar
  have h := schwartzBruhat_positiveReal_isotype_equiv m hm κ j hj (1 : PontryaginDual K)
  let L := h.choose
  have hval := h.choose_spec.choose_spec.1
  let M := (exists_schwartzBruhat_characterEquiv χ).choose
  have hM := (exists_schwartzBruhat_characterEquiv χ).choose_spec
  have hval' (f : SchwartzBruhat ℝ≥0ˣ) (k : K) (t : ℝ≥0ˣ) :
      L f ((k : G) * j t) = f t := (hval f k t).trans (by change star (1 : ℂ) * f t = f t; rw [star_one, one_mul])
  refine ⟨M.toContinuousLinearMap.comp L, fun f x ↦ (hM (L f) x).trans (congrArg ((χ x : ℂ) * ·) ?_)⟩
  let k : K := ⟨x / j (m x), by change m (x / j (m x)) = 1; rw [map_div, hj, div_self']⟩
  exact (congrArg (fun z : G ↦ L f z) (div_mul_cancel x (j (m x)))).symm.trans (hval' f k (m x))

open scoped Pointwise in
/-- The restrictions of group characters span a dense subspace of the
continuous functions on any compact subset. -/
private theorem dense_characters_on_compact (K : Set G) [CompactSpace K]
    (r : PontryaginDual G →* C(K, ℂ)) (hr : ∀ χ x, r χ x = (χ x.val : ℂ)) :
    (Submodule.span ℂ (range r)).topologicalClosure = ⊤ := by
  let S := MonoidHom.mrange r
  let A := StarAlgebra.adjoin ℂ (S : Set C(K, ℂ))
  have hstar : star (S : Set C(K, ℂ)) ⊆ S := by
    rw [Set.star_subset]
    rintro _ ⟨ψ, rfl⟩
    exact ⟨ψ⁻¹, ContinuousMap.ext fun x ↦ (hr _ x).trans
      ((Circle.coe_inv_eq_conj (ψ x.val)).trans (congrArg star (hr ψ x).symm))⟩
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one (div_ne_one.mpr (Subtype.val_injective.ne hxy))
    refine ⟨_, ⟨r ψ, StarAlgebra.subset_adjoin ℂ (S : Set C(K, ℂ)) ⟨ψ, rfl⟩, rfl⟩, ?_⟩
    change r ψ x ≠ r ψ y
    rw [hr, hr, Ne, Circle.coe_inj]
    exact fun h ↦ hψ ((map_div ψ _ _).trans (div_eq_one.mpr h))
  have hspan : A.toSubalgebra.toSubmodule = Submodule.span ℂ (range r) := by
    rw [StarAlgebra.adjoin_eq_span, Set.union_eq_left.mpr hstar, S.closure_eq]
    rfl
  rw [← hspan]
  exact congrArg (fun A : StarSubalgebra ℂ C(K, ℂ) ↦ A.toSubalgebra.toSubmodule)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep)

/-- Finite character polynomials lift log profiles continuously to the group
and preserve compact Fourier support. -/
private theorem polynomial_profile_lift (hm : IsModulation m)
    (j : ℝ≥0ˣ →ₜ* G) (hj : RightInverse j m) (K : Set G) [CompactSpace K]
    (r : PontryaginDual G →* C(K, ℂ)) (hr : ∀ χ x, r χ x = (χ x.val : ℂ))
    (p : C(K, ℂ)) (hp : p ∈ Submodule.span ℂ (range r)) :
    ∃ L : SchwartzBruhat ℝ≥0ˣ →L[ℂ] SchwartzBruhat G,
      (∀ f (x : K), L f x.val = p x * f (m x.val)) ∧
      (∀ (f : SchwartzBruhat ℝ≥0ˣ) x, f (m x) = 0 → L f x = 0) ∧
      ∀ (f : SchwartzBruhat ℝ≥0ˣ), HasCompactSupport (lcaFourier (μ.map m) f) → HasCompactSupport (lcaFourier μ (L f)) := by
  classical
  let : ContinuousSMul ℂ (SchwartzBruhat G) := (withGeneratingSeminorms_spec _ _).continuousSMul
  let A (χ : PontryaginDual G) := (exists_character_profile_lift m hm j hj χ).choose
  have hA (χ : PontryaginDual G) (f : SchwartzBruhat ℝ≥0ˣ) (x : G) :
      A χ f x = (χ x : ℂ) * f (m x) := (exists_character_profile_lift m hm j hj χ).choose_spec f x
  let c := (Finsupp.mem_span_range_iff_exists_finsupp.mp hp).choose
  have hcp : (∑ χ ∈ c.support, c χ • r χ) = p :=
    (Finsupp.mem_span_range_iff_exists_finsupp.mp hp).choose_spec
  let L := ∑ χ ∈ c.support, c χ • A χ
  let ev (x : G) : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let eval (f : SchwartzBruhat ℝ≥0ˣ) : (SchwartzBruhat ℝ≥0ˣ →L[ℂ] SchwartzBruhat G) →ₗ[ℂ] SchwartzBruhat G :=
    { toFun := fun B ↦ B f
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hsum (f : SchwartzBruhat ℝ≥0ˣ) (x : G) :
      L f x = (∑ χ ∈ c.support, c χ * (χ x : ℂ)) * f (m x) := by
    let π := (ev x).comp (eval f)
    have hterm (χ) : π (c χ • A χ) = (c χ * (χ x : ℂ)) * f (m x) :=
      (congrArg (c χ * ·) (hA χ f x)).trans (mul_assoc (c χ) (χ x : ℂ) (f (m x))).symm
    exact (map_sum π (fun χ ↦ c χ • A χ) c.support).trans ((Finset.sum_congr rfl
      (fun χ _ ↦ hterm χ)).trans (Finset.sum_mul c.support (fun χ ↦ c χ * (χ x : ℂ)) (f (m x))).symm)
  refine ⟨L, fun f x ↦ (hsum f x.val).trans ?_, fun f x hx ↦ (hsum f x).trans (by rw [hx, mul_zero]), ?_⟩
  · have hcx := congrArg (fun g : C(K, ℂ) ↦ g x) hcp
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, hr, smul_eq_mul] at hcx
    exact congrArg (· * f (m x.val)) hcx
  · intro f hf
    let F := (schwartzBruhat_fourier_equiv μ).choose
    have hF (u : SchwartzBruhat G) : (F u : PontryaginDual G → ℂ) = lcaFourier μ u :=
      funext ((schwartzBruhat_fourier_equiv μ).choose_spec u).2
    have hb (χ : PontryaginDual G) : HasCompactSupport (lcaFourier μ (A χ f)) := by
      apply HasCompactSupport.of_support_subset_isCompact (hf.image
        (f := fun ξ ↦ χ * PontryaginDual.map m ξ) (continuous_const.mul (PontryaginDual.map m).continuous))
      have hpt := funext (hA χ f)
      rw [hpt]
      exact (support_fourier_character_profile μ m j hj χ _ (continuous_schwartzBruhat f)).trans
        (image_mono (subset_tsupport _))
    let V := ((schwartzBruhatSubmodule (PontryaginDual G)).subtype.comp F.toLinearMap)
    have hV (u : SchwartzBruhat G) : V u = lcaFourier μ u := hF u
    let π := V.comp (eval f)
    have hsum : lcaFourier μ (L f) = ∑ χ ∈ c.support, π (c χ • A χ) :=
      (hV (L f)).symm.trans (map_sum π _ _)
    rw [hsum]
    have hterm (χ) : HasCompactSupport (π (c χ • A χ)) := by
      have hχ : π (c χ • A χ) = c χ • lcaFourier μ (A χ f) :=
        (map_smul π _ _).trans (congrArg (c χ • ·) (hV (A χ f)))
      rw [hχ]
      exact (hb χ).comp_left (show (c χ • (0 : ℂ)) = 0 from smul_zero _)
    have hs (s : Finset (PontryaginDual G)) : HasCompactSupport (∑ χ ∈ s, π (c χ • A χ)) := by
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.sum_empty] using (show HasCompactSupport (0 : PontryaginDual G → ℂ) by simp [HasCompactSupport])
      | insert i s hi ih => rw [Finset.sum_insert hi]; exact (hterm i).add ih
    exact hs _

/-- Uniformly approximating two kernels on a common compact support
controls the difference of their integrated operators. -/
private theorem compact_kernel_integral_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (T : G → E →L[ℂ] E) (hT : ∀ u, Continuous (fun g ↦ T g u))
    {K : Set G} (hK : IsCompact K) {c ε : ℝ} (hε : 0 ≤ ε) (hB : ∀ x ∈ K, ‖T x‖ ≤ c)
    {v k : G → ℂ} (hv : Continuous v) (hk : Continuous k)
    (hvo : ∀ x ∉ K, v x = 0) (hko : ∀ x ∉ K, k x = 0) (hd : ∀ x ∈ K, ‖v x - k x‖ ≤ ε) (u : E) :
    ‖(∫ x, v x • T x u ∂μ) - ∫ x, k x • T x u ∂μ‖ ≤ (ε * (c * μ.real K)) * ‖u‖ := by
  let D (x : G) := (v x - k x) • T x u
  have hs (f : G → ℂ) (hf : Continuous f) (ho : ∀ x ∉ K, f x = 0) :
      Integrable (fun x ↦ f x • T x u) μ :=
    let hc := HasCompactSupport.intro hK ho
    integrable_smul_orbit μ (hf.integrable_of_hasCompactSupport hc) hc (hT u)
  have he : (∫ x, v x • T x u ∂μ) - (∫ x, k x • T x u ∂μ) = ∫ x in K, D x ∂μ := by
    refine (integral_sub (hs v hv hvo) (hs k hk hko)).symm.trans ?_
    simp only [D, sub_smul]
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by simp [hvo x hx, hko x hx]
  rw [he]
  have hb {x} (hx : x ∈ K) : ‖D x‖ ≤ ε * (c * ‖u‖) := by
    change ‖(v x - k x) • T x u‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul (hd x hx) (((T x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hB x hx) (norm_nonneg _))) (norm_nonneg _) hε
  exact (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top (fun x hx ↦ hb hx)).trans_eq (by ring)

/-- A smooth log profile equal to one on a given compact set vanishes outside
a larger compact set by properness of the modulation. -/
private theorem exists_profile_plateau (hm : IsModulation m) {S : Set G} (hS : IsCompact S) :
    ∃ (f : SchwartzBruhat ℝ≥0ˣ) (K : Set G), IsCompact K ∧ S ⊆ K ∧
      (∀ x ∈ S, f (m x) = 1) ∧ (∀ x ∉ K, f (m x) = 0) ∧ ∀ x, ‖f (m x)‖ ≤ 1 := by
  let e : ℝ≥0ˣ ≃ₜ ℝ := positiveRealLogEquiv.toHomeomorph
  let t (x : G) := e (m x)
  have ht : Continuous t := e.continuous.comp m.continuous
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn ht.continuousOn
  let r := max M 0 + 1
  let B : ContDiffBump (0 : ℝ) := ⟨r, r + 1, by dsimp [r]; positivity, by linarith⟩
  let b : 𝓢(ℝ, ℂ) := (B.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp B.contDiff)
  let U := (schwartzBruhat_realCoordinate_equiv positiveRealLogEquiv).choose
  have hU := (schwartzBruhat_realCoordinate_equiv positiveRealLogEquiv).choose_spec
  let K := m ⁻¹' (e ⁻¹' Metric.closedBall 0 (r + 1))
  have hK : IsCompact K := hm.1.isCompact_preimage
    (e.isCompact_preimage.mpr (isCompact_closedBall _ _))
  have hin {x} (hx : x ∈ S) : dist (t x) 0 ≤ r :=
    ((dist_zero_right (t x)).trans_le (hM x hx)).trans (by dsimp [r]; linarith [le_max_left M 0])
  have hval (x) : U b (m x) = (B (t x) : ℂ) := hU b (m x)
  refine ⟨U b, K, hK, fun x hx ↦ (hin hx).trans (by linarith : r ≤ r + 1), fun x hx ↦ ?_,
    fun x hx ↦ ?_, fun x ↦ ?_⟩
  · rw [hval, B.one_of_mem_closedBall (hin hx), Complex.ofReal_one]
  · rw [hval, B.zero_of_le_dist (le_of_not_ge hx), Complex.ofReal_zero]
  · rw [hval, Complex.norm_real, Real.norm_of_nonneg B.nonneg]
    exact B.le_one

/-- Approximate a compact kernel first by a character polynomial times a
smooth log cutoff, then approximate the cutoff by band-limited log profiles
in the Schwartz topology. -/
private theorem approximate_compact_kernel_by_profiles {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (hm : IsModulation m) (j : ℝ≥0ˣ →ₜ* G) (hj : RightInverse j m)
    (T : G → E →L[ℂ] E) (hT : ∀ u, Continuous (fun g ↦ T g u)) (w : G → ℝ)
    (hw : Continuous w) (hB : ∀ g, ‖T g‖ ≤ w g)
    (A : SchwartzBruhat G →L[ℂ] (E →L[ℂ] E))
    (hA : ∀ (f : SchwartzBruhat G), HasCompactSupport (f : G → ℂ) →
      ∀ u, A f u = ∫ g, f g • T g u ∂μ)
    {k : G → ℂ} (hc : Continuous k) (hkc : HasCompactSupport k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : SchwartzBruhat G, HasCompactSupport (lcaFourier μ f) ∧
      ∀ u, ‖A f u - ∫ g, k g • T g u ∂μ‖ ≤ δ * ‖u‖ := by
  classical
  let H := exists_profile_plateau m hm hkc
  let b := H.choose
  let K := H.choose_spec.choose
  have hK : IsCompact K := H.choose_spec.choose_spec.1
  have hsub : tsupport k ⊆ K := H.choose_spec.choose_spec.2.1
  have hone : ∀ x ∈ tsupport k, b (m x) = 1 := H.choose_spec.choose_spec.2.2.1
  have hout : ∀ x ∉ K, b (m x) = 0 := H.choose_spec.choose_spec.2.2.2.1
  have hle : ∀ x, ‖b (m x)‖ ≤ 1 := H.choose_spec.choose_spec.2.2.2.2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let r : PontryaginDual G →* C(K, ℂ) :=
    { toFun := fun χ ↦ ⟨fun x ↦ (χ x.val : ℂ), continuous_subtype_val.comp (χ.continuous.comp continuous_subtype_val)⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  let cb := hK.exists_bound_of_continuousOn hw.continuousOn
  let C := cb.choose
  have hC := cb.choose_spec
  let c := max C 0
  have hBound {x} (hx : x ∈ K) : ‖T x‖ ≤ c :=
    (hB x).trans ((le_abs_self _).trans ((hC x hx).trans (le_max_left _ _)))
  let ε := δ / (2 * (1 + c * μ.real K))
  have hc0 : 0 ≤ c := le_max_right _ _
  have hm0 : 0 ≤ μ.real K := measureReal_nonneg
  have hden : 0 < 1 + c * μ.real K := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hc0 hm0)
  have hε : 0 < ε := div_pos hδ (mul_pos (by norm_num) hden)
  let g : C(K, ℂ) := ⟨fun x ↦ k x.val, hc.comp continuous_subtype_val⟩
  have hd : Dense ((Submodule.span ℂ (range r) : Submodule ℂ C(K, ℂ)) : Set C(K, ℂ)) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, dense_characters_on_compact K r (fun _ _ ↦ rfl)]
    rfl
  let pp := hd.exists_mem_open (Metric.isOpen_ball (x := g) (ε := ε))
    ⟨g, Metric.mem_ball_self hε⟩
  let p := pp.choose
  have hp := pp.choose_spec.1
  have hdist := pp.choose_spec.2
  let hl := polynomial_profile_lift μ m hm j hj K r (fun _ _ ↦ rfl) p hp
  let L := hl.choose
  have hL := hl.choose_spec
  let η := μ.map m
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : η.IsHaarMeasure := Measure.isHaarMeasure_map μ m.toMonoidHom m.continuous hj.surjective
    (isProperMap_iff_tendsto_cocompact.mp hm.1).2
  let F := A.comp L
  have hBall : IsOpen {z | ‖F z - F b‖ < δ / 2} :=
    isOpen_lt ((F.continuous.sub continuous_const).norm) continuous_const
  let vv := (dense_bandlimited_profiles η).exists_mem_open hBall
    ⟨b, by change ‖F b - F b‖ < δ / 2; rw [sub_self, norm_zero]; exact half_pos hδ⟩
  let v := vv.choose
  have hv := vv.choose_spec.1
  have hclose := vv.choose_spec.2
  refine ⟨L v, hL.2.2 v hv, fun u ↦ ?_⟩
  have ho {x} (hx : x ∉ K) : L b x = 0 := hL.2.1 b x (hout x hx)
  have hkout {x} (hx : x ∉ K) : k x = 0 := image_eq_zero_of_notMem_tsupport (fun hy ↦ hx (hsub hy))
  have hpb : HasCompactSupport (L b : G → ℂ) := HasCompactSupport.intro hK fun _ ↦ ho
  have hdiff {x} (hx : x ∈ K) : ‖L b x - k x‖ ≤ ε := by
    have hpg : ‖p ⟨x, hx⟩ - k x‖ ≤ ε := (ContinuousMap.norm_coe_le_norm (p - g) ⟨x, hx⟩).trans
      (le_of_lt (show ‖p - g‖ < ε from (dist_eq_norm p g) ▸ (Metric.mem_ball.mp hdist)))
    have hk (x) : k x * b (m x) = k x := by
      by_cases hx : x ∈ tsupport k
      · rw [hone x hx, mul_one]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    apply le_of_eq_of_le (congrArg norm (congrArg₂ (· - ·) (hL.1 b ⟨x, hx⟩) (hk x).symm))
    change ‖p ⟨x, hx⟩ * b (m x) - k x * b (m x)‖ ≤ _
    rw [← sub_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hle x) (norm_nonneg _)).trans ((mul_one _).le.trans hpg)
  have hUb := hA (L b) hpb u
  have hΔ : ‖A (L b) u - ∫ g, k g • T g u ∂μ‖ ≤ δ / 2 * ‖u‖ := by
    rw [hUb]
    apply (compact_kernel_integral_sub_le μ T hT hK hε.le (fun _ hx ↦ hBound hx)
      (continuous_schwartzBruhat _) hc (fun _ hx ↦ ho hx) (fun _ hx ↦ hkout hx)
      (fun _ hx ↦ hdiff hx) u).trans
    have hcoeff : ε * (c * μ.real K) ≤ δ / 2 := by
      calc
        _ ≤ ε * (1 + c * μ.real K) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hε.le
        _ = _ := by
          change δ / (2 * (1 + c * μ.real K)) * (1 + c * μ.real K) = δ / 2
          rw [← div_div, div_mul_cancel₀ _ hden.ne']
    exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg u)
  have he := (F v - F b).le_opNorm u
  change ‖A (L v) u - A (L b) u‖ ≤ ‖F v - F b‖ * ‖u‖ at he
  have hb := he.trans (mul_le_mul_of_nonneg_right (le_of_lt hclose) (norm_nonneg u))
  exact (norm_sub_le_norm_sub_add_norm_sub _ (A (L b) u) _).trans
    ((add_le_add hb hΔ).trans_eq (by rw [← add_mul, add_halves]))

/-- Nonnegative continuous unit-mass kernels can be supported in an arbitrary
shrinking identity neighborhood basis on which a continuous weight is small. -/
private theorem exists_shrinking_mass_one (w : G → ℝ) (hw : Continuous w) (hw₁ : w 1 = 1) :
    ∃ k : ℕ → G → ℝ, (∀ n, Continuous (k n) ∧ HasCompactSupport (k n) ∧
      (∀ x, 0 ≤ k n x) ∧ (∫ x, k n x ∂μ) = 1 ∧
      ∀ x ∈ tsupport (k n), w x < 3 / 2) ∧
      ∀ U ∈ 𝓝 (1 : G), ∀ᶠ n in atTop, tsupport (k n) ⊆ U := by
  obtain ⟨B, hB⟩ := (𝓝 (1 : G)).exists_antitone_basis
  have hV : {x | w x < 3 / 2} ∈ 𝓝 (1 : G) :=
    (isOpen_lt hw continuous_const).mem_nhds (by simp [hw₁]; norm_num)
  have h (n : ℕ) : ∃ f : G → ℝ, Continuous f ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x) ∧ (∫ x, f x ∂μ) = 1 ∧ tsupport f ⊆ B n ∩ {x | w x < 3 / 2} := by
    obtain ⟨U, hU, ho, h₁⟩ := mem_nhds_iff.mp (inter_mem (hB.mem n) hV)
    obtain ⟨f, he, hK, hsub, hval⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
      (isCompact_singleton (x := (1 : G))) ho (singleton_subset_iff.mpr h₁)
    let c := ∫ x, f x ∂μ
    have hc : 0 < c := f.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero hK
      (fun x ↦ (hval x).1) ((he (mem_singleton _)).trans_ne one_ne_zero)
    let k := fun x ↦ c⁻¹ * f x
    have hk : tsupport k ⊆ tsupport (f : G → ℝ) := tsupport_mul_subset_right
    refine ⟨k, continuous_const.mul f.continuous, hK.of_isClosed_subset (isClosed_tsupport _) hk,
      fun x ↦ mul_nonneg (inv_nonneg.mpr hc.le) (hval x).1, ?_, hk.trans (hsub.trans hU)⟩
    rw [show (∫ x, k x ∂μ) = c⁻¹ * c from integral_const_mul .., inv_mul_cancel₀ hc.ne']
  choose k hc hs hpos hi hk using h
  exact ⟨k, fun n ↦ ⟨hc n, hs n, hpos n, hi n, fun x hx ↦ ((hk n hx).2)⟩,
    fun U hU ↦ (hB.eventually_subset hU).mono fun n hn ↦ (hk n).trans (inter_subset_left.trans hn)⟩

/-- Operator-norm approximation of compact kernels transfers a shrinking
unit-mass family to a uniformly bounded strong approximate identity. -/
private theorem approximate_identity_of_kernel_approx {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : V → E →L[ℂ] E) (P : V → Prop)
    (T : G → E →L[ℂ] E) (hT : ∀ u, Continuous (fun g ↦ T g u)) (h₁ : ∀ u, T 1 u = u)
    (w : G → ℝ) (hw : Continuous w) (hw₁ : w 1 = 1) (hB : ∀ g, ‖T g‖ ≤ w g)
    (happrox : ∀ (k : G → ℂ), Continuous k → HasCompactSupport k → ∀ δ : ℝ, 0 < δ →
      ∃ v, P v ∧ ∀ u, ‖A v u - ∫ g, k g • T g u ∂μ‖ ≤ δ * ‖u‖) :
    ∃ v : ℕ → V, (∀ n, ‖A (v n)‖ ≤ 2 ∧ P (v n)) ∧
      ∀ u, Tendsto (fun n ↦ A (v n) u) atTop (𝓝 u) := by
  obtain ⟨k, hk, hshrink⟩ := exists_shrinking_mass_one μ w hw hw₁
  let δ (n : ℕ) := ((n : ℝ) + 3)⁻¹
  have hδ (n) : 0 < δ n := by dsimp [δ]; positivity
  have hδ' (n) : δ n ≤ 1 / 2 := by
    dsimp [δ]; rw [← one_div]; apply one_div_le_one_div_of_le (by norm_num); linarith [Nat.cast_nonneg (α := ℝ) n]
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  let I (n : ℕ) (u : E) := ∫ g, (k n g : ℂ) • T g u ∂μ
  have hi (n : ℕ) (u : E) : Integrable (fun g ↦ (k n g : ℂ) • T g u) μ :=
    integrable_smul_orbit μ ((Complex.continuous_ofReal.comp (hk n).1).integrable_of_hasCompactSupport
      ((hk n).2.1.comp_left Complex.ofReal_zero)) ((hk n).2.1.comp_left Complex.ofReal_zero) (hT u)
  choose v hv he using fun n ↦ happrox (fun g ↦ (k n g : ℂ))
    (Complex.continuous_ofReal.comp (hk n).1) ((hk n).2.1.comp_left Complex.ofReal_zero) (δ n) (hδ n)
  have hiBound (n : ℕ) (u : E) : ‖I n u‖ ≤ 3 / 2 * ‖u‖ := by
    calc
      _ ≤ ∫ g, k n g * (3 / 2 * ‖u‖) ∂μ := by
        apply (norm_integral_le_integral_norm _).trans
        apply integral_mono (hi n u).norm (((hk n).1.integrable_of_hasCompactSupport (hk n).2.1).mul_const _)
        intro g
        change ‖(k n g : ℂ) • T g u‖ ≤ _
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ((hk n).2.2.1 g)]
        by_cases hg : k n g = 0
        · simp [hg]
        · exact mul_le_mul_of_nonneg_left (((T g).le_opNorm u).trans
            (mul_le_mul_of_nonneg_right ((hB g).trans ((hk n).2.2.2.2 g (subset_tsupport _ hg)).le)
              (norm_nonneg _))) ((hk n).2.2.1 _)
      _ = _ := by rw [integral_mul_const, (hk n).2.2.2.1, one_mul]
  refine ⟨v, fun n ↦ ⟨(A (v n)).opNorm_le_bound (by norm_num) (fun u ↦ ?_), hv n⟩, fun u ↦ ?_⟩
  · have hh := norm_le_norm_sub_add (A (v n) u) (I n u)
    have := he n u; change ‖A (v n) u - I n u‖ ≤ _ at this
    nlinarith [hiBound n u, mul_le_mul_of_nonneg_right (hδ' n) (norm_nonneg u)]
  · have ht : Tendsto (fun n ↦ I n u) atTop (𝓝 u) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hne : {g | ‖T g u - u‖ < ε / 2} ∈ 𝓝 (1 : G) :=
        (isOpen_lt (((hT u).sub continuous_const).norm) continuous_const).mem_nhds
          (by change ‖T 1 u - u‖ < ε / 2; rw [h₁, sub_self, norm_zero]; exact half_pos hε)
      filter_upwards [hshrink _ hne] with n hn
      have hki := (hk n).1.integrable_of_hasCompactSupport (μ := μ) (hk n).2.1
      have hconst : (∫ g, (k n g : ℂ) • u ∂μ) = u := by
        rw [integral_smul_const, integral_complex_ofReal, (hk n).2.2.2.1, Complex.ofReal_one, one_smul]
      rw [dist_eq_norm, show I n u - u = ∫ g, (k n g : ℂ) • (T g u - u) ∂μ from by
        conv_lhs => rhs; rw [← hconst]
        change (∫ g, _ ∂μ) - (∫ g, _ ∂μ) = _
        refine (integral_sub (hi n u) (hki.ofReal.smul_const u)).symm.trans ?_
        exact integral_congr_ae (.of_forall fun g ↦ (smul_sub (k n g : ℂ) (T g u) u).symm)]
      apply lt_of_le_of_lt ((norm_integral_le_integral_norm _).trans ?_) (half_lt_self hε)
      calc
        _ ≤ ∫ g, k n g * (ε / 2) ∂μ := by
          apply integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) (hki.mul_const _)
          refine .of_forall fun g ↦ ?_
          change ‖(k n g : ℂ) • (T g u - u)‖ ≤ _
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ((hk n).2.2.1 g)]
          by_cases hg : k n g = 0
          · simp [hg]
          · exact mul_le_mul_of_nonneg_left (le_of_lt (hn (subset_tsupport _ hg))) ((hk n).2.2.1 _)
        _ = _ := by rw [integral_mul_const, (hk n).2.2.2.1, one_mul]
    apply ht.congr_dist
    have hd (n : ℕ) : dist (I n u) (A (v n) u) ≤ δ n * ‖u‖ := by
      simpa only [dist_comm (I n u), dist_eq_norm] using he n u
    apply squeeze_zero (fun _ ↦ dist_nonneg) hd
    simpa using hδlim.mul_const ‖u‖

/-- Evaluation of the inverse singleton twist divides by the endpoint character. -/
private theorem inverse_singleton_twist_value (b : ℝ)
    (e : ModulatedExponentialDecay m {b} ≃L[ℂ] SchwartzBruhat G)
    (he : ∀ v, (e v : G → ℂ) = modulationWeight m b v.val)
    (f : SchwartzBruhat G) (g : G) :
    f g * (Real.exp (b * Real.log ((m g).val : ℝ)) : ℂ)⁻¹ = (e.symm f).val g := by
  let d := Real.exp (b * Real.log ((m g).val : ℝ))
  have hval := (congrArg (fun z : SchwartzBruhat G ↦ z g) (e.apply_symm_apply f)).symm.trans (congrFun (he (e.symm f)) g)
  change f g = ((((m g).val : ℝ) ^ b : ℝ) : ℂ) * (e.symm f).val g at hval
  have hpow : (((m g).val : ℝ) ^ b) = Real.exp (b * Real.log ((m g).val : ℝ)) :=
    (Real.rpow_def_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)) b).trans
      (congrArg Real.exp (mul_comm _ _))
  have hval' : f g = (d : ℂ) * (e.symm f).val g := hval.trans
    (congrArg (fun r : ℝ ↦ (r : ℂ) * (e.symm f).val g) hpow)
  have hne : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  let y := (e.symm f).val g
  have cancel (a z : ℂ) (ha : a ≠ 0) : (a * z) * a⁻¹ = z :=
    (mul_right_comm a z a⁻¹).trans ((congrArg (· * z) (mul_inv_cancel₀ ha)).trans (one_mul z))
  exact (congrArg (· * (d : ℂ)⁻¹) hval').trans (cancel _ y hne)

/-- After the singleton twist the translation bound has polynomial growth
in the log coordinate. On kernel translates the normalizing factor cancels. -/
private theorem normalized_line_kernel_model (hm : IsModulation m) (hms : Surjective m)
    (b s : ℝ) (hs : 0 ≤ s) :
    let W := CompactIntervalSobolev μ (fun g ↦ Real.log ((m g).val : ℝ)) b b s
    let τ := hardySobolevTranslation μ m b b s le_rfl hs
    let A := (existsUnique_singletonDecay_lineAction μ m hm hms b s hs).exists.choose
    ∃ (e : ModulatedExponentialDecay m {b} ≃L[ℂ] SchwartzBruhat G) (T : G → W →L[ℂ] W)
      (w : G → ℝ), (∀ v, (e v : G → ℂ) = modulationWeight m b v.val) ∧
      (∀ u, Continuous (fun g ↦ T g u)) ∧ (∀ u, T 1 u = u) ∧ Continuous w ∧ w 1 = 1 ∧
      (∀ g, ‖T g‖ ≤ w g) ∧ (∀ k : m.toMonoidHom.ker, ‖τ k.val‖ ≤ 1) ∧
      (∀ (k : m.toMonoidHom.ker) g u, T (k.val * g) u = T g (τ k.val u)) ∧
      ∀ (f : SchwartzBruhat G) u, A (e.symm f) u = ∫ g, f g • T g u ∂μ := by
  intro W τ A
  let d (g : G) := Real.exp (b * Real.log ((m g).val : ℝ))
  let t (g : G) := Real.log ((m g).val : ℝ)
  let w (g : G) := (1 + |t g|) ^ (s / 2)
  let T (g : G) : W →L[ℂ] W := (d g : ℂ)⁻¹ • τ g
  let e := (modulatedExponentialDecay_singleton_schwartz m hm hms b).choose
  have he := (modulatedExponentialDecay_singleton_schwartz m hm hms b).choose_spec
  have htc : Continuous t := continuous_logModule' m
  have hw : Continuous w := (continuous_const.add htc.abs).rpow_const
    fun x ↦ Or.inl (ne_of_gt (by positivity : 0 < 1 + |t x|))
  have hw₁ : w 1 = 1 := by simp [w, t]
  have hd : Continuous (fun g ↦ (d g : ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul htc))).inv₀
      fun g ↦ Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hT (u : W) : Continuous (fun g ↦ T g u) := hd.smul
    ((exists_hardySobolevTranslation μ m b b s le_rfl hs).choose_spec.2.comp (Continuous.prodMk_left u))
  have hB (g) : ‖T g‖ ≤ w g := by
    have h0 := norm_hardySobolevTranslation_le μ m b b s le_rfl hs g
    rw [max_self] at h0
    change ‖(d g : ℂ)⁻¹ • τ g‖ ≤ _
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (inv_mul_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm (w g)] using h0)
  refine ⟨e, T, w, he, hT, fun u ↦ ?_, hw, hw₁, hB, fun k ↦ ?_, fun k g u ↦ ?_, fun f u ↦ ?_⟩
  · change ((d 1 : ℂ)⁻¹) • (τ 1 u) = u
    have h : d 1 = 1 := by simp [d]
    rw [h, Complex.ofReal_one, inv_one, one_smul, map_one τ]; rfl
  · have hk : m k.val = 1 := k.property
    have h := norm_hardySobolevTranslation_le μ m b b s le_rfl hs k.val
    simpa only [hk, Units.val_one, NNReal.coe_one, Real.log_one, mul_zero, Real.exp_zero, max_self, abs_zero, add_zero, Real.one_rpow, mul_one] using h
  · have hk : m k.val = 1 := k.property
    change ((d (k.val * g) : ℂ)⁻¹) • (τ (k.val * g) u) = (d g : ℂ)⁻¹ • τ g (τ k.val u)
    have hkd : d (k.val * g) = d g := by simp [d, hk]
    rw [hkd, mul_comm, map_mul, mul_apply_eq_comp]
  · have hP := (existsUnique_singletonDecay_lineAction μ m hm hms b s hs).exists.choose_spec.1 (e.symm f) u
    have hpt (g) : (f g * (d g : ℂ)⁻¹) = (e.symm f).val g := inverse_singleton_twist_value m b e he f g
    have hi : Integrable (fun g ↦ f g • T g u) μ := by
      refine ((integrable_schwartz_log_weight μ m f (s / 2)).mul_const ‖u‖).mono'
        ((continuous_schwartzBruhat f).smul (hT u)).aestronglyMeasurable (.of_forall fun g ↦ ?_)
      change ‖f g • T g u‖ ≤ (‖f g‖ * w g) * ‖u‖
      rw [norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (((T g).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hB g) (norm_nonneg _))) (norm_nonneg _)
    have heq (g) : f g • T g u = (e.symm f).val g • τ g u := by
      change f g • ((d g : ℂ)⁻¹ • τ g u) = _
      exact (mul_smul _ _ _).symm.trans (congrArg (· • τ g u) (hpt g))
    exact hP.unique (Eq.subst (motive := fun F ↦ HasPettisIntegral (.positive μ) F _)
      (funext heq) (Integrable.hasPettisIntegral hi))

/-- Paper: Lemma 9.3.2.1(4), p. 422. Band-limited convolutions approximate
the identity on the full b-line space with a uniform operator norm bound.
Deviation: The kernels may combine finitely many compact-group frequencies,
as needed for inputs with components in several isotypes.

Deviation: Lemma 9.3.2.1(4) claims strong approximation on the full space by individual
homogeneous kernels. We allow mixed compact frequencies for convergence on the full space.
-/
theorem exists_singletonDecay_approximation (hm : IsModulation m) (hms : Surjective m)
    (b s : ℝ) (hs : 0 ≤ s) :
    let A := (existsUnique_singletonDecay_lineAction μ m hm hms b s hs).exists.choose
    ∃ φ : ℕ → ModulatedExponentialDecay m {b},
      (∀ n, ‖A (φ n)‖ ≤ 2 ∧ HasCompactSupport (lcaFourier μ (modulationWeight m b (φ n).val))) ∧
      ∀ u, Tendsto (fun n ↦ A (φ n) u) atTop (𝓝 u) := by
  intro A
  let H := normalized_line_kernel_model μ m hm hms b s hs
  let e := H.choose
  let T := H.choose_spec.choose
  let w := H.choose_spec.choose_spec.choose
  have he := H.choose_spec.choose_spec.choose_spec.1
  have ht := H.choose_spec.choose_spec.choose_spec.2
  let B := A.comp e.symm.toContinuousLinearMap
  let j := (exists_fullModulationSection m hm hms).choose
  have hj := (exists_fullModulationSection m hm hms).choose_spec
  let P (f : SchwartzBruhat G) := HasCompactSupport (lcaFourier μ f)
  have happ := approximate_identity_of_kernel_approx μ B P T ht.1 ht.2.1 w ht.2.2.1 ht.2.2.2.1
    ht.2.2.2.2.1 (fun k hk hkc δ hδ ↦ approximate_compact_kernel_by_profiles μ m hm j hj T ht.1
      w ht.2.2.1 ht.2.2.2.2.1 B (fun f _ u ↦ ht.2.2.2.2.2.2.2 f u) hk hkc hδ)
  let f := happ.choose
  have h := happ.choose_spec
  refine ⟨fun n ↦ e.symm (f n), fun n ↦ ⟨(h.1 n).1, ?_⟩, h.2⟩
  have hval : modulationWeight m b (e.symm (f n)).val = (f n : G → ℂ) :=
    (he (e.symm (f n))).symm.trans (congrArg (fun z : SchwartzBruhat G ↦ (z : G → ℂ)) (e.apply_symm_apply _))
  exact Eq.subst (motive := fun v : G → ℂ ↦ HasCompactSupport (lcaFourier μ v)) hval.symm (h.1 n).2

open Classical in
/-- Fourier evaluation of the compact-kernel average retains exactly the
characters whose restriction gives the inverse translation eigencharacter. -/
private theorem fourier_isotypic_average (K : Subgroup G) [CompactSpace K]
    (κ : Measure K) [κ.IsHaarMeasure] [IsProbabilityMeasure κ] (ξ : PontryaginDual K)
    (P : SchwartzBruhat G →L[ℂ] SchwartzBruhat G)
    (hP : IsPettisIsotypicAverageOn κ univ ((schwartzBruhatTranslationAction (G := G)).comp K.subtype) ξ P)
    (f : SchwartzBruhat G) (γ : PontryaginDual G) :
    lcaFourier μ (P f) γ =
      if ξ = (γ⁻¹).comp ⟨K.subtype, continuous_subtype_val⟩ then lcaFourier μ f γ else 0 := by
  classical
  let F := (schwartzBruhat_fourier_equiv μ).choose
  let δ : SchwartzBruhat (PontryaginDual G) →L[ℂ] ℂ :=
    ⟨(LinearMap.proj γ).comp (schwartzBruhatSubmodule _).subtype, continuous_schwartzBruhat_eval γ⟩
  let d := δ.comp F.toContinuousLinearMap
  have hd (z : SchwartzBruhat G) : d z = lcaFourier μ z γ :=
    ((schwartzBruhat_fourier_equiv μ).choose_spec z).2 γ
  let η : PontryaginDual K := (γ⁻¹).comp ⟨K.subtype, continuous_subtype_val⟩
  have he (k : K) : d (star (ξ k : ℂ) • schwartzBruhatTranslationAction (G := G) k.val f) =
      (star (ξ k : ℂ) * (η k : ℂ)) * lcaFourier μ f γ := by
    rw [map_smul, hd, smul_eq_mul]
    have hz := funext fun x ↦ schwartzBruhatTranslationAction_apply k.val x f
    rw [hz, lcaFourier_translate, map_inv, mul_assoc]
    rfl
  have hi := pettisIntegral_univ_eval (hP f) d
  calc
    lcaFourier μ (P f) γ = d (P f) := (hd _).symm
    _ = ∫ k, (star (ξ k : ℂ) * (η k : ℂ)) * lcaFourier μ f γ ∂κ :=
      hi.trans (integral_congr_ae (.of_forall he))
    _ = _ := by
      rw [integral_mul_const, integral_character_pair κ ξ η]
      change (if ξ = η then (κ.real univ : ℂ) else 0) * lcaFourier μ f γ =
        (if ξ = η then lcaFourier μ f γ else 0)
      by_cases h : ξ = η <;> simp [h]

/-- The characters trivial on the compact kernel form an open real line. Its
coordinate is normalized so the character at t is exp(i t log m). -/
private theorem exists_frequency_line (hm : IsModulation m) (hms : Surjective m) :
    ∃ e : Multiplicative ℝ ≃ₜ* lcaAnnihilator m.toMonoidHom.ker,
      ∀ (t : ℝ) g, (e (Multiplicative.ofAdd t)).val g = Circle.exp (t * Real.log ((m g).val : ℝ)) := by
  obtain ⟨j, hj⟩ := exists_fullModulationSection m hm hms
  let ℓ := (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp m
  let i := j.comp (positiveRealLogEquiv.symm : Multiplicative ℝ →ₜ* ℝ≥0ˣ)
  have hli (t : Multiplicative ℝ) : ℓ (i t) = t := by
    change positiveRealLogEquiv (m (j _)) = t
    rw [hj]
    exact positiveRealLogEquiv.apply_symm_apply t
  let L := lcaAnnihilator m.toMonoidHom.ker
  let f (χ : PontryaginDual (Multiplicative ℝ)) : L := ⟨PontryaginDual.map ℓ χ,
    (mem_lcaAnnihilator_iff _ _).mpr fun k ↦ by
      change χ (positiveRealLogEquiv (m k)) = 1
      rw [show m k = 1 from k.property, map_one, map_one]⟩
  let d : PontryaginDual (Multiplicative ℝ) ≃ₜ* L :=
    { toFun := f
      invFun := fun ξ ↦ PontryaginDual.map i ξ.val
      map_mul' := fun χ ψ ↦ Subtype.ext ((PontryaginDual.map ℓ).map_mul χ ψ)
      left_inv := fun χ ↦ PontryaginDual.ext fun t ↦ congrArg χ (hli t)
      right_inv := fun ξ ↦ Subtype.ext (PontryaginDual.ext fun g ↦ by
        have hk : g / i (ℓ g) ∈ m.toMonoidHom.ker := by
          change m (g / j (positiveRealLogEquiv.symm (positiveRealLogEquiv (m g)))) = 1
          rw [map_div, hj, positiveRealLogEquiv.symm_apply_apply, div_self']
        have h := (mem_lcaAnnihilator_iff _ _).mp ξ.property ⟨_, hk⟩
        exact ((div_eq_one.mp ((map_div ξ.val _ _).symm.trans h))).symm)
      continuous_toFun := (PontryaginDual.map ℓ).continuous.subtype_mk _
      continuous_invFun := (PontryaginDual.map i).continuous.comp continuous_subtype_val }
  obtain ⟨R, hR⟩ := exists_realPontryaginDualEquiv
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  let scale : Multiplicative ℝ ≃ₜ* Multiplicative ℝ :=
    ContinuousMulEquiv.mk' (show ℝ ≃ₜ ℝ from Homeomorph.mulLeft₀ c⁻¹ (inv_ne_zero hc)) fun x y ↦ mul_add _ x.toAdd y.toAdd
  refine ⟨scale.trans (R.trans d), fun t g ↦ ?_⟩
  change R (Multiplicative.ofAdd (c⁻¹ * t)) (ℓ g) = _
  rw [show ℓ g = Multiplicative.ofAdd (Real.log ((m g).val : ℝ)) from
    congrArg Multiplicative.ofAdd (positiveRealLogEquiv_apply (m g)), hR]
  congr 1
  change c * (c⁻¹ * t * _) = _
  rw [mul_assoc c⁻¹, mul_inv_cancel_left₀ hc]

/-- The annihilator of a surjective modulation's kernel is a real frequency line.
The character at `t` evaluates to `exp(i t log m(g))`. -/
theorem exists_modulatedFrequencyLine (hm : IsModulation m) (hms : Surjective m) :
    ∃ e : Multiplicative ℝ ≃ₜ* lcaAnnihilator m.toMonoidHom.ker,
      ∀ (t : ℝ) g, (e (Multiplicative.ofAdd t)).val g = Circle.exp (t * Real.log ((m g).val : ℝ)) :=
  exists_frequency_line m hm hms

/-- A compact set of frequencies with a fixed restriction to the kernel
lies in a bounded interval in the corresponding real frequency line. -/
private theorem compact_subset_frequency_band (hm : IsModulation m) (hms : Surjective m)
    (χ : PontryaginDual G) (S : Set (PontryaginDual G)) (hS : IsCompact S)
    (hline : ∀ γ ∈ S, χ⁻¹ * γ ∈ lcaAnnihilator m.toMonoidHom.ker) :
    ∃ N : ℕ, S ⊆ modulatedFrequencyBand m χ (-(N : ℝ)) N := by
  let L := lcaAnnihilator m.toMonoidHom.ker
  let e := (exists_frequency_line m hm hms).choose
  have he := (exists_frequency_line m hm hms).choose_spec
  let q (γ : S) : L := ⟨χ⁻¹ * γ.val, hline γ.val γ.property⟩
  let t (γ : S) : ℝ := (e.symm (q γ)).toAdd
  have ht : Continuous t := e.symm.continuous.comp ((continuous_const.mul continuous_subtype_val).subtype_mk _)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn ht.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_ge C
  refine ⟨N, fun γ hγ ↦ ?_⟩
  let z : S := ⟨γ, hγ⟩
  have hn := abs_le.mp ((hC z (mem_univ _)).trans hN)
  refine ⟨t z, hn, fun g ↦ ?_⟩
  have hq := congrArg (fun a : L ↦ a.val g) (e.apply_symm_apply (q z))
  calc
    γ g = χ g * (q z).val g := (mul_inv_cancel_left (χ g) (γ g)).symm
    _ = _ := congrArg (χ g * ·) (hq.symm.trans (he (t z) g))

/-- Reindex a sequence with arbitrary finite bandwidths to fit the prescribed
integer bandwidth, starting once the first member fits. -/
private theorem exists_band_reindex (k : ℕ → ℕ) :
    ∃ r : ℕ → ℕ, Tendsto r atTop atTop ∧ ∀ n, k 0 ≤ n → k (r n) ≤ n := by
  let r n := Nat.findGreatest (fun i ↦ k i ≤ n) n
  refine ⟨r, tendsto_atTop.mpr (fun i ↦ ?_), fun n hn ↦ Nat.findGreatest_spec (P := fun i ↦ k i ≤ n) (Nat.zero_le n) hn⟩
  filter_upwards [eventually_ge_atTop (max i (k i))] with n hn
  exact Nat.le_findGreatest (P := fun l ↦ k l ≤ n) ((le_max_left ..).trans hn) ((le_max_right ..).trans hn)

/-- Averaging translated kernels is contractive on operators. On matching
input eigenvectors the character cancels and the average acts as the
original convolution. -/
private theorem averaged_action_on_isotype {K S E : Type*}
    [CommGroup K] [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S] [ContinuousSMul ℂ S]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (κ : Measure K) [IsProbabilityMeasure κ] (ξ : PontryaginDual K)
    (σ : K →* (S →L[ℂ] S)) (τ : K →* (E →L[ℂ] E)) (B : S →L[ℂ] (E →L[ℂ] E))
    (P : S →L[ℂ] S) (hP : IsPettisIsotypicAverageOn κ univ σ ξ P)
    (hc : ∀ u, Continuous (fun k ↦ τ k u)) (ht : ∀ k, ‖τ k‖ ≤ 1)
    (hB : ∀ k f u, B (σ k f) u = B f (τ k u)) (f : S) :
    ‖B (P f)‖ ≤ ‖B f‖ ∧ ∀ u ∈ actionIsotype τ ξ, B (P f) u = B f u := by
  let F (u : E) (k : K) := star (ξ k : ℂ) • B f (τ k u)
  have hi (u : E) : Integrable (F u) κ :=
    (((continuous_subtype_val.comp ξ.continuous).star.smul ((B f).continuous.comp (hc u))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have he (u : E) : B (P f) u = ∫ k, F u k ∂κ := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    intro δ
    let l := δ.comp ((ContinuousLinearMap.apply ℂ E u).comp B)
    have h := pettisIntegral_univ_eval (hP f) l
    refine h.trans ((integral_congr_ae (.of_forall fun k ↦ ?_)).trans (δ.integral_comp_comm (hi u)))
    change l (star (ξ k : ℂ) • σ k f) = δ (star (ξ k : ℂ) • B f (τ k u))
    rw [map_smul, map_smul]
    exact congrArg (fun z ↦ star (ξ k : ℂ) • δ z) (hB k f u)
  refine ⟨(B (P f)).opNorm_le_bound (norm_nonneg _) (fun u ↦ ?_), fun u hu ↦ ?_⟩
  · rw [he]
    have hnorm (k : K) : ‖F u k‖ ≤ ‖B f‖ * ‖u‖ := by
      change ‖star (ξ k : ℂ) • B f (τ k u)‖ ≤ _
      rw [norm_smul, norm_star, Circle.norm_coe, one_mul]
      exact ((B f).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (((τ k).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (ht k) (norm_nonneg _)).trans_eq (one_mul _)))
        (norm_nonneg _))
    exact (norm_integral_le_of_norm_le_const (.of_forall hnorm)).trans_eq (by simp)
  · have hval := (mem_actionIsotype τ ξ u).mp hu
    have hfixed (k : K) : F u k = B f u := by
      change star (ξ k : ℂ) • B f (τ k u) = B f u
      rw [hval, map_smul, smul_smul]
      have hunit : star (ξ k : ℂ) * (ξ k : ℂ) = 1 := by
        have h : star (ξ k : ℂ) = (ξ k : ℂ)⁻¹ := (Circle.coe_inv_eq_conj (ξ k)).symm
        exact (congrArg (· * (ξ k : ℂ)) h).trans (inv_mul_cancel₀ (Circle.coe_ne_zero _))
      rw [hunit, one_smul]
    rw [he, funext hfixed, integral_const]
    simp

/-- Translating a normalized kernel by a member of the compact kernel
translates the input of its integrated operator. -/
private theorem normalized_action_translate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (K : Subgroup G) (τ : K →* (E →L[ℂ] E))
    (T : G → E →L[ℂ] E) (hT : ∀ (k : K) g u, T (k.val * g) u = T g (τ k u))
    (B : SchwartzBruhat G →L[ℂ] (E →L[ℂ] E)) (hB : ∀ (f : SchwartzBruhat G) u,
      B f u = ∫ g, f g • T g u ∂μ) (k : K) (f : SchwartzBruhat G) (u : E) :
    B (schwartzBruhatTranslationAction (G := G) k.val f) u = B f (τ k u) := by
  let F (g : G) := schwartzBruhatTranslationAction (G := G) k.val f g • T g u
  refine (hB _ u).trans ((integral_mul_left_eq_self F k.val (μ := μ)).symm.trans
    ((integral_congr_ae (.of_forall fun g ↦ ?_)).trans (hB f (τ k u)).symm))
  change schwartzBruhatTranslationAction (G := G) k.val f (k.val * g) • T (k.val * g) u = _
  rw [schwartzBruhatTranslationAction_apply, inv_mul_cancel_left, hT]

open Classical in
/-- Projecting a Schwartz kernel with compact Fourier support onto a kernel
isotype cuts its spectrum down to a bounded segment of one frequency line. -/
private theorem projected_frequency_band (hm : IsModulation m) (hms : Surjective m)
    (χ : PontryaginDual G) (f z : SchwartzBruhat G) (hf : HasCompactSupport (lcaFourier μ f))
    (hF : ∀ γ, lcaFourier μ z γ =
      if (χ⁻¹).comp ⟨m.toMonoidHom.ker.subtype, continuous_subtype_val⟩ =
        (γ⁻¹).comp ⟨m.toMonoidHom.ker.subtype, continuous_subtype_val⟩ then lcaFourier μ f γ else 0) :
    ∃ N : ℕ, tsupport (lcaFourier μ z) ⊆ modulatedFrequencyBand m χ (-(N : ℝ)) N := by
  classical
  let K := m.toMonoidHom.ker
  let i : K →ₜ* G := ⟨K.subtype, continuous_subtype_val⟩
  let r (γ : PontryaginDual G) := PontryaginDual.map i γ⁻¹
  have hr : Continuous r := (PontryaginDual.map i).continuous.comp continuous_inv
  have h (γ) : lcaFourier μ z γ = if r χ = r γ then lcaFourier μ f γ else 0 := hF γ
  have hsub : support (lcaFourier μ z) ⊆ support (lcaFourier μ f) ∩ {γ | r χ = r γ} := by
    intro γ hγ
    by_cases he : r χ = r γ
    · exact ⟨fun hz ↦ hγ ((h γ).trans ((ite_eq_left he).trans hz)), he⟩
    · exact False.elim (hγ ((h γ).trans (ite_eq_right he)))
  have hc : tsupport (lcaFourier μ z) ⊆ tsupport (lcaFourier μ f) :=
    closure_mono (hsub.trans inter_subset_left)
  have hl := closure_minimal (hsub.trans inter_subset_right) (isClosed_eq continuous_const hr)
  apply compact_subset_frequency_band m hm hms χ _ (hf.of_isClosed_subset (isClosed_tsupport _) hc)
  intro γ hγ
  apply (mem_lcaAnnihilator_iff ..).mpr
  intro k
  have hrestr := congrArg (fun a : PontryaginDual K ↦ a k) (hl hγ)
  change (χ k.val)⁻¹ = (γ k.val)⁻¹ at hrestr
  change (χ k.val)⁻¹ * γ k.val = 1
  rw [inv_injective hrestr, inv_mul_cancel]

/-- Contractive projection on the compact kernel preserves the convolution
on eigenvectors and produces homogeneous kernels in a bounded frequency band. -/
private theorem exists_projected_kernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hm : IsModulation m) (hms : Surjective m) (χ : PontryaginDual G)
    (τ : m.toMonoidHom.ker →* (E →L[ℂ] E)) (hc : ∀ u, Continuous (fun k ↦ τ k u))
    (ht : ∀ k, ‖τ k‖ ≤ 1) (T : G → E →L[ℂ] E)
    (hT : ∀ (k : m.toMonoidHom.ker) g u, T (k.val * g) u = T g (τ k u))
    (B : SchwartzBruhat G →L[ℂ] (E →L[ℂ] E)) (hB : ∀ (f : SchwartzBruhat G) u,
      B f u = ∫ g, f g • T g u ∂μ) (f : SchwartzBruhat G) (hf : HasCompactSupport (lcaFourier μ f)) :
    ∃ (z : SchwartzBruhat G) (N : ℕ), ‖B z‖ ≤ ‖B f‖ ∧
      (∀ (k : m.toMonoidHom.ker) x, z (k.val⁻¹ * x) = star (χ k.val : ℂ) * z x) ∧
      tsupport (lcaFourier μ z) ⊆ modulatedFrequencyBand m χ (-(N : ℝ)) N ∧
      ∀ u ∈ actionIsotype τ ((χ⁻¹).comp ⟨m.toMonoidHom.ker.subtype, continuous_subtype_val⟩), B z u = B f u := by
  let K := m.toMonoidHom.ker
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let κ : Measure K := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)
  let : IsProbabilityMeasure κ := ⟨Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))⟩
  let ξ : PontryaginDual K := (χ⁻¹).comp ⟨K.subtype, continuous_subtype_val⟩
  let σ := (schwartzBruhatTranslationAction (G := G)).comp K.subtype
  let P := schwartzBruhatIsotypicProjector m hm κ ξ
  let H := schwartzBruhat_modulation_source_projector m hm κ ξ
  let : ContinuousSMul ℂ (SchwartzBruhat G) := (withGeneratingSeminorms_spec _ _).continuousSMul
  have hmass : κ.real univ = 1 := by simp
  have hP : IsPettisIsotypicAverageOn κ univ σ ξ P := by
    have h := H.1
    simpa only [hmass, one_smul] using h
  have hcov (k : K) (v : SchwartzBruhat G) (u : E) : B (σ k v) u = B v (τ k u) :=
    normalized_action_translate μ K τ T hT B hB k v u
  have hbound := averaged_action_on_isotype κ ξ σ τ B P hP hc ht hcov f
  let hb := projected_frequency_band μ m hm hms χ f (P f) hf (fourier_isotypic_average μ K κ ξ P hP f)
  refine ⟨P f, hb.choose, hbound.1, fun k x ↦ ?_, hb.choose_spec, hbound.2⟩
  have he := congrArg (fun z : SchwartzBruhat G ↦ z x) ((mem_actionIsotype σ ξ (P f)).mp (H.2.1 f) k)
  exact (schwartzBruhatTranslationAction_apply k.val x (P f)).symm.trans
    (he.trans (congrArg (· * P f x) (Circle.coe_inv_eq_conj (χ k.val))))

/-- Project a full approximate identity and reindex its spectra to obtain
the prescribed bands. The zero kernel fills the finitely many initial slots. -/
private theorem projected_approximate_identity {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (hm : IsModulation m) (hms : Surjective m) (χ : PontryaginDual G)
    (τ : m.toMonoidHom.ker →* (E →L[ℂ] E)) (hc : ∀ u, Continuous (fun k ↦ τ k u))
    (ht : ∀ k, ‖τ k‖ ≤ 1) (T : G → E →L[ℂ] E)
    (hT : ∀ (k : m.toMonoidHom.ker) g u, T (k.val * g) u = T g (τ k u))
    (B : SchwartzBruhat G →L[ℂ] (E →L[ℂ] E)) (hB : ∀ (f : SchwartzBruhat G) u,
      B f u = ∫ g, f g • T g u ∂μ) (f : ℕ → SchwartzBruhat G)
    (hf : ∀ i, ‖B (f i)‖ ≤ 2 ∧ HasCompactSupport (lcaFourier μ (f i)))
    (hlim : ∀ u, Tendsto (fun i ↦ B (f i) u) atTop (𝓝 u)) :
    ∃ z : ℕ → SchwartzBruhat G, (∀ n, ‖B (z n)‖ ≤ 2) ∧
      (∀ n (k : m.toMonoidHom.ker) x, z n (k.val⁻¹ * x) = star (χ k.val : ℂ) * z n x) ∧
      (∀ n, tsupport (lcaFourier μ (z n)) ⊆ modulatedFrequencyBand m χ (-(n : ℝ)) n) ∧
      ∀ u ∈ actionIsotype τ ((χ⁻¹).comp ⟨m.toMonoidHom.ker.subtype, continuous_subtype_val⟩),
        Tendsto (fun n ↦ B (z n) u) atTop (𝓝 u) := by
  let h i := exists_projected_kernel μ m hm hms χ τ hc ht T hT B hB (f i) (hf i).2
  let v i := (h i).choose
  let N i := (h i).choose_spec.choose
  have hv i := (h i).choose_spec.choose_spec
  let r := (exists_band_reindex N).choose
  have hr := (exists_band_reindex N).choose_spec
  let z (n : ℕ) : SchwartzBruhat G := if N 0 ≤ n then v (r n) else 0
  have hzero {n} (hn : ¬ N 0 ≤ n) : z n = 0 := ite_eq_right hn
  have hval {n} (hn : N 0 ≤ n) : z n = v (r n) := ite_eq_left hn
  refine ⟨z, fun n ↦ ?_, fun n k x ↦ ?_, fun n ↦ ?_, fun u hu ↦ ?_⟩
  · by_cases hn : N 0 ≤ n
    · exact (congrArg (fun y ↦ ‖B y‖) (hval hn)).le.trans ((hv (r n)).1.trans (hf (r n)).1)
    · exact ((congrArg norm ((congrArg B (hzero hn)).trans (map_zero B))).trans norm_zero).le.trans
        (by norm_num : (0 : ℝ) ≤ 2)
  · by_cases hn : N 0 ≤ n
    · exact Eq.subst (motive := fun y : SchwartzBruhat G ↦ y (k.val⁻¹ * x) = star (χ k.val : ℂ) * y x)
        (hval hn).symm ((hv (r n)).2.1 k x)
    · exact Eq.subst (motive := fun y : SchwartzBruhat G ↦ y (k.val⁻¹ * x) = star (χ k.val : ℂ) * y x)
        (hzero hn).symm (mul_zero _).symm
  · by_cases hn : N 0 ≤ n
    · have hle : (N (r n) : ℝ) ≤ n := Nat.cast_le.mpr (hr.2 n hn)
      have hmon : modulatedFrequencyBand m χ (-(N (r n) : ℝ)) (N (r n)) ⊆
          modulatedFrequencyBand m χ (-(n : ℝ)) n := fun _ ⟨t, ht, heq⟩ ↦
        ⟨t, ⟨(neg_le_neg hle).trans ht.1, ht.2.trans hle⟩, heq⟩
      exact Eq.subst (motive := fun y : SchwartzBruhat G ↦ tsupport (lcaFourier μ y) ⊆ _)
        (hval hn).symm (((hv (r n)).2.2.1).trans hmon)
    · have hF : lcaFourier μ ((0 : SchwartzBruhat G) : G → ℂ) = 0 := by
        funext γ
        change (∫ x, (0 : ℂ) * star (γ x : ℂ) ∂μ) = 0
        simp
      have hs : tsupport (lcaFourier μ (z n)) = ∅ :=
        (congrArg (fun y : SchwartzBruhat G ↦ tsupport (lcaFourier μ y)) (hzero hn)).trans
          ((congrArg tsupport hF).trans tsupport_zero)
      exact hs.subset.trans (empty_subset _)
  · refine ((hlim u).comp hr.1).congr' ?_
    filter_upwards [eventually_ge_atTop (N 0)] with n hn
    exact ((hv (r n)).2.2.2 u hu).symm.trans (congrArg (fun y ↦ B y u) (hval hn).symm)

/-- Paper: Lemma 9.3.2.1(1)–(4), pp. 422–424. On each fixed kernel isotype
there is a uniformly bounded sequence of convolutions converging strongly to
the identity there, with band-limited twisted kernels.
Deviation: A single homogeneous kernel kills the other isotypes. The
left-translation eigencharacter is inverse to the Fourier frequency on the kernel.

Deviation: Lemma 9.3.2.1(4) claims full-space convergence with individual homogeneous kernels.
The homogeneous family here converges to the identity on the corresponding isotype.
-/
theorem exists_singletonDecay_isotype_approximation (hm : IsModulation m) (hms : Surjective m)
    (b s : ℝ) (hs : 0 ≤ s) (χ : PontryaginDual G) :
    let τ := hardySobolevTranslation μ m b b s le_rfl hs
    let A := (existsUnique_singletonDecay_lineAction μ m hm hms b s hs).exists.choose
    let Eχ := actionIsotype (τ.comp m.toMonoidHom.ker.subtype)
      ((χ⁻¹).comp ⟨m.toMonoidHom.ker.subtype, continuous_subtype_val⟩)
    ∃ φ : ℕ → ModulatedExponentialDecay m {b},
      (∀ n, ‖A (φ n)‖ ≤ 2) ∧
      (∀ (n : ℕ) (k : m.toMonoidHom.ker) x,
        (φ n).val ((k : G)⁻¹ * x) = star (χ (k : G) : ℂ) * (φ n).val x) ∧
      (∀ n, tsupport (lcaFourier μ (modulationWeight m b (φ n).val)) ⊆
        modulatedFrequencyBand m χ (-(n : ℝ)) n) ∧
      ∀ u : Eχ, Tendsto (fun n ↦ A (φ n) u.val) atTop (𝓝 u.val) := by
  intro τ A Eχ
  let H := normalized_line_kernel_model μ m hm hms b s hs
  let e := H.choose
  let T := H.choose_spec.choose
  have he := H.choose_spec.choose_spec.choose_spec.1
  have hT := H.choose_spec.choose_spec.choose_spec.2
  have hker := hT.2.2.2.2.2.1
  have hcov := hT.2.2.2.2.2.2.1
  have hact := hT.2.2.2.2.2.2.2
  let B := A.comp e.symm.toContinuousLinearMap
  let v := (exists_singletonDecay_approximation μ m hm hms b s hs).choose
  have hv := (exists_singletonDecay_approximation μ m hm hms b s hs).choose_spec
  let f n := e (v n)
  have hval (n : ℕ) : B (f n) = A (v n) := congrArg A (e.symm_apply_apply (v n))
  have hf n : ‖B (f n)‖ ≤ 2 ∧ HasCompactSupport (lcaFourier μ (f n)) :=
    ⟨(congrArg norm (hval n)).le.trans (hv.1 n).1,
     Eq.subst (motive := fun g ↦ HasCompactSupport (lcaFourier μ g)) (he (v n)).symm (hv.1 n).2⟩
  have hlim u := (hv.2 u).congr (fun n ↦ congrArg (fun z ↦ z u) (hval n).symm)
  have hc u := (((exists_hardySobolevTranslation μ m b b s le_rfl hs).choose_spec.2.comp
    (Continuous.prodMk_left u)).comp (continuous_subtype_val (p := (· ∈ m.toMonoidHom.ker))))
  let h := projected_approximate_identity μ m hm hms χ (τ.comp m.toMonoidHom.ker.subtype) hc
    hker T hcov B hact f hf hlim
  let z := h.choose
  have hz := h.choose_spec
  have htwist n : modulationWeight m b (e.symm (z n)).val = (z n : G → ℂ) :=
    (he _).symm.trans (congrArg (fun y : SchwartzBruhat G ↦ (y : G → ℂ)) (e.apply_symm_apply _))
  refine ⟨fun n ↦ e.symm (z n), hz.1, fun n k x ↦ ?_, fun n ↦
    Eq.subst (motive := fun g ↦ tsupport (lcaFourier μ g) ⊆ _) (htwist n).symm (hz.2.2.1 n),
    fun u ↦ hz.2.2.2 u.val u.property⟩
  let c (y : G) : ℂ := (Real.exp (b * Real.log ((m y).val : ℝ)) : ℂ)⁻¹
  have hc : c (k.val⁻¹ * x) = c x := by
    simp only [c, map_mul, map_inv, show m k.val = 1 from k.property, inv_one, one_mul]
  have twist (y : G) : z n y * c y = (e.symm (z n)).val y := inverse_singleton_twist_value m b e he (z n) y
  exact (twist _).symm.trans ((congrArg₂ (· * ·) (hz.2.1 n k x) hc).trans
    ((mul_assoc _ _ _).trans (congrArg (star (χ k.val : ℂ) * ·) (twist x))))

local instance instDualMeasurableSpaceSec3 : MeasurableSpace (PontryaginDual G) := borel _

variable (ν : Measure (PontryaginDual G)) (hν : IsLCAPlancherelMeasure μ ν)

set_option quotPrecheck false in
local notation "Fourier" => (lcaFourier_unitary μ ν hν).exists.choose

/-- Extend a real Schwartz profile by zero from an open real line in a group
whose trivial subgroup is good. This is one elementary Schwartz stage. -/
private theorem schwartz_open_line {H : Type*} [CommGroup H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (L : Subgroup H) (ho : IsOpen (L : Set H)) (hgood : IsBruhatGoodSubgroup (⊥ : Subgroup H))
    (e : Multiplicative ℝ ≃ₜ* L) (f : 𝓢(ℝ, ℂ)) :
    ∃ v : SchwartzBruhat H, (∀ t : ℝ, v ((e (Multiplicative.ofAdd t)).val) = f t) ∧
      ∀ g ∉ L, v g = 0 := by
  let a : BruhatStructuralPair H := ⟨(L, OrderDual.toDual ⊥), ho,
    isCompactlyGeneratedGroup_of_continuousMulEquiv e isCompactlyGeneratedGroup_real, hgood, bot_le⟩
  let p := (QuotientGroup.mk' _ : L →* a.quotient)
  have hp : IsOpenQuotientMap p := QuotientGroup.isOpenQuotientMap_mk
  have hinj : Injective p := (MonoidHom.ker_eq_bot_iff p).mp (le_antisymm (fun x hx ↦ by
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact (a.quotient_mk_eq_one x).mp hx) bot_le)
  let q := (MulEquiv.ofBijective p ⟨hinj, hp.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hp.isQuotientMap.isOpen_preimage)
  let : Unique ((Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit) := uniqueOfSubsingleton 0
  let line := (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
  let l : Multiplicative (ElementaryLieGroup 1 0 0 PUnit) ≃ₜ* Multiplicative ℝ :=
    ContinuousMulEquiv.mk' ((Homeomorph.prodUnique _ _).trans line.toHomeomorph)
      (fun x y ↦ line.map_add x.toAdd.1 y.toAdd.1)
  let E : ElementaryLCAPresentation a.quotient := ⟨1, 0, 0, PUnit, q.symm.trans (e.symm.trans l.symm)⟩
  let u := elementarySchwartz_line_equiv.choose (schwartzChangeVariable ℂ line f)
  refine ⟨schwartzBruhatStageInclusion a E u, fun t ↦ ?_, fun g hg ↦ ?_⟩
  · rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
      dite_eq_left (e (Multiplicative.ofAdd t)).property, elementarySchwartz_line_equiv.choose_spec]
    apply congrArg f
    change (l (l.symm (e.symm (q.symm (q (e (Multiplicative.ofAdd t))))))).toAdd = t
    rw [q.symm_apply_apply, e.symm_apply_apply, l.apply_symm_apply]
    rfl
  · rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply, dite_eq_right hg]

/-- Compact generation on the original group makes the trivial subgroup of the dual good. -/
private theorem good_bot_dual_of_compactlyGenerated (hG : IsCompactlyGeneratedGroup G) :
    IsBruhatGoodSubgroup (⊥ : Subgroup (PontryaginDual G)) := by
  obtain ⟨b, _⟩ := pontryaginDual_bidual (G := G)
  let H := PontryaginDual (PontryaginDual G)
  let topE : H ≃ₜ* (⊤ : Subgroup H) :=
    ⟨Subgroup.topEquiv.symm, continuous_id.subtype_mk _, continuous_subtype_val⟩
  have ht : lcaAnnihilator (⊥ : Subgroup (PontryaginDual G)) = ⊤ := by
    refine eq_top_iff.mpr fun χ _ ↦ (mem_lcaAnnihilator_iff _ _).mpr fun k ↦ ?_
    rw [Subgroup.mem_bot.mp k.2, map_one]
  refine ⟨by simpa only [Subgroup.coe_bot] using isClosed_singleton, ?_, ?_⟩
  · rw [ht, Subgroup.coe_top]
    exact isOpen_univ
  · rw [ht]
    exact isCompactlyGeneratedGroup_of_continuousMulEquiv (b.trans topE) hG

/-- The frequency band is the compact image of a real interval in the translate
of the annihilator of the kernel. -/
private theorem frequencyBand_eq_image (χ : PontryaginDual G)
    (e : Multiplicative ℝ ≃ₜ* lcaAnnihilator m.toMonoidHom.ker)
    (he : ∀ (t : ℝ) g, (e (Multiplicative.ofAdd t)).val g = Circle.exp (t * Real.log ((m g).val : ℝ)))
    (α β : ℝ) : modulatedFrequencyBand m χ α β =
      (fun t : ℝ ↦ χ * (e (Multiplicative.ofAdd t)).val) '' Icc α β := by
  ext ψ
  constructor
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, ht, PontryaginDual.ext fun g ↦ (congrArg (χ g * ·) (he t g)).trans (hp g).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, fun g ↦ congrArg (χ g * ·) (he t g)⟩

/-- A smooth bump on the real frequency line, extended by zero and translated
by the starting character, gives a Schwartz cutoff on the full dual. -/
private theorem schwartz_frequency_cutoff (hm : IsModulation m) (hms : Surjective m)
    (χ : PontryaginDual G) (α β ε : ℝ) (hε : 0 < ε) (hband : α + ε < β - ε) :
    ∃ v : SchwartzBruhat (PontryaginDual G),
      tsupport (v : PontryaginDual G → ℂ) ⊆ modulatedFrequencyBand m χ α β ∧
      EqOn (v : PontryaginDual G → ℂ) 1 (modulatedFrequencyBand m χ (α + ε) (β - ε)) := by
  let L := lcaAnnihilator m.toMonoidHom.ker
  obtain ⟨e, he⟩ := exists_frequency_line m hm hms
  let center := (α + β) / 2
  let radius := (β - α) / 2
  let B : ContDiffBump center := ⟨radius - ε, radius, by dsimp [radius]; linarith, by linarith⟩
  let b := fun t : ℝ ↦ (B t : ℂ)
  let f : 𝓢(ℝ, ℂ) := (B.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp B.contDiff)
  obtain ⟨v, hv, hzero⟩ := schwartz_open_line L (isOpen_lcaAnnihilator _ hm.isCompact_ker)
    (good_bot_dual_of_compactlyGenerated (compactlyGenerated_of_surjective_modulation m hm hms)) e f
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual G) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap G Circle).secondCountableTopology
  let V := schwartzBruhatTranslationAction (G := PontryaginDual G) χ v
  let k (t : ℝ) := χ * (e (Multiplicative.ofAdd t)).val
  have hk : Continuous k := continuous_const.mul (continuous_subtype_val.comp e.continuous)
  have hvk (t : ℝ) : V (k t) = b t := by
    rw [show V (k t) = v (χ⁻¹ * k t) from schwartzBruhatTranslationAction_apply ..]
    change v (χ⁻¹ * (χ * _)) = _
    rw [inv_mul_cancel_left]
    exact hv t
  have him (a b : ℝ) : modulatedFrequencyBand m χ a b = k '' Icc a b :=
    frequencyBand_eq_image m χ e he a b
  refine ⟨V, ?_, ?_⟩
  · rw [him]
    apply closure_minimal _ (isCompact_Icc.image hk).isClosed
    intro ψ hψ
    have hmL : χ⁻¹ * ψ ∈ L := by
      by_contra h
      exact hψ ((schwartzBruhatTranslationAction_apply χ ψ v).trans (hzero _ h))
    let t := (e.symm ⟨_, hmL⟩).toAdd
    have ht : k t = ψ := by
      change χ * (e (e.symm ⟨_, hmL⟩)).val = ψ
      rw [e.apply_symm_apply, mul_inv_cancel_left]
    have hsupp : t ∈ support B := fun h ↦ hψ (by rw [← ht, hvk]; exact congrArg Complex.ofReal h)
    rw [B.support_eq, Metric.mem_ball, Real.dist_eq] at hsupp
    obtain ⟨h1, h2⟩ := abs_lt.mp hsupp
    change -radius < t - center at h1
    change t - center < radius at h2
    refine ⟨t, ⟨?_, ?_⟩, ht⟩ <;> dsimp [center, radius] at h1 h2 <;> linarith
  · rw [him]
    rintro _ ⟨t, ⟨ht, ht'⟩, rfl⟩
    rw [hvk]
    change (B t : ℂ) = 1
    exact_mod_cast (B.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      change -(radius - ε) ≤ t - center ∧ t - center ≤ radius - ε
      dsimp [center, radius]
      constructor <;> linarith) : B t = 1)

/-- An ordinary Schwartz–Bruhat function belongs to every nonnegative
logarithmically weighted L² space. -/
private theorem schwartz_mem_modulatedSobolev (f : SchwartzBruhat G) (s : ℝ) (hs : 0 ≤ s) :
    MemLp (f : G → ℂ) 2 (sobolevMeasure μ (modulatedSobolevWeight m) s) := by
  apply schwartzBruhat_memLp_two_of_integrable
  let t (x : G) := Real.log ((m x).val : ℝ)
  let d (x : G) := (1 + |t x| ^ 2) ^ (s / 2)
  have hd : Continuous d := (continuous_const.add ((continuous_logModule' m).abs.pow 2)).rpow_const
    fun x ↦ Or.inl (ne_of_gt (by positivity : 0 < 1 + |t x| ^ 2))
  have hp (x) : 0 ≤ d x := Real.rpow_nonneg (by positivity) _
  change Integrable (f : G → ℂ) (μ.withDensity fun x ↦ ENNReal.ofReal (d x))
  apply (integrable_withDensity_iff_integrable_smul' hd.measurable.ennreal_ofReal (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mpr
  apply (integrable_schwartz_log_weight μ m f s).mono'
  · exact (hd.measurable.ennreal_ofReal.ennreal_toReal.smul (continuous_schwartzBruhat f).measurable).aestronglyMeasurable
  · refine .of_forall fun x ↦ ?_
    change ‖(ENNReal.ofReal (d x)).toReal • f x‖ ≤ _
    rw [norm_smul, ENNReal.toReal_ofReal (hp x), Real.norm_of_nonneg (hp x), mul_comm (d x)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      d x ≤ ((1 + |t x|) ^ 2) ^ (s / 2) :=
        Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg (t x)]) (by linarith)
      _ = _ := by rw [← Real.rpow_natCast (1 + |t x|) 2, ← Real.rpow_mul (by positivity)]; congr 1; ring

/-- Schwartz–Bruhat functions are square-integrable with every nonnegative power of the
logarithmic Sobolev weight of a modulation. -/
theorem SchwartzBruhat.memLp_modulatedSobolev (f : SchwartzBruhat G) (s : ℝ) (hs : 0 ≤ s) :
    MemLp (f : G → ℂ) 2 (sobolevMeasure μ (modulatedSobolevWeight m) s) :=
  schwartz_mem_modulatedSobolev μ m f s hs

/-- Paper: Corollary 9.3.2.3(1), p. 425. There is a Sobolev function whose
Fourier transform has a smooth representative supported in the outer frequency band
and equal to one in the inner band.
Deviation: The proof uses the full dual rather than the printed norm-one dual for
the support. The transform is the Plancherel transform and the support condition
is on a representative. -/
theorem exists_modulatedSobolev_fourierCutoff
    (_hm : IsModulation m) (_hms : Surjective m)
    (s : ℝ) (_hs : 0 ≤ s) (χ : PontryaginDual G) (α β ε : ℝ)
    (_hαβ : α < β) (_hε : 0 < ε) (_hband : α + ε < β - ε) :
    ∃ (u : Lp ℂ 2 μ) (v : PontryaginDual G → ℂ),
      MemLp (u : G → ℂ) 2 (sobolevMeasure μ (modulatedSobolevWeight m) s) ∧
      (Fourier u : PontryaginDual G → ℂ) =ᵐ[ν] v ∧
      IsBruhatSmooth v ∧ tsupport v ⊆ modulatedFrequencyBand m χ α β ∧
      EqOn v 1 (modulatedFrequencyBand m χ (α + ε) (β - ε)) := by
  obtain ⟨v, hvs, hvone⟩ := schwartz_frequency_cutoff m _hm _hms χ α β ε _hε _hband
  let F := (schwartzBruhat_fourier_equiv μ).choose
  have hF := (schwartzBruhat_fourier_equiv μ).choose_spec
  let f := F.symm v
  have hi := (hF f).1
  have h₂ := schwartzBruhat_memLp_two_of_integrable f hi
  have hmem := schwartz_mem_modulatedSobolev μ m f s _hs
  refine ⟨h₂.toLp f, v, hmem.ae_eq ((withDensity_absolutelyContinuous μ _).ae_eq h₂.coeFn_toLp.symm), ?_,
    schwartzBruhat_isBruhatSmooth v, hvs, hvone⟩
  apply ((lcaFourier_unitary μ ν hν).exists.choose_spec _ hi h₂).trans
  exact .of_forall fun ψ ↦ ((hF f).2 ψ).symm.trans
    (congrArg (fun z : SchwartzBruhat (PontryaginDual G) ↦ z ψ) (F.apply_symm_apply v))

/-- Forgetting a larger measure preserves representatives in the smaller L² space. -/
private theorem exists_L2_restriction {X : Type*} [MeasurableSpace X] (ν μ : Measure X) (h : μ ≤ ν) :
    ∃ J : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ, ∀ u, (J u : X → ℂ) =ᵐ[μ] (u : X → ℂ) := by
  have hle : μ ≤ (1 : ℝ≥0∞) • ν := by simpa only [one_smul] using h
  let L := Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) ENNReal.one_ne_top hle
  have hL (u : Lp ℂ 2 ν) := Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℂ) ENNReal.one_ne_top hle u
  refine ⟨{ toFun := L, map_add' := L.map_add, map_smul' := ?_, cont := L.continuous }, hL⟩
  intro c u
  exact Lp.ext ((hL (c • u)).trans (Filter.EventuallyEq.trans (ae_mono h (Lp.coeFn_smul c u))
    (((hL u).symm.fun_comp (c • ·)).trans (Lp.coeFn_smul c (L u)).symm)))

/-- An integrable kernel acting by a Pettis integral on a weighted space gives
ordinary Haar convolution after passage to unweighted L². -/
private theorem pettis_convolution_haar_L2 {w : Measure G}
    (J : Lp ℂ 2 w →L[ℂ] Lp ℂ 2 μ) (hJ : ∀ u, (J u : G → ℂ) =ᵐ[μ] (u : G → ℂ))
    (τ : G →* (Lp ℂ 2 w →L[ℂ] Lp ℂ 2 w))
    (hτ : ∀ g u, (τ g u : G → ℂ) =ᵐ[μ] fun x ↦ u (g⁻¹ * x))
    (hcτ : Continuous (fun z : G × Lp ℂ 2 w ↦ τ z.1 z.2))
    (φ : G → ℂ) (hφ : Integrable φ μ) (u v : Lp ℂ 2 w)
    (hv : HasPettisIntegral (.positive μ) (fun g ↦ φ g • τ g u) v) :
    (J v : G → ℂ) =ᵐ[μ] lcaConvolution μ φ u := by
  let O (g : G) := J (τ g u)
  have hO : Continuous O := J.continuous.comp (hcτ.comp (Continuous.prodMk_left u))
  have hrep (g : G) : (O g : G → ℂ) =ᵐ[μ] fun x ↦ u (g⁻¹ * x) := (hJ _).trans (hτ g u)
  have hnorm (g : G) : ‖O g‖ = ‖J u‖ := by
    let T : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ := Lp.compMeasurePreservingₗᵢ ℂ (fun x : G ↦ g⁻¹ * x) (measurePreserving_mul_left μ g⁻¹)
    have heq : O g = T (J u) := by
      apply Lp.ext
      exact (hrep g).trans (((measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp
        (hJ u).symm).trans (Lp.coeFn_compMeasurePreserving (J u) (measurePreserving_mul_left μ g⁻¹)).symm)
    exact heq ▸ T.norm_map _
  have hi : Integrable (fun g ↦ φ g • O g) μ := by
    apply (hφ.norm.mul_const ‖J u‖).mono' (hφ.1.smul hO.aestronglyMeasurable)
    exact .of_forall fun g ↦ by change ‖φ g • O g‖ ≤ _; rw [norm_smul, hnorm]
  have heq : J v = ∫ g, φ g • O g ∂μ := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro δ
    calc
      δ (J v) = ∫ g, (δ.comp J) (φ g • τ g u) ∂μ := eval_pettis_positive μ hv (δ.comp J)
      _ = ∫ g, δ (φ g • O g) ∂μ := integral_congr_ae (.of_forall fun g ↦ by simp [O])
      _ = δ _ := (eval_pettis_positive μ (Integrable.hasPettisIntegral hi) δ).symm
  rw [heq]
  apply (integral_L2_representative hi (f := fun z : G × G ↦ φ z.1 * u (z.1⁻¹ * z.2)) ?_ ?_).mono
    (fun x hx ↦ hx.2)
  · exact hφ.1.comp_fst.mul ((Lp.stronglyMeasurable u).comp_measurable
      (measurable_fst.inv.mul measurable_snd)).aestronglyMeasurable
  · refine .of_forall fun g ↦ ?_
    filter_upwards [Lp.coeFn_smul (φ g) (O g), hrep g] with x hx hx'
    rw [hx, Pi.smul_apply, hx', smul_eq_mul]

/-- Paper: Corollary 9.3.2.3(2), p. 425. Functions whose Plancherel transform has
a compactly supported representative are dense in the logarithmically weighted Sobolev norm.
Deviation: A Haar L² class sharing the weighted class's representative is made explicit. -/
theorem dense_modulatedSobolev_fourierCompactSupport
    (_hm : IsModulation m) (_hms : Surjective m) (s : ℝ) (_hs : 0 ≤ s) :
    Dense {f : ModulatedSobolev m μ s | ∃ (u : Lp ℂ 2 μ) (v : PontryaginDual G → ℂ),
      (u : G → ℂ) =ᵐ[μ] (f : G → ℂ) ∧
      (Fourier u : PontryaginDual G → ℂ) =ᵐ[ν] v ∧ HasCompactSupport v} := by
  classical
  let w := μ.withDensity fun x ↦ ENNReal.ofReal
    (intervalSobolevDensity 0 0 s (Real.log ((m x).val : ℝ)))
  have hw : w = sobolevMeasure μ (modulatedSobolevWeight m) s := intervalSobolev_zero_eq_sobolevMeasure ..
  change Dense {u : Lp ℂ 2 (sobolevMeasure μ (modulatedSobolevWeight m) s) | _}
  rw [← hw]
  have hle : μ ≤ w := by
    calc
      μ = μ.withDensity 1 := withDensity_one.symm
      _ ≤ _ := withDensity_mono (.of_forall fun x ↦ by
        change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s _)
        rw [ENNReal.one_le_ofReal]
        simpa [intervalSobolevDensity] using Real.one_le_rpow
          (le_add_of_nonneg_right (sq_nonneg _)) (by linarith : 0 ≤ s / 2))
  obtain ⟨J, hJ⟩ := exists_L2_restriction w μ hle
  let τ := hardySobolevTranslation μ m 0 0 s le_rfl _hs
  let A := (existsUnique_singletonDecay_lineAction μ m _hm _hms 0 s _hs).exists.choose
  have hA := (existsUnique_singletonDecay_lineAction μ m _hm _hms 0 s _hs).exists.choose_spec.1
  let approx := exists_singletonDecay_approximation μ m _hm _hms 0 s _hs
  let φ := approx.choose
  have hφ := approx.choose_spec
  have htw (n : ℕ) : modulationWeight m 0 (φ n).val = (φ n).val := by
    funext x
    simp [modulationWeight]
  have hkernel (n : ℕ) : Integrable (φ n).val μ := by
    let ψ := modulatedExponentialDecayTwist m {(0 : ℝ)} ⟨0, rfl⟩ (φ n)
    have ht : (ψ : G → ℂ) = (φ n).val := htw n
    rw [← ht]
    exact ((schwartzBruhat_fourier_equiv μ).choose_spec ψ).1
  have hψ (n : ℕ) : HasCompactSupport (lcaFourier μ (φ n).val) := htw n ▸ ((hφ.1 n).2)
  let D := {u : Lp ℂ 2 w | Integrable (u : G → ℂ) μ}
  have hD : Dense D := by
    have : IsLocallyFiniteMeasure w := IsLocallyFiniteMeasure.withDensity_ofReal
      ((continuous_intervalSobolevDensity 0 0 s).comp (continuous_logModule' m))
    intro u
    apply EMetric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨r, hr, hlt⟩ := exists_between hε
    obtain ⟨f, hc, he, hf, hm⟩ := (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le (by simp) hr.ne'
    refine ⟨hm.toLp f, (hf.integrable_of_hasCompactSupport hc).congr (ae_mono hle hm.coeFn_toLp.symm), ?_⟩
    rw [Lp.edist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub hm.coeFn_toLp)]
    exact he.trans_lt hlt
  apply Dense.of_closure (hD.mono ?_)
  intro u hu
  apply mem_closure_of_tendsto (hφ.2 u)
  refine .of_forall fun n ↦ ?_
  let v := A (φ n) u
  let f := lcaConvolution μ (φ n).val u
  have hv : (J v : G → ℂ) =ᵐ[μ] f := pettis_convolution_haar_L2 μ J hJ τ
    (hardySobolevTranslation_apply μ m 0 0 s le_rfl _hs)
    (exists_hardySobolevTranslation μ m 0 0 s le_rfl _hs).choose_spec.2
    _ (hkernel n) u v (hA (φ n) u)
  have hf : MemLp f 2 μ := (Lp.memLp (J v)).ae_eq hv
  have heq : J v = hf.toLp f := Lp.ext (hv.trans hf.coeFn_toLp.symm)
  refine ⟨J v, lcaFourier μ f, hJ v, heq ▸
    (lcaFourier_unitary μ ν hν).exists.choose_spec f (lcaConvolution_integrable μ (hkernel n) hu).2.1 hf, ?_⟩
  rw [show lcaFourier μ f = _ from lcaFourier_convolution μ (hkernel n) hu]
  exact (hψ n).mul_right

-- TODO(paper-gap): Lemma 9.3.2.4 includes identically zero Mellin components and
-- also fails for nonzero components, e.g. exp(z²) sin(z²) on the positive reals.

-- TODO(paper-gap): Lemma 9.3.2.5 gives an empty coefficient family for a Gaussian
-- with nowhere-zero Mellin transform, although the algebraic convolution ideal is proper.

-- TODO(paper-gap): Theorem 9.3.2.6 leaves φ and χ unbound. The kernels in (9.3.2.10)
-- become more restrictive as T increases. With a zero at the origin the projectors
-- all kill the same nonzero vector normal to the evaluation kernel.

end ApproximateUnits

section Trace

variable [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false in
local notation "weightDensity" => (fun a b s x ↦
  intervalSobolevDensity a b s (Real.log ((m x).val : ℝ)))
local notation "weightedMeasure" => (fun a b s ↦
  μ.withDensity (fun x ↦ ENNReal.ofReal (weightDensity a b s x)))
set_option quotPrecheck false in
local notation "W" => (fun a b s ↦
  CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) a b s)

/-- Paper: §9.3.3.1, p. 426. A bounded measurable compactly supported kernel
acts by convolution on the Hardy–Sobolev space.
Deviation: Haar measurability is explicit. The existing weighted L² model
is available for compact base intervals.

Deviation: Theorem 9.3.3.5(1) specifies a bounded compactly supported symbol. We require
measurability for completed Haar measure, expressed as `AEMeasurable φ μ`.
-/
theorem exists_hardySobolevConvolution (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (φ : G → ℂ) (_hφ : AEMeasurable φ μ) (_hc : HasCompactSupport φ)
    (_hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C) :
    ∃ A : W a b s →L[ℂ] W a b s, ∀ u,
      ∀ᵐ x ∂μ, Integrable (fun g ↦ φ g * u (g⁻¹ * x)) μ ∧
        A u x = lcaConvolution μ φ u x := by
  let V := W a b s
  let τ := hardySobolevTranslation μ m a b s _hab _hs
  have hτ := (exists_hardySobolevTranslation μ m a b s _hab _hs).choose_spec.2
  obtain ⟨M, hM⟩ := _hb
  have htop := memLp_top_of_bound _hφ.aestronglyMeasurable M (.of_forall hM)
  have hi : Integrable φ μ :=
    memLp_one_iff_integrable.mp (htop.mono_exponent_of_measure_support_ne_top
      (fun _ ↦ image_eq_zero_of_notMem_tsupport) _hc.measure_lt_top.ne le_top)
  have horbit (u : V) : Integrable (fun g ↦ φ g • τ g u) μ :=
    integrable_smul_orbit μ hi _hc (hτ.comp (Continuous.prodMk_left u))
  let L : V →ₗ[ℂ] V :=
    { toFun := fun u ↦ ∫ g, φ g • τ g u ∂μ
      map_add' := fun u v ↦ by
        simp only [map_add, smul_add]
        exact integral_add (horbit u) (horbit v)
      map_smul' := fun c u ↦ by simp only [map_smul, smul_comm (φ _) c, integral_smul, RingHom.id_apply] }
  let logm (g : G) := Real.log ((m g).val : ℝ)
  let B (g : G) := max (Real.exp (a * logm g)) (Real.exp (b * logm g)) * (1 + |logm g|) ^ (s / 2)
  have hlog : Continuous logm :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hB : Continuous B := by
    refine Continuous.mul ((Real.continuous_exp.comp (continuous_const.mul hlog)).max
      (Real.continuous_exp.comp (continuous_const.mul hlog))) ?_
    exact (continuous_const.add hlog.abs).rpow_const fun g ↦ Or.inl
      (ne_of_gt (by positivity : 0 < 1 + |logm g|))
  obtain ⟨C, hC⟩ := _hc.exists_bound_of_continuousOn hB.continuousOn
  refine ⟨L.mkContinuous ((∫ g, ‖φ g‖ ∂μ) * C) (fun u ↦ ?_), fun u ↦
    hardySobolev_orbit_integral μ m a b s _hab _hs hi _hc u⟩
  calc ‖∫ g, φ g • τ g u ∂μ‖ ≤ ∫ g, ‖φ g • τ g u‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ g, ‖φ g‖ * (C * ‖u‖) ∂μ := by
      apply integral_mono (horbit u).norm (hi.norm.mul_const _)
      intro g
      change ‖φ g • τ g u‖ ≤ ‖φ g‖ * (C * ‖u‖)
      rw [norm_smul]
      by_cases hg : φ g = 0
      · simp [hg]
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply ((τ g).le_opNorm u).trans
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (norm_hardySobolevTranslation_le μ m a b s _hab _hs g).trans
          ((le_abs_self (B g)).trans (hC g (subset_tsupport _ hg)))
    _ = _ := by rw [integral_mul_const, mul_assoc]

/-- Paper: §9.3.3.1, p. 426. The integrated regular representation for a bounded
measurable compactly supported symbol is the operator given by convolution.

Deviation: The convolution formula on p. 426 specifies boundedness and compact support. The
symbol must also be measurable for completed Haar measure, expressed as `AEMeasurable φ μ`.
-/
def hardySobolevConvolution (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : G → ℂ) (hφ : AEMeasurable φ μ) (hc : HasCompactSupport φ)
    (hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C) :
    W a b s →L[ℂ] W a b s :=
  (exists_hardySobolevConvolution μ m a b s hab hs φ hφ hc hb).choose

/-- Paper: §9.3.3.1, p. 426. Applying the integrated operator gives the stated
convolution integral almost everywhere, with integrability of the integrand. -/
theorem hardySobolevConvolution_apply (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : G → ℂ) (hφ : AEMeasurable φ μ) (hc : HasCompactSupport φ)
    (hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C) (u : W a b s) :
    ∀ᵐ x ∂μ, Integrable (fun g ↦ φ g * u (g⁻¹ * x)) μ ∧
      hardySobolevConvolution μ m a b s hab hs φ hφ hc hb u x = lcaConvolution μ φ u x :=
  (exists_hardySobolevConvolution μ m a b s hab hs φ hφ hc hb).choose_spec u

/-- Paper: §9.3.3.1, p. 426. On a test function the operator used for the
trace is the regularized action of Definition 9.3.1.1. -/
theorem hardySobolevConvolution_eq_testAction (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) (hφ : AEMeasurable φ.val μ)
    (hb : ∃ C : ℝ, ∀ x, ‖φ.val x‖ ≤ C) :
    hardySobolevConvolution μ m a b s hab hs φ.val hφ φ.property.2 hb =
      hardySobolevTestAction μ m a b s hab hs φ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ _).ae_eq
  filter_upwards [hardySobolevConvolution_apply μ m a b s hab hs φ.val hφ φ.property.2 hb u,
    hardySobolevTestAction_apply μ m a b s hab hs φ u] with x hx hy
  exact hx.2.trans hy.symm

section Cutoffs

set_option quotPrecheck false in
local notation "moduleValue" => (fun x ↦ ((m x).val : ℝ))

/-- Paper: Definition 9.3.3.1, p. 427. A cutoff is an inversion-symmetric
nonnegative function of the module with supremum one. Its profile is smooth off a
finite set with finite one-sided limits of every derivative, and it vanishes
outside the larger annulus and equals one on the smaller annulus.
Deviation: The symbol is real-valued, and the uniform norm requirement is expressed
by a supremum over its range. The interval of smoothness of the profile is the positive axis. -/
structure IsModulatedCutoff (Λ ε : ℝ) (ρ : G → ℝ) : Prop where
  radius_pos : 0 < Λ
  width_pos : 0 < ε
  outer_left_sub_width_pos : 0 < Λ⁻¹ - ε
  outer_left_sub_width_lt : Λ⁻¹ - ε < Λ - ε
  nonneg : ∀ x, 0 ≤ ρ x
  abs_le_one : ∀ x, |ρ x| ≤ 1
  sup_eq_one : sSup (range ρ) = 1
  profile : ∃ (q : ℝ → ℝ) (jumps : Finset ℝ),
    (∀ x, ρ x = q (moduleValue x)) ∧ (↑jumps : Set ℝ) ⊆ Ioi 0 ∧
    ContDiffOn ℝ ∞ q (Ioi 0 \ (↑jumps : Set ℝ)) ∧
    ∀ c ∈ jumps, ∀ n : ℕ, ∃ l r : ℝ,
      Tendsto (iteratedDeriv n q) (𝓝[<] c) (𝓝 l) ∧
      Tendsto (iteratedDeriv n q) (𝓝[>] c) (𝓝 r)
  inv_eq : ∀ x, ρ x = ρ x⁻¹
  support_subset : tsupport ρ ⊆ moduleValue ⁻¹' Icc Λ⁻¹ Λ
  eq_one : EqOn ρ 1 (moduleValue ⁻¹' Icc (Λ⁻¹ + ε) (Λ - ε))

/-- Paper: Definition 9.3.3.1, p. 427. A cutoff equals one at the identity
whenever the inner module band contains one.
Deviation: Sanity check on the plateau condition. -/
theorem IsModulatedCutoff.apply_one {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) (_h₁ : Λ⁻¹ + ε ≤ 1) (_h₂ : 1 ≤ Λ - ε) :
    ρ 1 = 1 :=
  hρ.eq_one (by
    change ((m 1).val : ℝ) ∈ Icc (Λ⁻¹ + ε) (Λ - ε)
    rw [map_one, Units.val_one, NNReal.coe_one]
    exact ⟨_h₁, _h₂⟩)

/-- Paper: Definition 9.3.3.1, p. 427. The piecewise smooth profile gives a
measurable function on the group.
Deviation: This is the measurability needed to act on weighted L². -/
theorem IsModulatedCutoff.measurable {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) :
    Measurable ρ := by
  obtain ⟨q, jumps, hfactor, _, hq, _⟩ := hρ.profile
  have hmeas : Measurable (fun t : Ioi (0 : ℝ) ↦ q t.val) := by
    apply ContinuousOn.measurable_of_countable_compl (s := (Subtype.val ⁻¹' (jumps : Set ℝ))ᶜ)
    · exact hq.continuousOn.comp continuous_subtype_val.continuousOn
        fun t ht ↦ ⟨t.property, ht⟩
    · rw [compl_compl]
      exact jumps.finite_toSet.countable.preimage Subtype.val_injective
  let modulePos (x : G) : Ioi (0 : ℝ) := ⟨(m x).val, NNReal.coe_pos.mpr (Units.zero_lt _)⟩
  have hmodule : Continuous modulePos :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).subtype_mk _
  rw [funext hfactor]
  exact hmeas.comp hmodule.measurable

/-- Paper: Definition 9.3.3.1, p. 427. A smooth cutoff is a cutoff whose
complex-valued realization on the group is Bruhat smooth. -/
def IsSmoothModulatedCutoff (Λ ε : ℝ) (ρ : G → ℝ) : Prop :=
  IsModulatedCutoff m Λ ε ρ ∧ IsBruhatSmooth (fun x ↦ (ρ x : ℂ))

/-- Paper: Definition 9.3.3.1, p. 427. A smooth cutoff is continuous on the
group, including at module values where the piecewise smooth definition permits jumps.
Deviation: Sanity check on the smoothness requirement. -/
theorem IsSmoothModulatedCutoff.continuous {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsSmoothModulatedCutoff m Λ ε ρ) :
    Continuous ρ := by
  obtain ⟨k, hk, _, hDescend⟩ := hρ.2 0
  have hkCompact : IsCompact (k : Set G) := by
    let A : OpenCompactlyGeneratedSubgroups (PontryaginDual G) := ⟨lcaAnnihilator k, hk.2⟩
    obtain ⟨_, _, _, hker, hCompact⟩ := lca_dualSubgroup_quotient A
    rwa [hker, show lcaDualAnnihilator A.val = k from lcaDualAnnihilator_annihilator k hk.1]
      at hCompact
  rw [continuous_iff_continuousAt]
  intro x
  -- Use a compact generating set containing the point, a neighborhood, and the good subgroup.
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : G)
  let L := insert x (U ∪ (k : Set G))
  let H := Subgroup.closure L
  have hLH : L ⊆ (H : Set G) := Subgroup.subset_closure
  have hL : L ∈ 𝓝 (1 : G) :=
    mem_of_superset hU (subset_union_left.trans (subset_insert _ _))
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds (mem_of_superset hL hLH)
  have hGen : IsCompactlyGeneratedGroup H :=
    ⟨Subtype.val ⁻¹' L, continuous_subtype_val.continuousAt.preimage_mem_nhds hL,
      (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage
        ((hUc.union hkCompact).insert x), Subgroup.closure_preimage_eq_top L⟩
  let p : BruhatStructuralPair G :=
    ⟨(H, OrderDual.toDual k), hH, hGen, hk,
      subset_union_right.trans ((subset_insert _ _).trans hLH)⟩
  obtain ⟨e⟩ := p.elementary
  obtain ⟨f₀, hf₀, hSmooth⟩ := hDescend p rfl
  let RealCoords := EuclideanSpace ℝ (Fin e.realDim)
  let TorusCover := EuclideanSpace ℝ (Fin e.torusDim)
  let DiscreteCoords := (Fin e.latticeRank → ℤ) × e.finiteFactor
  let Elementary := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let cover : (RealCoords × TorusCover) × DiscreteCoords → Elementary := fun u ↦ elementaryCover u.1 u.2.1 u.2.2
  have hq : IsOpenQuotientMap (fun u : TorusCover ↦ fun i ↦ (u i : AddCircle (1 : ℝ))) :=
    (IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk).comp
      (PiLp.homeomorph 2 (fun _ : Fin e.torusDim ↦ ℝ)).isOpenQuotientMap
  have hCover : IsOpenQuotientMap cover :=
    (Homeomorph.prodAssoc RealCoords (Fin e.torusDim → AddCircle (1 : ℝ)) DiscreteCoords).isOpenQuotientMap.comp
      ((IsOpenQuotientMap.id.prodMap hq).prodMap IsOpenQuotientMap.id)
  let g : Elementary → ℂ := fun y ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd y))
  have hg : Continuous g := by
    apply hCover.continuous_comp_iff.mp
    exact continuous_prod_of_discrete_right.mpr fun d ↦ (hSmooth e d.1 d.2).continuous
  have hf₀c : Continuous f₀ := by
    have hc : Continuous (fun y : p.quotient ↦ g (e.equiv y).toAdd) := hg.comp e.equiv.continuous
    simpa only [g, ofAdd_toAdd, e.equiv.symm_apply_apply] using hc
  have hlocal : Continuous (fun y : H ↦ ρ y.val) := by
    have hc : Continuous (fun y : H ↦ (f₀ (QuotientGroup.mk y)).re) :=
      Complex.continuous_re.comp (hf₀c.comp QuotientGroup.continuous_mk)
    simpa only [hf₀, Complex.ofReal_re] using hc
  exact hH.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
    (hlocal.continuousAt (x := (⟨x, hLH (mem_insert _ _)⟩ : H)))

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- A smooth function of the logarithmic module is Bruhat smooth. On each
structural quotient, compose the descended positive quasi-character with log. -/
theorem isBruhatSmooth_logProfile (m : G →ₜ* ℝ≥0ˣ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) :
    IsBruhatSmooth (fun x ↦ (f (Real.log ((m x).val : ℝ)) : ℂ)) := by
  let χ : QuasiCharacter G :=
    { toFun := fun x ↦ ((m x).val : ℝ)
      map_one' := by simp
      map_mul' := fun x y ↦ by simp
      continuous_toFun := Complex.continuous_ofReal.comp
        (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)) }
  intro p
  obtain ⟨k, hk, hinv, hdesc⟩ :=
    (mem_bruhatSmoothSubmodule_iff _).1 (quasiCharacter_mem_bruhatSmooth χ) p
  refine ⟨k, hk, fun h x ↦ congrArg (fun z : ℂ ↦ (f (Real.log z.re) : ℂ)) (hinv h x), ?_⟩
  intro a ha
  obtain ⟨q, hq, hdiff⟩ := hdesc a ha
  have hpos (y : a.quotient) : 0 < (q y).re := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hq]
    exact NNReal.coe_pos.mpr (Units.zero_lt _)
  refine ⟨fun y ↦ (f (Real.log (q y).re) : ℂ),
    fun x ↦ congrArg (fun z : ℂ ↦ (f (Real.log z.re) : ℂ)) (hq x), ?_⟩
  intro e z b
  exact (hf.of_le (by simp)).comp
    ((Complex.reCLM.contDiff.comp (hdiff e z b)).log fun x ↦ (hpos _).ne')

/-- Paper: Definition 9.3.3.1, p. 427. A positive real modulation admits a
smooth cutoff with outer radius two and width one quarter.
Deviation: Sanity check that both cutoff predicates are inhabited. -/
theorem exists_smoothModulatedCutoff_radius_two (_hm : IsModulation m) (_hms : Surjective m) :
    ∃ ρ : G → ℝ, IsSmoothModulatedCutoff m 2 (1 / 4) ρ := by
  let B : ContDiffBump (0 : ℝ) :=
    ⟨Real.log (7 / 4), Real.log 2, Real.log_pos (by norm_num),
      Real.log_lt_log (by norm_num) (by norm_num)⟩
  let r (x : G) : ℝ := (m x).val
  have hr : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hpos (x : G) : 0 < r x := NNReal.coe_pos.mpr (Units.zero_lt _)
  let ρ (x : G) := B (Real.log (r x))
  have h1 : ρ 1 = 1 := by
    apply B.one_of_mem_closedBall
    simp [r, B.rIn_pos.le]
  refine ⟨ρ, ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    fun _ ↦ B.nonneg, fun x ↦ (abs_of_nonneg (B.nonneg (x := Real.log (r x)))) ▸ B.le_one,
    ?_, ?_, ?_, ?_, ?_⟩, isBruhatSmooth_logProfile m (Complex.ofRealCLM.contDiff.comp B.contDiff)⟩
  · exact IsGreatest.csSup_eq ⟨⟨1, h1⟩, forall_mem_range.mpr fun _ ↦ B.le_one⟩
  · refine ⟨fun t ↦ B (Real.log t), ∅, fun _ ↦ rfl, by simp, ?_, by simp⟩
    simp only [Finset.coe_empty, sdiff_empty]
    exact B.contDiff.comp_contDiffOn (fun x hx ↦ (Real.contDiffAt_log.mpr (mem_Ioi.mp hx).ne').contDiffWithinAt)
  · intro x
    change B (Real.log ((m x).val : ℝ)) = B (Real.log ((m x⁻¹).val : ℝ))
    rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, B.neg]
  · apply closure_minimal _ (isClosed_Icc.preimage hr)
    intro x hx
    have hmem : Real.log (r x) ∈ support B := hx
    rw [B.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
    obtain ⟨hl, hu⟩ := abs_lt.mp hmem
    change (2 : ℝ)⁻¹ ≤ r x ∧ r x ≤ 2
    rw [← Real.log_le_log_iff (by norm_num) (hpos x), Real.log_inv,
      ← Real.log_le_log_iff (hpos x) (by norm_num)]
    exact ⟨hl.le, hu.le⟩
  · intro x hx
    apply B.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    change -Real.log (7 / 4) ≤ _ ∧ _ ≤ Real.log (7 / 4)
    rw [← Real.log_inv, Real.log_le_log_iff (by norm_num) (hpos x),
      Real.log_le_log_iff (hpos x) (by norm_num)]
    change (2 : ℝ)⁻¹ + 1 / 4 ≤ r x ∧ r x ≤ 2 - 1 / 4 at hx
    constructor <;> linarith [hx.1, hx.2]

/-- Paper: Remark 9.3.3.2, pp. 427–428. Multiplication by a measurable symbol
bounded in absolute value by one defines a contractive endomorphism.
Deviation: This uses an arbitrary L² measure so the same construction applies to each
Hardy–Sobolev weight. -/
theorem exists_lpCutoffMultiplier (ν : Measure G) (ρ : G → ℝ) (_hm : Measurable ρ)
    (_hb : ∀ x, |ρ x| ≤ 1) :
    ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν, ‖T‖ ≤ 1 ∧
      ∀ u, (T u : G → ℂ) =ᵐ[ν] fun x ↦ (ρ x : ℂ) * u x := by
  let symbol (x : G) : ℂ := ρ x
  have hbound (x : G) : ‖symbol x‖ ≤ 1 := by
    simpa only [symbol, Complex.norm_real, Real.norm_eq_abs] using _hb x
  have hsymbol : MemLp symbol ∞ ν :=
    memLp_top_of_bound (Complex.measurable_ofReal.comp _hm).aestronglyMeasurable
      1 (.of_forall hbound)
  let multiply := ContinuousLinearMap.mul ℂ ℂ
  let T := multiply.holderL ν ∞ 2 2 (hsymbol.toLp symbol)
  have hT (u : Lp ℂ 2 ν) : (T u : G → ℂ) =ᵐ[ν] fun x ↦ symbol x * u x :=
    (multiply.coeFn_holder (r := 2) (hsymbol.toLp symbol) u).trans <|
      hsymbol.coeFn_toLp.mono fun x hx ↦ congrArg (· * u x) hx
  refine ⟨T, T.opNorm_le_bound zero_le_one (fun u ↦ ?_), hT⟩
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hT u] with x hx
  rw [hx, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hbound x)

/-- Paper: Definition 9.3.3.1, p. 427. The cutoff operator is pointwise multiplication
on the space of square-integrable classes.
Deviation: Its measure is a parameter. Applying the operator to the weighted
measure gives the Hardy–Sobolev cutoff. -/
def lpCutoffMultiplier (ν : Measure G) (ρ : G → ℝ) (hm : Measurable ρ)
    (hb : ∀ x, |ρ x| ≤ 1) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  (exists_lpCutoffMultiplier ν ρ hm hb).choose

/-- Paper: (9.3.3.2), p. 427. Representatives of the cutoff operator agree
almost everywhere with the product by the symbol. -/
theorem lpCutoffMultiplier_apply (ν : Measure G) (ρ : G → ℝ) (hm : Measurable ρ)
    (hb : ∀ x, |ρ x| ≤ 1) (u : Lp ℂ 2 ν) :
    (lpCutoffMultiplier ν ρ hm hb u : G → ℂ) =ᵐ[ν] fun x ↦ (ρ x : ℂ) * u x :=
  (exists_lpCutoffMultiplier ν ρ hm hb).choose_spec.2 u

/-- Paper: Definition 9.3.3.1, p. 427. A cutoff gives a truncation operator
on square-integrable classes for the chosen measure. -/
def modulatedCutoffOperator (ν : Measure G) {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  lpCutoffMultiplier ν ρ hρ.measurable hρ.abs_le_one

/-- Paper: (9.3.3.2), p. 427. The truncation multiplies by the cutoff on almost
every representative value. -/
theorem modulatedCutoffOperator_apply (ν : Measure G) {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) (u : Lp ℂ 2 ν) :
    (modulatedCutoffOperator m ν hρ u : G → ℂ) =ᵐ[ν]
      fun x ↦ (ρ x : ℂ) * u x :=
  lpCutoffMultiplier_apply ν ρ hρ.measurable hρ.abs_le_one u

/-- Paper: Remark 9.3.3.2, pp. 427–428. A nonnegative cutoff acts by a
positive self-adjoint operator on weighted L². -/
theorem modulatedCutoffOperator_isPositive (ν : Measure G) {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) :
    (modulatedCutoffOperator m ν hρ).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).2
  intro u
  have hinner : inner ℂ (modulatedCutoffOperator m ν hρ u) u =
      ((∫ x, ρ x * ‖u x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [modulatedCutoffOperator_apply m ν hρ u] with x hx
    rw [hx, ← smul_eq_mul, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp
  rw [hinner]
  exact ⟨rfl, integral_nonneg fun x ↦ mul_nonneg (hρ.nonneg x) (sq_nonneg _)⟩

/-- Paper: Remark 9.3.3.2, p. 428. The multiplier norm is the essential
supremum of its symbol for a sigma-finite measure.
Deviation: A pointwise supremum of one can be attained only on a null set
when the inner band is empty.

Deviation: Remark 9.3.3.2 identifies the norm with the uniform supremum and asserts it is one.
The width condition on p. 427 can leave the plateau empty and the maximum confined to a
Haar-null set. The operator norm is the essential supremum. The strict width condition
$1/\Lambda+\varepsilon<\Lambda-\varepsilon$ on p. 429 ensures a positive-measure plateau for the
Haar measure on the positive reals.
-/
theorem modulatedCutoffOperator_norm (ν : Measure G) [SigmaFinite ν] {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) :
    ‖modulatedCutoffOperator m ν hρ‖ = (eLpNorm ρ ∞ ν).toReal := by
  let T := modulatedCutoffOperator m ν hρ
  change ‖T‖ = _
  have hmul (u : Lp ℂ 2 ν) : ∀ᵐ x ∂ν, ‖(T u) x‖ = ‖ρ x‖ * ‖u x‖ := by
    filter_upwards [modulatedCutoffOperator_apply m ν hρ u] with x hx
    rw [hx, norm_mul, Complex.norm_real]
  have htop : MemLp ρ ∞ ν :=
    memLp_top_of_bound hρ.measurable.aestronglyMeasurable 1 (.of_forall hρ.abs_le_one)
  apply le_antisymm
  · apply T.opNorm_le_bound ENNReal.toReal_nonneg
    intro u
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hmul u, ae_le_lpNorm_exponent_top htop] with x hTu hx
    exact hTu.trans_le (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
    have hc₀ : 0 ≤ c := (norm_nonneg T).trans hc.le
    apply ENNReal.toReal_le_of_le_ofReal hc₀
    rw [eLpNorm_exponent_top htop.aestronglyMeasurable]
    apply eLpNormEssSup_le_of_ae_bound
    rw [ae_iff]
    simp only [not_le]
    by_contra hnonzero
    -- Test the operator on a finite-measure subset where the cutoff exceeds c.
    obtain ⟨s, hs, hsub, hpos, hfin⟩ := Measure.exists_subset_measure_lt_top
      (measurableSet_lt measurable_const hρ.measurable.norm) (pos_iff_ne_zero.mpr hnonzero)
    let u : Lp ℂ 2 ν := indicatorConstLp 2 hs hfin.ne 1
    have hu : 0 < ‖u‖ := by
      dsimp only [u]
      rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
      exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hpos.ne' hfin.ne) _
    have hlow : c * ‖u‖ ≤ ‖T u‖ := by
      rw [← Real.norm_of_nonneg hc₀, ← norm_smul]
      apply Lp.norm_le_norm_of_ae_le
      have hout : ∀ᵐ x ∂ν, x ∉ s → u x = 0 := indicatorConstLp_coeFn_notMem
      filter_upwards [Lp.coeFn_smul c u, hmul u, hout] with x hcu hTu hxout
      rw [hcu, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc₀, hTu]
      by_cases hx : x ∈ s
      · exact mul_le_mul_of_nonneg_right (hsub hx).le (norm_nonneg _)
      · simp [hxout hx]
    exact (mul_lt_mul_of_pos_right hc hu).not_ge (hlow.trans (T.le_opNorm u))

/-- Reflecting the logarithmic coordinate exchanges the base interval with its negative. -/
private theorem intervalSobolevDensity_neg (a b s t : ℝ) :
    intervalSobolevDensity a b s (-t) = intervalSobolevDensity (-b) (-a) s t := by
  have ha : 2 * a * -t = 2 * -a * t := by ring
  have hb : 2 * b * -t = 2 * -b * t := by ring
  unfold intervalSobolevDensity
  rw [max_comm, neg_sq, ha, hb]

/-- Inversion carries the measure with the reflected density to the measure with the
original density, for an inversion-invariant base measure. -/
private theorem measurePreserving_inv_withDensity {H : Type*} [Group H] [MeasurableSpace H]
    [MeasurableInv H] (ν : Measure H) [ν.IsInvInvariant] {f : H → ℝ≥0∞} (hf : Measurable f) :
    MeasurePreserving Inv.inv (ν.withDensity fun x ↦ f x⁻¹) (ν.withDensity f) := by
  refine ⟨measurable_inv, Measure.ext fun t ht ↦ ?_⟩
  rw [Measure.map_apply measurable_inv ht, withDensity_apply _ (measurable_inv ht),
    withDensity_apply _ ht]
  exact (Measure.measurePreserving_inv ν).setLIntegral_comp_preimage ht hf

/-- Composition with inversion is an isometric isomorphism between the square-integrable
classes of two measures that inversion exchanges. -/
private theorem exists_lpInversion {H : Type*} [InvolutiveInv H] [MeasurableSpace H]
    {ν₁ ν₂ : Measure H} (h₁ : MeasurePreserving Inv.inv ν₂ ν₁)
    (h₂ : MeasurePreserving Inv.inv ν₁ ν₂) :
    ∃ J : Lp ℂ 2 ν₁ ≃ₗᵢ[ℂ] Lp ℂ 2 ν₂, ∀ u, (J u : H → ℂ) =ᵐ[ν₂] fun x ↦ u x⁻¹ := by
  let F : Lp ℂ 2 ν₁ →ₗᵢ[ℂ] Lp ℂ 2 ν₂ := Lp.compMeasurePreservingₗᵢ ℂ Inv.inv h₁
  let B : Lp ℂ 2 ν₂ →ₗᵢ[ℂ] Lp ℂ 2 ν₁ := Lp.compMeasurePreservingₗᵢ ℂ Inv.inv h₂
  have hF (u : Lp ℂ 2 ν₁) : (F u : H → ℂ) =ᵐ[ν₂] fun x ↦ u x⁻¹ :=
    Lp.coeFn_compMeasurePreserving u h₁
  have hB (v : Lp ℂ 2 ν₂) : (B v : H → ℂ) =ᵐ[ν₁] fun x ↦ v x⁻¹ :=
    Lp.coeFn_compMeasurePreserving v h₂
  have hBF (u : Lp ℂ 2 ν₁) : B (F u) = u := by
    apply Lp.ext
    filter_upwards [hB (F u), h₂.quasiMeasurePreserving.ae_eq_comp (hF u)] with x hx hx'
    rw [hx]
    simpa only [comp_apply, inv_inv] using hx'
  have hFB (v : Lp ℂ 2 ν₂) : F (B v) = v := by
    apply Lp.ext
    filter_upwards [hF (B v), h₁.quasiMeasurePreserving.ae_eq_comp (hB v)] with x hx hx'
    rw [hx]
    simpa only [comp_apply, inv_inv] using hx'
  exact ⟨{ toLinearEquiv := LinearEquiv.ofLinearMap F.toLinearMap B.toLinearMap
            (LinearMap.ext hFB) (LinearMap.ext hBF)
           norm_map' := F.norm_map }, hF⟩

/-- An isometry acting by inversion on representatives intertwines the multipliers
of an inversion-invariant symbol. -/
private theorem lpCutoffMultiplier_inversion {ν₁ ν₂ : Measure G}
    (h₁ : MeasurePreserving Inv.inv ν₂ ν₁) (J : Lp ℂ 2 ν₁ ≃ₗᵢ[ℂ] Lp ℂ 2 ν₂)
    (hJ : ∀ u, (J u : G → ℂ) =ᵐ[ν₂] fun x ↦ u x⁻¹) (ρ : G → ℝ) (hm : Measurable ρ)
    (hb : ∀ x, |ρ x| ≤ 1) (hinv : ∀ x, ρ x = ρ x⁻¹) (u : Lp ℂ 2 ν₁) :
    J (lpCutoffMultiplier ν₁ ρ hm hb u) = lpCutoffMultiplier ν₂ ρ hm hb (J u) := by
  apply Lp.ext
  filter_upwards [hJ (lpCutoffMultiplier ν₁ ρ hm hb u),
    h₁.quasiMeasurePreserving.ae_eq_comp (lpCutoffMultiplier_apply ν₁ ρ hm hb u),
    lpCutoffMultiplier_apply ν₂ ρ hm hb (J u), hJ u] with x hx₁ hx₂ hx₃ hx₄
  rw [hx₁, hx₃, hx₄, hinv x]
  exact hx₂

/-- Paper: (9.3.3.3), p. 427. Inversion interchanges the two reflected
interval spaces and intertwines their cutoff multipliers. -/
theorem modulatedCutoffOperator_inversion (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    {Λ ε : ℝ} {ρ : G → ℝ} (hρ : IsModulatedCutoff m Λ ε ρ) :
    ∃ J : W a b s ≃ₗᵢ[ℂ] W (-b) (-a) s,
      (∀ u, (J u : G → ℂ) =ᵐ[μ] fun x ↦ u x⁻¹) ∧
      ∀ u, J (modulatedCutoffOperator m (weightedMeasure a b s) hρ u) =
        modulatedCutoffOperator m (weightedMeasure (-b) (-a) s) hρ (J u) := by
  have hmeas (a b : ℝ) : Measurable fun x : G ↦
      ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ))) := by
    have hlog : Measurable fun x : G ↦ Real.log ((m x).val : ℝ) :=
      Real.measurable_log.comp
        (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable
    have hdensity : Measurable (intervalSobolevDensity a b s) := by
      unfold intervalSobolevDensity
      fun_prop
    exact (hdensity.comp hlog).ennreal_ofReal
  have hpres (a b : ℝ) : MeasurePreserving Inv.inv
      (μ.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity (-b) (-a) s (Real.log ((m x).val : ℝ))))
      (μ.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ)))) := by
    have hreflect : (fun x : G ↦
        ENNReal.ofReal (intervalSobolevDensity (-b) (-a) s (Real.log ((m x).val : ℝ)))) =
        fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x⁻¹).val : ℝ))) := by
      funext x
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv,
        intervalSobolevDensity_neg]
    have h := measurePreserving_inv_withDensity μ (hmeas a b)
    rw [hreflect]
    exact h
  have h₁ := hpres a b
  have h₂ := hpres (-b) (-a)
  rw [neg_neg, neg_neg] at h₂
  obtain ⟨J, hJ⟩ := exists_lpInversion h₁ h₂
  refine ⟨J, fun u ↦ ?_, fun u ↦ ?_⟩
  · refine (withDensity_absolutelyContinuous' (hmeas (-b) (-a)).aemeasurable
      (.of_forall fun x ↦ ?_)).ae_eq (hJ u)
    have hpos : 0 < intervalSobolevDensity (-b) (-a) s (Real.log ((m x).val : ℝ)) := by
      unfold intervalSobolevDensity
      exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
    exact (ENNReal.ofReal_pos.mpr hpos).ne'
  · exact lpCutoffMultiplier_inversion h₁ J hJ ρ hρ.measurable hρ.abs_le_one hρ.inv_eq u

/-- Paper: Definition 9.3.3.3, p. 428. The absolute cutoff associated to a set
of module values is the indicator of its inverse image.
Deviation: Use the same formula for the positive, negative and two-sided cutoffs
with `Ici Λ⁻¹`, `Iic Λ`, and `Icc Λ⁻¹ Λ`, respectively. -/
def modulatedAbsoluteCutoff (J : Set ℝ) : G → ℝ :=
  (moduleValue ⁻¹' J).indicator 1

/-- Paper: (9.3.3.4)–(9.3.3.5), p. 428. The two-sided absolute cutoff is the
product of the two one-sided cutoffs. -/
theorem modulatedAbsoluteCutoff_Icc (Λ : ℝ) :
    modulatedAbsoluteCutoff m (Icc Λ⁻¹ Λ) =
      modulatedAbsoluteCutoff m (Ici Λ⁻¹) * modulatedAbsoluteCutoff m (Iic Λ) := by
  ext x
  simp only [modulatedAbsoluteCutoff, Pi.mul_apply, indicator, mem_preimage, mem_Icc, mem_Ici,
    mem_Iic, Pi.one_apply]
  split_ifs <;> simp_all

/-- Paper: Definition 9.3.3.3, p. 428. The two-sided cutoff of radius two
takes value one at the identity.
Deviation: Sanity check at a point inside the band. -/
theorem modulatedAbsoluteCutoff_radius_two_apply_one :
    modulatedAbsoluteCutoff m (Icc (1 / 2) 2) 1 = 1 := by
  simp only [modulatedAbsoluteCutoff, map_one, Units.val_one]
  exact indicator_of_mem (by norm_num) _

/-- Paper: Definition 9.3.3.3, p. 428. Each measurable module band has a
measurable indicator with values bounded in absolute value by one.
Deviation: These are the side conditions for applying the common multiplier. -/
theorem modulatedAbsoluteCutoff_measurable_bounded (J : Set ℝ) (_hJ : MeasurableSet J) :
    Measurable (modulatedAbsoluteCutoff m J) ∧ ∀ x, |modulatedAbsoluteCutoff m J x| ≤ 1 := by
  refine ⟨measurable_const.indicator
    (_hJ.preimage (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable),
    fun x ↦ ?_⟩
  simp only [modulatedAbsoluteCutoff, indicator]
  split_ifs <;> simp

/-- Paper: Definition 9.3.3.3, p. 428. The absolute cutoff operator is
multiplication by the indicator of the chosen set of module values. -/
def modulatedAbsoluteCutoffOperator (ν : Measure G) (J : Set ℝ) (hJ : MeasurableSet J) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  (hardySobolevCutoff_spec (μ := ν) (U := moduleValue ⁻¹' J)
    (hJ.preimage (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable)).choose

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- Paper: Definition 9.3.3.3, p. 428. The band operator agrees with
the measurable-set projection used in §9.2 on every input. -/
theorem modulatedAbsoluteCutoffOperator_eq_hardySobolevCutoff (ν : Measure G)
    (J : Set ℝ) (hJ : MeasurableSet J) (u : Lp ℂ 2 ν) :
    modulatedAbsoluteCutoffOperator m ν J hJ u =
      hardySobolevCutoff (U := moduleValue ⁻¹' J)
        (hJ.preimage (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable) u :=
  (((hardySobolevCutoff_spec (μ := ν) _).choose_spec.2) u).2.1

/-- Paper: (9.3.3.6)–(9.3.3.7), p. 428. The absolute cutoff retains the input
on the chosen band and vanishes outside it, as an identity of L² representatives. -/
theorem modulatedAbsoluteCutoffOperator_apply (ν : Measure G) (J : Set ℝ)
    (hJ : MeasurableSet J) (u : Lp ℂ 2 ν) :
    (modulatedAbsoluteCutoffOperator m ν J hJ u : G → ℂ) =ᵐ[ν]
      fun x ↦ (modulatedAbsoluteCutoff m J x : ℂ) * u x := by
  have h := (((hardySobolevCutoff_spec (μ := ν) (U := moduleValue ⁻¹' J)
    (hJ.preimage (NNReal.continuous_coe.comp
      (Units.continuous_val.comp m.continuous)).measurable)).choose_spec.2) u).2.2
  refine h.trans (Eventually.of_forall fun x ↦ ?_)
  simp only [modulatedAbsoluteCutoff, indicator]
  split_ifs <;> simp

-- TODO(paper-gap): Remark 9.3.3.4 calls the projectors injective and their symbols
-- bounded below away from zero almost everywhere. Each one-sided cutoff kills
-- functions supported on its excluded half of the module axis.
-- The two-sided cutoff is zero almost everywhere for Λ ≤ 1 on the positive reals.

/-- Paper: Remark 9.3.3.4, p. 428. Every absolute band cutoff is an
orthogonal projection with closed range, including the zero projection. -/
theorem modulatedAbsoluteCutoffOperator_projection (ν : Measure G) (J : Set ℝ)
    (hJ : MeasurableSet J) :
    IsStarProjection (modulatedAbsoluteCutoffOperator m ν J hJ) ∧
      IsClosed (range (modulatedAbsoluteCutoffOperator m ν J hJ)) := by
  have hU : MeasurableSet (moduleValue ⁻¹' J) :=
    hJ.preimage (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable
  obtain ⟨hclosed, hP⟩ := (hardySobolevCutoff_spec (μ := ν) hU).choose_spec
  refine ⟨⟨ContinuousLinearMap.ext fun u ↦ (hP u).1, ?_⟩, hclosed⟩
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
  intro u v
  rw [ContinuousLinearMap.coe_coe, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [modulatedAbsoluteCutoffOperator_apply m ν J hJ u,
    modulatedAbsoluteCutoffOperator_apply m ν J hJ v] with x hu hv
  rw [hu, hv]
  simp only [modulatedAbsoluteCutoff, indicator]
  split_ifs <;> simp

end Cutoffs

section FourierKernels

open UniformSpace
open scoped TensorProduct InnerProductSpace ComplexConjugate

attribute [local instance] instDualMeasurableSpaceSec3

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul in
/-- An absolutely integrable superposition of rank-one operators is nuclear.
Its trace norm is controlled by the integrated cost of the rank-one operators. -/
private theorem integral_rankOne_nuclear_bound {H X : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) (f : X → ℂ) (hf : Integrable f ν)
    (a : X → H) (b : X → StrongDual ℂ H) (ha : Continuous a) (hb : Continuous b)
    (C : ℝ) (hC : ∀ x, ‖b x‖ * ‖a x‖ ≤ C) :
    ∃ (T : H →L[ℂ] H) (hT : IsNuclearOperator T),
      traceNorm ⟨T,hT⟩ ≤ C * ∫ x, ‖f x‖ ∂ν ∧
      (∀ u, Integrable (fun x ↦ (f x * b x u) • a x) ν ∧
        T u = ∫ x, (f x * b x u) • a x ∂ν) ∧
      hilbertTrace ⟨T, hT⟩ = ∫ x, f x * b x (a x) ∂ν := by
  let TensorModel := WithLocalSeminorm (banachProjectiveSeminorm (X := StrongDual ℂ H) (Y := H))
  let M : Completion TensorModel →L[ℂ] (H →L[ℂ] H) := projectiveModelToOperator
  have hM (z : Completion TensorModel) : IsNuclearOperator (M z) :=
    (isNuclearOperator_iff_isBanachNuclear _).mpr ((isBanachNuclear_iff_mem_range _).mpr
      ⟨fromProjectiveSeminorm.completion z, rfl⟩)
  let N := M.toLinearMap.codRestrict (nuclearEndomorphisms H) hM
  let τ := (hilbertTrace_linear (H := H)).choose
  have hτ := (hilbertTrace_linear (H := H)).choose_spec
  have hcost (z : Completion TensorModel) : traceNorm (N z) ≤ ‖z‖ := by
    rw [← schattenNorm_one_eq_traceNorm]
    obtain ⟨d, hd⟩ := projectiveModel_singular_sum z
    change (∑' n, approximationNumber (M z) n ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ ‖z‖
    simpa [d.coeff_eq_approximationNumber, M] using hd.tsum_eq.le
  have htrace (z : Completion TensorModel) : ‖τ (N z)‖ ≤ 1 * ‖z‖ := by
    rw [one_mul, hτ]
    exact (norm_hilbertTrace_le _).trans (hcost z)
  let tr := (τ.comp N).mkContinuous 1 htrace
  let tm (p : StrongDual ℂ H × H) : TensorModel := p.1 ⊗ₜ[ℂ] p.2
  have htm : Continuous tm := by
    apply IsBoundedBilinearMap.continuous (𝕜 := ℂ)
    exact ⟨TensorProduct.add_tmul, TensorProduct.smul_tmul', TensorProduct.tmul_add,
      TensorProduct.tmul_smul, 1, one_pos, fun φ v ↦ (projectiveSeminorm_tmul_le φ v).trans_eq (by rw [one_mul])⟩
  let K (x : X) : Completion TensorModel := (tm (b x, a x) : TensorModel)
  have hK : Continuous K := (Completion.continuous_coe (α := TensorModel)).comp (htm.comp (hb.prodMk ha))
  have hKN (x : X) : ‖f x • K x‖ ≤ ‖f x‖ * C := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((Completion.norm_coe _).le.trans
      ((projectiveSeminorm_tmul_le _ _).trans (hC x))) (norm_nonneg _)
  have hKI : Integrable (fun x ↦ f x • K x) ν :=
    (hf.norm.mul_const C).mono' (hf.1.smul hK.aestronglyMeasurable) (.of_forall hKN)
  let z := ∫ x, f x • K x ∂ν
  have hR (x) : M (K x) = (b x).smulRight (a x) := projectiveModelToOperator_coe _
  refine ⟨M z, hM z, ?_, fun u ↦ ?_, ?_⟩
  · apply (hcost z).trans
    refine (norm_integral_le_integral_norm _).trans ((integral_mono hKI.norm (hf.norm.mul_const C) hKN).trans_eq ?_)
    rw [integral_mul_const,mul_comm]
  · let ev := (ContinuousLinearMap.apply ℂ H u).comp M
    have heq (x) : ev (f x • K x) = (f x * b x u) • a x := by
      change M (f x • K x) u = _
      rw [map_smul, smul_apply, hR, ContinuousLinearMap.smulRight_apply, mul_smul]
    exact ⟨(ev.integrable_comp hKI).congr (.of_forall heq),
      (ev.integral_comp_comm hKI).symm.trans (integral_congr_ae (.of_forall heq))⟩
  · change hilbertTrace (N z) = _
    rw [← hτ]
    change tr z = _
    refine (tr.integral_comp_comm hKI).symm.trans (integral_congr_ae (.of_forall fun x ↦ ?_))
    change tr (f x • K x) = _
    rw [map_smul]
    change f x * τ (N (K x)) = _
    apply congrArg (f x * ·)
    rw [hτ]
    exact (congrArg hilbertTrace (Subtype.ext (hR x))).trans (hilbertTrace_smulRight (b x) (a x))

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul in
/-- An absolutely integrable superposition of rank-one operators is nuclear.
Its trace integrates the rank-one traces. -/
private theorem integral_rankOne_nuclear {H X : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) (f : X → ℂ) (hf : Integrable f ν)
    (a : X → H) (b : X → StrongDual ℂ H) (ha : Continuous a) (hb : Continuous b)
    (C : ℝ) (hC : ∀ x, ‖b x‖ * ‖a x‖ ≤ C) :
    ∃ (T : H →L[ℂ] H) (hT : IsNuclearOperator T),
      (∀ u, Integrable (fun x ↦ (f x * b x u) • a x) ν ∧
        T u = ∫ x, (f x * b x u) • a x ∂ν) ∧
      hilbertTrace ⟨T, hT⟩ = ∫ x, f x * b x (a x) ∂ν := by
  obtain ⟨T,hT,_,hrep,htr⟩ := integral_rankOne_nuclear_bound ν f hf a b ha hb C hC
  exact ⟨T,hT,hrep,htr⟩

/-- Multiplication by a unitary character acts continuously in the character
on each fixed L² vector, preserving its norm. -/
private theorem character_modulations_L2 (ν : Measure G) {k : G → ℂ} (hk : MemLp k 2 ν)
    [FirstCountableTopology (PontryaginDual G)] :
    ∃ v : PontryaginDual G → Lp ℂ 2 ν, Continuous v ∧
      (∀ χ, (v χ : G → ℂ) =ᵐ[ν] fun x ↦ (χ x : ℂ) * k x) ∧
      ∀ χ, ‖v χ‖ = ‖hk.toLp k‖ := by
  let q (χ : PontryaginDual G) (x : G) := (χ x : ℂ) * k x
  have hq (χ : PontryaginDual G) : MemLp (q χ) 2 ν := by
    apply hk.congr_norm ((continuous_subtype_val.comp χ.continuous).aestronglyMeasurable.mul hk.aestronglyMeasurable)
    exact .of_forall fun x ↦ by change ‖k x‖ = ‖(χ x : ℂ) * k x‖; simp
  let v (χ : PontryaginDual G) := (hq χ).toLp (q χ)
  have hrep (χ) : (v χ : G → ℂ) =ᵐ[ν] q χ := (hq χ).coeFn_toLp
  refine ⟨v, ?_, hrep, fun χ ↦ ?_⟩
  · rw [continuous_iff_continuousAt]
    intro γ
    let D (χ : PontryaginDual G) (x : G) := ‖q χ x - q γ x‖ ^ 2
    have ht : Tendsto (fun χ ↦ ∫ x, D χ x ∂ν) (𝓝 γ) (𝓝 (∫ _ : G, (0 : ℝ) ∂ν)) := by
      apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ 4 * ‖k x‖ ^ 2)
      · exact .of_forall fun χ ↦ ((hq χ).aestronglyMeasurable.sub (hq γ).aestronglyMeasurable).norm.pow 2
      · exact .of_forall fun χ ↦ .of_forall fun x ↦ by
          change ‖‖q χ x - q γ x‖ ^ 2‖ ≤ _
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          calc
            _ ≤ (‖q χ x‖ + ‖q γ x‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) _
            _ = _ := by simp [q]; ring
      · exact hk.norm.integrable_sq.const_mul 4
      · refine .of_forall fun x ↦ ?_
        have hc : Continuous (fun χ : PontryaginDual G ↦ q χ x) :=
          (continuous_subtype_val.comp (pontryaginDual_eval x).continuous).mul continuous_const
        have hd : Continuous (fun χ ↦ D χ x) := ((hc.sub (continuous_const (y := q γ x))).norm.pow 2)
        simpa [D] using hd.tendsto γ
    have hsq (χ) : ‖v χ - v γ‖ ^ 2 = ∫ x, D χ x ∂ν := by
      rw [← L2.integral_sq_norm (𝕜 := ℂ)]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (v χ) (v γ), hrep χ, hrep γ] with x hx hy hz
      simp only [hx, Pi.sub_apply, hy, hz, D]
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    simpa only [integral_zero, comp_def, ← hsq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero]
      using (Real.continuous_sqrt.tendsto _).comp ht
  · change ‖(hq χ).toLp _‖ = _
    rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_congr_norm_ae (hq χ).aestronglyMeasurable hk.aestronglyMeasurable (.of_forall fun x ↦ by simp [q] : ∀ᵐ x ∂ν, ‖q χ x‖ = ‖k x‖)]

/-- Fourier inversion of a smooth compactly supported kernel is absolute and
pointwise for the Plancherel measure. -/
private theorem smooth_kernel_fourier_integral (hm : IsModulation m) (hms : Surjective m)
    {φ : G → ℂ} (hc : HasCompactSupport φ) (hs : IsBruhatSmooth φ)
    (η : Measure (PontryaginDual G)) (hη : IsLCAPlancherelMeasure μ η) :
    ∃ f : PontryaginDual G → ℂ, Integrable f η ∧
      ∀ x, φ x = ∫ χ, f χ * (χ x : ℂ) ∂η := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : η.IsHaarMeasure := hη.1
  let : η.Regular := hη.2.1
  have hφS : φ ∈ schwartzBruhatSubmodule G := by
    rw [← modulatedExponentialDecaySubmodule_singleton_zero m]
    exact bruhatCompactSupport_le_modulatedExponentialDecay m {0} hm hms
      ⟨(mem_bruhatSmoothSubmodule_iff _).mpr hs, hc⟩
  let u : SchwartzBruhat G := (⟨φ, hφS⟩ : schwartzBruhatSubmodule G)
  obtain ⟨T, hT⟩ := schwartzBruhat_fourier_equiv μ
  obtain ⟨_, hT'⟩ := schwartzBruhat_fourier_equiv η
  let f := T u
  have hfi : Integrable (f : PontryaginDual G → ℂ) η := (hT' f).1
  have hφc : Continuous φ := continuous_of_bruhatSmooth hs
  have h₂ := hφc.memLp_of_hasCompactSupport (μ := μ) (p := 2) hc
  have hF : ((lcaFourier_unitary μ η hη).exists.choose (h₂.toLp φ) : PontryaginDual G → ℂ)
      =ᵐ[η] (f : PontryaginDual G → ℂ) :=
    ((lcaFourier_unitary μ η hη).exists.choose_spec _ (hT u).1 h₂).trans
      (.of_forall fun χ ↦ ((hT u).2 χ).symm)
  obtain ⟨K, hK, hp⟩ := lcaInverseFourier_zeroAtInfty μ η hη (h₂.toLp φ) f hfi hF
  have heq := Measure.eq_of_ae_eq (hK.trans h₂.coeFn_toLp) K.continuous hφc
  exact ⟨f, hfi, fun x ↦ (congrFun heq x).symm.trans (hp x)⟩

/-- Absolute Fourier inversion can be integrated against any L¹ input. -/
private theorem fourier_kernel_exchange (η : Measure (PontryaginDual G)) (ν : Measure G)
    [SFinite η] [SFinite ν] [BorelSpace (PontryaginDual G)]
    [SecondCountableTopology (PontryaginDual G)] {f : PontryaginDual G → ℂ}
    (hf : Integrable f η) {φ : G → ℂ} (hφ : ∀ z, φ z = ∫ χ, f χ * (χ z : ℂ) ∂η)
    {v : G → ℂ} (hv : Integrable v ν) (x : G) :
    (∫ χ, f χ * (χ x : ℂ) * (∫ y, star (χ y : ℂ) * v y ∂ν) ∂η) =
      ∫ y, φ (x * y⁻¹) * v y ∂ν := by
  let Q (χ : PontryaginDual G) (y : G) := (f χ * (χ (x * y⁻¹) : ℂ)) * v y
  have he : Continuous (fun p : PontryaginDual G × G ↦ (p.1 (x * p.2⁻¹) : ℂ)) :=
    continuous_subtype_val.comp ((continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_fst).prodMk (continuous_const.mul continuous_snd.inv)))
  have hQ : Integrable (Function.uncurry Q) (η.prod ν) := by
    apply (hf.mul_prod hv).norm.mono' ((hf.1.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).mul he.aestronglyMeasurable |>.mul
      (hv.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
    exact .of_forall fun p ↦ by simp
  calc
    _ = ∫ χ, ∫ y, Q χ y ∂ν ∂η := by
      congr with χ
      rw [← integral_const_mul]
      congr with y
      simp only [Q, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj, Complex.star_def]
      ring
    _ = ∫ y, ∫ χ, Q χ y ∂η ∂ν := integral_integral_swap hQ
    _ = _ := by simp only [Q, integral_mul_const, ← hφ]

/-- An inverse Fourier integral masked on both sides by L² functions gives a
nuclear kernel. Its trace norm is bounded by the product of the two mask norms
and the absolute Fourier mass. Its diagonal trace separates into a Fourier mass and a pairing. -/
theorem masked_fourier_kernel_traceNorm_le (η : Measure (PontryaginDual G)) (ν : Measure G)
    [SFinite η] [SigmaFinite ν] [BorelSpace (PontryaginDual G)]
    [SecondCountableTopology (PontryaginDual G)] {f : PontryaginDual G → ℂ}
    (hf : Integrable f η) {φ : G → ℂ} (hφ : ∀ z, φ z = ∫ χ, f χ * (χ z : ℂ) ∂η)
    {a b : G → ℂ} (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) :
    ∃ (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hn : IsNuclearOperator T),
      traceNorm ⟨T,hn⟩ ≤ (‖hb.toLp b‖ * ‖ha.toLp a‖) * ∫ χ, ‖f χ‖ ∂η ∧
      (∀ u, ∀ᵐ x ∂ν, T u x = ∫ y, a x * φ (x * y⁻¹) * star (b y) * u y ∂ν) ∧
      hilbertTrace ⟨T, hn⟩ = φ 1 * ∫ y, star (b y) * a y ∂ν := by
  obtain ⟨A, hAc, hA, hAn⟩ := character_modulations_L2 ν ha
  obtain ⟨B, hBc, hB, hBn⟩ := character_modulations_L2 ν hb
  let L (χ : PontryaginDual G) := innerSL ℂ (B χ)
  have hLc : Continuous L := (innerSL ℂ).continuous.comp hBc
  obtain ⟨T, hn, hcost, hT, htr⟩ := integral_rankOne_nuclear_bound η f hf A L hAc hLc
    (‖hb.toLp b‖ * ‖ha.toLp a‖) (fun χ ↦ by simp only [L, innerSL_apply_norm, hAn, hBn, le_refl])
  have hL (χ) (u : Lp ℂ 2 ν) :
      L χ u = ∫ y, star (χ y : ℂ) * (star (b y) * u y) ∂ν := by
    rw [show L χ u = inner ℂ (B χ) u from rfl, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hB χ] with y hy
    simp only [RCLike.inner_apply, hy, map_mul, Complex.star_def]
    ring
  refine ⟨T, hn, hcost, fun u ↦ ?_, ?_⟩
  · let C (χ : PontryaginDual G) := f χ * L χ u
    have hC : AEStronglyMeasurable C η :=
      hf.1.mul (((ContinuousLinearMap.apply ℂ ℂ u).continuous.comp hLc).aestronglyMeasurable)
    have hE : Continuous (fun p : PontryaginDual G × G ↦ (p.1 p.2 : ℂ)) :=
      continuous_subtype_val.comp ((continuous_eval (F := C(G, Circle))).comp
        (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
          continuous_fst).prodMk continuous_snd))
    have hrep := integral_L2_representative (hT u).1 (f := fun p ↦ C p.1 * ((p.1 p.2 : ℂ) * a p.2))
      ((hC.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
        (hE.aestronglyMeasurable.mul (ha.aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd))) (.of_forall fun χ ↦ by
        filter_upwards [Lp.coeFn_smul (C χ) (A χ), hA χ] with y hy hz
        simp only [C] at *
        rw [hy, Pi.smul_apply, hz, smul_eq_mul])
    have hv : Integrable (fun y ↦ star (b y) * u y) ν := by
      apply (L2.integrable_inner (𝕜 := ℂ) (hb.toLp b) u).congr
      filter_upwards [hb.coeFn_toLp] with y hy
      simp [RCLike.inner_apply, hy, mul_comm]
    filter_upwards [hrep] with x hx
    rw [(hT u).2]
    refine hx.2.trans ?_
    calc
      _ = a x * (∫ χ, f χ * (χ x : ℂ) * (∫ y, star (χ y : ℂ) * (star (b y) * u y) ∂ν) ∂η) := by
        rw [← integral_const_mul]
        congr with χ
        simp only [C, hL]
        ring
      _ = _ := by
        rw [fourier_kernel_exchange η ν hf hφ hv, ← integral_const_mul]
        congr with y
        ring
  · have hdiag (χ) : L χ (A χ) = ∫ y, star (b y) * a y ∂ν := by
      rw [hL]
      apply integral_congr_ae
      filter_upwards [hA χ] with y hy
      rw [hy, show star (χ y : ℂ) = ((χ y)⁻¹ : Circle) from (Circle.coe_inv_eq_conj _).symm]
      have hunit : ((χ y)⁻¹ : Circle) * χ y = 1 := inv_mul_cancel _
      have hz := congrArg (fun z : Circle ↦ (z : ℂ)) hunit
      simp only [Circle.coe_mul, Circle.coe_one] at hz
      linear_combination (star (b y) * a y) * hz
    rw [htr]
    simp only [hdiag, integral_mul_const, hφ 1, map_one, Circle.coe_one, mul_one]

/-- An inverse Fourier integral masked on both sides by L² functions gives a
nuclear kernel. Its diagonal trace separates into a Fourier mass and a pairing. -/
private theorem masked_fourier_kernel (η : Measure (PontryaginDual G)) (ν : Measure G)
    [SFinite η] [SigmaFinite ν] [BorelSpace (PontryaginDual G)]
    [SecondCountableTopology (PontryaginDual G)] {f : PontryaginDual G → ℂ}
    (hf : Integrable f η) {φ : G → ℂ} (hφ : ∀ z, φ z = ∫ χ, f χ * (χ z : ℂ) ∂η)
    {a b : G → ℂ} (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) :
    ∃ (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hn : IsNuclearOperator T),
      (∀ u, ∀ᵐ x ∂ν, T u x = ∫ y, a x * φ (x * y⁻¹) * star (b y) * u y ∂ν) ∧
      hilbertTrace ⟨T, hn⟩ = φ 1 * ∫ y, star (b y) * a y ∂ν := by
  obtain ⟨T,hn,_,hrep,htr⟩ := masked_fourier_kernel_traceNorm_le η ν hf hφ ha hb
  exact ⟨T,hn,hrep,htr⟩

include μ in
/-- Two square-integrable masks of a smooth compactly supported group
convolution kernel give a nuclear integral operator on any sigma-finite
measure. Its kernel and diagonal use that same measure. -/
theorem masked_bruhat_convolution_nuclear (hm : IsModulation m) (hms : Surjective m)
    {φ : G → ℂ} (hc : HasCompactSupport φ) (hs : IsBruhatSmooth φ)
    (ν : Measure G) [SigmaFinite ν] {l r : G → ℂ} (hl : MemLp l 2 ν) (hr : MemLp r 2 ν) :
    ∃ (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hn : IsNuclearOperator T),
      (∀ u, ∀ᵐ x ∂ν, T u x = ∫ y, l x * φ (x * y⁻¹) * star (r y) * u y ∂ν) ∧
      hilbertTrace ⟨T, hn⟩ = φ 1 * ∫ y, star (r y) * l y ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual G) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap G Circle).secondCountableTopology
  obtain ⟨η,hη,-⟩ := lcaPlancherelMeasure_existsUnique μ
  let : η.IsHaarMeasure := hη.1
  obtain ⟨f,hf,hφ⟩ := smooth_kernel_fourier_integral μ m hm hms hc hs η hη
  exact masked_fourier_kernel η ν hf hφ hl hr

/-- An exhaustion of the dual group by measurable frequency windows gives vanishing
trace-norm error for a Fourier kernel with two square-integrable masks. It suffices that
almost every frequency is eventually retained. The windows may vary without nesting. -/
theorem masked_fourier_kernel_tail_traceNorm_tendsto
    (η : Measure (PontryaginDual G)) (ν : Measure G)
    [SFinite η] [SigmaFinite ν] [BorelSpace (PontryaginDual G)] [SecondCountableTopology (PontryaginDual G)]
    {f : PontryaginDual G → ℂ} (hf : Integrable f η)
    (windows : ℕ → Set (PontryaginDual G)) (hW : ∀ n, MeasurableSet (windows n))
    (hcover : ∀ᵐ χ ∂η, ∀ᶠ n in atTop, χ ∈ windows n)
    {a b : G → ℂ} (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) :
    let θ (n : ℕ) (z : G) := ∫ χ, (windows n)ᶜ.indicator f χ * (χ z : ℂ) ∂η
    ∃ E : ℕ → nuclearEndomorphisms (Lp ℂ 2 ν),
      (∀ n u, ∀ᵐ x ∂ν, (E n).val u x = ∫ y, a x * θ n (x * y⁻¹) * star (b y) * u y ∂ν) ∧
      (∀ n, traceNorm (E n) ≤ ‖hb.toLp b‖ * ‖ha.toLp a‖ * ∫ χ, ‖(windows n)ᶜ.indicator f χ‖ ∂η) ∧
      Tendsto (fun n ↦ traceNorm (E n)) atTop (𝓝 0) := by
  intro θ
  let d (n : ℕ) := (windows n)ᶜ.indicator f
  have hd (n : ℕ) : Integrable (d n) η := hf.indicator (hW n).compl
  choose T hn hcost hrep _ using fun n ↦
    masked_fourier_kernel_traceNorm_le η ν (hd n) (φ := θ n) (fun _ ↦ rfl) ha hb
  let E (n : ℕ) : nuclearEndomorphisms (Lp ℂ 2 ν) := ⟨T n, hn n⟩
  refine ⟨E, hrep, hcost, ?_⟩
  have hsmall : Tendsto (fun n ↦ ∫ χ, ‖d n χ‖ ∂η) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun χ ↦ ‖f χ‖)
      (f := fun _ ↦ (0 : ℝ)) (fun n ↦ (hd n).norm.aestronglyMeasurable) hf.norm
      (fun n ↦ Filter.Eventually.of_forall fun χ ↦ ?_) ?_
    · simpa only [integral_zero] using h
    · by_cases hχ : χ ∈ windows n <;> simp [d, hχ]
    · filter_upwards [hcover] with χ hχ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hχ] with n hn
      simp [d, hn]
  have hnonneg (n : ℕ) : 0 ≤ traceNorm (E n) := by
    let : Norm (nuclearEndomorphisms (Lp ℂ 2 ν)) := ⟨traceNorm⟩
    exact (traceNorm_normedSpaceCore (H := Lp ℂ 2 ν)).norm_nonneg (E n)
  exact squeeze_zero hnonneg hcost (by
    simpa only [mul_zero] using hsmall.const_mul (‖hb.toLp b‖ * ‖ha.toLp a‖))

end FourierKernels

variable (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
variable (φ : G → ℂ) (hφ : AEMeasurable φ μ) (hc : HasCompactSupport φ)
  (hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C)
variable {Λ ε : ℝ} {ρ : G → ℝ}

local notation "A" => hardySobolevConvolution μ m a b s hab hs φ hφ hc hb
local notation "truncation" => modulatedCutoffOperator m (weightedMeasure a b s)

-- TODO(paper-gap): Theorem 9.3.3.5(1) assumes neither measurability of φ nor
-- existence of a differentiation limit at the identity. The diagonal smoothening
-- can fail for a bounded Borel φ oscillating on sufficiently separated annuli.

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- A modulated cutoff has compact support when the modulation is proper. -/
private theorem IsModulatedCutoff.isCompact_tsupport' (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    {Λ ε : ℝ} {ρ : G → ℝ} (hρ : IsModulatedCutoff m Λ ε ρ) : IsCompact (tsupport ρ) := by
  have hΛ : 0 < Λ⁻¹ := inv_pos.mpr hρ.radius_pos
  let e := Nonneg.unitsHomeomorphPos ℝ
  have hS : IsCompact ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Icc Λ⁻¹ Λ) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr fun t (ht : t ∈ Icc Λ⁻¹ Λ) ↦ mem_Ioi.mpr (hΛ.trans_le ht.1)]
    exact isCompact_Icc
  have hT := hm.1.isCompact_preimage (e.isCompact_preimage.mpr hS)
  refine hT.of_isClosed_subset (isClosed_tsupport ρ) (hρ.support_subset.trans ?_)
  intro x hx
  exact hx

/-- Paper: Theorem 9.3.3.5(1), p. 429. Truncated convolution is Hilbert–Schmidt
and is represented by the displayed square-integrable kernel.
Deviation: This retains the Hilbert–Schmidt conclusion for measurable symbols
on compact base intervals. The source density in the denominator accounts for
integration against the weighted measure. -/
theorem truncatedHardySobolevConvolution_hilbertSchmidt
    (_hm : IsModulation m) (_hms : Surjective m)
    (hρ : IsModulatedCutoff m Λ ε ρ) (_hband : 0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε) :
    let ν := weightedMeasure a b s
    let k : G × G → ℂ := fun p ↦
      (ρ p.1 : ℂ) * φ (p.1 * p.2⁻¹) / (weightDensity a b s p.2 : ℂ)
    (truncation hρ).comp A ∈ hilbertSchmidtOperators (W a b s) (W a b s) ∧
      MemLp k 2 (ν.prod ν) ∧
      ∀ u : W a b s, ∀ᵐ x ∂ν,
        Integrable (fun y ↦ k (x, y) * u y) ν ∧
          (truncation hρ).comp A u x = ∫ y, k (x, y) * u y ∂ν := by
  intro ν k
  -- The weight is a continuous positive density.
  let w : G → ℝ := fun x ↦ weightDensity a b s x
  have hwpos (x : G) : 0 < w x := intervalSobolevDensity_pos' a b s _
  have hwcont : Continuous w :=
    (continuous_intervalSobolevDensity a b s).comp (continuous_logModule' m)
  let wN : G → ℝ≥0 := fun x ↦ (w x).toNNReal
  have hwN : Measurable wN := hwcont.measurable.real_toNNReal
  have hνdef : ν = μ.withDensity fun x ↦ (wN x : ℝ≥0∞) := rfl
  have hwN_smul (x : G) (z : ℂ) : wN x • z = (w x : ℂ) * z := by
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hwpos x).le, Complex.real_smul]
  have : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hwcont
  have hνμ : ν ≪ μ := withDensity_absolutelyContinuous μ _
  -- The kernel is supported in a compact set.
  have hρc : IsCompact (tsupport ρ) := IsModulatedCutoff.isCompact_tsupport' m _hm hρ
  let K₃ : Set G := (fun p : G × G ↦ p.1⁻¹ * p.2) '' (tsupport φ ×ˢ tsupport ρ)
  have hK₃ : IsCompact K₃ := (hc.prod hρc).image (by fun_prop)
  have hsupp (p : G × G) (hp : k p ≠ 0) : p ∈ tsupport ρ ×ˢ K₃ := by
    have h1 : ρ p.1 ≠ 0 := fun h ↦ hp (by simp [k, h])
    have h2 : φ (p.1 * p.2⁻¹) ≠ 0 := fun h ↦ hp (by simp [k, h])
    refine ⟨subset_tsupport _ h1, ⟨(p.1 * p.2⁻¹, p.1), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, ?_⟩⟩
    simp
  obtain ⟨B, hB⟩ := hK₃.exists_bound_of_continuousOn
    (f := fun y ↦ (w y)⁻¹) (hwcont.inv₀ fun y ↦ (hwpos y).ne').continuousOn
  have ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hbound (p : G × G) : ‖k p‖ ≤ C * max B 0 := by
    by_cases hp : k p = 0
    · rw [hp, norm_zero]; exact mul_nonneg hC0 (le_max_right _ _)
    obtain ⟨-, hy⟩ := hsupp p hp
    have hρ1 : ‖(ρ p.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hρ.abs_le_one _
    have hw1 : ‖((w p.2 : ℂ))⁻¹‖ ≤ max B 0 := by
      rw [norm_inv, Complex.norm_real]; exact (norm_inv (w p.2) ▸ hB _ hy).trans (le_max_left _ _)
    change ‖(ρ p.1 : ℂ) * φ (p.1 * p.2⁻¹) / (w p.2 : ℂ)‖ ≤ _
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc ‖(ρ p.1 : ℂ)‖ * ‖φ (p.1 * p.2⁻¹)‖ * ‖((w p.2 : ℂ))⁻¹‖ ≤ 1 * C * max B 0 := by
          gcongr
          exact hC _
      _ = C * max B 0 := by ring
  -- Measurability of the kernel.
  have hkmeas : AEStronglyMeasurable k (ν.prod ν) := by
    have hdiv : AEMeasurable (fun p : G × G ↦ φ (p.1 * p.2⁻¹)) (μ.prod μ) := by
      simp_rw [← div_eq_mul_inv]
      exact hφ.comp_quasiMeasurePreserving (quasiMeasurePreserving_div μ μ)
    have hk : AEMeasurable k (μ.prod μ) :=
      ((Complex.measurable_ofReal.comp (hρ.measurable.comp measurable_fst)).aemeasurable.mul
        hdiv).div (Complex.measurable_ofReal.comp (hwcont.measurable.comp measurable_snd)).aemeasurable
    exact (hk.mono_ac (hνμ.prod hνμ)).aestronglyMeasurable
  have hkL2 : MemLp k 2 (ν.prod ν) :=
    (memLp_top_of_bound hkmeas _ (.of_forall hbound)).mono_exponent_of_measure_support_ne_top
      (fun p hp ↦ by_contra fun h ↦ hp (hsupp p h)) ((hρc.prod hK₃).measure_lt_top).ne le_top
  -- The action of the truncated convolution.
  have happly : ∀ u : W a b s, ∀ᵐ x ∂ν, Integrable (fun y ↦ k (x, y) * u y) ν ∧
      (truncation hρ).comp A u x = ∫ y, k (x, y) * u y ∂ν := by
    intro u
    filter_upwards [modulatedCutoffOperator_apply m ν hρ (A u),
      hνμ.ae_le (hardySobolevConvolution_apply μ m a b s hab hs φ hφ hc hb u)]
      with x hx ⟨hint, hconv⟩
    let F : G → ℂ := fun g ↦ φ g * u (g⁻¹ * x)
    have hFx (y : G) : F (x / y) = φ (x * y⁻¹) * u y := by
      simp [F, div_eq_mul_inv]
    have hsmul (y : G) : wN y • (k (x, y) * u y) = (ρ x : ℂ) * (φ (x * y⁻¹) * u y) := by
      rw [hwN_smul]
      change (w y : ℂ) * ((ρ x : ℂ) * φ (x * y⁻¹) / (w y : ℂ) * u y) = _
      have : (w y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwpos y).ne'
      field_simp
    have hint' : Integrable (fun y ↦ φ (x * y⁻¹) * u y) μ := by
      have := ((Measure.measurePreserving_div_left μ x).integrable_comp_emb
        (MeasurableEquiv.divLeft x).measurableEmbedding).mpr hint
      exact this.congr (.of_forall fun y ↦ hFx y)
    refine ⟨?_, ?_⟩
    · rw [hνdef, integrable_withDensity_iff_integrable_smul hwN]
      exact (hint'.const_mul (ρ x : ℂ)).congr (.of_forall fun y ↦ (hsmul y).symm)
    · rw [ContinuousLinearMap.comp_apply, hx, hconv, hνdef,
        integral_withDensity_eq_integral_smul hwN]
      simp_rw [hsmul]
      rw [integral_const_mul, lcaConvolution, ← integral_div_left_eq_self F μ x]
      simp_rw [hFx]
  refine ⟨?_, hkL2, happly⟩
  -- Identify the operator with the integral operator of the kernel.
  let op := integralKernelOperator ν (hkL2.toLp k)
  have hop : (truncation hρ).comp A = op.val := by
    refine ContinuousLinearMap.ext fun u ↦ Lp.ext ?_
    have hk' := Measure.ae_ae_of_ae_prod hkL2.coeFn_toLp
    filter_upwards [happly u, integralKernelOperator_apply ν (hkL2.toLp k) u, hk']
      with x hx hopx hkx
    rw [hx.2, hopx.2]
    exact integral_congr_ae (hkx.mono fun y hy ↦ by simp only [hy])
  rw [hop]
  exact op.property

/-- Paper: Theorem 9.3.3.5(2), p. 429. For smooth compactly supported symbols
and piecewise smooth cutoffs, the truncated convolution operator is nuclear, and its trace
equals the integral over the diagonal.
Deviation: A smooth multiplier equal to one on the compact cutoff support gives
the factorization through the smooth case. The diagonal uses Haar measure after the weighted L²
density cancels. The base interval is compact, as in the available Hilbert model. -/
theorem truncatedHardySobolevConvolution_trace
    (_hm : IsModulation m) (_hms : Surjective m)
    (hφsmooth : IsBruhatSmooth φ) (hρ : IsModulatedCutoff m Λ ε ρ)
    (_hband : 0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε) :
    let T := (truncation hρ).comp A
    ∃ hT : IsNuclearOperator T,
      Integrable (fun x ↦ (ρ x : ℂ) * φ 1) μ ∧
      hilbertTrace ⟨T, hT⟩ = ∫ x, (ρ x : ℂ) * φ 1 ∂μ := by
  classical
  intro T
  let w (x : G) := weightDensity a b s x
  let ν := weightedMeasure a b s
  have hw (x) : 0 < w x := intervalSobolevDensity_pos' a b s _
  have hwc : Continuous w := (continuous_intervalSobolevDensity a b s).comp (continuous_logModule' m)
  let : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hwc
  have hρc := IsModulatedCutoff.isCompact_tsupport' m _hm hρ
  let S := tsupport ρ ∪ (fun p : G × G ↦ p.1⁻¹ * p.2) '' (tsupport φ ×ˢ tsupport ρ)
  have hS : IsCompact S := hρc.union ((hc.prod hρc).image (by fun_prop))
  let l (x : G) := (ρ x : ℂ)
  let r := S.indicator (fun x ↦ ((w x : ℂ))⁻¹)
  have hlm : Measurable l := Complex.measurable_ofReal.comp hρ.measurable
  have hlB (x) : ‖l x‖ ≤ 1 := by simpa [l, Real.norm_eq_abs] using hρ.abs_le_one x
  have hls : support l ⊆ tsupport ρ :=
    fun x hx ↦ subset_tsupport _ (fun h ↦ hx (by simp [l, h]))
  have hlp (σ : Measure G) [IsLocallyFiniteMeasure σ] (p : ℝ≥0∞) : MemLp l p σ :=
    (memLp_top_of_bound hlm.aestronglyMeasurable 1 (.of_forall hlB)).mono_exponent_of_measure_support_ne_top
      (fun x hx ↦ by_contra fun h ↦ hx (hls h)) hρc.measure_lt_top.ne le_top
  have hr : MemLp r 2 ν := by
    rw [memLp_indicator_iff_restrict hS.measurableSet.nullMeasurableSet]
    have hrc : Continuous (fun x ↦ ((w x : ℂ))⁻¹) :=
      (Complex.continuous_ofReal.comp hwc).inv₀ fun x ↦ Complex.ofReal_ne_zero.mpr (hw x).ne'
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hrc.continuousOn
    let : IsFiniteMeasure (ν.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
    exact (memLp_top_of_bound hrc.aestronglyMeasurable C
      ((ae_restrict_mem hS.measurableSet).mono hC)).mono_exponent le_top
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual G) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap G Circle).secondCountableTopology
  obtain ⟨η, hη, -⟩ := lcaPlancherelMeasure_existsUnique μ
  let : η.IsHaarMeasure := hη.1
  obtain ⟨f, hf, hi⟩ := smooth_kernel_fourier_integral μ m _hm _hms hc hφsmooth η hη
  obtain ⟨U, hn, hU, htr⟩ := masked_fourier_kernel η ν hf hi (hlp ν 2) hr
  have hin (y) (hy : y ∈ S) : star (r y) = ((w y : ℂ))⁻¹ := by
    simp [r, indicator_of_mem hy]
  have heq : T = U := by
    refine ContinuousLinearMap.ext fun u ↦ Lp.ext ?_
    filter_upwards [(truncatedHardySobolevConvolution_hilbertSchmidt μ m a b s hab hs φ hφ hc hb
      _hm _hms hρ _hband).2.2 u, hU u] with x hx hu
    rw [hu]
    refine hx.2.trans (integral_congr_ae (.of_forall fun y ↦ ?_))
    by_cases h : l x * φ (x * y⁻¹) = 0
    · change l x * φ (x * y⁻¹) / (w y : ℂ) * u y = _
      simp [h]
    · have hl : l x ≠ 0 := left_ne_zero_of_mul h
      have hp : φ (x * y⁻¹) ≠ 0 := right_ne_zero_of_mul h
      have hy : y ∈ S := Or.inr ⟨(x * y⁻¹, x), ⟨subset_tsupport _ hp, hls hl⟩, by simp⟩
      change l x * φ (x * y⁻¹) / (w y : ℂ) * u y = l x * φ _ * star (r y) * u y
      rw [hin y hy]
      rfl
  have hd : (∫ y, star (r y) * l y ∂ν) = ∫ y, l y ∂μ := by
    let d (y : G) := (w y).toNNReal
    change (∫ y, star (r y) * l y ∂(μ.withDensity fun y ↦ (d y : ℝ≥0∞))) = _
    rw [integral_withDensity_eq_integral_smul hwc.measurable.real_toNNReal]
    apply integral_congr_ae
    refine .of_forall fun y ↦ ?_
    by_cases hy : l y = 0
    · simp [hy]
    · change (w y).toNNReal • (star (r y) * l y) = l y
      rw [hin y (Or.inl (hls hy)), NNReal.smul_def, Real.coe_toNNReal _ (hw y).le, Complex.real_smul]
      rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (hw y).ne')]
  subst U
  exact ⟨hn, (memLp_one_iff_integrable.mp (hlp μ 1)).mul_const _, htr.trans (by
    rw [hd, integral_mul_const, mul_comm])⟩

-- TODO(paper-gap): Theorem 9.3.3.5(3) uses a point value and the nuclear trace.
-- For general bounded symbols the point value can change without affecting convolution.

/-- Under the Haar splitting, the mass of a positive module band is its
logarithmic length times the mass of the compact kernel. -/
private theorem moduleBand_mass (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
    (hμ : μ = (μ₁.prod positiveRealHaar).map
      (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2))
    {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
    μ {g | ((m g).val : ℝ) ∈ Icc l r} =
      μ₁ univ * ENNReal.ofReal (Real.log r - Real.log l) := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let e (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (by positivity)
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hs : MeasurableSet {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc l r} :=
    measurableSet_Icc.preimage (NNReal.continuous_coe.comp Units.continuous_val).measurable
  have hpre : e ⁻¹' {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc l r} = Icc (Real.log l) (Real.log r) := by
    ext x
    change (l ≤ ((Real.exp x).toNNReal : ℝ) ∧ ((Real.exp x).toNNReal : ℝ) ≤ r) ↔ _
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, ← Real.log_le_iff_le_exp hl,
      ← Real.le_log_iff_exp_le (hl.trans_le hlr)]
    rfl
  have hband : MeasurableSet {g : G | ((m g).val : ℝ) ∈ Icc l r} :=
    isClosed_Icc.measurableSet.preimage (NNReal.continuous_coe.comp
      (Units.continuous_val.comp m.continuous)).measurable
  rw [hμ, Measure.map_apply (Continuous.measurable (by fun_prop)) hband]
  have hset : (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) ⁻¹'
      {g | ((m g).val : ℝ) ∈ Icc l r} = univ ×ˢ {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc l r} := by
    ext ⟨k, t⟩
    have hk : m (k : G) = 1 := k.property
    simp [hk, hτ t]
  rw [hset, Measure.prod_prod]
  change _ * (volume.map e) _ = _
  rw [Measure.map_apply he hs, hpre, Real.volume_Icc]

/-- Paper: Theorem 9.3.3.5(3), p. 429. For a smooth convolution symbol, the
difference from twice the logarithmic radius times the kernel Haar mass and φ(1)
tends to zero if εΛ tends to zero.
Deviation: The convolution symbol is smooth and the cutoff may have jumps.
A Haar splitting makes the normalization of the kernel Haar measure explicit. The
base interval is compact. -/
theorem truncatedHardySobolevConvolution_trace_tendsto
    (_hm : IsModulation m)
    (_hφsmooth : IsBruhatSmooth φ)
    (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
    (_hμ : μ = (μ₁.prod positiveRealHaar).map
      (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2))
    (ε : ℝ → ℝ) (ρ : ℝ → G → ℝ)
    (_hε : Tendsto (fun Λ ↦ ε Λ * Λ) atTop (𝓝 0))
    (_hρlim : ∀ x, Tendsto (fun Λ ↦ ρ Λ x) atTop (𝓝 1))
    (_hcutoff : ∀ᶠ Λ in atTop, IsModulatedCutoff m Λ (ε Λ) (ρ Λ) ∧
      0 < Λ⁻¹ + ε Λ ∧ Λ⁻¹ + ε Λ < Λ - ε Λ) :
    ∃ traces : ℝ → ℂ,
      (∀ᶠ Λ in atTop, ∃ (hρ : IsModulatedCutoff m Λ (ε Λ) (ρ Λ)),
        let T := (truncation hρ).comp A
        ∃ hT : IsNuclearOperator T, traces Λ = hilbertTrace ⟨T, hT⟩) ∧
      Tendsto (fun Λ ↦ traces Λ - (2 * Real.log Λ * μ₁.real univ : ℝ) * φ 1)
        atTop (𝓝 0) := by
  classical
  let mass (R : ℝ) := ∫ x, ρ R x ∂μ
  refine ⟨fun R ↦ (mass R : ℂ) * φ 1, ?_, ?_⟩
  · filter_upwards [_hcutoff] with R ⟨h, hband⟩
    obtain ⟨hT, -, ht⟩ := truncatedHardySobolevConvolution_trace μ m a b s hab hs φ hφ hc hb
      _hm _hτ.surjective _hφsmooth h hband
    refine ⟨h, hT, ?_⟩
    rw [ht, integral_mul_const, integral_complex_ofReal]
  · let k := μ₁.real univ
    let band (l r : ℝ) := {x : G | ((m x).val : ℝ) ∈ Icc l r}
    have hmBand (l r : ℝ) : MeasurableSet (band l r) := isClosed_Icc.measurableSet.preimage
      (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable
    have : CompactSpace m.toMonoidHom.ker := isCompact_iff_compactSpace.mp _hm.isCompact_ker
    have hbound (R : ℝ) (h : IsModulatedCutoff m R (ε R) (ρ R))
        (hband : 0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
        k * (Real.log (R - ε R) - Real.log (R⁻¹ + ε R)) ≤ mass R ∧
        mass R ≤ k * (2 * Real.log R) := by
      have hm' {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) := moduleBand_mass μ m τ _hτ μ₁ _hμ hl hlr
      have hR := h.radius_pos
      have hout : R⁻¹ ≤ R := by linarith [h.width_pos, hband.2]
      have hi : Integrable ((band R⁻¹ R).indicator (1 : G → ℝ)) μ := by
        rw [integrable_indicator_iff (hmBand _ _)]
        refine integrableOn_const ?_ (by simp)
        exact (hm' (inv_pos.mpr hR) hout ▸ ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top)
      have upper (x : G) : ρ R x ≤ (band R⁻¹ R).indicator (1 : G → ℝ) x := by
        by_cases hx : x ∈ band R⁻¹ R
        · simpa [indicator_of_mem hx] using (le_abs_self _).trans (h.abs_le_one x)
        · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (h.support_subset hs))]
      have hρi : Integrable (ρ R) μ := hi.mono' h.measurable.aestronglyMeasurable
        (.of_forall fun x ↦ (Real.norm_of_nonneg (h.nonneg x)).le.trans (upper x))
      have hmass {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
          (∫ x, (band l r).indicator (1 : G → ℝ) x ∂μ) = k * (Real.log r - Real.log l) := by
        rw [integral_indicator (hmBand l r)]
        simp only [Pi.one_apply, setIntegral_one_eq_measureReal, Measure.real, band,
          hm' hl hlr, ENNReal.toReal_mul, ENNReal.toReal_ofReal
            (sub_nonneg.mpr (Real.log_le_log hl hlr))]
        rfl
      constructor
      · rw [← hmass hband.1 hband.2.le]
        apply integral_mono_of_nonneg (ae_of_all _ (fun x ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) x)) hρi
        refine ae_of_all _ fun x ↦ ?_
        by_cases hx : x ∈ band (R⁻¹ + ε R) (R - ε R)
        · simp only [indicator_of_mem hx, h.eq_one hx, Pi.one_apply, le_refl]
        · simpa only [indicator_of_notMem hx] using h.nonneg x
      · have hle := integral_mono hρi hi upper
        rw [hmass (inv_pos.mpr hR) hout, Real.log_inv, sub_neg_eq_add, ← two_mul] at hle
        exact hle
    have hdiv : Tendsto (fun R ↦ ε R / R) atTop (𝓝 0) := by
      have ht := (_hε.mul (tendsto_inv_atTop_zero (𝕜 := ℝ))).mul
        (tendsto_inv_atTop_zero (𝕜 := ℝ))
      simp only [zero_mul] at ht
      apply ht.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      field_simp
    have hlog : Tendsto (fun R ↦ k * (Real.log (1 - ε R / R) - Real.log (1 + ε R * R)))
        atTop (𝓝 0) := by
      have h₁ := (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv
      have h₂ := (tendsto_const_nhds (x := (1 : ℝ))).add _hε
      simp only [sub_zero, add_zero] at h₁ h₂
      simpa using ((h₁.log one_ne_zero).sub (h₂.log one_ne_zero)).const_mul k
    have ht : Tendsto (fun R ↦ mass R - 2 * Real.log R * k) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlog tendsto_const_nhds
      · filter_upwards [_hcutoff] with R ⟨h, hband⟩
        have hR := h.radius_pos.ne'
        have h₁ : R - ε R = R * (1 - ε R / R) := by field_simp
        have h₂ : R⁻¹ + ε R = R⁻¹ * (1 + ε R * R) := by field_simp
        have hn₁ : 1 - ε R / R ≠ 0 := fun hn ↦ by
          rw [hn, mul_zero] at h₁
          linarith [hband.1, hband.2]
        have hn₂ : 1 + ε R * R ≠ 0 := (add_pos zero_lt_one (mul_pos h.width_pos h.radius_pos)).ne'
        have hl := (hbound R h hband).1
        rw [h₁, h₂, Real.log_mul hR hn₁, Real.log_mul (inv_ne_zero hR) hn₂, Real.log_inv] at hl
        linarith only [hl]
      · filter_upwards [_hcutoff] with R ⟨h, hband⟩
        linarith only [(hbound R h hband).2]
    have ht' := (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).mul_const (φ 1)
    simpa only [comp_apply, Complex.ofReal_sub, Complex.ofReal_zero, zero_mul,
      sub_mul] using ht'

end Trace

section MellinFrequencyChart

variable [SecondCountableTopology G]

/-- On the positive reals, the Mellin frequency normalized by exp(−it log x)
has a surjective real Schwartz Fourier chart for every choice of Haar measure. -/
private theorem positiveRealSchwartz_mellinFrequencyEquiv (η : Measure ℝ≥0ˣ) [η.IsHaarMeasure] :
    ∃ e : 𝓢(ℝ, ℂ) ≃L[ℂ] SchwartzBruhat ℝ≥0ˣ,
      ∃ r : Multiplicative ℝ ≃ₜ* PontryaginDual ℝ≥0ˣ,
        (∀ (t : ℝ) (x : ℝ≥0ˣ), r (Multiplicative.ofAdd t) x = Circle.exp (-t * Real.log (x.val : ℝ))) ∧
        ∀ (p : 𝓢(ℝ, ℂ)) (t : ℝ), lcaFourier η (e p) (r (Multiplicative.ofAdd t)) = p t := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : LocallyCompactSpace ℝ≥0ˣ := positiveRealLogEquiv.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  obtain ⟨R,hR⟩ := exists_realPontryaginDualEquiv
  let d : PontryaginDual ℝ≥0ˣ ≃ₜ* PontryaginDual (Multiplicative ℝ) :=
    { toFun := PontryaginDual.map (positiveRealLogEquiv.symm : Multiplicative ℝ →ₜ* ℝ≥0ˣ)
      invFun := PontryaginDual.map (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ)
      map_mul' := (PontryaginDual.map _).map_mul
      left_inv := fun χ ↦ PontryaginDual.ext fun u ↦ congrArg χ (positiveRealLogEquiv.symm_apply_apply u)
      right_inv := fun χ ↦ PontryaginDual.ext fun u ↦ congrArg χ (positiveRealLogEquiv.apply_symm_apply u)
      continuous_toFun := (PontryaginDual.map _).continuous
      continuous_invFun := (PontryaginDual.map _).continuous }
  let c := 2 * Real.pi
  have hc : c ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  let scale : Multiplicative ℝ ≃ₜ* Multiplicative ℝ :=
    ContinuousMulEquiv.mk' (show ℝ ≃ₜ ℝ from Homeomorph.mulLeft₀ (-c⁻¹) (neg_ne_zero.mpr (inv_ne_zero hc)))
      fun x y ↦ mul_add _ x.toAdd y.toAdd
  let r := scale.trans (R.trans d.symm)
  obtain ⟨U,hU⟩ := schwartzBruhat_realCoordinate_equiv r.symm
  obtain ⟨G,hG⟩ := schwartzBruhat_fourier_equiv η
  let e := U.trans G.symm
  refine ⟨e, r, ?_, fun p t ↦ ?_⟩
  · intro t x
    change R (Multiplicative.ofAdd (-c⁻¹ * t)) (positiveRealLogEquiv x) = _
    rw [show positiveRealLogEquiv x = Multiplicative.ofAdd (Real.log (x.val : ℝ)) from
      congrArg Multiplicative.ofAdd (positiveRealLogEquiv_apply x), hR]
    congr 1
    change c * (-c⁻¹ * t * _) = _
    field_simp
  · exact ((hG (e p)).2 _).symm.trans
      ((congrArg (fun v : SchwartzBruhat (PontryaginDual ℝ≥0ˣ) ↦ v (r (Multiplicative.ofAdd t)))
        (G.apply_symm_apply (U p))).trans ((hU p _).trans (congrArg (fun z : Multiplicative ℝ ↦ p z.toAdd)
          (r.symm_apply_apply _))))

/-- The inverse base character times arbitrary Schwartz profiles of the norm
gives every Schwartz–Bruhat vector of the corresponding translation isotype. -/
private theorem exists_modulatedSchwartz_isotypeLift (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    (hms : Surjective m) (χ : PontryaginDual G) :
    ∃ L : SchwartzBruhat ℝ≥0ˣ →L[ℂ] SchwartzBruhat G,
      (∀ p x, L p x = ((χ⁻¹ x : Circle) : ℂ) * p (m x)) ∧
      ∀ v : SchwartzBruhat G, (∀ (k : m.toMonoidHom.ker) (x : G), v (k.val⁻¹ * x) = (χ k.val : ℂ) * v x) → ∃ p, L p = v := by
  obtain ⟨τ,hτ⟩ := exists_fullModulationSection m hm hms
  obtain ⟨L,hL⟩ := exists_character_profile_lift m hm τ hτ χ⁻¹
  refine ⟨L,hL, fun v hv ↦ ?_⟩
  let : CompactSpace m.toMonoidHom.ker := isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker (m := m) hm)
  let : BorelSpace m.toMonoidHom.ker := inferInstance
  let : LocallyCompactSpace m.toMonoidHom.ker := inferInstance
  let κ : Measure m.toMonoidHom.ker := Measure.haar
  let : κ.IsHaarMeasure := inferInstanceAs (Measure.haar (G := m.toMonoidHom.ker)).IsHaarMeasure
  obtain ⟨M,hM⟩ := exists_schwartzBruhat_characterEquiv χ
  let u := M v
  have hu (k : m.toMonoidHom.ker) (x : G) : u (k.val⁻¹*x) = u x := by
    simp only [u, hM, hv, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
    field_simp [Circle.coe_ne_zero]
  obtain ⟨R, -, hR⟩ := exists_schwartzBruhat_isotype_profile m hm κ τ hτ (1 : PontryaginDual m.toMonoidHom.ker)
  have hPu : schwartzBruhatIsotypicProjector m hm κ (1 : PontryaginDual m.toMonoidHom.ker) u = u := by
    apply schwartzBruhatIsotypicProjector_apply_isotype
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    apply Subtype.ext
    funext x
    change schwartzBruhatTranslationAction (G := G) k.val u x = (1 : ℂ) * u x
    rw [schwartzBruhatTranslationAction_apply, one_mul, hu]
  refine ⟨R u, Subtype.ext (funext fun x ↦ ?_)⟩
  let k : m.toMonoidHom.ker := ⟨x / τ (m x), by change m (x / τ (m x)) = 1; rw [map_div, hτ, div_self']⟩
  have hk : k.val⁻¹ * x = τ (m x) := by change (x / τ (m x))⁻¹ * x = _; rw [inv_div, div_mul_cancel]
  have hprof : R u (m x) = u x := by rw [hR, hPu, ← hk, hu]
  change L (R u) x = v x
  rw [hL, hprof, hM]
  change (((χ x)⁻¹ : Circle) : ℂ) * ((χ x : ℂ) * v x) = v x
  rw [Circle.coe_inv, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]

/-- Real Schwartz profiles on a single component of the dual have a continuous
linear inverse Fourier transform. The chart uses the Mellin ordinate, vanishes off
that component and exhausts the Schwartz tests in its compact-character isotype. -/
theorem exists_schwartzBruhat_mellinFrequencyChart (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    (hms : Surjective m) (μ : Measure G) [μ.IsHaarMeasure] (χ : PontryaginDual G) :
    ∃ (P : 𝓢(ℝ, ℂ) →L[ℂ] SchwartzBruhat G) (γ : ℝ → PontryaginDual G),
      (∀ t x, γ t x = (χ x)⁻¹ * Circle.exp (-t * Real.log ((m x).val : ℝ))) ∧
      (∀ p t, lcaFourier μ (P p) (γ t) = p t) ∧
      (∀ p ψ, ψ ∉ range γ → lcaFourier μ (P p) ψ = 0) ∧
      (∀ p (k : m.toMonoidHom.ker) (x : G), P p (k.val⁻¹ * x) = (χ k.val : ℂ) * P p x) ∧
      ∀ v : SchwartzBruhat G, (∀ (k : m.toMonoidHom.ker) (x : G), v (k.val⁻¹ * x) = (χ k.val : ℂ) * v x) → ∃ p, P p = v := by
  let η := (μ).map m
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : η.IsHaarMeasure := Measure.isHaarMeasure_map μ (m).toMonoidHom (m).continuous hms
    (isProperMap_iff_tendsto_cocompact.mp hm.1).2
  obtain ⟨e,r,hr,he⟩ := positiveRealSchwartz_mellinFrequencyEquiv η
  obtain ⟨L,hL,honto⟩ := exists_modulatedSchwartz_isotypeLift m hm hms χ
  let P := L.comp e.toContinuousLinearMap
  let γ (t : ℝ) := χ⁻¹ * PontryaginDual.map m (r (Multiplicative.ofAdd t))
  have hP (p : 𝓢(ℝ, ℂ)) (x : G) : P p x = ((χ⁻¹ x : Circle) : ℂ) * e p (m x) := hL _ _
  refine ⟨P, γ, fun t x ↦ ?_, fun p t ↦ ?_, fun p ψ hψ ↦ ?_, fun p k x ↦ ?_, fun v hv ↦ ?_⟩
  · change (χ x)⁻¹ * r (Multiplicative.ofAdd t) (m x) = _
    rw [hr]
  · let ξ := r (Multiplicative.ofAdd t)
    have heq (x : G) : P p x * star (γ t x : ℂ) = (e p (m x)) * star (ξ (m x) : ℂ) := by
      rw [hP]
      change ↑((χ x)⁻¹) * e p (m x) * star (((χ x)⁻¹ * ξ (m x) : Circle) : ℂ) = _
      rw [Circle.coe_mul, Circle.coe_inv_eq_conj, ← Complex.star_def, star_mul, star_star]
      rw [show star (χ x : ℂ) = (χ x : ℂ)⁻¹ from (Circle.coe_inv_eq_conj _).symm.trans (Circle.coe_inv _)]
      field_simp [Circle.coe_ne_zero]
    calc
      lcaFourier μ (P p) (γ t) = ∫ x, e p (m x) * star (ξ (m x) : ℂ) ∂μ :=
        integral_congr_ae (.of_forall heq)
      _ = lcaFourier η (e p) ξ :=
        (integral_map (m).continuous.measurable.aemeasurable
          ((continuous_schwartzBruhat (e p)).mul (continuous_subtype_val.comp ξ.continuous).star).aestronglyMeasurable).symm
      _ = p t := he p t
  · by_contra hne
    obtain ⟨τ,hτ⟩ := exists_fullModulationSection m hm hms
    have hne' : ψ ∈ support (lcaFourier μ (fun x ↦ (χ⁻¹ x : ℂ) * e p (m x))) := by
      change lcaFourier μ _ ψ ≠ 0
      rwa [← (show ⇑(P p) = _ from funext (hP p))]
    obtain ⟨ξ, -, hψ'⟩ := support_fourier_character_profile μ m τ hτ χ⁻¹ (e p) (continuous_schwartzBruhat _) hne'
    obtain ⟨z,rfl⟩ := r.surjective ξ
    exact hψ ⟨z.toAdd,hψ'⟩
  · have hm : m (k.val⁻¹ * x) = m x := by
      rw [map_mul, map_inv, show m k.val = 1 from k.property, inv_one, one_mul]
    rw [hP, hP, hm]
    change (((χ (k.val⁻¹ * x))⁻¹ : Circle) : ℂ) * _ = _
    rw [map_mul, map_inv, mul_inv_rev, inv_inv, Circle.coe_mul]
    change _ = (χ k.val : ℂ) * ((((χ x)⁻¹ : Circle) : ℂ) * e p (m x))
    ring
  · obtain ⟨q,hq⟩ := honto v hv
    exact ⟨e.symm q, (congrArg L (e.apply_symm_apply q)).trans hq⟩

end MellinFrequencyChart

end RiemannMasullo
