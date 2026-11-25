import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Transfer of the logarithmic mean deficit between disks

For an entire function `f` bounded by `M` on a disk about `c`, the function
`log M - log ‖f‖` is nonnegative and superharmonic there. Its circle average
about a second center is at most its average over the enclosed disk. Positivity
enlarges that disk to the one about `c`, where Jensen's inequality bounds the
average by the deficit at `c`. The area integrals are taken in `ℝ≥0∞`, so no
integrability over a disk is needed.
-/

noncomputable section

open Set Metric MeasureTheory Real
open scoped ENNReal

namespace MasulloResearch.StripJets

/-- Jensen's inequality at a center where the function does not vanish. -/
theorem log_norm_le_circleAverage_log_norm {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ circleAverage (fun z ↦ Real.log ‖f z‖) c R := by
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by rwa [abs_of_pos hR]
  rw [hf'.circleAverage_log_norm hc, le_add_iff_nonneg_left]
  apply finsum_nonneg
  intro u
  by_cases hu : u ∈ closedBall c |R|
  · apply mul_nonneg
    · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf' u
    · rcases eq_or_ne u c with rfl | huc
      · simp
      · apply Real.log_nonneg
        rw [abs_of_pos hR, mem_closedBall, dist_comm, dist_eq_norm] at hu
        have hpos : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        linarith
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

/-- Circle averages of `log ‖f‖` about a fixed center increase with the radius
when `f` is entire. -/
theorem circleAverage_log_norm_mono_radius {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z) (ρ : ℂ)
    {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    circleAverage (fun z ↦ Real.log ‖f z‖) ρ s ≤
      circleAverage (fun z ↦ Real.log ‖f z‖) ρ r := by
  let g : ℂ → ℂ := fun z ↦ f (z + ρ)
  have hgA : AnalyticOnNhd ℂ g univ := fun z _ ↦
    (hf (z + ρ)).comp (f := fun z : ℂ ↦ z + ρ) (by fun_prop)
  have hg : Meromorphic g := fun z ↦ (hgA z (mem_univ z)).meromorphicAt
  have htop : ValueDistribution.logCounting g ⊤ = 0 := by
    rw [ValueDistribution.logCounting_top,
      negPart_eq_zero.mpr (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hgA), map_zero]
  have key (t : ℝ) (ht : 0 < t) : circleAverage (fun z ↦ Real.log ‖f z‖) ρ t =
      ValueDistribution.logCounting g 0 t + Real.log ‖meromorphicTrailingCoeffAt g 0‖ := by
    have h1 := ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const
      hg ht.ne'
    rw [htop, sub_zero] at h1
    have h2 : circleAverage (fun z ↦ Real.log ‖g z‖) 0 t =
        circleAverage (fun z ↦ Real.log ‖f z‖) ρ t :=
      circleAverage_map_add_const (f := fun z ↦ Real.log ‖f z‖) (c := ρ)
    rw [← h2]
    linarith
  rw [key s hs, key r (hs.trans_le hsr)]
  gcongr
  exact ValueDistribution.logCounting_monotoneOn hs (hs.trans_le hsr) hsr

/-- The integral over the open angular interval is the circle average, scaled. -/
theorem integral_Ioo_circleMap (g : ℂ → ℝ) (p : ℂ) (s : ℝ) :
    ∫ θ in Ioo (-π) π, g (circleMap p s θ) = 2 * π * circleAverage g p s := by
  have hper : Function.Periodic (fun θ ↦ g (circleMap p s θ)) (2 * π) := fun x ↦ by
    simp [periodic_circleMap p s x]
  have h := hper.intervalIntegral_add_eq (-π) 0
  rw [zero_add, show -π + 2 * π = π by ring] at h
  rw [circleAverage_def, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul,
    ← h, intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo]

/-- Polar coordinates about an arbitrary center, for a nonnegative function. -/
theorem lintegral_closedBall_eq_polar {G : ℂ → ℝ≥0∞} (hG : Measurable G) (p : ℂ) (r : ℝ) :
    ∫⁻ z in closedBall p r, G z =
      ∫⁻ s in Ioc 0 r, ENNReal.ofReal s * ∫⁻ θ in Ioo (-π) π, G (circleMap p s θ) := by
  let H : ℂ → ℝ≥0∞ := fun z ↦ (closedBall p r).indicator G (z + p)
  have hH : Measurable H := (hG.indicator measurableSet_closedBall).comp (measurable_add_const p)
  have hsymm : Measurable fun q : ℝ × ℝ ↦ Complex.polarCoord.symm q := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hmap (s θ : ℝ) : Complex.polarCoord.symm (s, θ) + p = circleMap p s θ := by
    simp [circleMap, Complex.exp_mul_I, add_comm]
  have hcirc (s : ℝ) : Measurable fun θ : ℝ ↦ G (circleMap p s θ) :=
    hG.comp (continuous_circleMap p s).measurable
  calc ∫⁻ z in closedBall p r, G z
      = ∫⁻ z, (closedBall p r).indicator G z :=
        (lintegral_indicator measurableSet_closedBall G).symm
    _ = ∫⁻ z, H z :=
        (lintegral_add_right_eq_self (fun z ↦ (closedBall p r).indicator G z) p).symm
    _ = ∫⁻ q in Complex.polarCoord.target,
          ENNReal.ofReal q.1 • H (Complex.polarCoord.symm q) :=
        (Complex.lintegral_comp_polarCoord_symm H).symm
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal s * H (Complex.polarCoord.symm (s, θ)) := by
        rw [Complex.polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
          lintegral_prod]
        · simp only [smul_eq_mul]
        · exact ((ENNReal.measurable_ofReal.comp measurable_fst).smul
            (hH.comp hsymm)).aemeasurable
    _ = ∫⁻ s in Ioi (0 : ℝ), (Iic r).indicator
          (fun s ↦ ENNReal.ofReal s * ∫⁻ θ in Ioo (-π) π, G (circleMap p s θ)) s := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
        have hs0 : 0 < s := hs
        have hmem (θ : ℝ) : circleMap p s θ ∈ closedBall p r ↔ s ≤ r := by
          rw [mem_closedBall, dist_eq_norm]
          simp [circleMap, abs_of_pos hs0]
        by_cases hsr : s ≤ r
        · rw [indicator_of_mem (show s ∈ Iic r from hsr),
            ← lintegral_const_mul _ (hcirc s)]
          refine lintegral_congr fun θ ↦ ?_
          simp only [H, hmap, indicator_of_mem ((hmem θ).mpr hsr)]
        · rw [indicator_of_notMem (show s ∉ Iic r from hsr)]
          simp only [H, hmap, indicator_of_notMem (fun h ↦ hsr ((hmem _).mp h)), mul_zero,
            lintegral_zero]
    _ = ∫⁻ s in Ioc 0 r, ENNReal.ofReal s * ∫⁻ θ in Ioo (-π) π, G (circleMap p s θ) := by
        rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
        congr 2
        ext s
        simp [and_comm]

/-- The radial weight integrates to half the squared radius. -/
theorem lintegral_ofReal_Ioc {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Ioc 0 t, ENNReal.ofReal s = ENNReal.ofReal (t ^ 2 / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le ht, integral_id]
    congr 1
    ring
  · exact (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun s hs ↦ hs.1.le)

/-- **Deficit transfer.** If an entire function is bounded by `M ≥ 1` on a
closed disk about `c` and does not vanish at `c`, its logarithmic mean on any
circle whose closed disk lies inside is controlled by the deficit at `c`,
with the area ratio as the constant. -/
theorem circleAverage_log_norm_deficit_transfer {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    {c ρ : ℂ} {R r M : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hsub : closedBall ρ r ⊆ closedBall c R) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M) (hc : f c ≠ 0) :
    r ^ 2 * (Real.log M - circleAverage (fun z ↦ Real.log ‖f z‖) ρ r) ≤
      R ^ 2 * (Real.log M - Real.log ‖f c‖) := by
  let u : ℂ → ℝ := fun z ↦ Real.log M - Real.log ‖f z‖
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun z ↦ (hf z).continuousAt
  have hmeas : Measurable fun z ↦ ENNReal.ofReal (u z) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.sub (Real.measurable_log.comp hcont.norm.measurable))
  have hnn : ∀ z ∈ closedBall c R, 0 ≤ u z := by
    intro z hz
    rcases eq_or_ne (f z) 0 with h0 | h0
    · simp [u, h0, Real.log_nonneg hM]
    · exact sub_nonneg.mpr (Real.log_le_log (norm_pos_iff.mpr h0) (hbound z hz))
  have inner (p : ℂ) (s : ℝ) (hin : sphere p |s| ⊆ closedBall c R) :
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (u (circleMap p s θ)) =
        ENNReal.ofReal
          (2 * π * (Real.log M - circleAverage (fun z ↦ Real.log ‖f z‖) p s)) := by
    have hci : CircleIntegrable (fun z ↦ Real.log ‖f z‖) p s :=
      MeromorphicOn.circleIntegrable_log_norm fun z _ ↦ (hf z).meromorphicAt
    have hcu : CircleIntegrable u p s := (circleIntegrable_const (Real.log M) p s).sub hci
    have hper : Function.Periodic (fun θ ↦ u (circleMap p s θ)) (2 * π) := fun x ↦ by
      simp [periodic_circleMap p s x]
    have hint : IntegrableOn (fun θ ↦ u (circleMap p s θ)) (Ioo (-π) π) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [pi_pos])).mp
        (hper.intervalIntegrable (by positivity) (t := 0) (by rw [zero_add]; exact hcu)
          (-π) π)).mono_set
        Ioo_subset_Ioc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun θ ↦ hnn _ (hin (circleMap_mem_sphere' p s θ))),
      integral_Ioo_circleMap u p s]
    congr 2
    have : u = (fun _ ↦ Real.log M) - fun z ↦ Real.log ‖f z‖ := rfl
    rw [this, circleAverage_sub (circleIntegrable_const _ p s) hci, circleAverage_const]
  have hΔ : 0 ≤ Real.log M - Real.log ‖f c‖ := hnn c (mem_closedBall_self hR.le)
  have hup : ∫⁻ z in closedBall c R, ENNReal.ofReal (u z) ≤
      ENNReal.ofReal (R ^ 2 / 2) *
        ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖f c‖)) := by
    rw [lintegral_closedBall_eq_polar hmeas c R, ← lintegral_ofReal_Ioc hR.le,
      ← lintegral_mul_const _ ENNReal.measurable_ofReal]
    refine setLIntegral_mono' measurableSet_Ioc fun s hs ↦ ?_
    rw [inner c s (by
      rw [abs_of_pos hs.1]
      exact sphere_subset_closedBall.trans (closedBall_subset_closedBall hs.2))]
    gcongr
    exact log_norm_le_circleAverage_log_norm hs.1 (fun z _ ↦ hf z) hc
  have hlow : ENNReal.ofReal (r ^ 2 / 2) *
      ENNReal.ofReal (2 * π * (Real.log M - circleAverage (fun z ↦ Real.log ‖f z‖) ρ r)) ≤
        ∫⁻ z in closedBall ρ r, ENNReal.ofReal (u z) := by
    rw [lintegral_closedBall_eq_polar hmeas ρ r, ← lintegral_ofReal_Ioc hr.le,
      ← lintegral_mul_const _ ENNReal.measurable_ofReal]
    refine setLIntegral_mono' measurableSet_Ioc fun s hs ↦ ?_
    rw [inner ρ s (by
      rw [abs_of_pos hs.1]
      exact (sphere_subset_closedBall.trans (closedBall_subset_closedBall hs.2)).trans hsub)]
    gcongr
    exact circleAverage_log_norm_mono_radius hf ρ hs.1 hs.2
  have hall := hlow.trans ((lintegral_mono_set hsub).trans hup)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hall
  have hπ := pi_pos
  have h2 : π * (r ^ 2 * (Real.log M - circleAverage (fun z ↦ Real.log ‖f z‖) ρ r)) ≤
      π * (R ^ 2 * (Real.log M - Real.log ‖f c‖)) := by linarith
  exact le_of_mul_le_mul_left h2 hπ

end MasulloResearch.StripJets
