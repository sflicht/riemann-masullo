module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The hyperbolic cardinal function on a finite gap

Here the coordinate measures distance from the node. At the far end the analytic side
vanishes and can be continued by zero. Derivative estimates at the two ends refer
to the analytic side. The constants are independent of the gap length.
-/

@[expose] public noncomputable section

namespace RiemannMasullo.GeometricHat

/-- The solution of the one-dimensional cardinal interpolation equation on a gap of width `d`,
measured at distance `r` from the endpoint where its value is one. -/
def profile (d r : ℝ) : ℝ := Real.sinh (d - r) / Real.sinh d

private theorem scaled_hyperbolic (d r : ℝ) :
    (2 * Real.exp d) * Real.sinh (d - r) =
        Real.exp (-r) * (Real.exp (2 * d) - Real.exp (2 * r)) ∧
    (2 * Real.exp d) * Real.cosh (d - r) =
        Real.exp (-r) * (Real.exp (2 * d) + Real.exp (2 * r)) := by
  have h₁ : Real.exp d * Real.exp (d - r) = Real.exp (-r) * Real.exp (2 * d) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h₂ : Real.exp d * Real.exp (-(d - r)) = Real.exp (-r) * Real.exp (2 * r) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  constructor
  · rw [Real.sinh_eq]
    nlinarith only [h₁, h₂]
  · rw [Real.cosh_eq]
    nlinarith only [h₁, h₂]

private theorem scaled_denominator (d : ℝ) :
    (2 * Real.exp d) * Real.sinh d = Real.exp (2 * d) - 1 := by
  simpa only [sub_zero, neg_zero, mul_zero, Real.exp_zero, one_mul] using
    (scaled_hyperbolic d 0).1

theorem hasDerivAt_profile (d r : ℝ) :
    HasDerivAt (profile d) (-Real.cosh (d - r) / Real.sinh d) r := by
  change HasDerivAt (fun x : ℝ ↦ Real.sinh (d - x) / Real.sinh d) _ _
  simpa using (((hasDerivAt_id r).const_sub d).sinh.div_const (Real.sinh d))

theorem profile_bounds {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) (hrd : r ≤ d) :
    0 ≤ profile d r ∧ profile d r ≤ Real.exp (-r) := by
  have hs := Real.sinh_pos_iff.mpr hd
  have hscale : 0 < 2 * Real.exp d := by positivity
  have hyr : 1 ≤ Real.exp (2 * r) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  refine ⟨div_nonneg (Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hrd)) hs.le, ?_⟩
  unfold profile
  apply (div_le_iff₀ hs).mpr
  refine le_of_mul_le_mul_left ?_ hscale
  calc
    (2 * Real.exp d) * Real.sinh (d - r) =
        Real.exp (-r) * (Real.exp (2 * d) - Real.exp (2 * r)) := (scaled_hyperbolic d r).1
    _ ≤ Real.exp (-r) * (Real.exp (2 * d) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hyr]) (Real.exp_pos _).le
    _ = (2 * Real.exp d) * (Real.exp (-r) * Real.sinh d) := by
      rw [← scaled_denominator]
      ring

theorem weighted_deriv_bound {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) (hrd : r ≤ d) :
    r * ‖deriv (profile d) r‖ ≤ (1 + 2 * r) * Real.exp (-r) := by
  have hs := Real.sinh_pos_iff.mpr hd
  have hscale : 0 < 2 * Real.exp d := by positivity
  have hyr : Real.exp (2 * r) ≤ Real.exp (2 * d) := Real.exp_le_exp.mpr (by linarith)
  have hxr : 2 * r ≤ Real.exp (2 * d) - 1 := by
    linarith only [hrd, Real.add_one_le_exp (2 * d)]
  have hc : r * (Real.exp (2 * d) + Real.exp (2 * r)) ≤
      (1 + 2 * r) * (Real.exp (2 * d) - 1) := by
    nlinarith only [mul_le_mul_of_nonneg_left hyr hr, hxr]
  rw [(hasDerivAt_profile d r).deriv, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_pos (Real.cosh_pos _), abs_of_pos hs, ← mul_div_assoc]
  apply (div_le_iff₀ hs).mpr
  refine le_of_mul_le_mul_left ?_ hscale
  calc
    (2 * Real.exp d) * (r * Real.cosh (d - r)) =
        r * ((2 * Real.exp d) * Real.cosh (d - r)) := by ring
    _ = Real.exp (-r) * (r * (Real.exp (2 * d) + Real.exp (2 * r))) := by
      rw [(scaled_hyperbolic d r).2]
      ring
    _ ≤ Real.exp (-r) * ((1 + 2 * r) * (Real.exp (2 * d) - 1)) :=
      mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
    _ = (2 * Real.exp d) * ((1 + 2 * r) * Real.exp (-r) * Real.sinh d) := by
      rw [← scaled_denominator]
      ring

/-- Apply on each side with the complex multiplier written in the distance coordinate.
Only the bound on its derivative on the segment from the node to the point is needed. -/
theorem cancellation_bounds {d r L : ℝ} (hd : 0 < d) (hr : 0 ≤ r) (hrd : r ≤ d)
    (f f' : ℝ → ℂ) (hf : ∀ t ∈ Set.Icc 0 r, HasDerivAt f (f' t) t)
    (hL : ∀ t ∈ Set.Icc 0 r, ‖f' t‖ ≤ L) :
    ‖(f r - f 0) * (profile d r : ℂ)‖ ≤ L * r * Real.exp (-r) ∧
    ‖deriv (fun t : ℝ ↦ (f t - f 0) * (profile d t : ℂ)) r‖ ≤
      2 * L * (1 + r) * Real.exp (-r) := by
  have hrr : r ∈ Set.Icc (0 : ℝ) r := ⟨hr, le_rfl⟩
  have hL₀ := (norm_nonneg (f' r)).trans (hL r hrr)
  have hdiff : ‖f r - f 0‖ ≤ L * r := by
    simpa only [sub_zero] using norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht ↦ (hf t ht).hasDerivWithinAt)
      (fun t ht ↦ hL t (Set.Ico_subset_Icc_self ht)) r hrr
  have hp := profile_bounds hd hr hrd
  have hpn : ‖(profile d r : ℂ)‖ ≤ Real.exp (-r) := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hp.1] using hp.2
  have hp' := (hasDerivAt_profile d r).differentiableAt.hasDerivAt.ofReal_comp
  have hprod := ((hf r hrr).sub_const (f 0)).mul hp'
  change HasDerivAt (fun t : ℝ ↦ (f t - f 0) * (profile d t : ℂ)) _ _ at hprod
  constructor
  · rw [norm_mul]
    exact mul_le_mul hdiff hpn (norm_nonneg _) (mul_nonneg hL₀ hr)
  · rw [hprod.deriv]
    calc
      _ ≤ ‖f' r * (profile d r : ℂ)‖ + ‖(f r - f 0) * Complex.ofReal (deriv (profile d) r)‖ :=
        norm_add_le _ _
      _ = ‖f' r‖ * ‖(profile d r : ℂ)‖ + ‖f r - f 0‖ * ‖deriv (profile d) r‖ := by
        simp only [norm_mul, Complex.norm_real]
      _ ≤ L * Real.exp (-r) + (L * r) * ‖deriv (profile d) r‖ :=
        add_le_add (mul_le_mul (hL r hrr) hpn (norm_nonneg _) hL₀)
          (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
      _ = L * Real.exp (-r) + L * (r * ‖deriv (profile d) r‖) := by ring
      _ ≤ L * Real.exp (-r) + L * ((1 + 2 * r) * Real.exp (-r)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (weighted_deriv_bound hd hr hrd) hL₀)
      _ = 2 * L * (1 + r) * Real.exp (-r) := by ring

theorem hasDerivAt_deriv_profile (d r : ℝ) :
    HasDerivAt (deriv (profile d)) (profile d r) r := by
  have heq : deriv (profile d) = fun x ↦ -Real.cosh (d - x) / Real.sinh d :=
    funext fun x ↦ (hasDerivAt_profile d x).deriv
  rw [heq]
  unfold profile
  simpa using (((hasDerivAt_id r).const_sub d).cosh.neg.div_const (Real.sinh d))

/-- The flux derivative for a real solution of the differential equation h'' = h
and a complex multiplier. Real scalar multiplication is pointwise multiplication
by the same real number in the complex algebra. -/
theorem energy_flux_derivative {x : ℝ} {b : ℝ → ℂ} {v : ℂ} {h q : ℝ → ℝ}
    (hb : HasDerivAt b v x) (hh : HasDerivAt h (q x) x) (hq : HasDerivAt q (h x) x) :
    HasDerivAt (fun t ↦ ‖b t‖ ^ 2 * h t * q t)
      (‖h x • b x‖ ^ 2 + ‖deriv (fun t ↦ h t • b t) x‖ ^ 2 - ‖v‖ ^ 2 * h x ^ 2) x := by
  have hprod := hh.smul hb
  change HasDerivAt (fun t : ℝ ↦ h t • b t) _ _ at hprod
  rw [hprod.deriv]
  have hflux := (hb.norm_sq.mul hh).mul hq
  change HasDerivAt (fun t ↦ ‖b t‖ ^ 2 * h t * q t) _ _ at hflux
  convert hflux using 1
  simp only [norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm v (b x), Pi.mul_apply]
  ring

/-- Exact finite-gap energy. For a multiplier f take b(t) = f(t) - f(0). -/
theorem finite_gap_energy (d : ℝ) {b : ℝ → ℂ} (hb : ContDiff ℝ 1 b) (hzero : b 0 = 0) :
    (∫ t in 0..d, ‖profile d t • b t‖ ^ 2 +
      ‖deriv (fun x ↦ profile d x • b x) t‖ ^ 2) =
      ∫ t in 0..d, ‖deriv b t‖ ^ 2 * profile d t ^ 2 := by
  let h := profile d
  let g := fun t ↦ h t • b t
  let e := fun t ↦ ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2
  let w := fun t ↦ ‖deriv b t‖ ^ 2 * h t ^ 2
  have ch : ContDiff ℝ 1 h := by
    change ContDiff ℝ 1 (fun x : ℝ ↦ Real.sinh (d - x) / Real.sinh d)
    fun_prop
  have cg : ContDiff ℝ 1 g := ch.smul hb
  have ce : Continuous e := (cg.continuous.norm.pow 2).add (cg.continuous_deriv_one.norm.pow 2)
  have cw : Continuous w := (hb.continuous_deriv_one.norm.pow 2).mul (ch.continuous.pow 2)
  have hflux : (∫ t in 0..d, e t - w t) =
      ‖b d‖ ^ 2 * h d * deriv h d - ‖b 0‖ ^ 2 * h 0 * deriv h 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ energy_flux_derivative (hb.differentiable_one t).hasDerivAt
        (ch.differentiable_one t).hasDerivAt (hasDerivAt_deriv_profile d t))
      ((ce.sub cw).intervalIntegrable 0 d)
  rw [intervalIntegral.integral_sub (ce.intervalIntegrable 0 d) (cw.intervalIntegrable 0 d)] at hflux
  apply sub_eq_zero.mp
  exact hflux.trans (by simp [h, profile, hzero])

/-- Interior points of a gap lie under only its two endpoint hats. -/
theorem adjacent_profile_sum_le_one {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) (hrd : r ≤ d) :
    profile d r + profile d (d - r) ≤ 1 := by
  have hs := Real.sinh_pos_iff.mpr hd
  have hl := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hrd)
  have hrr := Real.sinh_nonneg_iff.mpr hr
  have hadd := Real.sinh_add (d - r) r
  rw [sub_add_cancel] at hadd
  unfold profile
  rw [sub_sub_cancel, ← add_div, div_le_one hs]
  nlinarith only [hadd, mul_nonneg hl (sub_nonneg.mpr (Real.one_le_cosh r)),
    mul_nonneg (sub_nonneg.mpr (Real.one_le_cosh (d - r))) hrr]

theorem adjacent_profile_sq_sum_le_one {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) (hrd : r ≤ d) :
    profile d r ^ 2 + profile d (d - r) ^ 2 ≤ 1 := by
  have ha := (profile_bounds hd hr hrd).1
  have hb := (profile_bounds hd (sub_nonneg.mpr hrd) (sub_le_self d hr)).1
  have hsum := adjacent_profile_sum_le_one hd hr hrd
  have ha₁ : 0 ≤ 1 - profile d r := by linarith only [hb, hsum]
  have hb₁ : 0 ≤ 1 - profile d (d - r) := by linarith only [ha, hsum]
  nlinarith only [mul_nonneg ha ha₁, mul_nonneg hb hb₁, hsum]

end RiemannMasullo.GeometricHat
