import research.StripJetInterpolation
import RiemannMasullo.AppB_AnalyticNT.Sec2
import RiemannMasullo.ForMathlib.Analysis.MellinTransform
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Radial realization of strip interpolants

Use the spectral coordinate `z = u - 1/2` and the radial coordinate `x = log |g|`.
The enlarged strip has real endpoints ±3 / 2. Absolute inversion on these two
lines bounds the radial representative pointwise. In particular the translated
height of a boundary envelope contributes no loss to its weighted squared norm.
The contour shift uses the project's Appendix B.2. The main theorem
`exists_sobolev_cardinal_jet` applies the construction to the interpolants
of `StripJetInterpolation.lean`.
-/

noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal FourierTransform Topology

namespace MasulloResearch.StripRadial

local notation "J" => Icc (-(3 / 2) : ℝ) (3 / 2)
local notation "line" => (fun (σ y : ℝ) ↦ (σ : ℂ) + (y : ℂ) * Complex.I)

/-- The squared radial weight of §9.2 on the interval `[-1,1]`. -/
def radialWeight (s x : ℝ) : ℝ :=
  max (Real.exp (2 * (-1) * x)) (Real.exp (2 * 1 * x)) * (1 + x ^ 2) ^ (s / 2)

/-- The remaining integrable weight after squaring the bound from the outer lines. -/
def sobolevKernel (s x : ℝ) : ℝ := (1 + x ^ 2) ^ (s / 2) * Real.exp (-|x|)

theorem integrable_sobolevKernel (s : ℝ) : Integrable (sobolevKernel s) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (s / 2)
  let k := 2 * (n + 1)
  let C : ℝ := (k.factorial : ℝ) * Real.exp 1
  have hmeas : Measurable (sobolevKernel s) := by unfold sobolevKernel; fun_prop
  refine (integrable_inv_one_add_sq.const_mul C).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  have hbase : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hpoly : (1 + x ^ 2) ^ (s / 2) ≤ (1 + x ^ 2) ^ n := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hbase hn
  have hsq : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
  have hpow : (1 + x ^ 2) ^ (n + 1) ≤ (1 + |x|) ^ k := by
    simpa only [k, pow_mul] using pow_le_pow_left₀ (by positivity) hsq (n + 1)
  have hfac := Real.pow_div_factorial_le_exp (1 + |x|) (by positivity) k
  have hbound : (1 + x ^ 2) ^ (n + 1) ≤ C * Real.exp |x| := by
    refine hpow.trans ?_
    have hf := (div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mp hfac
    rw [Real.exp_add] at hf
    dsimp [C]
    linarith only [hf, show Real.exp 1 * Real.exp |x| * k.factorial =
      (k.factorial : ℝ) * Real.exp 1 * Real.exp |x| by ring]
  rw [Real.norm_of_nonneg (by unfold sobolevKernel; positivity), sobolevKernel, Real.exp_neg,
    ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  calc
    _ ≤ (1 + x ^ 2) ^ n * (1 + x ^ 2) := by gcongr
    _ = _ := (pow_succ _ _).symm
    _ ≤ _ := hbound

private theorem exp_abs_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ ↦ Real.exp (-c * |x|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · apply (integrableOn_exp_mul_Iic hc 0).congr_fun _ measurableSet_Iic
    intro x hx
    simp [abs_of_nonpos (mem_Iic.mp hx)]
  · apply (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    simp [abs_of_pos (mem_Ioi.mp hx)]

/-- A Cauchy envelope has boundary mass at most `π C`, at every center height. -/
theorem boundary_mass {f : ℝ → ℂ} (hf : Integrable f) {C τ : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ C * (1 + (y - τ) ^ 2)⁻¹) :
    (∫ y, ‖f y‖) ≤ C * Real.pi := by
  calc
    _ ≤ ∫ y : ℝ, C * (1 + (y - τ) ^ 2)⁻¹ := integral_mono hf.norm
      ((integrable_inv_one_add_sq.comp_sub_right τ).const_mul C) hb
    _ = _ := by
      rw [integral_const_mul, integral_sub_right_eq_self (fun x : ℝ ↦ (1 + x ^ 2)⁻¹),
        integral_univ_inv_one_add_sq]

/-- The absolute inverse Mellin integral on one line, in logarithmic coordinates. -/
private theorem inverse_line_bound {F : ℂ → ℂ} (σ x : ℝ) :
    ‖mellinInv σ F (Real.exp x)‖ ≤ (1 / (2 * Real.pi)) * Real.exp (-σ * x) *
      ∫ y : ℝ, ‖F (line σ y)‖ := by
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos _)]
  simp [Real.rpow_def_of_pos (Real.exp_pos x), mul_comm]

/-- A common inverse Mellin representative on the strip. The bound involves only
the two boundary masses; the qualitative decay constant on the strip is unrestricted. -/
theorem exists_radial_representative {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' J))
    (htail : ∃ B ≥ (0 : ℝ), ∀ σ ∈ J, ∀ y : ℝ,
      ‖F (line σ y)‖ ≤ B * (1 + ‖y‖) ^ (-(2 : ℝ)))
    {A : ℝ} (hA : 0 ≤ A)
    (hedge : ∀ σ : ℝ, σ = -(3 / 2) ∨ σ = 3 / 2 →
      (∫ y : ℝ, ‖F (line σ y)‖) ≤ 2 * Real.pi * A) :
    ∃ p : ℝ → ℂ, Continuous p ∧
      (∀ x, ‖p x‖ ≤ A * Real.exp (-(3 / 2) * |x|)) ∧
      ∀ z : ℂ, |z.re| < 3 / 2 →
        MellinConvergent (fun t ↦ p (Real.log t)) z ∧
        (∫ x : ℝ, Complex.exp (z * x) * p x) = F z := by
  obtain ⟨B, hB, hb⟩ := htail
  have h0 : (0 : ℝ) ∈ J := by constructor <;> norm_num
  have hcont (σ : ℝ) (hσ : σ ∈ J) : Continuous (fun y ↦ F (line σ y)) :=
    hF.continuousOn.comp_continuous (by fun_prop) (fun _ ↦ by simpa using hσ)
  have hi (σ : ℝ) (hσ : σ ∈ J) : Complex.VerticalIntegrable F σ := by
    have hk : Integrable (fun y : ℝ ↦ (1 + ‖y‖) ^ (-(2 : ℝ))) := integrable_one_add_norm (by simp)
    exact (hk.const_mul B).mono' (hcont σ hσ).aestronglyMeasurable (ae_of_all _ (hb σ hσ))
  let p := fun x ↦ mellinInv 0 F (Real.exp x)
  have hshift (σ : ℝ) (hσ : σ ∈ J) (x : ℝ) : p x = mellinInv σ F (Real.exp x) := by
    have aux (c d : ℝ) (hc : c ∈ J) (hd : d ∈ J) (hcd : c ≤ d) :=
      RiemannMasullo.mellinInv_eq_of_verticalTrace_decay hcd
        (hF.mono (preimage_mono (Icc_subset_Icc hc.1 hd.2))) (hi c hc) (hi d hd)
        hB (by norm_num : (1 : ℝ) ≤ 2)
        (fun σ hσ ↦ hb σ (Icc_subset_Icc hc.1 hd.2 hσ)) (Real.exp_pos x)
    rcases le_total 0 σ with h | h
    · exact aux 0 σ h0 hσ h
    · exact (aux σ 0 hσ h0 h).symm
  let trace := fun (σ y : ℝ) ↦ F (line σ (2 * Real.pi * y))
  have htrace (σ : ℝ) (hσ : σ ∈ J) : Integrable (trace σ) :=
    (hi σ hσ).comp_mul_left' (by positivity : 2 * Real.pi ≠ 0)
  have hweight (σ : ℝ) (hσ : σ ∈ J) (x : ℝ) :
      (Real.exp (σ * x) : ℂ) * p x = 𝓕 (trace σ) x := by
    rw [hshift σ hσ, mellinInv_eq_fourierInv _ _ (Real.exp_pos x), Real.log_exp,
      Real.fourierInv_eq_fourier_neg, neg_neg, smul_eq_mul,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
      Complex.ofReal_mul, ← mul_assoc, ← Complex.exp_add]
    simp [trace, mul_comm (x : ℂ)]
  have hp : Continuous p := by
    have hpeq : p = 𝓕 (trace 0) := funext (fun x ↦ by simpa using hweight 0 h0 x)
    rw [hpeq]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (htrace 0 h0)
  have hdec (x : ℝ) : ‖p x‖ ≤ A * Real.exp (-(3 / 2) * |x|) := by
    have edge (σ : ℝ) (hs : σ = -(3 / 2) ∨ σ = 3 / 2) (hσ : σ ∈ J) :
        ‖p x‖ ≤ A * Real.exp (-σ * x) := by
      rw [hshift σ hσ]
      refine (inverse_line_bound σ x).trans ?_
      calc
        _ ≤ 1 / (2 * Real.pi) * Real.exp (-σ * x) * (2 * Real.pi * A) := by
          gcongr
          exact hedge σ hs
        _ = _ := by field_simp
    by_cases hx : 0 ≤ x
    · simpa [abs_of_nonneg hx] using edge (3 / 2) (Or.inr rfl) ⟨by norm_num, le_rfl⟩
    · simpa [abs_of_neg (lt_of_not_ge hx)] using edge (-(3 / 2)) (Or.inl rfl) ⟨le_rfl, by norm_num⟩
  refine ⟨p, hp, hdec, ?_⟩
  intro z hz
  have hσ := abs_lt.mp hz
  have hσJ : z.re ∈ J := ⟨hσ.1.le, hσ.2.le⟩
  have hwint : Integrable (fun x ↦ (Real.exp (z.re * x) : ℂ) * p x) := by
    apply ((exp_abs_integrable (sub_pos.mpr hz)).const_mul A).mono' (by fun_prop)
    filter_upwards with x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ Real.exp (z.re * x) * (A * Real.exp (-(3 / 2) * |x|)) := by gcongr; exact hdec x
      _ = A * Real.exp (z.re * x - 3 / 2 * |x|) := by rw [sub_eq_add_neg, ← neg_mul, Real.exp_add]; ring
      _ ≤ _ := by
        gcongr
        have hzx := (le_abs_self (z.re * x)).trans_eq (abs_mul _ _)
        linarith only [hzx, show -(3 / 2 - |z.re|) * |x| = |z.re| * |x| - 3 / 2 * |x| by ring]
  refine ⟨RiemannMasullo.mellinConvergent_of_integrable_logWeight p z hwint, ?_⟩
  rw [← RiemannMasullo.mellin_logProfile_eq, mellin_eq_fourier]
  have hf : (fun u : ℝ ↦ Real.exp (-z.re * u) • p (Real.log (Real.exp (-u)))) = 𝓕⁻ (trace z.re) := by
    funext u
    rw [Real.log_exp, Complex.real_smul, neg_mul, ← mul_neg, Real.fourierInv_eq_fourier_neg]
    exact hweight z.re hσJ (-u)
  have ht : Continuous (trace z.re) := (hcont z.re hσJ).comp (by fun_prop)
  have hft : Integrable (𝓕 (trace z.re)) := by
    apply hwint.congr
    exact ae_of_all _ (hweight z.re hσJ)
  rw [hf, ht.fourier_fourierInv_eq (htrace z.re hσJ) hft]
  change F (line z.re (2 * Real.pi * (z.im / (2 * Real.pi)))) = F z
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity : 2 * Real.pi ≠ 0)]
  exact congrArg F (Complex.re_add_im z)

/-- Lebesgue measure with the squared interval-Sobolev weight in log norm. -/
def radialMeasure (s : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (radialWeight s x))

/-- Pointwise decay yields a bound on the actual norm of the weighted L² class.
The constant multiplying `A²` depends only on the Sobolev exponent. -/
theorem radial_sobolev_bound {p : ℝ → ℂ} (hp : Continuous p) {A : ℝ}
    (hdec : ∀ x, ‖p x‖ ≤ A * Real.exp (-(3 / 2) * |x|)) (s : ℝ) :
    ∃ h : MemLp p 2 (radialMeasure s),
      ‖h.toLp p‖ ^ 2 ≤ A ^ 2 * ∫ x, sobolevKernel s x := by
  have hw (x : ℝ) : 0 ≤ radialWeight s x := by unfold radialWeight; positivity
  have hwm : Measurable (fun x ↦ ENNReal.ofReal (radialWeight s x)) := by
    unfold radialWeight
    fun_prop
  have he (x : ℝ) :
      ‖p x‖ ^ 2 * radialWeight s x ≤ A ^ 2 * sobolevKernel s x := by
    have hw' : max (Real.exp (2 * (-1) * x)) (Real.exp (2 * 1 * x)) =
        Real.exp (2 * |x|) := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx, max_eq_right (Real.exp_le_exp.mpr (by linarith))]
        ring_nf
      · rw [abs_of_nonpos hx, max_eq_left (Real.exp_le_exp.mpr (by linarith))]
        ring_nf
    calc
      _ ≤ (A * Real.exp (-(3 / 2) * |x|)) ^ 2 * radialWeight s x := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hdec x) 2) (hw x)
      _ = A ^ 2 * sobolevKernel s x := by
        rw [radialWeight, hw', sobolevKernel, mul_pow, ← Real.exp_nat_mul]
        norm_num only [Nat.cast_ofNat]
        rw [show (2 : ℝ) * (-(3 / 2) * |x|) = -3 * |x| by ring]
        rw [show -|x| = -3 * |x| + 2 * |x| by ring, Real.exp_add]
        ring
  have hdom := (integrable_sobolevKernel s).const_mul (A ^ 2)
  have hmeas : Measurable (fun x ↦ ‖p x‖ ^ 2 * radialWeight s x) := by
    unfold radialWeight
    fun_prop
  have hi : Integrable (fun x ↦ ‖p x‖ ^ 2 * radialWeight s x) :=
    hdom.mono' hmeas.aestronglyMeasurable <| ae_of_all _ fun x ↦
      (Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hw x))).le.trans (he x)
  have h : MemLp p 2 (radialMeasure s) := by
    apply (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mpr
    rw [radialMeasure, integrable_withDensity_iff hwm (by simp)]
    simpa only [ENNReal.toReal_ofReal (hw _)] using hi
  refine ⟨h, ?_⟩
  calc
    ‖h.toLp p‖ ^ 2 = ∫ x, ‖p x‖ ^ 2 ∂radialMeasure s := by
      rw [← L2.integral_sq_norm (𝕜 := ℂ)]
      exact integral_congr_ae (h.coeFn_toLp.mono fun _ hx ↦ congrArg (fun v : ℂ ↦ ‖v‖ ^ 2) hx)
    _ = ∫ x, ‖p x‖ ^ 2 * radialWeight s x := by
      rw [radialMeasure, integral_withDensity_eq_integral_toReal_smul hwm (by simp)]
      simp only [ENNReal.toReal_ofReal (hw _), smul_eq_mul, mul_comm]
    _ ≤ ∫ x, A ^ 2 * sobolevKernel s x := integral_mono hi hdom he
    _ = _ := integral_const_mul _ _

/-- A boundary envelope centered at an arbitrary ordinate gives a radial L²
representative with that same linear scale. Mellin inversion recovers the input
throughout the open strip, so in particular it recovers all its interior jets. -/
theorem exists_sobolev_representative {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' J))
    (htail : ∃ B ≥ (0 : ℝ), ∀ σ ∈ J, ∀ y : ℝ,
      ‖F (line σ y)‖ ≤ B * (1 + ‖y‖) ^ (-(2 : ℝ)))
    {C τ : ℝ} (hC : 0 ≤ C)
    (hedge : ∀ σ : ℝ, σ = -(3 / 2) ∨ σ = 3 / 2 → ∀ y : ℝ,
      ‖F (line σ y)‖ ≤ C * (1 + (y - τ) ^ 2)⁻¹) (s : ℝ) :
    ∃ (p : ℝ → ℂ) (h : MemLp p 2 (radialMeasure s)), Continuous p ∧
      ‖h.toLp p‖ ^ 2 ≤ (C / 2) ^ 2 * ∫ x, sobolevKernel s x ∧
      ∀ z : ℂ, |z.re| < 3 / 2 →
        MellinConvergent (fun t ↦ p (Real.log t)) z ∧
        (∫ x : ℝ, Complex.exp (z * x) * p x) = F z := by
  have hmass (σ : ℝ) (hσ : σ = -(3 / 2) ∨ σ = 3 / 2) :
      (∫ y, ‖F (line σ y)‖) ≤ 2 * Real.pi * (C / 2) := by
    have hj : σ ∈ J := by rcases hσ with rfl | rfl <;> constructor <;> norm_num
    have hc : Continuous (fun y ↦ F (line σ y)) :=
      hF.continuousOn.comp_continuous (by fun_prop) (fun _ ↦ by simpa using hj)
    have hi := ((integrable_inv_one_add_sq.comp_sub_right τ).const_mul C).mono'
      hc.aestronglyMeasurable (ae_of_all _ (hedge σ hσ))
    exact (boundary_mass hi (hedge σ hσ)).trans_eq (by ring)
  obtain ⟨p, hp, hdec, hmellin⟩ := exists_radial_representative hF htail (by positivity) hmass
  obtain ⟨h, hbound⟩ := radial_sobolev_bound hp hdec s
  exact ⟨p, h, hp, hbound, hmellin⟩

/-- The constant used to justify a contour shift may depend on the height and on
values inside the unit disk. Only the translated exterior bound is needed quantitatively. -/
private theorem tail_of_exterior {H : ℂ → ℂ} (hc : ContinuousOn H (Complex.re ⁻¹' J))
    (a : ℂ) {K : ℝ} (hK : 0 ≤ K) (hout : ∀ σ ∈ J, ∀ y : ℝ, 1 ≤ ‖line σ y - a‖ →
      ‖H (line σ y)‖ ≤ K * (1 + (y - a.im) ^ 2)⁻¹) :
    ∃ B ≥ (0 : ℝ), ∀ σ ∈ J, ∀ y : ℝ, ‖H (line σ y)‖ ≤ B * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  let S := J ×ˢ Icc (a.im - 1) (a.im + 1)
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  let f := fun p : ℝ × ℝ ↦ ‖H (line p.1 p.2)‖ * (1 + ‖p.2‖) ^ 2
  have hh : ContinuousOn (fun p : ℝ × ℝ ↦ H (line p.1 p.2)) S :=
    hc.comp (by fun_prop) (fun p hp ↦ by simpa using hp.1)
  have hf : ContinuousOn f S := hh.norm.mul
    (((continuous_const.add continuous_snd.norm).pow 2).continuousOn)
  obtain ⟨b, hb⟩ := hS.bddAbove_image hf
  let D := 2 * (1 + |a.im|) ^ 2
  refine ⟨max (max b 0) (K * D), (le_max_right b 0).trans (le_max_left _ _), ?_⟩
  intro σ hσ y
  rw [Real.rpow_neg (by positivity), Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  by_cases hy : y ∈ Icc (a.im - 1) (a.im + 1)
  · exact (hb (mem_image_of_mem f (show (σ, y) ∈ S from ⟨hσ, hy⟩))).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  · have hy' : 1 ≤ |y - a.im| := by
      by_contra! h
      exact hy ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩
    have hz : 1 ≤ ‖line σ y - a‖ := hy'.trans (by simpa using Complex.abs_im_le_norm (line σ y - a))
    have hab : 1 + ‖y‖ ≤ (1 + |a.im|) * (1 + |y - a.im|) := by
      have h := abs_add_le (y - a.im) a.im
      rw [sub_add_cancel] at h
      rw [Real.norm_eq_abs]
      nlinarith [mul_nonneg (abs_nonneg a.im) (abs_nonneg (y - a.im))]
    have hs : (1 + |y - a.im|) ^ 2 ≤ 2 * (1 + (y - a.im) ^ 2) := by
      nlinarith [sq_abs (y - a.im), sq_nonneg (|y - a.im| - 1)]
    have hscale : (1 + ‖y‖) ^ 2 ≤ D * (1 + (y - a.im) ^ 2) := by
      refine (pow_le_pow_left₀ (by positivity) hab 2).trans ?_
      rw [mul_pow]
      exact (mul_le_mul_of_nonneg_left hs (sq_nonneg _)).trans_eq (by dsimp [D]; ring)
    apply le_trans _ (le_max_right _ _)
    calc
      _ ≤ (K * (1 + (y - a.im) ^ 2)⁻¹) * (D * (1 + (y - a.im) ^ 2)) :=
        mul_le_mul (hout σ hσ y hz) hscale (sq_nonneg _) (by positivity)
      _ = _ := by field_simp

/-- Construct a weighted radial representative for a specified derivative at `a`
from the divisor in local coordinates. All other interior zero orders are
preserved. The norm bound retains the full inverse factorial. -/
theorem exists_sobolev_cardinal_jet {F : ℂ → ℂ} {D : Set ℂ} (hF : AnalyticOnNhd ℂ F D)
    (a : ℂ) (ha : |a.re| ≤ 1 / 2) (hdisk : Metric.closedBall (0 : ℂ) 1 ⊆ D)
    (hstrip : ∀ z : ℂ, z.re ∈ J → z - a ∈ D)
    {k m : ℕ} (hk : k < m) (hm : analyticOrderAt F 0 = m)
    {r U : ℝ} (hr : 0 < r) (hr2 : 2 * r ≤ 1)
    (hiso : ∀ v ∈ Metric.ball 0 (2 * r), v ≠ 0 → F v ≠ 0)
    (hU : ∀ v ∈ Metric.sphere (0 : ℂ) 1, ‖F v‖ ≤ U)
    (hU0 : ‖iteratedDeriv m F 0 / (m.factorial : ℂ)‖ < U)
    {C : ℝ} (hC : 0 ≤ C) (hdiv : ∀ σ ∈ J, ∀ y : ℝ, 1 ≤ ‖line σ y - a‖ →
      ‖F (line σ y - a)‖ ≤ C * (1 + (y - a.im) ^ 2)⁻¹) (s : ℝ) :
    let K := (m - k : ℕ) * (U ^ 2 / ‖iteratedDeriv m F 0 / (m.factorial : ℂ)‖ ^ 3 / r ^ m) *
      C / (k.factorial : ℝ)
    ∃ (p : ℝ → ℂ) (h : MemLp p 2 (radialMeasure s)), Continuous p ∧
      ‖h.toLp p‖ ^ 2 ≤ (K / 2) ^ 2 * ∫ x, sobolevKernel s x ∧
      (∀ z : ℂ, |z.re| < 3 / 2 → MellinConvergent (fun t ↦ p (Real.log t)) z) ∧
      let M := fun v : ℂ ↦ ∫ x : ℝ, Complex.exp ((v + a) * x) * p x
      (∀ j < m, iteratedDeriv j M 0 = if j = k then 1 else 0) ∧
      ∀ v : ℂ, |(v + a).re| < 3 / 2 → v ≠ 0 → analyticOrderAt F v ≤ analyticOrderAt M v := by
  intro K
  obtain ⟨H, hH, hjet, hother, hext⟩ :=
    StripJets.exists_cardinal_interpolant hF hdisk hk hm hr hr2 hiso hU hU0
  let G := fun z ↦ H (z - a)
  have hG : DifferentiableOn ℂ G (Complex.re ⁻¹' J) :=
    hH.differentiableOn.comp (differentiable_id.sub_const a).differentiableOn hstrip
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hGbound (σ : ℝ) (hσ : σ ∈ J) (y : ℝ) (hv : 1 ≤ ‖line σ y - a‖) :
      ‖G (line σ y)‖ ≤ K * (1 + (y - a.im) ^ 2)⁻¹ := by
    apply (hext _ (hstrip _ (by simpa using hσ)) hv).trans
    dsimp [K]
    calc
      _ ≤ (m - k : ℕ) * (U ^ 2 / ‖iteratedDeriv m F 0 / (m.factorial : ℂ)‖ ^ 3 / r ^ m) *
          (C * (1 + (y - a.im) ^ 2)⁻¹) / (k.factorial : ℝ) := by gcongr; exact hdiv σ hσ y hv
      _ = _ := by ring
  have hedge (σ : ℝ) (hσ : σ = -(3 / 2) ∨ σ = 3 / 2) (y : ℝ) :
      ‖G (line σ y)‖ ≤ K * (1 + (y - a.im) ^ 2)⁻¹ := by
    have hj : σ ∈ J := by rcases hσ with rfl | rfl <;> constructor <;> norm_num
    apply hGbound σ hj y
    apply le_trans _ (Complex.abs_re_le_norm _)
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
      Complex.ofReal_im, neg_zero, add_zero]
    rcases hσ with rfl | rfl
    · exact (neg_le_abs _).trans' (by linarith [(abs_le.mp ha).1])
    · exact (le_abs_self _).trans' (by linarith [(abs_le.mp ha).2])
  obtain ⟨p, h, hp, hnorm, hrec⟩ := exists_sobolev_representative hG
    (tail_of_exterior hG.continuousOn a hK hGbound) hK hedge s
  refine ⟨p, h, hp, hnorm, fun z hz ↦ (hrec z hz).1, ?_⟩
  let M := fun v : ℂ ↦ ∫ x : ℝ, Complex.exp ((v + a) * x) * p x
  have hlocal (v : ℂ) (hv : |(v + a).re| < 3 / 2) : M =ᶠ[𝓝 v] H := by
    have hopen : IsOpen {w : ℂ | |(w + a).re| < 3 / 2} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hv] with w hw
    simpa only [M, G, add_sub_cancel_right] using (hrec (w + a) hw).2
  have hzero := hlocal 0 (by simpa using ha.trans_lt (by norm_num : (1 / 2 : ℝ) < 3 / 2))
  refine ⟨fun j hj ↦ (hzero.iteratedDeriv_eq j).trans (hjet j hj), ?_⟩
  intro v hv hne
  rw [analyticOrderAt_congr (hlocal v hv)]
  have hvD := hstrip (v + a) (show (v + a).re ∈ J from ⟨(abs_lt.mp hv).1.le, (abs_lt.mp hv).2.le⟩)
  exact hother v (by simpa using hvD) hne

end MasulloResearch.StripRadial
