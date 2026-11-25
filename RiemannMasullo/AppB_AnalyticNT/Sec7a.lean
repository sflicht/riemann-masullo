module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import Mathlib.Algebra.Order.Round
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import RiemannMasullo.ForMathlib.Analysis.Complex.RectangleIntegral

/-!
# Logarithmic derivatives and Perron's formula on the 1-line

Masullo, §B.7.1, pp. 643–648. The finite Hecke L-function on the boundary is
represented by a meromorphic continuation in normal form, as in §B.6.
-/

@[expose] public noncomputable section

open Filter NumberField Set
open scoped Asymptotics Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "oneLine" => Complex.re ⁻¹' ({1} : Set ℝ)

/-- Paper: Equation (B.7.1.1), p. 643. The twisted ideal von Mangoldt series
converges absolutely to the negative logarithmic derivative to the right of one. -/
theorem finiteHeckeL_negLogDeriv_hasSum_ideals (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : halfPlane) :
    HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
      heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val /
        (I.val.absNorm : ℂ) ^ (s : ℂ)) (-logDeriv L s) := by
  simpa only [neg_div, neg_neg] using (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries s).2.2.neg

/-- Paper: Equations (B.7.1.4)–(B.7.1.5), p. 644. This is the normalized integral
of `f(s+w) x^w / w` up the segment from `c - iT` to `c + iT`. The factor
`i` in the path derivative cancels the `i` in the normalization. -/
def truncatedPerronIntegral (f : ℂ → ℂ) (s : ℂ) (x c T : ℝ) : ℂ :=
  (∫ t in -T..T, f (s + ⟨c, t⟩) * (x : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
    (2 * (Real.pi : ℂ))

/-- Paper: Equation (B.7.1.7), p. 645. At the endpoint, the integral of the
constant series at cutoff one gives the arctangent factor. -/
theorem truncatedPerronIntegral_one (s : ℂ) {c T : ℝ} (hc : 0 < c) :
    truncatedPerronIntegral (fun _ ↦ 1) s 1 c T = (Real.arctan (T / c) / Real.pi : ℝ) := by
  have hz : ∀ t : ℝ, (⟨c, t⟩ : ℂ) ≠ 0 := fun t h ↦ hc.ne' (congrArg Complex.re h)
  have hinv : ∀ t : ℝ, 1 / (⟨c, t⟩ : ℂ) =
      ((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) - Complex.I * ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    intro t
    rw [one_div]
    apply Complex.ext <;>
      simp only [Complex.inv_re, Complex.inv_im, Complex.normSq_mk, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im] <;>
      ring
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ ↦ (Real.arctan (t / c) : ℂ) - Complex.I * (Real.log (c ^ 2 + t ^ 2) / 2 : ℝ))
      (1 / (⟨c, t⟩ : ℂ)) t := by
    intro t
    have hpos : 0 < c ^ 2 + t ^ 2 := by positivity
    have h1 := ((hasDerivAt_id' t).div_const c).arctan.ofReal_comp
    have h2 := ((((hasDerivAt_pow 2 t).const_add (c ^ 2)).log hpos.ne').div_const 2).ofReal_comp
    convert h1.sub (h2.const_mul Complex.I) using 1
    rw [hinv t]
    congr 3
    · field_simp
    · field_simp
      ring
  have hcont : Continuous fun t : ℝ ↦ 1 / (⟨c, t⟩ : ℂ) := by
    refine continuous_const.div ?_ hz
    rw [show Complex.mk c = fun t : ℝ ↦ (c : ℂ) + (t : ℂ) * Complex.I from
      funext fun t ↦ Complex.mk_eq_add_mul_I c t]
    fun_prop
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  show (∫ t in -T..T, (1 : ℂ) * ((1 : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
    (2 * (Real.pi : ℂ)) = _
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (hcont.intervalIntegrable _ _)]
  simp only [neg_div, Real.arctan_neg, neg_sq, Complex.ofReal_neg]
  push_cast
  field_simp
  ring

/-- Paper: Lemma B.7.1.1, pp. 644–645. This sums the Dirichlet terms for positive
integers up to the real cutoff, with half weight when the cutoff is an integer. -/
def perronHalfWeightedSum (a : ℕ → ℂ) (s : ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    if (n : ℝ) = x then LSeries.term a s n / 2 else LSeries.term a s n

/-- Paper: Equation (B.7.1.5), p. 644. At a positive integer cutoff, the terms
strictly below the cutoff have full weight and the last term has half weight. -/
theorem perronHalfWeightedSum_nat (a : ℕ → ℂ) (s : ℂ) {m : ℕ} (hm : 0 < m) :
    perronHalfWeightedSum a s m =
      (∑ n ∈ Finset.Ico 1 m, LSeries.term a s n) + LSeries.term a s m / 2 := by
  show (∑ n ∈ Finset.Icc 1 ⌊(m : ℝ)⌋₊,
      if (n : ℝ) = m then LSeries.term a s n / 2 else LSeries.term a s n) = _
  rw [Nat.floor_natCast, Finset.Icc_eq_cons_Ico hm, Finset.sum_cons, ite_eq_left rfl, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun n hn ↦ ite_eq_right ?_
  exact_mod_cast (Finset.mem_Ico.mp hn).2.ne

/-- A horizontal edge at height `±T`: the integral of `y^w / w` is at most the integral
of `y^u / T`. -/
private theorem truncatedPerron_error_horizontal {y T τ a b : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
    (hT : 0 < T) (hτ : |τ| = T) (hab : a ≤ b) :
    ‖∫ u in a..b, (y : ℂ) ^ (⟨u, τ⟩ : ℂ) / (⟨u, τ⟩ : ℂ)‖ ≤
      (y ^ b - y ^ a) / (T * Real.log y) := by
  have hlog : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
  have hpt : ∀ u : ℝ, u ∈ Ioc a b →
      ‖(y : ℂ) ^ (⟨u, τ⟩ : ℂ) / (⟨u, τ⟩ : ℂ)‖ ≤ y ^ u / T := by
    intro u _
    have hn : T ≤ ‖(⟨u, τ⟩ : ℂ)‖ := by
      have h := Complex.abs_im_le_norm (⟨u, τ⟩ : ℂ)
      rwa [show (⟨u, τ⟩ : ℂ).im = τ from rfl, hτ] at h
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, show (⟨u, τ⟩ : ℂ).re = u from rfl]
    exact div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hy u).le hT hn
  have hderiv : ∀ u ∈ uIcc a b,
      HasDerivAt (fun u : ℝ ↦ y ^ u / (T * Real.log y)) (y ^ u / T) u := by
    intro u _
    have h1 := (Real.hasStrictDerivAt_const_rpow hy u).hasDerivAt.div_const (T * Real.log y)
    refine h1.congr_deriv ?_
    field_simp
  have hcont : Continuous fun u : ℝ ↦ y ^ u / T :=
    (Real.continuous_const_rpow hy.ne').div_const T
  have hle : ‖∫ u in a..b, (y : ℂ) ^ (⟨u, τ⟩ : ℂ) / (⟨u, τ⟩ : ℂ)‖ ≤ ∫ u in a..b, y ^ u / T :=
    intervalIntegral.norm_integral_le_of_norm_le hab (Eventually.of_forall hpt)
      (hcont.intervalIntegrable _ _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
    at hle
  rwa [← sub_div] at hle

/-- The rectangle identity bounds one vertical edge by the other three. -/
private theorem truncatedPerron_error_rect_norm {A₁ A₂ V J : ℂ}
    (h : A₁ - A₂ + Complex.I • V - Complex.I • J = 0) : ‖J‖ ≤ ‖A₁‖ + ‖A₂‖ + ‖V‖ := by
  have hJ : Complex.I * J = A₁ - A₂ + Complex.I * V := by
    simp only [smul_eq_mul] at h
    linear_combination (-1 : ℂ) * h
  calc ‖J‖ = ‖Complex.I * J‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ = ‖A₁ - A₂ + Complex.I * V‖ := by rw [hJ]
    _ ≤ ‖A₁‖ + ‖A₂‖ + ‖V‖ := by
        refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
        rw [norm_mul, Complex.norm_I, one_mul]

/-- Perron's kernel for `y < 1`: shifting the segment to the right. -/
private theorem truncatedPerron_error_lt_one {y c T : ℝ} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)‖ ≤
      2 * y ^ c / (T * |Real.log y|) := by
  have hlog : Real.log y < 0 := Real.log_neg hy hy1
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨U, hUc, hUε⟩ : ∃ U : ℝ, c < U ∧ 2 * T / ε ≤ U :=
    ⟨max (c + 1) (2 * T / ε), lt_max_of_lt_left (lt_add_one c), le_max_right _ _⟩
  have hU0 : 0 < U := hc.trans hUc
  have H : DifferentiableOn ℂ (fun w : ℂ ↦ (y : ℂ) ^ w / w)
      (uIcc (⟨c, -T⟩ : ℂ).re (⟨U, T⟩ : ℂ).re ×ℂ uIcc (⟨c, -T⟩ : ℂ).im (⟨U, T⟩ : ℂ).im) := by
    intro w hw
    have hre : c ≤ w.re := by
      have h1 : w.re ∈ uIcc c U := hw.1
      rw [uIcc_of_le hUc.le] at h1
      exact h1.1
    have hw0 : w ≠ 0 := fun h ↦ by
      rw [h, Complex.zero_re] at hre
      linarith
    exact ((differentiableAt_id.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).div differentiableAt_id
        hw0).differentiableWithinAt
  have rect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ _ _ H
  dsimp only at rect
  simp only [← Complex.mk_eq_add_mul_I] at rect
  have hJ := truncatedPerron_error_rect_norm rect
  have hA₁ := truncatedPerron_error_horizontal hy hy1.ne hT (τ := -T)
    (by rw [abs_neg, abs_of_pos hT]) hUc.le
  have hA₂ := truncatedPerron_error_horizontal hy hy1.ne hT (τ := T) (abs_of_pos hT) hUc.le
  have hV : ‖∫ t in -T..T, (y : ℂ) ^ (⟨U, t⟩ : ℂ) / (⟨U, t⟩ : ℂ)‖ ≤ 1 / U * |T - -T| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    have hn : U ≤ ‖(⟨U, t⟩ : ℂ)‖ := by
      have h := Complex.abs_re_le_norm (⟨U, t⟩ : ℂ)
      rwa [show (⟨U, t⟩ : ℂ).re = U from rfl, abs_of_pos hU0] at h
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, show (⟨U, t⟩ : ℂ).re = U from rfl]
    exact div_le_div₀ zero_le_one (Real.rpow_le_one hy.le hy1.le hU0.le) hU0 hn
  have hTl : 0 < T * -Real.log y := mul_pos hT (by linarith)
  have hb : (y ^ U - y ^ c) / (T * Real.log y) ≤ y ^ c / (T * |Real.log y|) := by
    have e : (y ^ U - y ^ c) / (T * Real.log y) = (y ^ c - y ^ U) / (T * -Real.log y) := by
      rw [mul_neg, ← neg_sub (y ^ U) (y ^ c), neg_div_neg_eq]
    rw [e, abs_of_neg hlog]
    exact div_le_div_of_nonneg_right (by linarith [Real.rpow_pos_of_pos hy U]) hTl.le
  have hε' : 1 / U * |T - -T| ≤ ε := by
    rw [sub_neg_eq_add, abs_of_pos (by linarith), one_div, inv_mul_le_iff₀ hU0]
    have := (div_le_iff₀ hε).mp hUε
    linarith
  have hsplit : 2 * y ^ c / (T * |Real.log y|) =
      y ^ c / (T * |Real.log y|) + y ^ c / (T * |Real.log y|) := by ring
  rw [hsplit]
  linarith

/-- Along a path that avoids the origin, the divided difference of `y^w` at `0` splits
into `y^w / w` and `1 / w`. -/
private theorem truncatedPerron_error_dslope_path {y : ℝ} (hy : 0 < y) {γ : ℝ → ℂ}
    (hγ : Continuous γ) (h0 : ∀ u, γ u ≠ 0) (a b : ℝ) :
    ∫ u in a..b, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (γ u) =
      (∫ u in a..b, (y : ℂ) ^ (γ u) / γ u) - ∫ u in a..b, 1 / γ u := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have h1 : Continuous fun u : ℝ ↦ (y : ℂ) ^ (γ u) / γ u :=
    (hγ.const_cpow (Or.inl hy0)).div hγ h0
  have h2 : Continuous fun u : ℝ ↦ 1 / γ u := continuous_const.div hγ h0
  rw [← intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun u _ ↦ ?_
  change dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (γ u) = (y : ℂ) ^ (γ u) / γ u - 1 / γ u
  rw [dslope_of_ne _ (h0 u), slope_def_field, Complex.cpow_zero, sub_zero, sub_div]

/-- The integral of `1 / w` along a horizontal segment off the real axis. -/
private theorem truncatedPerron_error_inv_horizontal {τ a b : ℝ} (hτ : τ ≠ 0) :
    ∫ u in a..b, 1 / (⟨u, τ⟩ : ℂ) =
      ((Real.log (b ^ 2 + τ ^ 2) / 2 - Real.log (a ^ 2 + τ ^ 2) / 2 : ℝ) : ℂ) -
        Complex.I * ((Real.arctan (b / τ) - Real.arctan (a / τ) : ℝ) : ℂ) := by
  have hτ2 : 0 < τ ^ 2 := by positivity
  have hpos : ∀ u : ℝ, 0 < u ^ 2 + τ ^ 2 := fun u ↦ by positivity
  have hz : ∀ u : ℝ, (⟨u, τ⟩ : ℂ) ≠ 0 := fun u h ↦ hτ (congrArg Complex.im h)
  have hinv : ∀ u : ℝ, 1 / (⟨u, τ⟩ : ℂ) =
      ((u / (u ^ 2 + τ ^ 2) : ℝ) : ℂ) - Complex.I * ((τ / (u ^ 2 + τ ^ 2) : ℝ) : ℂ) := by
    intro u
    rw [one_div]
    apply Complex.ext <;>
      simp only [Complex.inv_re, Complex.inv_im, Complex.normSq_mk, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im] <;>
      ring
  have hderiv : ∀ u ∈ uIcc a b, HasDerivAt
      (fun u : ℝ ↦ ((Real.log (u ^ 2 + τ ^ 2) / 2 : ℝ) : ℂ) -
        Complex.I * ((Real.arctan (u / τ) : ℝ) : ℂ)) (1 / (⟨u, τ⟩ : ℂ)) u := by
    intro u _
    have hne := (hpos u).ne'
    have h1 : HasDerivAt (fun u : ℝ ↦ ((Real.log (u ^ 2 + τ ^ 2) / 2 : ℝ) : ℂ))
        ((u / (u ^ 2 + τ ^ 2) : ℝ) : ℂ) u := by
      have h := (((hasDerivAt_pow 2 u).add_const (τ ^ 2)).log hne).div_const 2
      refine (h.congr_deriv ?_).ofReal_comp
      rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, Nat.cast_ofNat]
      field_simp
    have h2 : HasDerivAt (fun u : ℝ ↦ ((Real.arctan (u / τ) : ℝ) : ℂ))
        ((τ / (u ^ 2 + τ ^ 2) : ℝ) : ℂ) u := by
      have h := ((hasDerivAt_id' u).div_const τ).arctan
      refine (h.congr_deriv ?_).ofReal_comp
      field_simp
      ring
    rw [hinv u]
    exact h1.sub (h2.const_mul Complex.I)
  have hcont : Continuous fun u : ℝ ↦ 1 / (⟨u, τ⟩ : ℂ) := by
    refine continuous_const.div ?_ hz
    rw [show (fun u : ℝ ↦ (⟨u, τ⟩ : ℂ)) = fun u : ℝ ↦ (u : ℂ) + (τ : ℂ) * Complex.I from
      funext fun u ↦ Complex.mk_eq_add_mul_I u τ]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  push_cast
  ring

/-- Perron's kernel for `y > 1`: shifting the segment to the left across the pole at `0`. -/
private theorem truncatedPerron_error_gt_one {y c T : ℝ} (hy1 : 1 < y) (hc : 0 < c)
    (hT : 0 < T) :
    ‖(2 * Real.pi : ℂ) - ∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)‖ ≤
      2 * y ^ c / (T * Real.log y) := by
  have hy : 0 < y := zero_lt_one.trans hy1
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hlog : 0 < Real.log y := Real.log_pos hy1
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨U, hU0, hUε⟩ : ∃ U : ℝ, 0 < U ∧ 6 * T / ε ≤ U :=
    ⟨max 1 (6 * T / ε), lt_max_of_lt_left one_pos, le_max_right _ _⟩
  have hdiff : Differentiable ℂ (dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0) := by
    have h1 : Differentiable ℂ fun w : ℂ ↦ (y : ℂ) ^ w :=
      differentiable_id.const_cpow (Or.inl hy0)
    have h2 := (Complex.differentiableOn_dslope (c := (0 : ℂ)) univ_mem).mpr h1.differentiableOn
    exact differentiableOn_univ.mp h2
  have rect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0) ⟨-U, -T⟩ ⟨c, T⟩ hdiff.differentiableOn
  dsimp only at rect
  simp only [← Complex.mk_eq_add_mul_I] at rect
  have hmkh : ∀ τ : ℝ, Continuous fun u : ℝ ↦ (⟨u, τ⟩ : ℂ) := fun τ ↦ by
    rw [show (fun u : ℝ ↦ (⟨u, τ⟩ : ℂ)) = fun u : ℝ ↦ (u : ℂ) + (τ : ℂ) * Complex.I from
      funext fun u ↦ Complex.mk_eq_add_mul_I u τ]
    fun_prop
  have hmkv : ∀ ρ : ℝ, Continuous fun t : ℝ ↦ (⟨ρ, t⟩ : ℂ) := fun ρ ↦ by
    rw [show (fun t : ℝ ↦ (⟨ρ, t⟩ : ℂ)) = fun t : ℝ ↦ (ρ : ℂ) + (t : ℂ) * Complex.I from
      funext fun t ↦ Complex.mk_eq_add_mul_I ρ t]
    fun_prop
  have hTne : T ≠ 0 := hT.ne'
  rw [truncatedPerron_error_dslope_path hy (hmkh (-T))
      (fun u h ↦ hTne (neg_eq_zero.mp (congrArg Complex.im h))) (-U) c,
    truncatedPerron_error_dslope_path hy (hmkh T)
      (fun u h ↦ hTne (congrArg Complex.im h)) (-U) c,
    truncatedPerron_error_dslope_path hy (hmkv c)
      (fun t h ↦ hc.ne' (congrArg Complex.re h)) (-T) T,
    truncatedPerron_error_inv_horizontal (neg_ne_zero.mpr hTne),
    truncatedPerron_error_inv_horizontal hTne] at rect
  have hS : ∫ t in -T..T, 1 / (⟨c, t⟩ : ℂ) = ((2 * Real.arctan (T / c) : ℝ) : ℂ) := by
    have h : (∫ t in -T..T, (1 : ℂ) * ((1 : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
        (2 * (Real.pi : ℂ)) = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) :=
      truncatedPerronIntegral_one (0 : ℂ) hc
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at h
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [div_eq_iff (mul_ne_zero two_ne_zero hπ)] at h
    rw [h]
    push_cast
    field_simp
  have hpi1 : Real.arctan (T / c) = Real.pi / 2 - Real.arctan (c / T) := by
    rw [← Real.arctan_inv_of_pos (div_pos hc hT), inv_div]
  have hpi2 : Real.arctan (U / T) = Real.pi / 2 - Real.arctan (T / U) := by
    rw [← Real.arctan_inv_of_pos (div_pos hT hU0), inv_div]
  rw [hS] at rect
  simp only [div_neg, neg_div, Real.arctan_neg, neg_sq] at rect
  rw [hpi1, hpi2] at rect
  have key : Complex.I * ((2 * Real.pi : ℂ) -
      ∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) =
      (∫ u in -U..c, (y : ℂ) ^ (⟨u, -T⟩ : ℂ) / (⟨u, -T⟩ : ℂ)) -
      (∫ u in -U..c, (y : ℂ) ^ (⟨u, T⟩ : ℂ) / (⟨u, T⟩ : ℂ)) +
      Complex.I * ((2 * Real.arctan (T / U) : ℝ) : ℂ) -
      Complex.I * ∫ t in -T..T, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (⟨-U, t⟩ : ℂ) := by
    simp only [smul_eq_mul] at rect
    push_cast at rect ⊢
    linear_combination (-1 : ℂ) * rect
  have hP₁ := truncatedPerron_error_horizontal hy hy1.ne' hT (τ := -T)
    (by rw [abs_neg, abs_of_pos hT]) (show -U ≤ c by linarith)
  have hP₂ := truncatedPerron_error_horizontal hy hy1.ne' hT (τ := T) (abs_of_pos hT)
    (show -U ≤ c by linarith)
  have hW : ‖∫ t in -T..T, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (⟨-U, t⟩ : ℂ)‖ ≤
      2 / U * |T - -T| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    have hne : (⟨-U, t⟩ : ℂ) ≠ 0 := fun h ↦ hU0.ne' (neg_eq_zero.mp (congrArg Complex.re h))
    have hn : U ≤ ‖(⟨-U, t⟩ : ℂ)‖ := by
      have h := Complex.abs_re_le_norm (⟨-U, t⟩ : ℂ)
      rwa [show (⟨-U, t⟩ : ℂ).re = -U from rfl, abs_neg, abs_of_pos hU0] at h
    rw [dslope_of_ne _ hne, slope_def_field, Complex.cpow_zero, sub_zero, norm_div]
    refine div_le_div₀ zero_le_two ((norm_sub_le _ _).trans ?_) hU0 hn
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, show (⟨-U, t⟩ : ℂ).re = -U from rfl, norm_one]
    linarith [Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by linarith : -U ≤ 0)]
  have hat : Real.arctan (T / U) ≤ T / U := Real.arctan_le_self (div_pos hT hU0).le
  have hat0 : 0 ≤ Real.arctan (T / U) := Real.arctan_nonneg.mpr (div_pos hT hU0).le
  have hb : (y ^ c - y ^ (-U)) / (T * Real.log y) ≤ y ^ c / (T * Real.log y) :=
    div_le_div_of_nonneg_right (by linarith [Real.rpow_pos_of_pos hy (-U)])
      (mul_pos hT hlog).le
  have hε' : 2 / U * |T - -T| + 2 * (T / U) ≤ ε := by
    rw [sub_neg_eq_add, abs_of_pos (by linarith)]
    have h6 := (div_le_iff₀ hε).mp hUε
    have e : 2 / U * (T + T) + 2 * (T / U) = 6 * T / U := by
      field_simp
      ring
    rw [e, div_le_iff₀ hU0]
    linarith
  have hnorm : ‖(2 * Real.pi : ℂ) - ∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)‖ =
      ‖Complex.I * ((2 * Real.pi : ℂ) -
        ∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ))‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  rw [hnorm, key]
  have hI2 : ‖Complex.I * ((2 * Real.arctan (T / U) : ℝ) : ℂ)‖ = 2 * Real.arctan (T / U) := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hIW : ‖Complex.I * ∫ t in -T..T, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (⟨-U, t⟩ : ℂ)‖ =
      ‖∫ t in -T..T, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (⟨-U, t⟩ : ℂ)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have htri := (norm_sub_le
    ((∫ u in -U..c, (y : ℂ) ^ (⟨u, -T⟩ : ℂ) / (⟨u, -T⟩ : ℂ)) -
      (∫ u in -U..c, (y : ℂ) ^ (⟨u, T⟩ : ℂ) / (⟨u, T⟩ : ℂ)) +
      Complex.I * ((2 * Real.arctan (T / U) : ℝ) : ℂ))
    (Complex.I * ∫ t in -T..T, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (⟨-U, t⟩ : ℂ)))
  have htri2 := (norm_add_le
    ((∫ u in -U..c, (y : ℂ) ^ (⟨u, -T⟩ : ℂ) / (⟨u, -T⟩ : ℂ)) -
      (∫ u in -U..c, (y : ℂ) ^ (⟨u, T⟩ : ℂ) / (⟨u, T⟩ : ℂ)))
    (Complex.I * ((2 * Real.arctan (T / U) : ℝ) : ℂ)))
  have htri3 := (norm_sub_le
    (∫ u in -U..c, (y : ℂ) ^ (⟨u, -T⟩ : ℂ) / (⟨u, -T⟩ : ℂ))
    (∫ u in -U..c, (y : ℂ) ^ (⟨u, T⟩ : ℂ) / (⟨u, T⟩ : ℂ)))
  rw [hI2] at htri2
  rw [hIW] at htri
  have hsplit : 2 * y ^ c / (T * Real.log y) =
      y ^ c / (T * Real.log y) + y ^ c / (T * Real.log y) := by ring
  rw [hsplit]
  linarith

/-- Perron's kernel with the three cases combined. -/
private theorem truncatedPerron_error_kernel {y c T : ℝ} (hy : 0 < y) (hc : 0 < c)
    (hT : 0 < T) :
    ‖(if 1 < y then (1 : ℂ) else if y = 1 then 1 / 2 else 0) -
        (∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) / (2 * (Real.pi : ℂ))‖ ≤
      if y = 1 then c / (Real.pi * T) else y ^ c / (Real.pi * T * |Real.log y|) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn2π : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_ofNat]
  have h2π0 : 0 < 2 * Real.pi := by positivity
  rcases lt_trichotomy y 1 with hlt | rfl | hgt
  · rw [ite_eq_right (not_lt.mpr hlt.le), ite_eq_right hlt.ne, ite_eq_right hlt.ne, zero_sub,
      norm_neg, norm_div, hn2π, div_le_iff₀ h2π0]
    have h := truncatedPerron_error_lt_one hy hlt hc hT
    have hlog : 0 < |Real.log y| := abs_pos.mpr (Real.log_neg hy hlt).ne
    have e : y ^ c / (Real.pi * T * |Real.log y|) * (2 * Real.pi) =
        2 * y ^ c / (T * |Real.log y|) := by
      field_simp
    rw [e]
    exact h
  · rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, ite_eq_left rfl]
    have h : (∫ t in -T..T, (1 : ℂ) * ((1 : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
        (2 * (Real.pi : ℂ)) = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) :=
      truncatedPerronIntegral_one (0 : ℂ) hc
    simp only [one_mul] at h
    rw [h]
    have hpi1 : Real.arctan (T / c) = Real.pi / 2 - Real.arctan (c / T) := by
      rw [← Real.arctan_inv_of_pos (div_pos hc hT), inv_div]
    have e : (1 / 2 : ℂ) - ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) =
        ((Real.arctan (c / T) / Real.pi : ℝ) : ℂ) := by
      rw [hpi1]
      push_cast
      field_simp
      ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg (Real.arctan_nonneg.mpr (div_pos hc hT).le) Real.pi_pos.le),
      div_le_div_iff₀ Real.pi_pos (mul_pos Real.pi_pos hT)]
    have h1 := Real.arctan_le_self (div_pos hc hT).le
    have h2 : Real.arctan (c / T) * T ≤ c := by
      calc Real.arctan (c / T) * T ≤ c / T * T := mul_le_mul_of_nonneg_right h1 hT.le
        _ = c := div_mul_cancel₀ c hT.ne'
    nlinarith [Real.pi_pos]
  · rw [ite_eq_left hgt, ite_eq_right hgt.ne']
    have h := truncatedPerron_error_gt_one hgt hc hT
    have hlog : 0 < Real.log y := Real.log_pos hgt
    have e : (1 : ℂ) - (∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
        (2 * (Real.pi : ℂ)) =
        ((2 * Real.pi : ℂ) - ∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
          (2 * (Real.pi : ℂ)) := by
      field_simp
    rw [e, norm_div, hn2π, abs_of_pos hlog, div_le_iff₀ h2π0]
    have e2 : y ^ c / (Real.pi * T * Real.log y) * (2 * Real.pi) =
        2 * y ^ c / (T * Real.log y) := by
      field_simp
    rw [e2]
    exact h

/-- Shifting the exponent by `c` rescales the norm of a Dirichlet term. -/
private theorem truncatedPerron_error_norm_term (a : ℕ → ℂ) (s : ℂ) {x c : ℝ} (hx : 0 < x)
    (n : ℕ) :
    ‖LSeries.term a s n‖ * (x / n) ^ c = x ^ c * ‖LSeries.term a (s + (c : ℂ)) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn, ite_eq_right hn,
      Complex.add_re, Complex.ofReal_re, Real.div_rpow hx.le hn0.le, Real.rpow_add hn0]
    have h1 := (Real.rpow_pos_of_pos hn0 s.re).ne'
    have h2 := (Real.rpow_pos_of_pos hn0 c).ne'
    field_simp

/-- Term by term integration of the Dirichlet series against Perron's kernel. -/
private theorem truncatedPerron_error_hasSum (a : ℕ → ℂ) (s : ℂ) {x c T : ℝ} (hx : 0 < x)
    (hc : 0 < c) (ha : LSeriesSummable a (s + (c : ℂ))) :
    HasSum (fun n : ℕ ↦ LSeries.term a s n *
        ((∫ t in -T..T, ((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
          (2 * (Real.pi : ℂ))))
      (truncatedPerronIntegral (LSeries a) s x c T) := by
  have hmk : Continuous fun t : ℝ ↦ (⟨c, t⟩ : ℂ) := by
    rw [show (fun t : ℝ ↦ (⟨c, t⟩ : ℂ)) = fun t : ℝ ↦ (c : ℂ) + (t : ℂ) * Complex.I from
      funext fun t ↦ Complex.mk_eq_add_mul_I c t]
    fun_prop
  have hz : ∀ t : ℝ, (⟨c, t⟩ : ℂ) ≠ 0 := fun t h ↦ hc.ne' (congrArg Complex.re h)
  have hF : ∀ (n : ℕ) (t : ℝ),
      LSeries.term a (s + ⟨c, t⟩) n * (x : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ) =
        LSeries.term a s n * (((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) := by
    intro n t
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hdiv : ((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) =
          (x : ℂ) ^ (⟨c, t⟩ : ℂ) / (n : ℂ) ^ (⟨c, t⟩ : ℂ) := by
        rw [div_eq_mul_inv x, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg hx.le (inv_nonneg.mpr hn0.le), Complex.ofReal_inv,
          Complex.ofReal_natCast, Complex.inv_cpow _ _
            (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), div_eq_mul_inv]
      have h1 : (n : ℂ) ^ s ≠ 0 := fun h ↦ hnC ((Complex.cpow_eq_zero_iff _ _).mp h).1
      have h2 : (n : ℂ) ^ (⟨c, t⟩ : ℂ) ≠ 0 := fun h ↦
        hnC ((Complex.cpow_eq_zero_iff _ _).mp h).1
      have h3 := hz t
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hnC,
        hdiv]
      field_simp
  have hsum : HasSum (fun n : ℕ ↦ ∫ t in -T..T,
        LSeries.term a s n * (((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)))
      (∫ t in -T..T, LSeries a (s + ⟨c, t⟩) * (x : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ ↦ x ^ c * ‖LSeries.term a (s + (c : ℂ)) n‖ / c) (fun n ↦ ?_) (fun n ↦ ?_)
      ?_ ?_ ?_
    · exact (continuous_const.mul
        ((hmk.const_cpow (Or.inr hz)).div hmk hz)).aestronglyMeasurable
    · refine Eventually.of_forall fun t _ ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        have hnorm : c ≤ ‖(⟨c, t⟩ : ℂ)‖ := by
          have h := Complex.abs_re_le_norm (⟨c, t⟩ : ℂ)
          rwa [show (⟨c, t⟩ : ℂ).re = c from rfl, abs_of_pos hc] at h
        rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hx hn0),
          show (⟨c, t⟩ : ℂ).re = c from rfl, ← truncatedPerron_error_norm_term a s hx n,
          mul_div_assoc]
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (Real.rpow_pos_of_pos (div_pos hx hn0) c).le hc hnorm)
          (norm_nonneg _)
    · exact Eventually.of_forall fun t _ ↦ (ha.norm.mul_left (x ^ c)).div_const c
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun t _ ↦ ?_
      have hre : (s + (c : ℂ)).re = (s + ⟨c, t⟩).re := by simp
      have hs' : LSeriesSummable a (s + ⟨c, t⟩) := (LSeriesSummable_iff_of_re_eq_re hre).mp ha
      have h0 : HasSum (LSeries.term a (s + ⟨c, t⟩)) (LSeries a (s + ⟨c, t⟩)) :=
        hs'.LSeriesHasSum
      have h := (h0.mul_right ((x : ℂ) ^ (⟨c, t⟩ : ℂ))).div_const (⟨c, t⟩ : ℂ)
      simpa only [hF] using h
  have h2 := hsum.div_const (2 * (Real.pi : ℂ))
  have h3 : (fun n : ℕ ↦ LSeries.term a s n *
      ((∫ t in -T..T, ((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
        (2 * (Real.pi : ℂ)))) = fun n : ℕ ↦ (∫ t in -T..T,
        LSeries.term a s n * (((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ))) /
        (2 * (Real.pi : ℂ)) := funext fun n ↦ by
    rw [intervalIntegral.integral_const_mul, mul_div_assoc]
  rw [h3]
  exact h2

/-- The half-weighted cutoff sum as a series with Perron's limiting weights. -/
private theorem truncatedPerron_error_hasSum_weights (a : ℕ → ℂ) (s : ℂ) {x : ℝ}
    (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ LSeries.term a s n *
        (if 1 < x / n then (1 : ℂ) else if x / n = 1 then 1 / 2 else 0))
      (perronHalfWeightedSum a s x) := by
  have key : ∀ n : ℕ, n ∉ Finset.Icc 1 ⌊x⌋₊ → LSeries.term a s n *
      (if 1 < x / n then (1 : ℂ) else if x / n = 1 then 1 / 2 else 0) = 0 := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hlt : ⌊x⌋₊ < n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨hn1, not_lt.mp h⟩)
      have hxn : x < n := (Nat.floor_lt hx.le).mp hlt
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have h1 : x / n < 1 := (div_lt_one hnpos).mpr hxn
      rw [ite_eq_right (not_lt.mpr h1.le), ite_eq_right h1.ne, mul_zero]
  have hval : perronHalfWeightedSum a s x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, LSeries.term a s n *
      (if 1 < x / n then (1 : ℂ) else if x / n = 1 then 1 / 2 else 0) := by
    change (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      if (n : ℝ) = x then LSeries.term a s n / 2 else LSeries.term a s n) = _
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hle : (n : ℝ) ≤ x := (Nat.cast_le.mpr hn2).trans (Nat.floor_le hx.le)
    by_cases hnx : (n : ℝ) = x
    · have h1 : x / n = 1 := by
        rw [← hnx]
        exact div_self hnpos.ne'
      rw [ite_eq_left hnx, ite_eq_right (by rw [h1]; exact lt_irrefl _), ite_eq_left h1]
      ring
    · have hlt : (n : ℝ) < x := lt_of_le_of_ne hle hnx
      rw [ite_eq_right hnx, ite_eq_left ((one_lt_div hnpos).mpr hlt), mul_one]
  rw [hval]
  exact hasSum_sum_of_ne_finset_zero key

/-- The error series is summable: far from the cutoff the logarithm is at least one. -/
private theorem truncatedPerron_error_summable (a : ℕ → ℂ) (s : ℂ) {x c : ℝ} (hx : 0 < x)
    (ha : LSeriesSummable a (s + (c : ℂ))) :
    Summable fun n : ℕ ↦ if n = 0 ∨ (n : ℝ) = x then 0
      else ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)| := by
  refine Summable.of_norm_bounded_eventually_nat ha.norm ?_
  filter_upwards [eventually_gt_atTop ⌈Real.exp 1 * x⌉₊] with n hn
  have hn' : Real.exp 1 * x < n := Nat.lt_of_ceil_lt hn
  have hnpos : (0 : ℝ) < n := (mul_pos (Real.exp_pos 1) hx).trans hn'
  have hlog : Real.log (x / n) ≤ -1 := by
    rw [Real.log_le_iff_le_exp (div_pos hx hnpos), div_le_iff₀ hnpos, Real.exp_neg,
      ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos 1)]
    linarith
  have habs : 1 ≤ |Real.log (x / n)| := by
    rw [abs_of_neg (by linarith)]
    linarith
  split_ifs
  · simp
  · rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (abs_nonneg _))]
    exact div_le_self (norm_nonneg _) habs

/-- Paper: Equations (B.7.1.6)–(B.7.1.7), pp. 644–645. The truncated Perron
error is bounded by a sum weighted by the inverse logarithmic distance from
the cutoff. An exact endpoint contributes the separate arctangent error.
Deviation: This includes both endpoint cases and assumes absolute convergence
at the specific line of integration, which suffices for this bound. -/
theorem truncatedPerron_error (a : ℕ → ℂ) (s : ℂ) {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 1 ≤ T) (ha : LSeriesSummable a (s + (c : ℂ))) :
    ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖ ≤
      x ^ c / (Real.pi * T) *
        (∑' n : ℕ, if n = 0 ∨ (n : ℝ) = x then 0
          else ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|) +
      (if (⌊x⌋₊ : ℝ) = x then
        c * ‖LSeries.term a s ⌊x⌋₊‖ / (Real.pi * T) else 0) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hπT : 0 < Real.pi * T := mul_pos Real.pi_pos hT0
  have hD := (truncatedPerron_error_hasSum_weights a s hx).sub
    (truncatedPerron_error_hasSum a s (T := T) hx hc ha)
  have he : HasSum (fun n : ℕ ↦ if (n : ℝ) = x then
      c * ‖LSeries.term a s n‖ / (Real.pi * T) else 0)
      (if (⌊x⌋₊ : ℝ) = x then c * ‖LSeries.term a s ⌊x⌋₊‖ / (Real.pi * T) else 0) := by
    refine hasSum_single ⌊x⌋₊ fun n hn ↦ ite_eq_right fun h ↦ hn ?_
    rw [← h, Nat.floor_natCast]
  have hg := ((truncatedPerron_error_summable a s hx ha).hasSum.mul_left
    (x ^ c / (Real.pi * T))).add he
  refine hD.norm_le_of_bounded hg fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hk := truncatedPerron_error_kernel (div_pos hx hnpos) hc hT0
    rw [← mul_sub, norm_mul]
    by_cases hnx : (n : ℝ) = x
    · have h1 : x / n = 1 := by
        rw [← hnx]
        exact div_self hnpos.ne'
      have hk' := hk.trans_eq (ite_eq_left h1)
      rw [ite_eq_left (Or.inr hnx), mul_zero, zero_add, ite_eq_left hnx]
      calc ‖LSeries.term a s n‖ * _ ≤ ‖LSeries.term a s n‖ * (c / (Real.pi * T)) :=
            mul_le_mul_of_nonneg_left hk' (norm_nonneg _)
        _ = c * ‖LSeries.term a s n‖ / (Real.pi * T) := by ring
    · have h1 : x / n ≠ 1 := fun h ↦ hnx ((div_eq_one_iff_eq hnpos.ne').mp h).symm
      have hk' := hk.trans_eq (ite_eq_right h1)
      rw [ite_eq_right (not_or.mpr ⟨hn, hnx⟩), ite_eq_right hnx, add_zero]
      calc ‖LSeries.term a s n‖ * _
          ≤ ‖LSeries.term a s n‖ *
            ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|)) :=
            mul_le_mul_of_nonneg_left hk' (norm_nonneg _)
        _ = ‖LSeries.term a s n‖ * (x / n) ^ c / (Real.pi * T * |Real.log (x / n)|) := by
            ring
        _ = x ^ c / (Real.pi * T) *
            (‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|) := by
            rw [truncatedPerron_error_norm_term a s hx n]
            ring

/-- A big-O bound along the natural numbers by a positive majorant holds at every index. -/
private theorem truncatedPerron_error_noninteger_coeff (a : ℕ → ℂ) (ψ : ℕ → ℝ)
    (hψ : ∀ n, 0 < ψ n) (hcoeff : a =O[atTop] ψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, ‖a n‖ ≤ C * ψ n := by
  obtain ⟨C, hC⟩ :=
    (Asymptotics.isBigO_nat_atTop_iff fun n h ↦ absurd h (hψ n).ne').mp hcoeff
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun n ↦ (hC n).trans ?_⟩
  rw [Real.norm_of_nonneg (hψ n).le]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hψ n).le

/-- The absolute series is `O((σ - 1)^(-α))` on the whole interval `(1, 2]`. -/
private theorem truncatedPerron_error_noninteger_abs (a : ℕ → ℂ) (α : ℝ) (hα : 0 < α)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (habs : (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖) =O[𝓝[>] 1]
      (fun σ : ℝ ↦ ((σ - 1) ^ α)⁻¹)) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ ∈ Ioc 1 2 →
      ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ ≤ C / (σ - 1) ^ α := by
  obtain ⟨c, hc⟩ := habs.bound
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hc
  have hu1' : (1 : ℝ) < u := hu1
  have hσ₁ : (1 : ℝ) < (1 + u) / 2 := by linarith
  have hA0 : ∀ σ : ℝ, 0 ≤ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ := fun σ ↦
    tsum_nonneg fun n ↦ norm_nonneg _
  refine ⟨max c 0 + (∑' n : ℕ, ‖LSeries.term a (((1 + u) / 2 : ℝ) : ℂ) n‖) + 1,
    by linarith [le_max_right c 0, hA0 ((1 + u) / 2)], fun σ hσ ↦ ?_⟩
  have hpos : 0 < (σ - 1) ^ α := Real.rpow_pos_of_pos (by linarith [hσ.1]) α
  have hle1 : (σ - 1) ^ α ≤ 1 :=
    Real.rpow_le_one (by linarith [hσ.1]) (by linarith [hσ.2]) hα.le
  have hinv : 1 ≤ ((σ - 1) ^ α)⁻¹ := (one_le_inv₀ hpos).mpr hle1
  rw [div_eq_mul_inv]
  by_cases hσu : σ < u
  · have h := hu ⟨hσ.1, hσu⟩
    change ‖∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖‖ ≤ c * ‖((σ - 1) ^ α)⁻¹‖ at h
    rw [Real.norm_of_nonneg (hA0 σ), Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hpos.le))
    linarith [le_max_left c 0, hA0 ((1 + u) / 2)]
  · have hle : ((1 + u) / 2 : ℝ) ≤ σ := by linarith [not_lt.mp hσu]
    have hmono : ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ ≤
        ∑' n : ℕ, ‖LSeries.term a (((1 + u) / 2 : ℝ) : ℂ) n‖ :=
      Summable.tsum_le_tsum
        (fun n ↦ LSeries.norm_term_le_of_re_le_re a
          (by rw [Complex.ofReal_re, Complex.ofReal_re]; exact hle) n)
        (ha _ (by rw [Complex.ofReal_re]; exact hσ.1)).norm
        (ha _ (by rw [Complex.ofReal_re]; exact hσ₁)).norm
    have h0 := hA0 ((1 + u) / 2)
    have hC : 0 ≤ max c 0 + (∑' n : ℕ, ‖LSeries.term a (((1 + u) / 2 : ℝ) : ℂ) n‖) + 1 := by
      linarith [le_max_right c 0]
    calc ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖
        ≤ (max c 0 + (∑' n : ℕ, ‖LSeries.term a (((1 + u) / 2 : ℝ) : ℂ) n‖) + 1) * 1 := by
          linarith [le_max_right c 0]
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv hC

/-- The harmonic sum below `m` is at most `2 log m`. -/
private theorem truncatedPerron_error_noninteger_harmonic (m : ℕ) :
    ∑ k ∈ Finset.Ico 1 m, (1 : ℝ) / k ≤ 2 * Real.log m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hm : 1 ≤ m := hm0
  clear hm0
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm]
    have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
    have h1 : Real.log ((m : ℝ) / (m + 1)) ≤ (m : ℝ) / (m + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hm0.ne' (by positivity)] at h1
    have h2 : (m : ℝ) / (m + 1) - 1 = -(1 / (m + 1)) := by
      field_simp
      ring
    have h3 : (1 : ℝ) / (2 * m) ≤ 1 / (m + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h4 : (1 : ℝ) / (2 * m) = 1 / m / 2 := by
      field_simp
    push_cast
    linarith

/-- Reciprocal distances to `N` on either side of `N` are dominated by harmonic sums. -/
private theorem truncatedPerron_error_noninteger_near (N K : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ S : ℝ, S ≤ B * (2 * Real.log N + 2 * Real.log K) ∧
      HasSum (fun n : ℕ ↦ (if n ∈ Finset.Ico 1 N then B / ((N - n : ℕ) : ℝ) else 0) +
        (if n ∈ Finset.Ico (1 + N) (K + N) then B / ((n - N : ℕ) : ℝ) else 0)) S := by
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.Ico 1 m, B / (k : ℝ) ≤ B * (2 * Real.log m) := by
    intro m
    have e : ∑ k ∈ Finset.Ico 1 m, B / (k : ℝ) = B * ∑ k ∈ Finset.Ico 1 m, (1 : ℝ) / k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_one_div]
    rw [e]
    exact mul_le_mul_of_nonneg_left (truncatedPerron_error_noninteger_harmonic m) hB
  have h1 : HasSum (fun n : ℕ ↦ if n ∈ Finset.Ico 1 N then B / ((N - n : ℕ) : ℝ) else 0)
      (∑ k ∈ Finset.Ico 1 N, B / (k : ℝ)) := by
    have e : ∑ k ∈ Finset.Ico 1 N, B / (k : ℝ) = ∑ n ∈ Finset.Ico 1 N,
        (if n ∈ Finset.Ico 1 N then B / ((N - n : ℕ) : ℝ) else 0) := by
      have r := Finset.sum_Ico_reflect (fun j : ℕ ↦ B / (j : ℝ)) 1 (Nat.le_succ N)
      simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] at r
      rw [← r]
      exact Finset.sum_congr rfl fun n hn ↦ (ite_eq_left hn).symm
    rw [e]
    exact hasSum_sum_of_ne_finset_zero fun n hn ↦ ite_eq_right hn
  have h2 : HasSum
      (fun n : ℕ ↦ if n ∈ Finset.Ico (1 + N) (K + N) then B / ((n - N : ℕ) : ℝ) else 0)
      (∑ k ∈ Finset.Ico 1 K, B / (k : ℝ)) := by
    have e : ∑ k ∈ Finset.Ico 1 K, B / (k : ℝ) = ∑ n ∈ Finset.Ico (1 + N) (K + N),
        (if n ∈ Finset.Ico (1 + N) (K + N) then B / ((n - N : ℕ) : ℝ) else 0) := by
      have r := Finset.sum_Ico_add' (fun n : ℕ ↦ B / ((n - N : ℕ) : ℝ)) 1 K N
      simp only [Nat.add_sub_cancel] at r
      rw [r]
      exact Finset.sum_congr rfl fun n hn ↦ (ite_eq_left hn).symm
    rw [e]
    exact hasSum_sum_of_ne_finset_zero fun n hn ↦ ite_eq_right hn
  exact ⟨_, by linarith [hsum N, hsum K], h1.add h2⟩

/-- Away from the cutoff by a factor of two the logarithmic distance is at least `log 2`. -/
private theorem truncatedPerron_error_noninteger_far {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : 2 * y ≤ x ∨ 2 * x ≤ y) : Real.log 2 ≤ |Real.log (x / y)| := by
  rcases h with h | h
  · exact (Real.log_le_log two_pos ((le_div_iff₀ hy).mpr h)).trans (le_abs_self _)
  · have h1 : Real.log 2 ≤ Real.log (y / x) := Real.log_le_log two_pos ((le_div_iff₀ hx).mpr h)
    have h2 : Real.log (x / y) = -Real.log (y / x) := by
      rw [← Real.log_inv, inv_div]
    rw [h2, abs_neg]
    exact h1.trans (le_abs_self _)

/-- Within a factor of two of the cutoff the logarithmic distance dominates the distance. -/
private theorem truncatedPerron_error_noninteger_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : y < 2 * x) : |x - y| / (2 * x) ≤ |Real.log (x / y)| := by
  rcases le_total y x with hyx | hxy
  · have h1 : 1 - (x / y)⁻¹ ≤ Real.log (x / y) := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
    rw [inv_div] at h1
    have h2 : 0 ≤ Real.log (x / y) := Real.log_nonneg ((one_le_div hy).mpr hyx)
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg h2]
    have h3 : (x - y) / (2 * x) ≤ 1 - y / x := by
      rw [div_le_iff₀ (by positivity)]
      have e : (1 - y / x) * (2 * x) = 2 * (x - y) := by
        field_simp
      rw [e]
      linarith
    exact h3.trans h1
  · have h1 : 1 - (y / x)⁻¹ ≤ Real.log (y / x) := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
    rw [inv_div] at h1
    have h2 : Real.log (x / y) = -Real.log (y / x) := by
      rw [← Real.log_inv, inv_div]
    have h3 : 0 ≤ Real.log (y / x) := Real.log_nonneg ((one_le_div hx).mpr hxy)
    rw [h2, abs_neg, abs_of_nonneg h3, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
    have h4 : (y - x) / (2 * x) ≤ 1 - x / y := by
      rw [div_le_iff₀ (by positivity)]
      have e : (1 - x / y) * (2 * x) = (y - x) * (2 * x / y) := by
        field_simp
      rw [e]
      have h5 : 1 ≤ 2 * x / y := (one_le_div hy).mpr h.le
      nlinarith [sub_nonneg.mpr hxy]
    exact h4.trans h1

/-- The scalar inequality that assembles the bound at a noninteger cutoff. -/
private theorem truncatedPerron_error_noninteger_scalar
    {C₁ C₂ P Q D L L₂ T p ψ₁ ψ₂ X d ρ W E : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hP : 0 < P) (hQ : 0 < Q) (hD : 0 < D) (hL : 0 ≤ L)
    (hL₂ : 0 < L₂) (hT : 0 < T) (hp : 0 < p) (hψ₁ : 0 < ψ₁) (hψ₂ : 0 < ψ₂) (hX : 0 < X)
    (hd : 0 < d) (hρ : 0 < ρ)
    (hW : ψ₂ * W ≤ 10 * ψ₂ * L + 8 * ρ * (ψ₁ / d))
    (hE : E ≤ C₂ / D / L₂ + (4 * (C₁ * ψ₁) / Q * (2 * X) / d +
      4 * (C₁ * ψ₂) / Q * (2 * X) * 2 * W)) :
    P / (p * T) * E + 0 ≤
      (C₂ / (p * L₂) + 160 * (C₁ / p) + (8 + 128 * ρ) * (C₁ / p)) *
        (P / (T * D) + ψ₂ * (X * P / Q) * L / T + ψ₁ * (X * P / Q) / (T * d)) := by
  have h1 : P / (p * T) * E ≤ P / (p * T) * (C₂ / D / L₂ +
      (4 * (C₁ * ψ₁) / Q * (2 * X) / d + 4 * (C₁ * ψ₂) / Q * (2 * X) * 2 * W)) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have e1 : P / (p * T) * (C₂ / D / L₂ +
      (4 * (C₁ * ψ₁) / Q * (2 * X) / d + 4 * (C₁ * ψ₂) / Q * (2 * X) * 2 * W)) =
      C₂ / (p * L₂) * (P / (T * D)) + 8 * (C₁ / p) * (ψ₁ * (X * P / Q) / (T * d)) +
        16 * (C₁ / p) * (X * P / Q / T) * (ψ₂ * W) := by
    field_simp
    ring
  have h2 : 16 * (C₁ / p) * (X * P / Q / T) * (ψ₂ * W) ≤
      16 * (C₁ / p) * (X * P / Q / T) * (10 * ψ₂ * L + 8 * ρ * (ψ₁ / d)) :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  have e2 : 16 * (C₁ / p) * (X * P / Q / T) * (10 * ψ₂ * L + 8 * ρ * (ψ₁ / d)) =
      160 * (C₁ / p) * (ψ₂ * (X * P / Q) * L / T) +
        128 * ρ * (C₁ / p) * (ψ₁ * (X * P / Q) / (T * d)) := by
    field_simp
    ring
  have hU : 0 ≤ P / (T * D) := by positivity
  have hV : 0 ≤ ψ₂ * (X * P / Q) * L / T := by positivity
  have hZ : 0 ≤ ψ₁ * (X * P / Q) / (T * d) := by positivity
  have hA : 0 ≤ C₂ / (p * L₂) := by positivity
  have hB : 0 ≤ C₁ / p := by positivity
  have key : ∀ A B U V Z r : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ U → 0 ≤ V → 0 ≤ Z → 0 ≤ r →
      A * U + 8 * B * Z + (160 * B * V + 128 * r * B * Z) ≤
        (A + 160 * B + (8 + 128 * r) * B) * (U + V + Z) := by
    intro A B U V Z r hA hB hU hV hZ hr
    nlinarith [mul_nonneg hA hV, mul_nonneg hA hZ, mul_nonneg hB hU, mul_nonneg hB hZ,
      mul_nonneg hB hV, mul_nonneg (mul_nonneg hr hB) hU, mul_nonneg (mul_nonneg hr hB) hV]
  have h3 := key _ _ _ _ _ _ hA hB hU hV hZ hρ.le
  rw [e1] at h1
  rw [e2] at h2
  linarith

/-- The harmonic weights at a noninteger cutoff are absorbed by the logarithm of the cutoff
when it is at least two, and by the term of the nearest integer otherwise. -/
private theorem truncatedPerron_error_noninteger_weight (ψ : ℕ → ℝ) (hψ : ∀ n, 0 < ψ n)
    (hmono : Monotone ψ) {x : ℝ} (hx : 0 < x) (N : ℕ) (hd : 0 < |x - (N : ℝ)|)
    (hN : |x - (N : ℝ)| ≤ 1 / 2) :
    ψ ⌊2 * x⌋₊ * (2 * Real.log N + 2 * Real.log (⌊2 * x⌋₊ + 1 : ℕ)) ≤
      10 * ψ ⌊2 * x⌋₊ * |Real.log x| + 8 * (ψ 3 / ψ 0) * (ψ N / |x - (N : ℝ)|) := by
  have hψ₂ : 0 < ψ ⌊2 * x⌋₊ := hψ _
  have hψN : 0 < ψ N := hψ _
  have hρ : 0 < ψ 3 / ψ 0 := div_pos (hψ 3) (hψ 0)
  have hNle : (N : ℝ) ≤ x + 1 / 2 := by linarith [(abs_le.mp hN).1]
  have hKle : ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * x + 1 := by
    push_cast
    linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * x)]
  have hr0 : 0 ≤ 8 * (ψ 3 / ψ 0) * (ψ N / |x - (N : ℝ)|) := by positivity
  have hl0 : 0 ≤ 10 * ψ ⌊2 * x⌋₊ * |Real.log x| := by positivity
  rcases le_or_gt 2 x with hx2 | hx2
  · have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have h2x : 2 * x ≤ x * x := mul_le_mul_of_nonneg_right hx2 hx.le
    have h3x : 2 * x * x ≤ x * x * x := mul_le_mul_of_nonneg_right h2x hx.le
    have h1 : Real.log N ≤ 2 * Real.log x := by
      rcases Nat.eq_zero_or_pos N with rfl | hNpos
      · rw [Nat.cast_zero, Real.log_zero]
        linarith
      · have h5 : (N : ℝ) ≤ x ^ 2 := by
          rw [sq]
          linarith
        have h6 := Real.log_le_log (Nat.cast_pos.mpr hNpos) h5
        rwa [Real.log_pow, Nat.cast_ofNat] at h6
    have h2 : Real.log (⌊2 * x⌋₊ + 1 : ℕ) ≤ 3 * Real.log x := by
      have h5 : ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) ≤ x ^ 3 := by
        have h7 : x ^ 3 = x * x * x := by ring
        rw [h7]
        linarith
      have h6 := Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos _)) h5
      rwa [Real.log_pow, Nat.cast_ofNat] at h6
    rw [abs_of_nonneg hlx]
    have h3 : ψ ⌊2 * x⌋₊ * (2 * Real.log N + 2 * Real.log (⌊2 * x⌋₊ + 1 : ℕ)) ≤
        ψ ⌊2 * x⌋₊ * (10 * Real.log x) :=
      mul_le_mul_of_nonneg_left (by linarith) hψ₂.le
    linarith
  · have h1 : Real.log N ≤ 5 / 2 :=
      (Real.log_le_self (Nat.cast_nonneg N)).trans (by linarith)
    have h2 : Real.log (⌊2 * x⌋₊ + 1 : ℕ) ≤ 5 :=
      (Real.log_le_self (Nat.cast_nonneg _)).trans (by linarith)
    have hfl : ⌊2 * x⌋₊ ≤ 3 := by
      have h5 : ⌊2 * x⌋₊ < 4 := (Nat.floor_lt (by positivity)).mpr (by push_cast; linarith)
      omega
    have h3 : ψ ⌊2 * x⌋₊ * 15 ≤ ψ 3 / ψ 0 * ψ N * 15 := by
      have h5 : ψ 3 = ψ 3 / ψ 0 * ψ 0 := (div_mul_cancel₀ (ψ 3) (hψ 0).ne').symm
      have h6 : ψ ⌊2 * x⌋₊ ≤ ψ 3 / ψ 0 * ψ N := by
        calc ψ ⌊2 * x⌋₊ ≤ ψ 3 := hmono hfl
          _ = ψ 3 / ψ 0 * ψ 0 := h5
          _ ≤ ψ 3 / ψ 0 * ψ N := mul_le_mul_of_nonneg_left (hmono (Nat.zero_le N)) hρ.le
      linarith
    have h4 : ψ ⌊2 * x⌋₊ * (2 * Real.log N + 2 * Real.log (⌊2 * x⌋₊ + 1 : ℕ)) ≤
        ψ ⌊2 * x⌋₊ * 15 := mul_le_mul_of_nonneg_left (by linarith) hψ₂.le
    have hd2 : 2 * ψ N ≤ ψ N / |x - (N : ℝ)| := by
      rw [le_div_iff₀ hd]
      have h7 : ψ N * |x - (N : ℝ)| ≤ ψ N * (1 / 2) := mul_le_mul_of_nonneg_left hN hψN.le
      linarith
    have h5 : ψ 3 / ψ 0 * (2 * ψ N) ≤ ψ 3 / ψ 0 * (ψ N / |x - (N : ℝ)|) :=
      mul_le_mul_of_nonneg_left hd2 hρ.le
    linarith

/-- The pointwise comparison of the error series with a far part, the term of the nearest
integer and reciprocal distances to it. -/
private theorem truncatedPerron_error_noninteger_pointwise (a : ℕ → ℂ) (ψ : ℕ → ℝ)
    (hψ : ∀ n, 0 < ψ n) (hmono : Monotone ψ) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hcoef : ∀ n, ‖a n‖ ≤ C₁ * ψ n) (s : ℂ) {x c : ℝ} (N : ℕ) (hx : 0 < x)
    (hσ : s.re + c ∈ Ioc 1 2) (hN : |x - (N : ℝ)| ≤ 1 / 2) (n : ℕ) :
    (if n = 0 ∨ (n : ℝ) = x then 0
        else ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|) ≤
      ‖LSeries.term a (s + (c : ℂ)) n‖ / Real.log 2 +
        ((if n = N then 4 * (C₁ * ψ N) / x ^ (s.re + c) * (2 * x) / |x - (N : ℝ)| else 0) +
          ((if n ∈ Finset.Ico 1 N then
              4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 / ((N - n : ℕ) : ℝ)
            else 0) +
            (if n ∈ Finset.Ico (1 + N) (⌊2 * x⌋₊ + 1 + N) then
              4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 / ((n - N : ℕ) : ℝ)
            else 0))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hσre : (s + (c : ℂ)).re = s.re + c := by
    rw [Complex.add_re, Complex.ofReal_re]
  have hψ₂ : 0 < ψ ⌊2 * x⌋₊ := hψ _
  have hψN : 0 < ψ N := hψ _
  have hQ : 0 < x ^ (s.re + c) := Real.rpow_pos_of_pos hx _
  have hK0 : 0 ≤ 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) := by positivity
  have hB0 : 0 ≤ 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 := by positivity
  have hBN : 0 ≤ 4 * (C₁ * ψ N) / x ^ (s.re + c) * (2 * x) / |x - (N : ℝ)| := by positivity
  have ht : 0 ≤ ‖LSeries.term a (s + (c : ℂ)) n‖ := norm_nonneg _
  have hgn : 0 ≤ ‖LSeries.term a (s + (c : ℂ)) n‖ / Real.log 2 := div_nonneg ht hlog2.le
  have h0n : 0 ≤ (if n = N then
      4 * (C₁ * ψ N) / x ^ (s.re + c) * (2 * x) / |x - (N : ℝ)| else 0) := by
    split_ifs
    · exact hBN
    · exact le_rfl
  have h1n : 0 ≤ (if n ∈ Finset.Ico 1 N then
      4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 / ((N - n : ℕ) : ℝ) else 0) := by
    split_ifs
    · exact div_nonneg hB0 (Nat.cast_nonneg _)
    · exact le_rfl
  have h2n : 0 ≤ (if n ∈ Finset.Ico (1 + N) (⌊2 * x⌋₊ + 1 + N) then
      4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 / ((n - N : ℕ) : ℝ) else 0) := by
    split_ifs
    · exact div_nonneg hB0 (Nat.cast_nonneg _)
    · exact le_rfl
  by_cases h0 : n = 0 ∨ (n : ℝ) = x
  · rw [ite_eq_left h0]
    linarith
  rw [ite_eq_right h0]
  obtain ⟨hn0, hnx⟩ := not_or.mp h0
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  by_cases hfar : 2 * (n : ℝ) ≤ x ∨ 2 * x ≤ n
  · have hl : Real.log 2 ≤ |Real.log (x / n)| :=
      truncatedPerron_error_noninteger_far hx hnpos hfar
    have hle : ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)| ≤
        ‖LSeries.term a (s + (c : ℂ)) n‖ / Real.log 2 :=
      div_le_div_of_nonneg_left ht hlog2 hl
    linarith
  · obtain ⟨hl1, hl2⟩ := not_or.mp hfar
    have hn2 : (n : ℝ) < 2 * x := not_le.mp hl2
    have hx2 : x < 2 * n := not_le.mp hl1
    have hlogb := truncatedPerron_error_noninteger_log hx hnpos hn2
    have hdist : 0 < |x - n| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hnx))
    have h4 : x ^ (s.re + c) / 4 ≤ (n : ℝ) ^ (s.re + c) := by
      have h1 : (x / 2) ^ (s.re + c) ≤ (n : ℝ) ^ (s.re + c) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith [hσ.1])
      have h2 : (2 : ℝ) ^ (s.re + c) ≤ 4 := by
        calc (2 : ℝ) ^ (s.re + c) ≤ (2 : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le one_le_two hσ.2
          _ = 4 := by
              rw [Real.rpow_two]
              norm_num
      rw [Real.div_rpow hx.le zero_le_two] at h1
      have h3 : 0 < (2 : ℝ) ^ (s.re + c) := by positivity
      exact (div_le_div_of_nonneg_left hQ.le h3 h2).trans h1
    have hterm_le : ∀ ψ' : ℝ, ψ n ≤ ψ' →
        ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)| ≤
          4 * (C₁ * ψ') / x ^ (s.re + c) * (2 * x) / |x - n| := by
      intro ψ' hψ'
      have han : ‖a n‖ ≤ C₁ * ψ' :=
        (hcoef n).trans (mul_le_mul_of_nonneg_left hψ' hC₁.le)
      have hψ'0 : 0 ≤ C₁ * ψ' := (norm_nonneg _).trans han
      have htK : ‖LSeries.term a (s + (c : ℂ)) n‖ ≤ 4 * (C₁ * ψ') / x ^ (s.re + c) := by
        rw [LSeries.norm_term_eq, ite_eq_right hn0, hσre]
        calc ‖a n‖ / (n : ℝ) ^ (s.re + c)
            ≤ C₁ * ψ' / (x ^ (s.re + c) / 4) := div_le_div₀ hψ'0 han (by positivity) h4
          _ = 4 * (C₁ * ψ') / x ^ (s.re + c) := by
              field_simp
      calc ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|
          ≤ 4 * (C₁ * ψ') / x ^ (s.re + c) / (|x - n| / (2 * x)) :=
            div_le_div₀ (by positivity) htK (by positivity) hlogb
        _ = _ := by
            field_simp
    by_cases hnN : n = N
    · have h1 := hterm_le (ψ N) (by rw [hnN])
      have e : |x - (n : ℝ)| = |x - (N : ℝ)| := by rw [hnN]
      rw [e] at h1
      rw [ite_eq_left hnN]
      linarith
    · have hfl : n ≤ ⌊2 * x⌋₊ := Nat.le_floor hn2.le
      have h1 := hterm_le (ψ ⌊2 * x⌋₊) (hmono hfl)
      have hNn : (1 : ℝ) ≤ |(n : ℝ) - N| := by
        have h5 : (1 : ℤ) ≤ |(n : ℤ) - N| :=
          Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hnN))
        exact_mod_cast h5
      have hxn : |(n : ℝ) - N| / 2 ≤ |x - n| := by
        have h3 : |(n : ℝ) - N| ≤ |x - N| + |x - n| := by
          have h5 : (n : ℝ) - N = (x - N) - (x - n) := by ring
          rw [h5]
          exact abs_sub _ _
        linarith
      have h2 : 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) / |x - n| ≤
          4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 / |(n : ℝ) - N| := by
        calc 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) / |x - n|
            ≤ 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) / (|(n : ℝ) - N| / 2) :=
              div_le_div_of_nonneg_left hK0 (by positivity) hxn
          _ = _ := by
              field_simp
      rcases lt_or_gt_of_ne hnN with hlt | hgt
      · have hmem : n ∈ Finset.Ico 1 N :=
          Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hlt⟩
        rw [ite_eq_left hmem]
        have e : ((N - n : ℕ) : ℝ) = |(n : ℝ) - N| := by
          rw [Nat.cast_sub hlt.le, abs_sub_comm,
            abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hlt))]
        rw [e]
        linarith
      · have hmem : n ∈ Finset.Ico (1 + N) (⌊2 * x⌋₊ + 1 + N) :=
          Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        rw [ite_eq_left hmem]
        have e : ((n - N : ℕ) : ℝ) = |(n : ℝ) - N| := by
          rw [Nat.cast_sub hgt.le, abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hgt))]
        rw [e]
        linarith

/-- Paper: Lemma B.7.1.1, Equation (B.7.1.4), p. 644.
The truncated Perron error at a noninteger cutoff has a far contribution,
a near contribution and a contribution from a nearest integer.
Deviation: The simplified estimate is uniform for `1 < s.re + c ≤ 2`.
Its constant may depend on the coefficient sequence and majorant.
The imaginary part of `s` is independent of the integration height.
The expression `ψ(2x)` is evaluated at the natural floor of `2x`. -/
theorem truncatedPerron_error_noninteger (a : ℕ → ℂ) (ψ : ℕ → ℝ)
    (hψ : ∀ n, 0 < ψ n) (hmono : Monotone ψ) (α : ℝ) (hα : 0 < α)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hcoeff : a =O[atTop] ψ)
    (habs : (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖) =O[𝓝[>] 1]
      (fun σ : ℝ ↦ ((σ - 1) ^ α)⁻¹)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (x c T : ℝ) (N : ℕ),
      0 < x → 0 < c → 1 ≤ T → s.re + c ∈ Ioc 1 2 →
      x ∉ Set.range (Int.cast : ℤ → ℝ) → |x - (N : ℝ)| ≤ 1 / 2 →
      ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖ ≤
        C * (x ^ c / (T * (s.re + c - 1) ^ α) +
          ψ ⌊2 * x⌋₊ * x ^ (1 - s.re) * |Real.log x| / T +
          ψ N * x ^ (1 - s.re) / (T * |x - (N : ℝ)|)) := by
  obtain ⟨C₁, hC₁, hcoef⟩ := truncatedPerron_error_noninteger_coeff a ψ hψ hcoeff
  obtain ⟨C₂, hC₂, hA⟩ := truncatedPerron_error_noninteger_abs a α hα ha habs
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hρ : 0 < ψ 3 / ψ 0 := div_pos (hψ 3) (hψ 0)
  refine ⟨C₂ / (Real.pi * Real.log 2) + 160 * (C₁ / Real.pi) +
    (8 + 128 * (ψ 3 / ψ 0)) * (C₁ / Real.pi), by positivity, ?_⟩
  intro s x c T N hx hc hT hσ hxint hN
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hσre : (s + (c : ℂ)).re = s.re + c := by
    rw [Complex.add_re, Complex.ofReal_re]
  have hsum : LSeriesSummable a (s + (c : ℂ)) := ha _ (by rw [hσre]; exact hσ.1)
  have hQ : 0 < x ^ (s.re + c) := Real.rpow_pos_of_pos hx _
  have hD : 0 < (s.re + c - 1) ^ α := Real.rpow_pos_of_pos (by linarith [hσ.1]) α
  have hxN : x ≠ (N : ℝ) := fun h ↦ hxint ⟨(N : ℤ), by rw [Int.cast_natCast, h]⟩
  have hd : 0 < |x - (N : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hxN)
  have h := truncatedPerron_error a s hx hc hT hsum
  rw [ite_eq_right (fun h' ↦ hxint ⟨(⌊x⌋₊ : ℤ), by rw [Int.cast_natCast]; exact h'⟩)] at h
  refine h.trans ?_
  have hB0 : 0 ≤ 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 := by
    have hψ₂ : 0 < ψ ⌊2 * x⌋₊ := hψ _
    positivity
  obtain ⟨S, hS, hSsum⟩ := truncatedPerron_error_noninteger_near N (⌊2 * x⌋₊ + 1)
    (4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2) hB0
  have hg := hsum.norm.hasSum.div_const (Real.log 2)
  have hf := (truncatedPerron_error_summable a s hx hsum).hasSum
  have hNsum := hasSum_ite_eq N (4 * (C₁ * ψ N) / x ^ (s.re + c) * (2 * x) / |x - (N : ℝ)|)
  have hE := hasSum_le
    (truncatedPerron_error_noninteger_pointwise a ψ hψ hmono hC₁ hcoef s N hx hσ hN)
    hf (hg.add (hNsum.add hSsum))
  have hterm : ∀ n, ‖LSeries.term a (s + (c : ℂ)) n‖ =
      ‖LSeries.term a ((s.re + c : ℝ) : ℂ) n‖ := fun n ↦ by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, Complex.ofReal_re, hσre]
  have hA' := hA (s.re + c) hσ
  rw [← tsum_congr hterm] at hA'
  have hE' : (∑' n : ℕ, if n = 0 ∨ (n : ℝ) = x then 0
      else ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|) ≤
      C₂ / (s.re + c - 1) ^ α / Real.log 2 +
        (4 * (C₁ * ψ N) / x ^ (s.re + c) * (2 * x) / |x - (N : ℝ)| +
          4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 *
            (2 * Real.log N + 2 * Real.log (⌊2 * x⌋₊ + 1 : ℕ))) := by
    have h5 := div_le_div_of_nonneg_right hA' hlog2.le
    linarith only [h5, hE, hS]
  have e1 : x ^ (1 - s.re) = x * x ^ c / x ^ (s.re + c) := by
    rw [show 1 - s.re = 1 + c - (s.re + c) by ring, Real.rpow_sub hx, Real.rpow_add hx,
      Real.rpow_one]
  rw [e1]
  exact truncatedPerron_error_noninteger_scalar hC₁ hC₂ (Real.rpow_pos_of_pos hx c) hQ hD
    (abs_nonneg _) hlog2 hT0 Real.pi_pos (hψ N) (hψ _) hx hd hρ
    (truncatedPerron_error_noninteger_weight ψ hψ hmono hx N hd hN) hE'

/-- The scalar inequality that assembles the bound at an integer cutoff. -/
private theorem truncatedPerron_error_integer_scalar {C₁ C₂ P Q R D L L₂ T c p ψ₁ ψ₂ M E t : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hP : 0 < P) (hQ : 0 < Q) (hR : 0 < R) (hD : 0 < D)
    (hL : 0 ≤ L) (hL₂ : 0 < L₂) (hT : 0 < T) (hc : 0 < c) (hp : 0 < p) (hψ₁ : 0 < ψ₁)
    (hψ₂ : 0 < ψ₂) (hM : 0 < M)
    (hE : E ≤ C₂ / D / L₂ + 4 * (C₁ * ψ₂) / Q * (2 * M) * (4 * L))
    (ht : t ≤ C₁ * ψ₁ / R) :
    P / (p * T) * E + c * t / (p * T) ≤
      (C₂ / (p * L₂) + 32 * C₁ / p) *
        (P / (T * D) + ψ₂ * (M * P / Q) * L / T + ψ₁ * c * R⁻¹ / T) := by
  have h1 : P / (p * T) * E ≤
      P / (p * T) * (C₂ / D / L₂ + 4 * (C₁ * ψ₂) / Q * (2 * M) * (4 * L)) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have h2 : c * t / (p * T) ≤ c * (C₁ * ψ₁ / R) / (p * T) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht hc.le) (by positivity)
  have e1 : P / (p * T) * (C₂ / D / L₂ + 4 * (C₁ * ψ₂) / Q * (2 * M) * (4 * L)) =
      C₂ / (p * L₂) * (P / (T * D)) + 32 * C₁ / p * (ψ₂ * (M * P / Q) * L / T) := by
    field_simp
    ring
  have e2 : c * (C₁ * ψ₁ / R) / (p * T) = C₁ / p * (ψ₁ * c * R⁻¹ / T) := by
    field_simp
  have hX : 0 ≤ P / (T * D) := by positivity
  have hY : 0 ≤ ψ₂ * (M * P / Q) * L / T := by positivity
  have hZ : 0 ≤ ψ₁ * c * R⁻¹ / T := by positivity
  have hA : 0 ≤ C₂ / (p * L₂) := by positivity
  have hB : 0 ≤ C₁ / p := by positivity
  have e3 : 32 * C₁ / p = 32 * (C₁ / p) := by ring
  rw [e3]
  rw [e1, e3] at h1
  rw [e2] at h2
  nlinarith [mul_nonneg hA hY, mul_nonneg hA hZ, mul_nonneg hB hX, mul_nonneg hB hZ,
    mul_nonneg hB hY]

/-- Paper: Lemma B.7.1.1, Equation (B.7.1.5), p. 644. The truncated
Perron error at an integer cutoff includes the half-weight endpoint error.
Deviation: The simplified estimate is uniform for `1 < s.re + c ≤ 2`.
Its constant may depend on the coefficient
sequence and majorant. The imaginary part of `s` is independent of the
integration height. -/
theorem truncatedPerron_error_integer (a : ℕ → ℂ) (ψ : ℕ → ℝ)
    (hψ : ∀ n, 0 < ψ n) (hmono : Monotone ψ) (α : ℝ) (hα : 0 < α)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hcoeff : a =O[atTop] ψ)
    (habs : (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖) =O[𝓝[>] 1]
      (fun σ : ℝ ↦ ((σ - 1) ^ α)⁻¹)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (m : ℕ) (c T : ℝ),
      0 < m → 0 < c → 1 ≤ T → s.re + c ∈ Ioc 1 2 →
      ‖perronHalfWeightedSum a s m - truncatedPerronIntegral (LSeries a) s m c T‖ ≤
        C * ((m : ℝ) ^ c / (T * (s.re + c - 1) ^ α) +
          ψ (2 * m) * (m : ℝ) ^ (1 - s.re) * Real.log m / T +
          ψ m * c * (m : ℝ) ^ (-s.re) / T) := by
  obtain ⟨C₁, hC₁, hcoef⟩ := truncatedPerron_error_noninteger_coeff a ψ hψ hcoeff
  obtain ⟨C₂, hC₂, hA⟩ := truncatedPerron_error_noninteger_abs a α hα ha habs
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨C₂ / (Real.pi * Real.log 2) + 32 * C₁ / Real.pi, by positivity, ?_⟩
  intro s m c T hm hc hT hσ
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hσre : (s + (c : ℂ)).re = s.re + c := by
    rw [Complex.add_re, Complex.ofReal_re]
  have hsum : LSeriesSummable a (s + (c : ℂ)) := ha _ (by rw [hσre]; exact hσ.1)
  have hψ₂ : 0 < ψ (2 * m) := hψ _
  have hQ : 0 < (m : ℝ) ^ (s.re + c) := Real.rpow_pos_of_pos hm0 _
  have hD : 0 < (s.re + c - 1) ^ α := Real.rpow_pos_of_pos (by linarith [hσ.1]) α
  have h := truncatedPerron_error a s hm0 hc hT hsum
  rw [Nat.floor_natCast, ite_eq_left rfl] at h
  refine h.trans ?_
  -- the error series
  have hK0 : 0 ≤ 4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) := by positivity
  have hB0 : 0 ≤ 4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) := by positivity
  obtain ⟨S, hS0, hSsum⟩ := truncatedPerron_error_noninteger_near m m
    (4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m)) hB0
  have hS : S ≤ 4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) * (4 * Real.log m) :=
    hS0.trans_eq (by ring)
  have hg := hsum.norm.hasSum.div_const (Real.log 2)
  have hf := (truncatedPerron_error_summable a s hm0 hsum).hasSum
  have hE := hasSum_le (fun n ↦ ?_) hf (hg.add hSsum)
  · have hterm : ∀ n, ‖LSeries.term a (s + (c : ℂ)) n‖ =
        ‖LSeries.term a ((s.re + c : ℝ) : ℂ) n‖ := fun n ↦ by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq, Complex.ofReal_re, hσre]
    have hA' := hA (s.re + c) hσ
    rw [← tsum_congr hterm] at hA'
    have hE' : (∑' n : ℕ, if n = 0 ∨ (n : ℝ) = (m : ℝ) then 0
        else ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log ((m : ℝ) / n)|) ≤
        C₂ / (s.re + c - 1) ^ α / Real.log 2 +
          4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) * (4 * Real.log m) := by
      have := div_le_div_of_nonneg_right hA' hlog2.le
      linarith
    have ht : ‖LSeries.term a s m‖ ≤ C₁ * ψ m / (m : ℝ) ^ s.re := by
      rw [LSeries.norm_term_eq, ite_eq_right hm.ne']
      exact div_le_div_of_nonneg_right (hcoef m) (Real.rpow_pos_of_pos hm0 _).le
    have e1 : (m : ℝ) ^ (1 - s.re) = (m : ℝ) * (m : ℝ) ^ c / (m : ℝ) ^ (s.re + c) := by
      rw [show 1 - s.re = 1 + c - (s.re + c) by ring, Real.rpow_sub hm0, Real.rpow_add hm0,
        Real.rpow_one]
    have e2 : (m : ℝ) ^ (-s.re) = ((m : ℝ) ^ s.re)⁻¹ := Real.rpow_neg hm0.le _
    rw [e1, e2]
    exact truncatedPerron_error_integer_scalar hC₁ hC₂ (Real.rpow_pos_of_pos hm0 c) hQ
      (Real.rpow_pos_of_pos hm0 s.re) hD (Real.log_natCast_nonneg m) hlog2 hT0 hc Real.pi_pos
      (hψ m) hψ₂ hm0 hE' ht
  · -- the pointwise comparison
    have ht : 0 ≤ ‖LSeries.term a (s + (c : ℂ)) n‖ := norm_nonneg _
    have hgn : 0 ≤ ‖LSeries.term a (s + (c : ℂ)) n‖ / Real.log 2 := div_nonneg ht hlog2.le
    have h1n : 0 ≤ (if n ∈ Finset.Ico 1 m then
        4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) / ((m - n : ℕ) : ℝ) else 0) := by
      split_ifs
      · exact div_nonneg hB0 (Nat.cast_nonneg _)
      · exact le_rfl
    have h2n : 0 ≤ (if n ∈ Finset.Ico (1 + m) (m + m) then
        4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) / ((n - m : ℕ) : ℝ) else 0) := by
      split_ifs
      · exact div_nonneg hB0 (Nat.cast_nonneg _)
      · exact le_rfl
    by_cases h0 : n = 0 ∨ (n : ℝ) = (m : ℝ)
    · rw [ite_eq_left h0]
      linarith
    rw [ite_eq_right h0]
    obtain ⟨hn0, hnm⟩ := not_or.mp h0
    have hnm' : n ≠ m := fun h ↦ hnm (by rw [h])
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    by_cases hfar : 2 * n ≤ m ∨ 2 * m ≤ n
    · have hl : Real.log 2 ≤ |Real.log ((m : ℝ) / n)| :=
        truncatedPerron_error_noninteger_far hm0 hnpos (by exact_mod_cast hfar)
      have hle : ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log ((m : ℝ) / n)| ≤
          ‖LSeries.term a (s + (c : ℂ)) n‖ / Real.log 2 :=
        div_le_div_of_nonneg_left ht hlog2 hl
      linarith
    · obtain ⟨hl1, hl2⟩ := not_or.mp hfar
      have hn2 : (n : ℝ) < 2 * m := by exact_mod_cast not_le.mp hl2
      have hm2 : (m : ℝ) < 2 * n := by exact_mod_cast not_le.mp hl1
      have hlogb := truncatedPerron_error_noninteger_log hm0 hnpos hn2
      have hdist : 0 < |(m : ℝ) - n| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hnm))
      have h4 : (m : ℝ) ^ (s.re + c) / 4 ≤ (n : ℝ) ^ (s.re + c) := by
        have h1 : ((m : ℝ) / 2) ^ (s.re + c) ≤ (n : ℝ) ^ (s.re + c) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith [hσ.1])
        have h2 : (2 : ℝ) ^ (s.re + c) ≤ 4 := by
          calc (2 : ℝ) ^ (s.re + c) ≤ (2 : ℝ) ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le one_le_two hσ.2
            _ = 4 := by
                rw [Real.rpow_two]
                norm_num
        rw [Real.div_rpow hm0.le zero_le_two] at h1
        have h3 : 0 < (2 : ℝ) ^ (s.re + c) := by positivity
        exact (div_le_div_of_nonneg_left hQ.le h3 h2).trans h1
      have htK : ‖LSeries.term a (s + (c : ℂ)) n‖ ≤
          4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) := by
        rw [LSeries.norm_term_eq, ite_eq_right hn0, hσre]
        have han : ‖a n‖ ≤ C₁ * ψ (2 * m) :=
          (hcoef n).trans (mul_le_mul_of_nonneg_left (hmono (by omega)) hC₁.le)
        calc ‖a n‖ / (n : ℝ) ^ (s.re + c)
            ≤ C₁ * ψ (2 * m) / ((m : ℝ) ^ (s.re + c) / 4) :=
              div_le_div₀ (mul_pos hC₁ hψ₂).le han (by positivity) h4
          _ = 4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) := by
              field_simp
      have hmain : ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log ((m : ℝ) / n)| ≤
          4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) / |(m : ℝ) - n| := by
        calc ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log ((m : ℝ) / n)|
            ≤ 4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) / (|(m : ℝ) - n| / (2 * m)) :=
              div_le_div₀ hK0 htK (by positivity) hlogb
          _ = _ := by
              field_simp
      rcases lt_or_gt_of_ne hnm' with hlt | hgt
      · rw [ite_eq_left (Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hlt⟩)]
        have e : ((m - n : ℕ) : ℝ) = |(m : ℝ) - n| := by
          rw [Nat.cast_sub hlt.le, abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hlt))]
        rw [e]
        linarith
      · have hmem : n ∈ Finset.Ico (1 + m) (m + m) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        rw [ite_eq_left hmem]
        have e : ((n - m : ℕ) : ℝ) = |(m : ℝ) - n| := by
          rw [Nat.cast_sub hgt.le, abs_sub_comm, abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hgt))]
        rw [e]
        linarith

/-- Paper: Equation (B.7.1.8), p. 645, and the coefficient choice on p. 646.
The cutoff polynomial sums the twisted von Mangoldt coefficients, grouped by
the norm of the ideal, through the last integer norm at most `x`. -/
def heckeLogDerivPolynomial (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s n

/-- Paper: Equation (B.7.1.8), p. 645. The polynomial grouped by norm equals
the sum over all nonzero integral ideals whose norms are at most the cutoff. -/
theorem heckeLogDerivPolynomial_eq_sum_ideals (χ : U[F]) (x : ℝ) (s : ℂ) :
    heckeLogDerivPolynomial χ x s =
      ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x},
        heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ s := by
  classical
  let g : Ideal (𝓞 F) → ℂ := fun I ↦
    heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I / (I.absNorm : ℂ) ^ s
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) ⌊x⌋₊).subset
      fun I hI ↦ Nat.le_floor hI.2
  let T := hfin.toFinset
  have hfib (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊x⌋₊) :
      LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s n =
        ∑ I ∈ T with I.absNorm = n, g I := by
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1
    have hset : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n} =
        ↑(T.filter fun I ↦ I.absNorm = n) := by
      ext I
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, T, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨h0, h1⟩
        refine ⟨⟨h0, ?_⟩, h1⟩
        rw [h1]
        exact (Nat.le_floor_iff' hn0).mp (Finset.mem_Icc.mp hn).2
      · rintro ⟨⟨h0, -⟩, h1⟩
        exact ⟨h0, h1⟩
    rw [LSeries.term_of_ne_zero hn0, heckeLogDerivCoefficient]
    change (∑ᶠ I : ↥{I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n},
      heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I) / (n : ℂ) ^ s = _
    rw [hset, finsum_set_coe_eq_finsum_mem, finsum_mem_coe_finset, Finset.sum_div]
    refine Finset.sum_congr rfl fun I hI ↦ ?_
    change _ = heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I / (I.absNorm : ℂ) ^ s
    rw [(Finset.mem_filter.mp hI).2]
  change ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s n =
    ∑ᶠ I : ↥{I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}, g I
  rw [finsum_set_coe_eq_finsum_mem, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_congr rfl hfib]
  refine Finset.sum_fiberwise_of_maps_to (fun I hI ↦ ?_) _
  simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI
  exact Finset.mem_Icc.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1), Nat.le_floor hI.2⟩

/-- Paper: Theorem B.7.1.2(1), p. 645. The set `J_b` consists of the integer
cuts and the real cuts at distance at least `b` from the integers. -/
def perronCutoffSet (b : ℝ) : Set ℝ :=
  Set.range (Int.cast : ℤ → ℝ) ∪ {x : ℝ | b ≤ |x - (round x : ℝ)|}

/-- Paper: Theorem B.7.1.2(1), p. 645. For positive `b`, integer cuts are always
allowed and half-integer cuts are allowed precisely when `b ≤ 1/2`. -/
theorem perronCutoffSet_integer_half_integer {b : ℝ} (hb : 0 < b) (n : ℤ) :
    (n : ℝ) ∈ perronCutoffSet b ∧
      ((n : ℝ) + 1 / 2 ∈ perronCutoffSet b ↔ b ≤ 1 / 2) := by
  refine ⟨Or.inl ⟨n, rfl⟩, ?_⟩
  have hround : round ((n : ℝ) + 1 / 2) = n + 1 := by
    rw [round_eq, add_assoc, add_halves, Int.floor_intCast_add, Int.floor_one]
  have hnot : (n : ℝ) + 1 / 2 ∉ Set.range (Int.cast : ℤ → ℝ) := by
    rintro ⟨k, hk⟩
    have h : ((2 * (k - n) : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h' : 2 * (k - n) = 1 := by exact_mod_cast h
    omega
  have habs : |(n : ℝ) + 1 / 2 - (round ((n : ℝ) + 1 / 2) : ℝ)| = 1 / 2 := by
    rw [hround, Int.cast_add, Int.cast_one, show (n : ℝ) + 1 / 2 - (n + 1) = -(1 / 2) by ring,
      abs_neg, abs_of_pos one_half_pos]
  change (n : ℝ) + 1 / 2 ∈ Set.range (Int.cast : ℤ → ℝ) ∨
    b ≤ |(n : ℝ) + 1 / 2 - (round ((n : ℝ) + 1 / 2) : ℝ)| ↔ _
  rw [habs]
  exact ⟨fun h ↦ h.resolve_left hnot, Or.inr⟩

/-- The finite L-function of the trivial character is the Dedekind zeta function. -/
private theorem heckeLogDerivPolynomial_perron_error_zeta (s : halfPlane) :
    finiteHeckeL (1 : U[F]) s = dedekindZeta F s := by
  have h := completedHeckeL_one_eq_dedekindZeta (F := F) s
  rw [← heckeGammaFactor_one] at h
  change heckeGammaFactor (1 : U[F]) s * finiteHeckeL (1 : U[F]) s = _ at h
  have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
  exact mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) hs) h

/-- A norm power of the trivial character is unramified everywhere. -/
private theorem heckeLogDerivPolynomial_perron_error_unramified (z : ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : (ideleClassNormTwist (1 : U[F]) z).IsUnramifiedAt v := by
  rw [HeckeCharacter.isUnramifiedAt_iff]
  intro u
  let g := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
  have hn : ‖(g : v.adicCompletion F)‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show g ∈ (v.adicCompletionIntegers F).units from ⟨u.val.property, u.inv.property⟩))
  change (ideleClassNormTwist (1 : U[F]) z).restrict v g = 1
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  change _ * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v g) : NNReal) : ℝ) :
    ℂ) ^ z = _
  rw [ideleClassNorm_ofAdicCompletion]
  change _ * (‖(g : v.adicCompletion F)‖ : ℂ) ^ z = _
  rw [hn, Complex.ofReal_one, Complex.one_cpow, mul_one]
  rfl

/-- At a uniformizer, the norm power `|·|^z` takes the value `N(v)^(-z)`. -/
private theorem heckeLogDerivPolynomial_perron_error_localValue (z : ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (ideleClassNormTwist (1 : U[F]) z).localValue v = ((v.asIdeal.absNorm : ℕ) : ℂ) ^ (-z) := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  have hπ := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose :
    v.adicCompletion F) hπ.ne_zero
  change (ideleClassNormTwist (1 : U[F]) z).restrict v (u : v.adicCompletion F) = _
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  change _ * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) :
    NNReal) : ℝ) : ℂ) ^ z = _
  rw [ideleClassNorm_ofAdicCompletion]
  change _ * (‖(u : v.adicCompletion F)‖ : ℂ) ^ z = _
  have hval : val (u : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)))
  have hq : (0 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hnorm : ‖(u : v.adicCompletion F)‖ = ((v.asIdeal.absNorm : ℝ))⁻¹ := by
    rw [FinitePlace.norm_def]
    change ((WithZeroMulInt.toNNReal _ (val u) : NNReal) : ℝ) = _
    rw [hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    simp
  rw [hnorm, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.ofReal_natCast]
    exact (Complex.natCast_arg).symm ▸ Real.pi_pos.ne), Complex.cpow_neg]
  exact one_mul _

/-- The twisted von Mangoldt weight of a norm power of the trivial character. -/
private theorem heckeLogDerivPolynomial_perron_error_vonMangoldt (z : ℂ) (I : Ideal (𝓞 F)) :
    heckeIdealVonMangoldt (ideleClassNormTwist (1 : U[F]) z) I =
      ((I.absNorm : ℕ) : ℂ) ^ (-z) * (idealVonMangoldt I : ℂ) := by
  classical
  by_cases h : ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k
  · obtain ⟨v, k, hk, rfl⟩ := h
    rw [heckeIdealVonMangoldt_prime_pow _ v
      (heckeLogDerivPolynomial_perron_error_unramified z v) hk,
      heckeLogDerivPolynomial_perron_error_localValue, idealVonMangoldt_prime_pow v hk, map_pow,
      Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  · have h0 : idealVonMangoldt I = 0 := by
      unfold idealVonMangoldt
      exact dite_eq_right_iff.mpr fun h' ↦ absurd h' h
    rw [heckeIdealVonMangoldt, h0]
    simp

/-- To the right of one, the coefficients of the cutoff polynomial are the Dirichlet
coefficients of the negative logarithmic derivative of Dedekind zeta, shifted by `t₀`. -/
private theorem heckeLogDerivPolynomial_perron_error_hasSum (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) (w : ℂ) (hw : 1 < w.re) :
    LSeriesHasSum (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) w
      (-logDeriv Z (w - Complex.I * t₀)) := by
  classical
  have hw' : 1 < (w - Complex.I * t₀).re := by simpa using hw
  have h := (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) Z hZ
    (fun s ↦ (hSeries s).trans (heckeLogDerivPolynomial_perron_error_zeta s).symm)
    ⟨w - Complex.I * t₀, hw'⟩).2.2.neg
  let f : {I : Ideal (𝓞 F) // I ≠ ⊥} → ℂ := fun I ↦
    heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ w
  have hf : HasSum f (-logDeriv Z (w - Complex.I * t₀)) := by
    refine h.congr_fun fun I ↦ ?_
    have hN : (I.val.absNorm : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    have hpow (y : ℂ) : (I.val.absNorm : ℂ) ^ y ≠ 0 :=
      fun h ↦ hN ((Complex.cpow_eq_zero_iff _ _).mp h).1
    simp only [f]
    rw [hχ, heckeLogDerivPolynomial_perron_error_vonMangoldt,
      heckeLogDerivPolynomial_perron_error_vonMangoldt, neg_zero, Complex.cpow_zero, one_mul,
      neg_div, neg_neg, Complex.cpow_sub _ _ hN, neg_mul, neg_neg]
    field_simp [hpow w, hpow (Complex.I * t₀)]
  have hg := hf.tsum_fiberwise (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦ I.val.absNorm)
  refine hg.congr_fun fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have : IsEmpty ↑((fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦ I.val.absNorm) ⁻¹' {0}) :=
      ⟨fun b ↦ b.val.property (Ideal.absNorm_eq_zero_iff.mp b.property)⟩
    rw [tsum_empty, LSeries.term_zero]
  · let S := {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}
    have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n}.Finite :=
      (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset fun _ h ↦ h.2
    have : Finite S := hfin.to_subtype
    have : Fintype S := Fintype.ofFinite _
    let e : ↑((fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦ I.val.absNorm) ⁻¹' {n}) ≃ S :=
      { toFun := fun b ↦ ⟨b.val.val, b.val.property, b.property⟩
        invFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, I.property.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [← e.symm.tsum_eq, tsum_fintype, LSeries.term_of_ne_zero hn, heckeLogDerivCoefficient,
      finsum_eq_sum_of_fintype, Finset.sum_div]
    refine Finset.sum_congr rfl fun I _ ↦ ?_
    change _ = _ / ((I.val.absNorm : ℕ) : ℂ) ^ w
    rw [I.property.2]
    rfl

/-- The untwisted coefficients are the real sums of the ideal von Mangoldt weights. -/
private theorem heckeLogDerivPolynomial_perron_error_coeff_real (n : ℕ) :
    heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n =
      ((∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}, idealVonMangoldt I.val : ℝ) : ℂ) := by
  classical
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset fun _ h ↦ h.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} := Fintype.ofFinite _
  rw [heckeLogDerivCoefficient, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  rw [heckeLogDerivPolynomial_perron_error_vonMangoldt, neg_zero, Complex.cpow_zero, one_mul]

private theorem heckeLogDerivPolynomial_perron_error_idealVonMangoldt_nonneg
    (I : Ideal (𝓞 F)) : 0 ≤ idealVonMangoldt I := by
  unfold idealVonMangoldt
  split_ifs
  exacts [Real.log_natCast_nonneg _, le_rfl]

/-- The untwisted coefficients are nonnegative reals. -/
private theorem heckeLogDerivPolynomial_perron_error_coeff_norm (n : ℕ) :
    heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n =
      (‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖ : ℂ) := by
  have h0 : 0 ≤ ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}, idealVonMangoldt I.val :=
    finsum_nonneg fun I ↦ heckeLogDerivPolynomial_perron_error_idealVonMangoldt_nonneg I.val
  rw [heckeLogDerivPolynomial_perron_error_coeff_real, Complex.norm_real, Real.norm_of_nonneg h0]

/-- A twist by `|·|^(-i t₀)` does not increase the coefficients in norm. -/
private theorem heckeLogDerivPolynomial_perron_error_coeff_le (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) (n : ℕ) :
    ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n‖ ≤
      ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖ := by
  classical
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset fun _ h ↦ h.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} := Fintype.ofFinite _
  have h0 : 0 ≤ ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}, idealVonMangoldt I.val :=
    finsum_nonneg fun I ↦ heckeLogDerivPolynomial_perron_error_idealVonMangoldt_nonneg I.val
  rw [heckeLogDerivPolynomial_perron_error_coeff_real (F := F) n, Complex.norm_real,
    Real.norm_of_nonneg h0, heckeLogDerivCoefficient, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ ↦ ?_)
  rw [hχ, heckeLogDerivPolynomial_perron_error_vonMangoldt, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (heckeLogDerivPolynomial_perron_error_idealVonMangoldt_nonneg _),
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr I.property.1))]
  simp

/-- The coefficient at one vanishes: the unit ideal is not a prime power. -/
private theorem heckeLogDerivPolynomial_perron_error_coeff_one :
    heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) 1 = 0 := by
  classical
  rw [heckeLogDerivPolynomial_perron_error_coeff_real, Complex.ofReal_eq_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun I ↦ ?_
  have hI : I.val = ⊤ := Ideal.absNorm_eq_one_iff.mp I.property.2
  unfold idealVonMangoldt
  refine dite_eq_right_iff.mpr fun ⟨v, k, hk, hv⟩ ↦ absurd hv ?_
  rw [hI]
  intro h
  have hle := Ideal.pow_le_self (I := v.asIdeal) hk.ne'
  rw [← h] at hle
  exact v.isPrime.ne_top (top_le_iff.mp hle)

/-- The untwisted coefficients are at most a constant times `log n`. -/
private theorem heckeLogDerivPolynomial_perron_error_coeff_log :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖ ≤ C * Real.log n := by
  obtain ⟨C, hC, h⟩ := heckeLogDerivCoefficient_bound (Module.finrank ℚ F)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (h F rfl)
  let b : ℕ → ℝ := fun n ↦ ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖
  let D := ∑ k ∈ Finset.range M, b k
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨C + D / Real.log 2, by positivity, fun n ↦ ?_⟩
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · have : IsEmpty {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = 0} :=
        ⟨fun I ↦ I.property.1 (Ideal.absNorm_eq_zero_iff.mp I.property.2)⟩
      rw [heckeLogDerivCoefficient, finsum_of_isEmpty]
      simp
    · simp [heckeLogDerivPolynomial_perron_error_coeff_one]
  · have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
    rcases le_or_gt M n with hMn | hMn
    · refine (hM n hMn 1).trans ?_
      have : 0 ≤ D / Real.log 2 * Real.log n := by positivity
      linarith
    · have h1 : b n ≤ D :=
        Finset.single_le_sum (f := b) (fun _ _ ↦ norm_nonneg _) (Finset.mem_range.mpr hMn)
      have h2 : D ≤ D / Real.log 2 * Real.log n := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
        exact mul_le_mul_of_nonneg_left hlogn hD
      have h3 : 0 ≤ C * Real.log n := by positivity
      change b n ≤ _
      linarith

/-- On the real half-line to the right of one, the Dirichlet series of the untwisted
coefficients sums to the negative logarithmic derivative of Dedekind zeta. -/
private theorem heckeLogDerivPolynomial_perron_error_hasSum_real (Z : ℂ → ℂ)
    (hZ : MeromorphicNFOn Z univ) (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    (σ : ℝ) (hσ : 1 < σ) :
    HasSum (fun n : ℕ ↦
      ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖ / (n : ℝ) ^ σ)
      (-(logDeriv Z σ).re) := by
  have h := heckeLogDerivPolynomial_perron_error_hasSum (1 : U[F]) 0 (by simp) Z hZ hSeries σ
    (by simpa using hσ)
  rw [Complex.ofReal_zero, mul_zero, sub_zero] at h
  have hre := Complex.hasSum_re h
  rw [Complex.neg_re] at hre
  refine hre.congr_fun fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (show σ ≠ 0 by linarith)]
  · rw [LSeries.term_of_ne_zero hn, heckeLogDerivPolynomial_perron_error_coeff_norm,
      ← Complex.ofReal_natCast, ← Complex.ofReal_cpow n.cast_nonneg, ← Complex.ofReal_div,
      Complex.ofReal_re]
    simp only [Complex.norm_real, norm_norm]

/-- To the right of one and up to two, the Dirichlet series of the untwisted coefficients is at
most `1/(σ - 1)` plus a constant: Dedekind zeta has a simple pole at one. -/
private theorem heckeLogDerivPolynomial_perron_error_pole (Z : ℂ → ℂ)
    (hZ : MeromorphicNFOn Z univ) (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      ∑' n : ℕ, ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖ /
        (n : ℝ) ^ σ ≤ 1 / (σ - 1) + K := by
  have hS₀ : ∀ s : halfPlane, Z s = finiteHeckeL (1 : U[F]) s :=
    fun s ↦ (hSeries s).trans (heckeLogDerivPolynomial_perron_error_zeta s).symm
  have hreal : Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using (show 1 < r from hr).ne'
  have hne (r : ℝ) (hr : 1 < r) : Z r ≠ 0 :=
    (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) Z hZ hS₀
      ⟨(r : ℂ), show 1 < (r : ℂ).re by simpa using hr⟩).2.1
  have htop : meromorphicOrderAt Z 1 ≠ ⊤ := by
    intro h
    obtain ⟨r, hr, hr1⟩ := ((hreal.eventually (meromorphicOrderAt_eq_top_iff.mp h)).and
      self_mem_nhdsWithin).exists
    exact hne r hr1 hr
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp htop
  obtain ⟨g, hg, hg1, hEq⟩ := (meromorphicOrderAt_eq_int_iff (hZ (mem_univ 1)).meromorphicAt).mp
    hm.symm
  -- The pole is at most simple, by the residue of Dedekind zeta.
  have hm1 : -1 ≤ m := by
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = -(m + 1) :=
      ⟨(-(m + 1)).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hk0 : k ≠ 0 := by omega
    have hlimZ : Tendsto (fun σ : ℝ ↦ ((σ : ℂ) - 1) * Z σ) (𝓝[>] 1)
        (𝓝 (dedekindZeta_residue F : ℂ)) := by
      refine (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      rw [show Z σ = dedekindZeta F σ from
        hSeries ⟨(σ : ℂ), show 1 < (σ : ℂ).re by simpa using hσ⟩]
    have hlimP : Tendsto (fun σ : ℝ ↦ ((σ : ℂ) - 1) ^ k * (((σ : ℂ) - 1) * Z σ)) (𝓝[>] 1)
        (𝓝 0) := by
      have h0 : Tendsto (fun σ : ℝ ↦ ((σ : ℂ) - 1) ^ k) (𝓝[>] 1) (𝓝 0) := by
        have hc : Continuous (fun σ : ℝ ↦ ((σ : ℂ) - 1) ^ k) := by fun_prop
        have h := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
        simpa [zero_pow hk0] using h
      simpa using h0.mul hlimZ
    have hlimg : Tendsto (fun σ : ℝ ↦ g σ) (𝓝[>] 1) (𝓝 (g 1)) :=
      hg.continuousAt.tendsto.comp (hreal.mono_right nhdsWithin_le_nhds)
    have heq : (fun σ : ℝ ↦ ((σ : ℂ) - 1) ^ k * (((σ : ℂ) - 1) * Z σ)) =ᶠ[𝓝[>] 1]
        fun σ ↦ g σ := by
      filter_upwards [hreal.eventually hEq, self_mem_nhdsWithin] with σ hσ hσ1
      have hs : (σ : ℂ) - 1 ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast (show 1 < σ from hσ1).ne')
      rw [hσ, smul_eq_mul, ← mul_assoc, ← mul_assoc]
      have h1 : ((σ : ℂ) - 1) ^ k * ((σ : ℂ) - 1) * ((σ : ℂ) - 1) ^ m = 1 := by
        rw [← zpow_natCast, ← zpow_add_one₀ hs, ← zpow_add₀ hs, hk,
          show -(m + 1) + 1 + m = 0 by ring, zpow_zero]
      rw [h1, one_mul]
    exact hg1 (tendsto_nhds_unique (hlimP.congr' heq) hlimg).symm
  have hcont : ContinuousAt (logDeriv g) 1 :=
    hg.deriv.continuousAt.div hg.continuousAt hg1
  have hbound : ∀ᶠ z in 𝓝 (1 : ℂ), ‖logDeriv g z‖ ≤ ‖logDeriv g 1‖ + 1 := by
    filter_upwards [hcont.norm.eventually (gt_mem_nhds (lt_add_one ‖logDeriv g 1‖))] with z hz
    exact hz.le
  have hlog := logDeriv_congr_nhdsNE hEq
  have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ),
      logDeriv Z z = (m : ℂ) / (z - 1) + logDeriv g z ∧
        ‖logDeriv g z‖ ≤ ‖logDeriv g 1‖ + 1 := by
    filter_upwards [hlog, nhdsWithin_le_nhds hbound, nhdsWithin_le_nhds hg.eventually_analyticAt,
      nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg1), self_mem_nhdsWithin]
      with z hz hb han hgz hz1
    refine ⟨?_, hb⟩
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hd : DifferentiableAt ℂ (fun w : ℂ ↦ w - 1) z := differentiableAt_id.sub_const 1
    rw [hz, show (fun w : ℂ ↦ (w - 1) ^ m • g w) = (fun w ↦ (w - 1) ^ m) * g from rfl,
      logDeriv_mul (f := fun w : ℂ ↦ (w - 1) ^ m) z (zpow_ne_zero _ hz1') hgz
      (hd.zpow (Or.inl hz1')) han.differentiableAt, logDeriv_fun_zpow hd]
    congr 1
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
    field_simp
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (hreal.eventually hev)
  have hu1 : 1 < u := hu
  let C₀ := ‖logDeriv g 1‖ + 1
  have hnear (σ : ℝ) (hσ : 1 < σ) (hσu : σ ≤ u) : -(logDeriv Z σ).re ≤ 1 / (σ - 1) + C₀ := by
    obtain ⟨h1, h2⟩ := hsub ⟨hσ, hσu⟩
    rw [h1, Complex.add_re]
    have hre : ((m : ℂ) / ((σ : ℂ) - 1)).re = m / (σ - 1) := by
      rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, show (m : ℂ) = ((m : ℝ) : ℂ) by
        norm_cast, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [hre]
    have hσ1 : 0 < σ - 1 := by linarith
    have hm' : -(m : ℝ) / (σ - 1) ≤ 1 / (σ - 1) := by
      apply div_le_div_of_nonneg_right _ hσ1.le
      have : (-1 : ℝ) ≤ m := by exact_mod_cast hm1
      linarith
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans h2)).1
    rw [neg_div] at hm'
    linarith
  have hC₀ : 0 ≤ C₀ := by positivity
  refine ⟨max C₀ (1 / (u - 1) + C₀), hC₀.trans (le_max_left _ _), fun σ hσ hσ2 ↦ ?_⟩
  have hsum := heckeLogDerivPolynomial_perron_error_hasSum_real Z hZ hSeries σ hσ
  rw [hsum.tsum_eq]
  rcases le_or_gt σ u with hσu | hσu
  · have := hnear σ hσ hσu
    have := le_max_left C₀ (1 / (u - 1) + C₀)
    linarith
  · have hsumu := heckeLogDerivPolynomial_perron_error_hasSum_real Z hZ hSeries u hu1
    have hle : -(logDeriv Z σ).re ≤ -(logDeriv Z u).re := by
      refine hasSum_le (fun n ↦ ?_) hsum hsumu
      rcases eq_or_ne n 0 with rfl | hn
      · simp [Real.zero_rpow (show σ ≠ 0 by linarith), Real.zero_rpow (show u ≠ 0 by linarith)]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          (Real.rpow_le_rpow_of_exponent_le hn1 hσu.le)
    have := hnear u hu1 le_rfl
    have h0 : 0 < 1 / (σ - 1) := by
      have : 0 < σ - 1 := by linarith
      positivity
    have := le_max_right C₀ (1 / (u - 1) + C₀)
    linarith

/-- On the line `1 + c`, the Dirichlet series of the untwisted coefficients is at most a constant
divided by `c (c + 2)`, for every `c > 0`: near zero by the pole, and for `c > 1` because the
series decays like `2^(-c)`. -/
private theorem heckeLogDerivPolynomial_perron_error_series (Z : ℂ → ℂ)
    (hZ : MeromorphicNFOn Z univ) (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 0 < c →
      Summable (fun n : ℕ ↦ ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖ /
        (n : ℝ) ^ (1 + c)) ∧
      (c + 2) * ∑' n : ℕ, ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖ /
        (n : ℝ) ^ (1 + c) ≤ K / c := by
  obtain ⟨K₀, hK₀, hpole⟩ := heckeLogDerivPolynomial_perron_error_pole Z hZ hSeries
  set b : ℕ → ℝ := fun n ↦ ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖
    with hb_def
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨3 * (1 + K₀) + 12 * (1 + K₀) / Real.log 2 ^ 2, by positivity, fun c hc ↦ ?_⟩
  have hsum := heckeLogDerivPolynomial_perron_error_hasSum_real Z hZ hSeries (1 + c)
    (by linarith)
  refine ⟨hsum.summable, ?_⟩
  have hA0 : 0 ≤ ∑' n : ℕ, b n / (n : ℝ) ^ (1 + c) :=
    tsum_nonneg fun n ↦ div_nonneg (norm_nonneg _) (by positivity)
  have hK : 3 * (1 + K₀) ≤ 3 * (1 + K₀) + 12 * (1 + K₀) / Real.log 2 ^ 2 := by
    have : 0 ≤ 12 * (1 + K₀) / Real.log 2 ^ 2 := by positivity
    linarith
  rcases le_or_gt c 1 with hc1 | hc1
  · have h := hpole (1 + c) (by linarith) (by linarith)
    rw [show 1 + c - 1 = c by ring] at h
    have h1 : (c + 2) * ∑' n : ℕ, b n / (n : ℝ) ^ (1 + c) ≤ 3 * (1 / c + K₀) :=
      mul_le_mul (by linarith) h hA0 (by positivity)
    have h2 : 3 * (1 / c + K₀) ≤ 3 * (1 + K₀) / c := by
      have : K₀ ≤ K₀ / c := by
        rw [le_div_iff₀ hc]
        nlinarith
      have e : 3 * (1 + K₀) / c = 3 * (1 / c) + 3 * (K₀ / c) := by ring
      rw [e]
      linarith
    exact h1.trans (h2.trans (div_le_div_of_nonneg_right hK hc.le))
  · have hsum2 := heckeLogDerivPolynomial_perron_error_hasSum_real Z hZ hSeries 2 one_lt_two
    have hA2 : ∑' n : ℕ, b n / (n : ℝ) ^ (2 : ℝ) ≤ 1 + K₀ := by
      have := hpole 2 one_lt_two le_rfl
      rw [show (1 : ℝ) / (2 - 1) = 1 by norm_num] at this
      exact this
    have hterm (n : ℕ) :
        b n / (n : ℝ) ^ (1 + c) ≤ (2 : ℝ) ^ (1 - c) * (b n / (n : ℝ) ^ (2 : ℝ)) := by
      rcases lt_or_ge n 2 with hn | hn
      · interval_cases n
        · simp [Real.zero_rpow (show 1 + c ≠ 0 by linarith)]
        · simp [b, heckeLogDerivPolynomial_perron_error_coeff_one]
      · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
        have hn0 : (0 : ℝ) < n := by linarith
        have hsplit : (n : ℝ) ^ (1 + c) = (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ (c - 1) := by
          rw [← Real.rpow_add hn0]
          ring_nf
        have hpow : (2 : ℝ) ^ (c - 1) ≤ (n : ℝ) ^ (c - 1) :=
          Real.rpow_le_rpow (by norm_num) hn2 (by linarith)
        have h21 : (2 : ℝ) ^ (1 - c) = ((2 : ℝ) ^ (c - 1))⁻¹ := by
          rw [← Real.rpow_neg (by norm_num)]
          ring_nf
        rw [hsplit, h21, ← div_eq_inv_mul, div_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          (mul_le_mul_of_nonneg_left hpow (by positivity))
    have hA : ∑' n : ℕ, b n / (n : ℝ) ^ (1 + c) ≤ (2 : ℝ) ^ (1 - c) * (1 + K₀) := by
      calc ∑' n : ℕ, b n / (n : ℝ) ^ (1 + c)
          ≤ ∑' n : ℕ, (2 : ℝ) ^ (1 - c) * (b n / (n : ℝ) ^ (2 : ℝ)) :=
            hsum.summable.tsum_le_tsum hterm (hsum2.summable.mul_left _)
        _ = (2 : ℝ) ^ (1 - c) * ∑' n : ℕ, b n / (n : ℝ) ^ (2 : ℝ) := tsum_mul_left
        _ ≤ (2 : ℝ) ^ (1 - c) * (1 + K₀) := mul_le_mul_of_nonneg_left hA2 (by positivity)
    -- `c² ≤ (2 / log² 2) 2^c`, from the quadratic term of the exponential series.
    have hexp : c ^ 2 * Real.log 2 ^ 2 ≤ 2 * (2 : ℝ) ^ c := by
      have h := Real.pow_div_factorial_le_exp (c * Real.log 2) (by positivity) 2
      rw [Real.rpow_def_of_pos two_pos, mul_comm (Real.log 2) c]
      norm_num [Nat.factorial] at h
      have e : (c * Real.log 2) ^ 2 = c ^ 2 * Real.log 2 ^ 2 := by ring
      linarith
    have h2c : (2 : ℝ) ^ (1 - c) = 2 / (2 : ℝ) ^ c := by
      rw [Real.rpow_sub two_pos, Real.rpow_one]
    have hpos : 0 < (2 : ℝ) ^ c := by positivity
    rw [le_div_iff₀ hc]
    have hcc : c * (c + 2) ≤ 3 * c ^ 2 := by nlinarith
    calc ((c + 2) * ∑' n : ℕ, b n / (n : ℝ) ^ (1 + c)) * c
        ≤ ((c + 2) * ((2 : ℝ) ^ (1 - c) * (1 + K₀))) * c := by
          gcongr
      _ = 2 * (c * (c + 2)) / (2 : ℝ) ^ c * (1 + K₀) := by rw [h2c]; ring
      _ ≤ 2 * (3 * c ^ 2) / (2 : ℝ) ^ c * (1 + K₀) := by
          gcongr
      _ ≤ 12 * (1 + K₀) / Real.log 2 ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hpos (by positivity)]
          nlinarith [hexp, hK₀]
      _ ≤ 3 * (1 + K₀) + 12 * (1 + K₀) / Real.log 2 ^ 2 := by linarith

/-- The harmonic sum up to `k` is at most `1 + log k`. -/
private theorem heckeLogDerivPolynomial_perron_error_harmonic (k : ℕ) :
    ∑ j ∈ Finset.range k, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have hstep : 1 / ((k : ℝ) + 1) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log k := by
        rw [← Real.log_div (by positivity) hk'.ne']
        have h := Real.one_sub_inv_le_log_of_pos (x := ((k + 1 : ℕ) : ℝ) / k) (by positivity)
        have e : 1 - (((k + 1 : ℕ) : ℝ) / k)⁻¹ = 1 / ((k : ℝ) + 1) := by
          push_cast
          field_simp
          ring
        linarith
      linarith

/-- A shifted harmonic sum: `∑_{j < k} 1/(δ + j) ≤ 1/δ + 1 + log k` for `δ > 0`. -/
private theorem heckeLogDerivPolynomial_perron_error_shifted {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∑ j ∈ Finset.range k, 1 / (δ + j) ≤ 1 / δ + 1 + Real.log k := by
  rcases k with _ | k
  · simp
    positivity
  · rw [Finset.sum_range_succ']
    have h1 : ∑ j ∈ Finset.range k, 1 / (δ + ((j + 1 : ℕ) : ℝ)) ≤
        ∑ j ∈ Finset.range k, 1 / ((j : ℝ) + 1) := by
      refine Finset.sum_le_sum fun j _ ↦ ?_
      push_cast
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 := heckeLogDerivPolynomial_perron_error_harmonic k
    have h3 : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · exact Real.log_le_log (by exact_mod_cast hk) (by push_cast; linarith)
    simp only [Nat.cast_zero, add_zero]
    linarith

/-- The sum of `1/(x - n)` over the positive integers `n < x`. -/
private theorem heckeLogDerivPolynomial_perron_error_left {x : ℝ} (hx : 1 < x) :
    ∑ n ∈ Finset.Ico 1 ⌈x⌉₊, 1 / (x - n) ≤
      1 / (x - ((⌈x⌉₊ - 1 : ℕ) : ℝ)) + 1 + Real.log x := by
  set M := ⌈x⌉₊ with hM
  have hM2 : 2 ≤ M := by
    have : (1 : ℝ) < M := hx.trans_le (Nat.le_ceil x)
    exact_mod_cast this
  set m := M - 1 with hm
  have hmM : M = m + 1 := by omega
  have hmx : (m : ℝ) < x := by
    have : m < M := by omega
    exact Nat.lt_ceil.mp this
  have hxm : x ≤ (m : ℝ) + 1 := by
    have h := Nat.ceil_le.mp (le_of_eq hmM)
    push_cast at h
    exact h
  have hδ : 0 < x - m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  rw [Finset.sum_Ico_eq_sum_range, show M - 1 = m from rfl,
    ← Finset.sum_range_reflect]
  have hre : ∑ j ∈ Finset.range m, 1 / (x - ((1 + (m - 1 - j) : ℕ) : ℝ)) =
      ∑ j ∈ Finset.range m, 1 / ((x - m) + j) := by
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : j < m := Finset.mem_range.mp hj
    have e : ((1 + (m - 1 - j) : ℕ) : ℝ) = m - j := by
      rw [show 1 + (m - 1 - j) = m - j by omega, Nat.cast_sub hj'.le]
    rw [e]
    ring_nf
  rw [hre]
  refine (heckeLogDerivPolynomial_perron_error_shifted hδ m).trans ?_
  have hlog : Real.log m ≤ Real.log x := Real.log_le_log (by linarith) hmx.le
  linarith

/-- The sum of `1/(n - x)` over the integers `n` with `x < n < N`. -/
private theorem heckeLogDerivPolynomial_perron_error_right (x : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Ico (⌊x⌋₊ + 1) N, 1 / ((n : ℝ) - x) ≤
      1 / (((⌊x⌋₊ + 1 : ℕ) : ℝ) - x) + 1 + Real.log N := by
  set m := ⌊x⌋₊ + 1 with hm
  have hδ : 0 < (m : ℝ) - x := by
    have := Nat.lt_floor_add_one x
    push_cast [hm]
    linarith
  rw [Finset.sum_Ico_eq_sum_range]
  have hre : ∑ j ∈ Finset.range (N - m), 1 / (((m + j : ℕ) : ℝ) - x) =
      ∑ j ∈ Finset.range (N - m), 1 / (((m : ℝ) - x) + j) := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast
    ring_nf
  rw [hre]
  refine (heckeLogDerivPolynomial_perron_error_shifted hδ (N - m)).trans ?_
  have hlog : Real.log ((N - m : ℕ) : ℝ) ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos (N - m) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg N
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.sub_le N m)
  linarith

/-- One term of the Perron error sum. Left of the cutoff, `e^(cℓ)/ℓ ≤ 1/ℓ + c e^(cℓ)` splits off
a term free of `c`; right of the cutoff and up to `2x` the power `(x/n)^c` is at most one; beyond
`2x` the logarithm is at least `log 2`. -/
private theorem heckeLogDerivPolynomial_perron_error_kernel {x c C₁ β : ℝ} {n : ℕ}
    (hx : 1 < x) (hc : 0 < c) (hC₁ : 0 ≤ C₁) (hβ0 : 0 ≤ β) (hβ : β ≤ C₁ * Real.log n)
    (hn : 1 ≤ n) (hnx : (n : ℝ) ≠ x) :
    x ^ c * (β / (n : ℝ) ^ (1 + c) / |Real.log (x / n)|) ≤
      ((if (n : ℝ) < x then C₁ * Real.log x * (1 / n + 1 / (x - n)) else 0) +
      (if x < n ∧ (n : ℝ) ≤ 2 * x then C₁ * Real.log (2 * x) * (1 / (n - x)) else 0)) +
      (c + 2) * (x ^ c * (β / (n : ℝ) ^ (1 + c))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  set E := (x / n) ^ c with hE
  have hsplit : x ^ c * (β / (n : ℝ) ^ (1 + c)) = β / n * E := by
    rw [hE, Real.div_rpow hx0.le hn0.le, Real.rpow_add hn0, Real.rpow_one]
    field_simp
  have hE0 : 0 < E := by positivity
  have hA0 : 0 ≤ x ^ c * (β / (n : ℝ) ^ (1 + c)) := by positivity
  rw [mul_div_assoc', ← mul_div_assoc, mul_div_assoc, hsplit]
  rcases lt_or_gt_of_ne hnx with hlt | hgt
  · -- Left of the cutoff.
    have hℓ : 0 < Real.log (x / n) := Real.log_pos ((one_lt_div hn0).mpr hlt)
    rw [abs_of_pos hℓ, ite_eq_left hlt, ite_eq_right (fun h ↦ (lt_asymm hlt h.1).elim), add_zero]
    have hEexp : E = Real.exp (c * Real.log (x / n)) := by
      rw [hE, Real.rpow_def_of_pos (div_pos hx0 hn0), mul_comm]
    -- `E ≤ 1 + c ℓ E`.
    have hE1 : E ≤ 1 + c * Real.log (x / n) * E := by
      have h := Real.add_one_le_exp (-(c * Real.log (x / n)))
      rw [hEexp]
      have hprod : Real.exp (-(c * Real.log (x / n))) * Real.exp (c * Real.log (x / n)) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith [Real.exp_pos (c * Real.log (x / n))]
    have hlog : (x - n) / x ≤ Real.log (x / n) := by
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hx0 hn0)
      rw [inv_div] at h
      have e : 1 - (n : ℝ) / x = (x - n) / x := by field_simp
      linarith
    have hxn : 0 < x - n := by linarith
    have hlogn : Real.log n ≤ Real.log x := Real.log_le_log hn0 hlt.le
    -- The term free of `c`.
    have h1 : β / n / Real.log (x / n) ≤ C₁ * Real.log x * (1 / n + 1 / (x - n)) := by
      have hβ' : β ≤ C₁ * Real.log x := hβ.trans (mul_le_mul_of_nonneg_left hlogn hC₁)
      calc β / n / Real.log (x / n) ≤ β / n / ((x - n) / x) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hlog
        _ = β * (1 / n + 1 / (x - n)) := by field_simp; ring
        _ ≤ C₁ * Real.log x * (1 / n + 1 / (x - n)) :=
            mul_le_mul_of_nonneg_right hβ' (by positivity)
    have h2 : β / n * E / Real.log (x / n) ≤ β / n / Real.log (x / n) + c * (β / n * E) := by
      rw [div_le_iff₀ hℓ, add_mul, div_mul_cancel₀ _ hℓ.ne']
      have hb : 0 ≤ β / n := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hE1 hb]
    have h3 : c * (β / n * E) ≤ (c + 2) * (β / n * E) := by
      have : 0 ≤ β / n * E := by positivity
      nlinarith
    linarith
  · -- Right of the cutoff.
    have hℓ : Real.log (x / n) < 0 := Real.log_neg (by positivity) ((div_lt_one hn0).mpr hgt)
    have habs : |Real.log (x / n)| = Real.log (n / x) := by
      rw [abs_of_neg hℓ, ← Real.log_inv, inv_div]
    rw [habs, ite_eq_right (fun h ↦ (lt_asymm hgt h).elim), zero_add]
    have hE1 : E ≤ 1 := Real.rpow_le_one (by positivity) ((div_le_one hn0).mpr hgt.le) hc.le
    have hb : 0 ≤ β / n := by positivity
    by_cases hn2 : (n : ℝ) ≤ 2 * x
    · rw [ite_eq_left ⟨hgt, hn2⟩]
      have hlog : (n - x) / n ≤ Real.log (n / x) := by
        have h := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hx0)
        rw [inv_div] at h
        have e : 1 - x / (n : ℝ) = (n - x) / n := by field_simp
        linarith
      have hnx' : 0 < (n : ℝ) - x := by linarith
      have hℓ' : 0 < Real.log (n / x) := by linarith [div_pos hnx' hn0]
      have hlogn : Real.log n ≤ Real.log (2 * x) := Real.log_le_log hn0 hn2
      have h1 : β / n * E / Real.log (n / x) ≤ C₁ * Real.log (2 * x) * (1 / (n - x)) := by
        calc β / n * E / Real.log (n / x) ≤ β / n / Real.log (n / x) :=
              div_le_div_of_nonneg_right (mul_le_of_le_one_right hb hE1) hℓ'.le
          _ ≤ β / n / ((n - x) / n) := div_le_div_of_nonneg_left hb (by positivity) hlog
          _ = β * (1 / (n - x)) := by field_simp
          _ ≤ C₁ * Real.log (2 * x) * (1 / (n - x)) :=
              mul_le_mul_of_nonneg_right (hβ.trans (mul_le_mul_of_nonneg_left hlogn hC₁))
                (by positivity)
      have h2 : 0 ≤ (c + 2) * (β / n * E) := by positivity
      linarith
    · rw [ite_eq_right (fun h ↦ hn2 h.2), zero_add]
      have hlog2 : 1 / 2 ≤ Real.log (n / x) := by
        have h2 : Real.log 2 ≤ Real.log (n / x) :=
          Real.log_le_log two_pos (by rw [le_div_iff₀ hx0]; linarith)
        have h3 := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) two_pos
        norm_num at h3
        linarith
      have hpos : 0 ≤ β / n * E := by positivity
      calc β / n * E / Real.log (n / x) ≤ β / n * E / (1 / 2) :=
            div_le_div_of_nonneg_left hpos (by norm_num) hlog2
        _ = 2 * (β / n * E) := by ring
        _ ≤ (c + 2) * (β / n * E) := by nlinarith

/-- Summing the pointwise bound: the Perron error sum is controlled by two sums near the cutoff
and by the Dirichlet series on the line `1 + c`. -/
private theorem heckeLogDerivPolynomial_perron_error_sum {x c C₁ : ℝ} (f β : ℕ → ℝ)
    (hx : 1 < x) (hc : 0 < c) (hC₁ : 0 ≤ C₁) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ : ∀ n, β n ≤ C₁ * Real.log n) (hsum : Summable fun n : ℕ ↦ β n / (n : ℝ) ^ (1 + c))
    (hf0 : ∀ n, 0 ≤ f n) (hfz : ∀ n : ℕ, n = 0 ∨ (n : ℝ) = x → f n = 0)
    (hf : ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≠ x →
      f n ≤ β n / (n : ℝ) ^ (1 + c) / |Real.log (x / n)|) :
    x ^ c * ∑' n : ℕ, f n ≤
      C₁ * Real.log x * ∑ n ∈ Finset.Ico 1 ⌈x⌉₊, (1 / (n : ℝ) + 1 / (x - n)) +
      C₁ * Real.log (2 * x) * ∑ n ∈ Finset.Ico (⌊x⌋₊ + 1) (⌊2 * x⌋₊ + 1), 1 / ((n : ℝ) - x) +
      (c + 2) * (x ^ c * ∑' n : ℕ, β n / (n : ℝ) ^ (1 + c)) := by
  have hx0 : 0 < x := by linarith
  set s₁ := Finset.Ico 1 ⌈x⌉₊
  set s₂ := Finset.Ico (⌊x⌋₊ + 1) (⌊2 * x⌋₊ + 1)
  let U : ℕ → ℝ := fun n ↦ C₁ * Real.log x * (1 / (n : ℝ) + 1 / (x - n))
  let V : ℕ → ℝ := fun n ↦ C₁ * Real.log (2 * x) * (1 / ((n : ℝ) - x))
  let W : ℕ → ℝ := fun n ↦ (c + 2) * (x ^ c * (β n / (n : ℝ) ^ (1 + c)))
  have hmem₁ (n : ℕ) : n ∈ s₁ ↔ 1 ≤ n ∧ (n : ℝ) < x := by
    simp only [s₁, Finset.mem_Ico, Nat.lt_ceil]
  have hmem₂ (n : ℕ) : n ∈ s₂ ↔ x < n ∧ (n : ℝ) ≤ 2 * x := by
    simp only [s₂, Finset.mem_Ico, Nat.add_one_le_iff, Nat.lt_add_one_iff,
      Nat.floor_lt hx0.le, Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ 2 * x)]
  have hU0 (n : ℕ) (hn : n ∈ s₁) : 0 ≤ U n := by
    obtain ⟨h1, h2⟩ := (hmem₁ n).mp hn
    have : (0 : ℝ) < n := by exact_mod_cast h1
    have : 0 < x - n := by linarith
    have : 0 ≤ Real.log x := Real.log_nonneg hx.le
    positivity
  have hV0 (n : ℕ) (hn : n ∈ s₂) : 0 ≤ V n := by
    obtain ⟨h1, -⟩ := (hmem₂ n).mp hn
    have : 0 < (n : ℝ) - x := by linarith
    have : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
    positivity
  have hW0 (n : ℕ) : 0 ≤ W n := by
    have := hβ0 n
    positivity
  let g : ℕ → ℝ := fun n ↦
    ((if n ∈ s₁ then U n else 0) + (if n ∈ s₂ then V n else 0)) + W n
  have hg (n : ℕ) : x ^ c * f n ≤ g n := by
    have hI0 : 0 ≤ (if n ∈ s₁ then U n else 0) + (if n ∈ s₂ then V n else 0) := by
      refine add_nonneg ?_ ?_
      · split_ifs with h
        exacts [hU0 n h, le_rfl]
      · split_ifs with h
        exacts [hV0 n h, le_rfl]
    by_cases hz : n = 0 ∨ (n : ℝ) = x
    · rw [hfz n hz, mul_zero]
      exact add_nonneg hI0 (hW0 n)
    · push Not at hz
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hz.1
      have hk := heckeLogDerivPolynomial_perron_error_kernel hx hc hC₁ (hβ0 n) (hβ n) hn1 hz.2
      have h1 : (if (n : ℝ) < x then C₁ * Real.log x * (1 / n + 1 / (x - n)) else 0) =
          if n ∈ s₁ then U n else 0 := by
        by_cases h : (n : ℝ) < x
        · rw [ite_eq_left h, ite_eq_left ((hmem₁ n).mpr ⟨hn1, h⟩)]
        · rw [ite_eq_right h, ite_eq_right (fun hm ↦ h ((hmem₁ n).mp hm).2)]
      have h2 : (if x < n ∧ (n : ℝ) ≤ 2 * x then C₁ * Real.log (2 * x) * (1 / (n - x)) else 0) =
          if n ∈ s₂ then V n else 0 := by
        by_cases h : x < n ∧ (n : ℝ) ≤ 2 * x
        · rw [ite_eq_left h, ite_eq_left ((hmem₂ n).mpr h)]
        · rw [ite_eq_right h, ite_eq_right (fun hm ↦ h ((hmem₂ n).mp hm))]
      rw [h1, h2] at hk
      exact (mul_le_mul_of_nonneg_left (hf n hz.1 hz.2) (by positivity)).trans hk
  have hsU : HasSum (fun n ↦ if n ∈ s₁ then U n else 0) (∑ n ∈ s₁, U n) := by
    have : HasSum (fun n ↦ if n ∈ s₁ then U n else 0)
        (∑ n ∈ s₁, if n ∈ s₁ then U n else 0) :=
      hasSum_sum_of_ne_finset_zero fun n hn ↦ ite_eq_right hn
    rwa [Finset.sum_congr rfl fun n hn ↦ ite_eq_left hn] at this
  have hsV : HasSum (fun n ↦ if n ∈ s₂ then V n else 0) (∑ n ∈ s₂, V n) := by
    have : HasSum (fun n ↦ if n ∈ s₂ then V n else 0)
        (∑ n ∈ s₂, if n ∈ s₂ then V n else 0) :=
      hasSum_sum_of_ne_finset_zero fun n hn ↦ ite_eq_right hn
    rwa [Finset.sum_congr rfl fun n hn ↦ ite_eq_left hn] at this
  have hsW : HasSum W ((c + 2) * (x ^ c * ∑' n : ℕ, β n / (n : ℝ) ^ (1 + c))) :=
    (hsum.hasSum.mul_left (x ^ c)).mul_left (c + 2)
  have hsg := (hsU.add hsV).add hsW
  have hsf : Summable fun n ↦ x ^ c * f n :=
    Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (by positivity) (hf0 n)) hg hsg.summable
  rw [← tsum_mul_left]
  refine (hsf.tsum_le_tsum hg hsg.summable).trans (le_of_eq ?_)
  rw [hsg.tsum_eq, Finset.mul_sum, Finset.mul_sum]

/-- The sum of `1/n` over the positive integers `n < x`. -/
private theorem heckeLogDerivPolynomial_perron_error_inv {x : ℝ} (hx : 1 < x) :
    ∑ n ∈ Finset.Ico 1 ⌈x⌉₊, 1 / (n : ℝ) ≤ 1 + Real.log x := by
  have hM2 : 2 ≤ ⌈x⌉₊ := by
    have : (1 : ℝ) < ⌈x⌉₊ := hx.trans_le (Nat.le_ceil x)
    exact_mod_cast this
  rw [Finset.sum_Ico_eq_sum_range]
  have hre : ∑ k ∈ Finset.range (⌈x⌉₊ - 1), 1 / (((1 + k : ℕ) : ℝ)) =
      ∑ k ∈ Finset.range (⌈x⌉₊ - 1), 1 / ((k : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    push_cast
    ring_nf
  rw [hre]
  refine (heckeLogDerivPolynomial_perron_error_harmonic _).trans ?_
  have hlt : ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x := Nat.lt_ceil.mp (by omega)
  have hpos : (0 : ℝ) < ((⌈x⌉₊ - 1 : ℕ) : ℝ) := by
    have : 0 < ⌈x⌉₊ - 1 := by omega
    exact_mod_cast this
  linarith [Real.log_le_log hpos hlt.le]

/-- The real inequality behind the final constant: the near-cutoff sums are at most a multiple of
`log² x`, plus `log x / |x - round x|` when `x` is not an integer. -/
private theorem heckeLogDerivPolynomial_perron_error_bracket {x : ℝ} (hx : 1 < x) :
    Real.log x * (2 + 2 * Real.log x + 1 / (x - ((⌈x⌉₊ - 1 : ℕ) : ℝ))) +
      Real.log (2 * x) * (1 / (((⌊x⌋₊ + 1 : ℕ) : ℝ) - x) + 1 +
        Real.log ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ)) ≤
      48 * (Real.log x ^ 2 +
        if (⌊x⌋₊ : ℝ) = x then 0 else Real.log x / |x - (round x : ℝ)|) := by
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hL_def
  have hL : 0 < L := Real.log_pos hx
  set dm := x - ((⌈x⌉₊ - 1 : ℕ) : ℝ) with hdm_def
  set dp := ((⌊x⌋₊ + 1 : ℕ) : ℝ) - x with hdp_def
  have hdp : 0 < dp := by
    have := Nat.lt_floor_add_one x
    push_cast [hdp_def]
    linarith
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hdm_ge : x - ⌊x⌋₊ ≤ dm := by
    have hlt : ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x := by
      refine Nat.lt_ceil.mp ?_
      have : 1 ≤ ⌈x⌉₊ := by
        have : (0 : ℝ) < ⌈x⌉₊ := hx0.trans_le (Nat.le_ceil x)
        exact_mod_cast this
      omega
    have : ((⌈x⌉₊ - 1 : ℕ) : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor hlt.le
    linarith
  -- `log N ≤ 2 + log x` and `log (2x) ≤ 1 + log x`.
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (x := (3 : ℝ)) (by norm_num)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    linarith
  have hlogN : Real.log ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) ≤ 2 + L := by
    have hN : ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * x := by
      have := Nat.floor_le (show (0 : ℝ) ≤ 2 * x by linarith)
      push_cast
      linarith
    have h1 := Real.log_le_log (by positivity) hN
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    linarith
  have hlog2x : Real.log (2 * x) ≤ 1 + L := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    linarith
  have hlog2x0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hlogN0 : 0 ≤ Real.log ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hhalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) two_pos
    norm_num at this
    linarith
  by_cases hint : (⌊x⌋₊ : ℝ) = x
  · rw [ite_eq_left hint, add_zero]
    set m := ⌊x⌋₊ with hm_def
    have hm1 : (1 : ℝ) < m := hint ▸ hx
    have hm2 : 2 ≤ m := by
      have : 1 < m := by exact_mod_cast hm1
      omega
    have hceil : ⌈x⌉₊ = m := by rw [← hint, Nat.ceil_natCast]
    have hdm1 : dm = 1 := by
      rw [hdm_def, hceil, Nat.cast_sub (by omega : 1 ≤ m), ← hint]
      push_cast
      ring
    have hdp1 : dp = 1 := by
      rw [hdp_def, ← hint]
      push_cast
      ring
    rw [hdm1, hdp1]
    have hL2 : 1 / 2 ≤ L := by
      have : Real.log 2 ≤ L := Real.log_le_log two_pos (by rw [← hint]; exact_mod_cast hm2)
      linarith
    have h1 : Real.log (2 * x) * (1 / 1 + 1 + Real.log ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ)) ≤
        (1 + L) * (4 + L) := by
      apply mul_le_mul hlog2x (by linarith) (by positivity) (by linarith)
    nlinarith
  · rw [ite_eq_right hint]
    set δ := |x - (round x : ℝ)| with hδ_def
    have hδpos : 0 < δ := by
      rcases (abs_nonneg (x - (round x : ℝ))).lt_or_eq with h' | h'
      · exact h'
      · exfalso
        apply hint
        set r := round x with hr
        have hxr : x = (r : ℝ) := by
          have := h'.symm
          rwa [abs_eq_zero, sub_eq_zero] at this
        have hr0 : 0 ≤ r := by
          have : (0 : ℝ) ≤ (r : ℝ) := hxr ▸ hx0.le
          exact_mod_cast this
        have hxn : x = ((r.toNat : ℕ) : ℝ) := by
          rw [hxr]
          exact_mod_cast (Int.toNat_of_nonneg hr0).symm
        rw [hxn, Nat.floor_natCast]
    have hδhalf : δ ≤ 1 / 2 := abs_sub_round x
    have edp : dp = (⌊x⌋₊ : ℝ) + 1 - x := by
      rw [hdp_def]
      push_cast
      ring
    have hδdm : δ ≤ dm := by
      have h := round_le x (⌊x⌋₊ : ℤ)
      rw [Int.cast_natCast] at h
      have h2 : |x - (⌊x⌋₊ : ℝ)| = x - ⌊x⌋₊ := abs_of_nonneg (by linarith)
      exact (h.trans_eq h2).trans hdm_ge
    have hδdp : δ ≤ dp := by
      have h := round_le x ((⌊x⌋₊ : ℤ) + 1)
      push_cast at h
      have h2 : |x - ((⌊x⌋₊ : ℝ) + 1)| = (⌊x⌋₊ : ℝ) + 1 - x := by
        rw [abs_sub_comm]
        exact abs_of_pos (by rw [← edp]; exact hdp)
      exact (h.trans_eq h2).trans_eq edp.symm
    set u := 1 / δ with hu_def
    have hu : 0 < u := by positivity
    have hdmu : 1 / dm ≤ u := one_div_le_one_div_of_le hδpos hδdm
    have hdpu : 1 / dp ≤ u := one_div_le_one_div_of_le hδpos hδdp
    have hLu : L / δ = L * u := by rw [hu_def]; ring
    rw [hLu]
    rcases le_or_gt (3 / 2) x with hx32 | hx32
    · have hL3 : 1 / 3 ≤ L := by
        have h1 := Real.one_sub_inv_le_log_of_pos (x := x) hx0
        have : x⁻¹ ≤ 2 / 3 := by
          rw [inv_le_comm₀ hx0 (by norm_num)]
          linarith
        linarith
      have h1 : L * (2 + 2 * L + 1 / dm) ≤ L * (2 + 2 * L + u) :=
        mul_le_mul_of_nonneg_left (by linarith) hL.le
      have h2 : Real.log (2 * x) * (1 / dp + 1 + Real.log ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ)) ≤
          (1 + L) * (u + 3 + L) := by
        apply mul_le_mul hlog2x (by linarith) (by positivity) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hL3 hu.le]
    · have hfl1 : ⌊x⌋₊ = 1 := by
        rw [Nat.floor_eq_iff hx0.le]
        push_cast
        constructor <;> linarith
      have hdp' : dp = 2 - x := by
        rw [edp, hfl1]
        push_cast
        ring
      have hdp2 : 1 / dp ≤ 2 := by
        rw [hdp', div_le_iff₀ (by linarith)]
        linarith
      have hδx : δ ≤ x - 1 := by
        have h := round_le x 1
        rw [Int.cast_one] at h
        have h1 : |x - 1| = x - 1 := abs_of_pos (by linarith)
        exact h.trans_eq h1
      have hLx : L ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
      have hLlow : 2 / 3 * (x - 1) ≤ L := by
        have h1 := Real.one_sub_inv_le_log_of_pos (x := x) hx0
        have e : 1 - x⁻¹ = (x - 1) / x := by field_simp
        rw [e] at h1
        have : 2 / 3 * (x - 1) ≤ (x - 1) / x := by
          rw [le_div_iff₀ hx0]
          nlinarith
        linarith
      have hux : 1 / (x - 1) ≤ u := one_div_le_one_div_of_le hδpos hδx
      have hLu23 : 2 / 3 ≤ L * u := by
        calc (2 : ℝ) / 3 = 2 / 3 * (x - 1) * (1 / (x - 1)) := by field_simp
          _ ≤ L * u := mul_le_mul hLlow hux (by positivity) hL.le
      have h1 : L * (2 + 2 * L + 1 / dm) ≤ L * (3 + u) := by
        apply mul_le_mul_of_nonneg_left _ hL.le
        linarith
      have h2 : Real.log (2 * x) * (1 / dp + 1 + Real.log ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ)) ≤
          (3 / 2) * (11 / 2) := by
        apply mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
      nlinarith

/-- Collecting the bounds on the error sum: `x^c S ≤ 48 C₁ Ψ + K x^c / c`. -/
private theorem heckeLogDerivPolynomial_perron_error_collect {x c C₁ K S A : ℝ} (hx : 1 < x)
    (hC₁ : 0 < C₁)
    (hS : x ^ c * S ≤
      C₁ * Real.log x * ∑ n ∈ Finset.Ico 1 ⌈x⌉₊, (1 / (n : ℝ) + 1 / (x - n)) +
      C₁ * Real.log (2 * x) * ∑ n ∈ Finset.Ico (⌊x⌋₊ + 1) (⌊2 * x⌋₊ + 1), 1 / ((n : ℝ) - x) +
      (c + 2) * (x ^ c * A))
    (hA : (c + 2) * A ≤ K / c) :
    x ^ c * S ≤ 48 * C₁ * (Real.log x ^ 2 +
      if (⌊x⌋₊ : ℝ) = x then 0 else Real.log x / |x - (round x : ℝ)|) + K * (x ^ c / c) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hs1 := heckeLogDerivPolynomial_perron_error_left hx
  have hs1' := heckeLogDerivPolynomial_perron_error_inv hx
  have hs2 := heckeLogDerivPolynomial_perron_error_right x (⌊2 * x⌋₊ + 1)
  have hbr := heckeLogDerivPolynomial_perron_error_bracket hx
  have hlog2x0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  refine hS.trans ?_
  have h1 : C₁ * Real.log x * ∑ n ∈ Finset.Ico 1 ⌈x⌉₊, (1 / (n : ℝ) + 1 / (x - n)) ≤
      C₁ * (Real.log x * (2 + 2 * Real.log x + 1 / (x - ((⌈x⌉₊ - 1 : ℕ) : ℝ)))) := by
    rw [Finset.sum_add_distrib, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hL.le) hC₁.le
    linarith
  have h2 : C₁ * Real.log (2 * x) *
      ∑ n ∈ Finset.Ico (⌊x⌋₊ + 1) (⌊2 * x⌋₊ + 1), 1 / ((n : ℝ) - x) ≤
      C₁ * (Real.log (2 * x) * (1 / (((⌊x⌋₊ + 1 : ℕ) : ℝ) - x) + 1 +
        Real.log ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ))) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs2 hlog2x0) hC₁.le
  have h3 : (c + 2) * (x ^ c * A) ≤ K * (x ^ c / c) := by
    have hxc : 0 < x ^ c := by positivity
    calc (c + 2) * (x ^ c * A) = x ^ c * ((c + 2) * A) := by ring
      _ ≤ x ^ c * (K / c) := mul_le_mul_of_nonneg_left hA hxc.le
      _ = K * (x ^ c / c) := by ring
  have h4 := mul_le_mul_of_nonneg_left hbr hC₁.le
  have e : C₁ * (Real.log x * (2 + 2 * Real.log x + 1 / (x - ((⌈x⌉₊ - 1 : ℕ) : ℝ)))) +
      C₁ * (Real.log (2 * x) * (1 / (((⌊x⌋₊ + 1 : ℕ) : ℝ) - x) + 1 +
        Real.log ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ))) =
      C₁ * (Real.log x * (2 + 2 * Real.log x + 1 / (x - ((⌈x⌉₊ - 1 : ℕ) : ℝ))) +
      Real.log (2 * x) * (1 / (((⌊x⌋₊ + 1 : ℕ) : ℝ) - x) + 1 +
        Real.log ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ))) := by ring
  have e2 : C₁ * (48 * (Real.log x ^ 2 +
      if (⌊x⌋₊ : ℝ) = x then 0 else Real.log x / |x - (round x : ℝ)|)) =
      48 * C₁ * (Real.log x ^ 2 +
      if (⌊x⌋₊ : ℝ) = x then 0 else Real.log x / |x - (round x : ℝ)|) := by ring
  linarith

/-- The final comparison with the stated majorant, given the bound on `x^c S` and on the endpoint
term at an integer cutoff. -/
private theorem heckeLogDerivPolynomial_perron_error_final {x c T C₁ K S E₀ : ℝ} (hx : 1 < x)
    (hc : 0 < c) (hT : 1 ≤ T) (hC₁ : 0 < C₁) (hK : 0 < K) (hS0 : 0 ≤ S) (hE₀ : 0 ≤ E₀)
    (hxS : x ^ c * S ≤ 48 * C₁ * (Real.log x ^ 2 +
      if (⌊x⌋₊ : ℝ) = x then 0 else Real.log x / |x - (round x : ℝ)|) + K * (x ^ c / c))
    (hend : (⌊x⌋₊ : ℝ) = x → E₀ ≤ C₁ * Real.log x / x) :
    x ^ c / (Real.pi * T) * S + (if (⌊x⌋₊ : ℝ) = x then c * E₀ / (Real.pi * T) else 0) ≤
      (48 * C₁ + K + C₁) * (x ^ c / (T * c) + Real.log x ^ 2 / T +
        (if (⌊x⌋₊ : ℝ) = x then c * Real.log x / (T * x)
         else Real.log x / (T * |x - (round x : ℝ)|))) := by
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hL : 0 < Real.log x := Real.log_pos hx
  have hxc : 0 < x ^ c := by positivity
  have hP : 0 ≤ x ^ c / c := by positivity
  have hL2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  have hπT (y : ℝ) (hy : 0 ≤ y) : y / (Real.pi * T) ≤ y / T :=
    div_le_div_of_nonneg_left hy hT0 (by nlinarith)
  have hA : x ^ c / (Real.pi * T) * S ≤ (48 * C₁ * (Real.log x ^ 2 +
      if (⌊x⌋₊ : ℝ) = x then 0 else Real.log x / |x - (round x : ℝ)|) + K * (x ^ c / c)) / T := by
    rw [div_mul_eq_mul_div]
    exact (hπT _ (by positivity)).trans (div_le_div_of_nonneg_right hxS hT0.le)
  by_cases h : (⌊x⌋₊ : ℝ) = x
  · rw [ite_eq_left h, ite_eq_left h]
    rw [ite_eq_left h, add_zero] at hA
    have hR : 0 ≤ c * Real.log x / x := by positivity
    have hend' : c * E₀ / (Real.pi * T) ≤ C₁ * (c * Real.log x / x) / T := by
      refine (hπT _ (by positivity)).trans (div_le_div_of_nonneg_right ?_ hT0.le)
      calc c * E₀ ≤ c * (C₁ * Real.log x / x) := mul_le_mul_of_nonneg_left (hend h) hc.le
        _ = C₁ * (c * Real.log x / x) := by ring
    have hd : (48 * C₁ + K + C₁) * (x ^ c / c + Real.log x ^ 2 + c * Real.log x / x) -
        (48 * C₁ * Real.log x ^ 2 + K * (x ^ c / c) + C₁ * (c * Real.log x / x)) =
        49 * C₁ * (x ^ c / c) + 48 * C₁ * (c * Real.log x / x) + K * Real.log x ^ 2 +
          K * (c * Real.log x / x) + C₁ * Real.log x ^ 2 := by ring
    have h0 : 0 ≤ 49 * C₁ * (x ^ c / c) + 48 * C₁ * (c * Real.log x / x) +
        K * Real.log x ^ 2 + K * (c * Real.log x / x) + C₁ * Real.log x ^ 2 := by positivity
    have key : 48 * C₁ * Real.log x ^ 2 + K * (x ^ c / c) + C₁ * (c * Real.log x / x) ≤
        (48 * C₁ + K + C₁) * (x ^ c / c + Real.log x ^ 2 + c * Real.log x / x) := by linarith
    have e3 : (48 * C₁ + K + C₁) * (x ^ c / (T * c) + Real.log x ^ 2 / T +
        c * Real.log x / (T * x)) =
        (48 * C₁ + K + C₁) * (x ^ c / c + Real.log x ^ 2 + c * Real.log x / x) / T := by ring
    rw [e3]
    calc x ^ c / (Real.pi * T) * S + c * E₀ / (Real.pi * T)
        ≤ (48 * C₁ * Real.log x ^ 2 + K * (x ^ c / c)) / T + C₁ * (c * Real.log x / x) / T :=
          add_le_add hA hend'
      _ = (48 * C₁ * Real.log x ^ 2 + K * (x ^ c / c) + C₁ * (c * Real.log x / x)) / T := by
          ring
      _ ≤ _ := div_le_div_of_nonneg_right key hT0.le
  · rw [ite_eq_right h, ite_eq_right h, add_zero]
    rw [ite_eq_right h] at hA
    set δ := |x - (round x : ℝ)| with hδ
    have hδ0 : 0 ≤ δ := abs_nonneg _
    have hR : 0 ≤ Real.log x / δ := div_nonneg hL.le hδ0
    have hd : (48 * C₁ + K + C₁) * (x ^ c / c + Real.log x ^ 2 + Real.log x / δ) -
        (48 * C₁ * (Real.log x ^ 2 + Real.log x / δ) + K * (x ^ c / c)) =
        49 * C₁ * (x ^ c / c) + K * Real.log x ^ 2 + K * (Real.log x / δ) +
          C₁ * Real.log x ^ 2 + C₁ * (Real.log x / δ) := by ring
    have h0 : 0 ≤ 49 * C₁ * (x ^ c / c) + K * Real.log x ^ 2 + K * (Real.log x / δ) +
        C₁ * Real.log x ^ 2 + C₁ * (Real.log x / δ) := by positivity
    have key : 48 * C₁ * (Real.log x ^ 2 + Real.log x / δ) + K * (x ^ c / c) ≤
        (48 * C₁ + K + C₁) * (x ^ c / c + Real.log x ^ 2 + Real.log x / δ) := by linarith
    have e3 : (48 * C₁ + K + C₁) * (x ^ c / (T * c) + Real.log x ^ 2 / T +
        Real.log x / (T * δ)) =
        (48 * C₁ + K + C₁) * (x ^ c / c + Real.log x ^ 2 + Real.log x / δ) / T := by ring
    rw [e3]
    exact hA.trans (div_le_div_of_nonneg_right key hT0.le)

/-- Perron's estimate for the cutoff polynomial of any Hecke character whose coefficient
Dirichlet series sums to `G` to the right of one, given the domination of its coefficients
by the untwisted ones. -/
private theorem heckeLogDerivPolynomial_perron_error_generic (χ : U[F]) (G : ℂ → ℂ)
    (hG : ∀ w : ℂ, 1 < w.re →
      LSeriesHasSum (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) w (G w))
    (hcoef : ∀ n : ℕ, ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n‖ ≤
      ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖)
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (x c T : ℝ), s ∈ oneLine → 1 < x → 0 < c → 1 ≤ T →
      ‖heckeLogDerivPolynomial χ x s -
        truncatedPerronIntegral G s x c T -
        (if (⌊x⌋₊ : ℝ) = x then
          LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s ⌊x⌋₊ / 2
         else 0)‖ ≤
        C * (x ^ c / (T * c) + (Real.log x) ^ 2 / T +
          (if (⌊x⌋₊ : ℝ) = x then c * Real.log x / (T * x)
           else Real.log x / (T * |x - (round x : ℝ)|))) := by
  classical
  obtain ⟨C₁, hC₁, hlogb⟩ := heckeLogDerivPolynomial_perron_error_coeff_log (F := F)
  obtain ⟨K, hK, hser⟩ := heckeLogDerivPolynomial_perron_error_series Z hZ hSeries
  refine ⟨48 * C₁ + K + C₁, by positivity, fun s x c T hs hx hc hT ↦ ?_⟩
  set a := heckeLogDerivCoefficient (ideleClassNormTwist χ 0) with ha
  have hsre : s.re = 1 := hs
  have hx0 : 0 < x := by linarith
  -- The cutoff polynomial minus the half term is the half-weighted sum.
  have hpoly : heckeLogDerivPolynomial χ x s -
      (if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0) =
      perronHalfWeightedSum a s x := by
    by_cases h : (⌊x⌋₊ : ℝ) = x
    · rw [ite_eq_left h]
      set m := ⌊x⌋₊ with hm_def
      have hm : 0 < m := Nat.floor_pos.mpr hx.le
      rw [← h, perronHalfWeightedSum_nat a s hm, heckeLogDerivPolynomial, Nat.floor_natCast,
        Finset.Icc_eq_cons_Ico hm, Finset.sum_cons]
      ring
    · rw [ite_eq_right h, sub_zero, heckeLogDerivPolynomial, perronHalfWeightedSum]
      refine Finset.sum_congr rfl fun n _ ↦ (ite_eq_right fun hnx ↦ h ?_).symm
      rw [← hnx, Nat.floor_natCast]
  -- The integrand is the L-series of the coefficients on the line of integration.
  have hint : truncatedPerronIntegral G s x c T =
      truncatedPerronIntegral (LSeries a) s x c T := by
    unfold truncatedPerronIntegral
    congr 1
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    have hre : 1 < (s + ⟨c, t⟩).re := by
      change 1 < s.re + c
      linarith
    rw [(hG _ hre).LSeries_eq]
  have hsumm : LSeriesSummable a (s + (c : ℂ)) :=
    (hG _ (by simp [hsre]; linarith)).summable
  have hE : heckeLogDerivPolynomial χ x s -
      truncatedPerronIntegral G s x c T -
      (if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0) =
      perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T := by
    rw [← hpoly, hint]
    ring
  rw [hE]
  refine (truncatedPerron_error a s hx0 hc hT hsumm).trans ?_
  obtain ⟨hsumβ, hserc⟩ := hser c hc
  have hS := heckeLogDerivPolynomial_perron_error_sum (x := x) (c := c) (C₁ := C₁)
    (fun n : ℕ ↦ if n = 0 ∨ (n : ℝ) = x then 0 else
      ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|)
    (fun n ↦ ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖) hx hc hC₁.le
    (fun n ↦ norm_nonneg _) hlogb hsumβ
    (fun n ↦ by split_ifs <;> positivity) (fun n hn ↦ ite_eq_left hn)
    (fun n hn hnx ↦ by
      rw [ite_eq_right (not_or.mpr ⟨hn, hnx⟩), LSeries.norm_term_eq, ite_eq_right hn]
      have hre : (s + (c : ℂ)).re = 1 + c := by simp [hsre]
      rw [hre]
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (hcoef n) (by positivity)) (abs_nonneg _))
  have hxS := heckeLogDerivPolynomial_perron_error_collect hx hC₁ hS hserc
  refine heckeLogDerivPolynomial_perron_error_final hx hc hT hC₁ hK
    (tsum_nonneg fun n ↦ by split_ifs <;> positivity) (norm_nonneg _) hxS fun h ↦ ?_
  have hm0 : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr hx.le).ne'
  rw [LSeries.norm_term_eq, ite_eq_right hm0, hsre, Real.rpow_one, h]
  have h1 := (hcoef ⌊x⌋₊).trans (hlogb ⌊x⌋₊)
  rw [h] at h1
  exact div_le_div_of_nonneg_right h1 hx0.le

/-- Paper: Equation (B.7.1.11), p. 646. Perron's estimate for the full Hecke
cutoff includes a correction for the remaining half of the last coefficient
at an integer cutoff.
Deviation: Adds the half-endpoint correction. For `c ≥ 1` the absence of
a norm-one coefficient gives exponential decay to the right. The initial contour lies
strictly to the right of the pole, so the estimate also holds at the pole ordinate. -/
theorem heckeLogDerivPolynomial_perron_error (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (x c T : ℝ), s ∈ oneLine → 1 < x → 0 < c → 1 ≤ T →
      ‖heckeLogDerivPolynomial χ x s -
        truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T -
        (if (⌊x⌋₊ : ℝ) = x then
          LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s ⌊x⌋₊ / 2
         else 0)‖ ≤
        C * (x ^ c / (T * c) + (Real.log x) ^ 2 / T +
          (if (⌊x⌋₊ : ℝ) = x then c * Real.log x / (T * x)
           else Real.log x / (T * |x - (round x : ℝ)|))) :=
  heckeLogDerivPolynomial_perron_error_generic χ _
    (fun w hw ↦ heckeLogDerivPolynomial_perron_error_hasSum χ t₀ hχ Z hZ hSeries w hw)
    (heckeLogDerivPolynomial_perron_error_coeff_le χ t₀ hχ) Z hZ hSeries

/-- On the half-plane of absolute convergence the finite L-function of the trivial
character is the Dedekind zeta function. -/
private theorem dedekindZeta_perron_left_bound_zeta {F : Type*} [Field F] [NumberField F]
    (s : halfPlane) : finiteHeckeL (1 : U[F]) s = dedekindZeta F s := by
  have h := completedHeckeL_one_eq_dedekindZeta (F := F) s
  rw [← heckeGammaFactor_one] at h
  change heckeGammaFactor (1 : U[F]) s * finiteHeckeL (1 : U[F]) s = _ at h
  have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
  exact mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) hs) h

/-- The logarithmic width `A / log (B (t + 3))` is an admissible width for the
logarithmic-derivative estimate: positive and at most `1/2`, differentiable,
nonincreasing, with derivative tending to zero and reciprocal `O(log t)`. -/
private theorem dedekindZeta_perron_left_bound_width (A B : ℝ) (hA : 0 < A)
    (hB : 1 / 3 < B) (hwidth : A ≤ Real.log (B * 3) / 2) :
    MapsTo (fun t : ℝ ↦ A / Real.log (B * (t + 3))) (Ici 0) (Ioc 0 (1 / 2)) ∧
      DifferentiableOn ℝ (fun t : ℝ ↦ A / Real.log (B * (t + 3))) (Ici 0) ∧
      AntitoneOn (fun t : ℝ ↦ A / Real.log (B * (t + 3))) (Ici 0) ∧
      Tendsto (derivWithin (fun t : ℝ ↦ A / Real.log (B * (t + 3))) (Ici 0)) atTop (𝓝 0) ∧
      ((fun t : ℝ ↦ (A / Real.log (B * (t + 3)))⁻¹) =O[atTop] Real.log) := by
  have hB0 : 0 < B := by linarith
  have hl3 : 0 < Real.log (B * 3) := by linarith
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < B * (t + 3) := fun t ht ↦ by positivity
  have hmono : ∀ t : ℝ, 0 ≤ t → Real.log (B * 3) ≤ Real.log (B * (t + 3)) := fun t ht ↦
    Real.log_le_log (by positivity) (by nlinarith)
  have hg0 : ∀ t : ℝ, 0 ≤ t → 0 < Real.log (B * (t + 3)) := fun t ht ↦
    hl3.trans_le (hmono t ht)
  have hgd : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun t : ℝ ↦ Real.log (B * (t + 3))) (B / (B * (t + 3))) t := fun t ht ↦ by
    have h1 : HasDerivAt (fun t : ℝ ↦ B * (t + 3)) (B * 1) t :=
      ((hasDerivAt_id t).add_const 3).const_mul B
    rw [mul_one] at h1
    exact h1.log (hpos t ht).ne'
  have hηd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ ↦ A / Real.log (B * (t + 3)))
      (A * (-(B / (B * (t + 3))) / Real.log (B * (t + 3)) ^ 2)) t := fun t ht ↦ by
    have := ((hgd t ht).inv (hg0 t ht).ne').const_mul A
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)
    simp [div_eq_mul_inv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have ht : 0 ≤ t := ht
    refine ⟨div_pos hA (hg0 t ht), ?_⟩
    rw [div_le_iff₀ (hg0 t ht)]
    linarith [hmono t ht]
  · exact fun t ht ↦ (hηd t ht).differentiableAt.differentiableWithinAt
  · intro a ha b hb hab
    have ha : 0 ≤ a := ha
    exact div_le_div_of_nonneg_left hA.le (hg0 a ha)
      (Real.log_le_log (hpos a ha) (by nlinarith))
  · have hbound : ∀ᶠ t : ℝ in atTop,
        ‖derivWithin (fun t : ℝ ↦ A / Real.log (B * (t + 3))) (Ici 0) t‖ ≤
          A / Real.log (B * 3) ^ 2 / (t + 3) := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht), (hηd t ht.le).deriv]
      have hBt : B / (B * (t + 3)) = 1 / (t + 3) := by field_simp
      have ht3 : 0 < t + 3 := by linarith
      have hgt := hg0 t ht.le
      have hsq : Real.log (B * 3) ^ 2 ≤ Real.log (B * (t + 3)) ^ 2 :=
        pow_le_pow_left₀ hl3.le (hmono t ht.le) 2
      have hval : A * (-(1 / (t + 3)) / Real.log (B * (t + 3)) ^ 2) =
          -(A / Real.log (B * (t + 3)) ^ 2 / (t + 3)) := by ring
      rw [hBt, hval, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left hA.le (pow_pos hl3 2) hsq) ht3.le
    exact squeeze_zero_norm' hbound
      (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id))
  · apply Asymptotics.IsBigO.of_bound (2 / A)
    filter_upwards [eventually_ge_atTop (max 3 (B + 3))] with t ht
    have ht3 : 3 ≤ t := (le_max_left _ _).trans ht
    have htB : B + 3 ≤ t := (le_max_right _ _).trans ht
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hgt0 := hg0 t (by linarith)
    rw [inv_div, Real.norm_of_nonneg (div_pos hgt0 hA).le, Real.norm_of_nonneg hlogt.le,
      div_le_iff₀ hA]
    have hlog : Real.log (B * (t + 3)) ≤ 2 * Real.log t := by
      rw [show (2 : ℝ) * Real.log t = Real.log (t ^ 2) by rw [Real.log_pow]; norm_num]
      apply Real.log_le_log (by positivity)
      nlinarith
    have hA' : 2 / A * Real.log t * A = 2 * Real.log t := by field_simp
    linarith

/-- In the narrowed logarithmic zero-free region the logarithmic derivative of the
Dedekind zeta continuation is bounded by a squared logarithm at large heights. -/
private theorem dedekindZeta_perron_left_bound_logDeriv {F : Type*} [Field F]
    [NumberField F] (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    {A B α : ℝ} (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1)
    (hwidth : A ≤ Real.log (B * 3) / 2)
    (hdisc : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0)
    (hzero : ∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re →
      meromorphicOrderAt Z z ≤ 0) :
    ∃ C T₁ : ℝ, 0 < C ∧ ∀ z : ℂ, T₁ ≤ |z.im| →
      1 - α * (A / Real.log (B * (|z.im| + 3))) ≤ z.re →
      ‖logDeriv Z z‖ ≤ C * (Real.log |z.im|) ^ 2 := by
  have hS1 : ∀ s : halfPlane, Z s = finiteHeckeL (1 : U[F]) s := fun s ↦
    (hSeries s).trans (dedekindZeta_perron_left_bound_zeta s).symm
  obtain ⟨C, hC, hmain⟩ := finiteHeckeL_logDeriv_isBigO_of_zeroFree (1 : U[F]) Z Z hZ hS1
    hZ hSeries α hα.1 hα.2 hdisc
  obtain ⟨hmaps, hdiff, hanti, hderiv, hO⟩ :=
    dedekindZeta_perron_left_bound_width A B hA hB hwidth
  obtain ⟨-, hbig⟩ := hmain (fun t : ℝ ↦ A / Real.log (B * (t + 3))) hmaps hdiff hanti hderiv
    hO hzero
  rw [Asymptotics.isBigOWith_iff, eventually_inf_principal, eventually_comap,
    eventually_atTop] at hbig
  obtain ⟨T₁, hT₁⟩ := hbig
  refine ⟨C, T₁, hC, fun z hz hre ↦ ?_⟩
  have h := hT₁ |z.im| hz z rfl hre
  rwa [Real.norm_of_nonneg (sq_nonneg _)] at h

/-- Near a point where it is in normal form, the logarithmic derivative of a meromorphic
function is at most a constant times the inverse distance to that point. -/
private theorem dedekindZeta_perron_left_bound_local (Z : ℂ → ℂ) (p : ℂ)
    (hZ : MeromorphicNFAt Z p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z in 𝓝 p, z ≠ p → ‖logDeriv Z z‖ ≤ M / ‖z - p‖ := by
  rcases hZ with h0 | ⟨n, g, hg, hgp, hfg⟩
  · refine ⟨0, le_rfl, ?_⟩
    filter_upwards [logDeriv_congr_nhds h0] with z hz _
    rw [hz]
    simp [logDeriv_apply]
  · have hcont : ContinuousAt (fun z ↦ ‖logDeriv g z‖) p :=
      (hg.deriv.continuousAt.div hg.continuousAt hgp).norm
    have hbd : ∀ᶠ z in 𝓝 p, ‖logDeriv g z‖ < ‖logDeriv g p‖ + 1 :=
      hcont.eventually (gt_mem_nhds (lt_add_one _))
    refine ⟨|(n : ℝ)| + (‖logDeriv g p‖ + 1), by positivity, ?_⟩
    filter_upwards [logDeriv_congr_nhds hfg, hg.eventually_analyticAt,
      hg.continuousAt.eventually_ne hgp, hbd, Metric.ball_mem_nhds p one_pos]
      with z hz hga hgz hb hball hzp
    have hsub : z - p ≠ 0 := sub_ne_zero.mpr hzp
    have hd : DifferentiableAt ℂ (fun w : ℂ ↦ w - p) z := by fun_prop
    have h1 : logDeriv ((· - p) ^ n • g) z = n / (z - p) + logDeriv g z := by
      have hfun : ((· - p) ^ n • g : ℂ → ℂ) = (fun w : ℂ ↦ (w - p) ^ n) * g := by
        ext w
        simp
      rw [hfun, logDeriv_mul (f := fun w : ℂ ↦ (w - p) ^ n) (g := g) z (zpow_ne_zero n hsub)
        hgz (hd.zpow (Or.inl hsub)) hga.differentiableAt, logDeriv_fun_zpow hd n]
      congr 1
      simp [logDeriv_apply, div_eq_mul_inv]
    rw [hz, h1]
    have hdist : ‖z - p‖ < 1 := by simpa [dist_eq_norm] using hball
    have hpos : 0 < ‖z - p‖ := norm_pos_iff.mpr hsub
    have hn : ‖(n : ℂ) / (z - p)‖ = |(n : ℝ)| / ‖z - p‖ := by
      rw [norm_div, Complex.norm_intCast]
    have hg1 : ‖logDeriv g z‖ ≤ (‖logDeriv g p‖ + 1) / ‖z - p‖ := by
      rw [le_div_iff₀ hpos]
      nlinarith [norm_nonneg (logDeriv g z), norm_nonneg (logDeriv g p)]
    calc ‖(n : ℂ) / (z - p) + logDeriv g z‖
        ≤ ‖(n : ℂ) / (z - p)‖ + ‖logDeriv g z‖ := norm_add_le _ _
      _ ≤ |(n : ℝ)| / ‖z - p‖ + (‖logDeriv g p‖ + 1) / ‖z - p‖ := by
          rw [hn]
          linarith
      _ = (|(n : ℝ)| + (‖logDeriv g p‖ + 1)) / ‖z - p‖ := by ring

/-- Close to a segment of the line `Re z = 1` and to its left, the logarithmic derivative
of a meromorphic function in normal form is at most a constant times `1 / (1 - Re z)`. -/
private theorem dedekindZeta_perron_left_bound_tube (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (T₁ : ℝ) :
    ∃ M δ₀ : ℝ, 0 ≤ M ∧ 0 < δ₀ ∧ ∀ z : ℂ, 1 - δ₀ < z.re → z.re < 1 → |z.im| ≤ T₁ →
      ‖logDeriv Z z‖ ≤ M / (1 - z.re) := by
  have hcont : Continuous fun t : ℝ ↦ (⟨1, t⟩ : ℂ) := by
    rw [show (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) = fun t : ℝ ↦ ((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I from
      funext fun t ↦ Complex.mk_eq_add_mul_I 1 t]
    fun_prop
  have hK : IsCompact ((fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) '' Icc (-T₁) T₁) := isCompact_Icc.image hcont
  have hP : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z in 𝓝ˢ ((fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) '' Icc (-T₁) T₁),
      z.re < 1 → ‖logDeriv Z z‖ ≤ M / (1 - z.re) := by
    refine hK.induction_on (p := fun S ↦ ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z in 𝓝ˢ S,
      z.re < 1 → ‖logDeriv Z z‖ ≤ M / (1 - z.re)) ?_ ?_ ?_ ?_
    · exact ⟨0, le_rfl, by simp⟩
    · rintro S S' hSS' ⟨M, hM, h⟩
      exact ⟨M, hM, h.filter_mono (nhdsSet_mono hSS')⟩
    · rintro S S' ⟨M, hM, h⟩ ⟨M', hM', h'⟩
      refine ⟨max M M', hM.trans (le_max_left _ _), ?_⟩
      rw [nhdsSet_union, eventually_sup]
      constructor
      · filter_upwards [h] with z hz hre
        exact (hz hre).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith))
      · filter_upwards [h'] with z hz hre
        exact (hz hre).trans (div_le_div_of_nonneg_right (le_max_right _ _) (by linarith))
    · rintro p ⟨t, -, rfl⟩
      obtain ⟨M, hM, h⟩ := dedekindZeta_perron_left_bound_local Z ⟨1, t⟩ (hZ (mem_univ _))
      obtain ⟨U, hUsub, hUopen, hpU⟩ := eventually_nhds_iff.mp h
      refine ⟨_ ∩ U, inter_mem_nhdsWithin _ (hUopen.mem_nhds hpU), M, hM, ?_⟩
      have hU : U ∈ 𝓝ˢ (((fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) '' Icc (-T₁) T₁) ∩ U) :=
        hUopen.mem_nhdsSet.mpr inter_subset_right
      filter_upwards [hU] with z hz hre
      have hne : z ≠ ⟨1, t⟩ := fun h ↦ by
        rw [h] at hre
        exact lt_irrefl _ hre
      have hle : 1 - z.re ≤ ‖z - ⟨1, t⟩‖ := by
        have h1 := Complex.abs_re_le_norm (z - ⟨1, t⟩)
        rw [Complex.sub_re] at h1
        have h2 := neg_abs_le (z.re - 1)
        change -|z.re - 1| ≤ z.re - 1 at h2
        change |z.re - 1| ≤ _ at h1
        linarith
      exact (hUsub z hz hne).trans (div_le_div_of_nonneg_left hM (by linarith) hle)
  obtain ⟨M, hM, h⟩ := hP
  obtain ⟨U, hUopen, hKU, hUsub⟩ := mem_nhdsSet_iff_exists.mp h
  obtain ⟨δ₀, hδ₀, hthick⟩ := hK.exists_thickening_subset_open hUopen hKU
  refine ⟨M, δ₀, hM, hδ₀, fun z h1 h2 h3 ↦ ?_⟩
  refine hUsub (hthick ?_) h2
  rw [Metric.mem_thickening_iff]
  refine ⟨⟨1, z.im⟩, ⟨z.im, abs_le.mp h3, rfl⟩, ?_⟩
  rw [Complex.dist_of_im_eq (z := z) (w := ⟨1, z.im⟩) rfl, Real.dist_eq]
  change |z.re - 1| < δ₀
  rw [abs_of_neg (by linarith)]
  linarith

/-- The integral of `1 / √(δ² + y²)` over a symmetric interval is at most a logarithm. -/
private theorem dedekindZeta_perron_left_bound_integral {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) :
    Continuous (fun y : ℝ ↦ 1 / √(δ ^ 2 + y ^ 2)) ∧
      ∫ y in -T..T, 1 / √(δ ^ 2 + y ^ 2) ≤ 2 * Real.log ((2 * T + δ) / δ) := by
  have hcont : Continuous fun y : ℝ ↦ 1 / √(δ ^ 2 + y ^ 2) := by
    refine continuous_const.div
      (Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2))) fun y ↦ ?_
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  refine ⟨hcont, ?_⟩
  have hG : ∀ y ∈ uIcc (-T) T, HasDerivAt (fun y : ℝ ↦ Real.log (y + √(δ ^ 2 + y ^ 2)))
      (1 / √(δ ^ 2 + y ^ 2)) y := by
    intro y _
    have hpos : 0 < δ ^ 2 + y ^ 2 := by positivity
    have hr : 0 < √(δ ^ 2 + y ^ 2) := Real.sqrt_pos.mpr hpos
    have habsy : |y| < √(δ ^ 2 + y ^ 2) := by
      rw [Real.lt_sqrt (abs_nonneg y), sq_abs]
      linarith [pow_pos hδ 2]
    have hyr : 0 < y + √(δ ^ 2 + y ^ 2) := by linarith [neg_abs_le y]
    have h1 : HasDerivAt (fun y : ℝ ↦ δ ^ 2 + y ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).const_add (δ ^ 2)
    have hs : HasDerivAt (fun y : ℝ ↦ √(δ ^ 2 + y ^ 2)) (y / √(δ ^ 2 + y ^ 2)) y := by
      have h := h1.rpow_const (p := 1 / 2) (Or.inl hpos.ne')
      have hfun : (fun y : ℝ ↦ √(δ ^ 2 + y ^ 2)) =
          fun y : ℝ ↦ (δ ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := funext fun y ↦ Real.sqrt_eq_rpow _
      rw [hfun]
      refine h.congr_deriv ?_
      rw [Real.sqrt_eq_rpow, Real.rpow_sub hpos, Real.rpow_one]
      obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (δ ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
      have hrpos : 0 < r := hrdef ▸ Real.rpow_pos_of_pos hpos _
      have hX : δ ^ 2 + y ^ 2 = r * r := by
        rw [hrdef, ← Real.rpow_add hpos]
        norm_num
      rw [← hrdef, hX]
      field_simp
    have h2 : HasDerivAt (fun y : ℝ ↦ Real.log (y + √(δ ^ 2 + y ^ 2)))
        ((1 + y / √(δ ^ 2 + y ^ 2)) / (y + √(δ ^ 2 + y ^ 2))) y :=
      ((hasDerivAt_id' y).add hs).log hyr.ne'
    refine h2.congr_deriv ?_
    have hr' := hr.ne'
    have hyr' := hyr.ne'
    rw [div_eq_div_iff hyr' hr']
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG (hcont.intervalIntegrable _ _), neg_sq]
  have hr : √(δ ^ 2 + T ^ 2) ≤ T + δ :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hrT : T < √(δ ^ 2 + T ^ 2) :=
    (Real.lt_sqrt hT.le).mpr (by linarith [pow_pos hδ 2])
  have hsq : √(δ ^ 2 + T ^ 2) ^ 2 = δ ^ 2 + T ^ 2 := Real.sq_sqrt (by positivity)
  have hlow : δ ^ 2 / (2 * T + δ) ≤ -T + √(δ ^ 2 + T ^ 2) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left
      (show √(δ ^ 2 + T ^ 2) + T ≤ 2 * T + δ by linarith)
      (show 0 ≤ √(δ ^ 2 + T ^ 2) - T by linarith)]
  have h1 : Real.log (T + √(δ ^ 2 + T ^ 2)) ≤ Real.log (2 * T + δ) :=
    Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log (δ ^ 2 / (2 * T + δ)) ≤ Real.log (-T + √(δ ^ 2 + T ^ 2)) :=
    Real.log_le_log (div_pos (pow_pos hδ 2) (by linarith)) hlow
  rw [Real.log_div (pow_pos hδ 2).ne' (by linarith), Real.log_pow] at h2
  rw [Real.log_div (by linarith) hδ.ne']
  push_cast at h2
  linarith

/-- The scalar inequality behind the cubed logarithm: a bound of size
`M / δ + C₁ (log h)²` times the logarithmic length of the edge. -/
private theorem dedekindZeta_perron_left_bound_scalar {M C₁ K₁ δ T h : ℝ} (hM : 0 ≤ M)
    (hC₁ : 0 < C₁) (hK₁ : 0 < K₁) (hδ : 0 < δ) (hT : 0 < T) (hTh : T ≤ h)
    (hL1 : 1 ≤ Real.log h) (hinvδ : 1 / δ ≤ K₁ * Real.log h) :
    (M / δ + C₁ * (Real.log h) ^ 2) * (2 * Real.log ((2 * T + δ) / δ)) ≤
      2 * (Real.log (2 * K₁ + 1) + 2) * (M * K₁ + C₁) * (Real.log h) ^ 3 := by
  have hh0 : 0 < h := hT.trans_le hTh
  have hLh : Real.log h ≤ h := (Real.log_le_sub_one_of_pos hh0).trans (by linarith)
  have h1h : 1 ≤ h := hL1.trans hLh
  have hlogK : 0 ≤ Real.log (2 * K₁ + 1) := Real.log_nonneg (by linarith)
  have hratio : (2 * T + δ) / δ ≤ (2 * K₁ + 1) * h ^ 2 := by
    have h1 : (2 * T + δ) / δ = 2 * T * (1 / δ) + 1 := by
      field_simp
    have h2 : 2 * T * (1 / δ) ≤ 2 * h * (K₁ * h) :=
      mul_le_mul (by linarith) (hinvδ.trans (mul_le_mul_of_nonneg_left hLh hK₁.le))
        (by positivity) (by linarith)
    rw [h1]
    nlinarith [mul_le_mul h1h h1h zero_le_one hh0.le]
  have hlogratio : Real.log ((2 * T + δ) / δ) ≤
      (Real.log (2 * K₁ + 1) + 2) * Real.log h := by
    have h1 : Real.log ((2 * T + δ) / δ) ≤ Real.log ((2 * K₁ + 1) * h ^ 2) :=
      Real.log_le_log (div_pos (by linarith) hδ) hratio
    rw [Real.log_mul (by linarith) (pow_pos hh0 2).ne', Real.log_pow] at h1
    push_cast at h1
    nlinarith [mul_nonneg hlogK (sub_nonneg.mpr hL1)]
  have hbL : M / δ + C₁ * (Real.log h) ^ 2 ≤ (M * K₁ + C₁) * (Real.log h) ^ 2 := by
    have h1 : M / δ ≤ M * (K₁ * Real.log h) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinvδ hM
    have h2 : Real.log h ≤ (Real.log h) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hM hK₁.le)]
  have hb0 : 0 ≤ M / δ + C₁ * (Real.log h) ^ 2 :=
    add_nonneg (div_nonneg hM hδ.le) (mul_nonneg hC₁.le (sq_nonneg _))
  have hK2L : 0 ≤ 2 * ((Real.log (2 * K₁ + 1) + 2) * Real.log h) :=
    mul_nonneg zero_le_two (mul_nonneg (by linarith) (by linarith))
  calc (M / δ + C₁ * (Real.log h) ^ 2) * (2 * Real.log ((2 * T + δ) / δ))
      ≤ (M / δ + C₁ * (Real.log h) ^ 2) *
        (2 * ((Real.log (2 * K₁ + 1) + 2) * Real.log h)) :=
        mul_le_mul_of_nonneg_left (by linarith) hb0
    _ ≤ (M * K₁ + C₁) * (Real.log h) ^ 2 *
        (2 * ((Real.log (2 * K₁ + 1) + 2) * Real.log h)) :=
        mul_le_mul_of_nonneg_right hbL hK2L
    _ = 2 * (Real.log (2 * K₁ + 1) + 2) * (M * K₁ + C₁) * (Real.log h) ^ 3 := by ring

-- TODO(paper-gap): The proof of (B.7.1.12) bounds the raw logarithmic derivative
-- on a region containing its pole. Subtract the principal part before using
-- compactness, and use the maximum absolute shifted height on the rectangle.

/-- The estimate (B.7.1.12) for any function in normal form whose logarithmic
derivative obeys the squared-logarithm bound in the narrowed zero-free region. -/
private theorem dedekindZeta_perron_left_bound_generic (Z : ℂ → ℂ)
    (hZ : MeromorphicNFOn Z univ)
    {A B α C₁ T₁ : ℝ} (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1)
    (hC₁ : 0 < C₁)
    (hbound : ∀ z : ℂ, T₁ ≤ |z.im| →
      1 - α * (A / Real.log (B * (|z.im| + 3))) ≤ z.re →
      ‖logDeriv Z z‖ ≤ C₁ * (Real.log |z.im|) ^ 2) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ (s : ℂ) (t₀ x T : ℝ),
      s ∈ oneLine → 1 ≤ x → T₀ + |s.im - t₀| ≤ T →
      let height := T + |s.im - t₀| + 3
      let δ := α * A / Real.log (B * height)
      ‖∫ y in -T..T, logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩) *
        (x : ℂ) ^ (⟨-δ, y⟩ : ℂ) / (⟨-δ, y⟩ : ℂ)‖ ≤
        C * x ^ (-δ) * (Real.log height) ^ 3 := by
  obtain ⟨M, δ₀, hM, hδ₀, htube⟩ := dedekindZeta_perron_left_bound_tube Z hZ (max T₁ 1)
  have hB0 : 0 < B := by linarith
  have hαA : 0 < α * A := mul_pos hα.1 hA
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = (|Real.log B| + 1) / (α * A) := ⟨_, rfl⟩
  have hK₁pos : 0 < K₁ := by
    rw [hK₁]
    exact div_pos (by linarith [abs_nonneg (Real.log B)]) hαA
  have hlogK : 0 ≤ Real.log (2 * K₁ + 1) := Real.log_nonneg (by linarith)
  have hMK : 0 < M * K₁ + C₁ := by linarith [mul_nonneg hM hK₁pos.le]
  refine ⟨2 * (Real.log (2 * K₁ + 1) + 2) * (M * K₁ + C₁),
    max 2 (max (Real.exp 1) (Real.exp (α * A / δ₀) / B)),
    mul_pos (mul_pos two_pos (by linarith)) hMK, le_max_left _ _, ?_⟩
  intro s t₀ x T hs hx hT height δ
  have hh : height = T + |s.im - t₀| + 3 := rfl
  have hδ : δ = α * A / Real.log (B * height) := rfl
  clear_value δ height
  have hs1 : s.re = 1 := hs
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hD : 0 ≤ |s.im - t₀| := abs_nonneg _
  have hT2 : 2 ≤ T := by
    linarith [le_max_left 2 (max (Real.exp 1) (Real.exp (α * A / δ₀) / B))]
  have hTe : Real.exp 1 ≤ T := by
    linarith [le_max_right 2 (max (Real.exp 1) (Real.exp (α * A / δ₀) / B)),
      le_max_left (Real.exp 1) (Real.exp (α * A / δ₀) / B)]
  have hTB : Real.exp (α * A / δ₀) / B ≤ T := by
    linarith [le_max_right 2 (max (Real.exp 1) (Real.exp (α * A / δ₀) / B)),
      le_max_right (Real.exp 1) (Real.exp (α * A / δ₀) / B)]
  have hT0 : 0 < T := by linarith
  have hh0 : 0 < height := by linarith
  have hL1 : 1 ≤ Real.log height := by
    rw [Real.le_log_iff_exp_le hh0]
    linarith
  have hl3 : 0 < Real.log (B * 3) := Real.log_pos (by linarith)
  have hlogBh : Real.log (B * 3) ≤ Real.log (B * height) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hB0.le)
  have hlogBh0 : 0 < Real.log (B * height) := by linarith
  have hδpos : 0 < δ := hδ ▸ div_pos hαA hlogBh0
  have hδlt : δ < δ₀ := by
    have h0 : B * height = T * B + B * (|s.im - t₀| + 3) := by
      rw [hh]
      ring
    have h1 : Real.exp (α * A / δ₀) < B * height := by
      have h2 := (div_le_iff₀ hB0).mp hTB
      have h3 : 0 < B * (|s.im - t₀| + 3) := mul_pos hB0 (by linarith)
      linarith
    have h2 : α * A / δ₀ < Real.log (B * height) :=
      (Real.lt_log_iff_exp_lt (mul_pos hB0 hh0)).mpr h1
    rw [div_lt_iff₀ hδ₀] at h2
    rw [hδ, div_lt_iff₀ hlogBh0]
    linarith
  have hinvδ : 1 / δ ≤ K₁ * Real.log height := by
    have h1 : 1 / δ = Real.log (B * height) / (α * A) := by
      rw [hδ, one_div_div]
    have h2 : Real.log (B * height) ≤ (|Real.log B| + 1) * Real.log height := by
      rw [Real.log_mul hB0.ne' hh0.ne']
      nlinarith [le_abs_self (Real.log B), mul_nonneg (abs_nonneg (Real.log B))
        (sub_nonneg.mpr hL1)]
    rw [h1, hK₁, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right h2 hαA.le
  have hxδ : 0 ≤ x ^ (-δ) := (Real.rpow_pos_of_pos hx0 _).le
  have hpt : ∀ y : ℝ, y ∈ Ioc (-T) T →
      ‖logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩) * (x : ℂ) ^ (⟨-δ, y⟩ : ℂ) /
        (⟨-δ, y⟩ : ℂ)‖ ≤
        (M / δ + C₁ * (Real.log height) ^ 2) * x ^ (-δ) * (1 / √(δ ^ 2 + y ^ 2)) := by
    intro y hy
    have hre : (s - Complex.I * t₀ + ⟨-δ, y⟩ : ℂ).re = 1 - δ := by
      simp [hs1, sub_eq_add_neg]
    have him : (s - Complex.I * t₀ + ⟨-δ, y⟩ : ℂ).im = s.im - t₀ + y := by
      simp
    have habs : |s.im - t₀ + y| ≤ T + |s.im - t₀| := by
      have h1 := abs_add_le (s.im - t₀) y
      have h2 : |y| ≤ T := abs_le.mpr ⟨hy.1.le, hy.2⟩
      linarith
    have hb : ‖logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩)‖ ≤
        M / δ + C₁ * (Real.log height) ^ 2 := by
      have hMδ : 0 ≤ M / δ := div_nonneg hM hδpos.le
      have hCL : 0 ≤ C₁ * (Real.log height) ^ 2 := mul_nonneg hC₁.le (sq_nonneg _)
      rcases le_or_gt (max T₁ 1) |s.im - t₀ + y| with hbig | hsmall
      · have h1 : (1 : ℝ) ≤ |s.im - t₀ + y| := (le_max_right _ _).trans hbig
        have hlogle : Real.log (B * (|s.im - t₀ + y| + 3)) ≤ Real.log (B * height) :=
          Real.log_le_log (by positivity)
            (mul_le_mul_of_nonneg_left (by linarith) hB0.le)
        have hlogpos : 0 < Real.log (B * (|s.im - t₀ + y| + 3)) :=
          hl3.trans_le (Real.log_le_log (by positivity)
            (mul_le_mul_of_nonneg_left (by linarith) hB0.le))
        have hδle : δ ≤ α * (A / Real.log (B * (|s.im - t₀ + y| + 3))) := by
          rw [hδ, ← mul_div_assoc]
          exact div_le_div_of_nonneg_left hαA.le hlogpos hlogle
        have h := hbound (s - Complex.I * t₀ + ⟨-δ, y⟩)
          (by rw [him]; exact (le_max_left _ _).trans hbig) (by rw [hre, him]; linarith)
        rw [him] at h
        have hℓ0 : 0 ≤ Real.log |s.im - t₀ + y| := Real.log_nonneg h1
        have hℓle : Real.log |s.im - t₀ + y| ≤ Real.log height :=
          Real.log_le_log (by linarith) (by linarith)
        have hsq : (Real.log |s.im - t₀ + y|) ^ 2 ≤ (Real.log height) ^ 2 :=
          pow_le_pow_left₀ hℓ0 hℓle 2
        calc ‖logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩)‖
            ≤ C₁ * (Real.log |s.im - t₀ + y|) ^ 2 := h
          _ ≤ C₁ * (Real.log height) ^ 2 := mul_le_mul_of_nonneg_left hsq hC₁.le
          _ ≤ M / δ + C₁ * (Real.log height) ^ 2 := le_add_of_nonneg_left hMδ
      · have h := htube (s - Complex.I * t₀ + ⟨-δ, y⟩) (by rw [hre]; linarith)
          (by rw [hre]; linarith) (by rw [him]; exact hsmall.le)
        rw [hre, sub_sub_cancel] at h
        exact h.trans (le_add_of_nonneg_right hCL)
    have hn : ‖(⟨-δ, y⟩ : ℂ)‖ = √(δ ^ 2 + y ^ 2) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
      change √((-δ) ^ 2 + y ^ 2) = _
      rw [neg_sq]
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      show (⟨-δ, y⟩ : ℂ).re = -δ from rfl, hn, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hxδ)
      (one_div_nonneg.mpr (Real.sqrt_nonneg _))
  obtain ⟨hcont, hI⟩ := dedekindZeta_perron_left_bound_integral hδpos hT0
  have hb0 : 0 ≤ (M / δ + C₁ * (Real.log height) ^ 2) * x ^ (-δ) :=
    mul_nonneg (add_nonneg (div_nonneg hM hδpos.le) (mul_nonneg hC₁.le (sq_nonneg _))) hxδ
  have hle : ‖∫ y in -T..T, logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩) *
      (x : ℂ) ^ (⟨-δ, y⟩ : ℂ) / (⟨-δ, y⟩ : ℂ)‖ ≤
      ∫ y in -T..T,
        (M / δ + C₁ * (Real.log height) ^ 2) * x ^ (-δ) * (1 / √(δ ^ 2 + y ^ 2)) :=
    intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
      (Eventually.of_forall hpt) ((continuous_const.mul hcont).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul] at hle
  have hscalar := dedekindZeta_perron_left_bound_scalar hM hC₁ hK₁pos hδpos hT0
    (show T ≤ height by linarith) hL1 hinvδ
  calc ‖∫ y in -T..T, logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩) *
        (x : ℂ) ^ (⟨-δ, y⟩ : ℂ) / (⟨-δ, y⟩ : ℂ)‖
      ≤ (M / δ + C₁ * (Real.log height) ^ 2) * x ^ (-δ) *
        ∫ y in -T..T, 1 / √(δ ^ 2 + y ^ 2) := hle
    _ ≤ (M / δ + C₁ * (Real.log height) ^ 2) * x ^ (-δ) *
        (2 * Real.log ((2 * T + δ) / δ)) := mul_le_mul_of_nonneg_left hI hb0
    _ = (M / δ + C₁ * (Real.log height) ^ 2) * (2 * Real.log ((2 * T + δ) / δ)) *
        x ^ (-δ) := by ring
    _ ≤ 2 * (Real.log (2 * K₁ + 1) + 2) * (M * K₁ + C₁) * (Real.log height) ^ 3 *
        x ^ (-δ) := mul_le_mul_of_nonneg_right hscalar hxδ
    _ = 2 * (Real.log (2 * K₁ + 1) + 2) * (M * K₁ + C₁) * x ^ (-δ) *
        (Real.log height) ^ 3 := by ring

/-- Paper: Equation (B.7.1.12), p. 647. The integral along the left edge is
bounded by the cutoff to the power `-δ` times a cubed logarithm.
Deviation: The width `δ` uses the maximum absolute shifted height. The
estimate allows the unregularized logarithmic derivative to contribute a
term of order `1 / δ` near its pole. The punctured disc is the hypothesis
on `α` in Theorem B.6.1.3. Both constants may depend on the chosen width. -/
theorem dedekindZeta_perron_left_bound (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    {A B α : ℝ} (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1)
    (hwidth : A ≤ Real.log (B * 3) / 2)
    (hdisc : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0)
    (hzero : ∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re →
      meromorphicOrderAt Z z ≤ 0) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ (s : ℂ) (t₀ x T : ℝ),
      s ∈ oneLine → 1 ≤ x → T₀ + |s.im - t₀| ≤ T →
      let height := T + |s.im - t₀| + 3
      let δ := α * A / Real.log (B * height)
      ‖∫ y in -T..T, logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩) *
        (x : ℂ) ^ (⟨-δ, y⟩ : ℂ) / (⟨-δ, y⟩ : ℂ)‖ ≤
        C * x ^ (-δ) * (Real.log height) ^ 3 := by
  obtain ⟨C₁, T₁, hC₁, hbound⟩ := dedekindZeta_perron_left_bound_logDeriv Z hZ hSeries
    hA hB hα hwidth hdisc hzero
  exact dedekindZeta_perron_left_bound_generic Z hZ hA hB hα hC₁ hbound

/-- The estimates (B.7.1.13)–(B.7.1.14) for any function whose logarithmic derivative
obeys the squared-logarithm bound in the narrowed zero-free region. -/
private theorem dedekindZeta_perron_horizontal_bound_generic (Z : ℂ → ℂ)
    {A B α C T₁ : ℝ} (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1)
    (hC : 0 < C)
    (hbound : ∀ z : ℂ, T₁ ≤ |z.im| →
      1 - α * (A / Real.log (B * (|z.im| + 3))) ≤ z.re →
      ‖logDeriv Z z‖ ≤ C * (Real.log |z.im|) ^ 2) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ (s : ℂ) (t₀ x c T y : ℝ),
      s ∈ oneLine → 1 < x → 0 < c → T₀ + |s.im - t₀| ≤ T → (y = -T ∨ y = T) →
      let δ := α * A / Real.log (B * (T + |s.im - t₀| + 3))
      ‖∫ u in -δ..c, logDeriv Z (s - Complex.I * t₀ + ⟨u, y⟩) *
        (x : ℂ) ^ (⟨u, y⟩ : ℂ) / (⟨u, y⟩ : ℂ)‖ ≤
        C * x ^ c * (Real.log (|s.im - t₀ + y| + 3)) ^ 2 / (T * Real.log x) := by
  refine ⟨C, max 2 T₁, hC, le_max_left _ _, ?_⟩
  intro s t₀ x c T y hs hx hc hT hy δ
  have hs1 : s.re = 1 := hs
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hD : 0 ≤ |s.im - t₀| := abs_nonneg _
  have hT2 : 2 + |s.im - t₀| ≤ T := (add_le_add_left (le_max_left 2 T₁) _).trans hT
  have hTT₁ : T₁ + |s.im - t₀| ≤ T := (add_le_add_left (le_max_right 2 T₁) _).trans hT
  have hT0 : 0 < T := by linarith
  have hyT : |y| = T := by
    rcases hy with rfl | rfl
    · rw [abs_neg, abs_of_pos hT0]
    · exact abs_of_pos hT0
  have hlo : T - |s.im - t₀| ≤ |s.im - t₀ + y| := by
    have h1 := abs_sub_abs_le_abs_sub y (-(s.im - t₀))
    rw [abs_neg, sub_neg_eq_add, hyT, add_comm y] at h1
    exact h1
  have hhi : |s.im - t₀ + y| ≤ T + |s.im - t₀| := by
    have h1 := abs_add_le (s.im - t₀) y
    rw [hyT] at h1
    linarith
  have hB0 : 0 < B := by linarith
  have hl3 : 0 < Real.log (B * 3) := Real.log_pos (by linarith)
  have hlogh : Real.log (B * 3) ≤ Real.log (B * (|s.im - t₀ + y| + 3)) :=
    Real.log_le_log (by positivity) (by nlinarith [abs_nonneg (s.im - t₀ + y)])
  have hlogle : Real.log (B * (|s.im - t₀ + y| + 3)) ≤
      Real.log (B * (T + |s.im - t₀| + 3)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hδpos : 0 < δ := div_pos (mul_pos hα.1 hA) (by linarith)
  have hδle : δ ≤ α * (A / Real.log (B * (|s.im - t₀ + y| + 3))) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_left (mul_pos hα.1 hA).le (by linarith) hlogle
  have hℓ0 : 0 ≤ Real.log |s.im - t₀ + y| := Real.log_nonneg (by linarith)
  have hℓle : Real.log |s.im - t₀ + y| ≤ Real.log (|s.im - t₀ + y| + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hpt : ∀ u : ℝ, u ∈ Ioc (-δ) c →
      ‖logDeriv Z (s - Complex.I * t₀ + ⟨u, y⟩) * (x : ℂ) ^ (⟨u, y⟩ : ℂ) / (⟨u, y⟩ : ℂ)‖ ≤
        C * (Real.log |s.im - t₀ + y|) ^ 2 / T * x ^ u := by
    intro u hu
    have hre : (s - Complex.I * t₀ + ⟨u, y⟩ : ℂ).re = 1 + u := by
      simp [hs1]
    have him : (s - Complex.I * t₀ + ⟨u, y⟩ : ℂ).im = s.im - t₀ + y := by
      simp
    have hb := hbound (s - Complex.I * t₀ + ⟨u, y⟩) (by rw [him]; linarith)
      (by rw [hre, him]; linarith [hu.1])
    rw [him] at hb
    have hn : T ≤ ‖(⟨u, y⟩ : ℂ)‖ := by
      have := Complex.abs_im_le_norm (⟨u, y⟩ : ℂ)
      rwa [show (⟨u, y⟩ : ℂ).im = y from rfl, hyT] at this
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      show (⟨u, y⟩ : ℂ).re = u from rfl, mul_div_right_comm]
    have hxu : 0 ≤ x ^ u := (Real.rpow_pos_of_pos hx0 u).le
    refine mul_le_mul_of_nonneg_right ?_ hxu
    exact div_le_div₀ (mul_nonneg hC.le (sq_nonneg _)) hb hT0 hn
  have hderiv : ∀ u ∈ uIcc (-δ) c, HasDerivAt
      (fun u : ℝ ↦ C * (Real.log |s.im - t₀ + y|) ^ 2 / T * (x ^ u / Real.log x))
      (C * (Real.log |s.im - t₀ + y|) ^ 2 / T * x ^ u) u := by
    intro u _
    have h1 := (Real.hasStrictDerivAt_const_rpow hx0 u).hasDerivAt.div_const (Real.log x)
    rw [mul_div_cancel_right₀ _ hlogx.ne'] at h1
    exact h1.const_mul _
  have hcont : Continuous fun u : ℝ ↦ C * (Real.log |s.im - t₀ + y|) ^ 2 / T * x ^ u :=
    continuous_const.mul (Real.continuous_const_rpow hx0.ne')
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable _ _)
  have hle : ‖∫ u in -δ..c, logDeriv Z (s - Complex.I * t₀ + ⟨u, y⟩) *
      (x : ℂ) ^ (⟨u, y⟩ : ℂ) / (⟨u, y⟩ : ℂ)‖ ≤
      ∫ u in -δ..c, C * (Real.log |s.im - t₀ + y|) ^ 2 / T * x ^ u :=
    intervalIntegral.norm_integral_le_of_norm_le (by linarith : -δ ≤ c)
      (Eventually.of_forall hpt) (hcont.intervalIntegrable (-δ) c)
  rw [hint] at hle
  refine hle.trans ?_
  have hxδ : 0 ≤ x ^ (-δ) := (Real.rpow_pos_of_pos hx0 _).le
  have hxc : 0 ≤ x ^ c := (Real.rpow_pos_of_pos hx0 _).le
  have hK : 0 ≤ C * (Real.log |s.im - t₀ + y|) ^ 2 / T :=
    div_nonneg (mul_nonneg hC.le (sq_nonneg _)) hT0.le
  have hsq : (Real.log |s.im - t₀ + y|) ^ 2 ≤ (Real.log (|s.im - t₀ + y| + 3)) ^ 2 :=
    pow_le_pow_left₀ hℓ0 hℓle 2
  calc C * (Real.log |s.im - t₀ + y|) ^ 2 / T * (x ^ c / Real.log x) -
        C * (Real.log |s.im - t₀ + y|) ^ 2 / T * (x ^ (-δ) / Real.log x)
      ≤ C * (Real.log |s.im - t₀ + y|) ^ 2 / T * (x ^ c / Real.log x) :=
        sub_le_self _ (mul_nonneg hK (div_nonneg hxδ hlogx.le))
    _ = C * x ^ c * (Real.log |s.im - t₀ + y|) ^ 2 / (T * Real.log x) := by
        field_simp
    _ ≤ C * x ^ c * (Real.log (|s.im - t₀ + y| + 3)) ^ 2 / (T * Real.log x) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (mul_nonneg hC.le hxc)) (mul_pos hT0 hlogx).le

/-- Paper: Equations (B.7.1.13)–(B.7.1.14), p. 647. On either horizontal
edge the squared logarithm of its shifted height controls the integral.
Deviation: Each edge uses its own absolute shifted height. The contour
width uses the maximum of both heights, and the estimate starts at a
sufficiently large height for the logarithmic-derivative estimate of §B.6.
The punctured disc is its hypothesis on `α`. Both constants may depend on the width. -/
theorem dedekindZeta_perron_horizontal_bound (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    {A B α : ℝ} (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1)
    (hwidth : A ≤ Real.log (B * 3) / 2)
    (hdisc : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0)
    (hzero : ∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re →
      meromorphicOrderAt Z z ≤ 0) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ (s : ℂ) (t₀ x c T y : ℝ),
      s ∈ oneLine → 1 < x → 0 < c → T₀ + |s.im - t₀| ≤ T → (y = -T ∨ y = T) →
      let δ := α * A / Real.log (B * (T + |s.im - t₀| + 3))
      ‖∫ u in -δ..c, logDeriv Z (s - Complex.I * t₀ + ⟨u, y⟩) *
        (x : ℂ) ^ (⟨u, y⟩ : ℂ) / (⟨u, y⟩ : ℂ)‖ ≤
        C * x ^ c * (Real.log (|s.im - t₀ + y| + 3)) ^ 2 / (T * Real.log x) := by
  obtain ⟨C, T₁, hC, hbound⟩ := dedekindZeta_perron_left_bound_logDeriv Z hZ hSeries
    hA hB hα hwidth hdisc hzero
  exact dedekindZeta_perron_horizontal_bound_generic Z hA hB hα hC hbound

/-- Cauchy's formula on a rectangle for a function differentiable on the closed rectangle. -/
private theorem heckeLogDerivPolynomial_normTwist_cauchy {g : ℂ → ℂ} {z w a : ℂ} (hzw : z.re ≤ w.re) (hzw' : z.im ≤ w.im)
    (ha : a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hg : DifferentiableOn ℂ g (Icc z.re w.re ×ℂ Icc z.im w.im)) :
    rectangleIntegral (fun u ↦ g u / (u - a)) z w =
      2 * (Real.pi : ℂ) * Complex.I * g a := by
  have hRn : Icc z.re w.re ×ℂ Icc z.im w.im ∈ 𝓝 a :=
    mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds ha)
      fun u hu ↦ ⟨Ioo_subset_Icc_self hu.1, Ioo_subset_Icc_self hu.2⟩
  have hd : DifferentiableOn ℂ (dslope g a) (Icc z.re w.re ×ℂ Icc z.im w.im) :=
    (Complex.differentiableOn_dslope hRn).mpr hg
  have hne : ∀ u ∈ (Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im),
      u ≠ a := fun u hu hua ↦ hu.2 (hua ▸ ha)
  have hcongr : rectangleIntegral (fun u ↦ g u / (u - a)) z w =
      rectangleIntegral (fun u ↦ dslope g a u + g a * (u - a)⁻¹) z w := by
    refine rectangleIntegral_congr_off_countable hzw hzw' countable_empty fun u hu ↦ ?_
    have hua : u - a ≠ 0 := sub_ne_zero.mpr (hne u hu.1)
    rw [dslope_of_ne _ (hne u hu.1), slope_def_field]
    field_simp
    ring
  have hc1 : ContinuousOn (dslope g a)
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) :=
    hd.continuousOn.mono sdiff_subset
  have hc2 : ContinuousOn (fun u ↦ g a * (u - a)⁻¹)
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀
      fun u hu ↦ sub_ne_zero.mpr (hne u hu))
  rw [hcongr, rectangleIntegral_add hzw hzw' hc1 hc2, rectangleIntegral_const_mul,
    rectangleIntegral_sub_inv ha]
  have h0 := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (dslope g a) z w
    (by rwa [uIcc_of_le hzw, uIcc_of_le hzw'])
  rw [rectangleIntegral_eq]
  simp only [smul_eq_mul] at h0
  rw [h0]
  ring

/-- Cauchy's formula for the derivative on a rectangle. -/
private theorem heckeLogDerivPolynomial_normTwist_cauchy2 {g : ℂ → ℂ} {z w a : ℂ} (hzw : z.re ≤ w.re) (hzw' : z.im ≤ w.im)
    (ha : a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hg : DifferentiableOn ℂ g (Icc z.re w.re ×ℂ Icc z.im w.im)) :
    rectangleIntegral (fun u ↦ g u / (u - a) ^ 2) z w =
      2 * (Real.pi : ℂ) * Complex.I * deriv g a := by
  have hRn : Icc z.re w.re ×ℂ Icc z.im w.im ∈ 𝓝 a :=
    mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds ha)
      fun u hu ↦ ⟨Ioo_subset_Icc_self hu.1, Ioo_subset_Icc_self hu.2⟩
  have hd : DifferentiableOn ℂ (dslope g a) (Icc z.re w.re ×ℂ Icc z.im w.im) :=
    (Complex.differentiableOn_dslope hRn).mpr hg
  have hne : ∀ u ∈ (Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im),
      u ≠ a := fun u hu hua ↦ hu.2 (hua ▸ ha)
  have hcongr : rectangleIntegral (fun u ↦ g u / (u - a) ^ 2) z w =
      rectangleIntegral (fun u ↦ dslope g a u / (u - a) + g a * (u - a) ^ (-2 : ℤ)) z w := by
    refine rectangleIntegral_congr_off_countable hzw hzw' countable_empty fun u hu ↦ ?_
    have hua : u - a ≠ 0 := sub_ne_zero.mpr (hne u hu.1)
    rw [dslope_of_ne _ (hne u hu.1), slope_def_field, zpow_neg, zpow_two]
    field_simp
    ring
  have hc1 : ContinuousOn (fun u ↦ dslope g a u / (u - a))
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) :=
    (hd.continuousOn.mono sdiff_subset).div (continuousOn_id.sub continuousOn_const)
      fun u hu ↦ sub_ne_zero.mpr (hne u hu)
  have hc2 : ContinuousOn (fun u ↦ g a * (u - a) ^ (-2 : ℤ))
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).zpow₀ _
      fun u hu ↦ Or.inl (sub_ne_zero.mpr (hne u hu)))
  rw [hcongr, rectangleIntegral_add hzw hzw' hc1 hc2, rectangleIntegral_const_mul,
    rectangleIntegral_sub_zpow_of_ne ha (by norm_num), heckeLogDerivPolynomial_normTwist_cauchy hzw hzw' ha hd, dslope_same]
  ring

/-- The rectangle with corners `-δ - iT` and `c + iT` splits the right edge into the other three. -/
private theorem heckeLogDerivPolynomial_normTwist_edges (G : ℂ → ℂ) (δ c T : ℝ) :
    (∫ t in -T..T, G ⟨c, t⟩) =
      (rectangleIntegral G ⟨-δ, -T⟩ ⟨c, T⟩ - (∫ u in -δ..c, G ⟨u, -T⟩) +
        ∫ u in -δ..c, G ⟨u, T⟩) / Complex.I + ∫ y in -T..T, G ⟨-δ, y⟩ := by
  rw [rectangleIntegral_eq]
  simp only [← Complex.mk_eq_add_mul_I]
  field_simp
  ring

/-- The residue computation for the Perron integrand `φ(u) xᵘ / u` when `φ` has a simple pole of
residue one at `ρ` with regular part `-Λ`: the two poles at `0` and `ρ` contribute
`dslope (x^·) 0 ρ - Λ 0`, also when `ρ = 0`. -/
private theorem heckeLogDerivPolynomial_normTwist_residue {φ Λ : ℂ → ℂ} {z w ρ : ℂ} {x : ℝ} (hx : 0 < x)
    (hzw : z.re ≤ w.re) (hzw' : z.im ≤ w.im)
    (h0 : (0 : ℂ) ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) (hρ : ρ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hΛ : DifferentiableOn ℂ Λ (Icc z.re w.re ×ℂ Icc z.im w.im))
    (hφ : ∀ u ∈ (Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im),
      φ u = (u - ρ)⁻¹ - Λ u) :
    rectangleIntegral (fun u ↦ φ u * (x : ℂ) ^ u / u) z w =
      2 * (Real.pi : ℂ) * Complex.I * (dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0 ρ - Λ 0) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hE : Differentiable ℂ (fun u : ℂ ↦ (x : ℂ) ^ u) := fun u ↦
    (Complex.hasStrictDerivAt_const_cpow (Or.inl hx0)).hasDerivAt.differentiableAt
  have hEΛ : DifferentiableOn ℂ (fun u ↦ Λ u * (x : ℂ) ^ u) (Icc z.re w.re ×ℂ Icc z.im w.im) :=
    hΛ.mul hE.differentiableOn
  have hne : ∀ a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im,
      ∀ u ∈ (Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im), u - a ≠ 0 :=
    fun a ha u hu h ↦ hu.2 ((sub_eq_zero.mp h) ▸ ha)
  have hcE (a : ℂ) (ha : a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) : ContinuousOn
      (fun u ↦ (x : ℂ) ^ u / (u - a))
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) :=
    hE.continuous.continuousOn.div (continuousOn_id.sub continuousOn_const) (hne a ha)
  have hcΛ : ContinuousOn (fun u ↦ (-1 : ℂ) * (Λ u * (x : ℂ) ^ u / (u - 0)))
      ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) :=
    continuousOn_const.mul ((hEΛ.continuousOn.mono sdiff_subset).div
      (continuousOn_id.sub continuousOn_const) (hne 0 h0))
  have hI1 := heckeLogDerivPolynomial_normTwist_cauchy hzw hzw' h0 hEΛ
  have hI0 := heckeLogDerivPolynomial_normTwist_cauchy hzw hzw' h0 hE.differentiableOn
  have hIρ := heckeLogDerivPolynomial_normTwist_cauchy hzw hzw' hρ hE.differentiableOn
  have hpi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by simp [Real.pi_ne_zero]
  by_cases hρ0 : ρ = 0
  · subst hρ0
    have hI2 := heckeLogDerivPolynomial_normTwist_cauchy2 hzw hzw' h0 hE.differentiableOn
    have hcongr : rectangleIntegral (fun u ↦ φ u * (x : ℂ) ^ u / u) z w =
        rectangleIntegral (fun u ↦ (x : ℂ) ^ u / (u - 0) ^ 2 +
          (-1 : ℂ) * (Λ u * (x : ℂ) ^ u / (u - 0))) z w := by
      refine rectangleIntegral_congr_off_countable hzw hzw' countable_empty fun u hu ↦ ?_
      have hu0 := hne 0 h0 u hu.1
      rw [sub_zero] at hu0
      simp only [hφ u hu.1, sub_zero]
      field_simp
      ring
    have hc2 : ContinuousOn (fun u ↦ (x : ℂ) ^ u / (u - 0) ^ 2)
        ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) :=
      hE.continuous.continuousOn.div ((continuousOn_id.sub continuousOn_const).pow 2)
        fun u hu ↦ pow_ne_zero 2 (hne 0 h0 u hu)
    rw [hcongr, rectangleIntegral_add hzw hzw' hc2 hcΛ, rectangleIntegral_const_mul, hI2, hI1,
      dslope_same, Complex.cpow_zero]
    ring
  · have hcongr : rectangleIntegral (fun u ↦ φ u * (x : ℂ) ^ u / u) z w =
        rectangleIntegral (fun u ↦ (ρ⁻¹ * ((x : ℂ) ^ u / (u - ρ)) +
          (-ρ⁻¹) * ((x : ℂ) ^ u / (u - 0))) +
          (-1 : ℂ) * (Λ u * (x : ℂ) ^ u / (u - 0))) z w := by
      refine rectangleIntegral_congr_off_countable hzw hzw' countable_empty fun u hu ↦ ?_
      have hu0 := hne 0 h0 u hu.1
      have huρ := hne ρ hρ u hu.1
      rw [sub_zero] at hu0
      simp only [hφ u hu.1, sub_zero]
      field_simp
      ring
    have hc1 : ContinuousOn (fun u ↦ ρ⁻¹ * ((x : ℂ) ^ u / (u - ρ)) +
          (-ρ⁻¹) * ((x : ℂ) ^ u / (u - 0)))
        ((Icc z.re w.re ×ℂ Icc z.im w.im) \ (Ioo z.re w.re ×ℂ Ioo z.im w.im)) :=
      (continuousOn_const.mul (hcE ρ hρ)).add (continuousOn_const.mul (hcE 0 h0))
    rw [hcongr, rectangleIntegral_add hzw hzw' hc1 hcΛ,
      rectangleIntegral_add (f := fun u ↦ ρ⁻¹ * ((x : ℂ) ^ u / (u - ρ)))
        (g := fun u ↦ (-ρ⁻¹) * ((x : ℂ) ^ u / (u - 0))) hzw hzw'
        (continuousOn_const.mul (hcE ρ hρ))
        (continuousOn_const.mul (hcE 0 h0)),
      rectangleIntegral_const_mul, rectangleIntegral_const_mul, rectangleIntegral_const_mul,
      hI1, hI0, hIρ, dslope_of_ne _ hρ0, slope_def_field, Complex.cpow_zero]
    field_simp
    ring


/-- The Dedekind zeta continuation has a simple pole at one and no other pole to the right of
the imaginary axis. -/
private theorem heckeLogDerivPolynomial_normTwist_zeta (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    meromorphicOrderAt Z 1 = -1 ∧ ∀ v : ℂ, 0 < v.re → v ≠ 1 → AnalyticAt ℂ Z v := by
  have hS₀ : ∀ s : halfPlane, Z s = finiteHeckeL (1 : U[F]) s :=
    fun s ↦ (hSeries s).trans (heckeLogDerivPolynomial_perron_error_zeta s).symm
  have hΓ (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ (heckeGammaFactor (1 : U[F])) s :=
    DifferentiableOn.analyticAt (s := Complex.re ⁻¹' Ioi 0)
      (fun w hw ↦ (differentiableAt_heckeGammaFactor_of_re_pos (1 : U[F]) hw).differentiableWithinAt)
      ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hs)
  let M : ℂ → ℂ := fun w ↦ heckeGammaFactor (1 : U[F]) w * Z w
  have hM : MeromorphicOn M univ := fun x _ ↦
    (meromorphic_heckeGammaFactor (1 : U[F]) x).mul (hZ (mem_univ x)).meromorphicAt
  have hΛs : ∀ s : halfPlane, toMeromorphicNFOn M univ s = completedHeckeL (1 : U[F]) s := by
    intro s
    have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
    have hMan : AnalyticAt ℂ M s :=
      (hΓ s hs).mul (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) Z hZ hS₀ s).1
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr hMan.meromorphicNFAt]
    simp [M, hS₀ s, completedHeckeL, finiteHeckeL]
  have hord (s : ℂ) (hs : 0 < s.re) :
      meromorphicOrderAt (toMeromorphicNFOn M univ) s = meromorphicOrderAt Z s := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hM (mem_univ _)]
    exact meromorphicOrderAt_mul_of_ne_zero (hΓ s hs)
      (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) hs)
  obtain ⟨t, ⟨-, -, h1, han⟩, -⟩ := completedHeckeL_continuation_simplePoles (1 : U[F])
    (toMeromorphicNFOn M univ) (meromorphicNFOn_toMeromorphicNFOn _ _) hΛs (by ext x; rfl)
  have hanZ (v : ℂ) (hv : 0 < v.re) (hv1 : v ≠ 1 + Complex.I * t) : AnalyticAt ℂ Z v := by
    have hvI : v ≠ Complex.I * t := fun h ↦ by
      rw [h] at hv
      simp at hv
    have h0 : 0 ≤ meromorphicOrderAt Z v := by
      rw [← hord v hv]
      exact (han v (by simp [hvI, hv1])).meromorphicOrderAt_nonneg
    exact (hZ (mem_univ v)).meromorphicOrderAt_nonneg_iff_analyticAt.mp h0
  -- The pole is at one, by the residue of Dedekind zeta.
  have ht : (t : ℂ) = 0 := by
    by_contra ht0
    have hne1 : (1 : ℂ) ≠ 1 + Complex.I * t := by
      intro h
      apply ht0
      have := congrArg Complex.im h
      simpa using this.symm
    have hA := hanZ 1 (by simp) hne1
    have hreal : Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
      simpa using (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
        nhdsWithin_le_nhds
    have hlimZ : Tendsto (fun σ : ℝ ↦ ((σ : ℂ) - 1) * Z σ) (𝓝[>] 1)
        (𝓝 (dedekindZeta_residue F : ℂ)) := by
      refine (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      rw [show Z σ = dedekindZeta F σ from
        hSeries ⟨(σ : ℂ), show 1 < (σ : ℂ).re by simpa using hσ⟩]
    have hlim0 : Tendsto (fun σ : ℝ ↦ ((σ : ℂ) - 1) * Z σ) (𝓝[>] 1) (𝓝 ((1 - 1) * Z 1)) :=
      ((continuous_id.sub continuous_const).continuousAt.mul hA.continuousAt).tendsto.comp hreal
    have := tendsto_nhds_unique hlimZ hlim0
    rw [sub_self, zero_mul, Complex.ofReal_eq_zero] at this
    exact dedekindZeta_residue_ne_zero F this
  have hp : 1 + Complex.I * (t : ℂ) = 1 := by rw [ht, mul_zero, add_zero]
  refine ⟨?_, fun v hv hv1 ↦ hanZ v hv (by rwa [hp])⟩
  rw [← hord 1 (by simp), ← hp]
  exact h1

/-- Removing the pole of Dedekind zeta: `W(v) = (v - 1) Z(v)` in normal form. -/
private theorem heckeLogDerivPolynomial_normTwist_W (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hord : meromorphicOrderAt Z 1 = -1)
    (han : ∀ v : ℂ, 0 < v.re → v ≠ 1 → AnalyticAt ℂ Z v) :
    (∀ v : ℂ, 0 < v.re → AnalyticAt ℂ (toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ) v) ∧
      toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ 1 ≠ 0 ∧
      ∀ v : ℂ, 0 < v.re → v ≠ 1 → Z v ≠ 0 →
        toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ v ≠ 0 ∧
        logDeriv Z v = logDeriv (toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ) v -
          (v - 1)⁻¹ := by
  set f : ℂ → ℂ := fun v ↦ (v - 1) * Z v with hf
  set W := toMeromorphicNFOn f univ with hW
  have hm : MeromorphicOn f univ := fun x _ ↦
    ((analyticAt_id.sub analyticAt_const).meromorphicAt).mul (hZ (mem_univ x)).meromorphicAt
  have hWNF : MeromorphicNFOn W univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hOpen : IsOpen {v : ℂ | 0 < v.re ∧ v ≠ 1} := by
    have h1 : IsOpen {v : ℂ | 0 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    exact h1.inter isOpen_ne
  have heq (v : ℂ) (hv : 0 < v.re) (hv1 : v ≠ 1) : W v = f v := by
    have hfa : AnalyticAt ℂ f v := (analyticAt_id.sub analyticAt_const).mul (han v hv hv1)
    rw [hW, toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr hfa.meromorphicNFAt]
  have hevent (v : ℂ) (hv : 0 < v.re) (hv1 : v ≠ 1) : W =ᶠ[𝓝 v] f := by
    filter_upwards [hOpen.mem_nhds ⟨hv, hv1⟩] with u hu
    exact heq u hu.1 hu.2
  have hord1 : meromorphicOrderAt W 1 = 0 := by
    rw [hW, meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _)]
    have := meromorphicOrderAt_mul (f := fun v : ℂ ↦ v - 1) (g := Z) (x := 1)
      (analyticAt_id.sub analyticAt_const).meromorphicAt (hZ (mem_univ 1)).meromorphicAt
    change meromorphicOrderAt ((fun v : ℂ ↦ v - 1) * Z) 1 = 0
    rw [this, meromorphicOrderAt_id_sub_const, hord]
    rfl
  have hW1 : AnalyticAt ℂ W 1 :=
    (hWNF (mem_univ 1)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hord1.ge
  refine ⟨fun v hv ↦ ?_, (hWNF (mem_univ 1)).meromorphicOrderAt_eq_zero_iff.mp hord1,
    fun v hv hv1 hZv ↦ ?_⟩
  · rcases eq_or_ne v 1 with rfl | hv1
    · exact hW1
    · exact ((analyticAt_id.sub analyticAt_const).mul (han v hv hv1)).congr
        (hevent v hv hv1).symm
  · have hsub : v - 1 ≠ 0 := sub_ne_zero.mpr hv1
    refine ⟨by rw [heq v hv hv1]; exact mul_ne_zero hsub hZv, ?_⟩
    have hZW : Z =ᶠ[𝓝 v] fun u ↦ W u * (u - 1)⁻¹ := by
      filter_upwards [hevent v hv hv1, hOpen.mem_nhds ⟨hv, hv1⟩] with u hu hu'
      rw [hu, hf]
      field_simp [sub_ne_zero.mpr hu'.2]
    have hWa : AnalyticAt ℂ W v :=
      ((analyticAt_id.sub analyticAt_const).mul (han v hv hv1)).congr (hevent v hv hv1).symm
    have hWv : W v ≠ 0 := by rw [heq v hv hv1]; exact mul_ne_zero hsub hZv
    rw [(logDeriv_congr_nhds hZW).eq_of_nhds]
    have hmul := logDeriv_mul (f := W) (g := fun u : ℂ ↦ (u - 1)⁻¹) v hWv (inv_ne_zero hsub)
      hWa.differentiableAt ((differentiableAt_id.sub_const 1).inv hsub)
    change logDeriv (W * fun u : ℂ ↦ (u - 1)⁻¹) v = _
    rw [hmul, sub_eq_add_neg]
    congr 1
    have hd : HasDerivAt (fun u : ℂ ↦ (u - 1)⁻¹) (-1 / (v - 1) ^ 2) v := by
      have h := (hasDerivAt_inv hsub).comp v ((hasDerivAt_id v).sub_const 1)
      convert h using 1
      · rfl
      · ring
    rw [logDeriv_apply (f := fun u : ℂ ↦ (u - 1)⁻¹), hd.deriv]
    field_simp


/-- Admissible constants for the zero-free region of Dedekind zeta, in the form used by the
contour estimates of (B.7.1.12)–(B.7.1.14). -/
private theorem heckeLogDerivPolynomial_normTwist_region (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ A B α : ℝ, 0 < A ∧ 1 / 3 < B ∧ α ∈ Ioo 0 1 ∧ A ≤ Real.log (B * 3) / 2 ∧
      (∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0) ∧
      (∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re → meromorphicOrderAt Z z ≤ 0) := by
  obtain ⟨A₀, hA₀, hF⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B, hB, hzf⟩ := hF F (1 : U[F])
  have hzf' := hzf Z hZ (fun s ↦ (hSeries s).trans (heckeLogDerivPolynomial_perron_error_zeta s).symm)
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = (Module.finrank ℚ F : ℝ) ^ 4 := ⟨_, rfl⟩
  rw [← hd_def] at hzf'
  have hd : 0 < d := by
    rw [hd_def]
    have : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos
    positivity
  have hl3 : 0 < Real.log (B * 3) := Real.log_pos (by linarith)
  have hl4 : 0 < Real.log (B * 4) := Real.log_pos (by linarith)
  obtain ⟨A, hA_def⟩ : ∃ A : ℝ, A = min (A₀ / d) (Real.log (B * 3) / 2) := ⟨_, rfl⟩
  have hA : 0 < A := hA_def ▸ lt_min (div_pos hA₀ hd) (by linarith)
  have hAd : A * d ≤ A₀ := by
    have h := hA_def ▸ min_le_left (A₀ / d) (Real.log (B * 3) / 2)
    calc A * d ≤ A₀ / d * d := mul_le_mul_of_nonneg_right h hd.le
      _ = A₀ := div_mul_cancel₀ _ hd.ne'
  obtain ⟨α, hα_def⟩ : ∃ α : ℝ, α = min (1 / 2) (A / Real.log (B * 4)) := ⟨_, rfl⟩
  have hα : 0 < α := hα_def ▸ lt_min (by norm_num) (div_pos hA hl4)
  have hα2 : α ≤ 1 / 2 := hα_def ▸ min_le_left _ _
  have hαA : α ≤ A / Real.log (B * 4) := hα_def ▸ min_le_right _ _
  have hzero : ∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re →
      meromorphicOrderAt Z z ≤ 0 := by
    intro z hz
    apply hzf' z
    have hlz : 0 < Real.log (B * (|z.im| + 3)) :=
      Real.log_pos (by nlinarith [abs_nonneg z.im])
    have hle : A / Real.log (B * (|z.im| + 3)) ≤
        A₀ / (d * Real.log (B * (|z.im| + 3))) := by
      rw [div_le_div_iff₀ hlz (by positivity)]
      nlinarith
    linarith
  refine ⟨A, B, α, hA, hB, ⟨hα, by linarith⟩, hA_def ▸ min_le_right _ _,
    fun z _ hz ↦ hzero z ?_, hzero⟩
  have him : |z.im| ≤ ‖z - 1‖ := by
    simpa using Complex.abs_im_le_norm (z - 1)
  have hre : 1 - z.re ≤ ‖z - 1‖ := by
    have h := Complex.abs_re_le_norm (z - 1)
    rw [Complex.sub_re, Complex.one_re] at h
    linarith [neg_abs_le (z.re - 1)]
  have hlz : 0 < Real.log (B * (|z.im| + 3)) :=
    Real.log_pos (by nlinarith [abs_nonneg z.im])
  have hle : Real.log (B * (|z.im| + 3)) ≤ Real.log (B * 4) :=
    Real.log_le_log (by nlinarith [abs_nonneg z.im]) (by nlinarith)
  have h2 : A / Real.log (B * 4) ≤ A / Real.log (B * (|z.im| + 3)) :=
    div_le_div_of_nonneg_left hA.le hlz hle
  linarith

/-- Paper: the residue computation and (B.7.1.12)–(B.7.1.14), pp. 646–647. The truncated Perron
integral of the shifted Dedekind zeta logarithmic derivative is the sum of the residues at `0`
and at the pole, up to the integrals over the left and horizontal edges of the rectangle. -/
private theorem heckeLogDerivPolynomial_normTwist_core (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ A B α C T₀ : ℝ, 0 < A ∧ 1 / 3 < B ∧ α ∈ Ioo 0 1 ∧ A ≤ Real.log (B * 3) / 2 ∧ 0 < C ∧
      2 ≤ T₀ ∧ ∀ (s : ℂ) (t₀ x c T : ℝ), s ∈ oneLine → 1 < x → 0 < c → T₀ + |s.im - t₀| ≤ T →
        ‖truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T -
          (dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0 (1 + Complex.I * t₀ - s) -
            logDeriv (toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ) (s - Complex.I * t₀))‖ ≤
          C * (x ^ c * (Real.log (T + |s.im - t₀| + 3)) ^ 2 / (T * Real.log x) +
            x ^ (-(α * A / Real.log (B * (T + |s.im - t₀| + 3)))) *
              (Real.log (T + |s.im - t₀| + 3)) ^ 3) := by
  obtain ⟨hord, hanZ⟩ := heckeLogDerivPolynomial_normTwist_zeta Z hZ hSeries
  obtain ⟨hWan, hW1, hWlog⟩ := heckeLogDerivPolynomial_normTwist_W Z hZ hord hanZ
  obtain ⟨A, B, α, hA, hB, hα, hwidth, hdisc, hzero⟩ := heckeLogDerivPolynomial_normTwist_region Z hZ hSeries
  obtain ⟨Cl, Tl, hCl, hTl, hleft⟩ :=
    dedekindZeta_perron_left_bound Z hZ hSeries hA hB hα hwidth hdisc hzero
  obtain ⟨Ch, Th, hCh, hTh, hhor⟩ :=
    dedekindZeta_perron_horizontal_bound Z hZ hSeries hA hB hα hwidth hdisc hzero
  refine ⟨A, B, α, 2 * Ch + Cl, max Tl Th, hA, hB, hα, hwidth, by positivity,
    le_max_of_le_left hTl, fun s t₀ x c T hs hx hc hT ↦ ?_⟩
  set W := toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ with hW
  have hs1 : s.re = 1 := hs
  have hx0 : 0 < x := by linarith
  have hD : 0 ≤ |s.im - t₀| := abs_nonneg _
  have hT2 : 2 ≤ T := by linarith [le_max_left Tl Th]
  have hT0 : 0 < T := by linarith
  set h := T + |s.im - t₀| + 3 with hh
  have hB0 : 0 < B := by linarith
  have hlogBh : 0 < Real.log (B * h) := Real.log_pos (by nlinarith)
  have hlog3 : Real.log (B * 3) ≤ Real.log (B * h) :=
    Real.log_le_log (by linarith) (by nlinarith)
  set δ := α * A / Real.log (B * h) with hδ
  have hδ0 : 0 < δ := div_pos (mul_pos hα.1 hA) hlogBh
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one hlogBh]
    nlinarith [hα.2]
  set v₀ := s - Complex.I * t₀ with hv₀
  set ρ : ℂ := 1 + Complex.I * t₀ - s with hρ
  -- Analyticity and nonvanishing on the closed rectangle.
  have hgood (u : ℂ) (hu : u ∈ Icc (-δ) c ×ℂ Icc (-T) T) :
      AnalyticAt ℂ W (v₀ + u) ∧ W (v₀ + u) ≠ 0 ∧ (v₀ + u ≠ 1 → Z (v₀ + u) ≠ 0) := by
    have hre : (v₀ + u).re = 1 + u.re := by simp [hv₀, hs1]
    have hpos : 0 < (v₀ + u).re := by rw [hre]; linarith [hu.1.1]
    have him : |(v₀ + u).im| + 3 ≤ h := by
      have h1 : (v₀ + u).im = (s.im - t₀) + u.im := by simp [hv₀]
      rw [h1]
      have := abs_add_le (s.im - t₀) u.im
      have := abs_le.mpr ⟨hu.2.1, hu.2.2⟩
      linarith
    have hlz : 0 < Real.log (B * (|(v₀ + u).im| + 3)) :=
      Real.log_pos (by nlinarith [abs_nonneg (v₀ + u).im])
    have hle : Real.log (B * (|(v₀ + u).im| + 3)) ≤ Real.log (B * h) :=
      Real.log_le_log (by nlinarith [abs_nonneg (v₀ + u).im]) (by nlinarith)
    have hδle : δ < A / Real.log (B * (|(v₀ + u).im| + 3)) := by
      calc δ = α * (A / Real.log (B * h)) := by rw [hδ, mul_div_assoc]
        _ < 1 * (A / Real.log (B * h)) :=
          mul_lt_mul_of_pos_right hα.2 (div_pos hA hlogBh)
        _ ≤ A / Real.log (B * (|(v₀ + u).im| + 3)) := by
          rw [one_mul]; exact div_le_div_of_nonneg_left hA.le hlz hle
    have hZne (h1 : v₀ + u ≠ 1) : Z (v₀ + u) ≠ 0 :=
      (hZ (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp
        (le_antisymm (hzero (v₀ + u) (by rw [hre]; linarith [hu.1.1]))
          (hanZ _ hpos h1).meromorphicOrderAt_nonneg)
    refine ⟨hWan _ hpos, ?_, hZne⟩
    rcases eq_or_ne (v₀ + u) 1 with h1 | h1
    · rw [h1]; exact hW1
    · exact (hWlog _ hpos h1 (hZne h1)).1
  have hrect : (-δ : ℝ) ≤ c := by linarith
  have hrect' : (-T : ℝ) ≤ T := by linarith
  have h0mem : (0 : ℂ) ∈ Ioo (⟨-δ, -T⟩ : ℂ).re (⟨c, T⟩ : ℂ).re ×ℂ
      Ioo (⟨-δ, -T⟩ : ℂ).im (⟨c, T⟩ : ℂ).im := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
  have hρmem : ρ ∈ Ioo (⟨-δ, -T⟩ : ℂ).re (⟨c, T⟩ : ℂ).re ×ℂ
      Ioo (⟨-δ, -T⟩ : ℂ).im (⟨c, T⟩ : ℂ).im := by
    have hρre : ρ.re = 0 := by simp [hρ, hs1]
    have hρim : ρ.im = t₀ - s.im := by simp [hρ]
    have habs : |t₀ - s.im| = |s.im - t₀| := abs_sub_comm _ _
    have h1 := neg_abs_le (t₀ - s.im)
    have h2 := le_abs_self (t₀ - s.im)
    have hTm : 2 + |s.im - t₀| ≤ T := by linarith [le_max_left Tl Th]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [hρre, hρim] <;> linarith
  have hΛ : DifferentiableOn ℂ (fun u ↦ logDeriv W (v₀ + u))
      (Icc (⟨-δ, -T⟩ : ℂ).re (⟨c, T⟩ : ℂ).re ×ℂ Icc (⟨-δ, -T⟩ : ℂ).im (⟨c, T⟩ : ℂ).im) := by
    intro u hu
    obtain ⟨hWa, hWne, -⟩ := hgood u hu
    have hd : DifferentiableAt ℂ (logDeriv W) (v₀ + u) :=
      hWa.deriv.differentiableAt.div hWa.differentiableAt hWne
    exact (hd.comp u ((differentiableAt_const _).add differentiableAt_id)).differentiableWithinAt
  have hφ : ∀ u ∈ (Icc (⟨-δ, -T⟩ : ℂ).re (⟨c, T⟩ : ℂ).re ×ℂ
      Icc (⟨-δ, -T⟩ : ℂ).im (⟨c, T⟩ : ℂ).im) \
      (Ioo (⟨-δ, -T⟩ : ℂ).re (⟨c, T⟩ : ℂ).re ×ℂ Ioo (⟨-δ, -T⟩ : ℂ).im (⟨c, T⟩ : ℂ).im),
      -logDeriv Z (v₀ + u) = (u - ρ)⁻¹ - logDeriv W (v₀ + u) := by
    intro u hu
    have huρ : u ≠ ρ := fun h ↦ hu.2 (h ▸ hρmem)
    have hv1 : v₀ + u ≠ 1 := fun h ↦ huρ (by rw [hρ]; linear_combination h)
    have hre : (v₀ + u).re = 1 + u.re := by simp [hv₀, hs1]
    have hpos : 0 < (v₀ + u).re := by rw [hre]; linarith [hu.1.1.1]
    rw [(hWlog _ hpos hv1 ((hgood u hu.1).2.2 hv1)).2,
      show v₀ + u - 1 = u - ρ by rw [hv₀, hρ]; ring]
    ring
  have hres := heckeLogDerivPolynomial_normTwist_residue (φ := fun u ↦ -logDeriv Z (v₀ + u))
    (Λ := fun u ↦ logDeriv W (v₀ + u)) hx0 hrect hrect' h0mem hρmem hΛ hφ
  set G : ℂ → ℂ := fun u ↦ -logDeriv Z (v₀ + u) * (x : ℂ) ^ u / u with hG
  have hres' : rectangleIntegral G ⟨-δ, -T⟩ ⟨c, T⟩ = 2 * (Real.pi : ℂ) * Complex.I *
      (dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0 ρ - logDeriv W v₀) := by
    have h' := hres
    simp only [add_zero] at h'
    exact h'
  have hPer : truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T =
      (∫ t in -T..T, G ⟨c, t⟩) / (2 * Real.pi) := by
    unfold truncatedPerronIntegral
    refine congrArg (· / (2 * (Real.pi : ℂ))) (intervalIntegral.integral_congr fun t _ ↦ ?_)
    change -logDeriv Z (s + (⟨c, t⟩ : ℂ) - Complex.I * t₀) * (x : ℂ) ^ (⟨c, t⟩ : ℂ) /
      (⟨c, t⟩ : ℂ) = -logDeriv Z (v₀ + ⟨c, t⟩) * (x : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)
    rw [show s + (⟨c, t⟩ : ℂ) - Complex.I * t₀ = v₀ + ⟨c, t⟩ by rw [hv₀]; ring]
  have hedge := heckeLogDerivPolynomial_normTwist_edges G δ c T
  have hEdge (a b : ℝ) (p : ℝ → ℂ) : (∫ u in a..b, G (p u)) =
      -∫ u in a..b, logDeriv Z (s - Complex.I * t₀ + p u) * (x : ℂ) ^ (p u) / p u := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    ext u
    simp only [hG, hv₀]
    ring
  have hbB := hhor s t₀ x c T (-T) hs hx hc (by linarith [le_max_right Tl Th]) (Or.inl rfl)
  have hbT := hhor s t₀ x c T T hs hx hc (by linarith [le_max_right Tl Th]) (Or.inr rfl)
  have hbL := hleft s t₀ x T hs hx.le (by linarith [le_max_left Tl Th])
  dsimp only at hbB hbT hbL
  rw [← hh, ← hδ] at hbB hbT hbL
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg (by linarith)
  have hlogy (y : ℝ) (hy : |y| = T) :
      Real.log (|s.im - t₀ + y| + 3) ^ 2 ≤ Real.log h ^ 2 := by
    have h1 : |s.im - t₀ + y| + 3 ≤ h := by
      have := abs_add_le (s.im - t₀) y
      rw [hh]; linarith
    have h2 : 0 ≤ Real.log (|s.im - t₀ + y| + 3) :=
      Real.log_nonneg (by linarith [abs_nonneg (s.im - t₀ + y)])
    exact pow_le_pow_left₀ h2 (Real.log_le_log (by positivity) h1) 2
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hX : 0 ≤ x ^ c * Real.log h ^ 2 / (T * Real.log x) := by positivity
  have hY : 0 ≤ x ^ (-δ) * Real.log h ^ 3 := by positivity
  have hB' : Ch * x ^ c * Real.log (|s.im - t₀ + -T| + 3) ^ 2 / (T * Real.log x) ≤
      Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) := by
    rw [show Ch * x ^ c * Real.log (|s.im - t₀ + -T| + 3) ^ 2 / (T * Real.log x) =
        (Ch * x ^ c / (T * Real.log x)) * Real.log (|s.im - t₀ + -T| + 3) ^ 2 by ring,
      show Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) =
        (Ch * x ^ c / (T * Real.log x)) * Real.log h ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left (hlogy (-T) (by rw [abs_neg, abs_of_pos hT0]))
      (by positivity)
  have hT' : Ch * x ^ c * Real.log (|s.im - t₀ + T| + 3) ^ 2 / (T * Real.log x) ≤
      Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) := by
    rw [show Ch * x ^ c * Real.log (|s.im - t₀ + T| + 3) ^ 2 / (T * Real.log x) =
        (Ch * x ^ c / (T * Real.log x)) * Real.log (|s.im - t₀ + T| + 3) ^ 2 by ring,
      show Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) =
        (Ch * x ^ c / (T * Real.log x)) * Real.log h ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left (hlogy T (abs_of_pos hT0)) (by positivity)
  have eB := hEdge (-δ) c (fun u ↦ ⟨u, -T⟩)
  have eT := hEdge (-δ) c (fun u ↦ ⟨u, T⟩)
  have eL := hEdge (-T) T (fun y ↦ ⟨-δ, y⟩)
  have hBo : ‖∫ u in -δ..c, G ⟨u, -T⟩‖ ≤ Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) := by
    rw [eB, norm_neg]; exact hbB.trans hB'
  have hTp : ‖∫ u in -δ..c, G ⟨u, T⟩‖ ≤ Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) := by
    rw [eT, norm_neg]; exact hbT.trans hT'
  have hLe : ‖∫ y in -T..T, G ⟨-δ, y⟩‖ ≤ Cl * (x ^ (-δ) * Real.log h ^ 3) := by
    rw [eL, norm_neg, ← mul_assoc]; exact hbL
  set Bo := ∫ u in -δ..c, G ⟨u, -T⟩
  set Tp := ∫ u in -δ..c, G ⟨u, T⟩
  set Le := ∫ y in -T..T, G ⟨-δ, y⟩
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have key : ((2 * (Real.pi : ℂ) * Complex.I * (dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0 ρ -
      logDeriv W v₀) - Bo + Tp) / Complex.I + Le) / (2 * (Real.pi : ℂ)) -
      (dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0 ρ - logDeriv W v₀) =
      ((-Bo + Tp) / Complex.I + Le) / (2 * (Real.pi : ℂ)) := by
    field_simp
    ring
  rw [hPer, hedge, hres', key, norm_div]
  have h2pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  rw [h2pi, div_le_iff₀ (by positivity)]
  have hsum : ‖(-Bo + Tp) / Complex.I + Le‖ ≤ ‖Bo‖ + ‖Tp‖ + ‖Le‖ := by
    calc ‖(-Bo + Tp) / Complex.I + Le‖ ≤ ‖(-Bo + Tp) / Complex.I‖ + ‖Le‖ := norm_add_le _ _
      _ = ‖-Bo + Tp‖ + ‖Le‖ := by rw [norm_div, Complex.norm_I, div_one]
      _ ≤ ‖Bo‖ + ‖Tp‖ + ‖Le‖ := by
        have := norm_add_le (-Bo) Tp
        rw [norm_neg] at this
        linarith
  have hpi3 := Real.pi_gt_three
  have hC : 0 ≤ (2 * Ch + Cl) * (x ^ c * Real.log h ^ 2 / (T * Real.log x) +
      x ^ (-δ) * Real.log h ^ 3) := by positivity
  nlinarith [mul_nonneg hCh.le hY, mul_nonneg hCl.le hX]

/-- On the 1-line, `W(v) = (v - 1) Z(v)` is analytic and nonzero, and `Z` has no zero. -/
private theorem heckeLogDerivPolynomial_normTwist_line (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) (v : ℂ) (hv : v.re = 1) :
    AnalyticAt ℂ (toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ) v ∧
      toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ v ≠ 0 ∧ (v ≠ 1 → Z v ≠ 0) := by
  obtain ⟨hord, hanZ⟩ := heckeLogDerivPolynomial_normTwist_zeta Z hZ hSeries
  obtain ⟨hWan, hW1, hWlog⟩ := heckeLogDerivPolynomial_normTwist_W Z hZ hord hanZ
  obtain ⟨A, B, α, hA, hB, -, -, -, hzero⟩ := heckeLogDerivPolynomial_normTwist_region Z hZ hSeries
  have hpos : 0 < v.re := by rw [hv]; norm_num
  have hZne (h1 : v ≠ 1) : Z v ≠ 0 := by
    have hlz : 0 < Real.log (B * (|v.im| + 3)) :=
      Real.log_pos (by nlinarith [abs_nonneg v.im])
    have hle := hzero v (by rw [hv]; linarith [div_pos hA hlz])
    exact (hZ (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp
      (le_antisymm hle (hanZ _ hpos h1).meromorphicOrderAt_nonneg)
  refine ⟨hWan v hpos, ?_, hZne⟩
  rcases eq_or_ne v 1 with h1 | h1
  · rw [h1]; exact hW1
  · exact (hWlog v hpos h1 (hZne h1)).1

/-- The cutoff polynomial is entire. -/
private theorem heckeLogDerivPolynomial_normTwist_poly (χ : U[F]) (x : ℝ) (s : ℂ) :
    AnalyticAt ℂ (heckeLogDerivPolynomial χ x) s := by
  have heq : heckeLogDerivPolynomial χ x = fun s ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n / (n : ℂ) ^ s := by
    funext s
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    exact LSeries.term_of_ne_zero (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1) _ _
  have hd : Differentiable ℂ (heckeLogDerivPolynomial χ x) := by
    rw [heq]
    refine Differentiable.fun_sum fun n hn s ↦ ?_
    have hn0 : (n : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1)
    exact (differentiableAt_const _).div
      (Complex.hasStrictDerivAt_const_cpow (Or.inl hn0)).hasDerivAt.differentiableAt
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))
  exact hd.analyticAt s

/-- The difference quotient of `u ↦ xᵘ` at `0` is entire. -/
private theorem heckeLogDerivPolynomial_normTwist_dslope {x : ℝ} (hx : 0 < x) (z : ℂ) :
    AnalyticAt ℂ (dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0) z := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hE : Differentiable ℂ (fun u : ℂ ↦ (x : ℂ) ^ u) := fun u ↦
    (Complex.hasStrictDerivAt_const_cpow (Or.inl hx0)).hasDerivAt.differentiableAt
  have hd : DifferentiableOn ℂ (dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0) univ :=
    (Complex.differentiableOn_dslope univ_mem).mpr hE.differentiableOn
  exact (differentiableOn_univ.mp hd).analyticAt z

/-- The majorant of the remainder decays along `σ = √(log x) → ∞`. -/
private theorem heckeLogDerivPolynomial_normTwist_decay (K₁ K₂ a : ℝ) (ha : 0 < a) :
    Tendsto (fun σ : ℝ ↦ K₁ * ((σ ^ 4 + σ ^ 2 + 1) * Real.exp (-σ)) +
      K₂ * (σ ^ 3 * Real.exp (-(a * σ)))) atTop (𝓝 0) := by
  have h4 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4
  have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have h3 : Tendsto (fun σ : ℝ ↦ σ ^ 3 * Real.exp (-(a * σ))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp
      (tendsto_id.const_mul_atTop ha)).const_mul (a⁻¹ ^ 3)
    rw [mul_zero] at h
    refine h.congr fun σ ↦ ?_
    simp only [Function.comp_apply, id]
    field_simp
  have hsum : Tendsto (fun σ : ℝ ↦ (σ ^ 4 + σ ^ 2 + 1) * Real.exp (-σ)) atTop (𝓝 0) := by
    have h := (h4.add h2).add h0
    rw [add_zero, add_zero] at h
    refine h.congr fun σ ↦ ?_
    ring
  simpa using (hsum.const_mul K₁).add (h3.const_mul K₂)

/-- The last term of (B.7.1.11) with `c = 1 / log x`, for cuts in `J_b`. -/
private theorem heckeLogDerivPolynomial_normTwist_int {x b T : ℝ} (hx : 1 < x) (hb : 0 < b)
    (hT : 0 < T) (hxJ : x ∈ perronCutoffSet b) :
    (if (⌊x⌋₊ : ℝ) = x then 1 / Real.log x * Real.log x / (T * x)
      else Real.log x / (T * |x - (round x : ℝ)|)) ≤ 1 / T + Real.log x / (T * b) := by
  have hL0 : 0 < Real.log x := Real.log_pos hx
  have hLb : 0 ≤ Real.log x / (T * b) := by positivity
  split_ifs with hfl
  · rw [one_div_mul_cancel hL0.ne']
    have : 1 / (T * x) ≤ 1 / T :=
      one_div_le_one_div_of_le hT (le_mul_of_one_le_right hT.le hx.le)
    linarith
  · have hJ : b ≤ |x - (round x : ℝ)| := by
      rcases hxJ with ⟨n, rfl⟩ | hJ
      · exfalso
        apply hfl
        have hn : 0 ≤ n := by
          have : (0 : ℝ) < n := by linarith
          exact_mod_cast this.le
        lift n to ℕ using hn
        simp
      · exact hJ
    have : Real.log x / (T * |x - (round x : ℝ)|) ≤ Real.log x / (T * b) :=
      div_le_div_of_nonneg_left hL0.le (by positivity) (mul_le_mul_of_nonneg_left hJ hT.le)
    have : 0 ≤ 1 / T := by positivity
    linarith

/-- The half-endpoint term is at most a constant times `log x / x`. -/
private theorem heckeLogDerivPolynomial_normTwist_half (χ : U[F])
    (hcoef : ∀ n : ℕ, ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n‖ ≤
      ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖)
    {C₃ : ℝ} (hC₃ : 0 < C₃) (hlog : ∀ n : ℕ,
      ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖ ≤ C₃ * Real.log n)
    {s : ℂ} (hs : s.re = 1) {x : ℝ} (hx : 1 < x) :
    ‖(if (⌊x⌋₊ : ℝ) = x then
      LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s ⌊x⌋₊ / 2 else 0)‖ ≤
      C₃ * Real.log x / x := by
  have hx0 : 0 < x := by linarith
  split_ifs with hfl
  · have hn0 : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr hx.le).ne'
    rw [norm_div, LSeries.norm_term_eq, ite_eq_right_iff.mpr (fun h ↦ absurd h hn0), hs,
      Real.rpow_one, hfl]
    have h1 := (hcoef ⌊x⌋₊).trans (hlog ⌊x⌋₊)
    rw [hfl] at h1
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2, div_div]
    calc ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) ⌊x⌋₊‖ / (x * 2)
        ≤ C₃ * Real.log x / (x * 2) := div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ C₃ * Real.log x / x :=
          div_le_div_of_nonneg_left (by have := Real.log_pos hx; positivity) hx0 (by linarith)
  · rw [norm_zero]
    have := Real.log_pos hx
    positivity

/-- The right-hand side of (B.7.1.11) in terms of `σ = √(log x)`, for `c = 1 / log x`. -/
private theorem heckeLogDerivPolynomial_normTwist_perronTerm {x b T C₁ σ I : ℝ} (hx : 1 < x)
    (hb : 0 < b) (hT : 0 < T) (hC₁ : 0 < C₁) (hσ : σ ^ 2 = Real.log x)
    (hinvT : 1 / T ≤ 2 * Real.exp (-σ)) (hI : I ≤ 1 / T + Real.log x / (T * b)) :
    C₁ * (x ^ (1 / Real.log x) / (T * (1 / Real.log x)) + Real.log x ^ 2 / T + I) ≤
      2 * C₁ * (Real.exp 1 + 1 / b + 1) * ((σ ^ 4 + σ ^ 2 + 1) * Real.exp (-σ)) := by
  have hL0 : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have hxc : x ^ (1 / Real.log x) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hx0, mul_one_div_cancel hL0.ne']
  rw [hxc]
  have hsum : Real.exp 1 / (T * (1 / Real.log x)) + Real.log x ^ 2 / T +
      (1 / T + Real.log x / (T * b)) =
      (Real.exp 1 * σ ^ 2 + σ ^ 4 + 1 + σ ^ 2 / b) * (1 / T) := by
    rw [← hσ]
    field_simp
    ring
  have hpoly : Real.exp 1 * σ ^ 2 + σ ^ 4 + 1 + σ ^ 2 / b ≤
      (Real.exp 1 + 1 / b + 1) * (σ ^ 4 + σ ^ 2 + 1) := by
    have he := Real.exp_pos 1
    have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
    have hσ4 : 0 ≤ σ ^ 4 := by positivity
    have hb1 : 0 ≤ 1 / b := by positivity
    rw [div_eq_mul_one_div (σ ^ 2) b]
    nlinarith [mul_nonneg he.le hσ4, mul_nonneg hb1 hσ4, mul_nonneg hb1 hσ2]
  have hP0 : 0 ≤ Real.exp 1 * σ ^ 2 + σ ^ 4 + 1 + σ ^ 2 / b := by positivity
  calc C₁ * (Real.exp 1 / (T * (1 / Real.log x)) + Real.log x ^ 2 / T + I)
      ≤ C₁ * (Real.exp 1 / (T * (1 / Real.log x)) + Real.log x ^ 2 / T +
          (1 / T + Real.log x / (T * b))) := by gcongr
    _ = C₁ * ((Real.exp 1 * σ ^ 2 + σ ^ 4 + 1 + σ ^ 2 / b) * (1 / T)) := by rw [hsum]
    _ ≤ C₁ * ((Real.exp 1 + 1 / b + 1) * (σ ^ 4 + σ ^ 2 + 1) * (2 * Real.exp (-σ))) := by
        gcongr
    _ = _ := by ring

/-- The contour terms of (B.7.1.12)–(B.7.1.14) in terms of `σ = √(log x)`, for `c = 1 / log x`
and heights `3 ≤ h ≤ e^σ`. -/
private theorem heckeLogDerivPolynomial_normTwist_contourTerm {x σ T h B α A : ℝ} (hx : 1 < x)
    (hσ : σ ^ 2 = Real.log x) (hσ1 : 1 ≤ σ) (hσB : |Real.log B| ≤ σ) (hB : 0 < B)
    (hT : 0 < T) (hh3 : 3 * B > 1) (hh : 3 ≤ h) (hhe : h ≤ Real.exp σ)
    (hαA : 0 < α * A) :
    x ^ (1 / Real.log x) * Real.log h ^ 2 / (T * Real.log x) ≤ Real.exp 1 * (1 / T) ∧
      x ^ (-(α * A / Real.log (B * h))) * Real.log h ^ 3 ≤
        σ ^ 3 * Real.exp (-(α * A / 2 * σ)) := by
  have hL0 : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have hσ0 : 0 < σ := by linarith
  have hlogh0 : 0 ≤ Real.log h := Real.log_nonneg (by linarith)
  have hloghσ : Real.log h ≤ σ := by
    rw [← Real.log_exp σ]; exact Real.log_le_log (by linarith) hhe
  constructor
  · rw [Real.rpow_def_of_pos hx0, mul_one_div_cancel hL0.ne', ← hσ]
    rw [show Real.exp 1 * Real.log h ^ 2 / (T * σ ^ 2) =
      Real.exp 1 * (1 / T) * (Real.log h ^ 2 / σ ^ 2) by field_simp]
    have hq : Real.log h ^ 2 / σ ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ hlogh0 hloghσ 2
    have h0 : 0 ≤ Real.exp 1 * (1 / T) := by positivity
    exact (mul_le_mul_of_nonneg_left hq h0).trans (le_of_eq (mul_one _))
  · have hlogBh : 0 < Real.log (B * h) := Real.log_pos (by nlinarith)
    have hlogBhσ : Real.log (B * h) ≤ 2 * σ := by
      rw [Real.log_mul hB.ne' (by linarith)]
      linarith [le_abs_self (Real.log B)]
    have h1 : x ^ (-(α * A / Real.log (B * h))) ≤ Real.exp (-(α * A / 2 * σ)) := by
      rw [Real.rpow_def_of_pos hx0, Real.exp_le_exp]
      have hδ : α * A / (2 * σ) ≤ α * A / Real.log (B * h) :=
        div_le_div_of_nonneg_left hαA.le hlogBh hlogBhσ
      have hL' : Real.log x * (α * A / (2 * σ)) = α * A / 2 * σ := by
        rw [← hσ]; field_simp
      nlinarith
    have h2 : Real.log h ^ 3 ≤ σ ^ 3 := pow_le_pow_left₀ hlogh0 hloghσ 3
    calc x ^ (-(α * A / Real.log (B * h))) * Real.log h ^ 3
        ≤ Real.exp (-(α * A / 2 * σ)) * σ ^ 3 :=
          mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
      _ = σ ^ 3 * Real.exp (-(α * A / 2 * σ)) := mul_comm _ _

/-- Paper: (B.7.1.11)–(B.7.1.15), pp. 646–648, with `c = 1 / log x` and the height
`T = e^σ - M - 3`, `σ = √(log x)`. Given Perron's estimate for an integrand `G` and the contour
estimate comparing its truncated integral with `R`, the cutoff polynomial minus `R` is bounded,
uniformly for `|Im s - t₀| ≤ M` on the 1-line and for cuts in `J_b`, by a function of `x`
tending to zero. -/
private theorem heckeLogDerivPolynomial_normTwist_mainAbs (χ : U[F]) (G : ℂ → ℂ)
    (R : ℝ → ℂ → ℂ) (t₀ : ℝ) {C₁ C₂ C₃ A B α T₀ M b : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hC₃ : 0 < C₃) (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1) (hT₀ : 2 ≤ T₀)
    (hM : 0 ≤ M) (hb : 0 < b)
    (hcoef : ∀ n : ℕ, ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n‖ ≤
      ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖)
    (hlog : ∀ n : ℕ,
      ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖ ≤ C₃ * Real.log n)
    (hper : ∀ (s : ℂ) (x c T : ℝ), s ∈ oneLine → 1 < x → 0 < c → 1 ≤ T →
      ‖heckeLogDerivPolynomial χ x s - truncatedPerronIntegral G s x c T -
        (if (⌊x⌋₊ : ℝ) = x then
          LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s ⌊x⌋₊ / 2
         else 0)‖ ≤
        C₁ * (x ^ c / (T * c) + (Real.log x) ^ 2 / T +
          (if (⌊x⌋₊ : ℝ) = x then c * Real.log x / (T * x)
           else Real.log x / (T * |x - (round x : ℝ)|))))
    (hcore : ∀ (s : ℂ) (x c T : ℝ), s ∈ oneLine → 1 < x → 0 < c → T₀ + |s.im - t₀| ≤ T →
      ‖truncatedPerronIntegral G s x c T - R x s‖ ≤
        C₂ * (x ^ c * (Real.log (T + |s.im - t₀| + 3)) ^ 2 / (T * Real.log x) +
          x ^ (-(α * A / Real.log (B * (T + |s.im - t₀| + 3)))) *
            (Real.log (T + |s.im - t₀| + 3)) ^ 3)) :
    ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧ ∀ᶠ x in atTop, x ∈ perronCutoffSet b →
      ∀ s ∈ oneLine, |s.im - t₀| ≤ M → ‖heckeLogDerivPolynomial χ x s - R x s‖ ≤ g x := by
  have hαA : 0 < α * A := mul_pos hα.1 hA
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ,
      K₁ = 2 * C₁ * (Real.exp 1 + 1 / b + 1) + C₃ + 2 * Real.exp 1 * C₂ := ⟨_, rfl⟩
  have hσ : Tendsto (fun x : ℝ ↦ √(Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  refine ⟨fun x ↦ K₁ * ((√(Real.log x) ^ 4 + √(Real.log x) ^ 2 + 1) *
      Real.exp (-√(Real.log x))) + C₂ * (√(Real.log x) ^ 3 *
        Real.exp (-(α * A / 2 * √(Real.log x)))),
    (heckeLogDerivPolynomial_normTwist_decay K₁ C₂ (α * A / 2) (by positivity)).comp hσ, ?_⟩
  have hB0 : 0 < B := by linarith
  filter_upwards [hσ.eventually_ge_atTop
      (max (max 1 |Real.log B|) (Real.log (2 * (T₀ + M + 3)))), eventually_gt_atTop 1]
    with x hσx hx1 hxJ s hs hsM
  obtain ⟨σ, hσ_def⟩ : ∃ σ : ℝ, σ = √(Real.log x) := ⟨_, rfl⟩
  rw [← hσ_def] at hσx ⊢
  have hL0 : 0 < Real.log x := Real.log_pos hx1
  have hLσ : σ ^ 2 = Real.log x := by rw [hσ_def]; exact Real.sq_sqrt hL0.le
  have hσ1 : 1 ≤ σ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hσx)
  have hσB : |Real.log B| ≤ σ := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hσx)
  have hσT : Real.log (2 * (T₀ + M + 3)) ≤ σ := le_trans (le_max_right _ _) hσx
  have heσ : 2 * (T₀ + M + 3) ≤ Real.exp σ := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 * (T₀ + M + 3) by positivity)]
    exact Real.exp_le_exp.mpr hσT
  have hx0 : 0 < x := by linarith
  obtain ⟨T, hT_def⟩ : ∃ T : ℝ, T = Real.exp σ - M - 3 := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by rw [hT_def]; linarith
  have hT0 : 0 < T := by linarith
  have hTT : T₀ + |s.im - t₀| ≤ T := by rw [hT_def]; linarith
  have hinvT : 1 / T ≤ 2 * Real.exp (-σ) := by
    rw [Real.exp_neg, div_le_iff₀ hT0]
    have := Real.exp_pos σ
    field_simp
    rw [hT_def]
    linarith
  have hc : 0 < 1 / Real.log x := by positivity
  have hs1 : s.re = 1 := hs
  -- The three error terms.
  have hP := hper s x (1 / Real.log x) T hs hx1 hc hT1
  have hK := hcore s x (1 / Real.log x) T hs hx1 hc hTT
  have hHb := heckeLogDerivPolynomial_normTwist_half χ hcoef hC₃ hlog hs1 hx1
  have hE1 := hP.trans (heckeLogDerivPolynomial_normTwist_perronTerm hx1 hb hT0 hC₁ hLσ hinvT
    (heckeLogDerivPolynomial_normTwist_int hx1 hb hT0 hxJ))
  have hh3 : 3 ≤ T + |s.im - t₀| + 3 := by linarith [abs_nonneg (s.im - t₀)]
  have hhe : T + |s.im - t₀| + 3 ≤ Real.exp σ := by rw [hT_def]; linarith
  obtain ⟨hc1, hc2⟩ := heckeLogDerivPolynomial_normTwist_contourTerm hx1 hLσ hσ1 hσB hB0 hT0
    (by linarith) hh3 hhe hαA
  have hK' := hK.trans (mul_le_mul_of_nonneg_left (add_le_add
    (hc1.trans (mul_le_mul_of_nonneg_left hinvT (Real.exp_pos 1).le)) hc2) hC₂.le)
  -- The half term, in terms of `σ`.
  have hHσ : C₃ * Real.log x / x ≤ C₃ * ((σ ^ 4 + σ ^ 2 + 1) * Real.exp (-σ)) := by
    rw [show x = Real.exp (Real.log x) from (Real.exp_log hx0).symm, Real.log_exp, ← hLσ,
      div_eq_mul_inv, ← Real.exp_neg, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC₃.le
    have hss : σ ≤ σ ^ 2 := by rw [sq]; exact le_mul_of_one_le_right (by linarith) hσ1
    have h1 : Real.exp (-σ ^ 2) ≤ Real.exp (-σ) := Real.exp_le_exp.mpr (neg_le_neg hss)
    have h2 : σ ^ 2 ≤ σ ^ 4 + σ ^ 2 + 1 := by
      have := pow_nonneg (by linarith : (0 : ℝ) ≤ σ) 4
      linarith
    exact mul_le_mul h2 h1 (Real.exp_pos _).le (by positivity)
  -- Assemble.
  set E₁ := heckeLogDerivPolynomial χ x s - truncatedPerronIntegral G s x (1 / Real.log x) T -
    (if (⌊x⌋₊ : ℝ) = x then
      LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s ⌊x⌋₊ / 2 else 0)
  set E₂ := truncatedPerronIntegral G s x (1 / Real.log x) T - R x s
  set H := (if (⌊x⌋₊ : ℝ) = x then
      LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s ⌊x⌋₊ / 2 else 0)
  have hsplit : heckeLogDerivPolynomial χ x s - R x s = E₁ + H + E₂ := by
    simp only [E₁, E₂]
    ring
  rw [hsplit]
  refine (norm_add₃_le).trans ?_
  have hexp := Real.exp_pos (-σ)
  have hone : 1 ≤ σ ^ 4 + σ ^ 2 + 1 := le_add_of_nonneg_left (by positivity)
  have hQ : Real.exp (-σ) ≤ (σ ^ 4 + σ ^ 2 + 1) * Real.exp (-σ) :=
    le_mul_of_one_le_left hexp.le hone
  have h2e : C₂ * (Real.exp 1 * (2 * Real.exp (-σ))) ≤
      2 * Real.exp 1 * C₂ * ((σ ^ 4 + σ ^ 2 + 1) * Real.exp (-σ)) := by
    rw [show C₂ * (Real.exp 1 * (2 * Real.exp (-σ))) =
      2 * Real.exp 1 * C₂ * Real.exp (-σ) by ring]
    exact mul_le_mul_of_nonneg_left hQ (by positivity)
  rw [mul_add] at hK'
  have hH := hHb.trans hHσ
  rw [hK₁, add_mul, add_mul]
  linarith

/-- The estimate of `heckeLogDerivPolynomial_normTwist_mainAbs` for the character
`|·|^(-it₀)`, whose truncated Perron integral is compared with the residues at `0` and at the
pole by `heckeLogDerivPolynomial_normTwist_core`. -/
private theorem heckeLogDerivPolynomial_normTwist_main (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) {M b : ℝ} (hM : 0 ≤ M) (hb : 0 < b) :
    ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧ ∀ᶠ x in atTop, x ∈ perronCutoffSet b →
      ∀ s ∈ oneLine, |s.im - t₀| ≤ M →
        ‖heckeLogDerivPolynomial χ x s +
          logDeriv (toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ) (s - Complex.I * t₀) -
          dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0 (1 + Complex.I * t₀ - s)‖ ≤ g x := by
  obtain ⟨C₁, hC₁, hper⟩ := heckeLogDerivPolynomial_perron_error χ t₀ hχ Z hZ hSeries
  obtain ⟨A, B, α, C₂, T₀, hA, hB, hα, -, hC₂, hT₀, hcore⟩ :=
    heckeLogDerivPolynomial_normTwist_core Z hZ hSeries
  obtain ⟨C₃, hC₃, hlog⟩ := heckeLogDerivPolynomial_perron_error_coeff_log (F := F)
  obtain ⟨g, hg, hev⟩ := heckeLogDerivPolynomial_normTwist_mainAbs χ _
    (fun x s ↦ dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0 (1 + Complex.I * t₀ - s) -
      logDeriv (toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ) (s - Complex.I * t₀))
    t₀ hC₁ hC₂ hC₃ hA hB hα hT₀ hM hb (heckeLogDerivPolynomial_perron_error_coeff_le χ t₀ hχ)
    hlog hper (fun s x c T hs hx hc hT ↦ hcore s t₀ x c T hs hx hc hT)
  refine ⟨g, hg, hev.mono fun x hx hJ s hs hsM ↦ ?_⟩
  have h := hx hJ s hs hsM
  rw [show heckeLogDerivPolynomial χ x s -
      (dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0 (1 + Complex.I * t₀ - s) -
        logDeriv (toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ) (s - Complex.I * t₀)) =
      heckeLogDerivPolynomial χ x s +
        logDeriv (toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ) (s - Complex.I * t₀) -
        dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0 (1 + Complex.I * t₀ - s) by ring] at h
  exact h

/-- Paper: Theorem B.7.1.2(1), Equation (B.7.1.8), p. 645. For the character
`|·|^(-it₀)`, the cutoff polynomial on the 1-line is the negative shifted
Dedekind zeta logarithmic derivative plus the oscillatory pole term and an
analytic remainder. The remainder tends uniformly to zero on compact subsets
away from the pole along `J_b`. -/
theorem heckeLogDerivPolynomial_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    (K : Set ℂ) (hK : IsCompact K) (hKline : K ⊆ oneLine)
    (hpole : (1 + Complex.I * t₀ : ℂ) ∉ K) {b : ℝ} (hb : 0 < b) :
    ∃ error : ℝ → ℂ → ℂ,
      (∀ x > 1, AnalyticOnNhd ℂ (error x) oneLine ∧
        ∀ s ∈ oneLine, s ≠ 1 + Complex.I * t₀ →
          heckeLogDerivPolynomial χ x s = -logDeriv Z (s - Complex.I * t₀) +
            (x : ℂ) ^ (1 + Complex.I * t₀ - s) / (1 + Complex.I * t₀ - s) + error x s) ∧
      TendstoUniformlyOn error (fun _ ↦ 0) (atTop ⊓ 𝓟 (perronCutoffSet b)) K := by
  classical
  obtain ⟨hord, hanZ⟩ := heckeLogDerivPolynomial_normTwist_zeta Z hZ hSeries
  obtain ⟨hWan, hW1, hWlog⟩ := heckeLogDerivPolynomial_normTwist_W Z hZ hord hanZ
  have hline := heckeLogDerivPolynomial_normTwist_line Z hZ hSeries
  set W := toMeromorphicNFOn (fun v ↦ (v - 1) * Z v) univ with hW
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨g, hg, hbound⟩ := heckeLogDerivPolynomial_normTwist_main χ t₀ hχ Z hZ hSeries
    (le_max_left 0 (R + |t₀|)) hb
  refine ⟨fun x s ↦ heckeLogDerivPolynomial χ x s + logDeriv W (s - Complex.I * t₀) -
    dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0 (1 + Complex.I * t₀ - s), fun x hx ↦ ⟨?_, ?_⟩, ?_⟩
  · intro s hs
    have hs1 : s.re = 1 := hs
    obtain ⟨hWa, hWne, -⟩ := hline (s - Complex.I * t₀) (by simp [hs1])
    have hf1 : AnalyticAt ℂ (fun s : ℂ ↦ s - Complex.I * t₀) s :=
      analyticAt_id.sub analyticAt_const
    have hf2 : AnalyticAt ℂ (fun s : ℂ ↦ 1 + Complex.I * t₀ - s) s :=
      analyticAt_const.sub analyticAt_id
    have hΛ : AnalyticAt ℂ (fun s ↦ logDeriv W (s - Complex.I * t₀)) s := by
      exact AnalyticAt.comp (f := fun s : ℂ ↦ s - Complex.I * t₀) (x := s)
        (hWa.deriv.div hWa hWne) hf1
    have hD : AnalyticAt ℂ
        (fun s ↦ dslope (fun u : ℂ ↦ (x : ℂ) ^ u) 0 (1 + Complex.I * t₀ - s)) s := by
      exact AnalyticAt.comp (f := fun s : ℂ ↦ 1 + Complex.I * t₀ - s) (x := s)
        (heckeLogDerivPolynomial_normTwist_dslope (by linarith : (0 : ℝ) < x)
          (1 + Complex.I * t₀ - s)) hf2
    exact ((heckeLogDerivPolynomial_normTwist_poly χ x s).add hΛ).sub hD
  · intro s hs hsp
    have hs1 : s.re = 1 := hs
    have hv1 : s - Complex.I * t₀ ≠ 1 := fun h ↦ hsp (by linear_combination h)
    have hρ : 1 + Complex.I * t₀ - s ≠ 0 := fun h ↦ hsp (by linear_combination -h)
    obtain ⟨-, -, hZne⟩ := hline (s - Complex.I * t₀) (by simp [hs1])
    have hre : 0 < (s - Complex.I * t₀).re := by simp [hs1]
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ) < x by linarith).ne'
    have hsub : s - Complex.I * t₀ - 1 ≠ 0 := sub_ne_zero.mpr hv1
    beta_reduce
    rw [(hWlog _ hre hv1 (hZne hv1)).2, dslope_of_ne _ hρ, slope_def_field, sub_zero,
      Complex.cpow_zero]
    field_simp
    ring
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [eventually_inf_principal]
    filter_upwards [hbound, hg.eventually (gt_mem_nhds hε)] with x hx hgx hxJ s hsK
    rw [dist_zero_left]
    refine (hx hxJ s (hKline hsK) ?_).trans_lt hgx
    have h1 := Complex.abs_im_le_norm s
    have h2 := hR s hsK
    have h3 := abs_sub (s.im) t₀
    exact le_max_of_le_right (by linarith)

/-- Paper: Theorem B.7.1.2(1), Equation (B.7.1.9), p. 645. At the pole
ordinate, the cutoff polynomial differs from the logarithm of the cutoff by
a bounded quantity as the real cutoff tends to infinity.
Deviation: The implied constant is for the fixed number field. The double-pole
residue on p. 648 involves the field's Euler–Kronecker constant. -/
theorem heckeLogDerivPolynomial_at_pole (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    (fun x : ℝ ↦ heckeLogDerivPolynomial χ x (1 + Complex.I * t₀) - (Real.log x : ℂ))
      =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  classical
  obtain ⟨Z₀, hZ, hS⟩ := finiteHeckeL_exists_continuation (1 : U[F])
  have hSeries : ∀ s : halfPlane, Z₀ s = dedekindZeta F s :=
    fun s ↦ (hS s).trans (heckeLogDerivPolynomial_perron_error_zeta s)
  set W := toMeromorphicNFOn (fun v ↦ (v - 1) * Z₀ v) univ with hW
  obtain ⟨g, hg, hbound⟩ := heckeLogDerivPolynomial_normTwist_main χ t₀ hχ Z₀ hZ hSeries (M := 0) le_rfl
    (b := 1 / 2) (by norm_num)
  set p : ℂ := 1 + Complex.I * t₀ with hp
  have hpl : p ∈ oneLine := by simp [hp]
  -- At integers the remainder at the pole ordinate is bounded.
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hbound.and (hg.eventually (gt_mem_nhds one_pos)))
  have hint (n : ℕ) (hn : N ≤ (n : ℝ)) (hn1 : 1 < n) :
      ‖heckeLogDerivPolynomial χ n p - (Real.log n : ℂ)‖ ≤ 1 + ‖logDeriv W 1‖ := by
    obtain ⟨hb, hg1⟩ := hN n hn
    have hJ : (n : ℝ) ∈ perronCutoffSet (1 / 2) := by
      have := (perronCutoffSet_integer_half_integer (b := 1 / 2) (by norm_num) (n : ℤ)).1
      simpa using this
    have h := hb hJ p hpl (by simp [hp])
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hx0 : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hv : p - Complex.I * t₀ = 1 := by rw [hp]; ring
    have hρ : 1 + Complex.I * t₀ - p = 0 := by rw [hp]; ring
    have hder : dslope (fun u : ℂ ↦ ((n : ℝ) : ℂ) ^ u) 0 0 = (Real.log n : ℂ) := by
      rw [dslope_same, (Complex.hasStrictDerivAt_const_cpow (Or.inl hx0)).hasDerivAt.deriv,
        Complex.cpow_zero, one_mul, Complex.ofReal_log hn0.le]
    rw [hv, hρ, hder] at h
    have hsplit : heckeLogDerivPolynomial χ n p - (Real.log n : ℂ) =
        (heckeLogDerivPolynomial χ n p + logDeriv W 1 - (Real.log n : ℂ)) - logDeriv W 1 := by
      ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    linarith
  -- Real cuts reduce to the integer below.
  refine Asymptotics.IsBigO.of_bound (1 + ‖logDeriv W 1‖ + Real.log 2) ?_
  filter_upwards [eventually_ge_atTop (max N 0 + 2)] with x hx
  set n := ⌊x⌋₊ with hn
  have hN0 := le_max_left N 0
  have hN1 := le_max_right N 0
  have hx0 : 0 ≤ x := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hNn : N ≤ (n : ℝ) := by linarith
  have hn1 : 1 < n := by
    have : (1 : ℝ) < n := by linarith
    exact_mod_cast this
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpoly : heckeLogDerivPolynomial χ x p = heckeLogDerivPolynomial χ n p := by
    unfold heckeLogDerivPolynomial
    rw [Nat.floor_natCast]
  have hlog : |Real.log x - Real.log n| ≤ Real.log 2 := by
    have h1 : Real.log n ≤ Real.log x := Real.log_le_log hn0 hnx
    have h2 : Real.log x ≤ Real.log 2 + Real.log n := by
      rw [← Real.log_mul (by norm_num) hn0.ne']
      exact Real.log_le_log (by linarith) (by linarith [(by exact_mod_cast hn1.le :
        (1 : ℝ) ≤ n)])
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hsplit : heckeLogDerivPolynomial χ x p - (Real.log x : ℂ) =
      (heckeLogDerivPolynomial χ n p - (Real.log n : ℂ)) -
        ((Real.log x - Real.log n : ℝ) : ℂ) := by
    rw [hpoly]; push_cast; ring
  rw [hsplit, norm_one, mul_one]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  linarith [hint n hNn hn1]

/-- A unitary character does not increase the coefficients in norm. -/
private theorem heckeLogDerivPolynomial_of_nontrivial_on_normOne_coeff_le (χ : U[F]) (n : ℕ) :
    ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n‖ ≤
      ‖heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n‖ := by
  classical
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset fun _ h ↦ h.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} := Fintype.ofFinite _
  have h0 : 0 ≤ ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}, idealVonMangoldt I.val :=
    finsum_nonneg fun I ↦ heckeLogDerivPolynomial_perron_error_idealVonMangoldt_nonneg I.val
  rw [heckeLogDerivPolynomial_perron_error_coeff_real (F := F) n, Complex.norm_real,
    Real.norm_of_nonneg h0, heckeLogDerivCoefficient, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ ↦ ?_)
  have hΛ := heckeLogDerivPolynomial_perron_error_idealVonMangoldt_nonneg I.val
  by_cases h : ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧
      I.val = v.asIdeal ^ k
  · obtain ⟨v, k, hk, hI⟩ := h
    rw [heckeIdealVonMangoldt, hI, heckeIdealValue_prime_pow _ v hk, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (hI ▸ hΛ)]
    refine mul_le_of_le_one_left (hI ▸ hΛ) ?_
    split_ifs
    · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow]
    · simp
  · have h0 : idealVonMangoldt I.val = 0 := by
      unfold idealVonMangoldt
      exact dite_eq_right_iff.mpr fun h' ↦ absurd h' h
    rw [heckeIdealVonMangoldt, h0]
    simp

/-- To the right of one, the coefficients of the cutoff polynomial are the Dirichlet
coefficients of the negative logarithmic derivative of the finite Hecke L-function. -/
private theorem heckeLogDerivPolynomial_of_nontrivial_on_normOne_hasSum (χ : U[F]) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) (w : ℂ) (hw : 1 < w.re) :
    LSeriesHasSum (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) w (-logDeriv L w) := by
  classical
  have hf := finiteHeckeL_negLogDeriv_hasSum_ideals χ L hL hSeries ⟨w, hw⟩
  have hg := hf.tsum_fiberwise (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦ I.val.absNorm)
  refine hg.congr_fun fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have : IsEmpty ↑((fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦ I.val.absNorm) ⁻¹' {0}) :=
      ⟨fun b ↦ b.val.property (Ideal.absNorm_eq_zero_iff.mp b.property)⟩
    rw [tsum_empty, LSeries.term_zero]
  · let S := {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}
    have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n}.Finite :=
      (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset fun _ h ↦ h.2
    have : Finite S := hfin.to_subtype
    have : Fintype S := Fintype.ofFinite _
    let e : ↑((fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦ I.val.absNorm) ⁻¹' {n}) ≃ S :=
      { toFun := fun b ↦ ⟨b.val.val, b.val.property, b.property⟩
        invFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, I.property.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [← e.symm.tsum_eq, tsum_fintype, LSeries.term_of_ne_zero hn, heckeLogDerivCoefficient,
      finsum_eq_sum_of_fintype, Finset.sum_div]
    refine Finset.sum_congr rfl fun I _ ↦ ?_
    change _ = _ / ((I.val.absNorm : ℕ) : ℂ) ^ w
    rw [I.property.2]
    rfl

/-- For a character nontrivial on the norm-one subgroup, the finite L-function has no pole
to the right of the imaginary axis. -/
private theorem heckeLogDerivPolynomial_of_nontrivial_on_normOne_analytic (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (v : ℂ) (hv : 0 < v.re) : AnalyticAt ℂ L v := by
  have hΓ (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ (heckeGammaFactor χ) s :=
    DifferentiableOn.analyticAt (s := Complex.re ⁻¹' Ioi 0)
      (fun w hw ↦ (differentiableAt_heckeGammaFactor_of_re_pos χ hw).differentiableWithinAt)
      ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hs)
  let M : ℂ → ℂ := fun w ↦ heckeGammaFactor χ w * L w
  have hM : MeromorphicOn M univ := fun x _ ↦
    (meromorphic_heckeGammaFactor χ x).mul (hL (mem_univ x)).meromorphicAt
  have hΛs : ∀ s : halfPlane, toMeromorphicNFOn M univ s = completedHeckeL χ s := by
    intro s
    have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
    have hMan : AnalyticAt ℂ M s :=
      (hΓ s hs).mul (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries s).1
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr hMan.meromorphicNFAt]
    simp [M, hSeries s, completedHeckeL, finiteHeckeL]
  have hD := completedHeckeL_continuation_entire χ (toMeromorphicNFOn M univ)
    (meromorphicNFOn_toMeromorphicNFOn _ _) hΛs hχ
  have h0 : 0 ≤ meromorphicOrderAt L v := by
    have hord : meromorphicOrderAt (toMeromorphicNFOn M univ) v = meromorphicOrderAt L v := by
      rw [meromorphicOrderAt_toMeromorphicNFOn hM (mem_univ _)]
      exact meromorphicOrderAt_mul_of_ne_zero (hΓ v hv) (heckeGammaFactor_ne_zero_of_re_pos χ hv)
    rw [← hord]
    exact (hD.analyticAt v).meromorphicOrderAt_nonneg
  exact (hL (mem_univ v)).meromorphicOrderAt_nonneg_iff_analyticAt.mp h0

/-- Admissible constants for the zero-free region of the finite L-function. -/
private theorem heckeLogDerivPolynomial_of_nontrivial_on_normOne_region (χ : U[F]) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ A B : ℝ, 0 < A ∧ 1 / 3 < B ∧ A ≤ Real.log (B * 3) / 2 ∧
      (∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re → meromorphicOrderAt L z ≤ 0) := by
  obtain ⟨A₀, hA₀, hF⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B, hB, hzf⟩ := hF F χ
  have hzf' := hzf L hL hSeries
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = (Module.finrank ℚ F : ℝ) ^ 4 := ⟨_, rfl⟩
  rw [← hd_def] at hzf'
  have hd : 0 < d := by
    rw [hd_def]
    have : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos
    positivity
  have hl3 : 0 < Real.log (B * 3) := Real.log_pos (by linarith)
  obtain ⟨A, hA_def⟩ : ∃ A : ℝ, A = min (A₀ / d) (Real.log (B * 3) / 2) := ⟨_, rfl⟩
  have hA : 0 < A := hA_def ▸ lt_min (div_pos hA₀ hd) (by linarith)
  have hAd : A * d ≤ A₀ := by
    have h := hA_def ▸ min_le_left (A₀ / d) (Real.log (B * 3) / 2)
    calc A * d ≤ A₀ / d * d := mul_le_mul_of_nonneg_right h hd.le
      _ = A₀ := div_mul_cancel₀ _ hd.ne'
  refine ⟨A, B, hA, hB, hA_def ▸ min_le_right _ _, fun z hz ↦ hzf' z ?_⟩
  have hlz : 0 < Real.log (B * (|z.im| + 3)) :=
    Real.log_pos (by nlinarith [abs_nonneg z.im])
  have hle : A / Real.log (B * (|z.im| + 3)) ≤
      A₀ / (d * Real.log (B * (|z.im| + 3))) := by
    rw [div_le_div_iff₀ hlz (by positivity)]
    nlinarith
  linarith

/-- In the narrowed zero-free region the logarithmic derivative of the finite L-function is
bounded by a squared logarithm at large heights. -/
private theorem heckeLogDerivPolynomial_of_nontrivial_on_normOne_logDeriv (χ : U[F]) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    {A B α : ℝ} (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1)
    (hwidth : A ≤ Real.log (B * 3) / 2)
    (hdisc : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0)
    (hzero : ∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re →
      meromorphicOrderAt L z ≤ 0) :
    ∃ C T₁ : ℝ, 0 < C ∧ ∀ z : ℂ, T₁ ≤ |z.im| →
      1 - α * (A / Real.log (B * (|z.im| + 3))) ≤ z.re →
      ‖logDeriv L z‖ ≤ C * (Real.log |z.im|) ^ 2 := by
  obtain ⟨C, hC, hmain⟩ := finiteHeckeL_logDeriv_isBigO_of_zeroFree χ L Z hL hSeries
    hZ hZSeries α hα.1 hα.2 hdisc
  obtain ⟨hmaps, hdiff, hanti, hderiv, hO⟩ :=
    dedekindZeta_perron_left_bound_width A B hA hB hwidth
  obtain ⟨-, hbig⟩ := hmain (fun t : ℝ ↦ A / Real.log (B * (t + 3))) hmaps hdiff hanti hderiv
    hO hzero
  rw [Asymptotics.isBigOWith_iff, eventually_inf_principal, eventually_comap,
    eventually_atTop] at hbig
  obtain ⟨T₁, hT₁⟩ := hbig
  refine ⟨C, T₁, hC, fun z hz hre ↦ ?_⟩
  have h := hT₁ |z.im| hz z rfl hre
  rwa [Real.norm_of_nonneg (sq_nonneg _)] at h

/-- Paper: (B.7.1.17), p. 648, and the estimates (B.7.1.12)–(B.7.1.14). The integrand has only
the pole at `0`, so the truncated Perron integral of `-L'/L` is `-L'/L(s)` up to the integrals
over the left and horizontal edges of the rectangle. -/
private theorem heckeLogDerivPolynomial_of_nontrivial_on_normOne_core (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ A B α C T₀ : ℝ, 0 < A ∧ 1 / 3 < B ∧ α ∈ Ioo 0 1 ∧ 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (s : ℂ) (x c T : ℝ), s ∈ oneLine → 1 < x → 0 < c → T₀ + |s.im - 0| ≤ T →
        ‖truncatedPerronIntegral (fun w ↦ -logDeriv L w) s x c T - -logDeriv L s‖ ≤
          C * (x ^ c * (Real.log (T + |s.im - 0| + 3)) ^ 2 / (T * Real.log x) +
            x ^ (-(α * A / Real.log (B * (T + |s.im - 0| + 3)))) *
              (Real.log (T + |s.im - 0| + 3)) ^ 3) := by
  obtain ⟨-, -, α, -, -, hα, -, hdisc, -⟩ := heckeLogDerivPolynomial_normTwist_region Z hZ hZSeries
  obtain ⟨A, B, hA, hB, hwidth, hzero⟩ := heckeLogDerivPolynomial_of_nontrivial_on_normOne_region χ L hL hSeries
  obtain ⟨C₁, T₁, hC₁, hbound⟩ :=
    heckeLogDerivPolynomial_of_nontrivial_on_normOne_logDeriv χ L hL hSeries Z hZ hZSeries hA hB hα hwidth hdisc hzero
  obtain ⟨Cl, Tl, hCl, hTl, hleft⟩ :=
    dedekindZeta_perron_left_bound_generic L hL hA hB hα hC₁ hbound
  obtain ⟨Ch, Th, hCh, hTh, hhor⟩ :=
    dedekindZeta_perron_horizontal_bound_generic L hA hB hα hC₁ hbound
  refine ⟨A, B, α, 2 * Ch + Cl, max Tl Th, hA, hB, hα, by positivity,
    le_max_of_le_left hTl, fun s x c T hs hx hc hT ↦ ?_⟩
  have hs1 : s.re = 1 := hs
  have hx0 : 0 < x := by linarith
  have hD : 0 ≤ |s.im - 0| := abs_nonneg _
  have hT2 : 2 ≤ T := by linarith [le_max_left Tl Th]
  have hT0 : 0 < T := by linarith
  set h := T + |s.im - 0| + 3 with hh
  have hB0 : 0 < B := by linarith
  have hlogBh : 0 < Real.log (B * h) := Real.log_pos (by nlinarith)
  set δ := α * A / Real.log (B * h) with hδ
  have hδ0 : 0 < δ := div_pos (mul_pos hα.1 hA) hlogBh
  have hδ1 : δ < 1 := by
    have hlog3 : Real.log (B * 3) ≤ Real.log (B * h) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [hδ, div_lt_one hlogBh]
    nlinarith [hα.2]
  set v₀ := s - Complex.I * ((0 : ℝ) : ℂ) with hv₀
  have hv₀s : v₀ = s := by rw [hv₀]; simp
  -- Analyticity and nonvanishing on the closed rectangle.
  have hgood (u : ℂ) (hu : u ∈ Icc (-δ) c ×ℂ Icc (-T) T) :
      AnalyticAt ℂ L (v₀ + u) ∧ L (v₀ + u) ≠ 0 := by
    have hre : (v₀ + u).re = 1 + u.re := by simp [hv₀s, hs1]
    have hpos : 0 < (v₀ + u).re := by rw [hre]; linarith [hu.1.1]
    have him : |(v₀ + u).im| + 3 ≤ h := by
      have h1 : (v₀ + u).im = (s.im - 0) + u.im := by simp [hv₀s]
      rw [h1]
      have := abs_add_le (s.im - 0) u.im
      have := abs_le.mpr ⟨hu.2.1, hu.2.2⟩
      linarith
    have hlz : 0 < Real.log (B * (|(v₀ + u).im| + 3)) :=
      Real.log_pos (by nlinarith [abs_nonneg (v₀ + u).im])
    have hle : Real.log (B * (|(v₀ + u).im| + 3)) ≤ Real.log (B * h) :=
      Real.log_le_log (by nlinarith [abs_nonneg (v₀ + u).im]) (by nlinarith)
    have hδle : δ < A / Real.log (B * (|(v₀ + u).im| + 3)) := by
      calc δ = α * (A / Real.log (B * h)) := by rw [hδ, mul_div_assoc]
        _ < 1 * (A / Real.log (B * h)) :=
          mul_lt_mul_of_pos_right hα.2 (div_pos hA hlogBh)
        _ ≤ A / Real.log (B * (|(v₀ + u).im| + 3)) := by
          rw [one_mul]; exact div_le_div_of_nonneg_left hA.le hlz hle
    have hLa := heckeLogDerivPolynomial_of_nontrivial_on_normOne_analytic χ hχ L hL hSeries _ hpos
    refine ⟨hLa, (hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp
      (le_antisymm (hzero (v₀ + u) (by rw [hre]; linarith [hu.1.1]))
        hLa.meromorphicOrderAt_nonneg)⟩
  have hrect : (-δ : ℝ) ≤ c := by linarith
  have hrect' : (-T : ℝ) ≤ T := by linarith
  have h0mem : (0 : ℂ) ∈ Ioo (⟨-δ, -T⟩ : ℂ).re (⟨c, T⟩ : ℂ).re ×ℂ
      Ioo (⟨-δ, -T⟩ : ℂ).im (⟨c, T⟩ : ℂ).im := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hg : DifferentiableOn ℂ (fun u ↦ logDeriv L (v₀ + u) * (x : ℂ) ^ u)
      (Icc (⟨-δ, -T⟩ : ℂ).re (⟨c, T⟩ : ℂ).re ×ℂ Icc (⟨-δ, -T⟩ : ℂ).im (⟨c, T⟩ : ℂ).im) := by
    intro u hu
    obtain ⟨hLa, hLne⟩ := hgood u hu
    have hd : DifferentiableAt ℂ (logDeriv L) (v₀ + u) :=
      hLa.deriv.differentiableAt.div hLa.differentiableAt hLne
    exact ((hd.comp u ((differentiableAt_const _).add differentiableAt_id)).mul
      (Complex.hasStrictDerivAt_const_cpow (Or.inl hx0')).hasDerivAt.differentiableAt
      ).differentiableWithinAt
  set G : ℂ → ℂ := fun u ↦ -logDeriv L (v₀ + u) * (x : ℂ) ^ u / u with hG
  have hres' : rectangleIntegral G ⟨-δ, -T⟩ ⟨c, T⟩ =
      2 * (Real.pi : ℂ) * Complex.I * (-logDeriv L v₀) := by
    have h1 : G = fun u ↦ (-1 : ℂ) * (logDeriv L (v₀ + u) * (x : ℂ) ^ u / (u - 0)) := by
      funext u
      simp only [hG, sub_zero]
      ring
    rw [h1, rectangleIntegral_const_mul,
      heckeLogDerivPolynomial_normTwist_cauchy hrect hrect' h0mem hg]
    simp only [add_zero, Complex.cpow_zero, mul_one]
    ring
  have hPer : truncatedPerronIntegral (fun w ↦ -logDeriv L w) s x c T =
      (∫ t in -T..T, G ⟨c, t⟩) / (2 * Real.pi) := by
    unfold truncatedPerronIntegral
    refine congrArg (· / (2 * (Real.pi : ℂ))) (intervalIntegral.integral_congr fun t _ ↦ ?_)
    change -logDeriv L (s + (⟨c, t⟩ : ℂ)) * (x : ℂ) ^ (⟨c, t⟩ : ℂ) /
      (⟨c, t⟩ : ℂ) = -logDeriv L (v₀ + ⟨c, t⟩) * (x : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)
    rw [hv₀s]
  have hedge := heckeLogDerivPolynomial_normTwist_edges G δ c T
  have hEdge (a b : ℝ) (p : ℝ → ℂ) : (∫ u in a..b, G (p u)) =
      -∫ u in a..b, logDeriv L (s - Complex.I * ((0 : ℝ) : ℂ) + p u) *
        (x : ℂ) ^ (p u) / p u := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    ext u
    simp only [hG, hv₀]
    ring
  have hbB := hhor s 0 x c T (-T) hs hx hc (by linarith [le_max_right Tl Th]) (Or.inl rfl)
  have hbT := hhor s 0 x c T T hs hx hc (by linarith [le_max_right Tl Th]) (Or.inr rfl)
  have hbL := hleft s 0 x T hs hx.le (by linarith [le_max_left Tl Th])
  dsimp only at hbB hbT hbL
  rw [← hh, ← hδ] at hbB hbT hbL
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg (by linarith)
  have hlogy (y : ℝ) (hy : |y| = T) :
      Real.log (|s.im - 0 + y| + 3) ^ 2 ≤ Real.log h ^ 2 := by
    have h1 : |s.im - 0 + y| + 3 ≤ h := by
      have := abs_add_le (s.im - 0) y
      rw [hh]; linarith
    have h2 : 0 ≤ Real.log (|s.im - 0 + y| + 3) :=
      Real.log_nonneg (by linarith [abs_nonneg (s.im - 0 + y)])
    exact pow_le_pow_left₀ h2 (Real.log_le_log (by positivity) h1) 2
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hX : 0 ≤ x ^ c * Real.log h ^ 2 / (T * Real.log x) := by positivity
  have hY : 0 ≤ x ^ (-δ) * Real.log h ^ 3 := by positivity
  have hB' : Ch * x ^ c * Real.log (|s.im - 0 + -T| + 3) ^ 2 / (T * Real.log x) ≤
      Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) := by
    rw [show Ch * x ^ c * Real.log (|s.im - 0 + -T| + 3) ^ 2 / (T * Real.log x) =
        (Ch * x ^ c / (T * Real.log x)) * Real.log (|s.im - 0 + -T| + 3) ^ 2 by ring,
      show Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) =
        (Ch * x ^ c / (T * Real.log x)) * Real.log h ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left (hlogy (-T) (by rw [abs_neg, abs_of_pos hT0]))
      (by positivity)
  have hT' : Ch * x ^ c * Real.log (|s.im - 0 + T| + 3) ^ 2 / (T * Real.log x) ≤
      Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) := by
    rw [show Ch * x ^ c * Real.log (|s.im - 0 + T| + 3) ^ 2 / (T * Real.log x) =
        (Ch * x ^ c / (T * Real.log x)) * Real.log (|s.im - 0 + T| + 3) ^ 2 by ring,
      show Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) =
        (Ch * x ^ c / (T * Real.log x)) * Real.log h ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left (hlogy T (abs_of_pos hT0)) (by positivity)
  have eB := hEdge (-δ) c (fun u ↦ ⟨u, -T⟩)
  have eT := hEdge (-δ) c (fun u ↦ ⟨u, T⟩)
  have eL := hEdge (-T) T (fun y ↦ ⟨-δ, y⟩)
  have hBo : ‖∫ u in -δ..c, G ⟨u, -T⟩‖ ≤ Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) := by
    rw [eB, norm_neg]; exact hbB.trans hB'
  have hTp : ‖∫ u in -δ..c, G ⟨u, T⟩‖ ≤ Ch * (x ^ c * Real.log h ^ 2 / (T * Real.log x)) := by
    rw [eT, norm_neg]; exact hbT.trans hT'
  have hLe : ‖∫ y in -T..T, G ⟨-δ, y⟩‖ ≤ Cl * (x ^ (-δ) * Real.log h ^ 3) := by
    rw [eL, norm_neg, ← mul_assoc]; exact hbL
  set Bo := ∫ u in -δ..c, G ⟨u, -T⟩
  set Tp := ∫ u in -δ..c, G ⟨u, T⟩
  set Le := ∫ y in -T..T, G ⟨-δ, y⟩
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have key : ((2 * (Real.pi : ℂ) * Complex.I * (-logDeriv L v₀) - Bo + Tp) / Complex.I + Le) /
      (2 * (Real.pi : ℂ)) - -logDeriv L v₀ =
      ((-Bo + Tp) / Complex.I + Le) / (2 * (Real.pi : ℂ)) := by
    field_simp
    ring
  rw [hPer, hedge, hres', ← hv₀s, key, norm_div]
  have h2pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  rw [h2pi, div_le_iff₀ (by positivity)]
  have hsum : ‖(-Bo + Tp) / Complex.I + Le‖ ≤ ‖Bo‖ + ‖Tp‖ + ‖Le‖ := by
    calc ‖(-Bo + Tp) / Complex.I + Le‖ ≤ ‖(-Bo + Tp) / Complex.I‖ + ‖Le‖ := norm_add_le _ _
      _ = ‖-Bo + Tp‖ + ‖Le‖ := by rw [norm_div, Complex.norm_I, div_one]
      _ ≤ ‖Bo‖ + ‖Tp‖ + ‖Le‖ := by
        have := norm_add_le (-Bo) Tp
        rw [norm_neg] at this
        linarith
  have hpi3 := Real.pi_gt_three
  have hC : 0 ≤ (2 * Ch + Cl) * (x ^ c * Real.log h ^ 2 / (T * Real.log x) +
      x ^ (-δ) * Real.log h ^ 3) := by positivity
  nlinarith [mul_nonneg hCh.le hY, mul_nonneg hCl.le hX]

/-- Paper: Theorem B.7.1.2(2), Equation (B.7.1.10), p. 646. For a character
nontrivial on the norm-one subgroup, the cutoff polynomial on the 1-line is the
negative logarithmic derivative plus an analytic remainder that tends uniformly
to zero on compact subsets along `J_b`.
Deviation: The positive parameter `b` occurring in part (1) is made explicit. -/
theorem heckeLogDerivPolynomial_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℂ) (hK : IsCompact K) (hKline : K ⊆ oneLine) {b : ℝ} (hb : 0 < b) :
    ∃ error : ℝ → ℂ → ℂ,
      (∀ x > 1, AnalyticOnNhd ℂ (error x) oneLine ∧
        ∀ s ∈ oneLine, heckeLogDerivPolynomial χ x s = -logDeriv L s + error x s) ∧
      TendstoUniformlyOn error (fun _ ↦ 0) (atTop ⊓ 𝓟 (perronCutoffSet b)) K := by
  classical
  obtain ⟨Z, hZ, hS⟩ := finiteHeckeL_exists_continuation (1 : U[F])
  have hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s :=
    fun s ↦ (hS s).trans (heckeLogDerivPolynomial_perron_error_zeta s)
  obtain ⟨A₀, B₀, hA₀, hB₀, -, hzero⟩ := heckeLogDerivPolynomial_of_nontrivial_on_normOne_region χ L hL hSeries
  have hline (v : ℂ) (hv : v.re = 1) : AnalyticAt ℂ L v ∧ L v ≠ 0 := by
    have hpos : 0 < v.re := by rw [hv]; norm_num
    have hLa := heckeLogDerivPolynomial_of_nontrivial_on_normOne_analytic χ hχ L hL hSeries v hpos
    have hlz : 0 < Real.log (B₀ * (|v.im| + 3)) :=
      Real.log_pos (by nlinarith [abs_nonneg v.im])
    refine ⟨hLa, (hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp
      (le_antisymm (hzero v (by rw [hv]; linarith [div_pos hA₀ hlz]))
        hLa.meromorphicOrderAt_nonneg)⟩
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨C₁, hC₁, hper⟩ := heckeLogDerivPolynomial_perron_error_generic χ
    (fun w ↦ -logDeriv L w) (heckeLogDerivPolynomial_of_nontrivial_on_normOne_hasSum χ L hL hSeries) (heckeLogDerivPolynomial_of_nontrivial_on_normOne_coeff_le χ) Z hZ hZSeries
  obtain ⟨A, B, α, C₂, T₀, hA, hB, hα, hC₂, hT₀, hcore⟩ :=
    heckeLogDerivPolynomial_of_nontrivial_on_normOne_core χ hχ L hL hSeries Z hZ hZSeries
  obtain ⟨C₃, hC₃, hlog⟩ := heckeLogDerivPolynomial_perron_error_coeff_log (F := F)
  obtain ⟨g, hg, hev⟩ := heckeLogDerivPolynomial_normTwist_mainAbs χ (fun w ↦ -logDeriv L w)
    (fun _ s ↦ -logDeriv L s) 0 hC₁ hC₂ hC₃ hA hB hα hT₀ (le_max_left 0 R) hb (heckeLogDerivPolynomial_of_nontrivial_on_normOne_coeff_le χ)
    hlog hper hcore
  refine ⟨fun x s ↦ heckeLogDerivPolynomial χ x s + logDeriv L s,
    fun x _ ↦ ⟨fun s hs ↦ ?_, fun s _ ↦ by ring⟩, ?_⟩
  · obtain ⟨hLa, hLne⟩ := hline s hs
    have h : AnalyticAt ℂ (logDeriv L) s := hLa.deriv.div hLa hLne
    exact (heckeLogDerivPolynomial_normTwist_poly χ x s).add h
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [eventually_inf_principal]
    filter_upwards [hev, hg.eventually (gt_mem_nhds hε)] with x hx hgx hxJ s hsK
    rw [dist_zero_left]
    have hb' : |s.im - 0| ≤ max 0 R := by
      rw [sub_zero]
      exact le_max_of_le_right ((Complex.abs_im_le_norm s).trans (hR s hsK))
    have h := hx hxJ s (hKline hsK) hb'
    rw [sub_neg_eq_add] at h
    exact h.trans_lt hgx

-- TODO(paper-gap): The uniform limit away from the pole does not justify taking
-- the limit at the pole in (B.7.1.9). The contour there has a double pole.

end RiemannMasullo
