import research.StripZetaRadius
import RiemannMasullo.External.ZetaLab.HardyFirstZero.EulerMaclaurin
import Mathlib.Analysis.Complex.Convex

/-!
# Polynomial growth for the pole-removed zeta function on a fixed strip

The fourth-order Euler–Maclaurin tail converges to the left of the critical
strip. The block proof below adapts Thomas Lince's MIT-licensed
`HardyFirstZero/EulerMaclaurin.lean` in the project's ZetaLab port
(original revision `a401821c9608526425f3d4cf7ff8e59bc37e1c79`, copyright
2026 Thomas Lince, license in `RiemannMasullo/External/ZetaLab/LICENSE`).
Working off the real axis keeps the derivative exponents nonzero.
-/

noncomputable section
open Complex Filter Metric Set MeasureTheory HardyFirstZero
open scoped Topology

namespace MasulloResearch.StripJets

private theorem block_bound {s : ℂ} (hs : -(5/2 : ℝ) < s.re) (hi : s.im ≠ 0) {x : ℝ} (hx : 1 ≤ x) :
    ‖eBlock s x‖ ≤ ‖P4 s‖ * x ^ (-s.re - 4) / 720 := by
  have hs1 : s ≠ 1 := fun h ↦ hi (by simp [h])
  have hx0 : 0 < x := by linarith
  have hpos : ∀ t ∈ Set.uIcc x (x + 1), 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    linarith [ht.1]
  have r0 : (-s : ℂ) ≠ 0 := by
    intro he
    apply hi
    simpa using congrArg Complex.im he
  have r1 : (-s - 1 : ℂ) ≠ 0 := by
    intro he
    apply hi
    simpa using congrArg Complex.im he
  have r2 : (-s - 1 - 1 : ℂ) ≠ 0 := by
    intro he
    apply hi
    simpa using congrArg Complex.im he
  have r3 : (-s - 1 - 1 - 1 : ℂ) ≠ 0 := by
    intro he
    apply hi
    simpa using congrArg Complex.im he
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (-s)
  set g1 : ℝ → ℂ := fun t => -s * (t : ℂ) ^ (-s - 1)
  set g2 : ℝ → ℂ := fun t => -s * (-s - 1) * (t : ℂ) ^ (-s - 1 - 1)
  set g3 : ℝ → ℂ := fun t => -s * (-s - 1) * (-s - 1 - 1) * (t : ℂ) ^ (-s - 1 - 1 - 1)
  set g4 : ℝ → ℂ := fun t =>
    -s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1) * (t : ℂ) ^ (-s - 1 - 1 - 1 - 1)
  have d0 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g (g1 t) t := fun t ht =>
    hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r0
  have d1 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g1 (g2 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r1).const_mul (-s)
    convert this using 1; simp only [g2]; ring
  have d2 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g2 (g3 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r2).const_mul (-s * (-s - 1))
    convert this using 1; simp only [g3]; ring
  have d3 : ∀ t ∈ Set.uIcc x (x + 1), HasDerivAt g3 (g4 t) t := fun t ht => by
    have := (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r3).const_mul
      (-s * (-s - 1) * (-s - 1 - 1))
    convert this using 1; simp only [g4]; ring
  have r4 : (-s - 1 - 1 - 1 - 1 : ℂ) ≠ 0 := by
    intro he
    apply hi
    simpa using congrArg Complex.im he
  have hc4 : ContinuousOn g4 (Set.uIcc x (x + 1)) := fun t ht =>
    ((hasDerivAt_ofReal_cpow_const (hpos t ht).ne' r4).continuousAt.const_mul
      _).continuousWithinAt
  have hM : ∀ t ∈ Set.Icc x (x + 1), ‖g4 t‖ ≤ ‖P4 s‖ * x ^ (-s.re - 4) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    simp only [g4]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hP : ‖-s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1)‖ = ‖P4 s‖ := by
      rw [show -s * (-s - 1) * (-s - 1 - 1) * (-s - 1 - 1 - 1) = P4 s by unfold P4; ring]
    rw [hP]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hre : (-s - 1 - 1 - 1 - 1).re = -s.re - 4 := by simp; ring
    rw [hre]
    exact Real.rpow_le_rpow_of_nonpos hx0 ht.1 (by linarith)
  have hT := corrected_trapezoid d0 d1 d2 d3 hc4 hM
  -- the integral in closed form
  have h0 : (0 : ℝ) ∉ Set.uIcc x (x + 1) := fun h => (lt_irrefl 0) (hpos 0 h)
  have hI : ∫ t in x..x + 1, g t
      = ((((x + 1 : ℝ) : ℂ) ^ (-s + 1) - ((x : ℝ) : ℂ) ^ (-s + 1)) / (-s + 1)) := by
    simp only [g]
    rw [integral_cpow (Or.inr ⟨fun h => hs1 (by linear_combination -h), h0⟩)]
  have hE : eBlock s x
      = (∫ t in x..x + 1, g t) - ((g x + g (x + 1)) / 2 - (g1 (x + 1) - g1 x) / 12) := by
    rw [hI]
    simp only [eBlock, g, g1]
    rw [show (-s + 1 : ℂ) = 1 - s by ring]
    push_cast
    ring
  rw [hE]
  calc _ ≤ ‖P4 s‖ * x ^ (-s.re - 4) / 720 := hT
    _ = _ := rfl

private def weight (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ (-(3/2) : ℝ)

private theorem weight_summable : Summable weight := by
  have h := (Real.summable_nat_rpow.mpr (by norm_num : (-(3/2) : ℝ) < -1))
  change Summable (fun k : ℕ ↦ ((k : ℝ) + 1) ^ (-(3/2) : ℝ))
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun k : ℕ ↦ (k : ℝ) ^ (-(3/2) : ℝ)) 1).mpr h

private theorem block_le_weight {s : ℂ} (hr : -(5/2 : ℝ) < s.re) (hi : s.im ≠ 0) (k : ℕ) :
    ‖eBlock s ((k : ℝ) + 1)‖ ≤ ‖P4 s‖ * weight k := by
  have hk : 1 ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  refine (block_bound hr hi hk).trans ?_
  have h := Real.rpow_le_rpow_of_exponent_le hk (by linarith : -s.re - 4 ≤ -(3/2 : ℝ))
  unfold weight
  nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg (P4 s)),
    mul_nonneg (norm_nonneg (P4 s)) (Real.rpow_nonneg (by positivity : 0 ≤ (k : ℝ) + 1) (-(3/2) : ℝ))]

private def tail (s : ℂ) : ℂ := ∑' k : ℕ, eBlock s ((k : ℝ) + 1)
private def em (s : ℂ) : ℂ := 1 / (s - 1) + 1 / 2 + s / 12 - tail s

private theorem em_eq_zeta {z : ℂ} (hr : -(5/2 : ℝ) < z.re) (hi : z.im ≠ 0) :
    em z = riemannZeta z := by
  let D : Set ℂ := {w | -(5/2 : ℝ) < w.re ∧ 0 < z.im * w.im}
  have hopen : IsOpen D := by
    change IsOpen ({w : ℂ | -(5/2 : ℝ) < w.re} ∩ {w : ℂ | 0 < z.im * w.im})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im))
  have hconv : Convex ℝ D := ((convex_Ioi (-(5/2) : ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioi 0).linear_preimage (z.im • Complex.imCLM.toLinearMap))
  have hni {w : ℂ} (hw : w ∈ D) : w.im ≠ 0 := fun e ↦ (mul_ne_zero_iff.mp hw.2.ne').2 e
  have hn1 {w : ℂ} (hw : w ∈ D) : w ≠ 1 := fun e ↦ hni hw (by simp [e])
  have he : AnalyticOnNhd ℂ em D := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro w hw
    have hpc : Continuous (fun s : ℂ ↦ ‖P4 s‖) := by unfold P4; fun_prop
    let K := ‖P4 w‖ + 1
    let V := D ∩ {s : ℂ | ‖P4 s‖ < K}
    have hop : IsOpen V := hopen.inter (isOpen_lt hpc continuous_const)
    have hwV : w ∈ V := ⟨hw, show ‖P4 w‖ < ‖P4 w‖ + 1 from lt_add_one _⟩
    have ht : DifferentiableOn ℂ tail V := by
      refine differentiableOn_tsum_of_summable_norm (weight_summable.mul_left K) ?_ hop ?_
      · intro n s hs
        exact (differentiableAt_eBlock (by positivity : (0 : ℝ) < n + 1) (hn1 hs.1)).differentiableWithinAt
      · intro n s hs
        exact (block_le_weight hs.1.1 (hni hs.1) n).trans (mul_le_mul_of_nonneg_right hs.2.le
          (Real.rpow_nonneg (by positivity) _))
    have hmain : DifferentiableAt ℂ (fun s : ℂ ↦ 1 / (s - 1) + 1 / 2 + s / 12) w := by
      fun_prop (disch := exact sub_ne_zero.mpr (hn1 hw))
    exact (hmain.sub (ht.differentiableAt (hop.mem_nhds hwV))).differentiableWithinAt
  have hz : AnalyticOnNhd ℂ riemannZeta D := fun w hw ↦ analyticOn_riemannZeta w (hn1 hw)
  let w₀ : ℂ := ⟨3, z.im⟩
  have h0 : w₀ ∈ D := ⟨by norm_num [w₀], mul_self_pos.mpr hi⟩
  have hnear : em =ᶠ[𝓝 w₀] riemannZeta := by
    have hop : IsOpen {w : ℂ | 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hop.mem_nhds (show w₀ ∈ {w : ℂ | 2 < w.re} by norm_num [w₀])] with w hw
    have hw0 : w ≠ 0 := by intro e; subst w; norm_num at hw
    rw [zeta_em4_of_two_lt hw 1]
    simp [em, tail, Complex.zero_cpow (neg_ne_zero.mpr hw0)]
  exact he.eqOn_of_preconnected_of_eventuallyEq hz hconv.isPreconnected h0 hnear
    ⟨hr, mul_self_pos.mpr hi⟩

/-- The pole-removed zeta function grows at most like the fifth power of the
height on the whole strip containing the radius-two circles about critical
strip zeros. The constant is independent of the center and the ordinate. -/
theorem poleRemovedZeta_strip_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc (-2 : ℝ) 3 →
      ‖poleRemovedZeta z‖ ≤ C * (8 + |z.im|) ^ 5 := by
  let S := ∑' k : ℕ, weight k
  have hS : 0 ≤ S := tsum_nonneg fun k ↦ Real.rpow_nonneg (by positivity) _
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : ℂ) 4).exists_bound_of_continuousOn
    (show Continuous poleRemovedZeta from continuous_iff_continuousAt.mpr fun z ↦
      (analyticAt_poleRemovedZeta z).continuousAt).continuousOn
  refine ⟨max A (3 + S), lt_of_lt_of_le (by linarith) (le_max_right _ _), fun z hz ↦ ?_⟩
  have habs : |z.re| ≤ 3 := abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  have hnorm := (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add habs (le_refl |z.im|))
  let T := 8 + |z.im|
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg z.im]
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  by_cases hlow : |z.im| ≤ 1
  · have hmem : z ∈ closedBall (0 : ℂ) 4 := mem_closedBall_zero_iff.mpr (by linarith)
    exact (hA z hmem).trans ((le_max_left A (3 + S)).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ max A (3 + S)) (one_le_pow₀ hT)))
  have hi : z.im ≠ 0 := by intro h; simp [h] at hlow
  have h1 : z ≠ 1 := fun e ↦ hi (by simp [e])
  have hden : 1 ≤ ‖z - 1‖ := (le_of_not_ge hlow).trans (by simpa using Complex.abs_im_le_norm (z - 1))
  have hden' : ‖z - 1‖ ≤ T := by grw [norm_sub_le, norm_one, hnorm]; dsimp [T]; linarith
  have hP : ‖P4 z‖ ≤ T ^ 4 := by
    have h (j : ℕ) (hj : j ≤ 3) : ‖z + j‖ ≤ T := by
      grw [norm_add_le, Complex.norm_natCast, hnorm]
      dsimp [T]; have : (j : ℝ) ≤ 3 := by exact_mod_cast hj
      linarith
    rw [P4, norm_mul, norm_mul, norm_mul, pow_succ, pow_succ, pow_succ, pow_one]
    gcongr
    · dsimp [T]; linarith
    · simpa using h 1 (by omega)
    · simpa using h 2 (by omega)
    · simpa using h 3 (by omega)
  have hr : -(5/2 : ℝ) < z.re := by linarith [hz.1]
  have ht : ‖tail z‖ ≤ T ^ 4 * S := by
    have hle := block_le_weight hr hi
    have hsum := weight_summable.mul_left ‖P4 z‖
    calc
      ‖tail z‖ ≤ ∑' k : ℕ, ‖eBlock z ((k : ℝ) + 1)‖ := norm_tsum_le_tsum_norm
        (.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hsum)
      _ ≤ ∑' k : ℕ, ‖P4 z‖ * weight k := Summable.tsum_le_tsum hle
        (.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hsum) hsum
      _ = ‖P4 z‖ * S := tsum_mul_left
      _ ≤ T ^ 4 * S := mul_le_mul_of_nonneg_right hP hS
  have hZ : ‖riemannZeta z‖ ≤ (3 + S) * T ^ 4 := by
    rw [← em_eq_zeta hr hi, em]
    have hzT : ‖z‖ ≤ T := by dsimp [T]; linarith
    have hlin : T ≤ T ^ 4 := by simpa using pow_le_pow_right₀ hT (show 1 ≤ 4 by decide)
    have hconst : (1 : ℝ) ≤ T ^ 4 := hT.trans hlin
    calc
      _ ≤ (‖(1 : ℂ) / (z - 1)‖ + ‖(1 / 2 : ℂ)‖ + ‖z / 12‖) + ‖tail z‖ := by
        grw [norm_sub_le, norm_add_le, norm_add_le]
      _ ≤ 1 + 1 + T + T ^ 4 * S := by
        gcongr
        · simpa [one_div] using (inv_le_one_of_one_le₀ hden)
        · norm_num
        · rw [norm_div]; norm_num; linarith
      _ ≤ _ := by nlinarith
  rw [poleRemovedZeta, Function.update_of_ne h1, norm_mul]
  calc
    _ ≤ T * ((3 + S) * T ^ 4) := mul_le_mul hden' hZ (norm_nonneg _) hTpos.le
    _ = (3 + S) * T ^ 5 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Each radius-two circle about a point of the critical strip has one
height-polynomial bound for the pole-removed zeta function. -/
theorem poleRemovedZeta_circle_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℂ, ρ.re ∈ Icc (0 : ℝ) 1 → ∀ w ∈ sphere ρ 2,
      ‖poleRemovedZeta w‖ ≤ C * (10 + |ρ.im|) ^ 5 := by
  obtain ⟨C, hC, hg⟩ := poleRemovedZeta_strip_growth
  refine ⟨C, hC, fun ρ hρ w hw ↦ ?_⟩
  have h := mem_sphere_iff_norm.mp hw
  have hre := abs_le.mp ((Complex.abs_re_le_norm (w - ρ)).trans_eq h)
  have him := (abs_sub_abs_le_abs_sub w.im ρ.im).trans ((Complex.abs_im_le_norm (w - ρ)).trans_eq h)
  simp only [Complex.sub_re] at hre
  refine (hg w ⟨by linarith [hρ.1], by linarith [hρ.2]⟩).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 5) hC.le

/-- A polynomial lower bound on the ordinary zeta leading coefficients gives
a polynomial cost for isolating each critical-strip zero, including its full
multiplicity. The fifth power is the unconditional fourth-order
Euler–Maclaurin estimate after removing the pole. -/
theorem zeta_radius_of_polynomial_coefficients {b : ℝ} (hb : 0 < b) (A : ℕ)
    (hζ : ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b / (2 + |w.im|) ^ A ≤ ‖taylorCoeff riemannZeta w n‖) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : ℂ, ρ.re ∈ Icc (0 : ℝ) 1 → 2 ≤ |ρ.im| → riemannZeta ρ = 0 →
      ∀ m : ℕ, analyticOrderAt riemannZeta ρ = m →
      ∃ r : ℝ, 0 < r ∧ 2 * r ≤ 1 ∧ (r ^ m)⁻¹ = K * (10 + |ρ.im|) ^ (A + 5) ∧
        ∀ L : ℕ, ∀ v ∈ ball (0 : ℂ) (2 * r), v ≠ 0 → dampedZeta ρ L v ≠ 0 := by
  obtain ⟨C, hC, hcircle⟩ := poleRemovedZeta_circle_growth
  refine ⟨C / b, div_pos hC hb, fun ρ hρ ht hz m hm ↦ ?_⟩
  let H := 10 + |ρ.im|
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨r, hr, hr2, he, hiso⟩ := exists_dampedZeta_radius ht hz hm
    (div_pos hb (pow_pos hH A)) (hcircle ρ hρ) (by
      intro w hw hzw n hn
      have hd := mem_closedBall_iff_norm.mp hw
      have hdiff : |w.im - ρ.im| ≤ 1 := (Complex.abs_im_le_norm (w - ρ)).trans hd
      have hup := (abs_sub_abs_le_abs_sub w.im ρ.im).trans hdiff
      have hlo := (abs_sub_abs_le_abs_sub ρ.im w.im).trans (show |ρ.im - w.im| ≤ 1 by simpa only [abs_sub_comm ρ.im w.im] using hdiff)
      refine (div_le_div_of_nonneg_left hb.le (pow_pos (by positivity) A) ?_).trans
        (hζ w (by linarith) hzw n hn)
      exact pow_le_pow_left₀ (by positivity) (by dsimp [H]; linarith) A)
  refine ⟨r, hr, hr2, ?_, hiso⟩
  rw [he, pow_add]
  change (b / H ^ A / (C * H ^ 5))⁻¹ = C / b * (H ^ A * H ^ 5)
  field_simp

/-- Seven powers of rational damping give the translated integrable envelope
on the full enlarged strip. The constant and the height exponent work for
every choice of center in the critical strip. -/
theorem dampedZeta_strip_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℂ, ρ.re ∈ Icc (0 : ℝ) 1 →
      ∀ u : ℂ, u.re ∈ Icc (-1 : ℝ) 2 →
      ‖dampedZeta ρ 7 (u - ρ)‖ ≤ C * (8 + |ρ.im|) ^ 5 / (1 + (u.im - ρ.im) ^ 2) := by
  obtain ⟨C, hC, hg⟩ := poleRemovedZeta_strip_growth
  refine ⟨8 ^ 7 * C, by positivity, fun ρ hρ u hu ↦ ?_⟩
  let v := u - ρ
  let d := |v.im|
  let H := 8 + |ρ.im|
  let q := ‖1 + v / 4‖
  have hd : 0 ≤ d := abs_nonneg _
  have hH : 1 ≤ H := by dsimp [H]; linarith [abs_nonneg ρ.im]
  have hqeq : 4 * q = ‖4 + v‖ := by
    rw [show (4 : ℂ) + v = 4 * (1 + v / 4) by ring, norm_mul]
    norm_num [q]
  have hre : 2 ≤ (4 + v).re := by simp [v]; linarith [hu.1, hρ.2]
  have hq : 2 ≤ 4 * q := hre.trans ((le_abs_self _).trans ((Complex.abs_re_le_norm _).trans_eq hqeq.symm))
  have hdq : d ≤ 4 * q := by simpa [d, hqeq] using Complex.abs_im_le_norm (4 + v)
  have hqpos : 0 < q := by linarith
  have hD : 1 + d ≤ 8 * q := by linarith
  have hY : 8 + |u.im| ≤ H * (1 + d) := by
    have hua : u.im = ρ.im + v.im := by simp [v]
    have := abs_add_le ρ.im v.im
    rw [← hua] at this
    change 8 + |u.im| ≤ (8 + |ρ.im|) * (1 + |v.im|)
    nlinarith [mul_nonneg (abs_nonneg ρ.im) (abs_nonneg v.im), abs_nonneg v.im]
  have hP := (hg u ⟨by linarith [hu.1], by linarith [hu.2]⟩).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hY 5) hC.le)
  unfold dampedZeta
  rw [sub_add_cancel, norm_mul, norm_inv, norm_pow, ← div_eq_mul_inv]
  change ‖poleRemovedZeta u‖ / q ^ 7 ≤ 8 ^ 7 * C * H ^ 5 / (1 + (v.im) ^ 2)
  rw [div_le_div_iff₀ (pow_pos hqpos _) (by positivity)]
  have hquad : 1 + v.im ^ 2 ≤ (1 + d) ^ 2 := by
    have : d ^ 2 = v.im ^ 2 := sq_abs _
    nlinarith
  calc
    _ ≤ C * (H * (1 + d)) ^ 5 * (1 + d) ^ 2 :=
      mul_le_mul hP hquad (by positivity) (by positivity)
    _ = C * H ^ 5 * (1 + d) ^ 7 := by ring
    _ ≤ C * H ^ 5 * (8 * q) ^ 7 := by gcongr
    _ = _ := by ring

end MasulloResearch.StripJets
