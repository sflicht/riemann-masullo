import research.CircleMeanTransfer
import research.StripZetaGrowth
import research.StripZetaClustering
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Logarithmic mean of zeta on quarter-circles in the critical strip

The mean of `log ‖ζ‖` over the circle of radius one quarter about any point of
the critical strip is at least a negative multiple of the logarithm of the
height. No hypothesis on the zeros is used. The anchor is `2 + i·Im w`, where
the Dirichlet series keeps zeta away from zero; the deficit there is carried to
the quarter-circle by `circleAverage_log_norm_deficit_transfer`.
-/

noncomputable section

open Set Metric

namespace MasulloResearch.StripJets

/-- On the half-plane `Re s ≥ 2`, zeta stays within `π²/6 - 1` of one. -/
theorem norm_riemannZeta_sub_one_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have hs1 : 1 < s.re := by linarith
  let F : ℕ → ℂ := fun n ↦ 1 / ((n : ℂ) + 1) ^ s
  have hG : HasSum (fun n : ℕ ↦ 1 / ((n + 2 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simpa [Finset.sum_range_succ] using h
  have hF (n : ℕ) : ‖F (n + 1)‖ ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
    have hcast : ((n + 1 : ℕ) : ℂ) + 1 = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
    simp only [F]
    rw [hcast, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (by omega)]
    apply one_div_le_one_div_of_le (by positivity)
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n + 2)) hs
  have hsum : Summable F := by
    rw [← summable_nat_add_iff 1]
    exact Summable.of_norm_bounded hG.summable hF
  have h0 : F 0 = 1 := by simp [F]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1, hsum.tsum_eq_zero_add, h0, add_sub_cancel_left]
  exact tsum_of_norm_bounded hG hF

/-- **Unconditional quarter-circle mean.** One constant bounds the logarithmic
mean of zeta from below on every quarter-circle centered in the critical strip
at height at least one. The center need not be a zero. -/
theorem zeta_quarterCircle_mean_lower :
    ∃ B : ℝ, ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → 1 ≤ |w.im| →
      -(B * Real.log (2 + |w.im|)) ≤
        Real.circleAverage (fun z ↦ Real.log ‖riemannZeta z‖) w (1/4) := by
  obtain ⟨C, hC, hgrow⟩ := poleRemovedZeta_strip_growth
  refine ⟨160 * Real.log (C + 2) + 4887, fun w hw ht ↦ ?_⟩
  let c : ℂ := ⟨2, w.im⟩
  let T : ℝ := 11 + |w.im|
  let M : ℝ := (C + 2) * T ^ 5
  have hT : 1 ≤ T := by dsimp only [T]; linarith [abs_nonneg w.im]
  have hT5 : 1 ≤ T ^ 5 := one_le_pow₀ hT
  have hM : 1 ≤ M := by dsimp only [M]; nlinarith
  have hπ : Real.pi ^ 2 / 6 - 1 ≤ 3 / 4 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hz2 {z : ℂ} (hz : 2 ≤ z.re) : ‖riemannZeta z - 1‖ ≤ 3 / 4 :=
    (norm_riemannZeta_sub_one_le hz).trans hπ
  -- The envelope on the disk of radius 9/4 about the anchor.
  have hbound : ∀ z ∈ closedBall c (9/4), ‖poleRemovedZeta z‖ ≤ M := by
    intro z hz
    have hd := mem_closedBall_iff_norm.mp hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm (z - c)).trans hd)
    have him := (Complex.abs_im_le_norm (z - c)).trans hd
    simp only [Complex.sub_re, Complex.sub_im, c] at hre him
    have himz : |z.im| ≤ |w.im| + 9/4 := by
      have := abs_sub_abs_le_abs_sub z.im w.im
      linarith
    by_cases h3 : z.re ≤ 3
    · calc ‖poleRemovedZeta z‖ ≤ C * (8 + |z.im|) ^ 5 := hgrow z ⟨by linarith [hre.1], h3⟩
        _ ≤ C * T ^ 5 := by
          gcongr
          dsimp only [T]
          linarith
        _ ≤ M := by dsimp only [M]; nlinarith
    · rw [not_le] at h3
      have hz1 : z ≠ 1 := fun h ↦ by rw [h] at h3; norm_num at h3
      rw [poleRemovedZeta, Function.update_of_ne hz1, norm_mul]
      have hζ : ‖riemannZeta z‖ ≤ 2 := by
        calc ‖riemannZeta z‖ = ‖(riemannZeta z - 1) + 1‖ := by ring_nf
          _ ≤ ‖riemannZeta z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ ≤ 2 := by rw [norm_one]; linarith [hz2 (z := z) (by linarith)]
      have hz1n : ‖z - 1‖ ≤ T := by
        calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im _
          _ ≤ T := by
            simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
            have : |z.re - 1| ≤ 13/4 := by rw [abs_le]; constructor <;> linarith [hre.1, hre.2]
            dsimp only [T]
            linarith
      calc ‖z - 1‖ * ‖riemannZeta z‖ ≤ T * 2 :=
            mul_le_mul hz1n hζ (norm_nonneg _) (by linarith)
        _ ≤ M := by
          dsimp only [M]
          have h5 : T ≤ T ^ 5 := le_self_pow₀ hT (by norm_num)
          nlinarith [mul_nonneg hC.le (zero_le_one.trans hT5)]
  -- The anchor.
  have hc1 : c ≠ 1 := fun h ↦ by
    have := congrArg Complex.re h
    norm_num [c] at this
  have hζc : 1/4 ≤ ‖riemannZeta c‖ := by
    have h := hz2 (z := c) (le_of_eq rfl)
    have h1 : ‖(1 : ℂ)‖ ≤ ‖riemannZeta c‖ + ‖riemannZeta c - 1‖ := by
      calc ‖(1 : ℂ)‖ = ‖riemannZeta c - (riemannZeta c - 1)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [norm_one] at h1
    linarith
  have hcm1 : 1 ≤ ‖c - 1‖ := by
    have := Complex.abs_re_le_norm (c - 1)
    norm_num [c] at this
    exact this
  have hfc : 1/4 ≤ ‖poleRemovedZeta c‖ := by
    rw [poleRemovedZeta, Function.update_of_ne hc1, norm_mul]
    nlinarith [norm_nonneg (riemannZeta c)]
  have hfc0 : poleRemovedZeta c ≠ 0 := fun h ↦ by
    rw [h, norm_zero] at hfc
    linarith
  have hsub : closedBall w (1/4) ⊆ closedBall c (9/4) := by
    apply closedBall_subset_closedBall'
    have hwc : w - c = ((w.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c]
    have : dist w c ≤ 2 := by
      rw [dist_eq_norm, hwc, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hw.1, hw.2]
    linarith
  have key := circleAverage_log_norm_deficit_transfer analyticAt_poleRemovedZeta
    (c := c) (ρ := w) (R := 9/4) (r := 1/4) (M := M) (by norm_num) (by norm_num) hsub hM
    hbound hfc0
  have hlogfc : -3 ≤ Real.log ‖poleRemovedZeta c‖ := by
    have h1 : Real.log (1/4) ≤ Real.log ‖poleRemovedZeta c‖ :=
      Real.log_le_log (by norm_num) hfc
    have h2 : -3 ≤ Real.log (1/4) := by
      rw [one_div, Real.log_inv]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      linarith
    linarith
  have hbf : -80 * Real.log M - 243 ≤
      Real.circleAverage (fun z ↦ Real.log ‖poleRemovedZeta z‖) w (1/4) := by
    norm_num at key
    linarith
  -- Pass from the pole-removed function to zeta on the circle.
  let ℓ : ℝ := Real.log (2 + |w.im|)
  have hℓ : 0 ≤ ℓ := Real.log_nonneg (by linarith [abs_nonneg w.im])
  have hfint : CircleIntegrable (fun z ↦ Real.log ‖poleRemovedZeta z‖) w (1/4) :=
    MeromorphicOn.circleIntegrable_log_norm fun z _ ↦
      (analyticAt_poleRemovedZeta z).meromorphicAt
  have hquarter : |(1/4 : ℝ)| = 1/4 := abs_of_pos (by norm_num)
  have hsphere {z : ℂ} (hz : z ∈ sphere w |(1/4 : ℝ)|) :
      z ≠ 1 ∧ ‖z - 1‖ ≤ 2 + |w.im| := by
    rw [hquarter] at hz
    have hd := mem_sphere_iff_norm.mp hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm (z - w)).trans_eq hd)
    have him := (Complex.abs_im_le_norm (z - w)).trans_eq hd
    simp only [Complex.sub_re, Complex.sub_im] at hre him
    have h1 : |w.im| - |z.im| ≤ 1/4 := by
      have := abs_sub_abs_le_abs_sub w.im z.im
      rw [abs_sub_comm] at this
      linarith
    have h2 : |z.im| ≤ |w.im| + 1/4 := by
      have := abs_sub_abs_le_abs_sub z.im w.im
      linarith
    refine ⟨fun h ↦ ?_, ?_⟩
    · rw [h] at h1
      norm_num at h1
      linarith
    · calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 2 + |w.im| := by
          simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
          have : |z.re - 1| ≤ 5/4 := by
            rw [abs_le]
            constructor <;> linarith [hw.1, hw.2, hre.1, hre.2]
          linarith
  have hζint : CircleIntegrable (fun z ↦ Real.log ‖riemannZeta z‖) w (1/4) :=
    MeromorphicOn.circleIntegrable_log_norm fun z hz ↦
      (analyticOn_riemannZeta z (hsphere hz).1).meromorphicAt
  have hpt : ∀ z ∈ sphere w |(1/4 : ℝ)|,
      ((fun z : ℂ ↦ Real.log ‖poleRemovedZeta z‖) - fun _ : ℂ ↦ ℓ) z ≤
        Real.log ‖riemannZeta z‖ := by
    intro z hz
    obtain ⟨hz1, hzn⟩ := hsphere hz
    simp only [Pi.sub_apply]
    rw [poleRemovedZeta, Function.update_of_ne hz1]
    rcases eq_or_ne (riemannZeta z) 0 with h0 | h0
    · simp [h0, hℓ]
    · have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
      rw [norm_mul, Real.log_mul hpos.ne' (norm_ne_zero_iff.mpr h0)]
      have : Real.log ‖z - 1‖ ≤ ℓ := Real.log_le_log hpos hzn
      linarith
  have hmono := Real.circleAverage_mono (hfint.sub (circleIntegrable_const ℓ w (1/4))) hζint hpt
  rw [Real.circleAverage_sub hfint (circleIntegrable_const ℓ w (1/4)),
    Real.circleAverage_const] at hmono
  -- Arithmetic.
  have hL : 1/2 ≤ ℓ := by
    have h2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith [abs_nonneg w.im])
    linarith [Real.log_two_gt_d9]
  have ha : 0 ≤ Real.log (C + 2) := Real.log_nonneg (by linarith)
  have hx : Real.log T ≤ 5 + ℓ := by
    have h6 : T ≤ 6 * (2 + |w.im|) := by dsimp only [T]; linarith [abs_nonneg w.im]
    have hpos : (0 : ℝ) < 2 + |w.im| := by linarith [abs_nonneg w.im]
    calc Real.log T ≤ Real.log (6 * (2 + |w.im|)) := Real.log_le_log (by linarith) h6
      _ = Real.log 6 + ℓ := Real.log_mul (by norm_num) hpos.ne'
      _ ≤ 5 + ℓ := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)
        linarith
  have hlogM : Real.log M = Real.log (C + 2) + 5 * Real.log T := by
    dsimp only [M]
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    norm_num
  have hprod : Real.log (C + 2) * (1/2) ≤ Real.log (C + 2) * ℓ :=
    mul_le_mul_of_nonneg_left hL ha
  show -((160 * Real.log (C + 2) + 4887) * ℓ) ≤ _
  nlinarith

/-- **Unconditional local lower bound.** At every point of the critical strip
of height at least one, the first nonzero Taylor coefficient of zeta is bounded
below by the cluster cost of the other zeros in the quarter-disk, up to a power
of the height. This is the lower half of the classical local product formula,
with every multiplicity retained. -/
theorem zetaCoeff_log_lower_of_clusterCost :
    ∃ B : ℝ, ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → 1 ≤ |w.im| → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n →
      -(B * Real.log (2 + |w.im|)) - zetaClusterCost w (1/4) ≤
        Real.log ‖taylorCoeff riemannZeta w n‖ := by
  obtain ⟨B, hB⟩ := zeta_quarterCircle_mean_lower
  refine ⟨B, fun w hw ht n hn ↦ ?_⟩
  have h := hB w hw ht
  rw [zeta_circleAverage_eq_cluster_add_coeff ht hn] at h
  have hlog : (n : ℝ) * Real.log (1/4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n)
      (Real.log_nonpos (by norm_num) (by norm_num))
  linarith

end MasulloResearch.StripJets
