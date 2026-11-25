import research.StripZetaRadius
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Close neighbors and the first nonzero zeta coefficient

The local product estimate and a short-interval zero count are explicit analytic
inputs. The calculation below isolates the contribution from distances smaller
than the inverse square of the logarithm of the height. Distances are complex
distances and each distinct neighbor is weighted by its full analytic order.
-/

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology
open scoped Classical BigOperators

namespace MasulloResearch.StripJets

/-- The other ordinary zeta zeros in the closed quarter-disk. A zero on the
boundary has logarithmic weight zero. -/
def zetaNeighbors (w : ℂ) : Finset ℂ :=
  ((isCompact_closedBall w (1/4 : ℝ)).inter_riemannZetaZeros_finite.toFinset).erase w

/-- Membership records a different zero within the closed quarter-disk. -/
theorem mem_zetaNeighbors_iff {w z : ℂ} :
    z ∈ zetaNeighbors w ↔ z ≠ w ∧ dist z w ≤ 1/4 ∧ riemannZeta z = 0 := by
  simp [zetaNeighbors, Metric.mem_closedBall, mem_riemannZetaZeros]

/-- Count the other zeros out to radius `r`, including their multiplicities.
Only radii up to a quarter are used. -/
def zetaNeighborCount (w : ℂ) (r : ℝ) : ℝ :=
  ∑ z ∈ zetaNeighbors w, if dist z w ≤ r then (analyticOrderNatAt riemannZeta z : ℝ) else 0

/-- Logarithmic contribution inside radius `r`. A neighbor at distance `d < r`
contributes its multiplicity times `log (r/d)`. -/
def zetaClusterCost (w : ℂ) (r : ℝ) : ℝ :=
  ∑ z ∈ zetaNeighbors w, (analyticOrderNatAt riemannZeta z : ℝ) *
    max 0 (Real.log (r / dist z w))

/-- Integrate the counting function in logarithmic radius. The truncation at
depth `U` charges even closer neighbors for exactly the first `U` units. -/
theorem truncated_log_sum_le {ι : Type*} (s : Finset ι) (a m : ι → ℝ)
    {U P Q : ℝ} (hU : 0 ≤ U) (ha : ∀ i ∈ s, 0 ≤ a i) (hm : ∀ i ∈ s, 0 ≤ m i)
    (hcount : ∀ u ∈ Icc 0 U, (∑ i ∈ s, if u ≤ a i then m i else 0) ≤
      P * Real.exp (-u) + Q) :
    ∑ i ∈ s, m i * min (a i) U ≤ P * (1 - Real.exp (-U)) + Q * U := by
  let step (i : ι) (u : ℝ) : ℝ := if u ≤ a i then m i else 0
  have hint (i : ι) (hi : i ∈ s) : IntervalIntegrable (step i) volume 0 U := by
    apply Antitone.intervalIntegrable
    intro x y hxy
    dsimp [step]
    split_ifs <;> first | rfl | exact hm i hi | linarith
  have heval (i : ι) (hi : i ∈ s) :
      (∫ u in (0:ℝ)..U, step i u) = m i * min (a i) U := by
    let b := min (a i) U
    have hb : b ∈ Icc 0 U := ⟨le_min (ha i hi) hU, min_le_right ..⟩
    calc
      _ = ∫ u in (0:ℝ)..U, indicator {x : ℝ | x ≤ b} (fun _ ↦ m i) u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hU] at hu
        simp [step, indicator, b, hu.2]
      _ = _ := by
        rw [intervalIntegral.integral_indicator hb, intervalIntegral.integral_const]
        simp [b, mul_comm]
  have hleft : IntervalIntegrable (fun u ↦ ∑ i ∈ s, step i u) volume 0 U := by
    simpa only [← Finset.sum_apply] using IntervalIntegrable.sum s hint
  have hexp : Continuous (fun u : ℝ ↦ P * Real.exp (-u)) := by fun_prop
  calc
    _ = ∫ u in (0:ℝ)..U, ∑ i ∈ s, step i u := by
      rw [intervalIntegral.integral_finsetSum hint]
      exact Finset.sum_congr rfl fun i hi ↦ (heval i hi).symm
    _ ≤ ∫ u in (0:ℝ)..U, P * Real.exp (-u) + Q :=
      intervalIntegral.integral_mono_on hU hleft
        ((hexp.add continuous_const).intervalIntegrable ..) hcount
    _ = _ := by
      rw [intervalIntegral.integral_add (hexp.intervalIntegrable ..) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg Real.exp,
        integral_exp, intervalIntegral.integral_const]
      simp [mul_comm]

/-- The RH-quality count is only needed from `1/L²` to `1/4`, where `L`
is the logarithm of the height. The bound is uniform over all closer clusters. -/
theorem zetaClusterCost_outer_le (w : ℂ) {L C : ℝ} (hL : 2 ≤ L) (hC : 0 ≤ C)
    (hcount : ∀ r ∈ Icc (1/L^2) (1/4 : ℝ), zetaNeighborCount w r ≤
      C * (r * L + L / Real.log L)) :
    zetaClusterCost w (1/4) ≤ zetaClusterCost w (1/L^2) + (9/4) * C * L := by
  let R : ℝ := 1/4
  let r₀ : ℝ := 1/L^2
  let U := Real.log (R/r₀)
  let a (z : ℂ) := Real.log (R / dist z w)
  let m (z : ℂ) : ℝ := analyticOrderNatAt riemannZeta z
  have hLp : 0 < L := by linarith
  have hlog : 0 < Real.log L := Real.log_pos (by linarith)
  have hR : 0 < R := by norm_num [R]
  have hr : 0 < r₀ := by dsimp [r₀]; positivity
  have hrR : r₀ ≤ R := by
    dsimp [r₀, R]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg (L-2)]
  have hU : 0 ≤ U := Real.log_nonneg ((one_le_div hr).mpr hrR)
  have hUle : U ≤ 2 * Real.log L := by
    dsimp [U,r₀]
    rw [Real.log_div hR.ne' (by positivity), Real.log_div (x := 1) (y := L^2) one_ne_zero (by positivity),
      Real.log_one, Real.log_pow]
    have := Real.log_nonpos hR.le (by norm_num [R])
    push_cast
    linarith
  have hdist {z : ℂ} (hz : z ∈ zetaNeighbors w) : 0 < dist z w ∧ dist z w ≤ R :=
    ⟨dist_pos.mpr (mem_zetaNeighbors_iff.mp hz).1, (mem_zetaNeighbors_iff.mp hz).2.1⟩
  have ha (z : ℂ) (hz : z ∈ zetaNeighbors w) : 0 ≤ a z :=
    Real.log_nonneg ((one_le_div (hdist hz).1).mpr (hdist hz).2)
  have hm (z : ℂ) (_ : z ∈ zetaNeighbors w) : 0 ≤ m z := Nat.cast_nonneg _
  have hscale (u : ℝ) : R * Real.exp (-u) = R / Real.exp u := by rw [Real.exp_neg, div_eq_mul_inv]
  have hcount' (u : ℝ) (hu : u ∈ Icc 0 U) :
      (∑ z ∈ zetaNeighbors w, if u ≤ a z then m z else 0) ≤
        (C * R * L) * Real.exp (-u) + C * (L / Real.log L) := by
    have hrad : R * Real.exp (-u) ∈ Icc r₀ R := by
      rw [hscale]
      constructor
      · rw [le_div_iff₀ (Real.exp_pos _), mul_comm, ← le_div_iff₀ hr]
        exact (Real.le_log_iff_exp_le (div_pos hR hr)).mp hu.2
      · exact div_le_self hR.le (Real.one_le_exp_iff.mpr hu.1)
    have heq (z : ℂ) (hz : z ∈ zetaNeighbors w) :
        u ≤ a z ↔ dist z w ≤ R * Real.exp (-u) := by
      rw [Real.le_log_iff_exp_le (div_pos hR (hdist hz).1), hscale,
        le_div_iff₀ (hdist hz).1, le_div_iff₀ (Real.exp_pos u), mul_comm]
    calc
      _ = zetaNeighborCount w (R * Real.exp (-u)) :=
        Finset.sum_congr rfl fun z hz ↦ by simp only [heq z hz]; rfl
      _ ≤ _ := (hcount _ hrad).trans_eq (by ring)
  have htr := truncated_log_sum_le (zetaNeighbors w) a m hU ha hm hcount'
  have hsplit : zetaClusterCost w R =
      zetaClusterCost w r₀ + ∑ z ∈ zetaNeighbors w, m z * min (a z) U := by
    unfold zetaClusterCost
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    have hrel : Real.log (r₀ / dist z w) = a z - U := by
      dsimp [a,U]
      rw [Real.log_div hr.ne' (hdist hz).1.ne', Real.log_div hR.ne' (hdist hz).1.ne',
        Real.log_div hR.ne' hr.ne']
      ring
    change m z * max 0 (a z) = _
    rw [max_eq_right (ha z hz), hrel]
    change m z * a z = m z * max 0 (a z - U) + m z * min (a z) U
    rcases le_total (a z) U with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, max_eq_right (sub_nonneg.mpr h)]; ring
  rw [show (1/4 : ℝ) = R from rfl, show 1 / L^2 = r₀ from rfl, hsplit]
  apply add_le_add_right (htr.trans _) _
  have hexp := mul_nonneg (mul_nonneg (mul_nonneg hC hR.le) hLp.le) (Real.exp_pos (-U)).le
  have hrem := mul_le_mul_of_nonneg_left hUle (mul_nonneg hC (div_nonneg hLp.le hlog.le))
  have he : C * (L / Real.log L) * (2 * Real.log L) = 2*C*L := by field_simp
  rw [he] at hrem
  dsimp [R] at *
  linarith

private theorem trailingCoeff_eq_taylorCoeff {f : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f w) {n : ℕ} (hn : analyticOrderAt f w = n) :
    meromorphicTrailingCoeffAt f w = taylorCoeff f w n := by
  obtain ⟨g, hg, hgw, he⟩ := hf.analyticOrderAt_eq_natCast.mp hn
  have htr := hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (f := f)
    (n := (n : ℤ)) hgw (by simpa only [Filter.EventuallyEq, zpow_natCast] using he.filter_mono nhdsWithin_le_nhds)
  rw [htr, taylorCoeff]
  have hfg : f =ᶠ[𝓝 w] fun z ↦ (z-w)^n * g z := he
  have hp : AnalyticAt ℂ (fun z : ℂ ↦ (z-w)^n) w := by fun_prop
  have hpow (j : ℕ) : iteratedDeriv j (fun z : ℂ ↦ (z-w)^n) w =
      if j = n then (n.factorial : ℂ) else 0 := by
    rw [iteratedDeriv_comp_sub_const (f := fun z : ℂ ↦ z^n)]
    simp only [sub_self, iteratedDeriv_fun_pow_zero]
    split_ifs <;> simp
  rw [hfg.iteratedDeriv_eq n, iteratedDeriv_fun_mul hp.contDiffAt hg.contDiffAt,
    Finset.sum_eq_single n]
  · simp [hpow, Nat.factorial_ne_zero]
  · intro j _ hj
    simp [hpow, hj]
  · simp

/-- Away from its pole, ordinary zeta has finite analytic order. -/
theorem zetaOrder_finite {z : ℂ} (hz : z ≠ 1) : analyticOrderAt riemannZeta z ≠ ⊤ := by
  apply analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected (x := 2)
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected (by simp) hz
  rw [(analyticOn_riemannZeta 2 (by norm_num)).analyticOrderAt_eq_zero.mpr
    (riemannZeta_ne_zero_of_one_le_re (by norm_num))]
  simp

/-- Exact quarter-circle Jensen formula for the ordinary zeta coefficient.
The central multiplicity is separated from the cost of all other zeros. -/
theorem zeta_circleAverage_eq_cluster_add_coeff {w : ℂ} (hw : 1 ≤ |w.im|)
    {n : ℕ} (hn : analyticOrderAt riemannZeta w = n) :
    Real.circleAverage (fun z ↦ Real.log ‖riemannZeta z‖) w (1/4) =
      zetaClusterCost w (1/4) + n * Real.log (1/4) +
        Real.log ‖taylorCoeff riemannZeta w n‖ := by
  let R : ℝ := 1/4
  let B := closedBall w R
  let D := MeromorphicOn.divisor riemannZeta B
  have hR : 0 < R := by norm_num [R]
  have hne (z : ℂ) (hz : z ∈ B) : z ≠ 1 := by
    rintro rfl
    have h := (Complex.abs_im_le_norm (1-w)).trans (mem_closedBall_iff_norm.mp hz)
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
    dsimp [R] at h
    linarith
  have han : AnalyticOnNhd ℂ riemannZeta B := fun z hz ↦ analyticOn_riemannZeta z (hne z hz)
  have hcenter : w ∈ B := mem_closedBall_self hR.le
  have hD (z : ℂ) (hz : z ∈ B) : D z = (analyticOrderNatAt riemannZeta z : ℤ) := by
    change MeromorphicOn.divisor riemannZeta B z = _
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply han hz, ← Nat.cast_analyticOrderNatAt (zetaOrder_finite (hne z hz)),
      ENat.map_natCast]
    simp
  have hDw : D w = (n : ℤ) := by rw [hD w hcenter]; simp [analyticOrderNatAt, hn]
  let term (z : ℂ) : ℝ := D z * Real.log (R * ‖w-z‖⁻¹)
  have hs : Function.support term ⊆ (zetaNeighbors w : Set ℂ) := by
    intro z hz
    have hterm : term z ≠ 0 := hz
    have hDz : D z ≠ 0 := by intro h; exact hterm (by simp [term,h])
    have hzB := D.supportWithinDomain (show z ∈ D.support from hDz)
    apply mem_zetaNeighbors_iff.mpr
    refine ⟨?_, hzB, ?_⟩
    · rintro rfl
      simp [term] at hterm
    · by_contra h
      rw [hD z hzB] at hDz
      simp [analyticOrderNatAt, (han z hzB).analyticOrderAt_eq_zero.mpr h] at hDz
  have hsum : ∑ᶠ z, term z = zetaClusterCost w R := by
    rw [finsum_eq_sum_of_support_subset _ hs]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    obtain ⟨hzw, hd, _⟩ := mem_zetaNeighbors_iff.mp hz
    have hp := dist_pos.mpr hzw
    have hlog : 0 ≤ Real.log (R / dist z w) := Real.log_nonneg ((one_le_div hp).mpr hd)
    simp [term, hD z hd, ← dist_eq_norm, dist_comm w z,
      max_eq_right hlog, ← div_eq_mul_inv]
  have hJ := MeromorphicOn.circleAverage_log_norm (f := riemannZeta) (c := w) hR.ne'
    (by simpa only [abs_of_pos hR] using han.meromorphicOn)
  rw [abs_of_pos hR] at hJ
  change _ = (∑ᶠ z, term z) + (D w : ℝ) * Real.log R + _ at hJ
  simpa only [hsum, hDw, Int.cast_natCast, trailingCoeff_eq_taylorCoeff (han w hcenter) hn]
    using hJ

/-- Only the neighbors within `r` need spacing. A polynomial lower gap bound
costs at most `K log T` per unit of multiplicity. -/
theorem zetaClusterCost_le_of_separation {w : ℂ} {r T : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hT : 1 ≤ T) (K : ℕ)
    (hgap : ∀ z ∈ zetaNeighbors w, dist z w ≤ r → 1/T^K ≤ dist z w) :
    zetaClusterCost w r ≤ zetaNeighborCount w r * (K * Real.log T) := by
  have hTpos := zero_lt_one.trans_le hT
  have hK : 0 ≤ (K : ℝ) * Real.log T := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hT)
  unfold zetaClusterCost zetaNeighborCount
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun z hz ↦ ?_
  have hd := dist_pos.mpr (mem_zetaNeighbors_iff.mp hz).1
  by_cases h : dist z w ≤ r
  · rw [ite_eq_left h]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    refine max_le hK ?_
    rw [← Real.log_pow]
    apply Real.log_le_log (div_pos hr hd)
    rw [div_le_iff₀ hd]
    calc r ≤ 1 := hr₁
         _ ≤ _ := by
           have := (div_le_iff₀ (pow_pos hTpos K)).mp (hgap z hz h)
           linarith [mul_comm (dist z w) (T^K)]
  · rw [ite_eq_right h, zero_mul, max_eq_left (Real.log_nonpos (div_nonneg hr.le hd.le)
      ((div_le_one hd).mpr (le_of_not_ge h))), mul_zero]

/-- Averaging a finite local product lower estimate over the quarter-circle
costs at most `log 4` per unit of multiplicity, even for zeros on the circle.
This gives the mean input from the fixed-window form of Titchmarsh 9.6(B). -/
theorem zeta_circleAverage_lower_of_localProduct {w : ℂ} (hw : 1 ≤ |w.im|)
    (S : Finset ℂ) {error : ℝ}
    (hprod : ∀ z ∈ sphere w (1/4 : ℝ),
      (∑ v ∈ S, (analyticOrderNatAt riemannZeta v : ℝ) * Real.log ‖z-v‖) - error ≤
        Real.log ‖riemannZeta z‖) :
    (∑ v ∈ S, (analyticOrderNatAt riemannZeta v : ℝ)) * Real.log (1/4) - error ≤
      Real.circleAverage (fun z ↦ Real.log ‖riemannZeta z‖) w (1/4) := by
  let R : ℝ := 1/4
  let m (v : ℂ) : ℝ := analyticOrderNatAt riemannZeta v
  let g (v z : ℂ) := m v * Real.log ‖z-v‖
  have hR : 0 < R := by norm_num [R]
  have hi (v : ℂ) : CircleIntegrable (g v) w R := by
    exact (MeromorphicOn.circleIntegrable_log_norm (f := fun z : ℂ ↦ z-v)
      (by fun_prop)).const_fun_smul (a := m v)
  have hz : CircleIntegrable (fun z ↦ Real.log ‖riemannZeta z‖) w R := by
    apply MeromorphicOn.circleIntegrable_log_norm
    intro z hz
    apply (analyticOn_riemannZeta z ?_).meromorphicAt
    rintro rfl
    have h := Complex.abs_im_le_norm (1-w)
    have hs := mem_sphere_iff_norm.mp hz
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
    rw [abs_of_pos hR] at hs
    dsimp [R] at hs
    linarith
  have hsum : CircleIntegrable (fun z ↦ ∑ v ∈ S, g v z) w R := by
    simpa only [← Finset.sum_apply] using CircleIntegrable.sum S (fun v _ ↦ hi v)
  calc
    _ ≤ (∑ v ∈ S, Real.circleAverage (g v) w R) - error := by
      rw [Finset.sum_mul]
      apply sub_le_sub_right
      refine Finset.sum_le_sum fun v _ ↦ ?_
      change m v * Real.log R ≤ Real.circleAverage (fun z ↦ m v • Real.log ‖z-v‖) w R
      rw [Real.circleAverage_fun_smul, smul_eq_mul, circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR.ne']
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right Real.posLog_nonneg) (Nat.cast_nonneg _)
    _ = Real.circleAverage (fun z ↦ (∑ v ∈ S, g v z) - error) w R := by
      rw [Real.circleAverage_fun_sub hsum (circleIntegrable_const error w R),
        Real.circleAverage_fun_sum (fun v _ ↦ hi v), Real.circleAverage_const]
    _ ≤ _ := Real.circleAverage_mono (hsum.fun_sub (circleIntegrable_const error w R)) hz
      (by simpa only [abs_of_pos hR] using hprod)

/-- The coefficient at an actual zero from a lower bound on the logarithmic
quarter-circle average, the short-interval count, and the innermost cost.
Here `B, C, E` are the constants in these three bounds respectively. -/
theorem zetaCoeff_log_lower_of_microcluster {w : ℂ} (hw : 1 ≤ |w.im|)
    {n : ℕ} (hn : analyticOrderAt riemannZeta w = n)
    {L B C E : ℝ} (hL : 2 ≤ L) (hC : 0 ≤ C)
    (hmean : -(B*L) ≤ Real.circleAverage (fun z ↦ Real.log ‖riemannZeta z‖) w (1/4))
    (hcount : ∀ r ∈ Icc (1/L^2) (1/4 : ℝ), zetaNeighborCount w r ≤ C * (r*L + L/Real.log L))
    (hclose : zetaClusterCost w (1/L^2) ≤ E*L) :
    -((B + (9/4)*C + E)*L) ≤ Real.log ‖taylorCoeff riemannZeta w n‖ := by
  rw [zeta_circleAverage_eq_cluster_add_coeff hw hn] at hmean
  have houter := zetaClusterCost_outer_le w hL hC hcount
  have hc := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) n)
    (Real.log_nonpos (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num))
  linarith

/-- A zero with at most `M` units of neighboring multiplicity inside the tiny
disk, each at distance at least `T⁻ᴷ`, has a polynomial coefficient bound at
that zero. When the tiny disk is empty one can take `M = 0`. -/
theorem zetaCoeff_lower_at_separated_zero {w : ℂ} (hw : 1 ≤ |w.im|)
    {n : ℕ} (hn : analyticOrderAt riemannZeta w = n)
    (K : ℕ) {B C M : ℝ} (hC : 0 ≤ C) :
    let T := 2+|w.im|
    let L := Real.log T
    2 ≤ L →
    -(B*L) ≤ Real.circleAverage (fun z ↦ Real.log ‖riemannZeta z‖) w (1/4) →
    (∀ r ∈ Icc (1/L^2) (1/4 : ℝ), zetaNeighborCount w r ≤ C*(r*L + L/Real.log L)) →
    zetaNeighborCount w (1/L^2) ≤ M →
    (∀ z ∈ zetaNeighbors w, dist z w ≤ 1/L^2 → 1/T^K ≤ dist z w) →
    T ^ (-(B + (9/4)*C + M*K)) ≤ ‖taylorCoeff riemannZeta w n‖ := by
  intro T L hL hmean hcount hM hgap
  have hT : 1 ≤ T := by dsimp [T]; linarith
  have hLp : 0 < L := by linarith
  have hr₁ : 1/L^2 ≤ 1 := (div_le_one (pow_pos hLp _)).mpr (one_le_pow₀ (by linarith) : 1 ≤ L^2)
  have hsep := zetaClusterCost_le_of_separation (w := w) (by positivity : 0 < 1/L^2)
    hr₁ hT K hgap
  have hclose : zetaClusterCost w (1/L^2) ≤ (M*K)*L := hsep.trans <|
    (mul_le_mul_of_nonneg_right hM (mul_nonneg (Nat.cast_nonneg _) hLp.le)).trans_eq (by ring)
  have hlog := zetaCoeff_log_lower_of_microcluster hw hn hL hC hmean hcount hclose
  have hne : w ≠ 1 := by rintro rfl; norm_num at hw
  have hd := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticOn_riemannZeta w hne)).mp hn).2
  have hp : 0 < ‖taylorCoeff riemannZeta w n‖ :=
    norm_pos_iff.mpr (div_ne_zero hd (by exact_mod_cast Nat.factorial_ne_zero n))
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos (zero_lt_one.trans_le hT) _) hp).mp
  rwa [Real.log_rpow (zero_lt_one.trans_le hT), neg_mul]

/-- Extend a uniform high-zero bound down to height one by finite compactness.
This is the coefficient hypothesis of `rational_convolution_finiteGram_bound`. -/
theorem extend_high_zetaCoeff_bound {H : ℝ} (A : ℕ)
    (hhigh : ∀ w : ℂ, H ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → 1/(2+|w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖) :
    ∃ b : ℝ, 0 < b ∧ ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b/(2+|w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖ := by
  let S := ((isCompact_closedBall (0:ℂ) (H+1)).inter_riemannZetaZeros_finite.toFinset).filter
    (fun w ↦ 1 ≤ |w.im|)
  let b' (w : ℂ) := ‖taylorCoeff riemannZeta w (analyticOrderNatAt riemannZeta w)‖
  have hpos (w : ℂ) (hw : w ∈ S) : 0 < b' w := by
    have ht := (Finset.mem_filter.mp hw).2
    have hne : w ≠ 1 := by rintro rfl; norm_num at ht
    have h := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticOn_riemannZeta w hne)).mp
      (Nat.cast_analyticOrderNatAt (zetaOrder_finite hne)).symm
    exact norm_pos_iff.mpr (div_ne_zero h.2 (by exact_mod_cast Nat.factorial_ne_zero _))
  let V := insert (1:ℝ) (S.image b')
  have hV : V.Nonempty := ⟨1, Finset.mem_insert_self ..⟩
  refine ⟨V.min' hV, ?_, fun w ht hz n hn ↦ ?_⟩
  · rcases Finset.mem_insert.mp (V.min'_mem hV) with h | h
    · rw [h]; norm_num
    · obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
      exact he ▸ hpos w hw
  · have hpow : 1 ≤ (2 + |w.im|)^A := one_le_pow₀ (by linarith)
    by_cases hi : H ≤ |w.im|
    · exact (div_le_div_of_nonneg_right (V.min'_le _ (Finset.mem_insert_self ..))
        (zero_le_one.trans hpow)).trans (hhigh w hi hz n hn)
    have hre : 0 < w.re := by
      by_contra! hr
      obtain ⟨k, rfl⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos hr).mp hz
      norm_num at ht
    have hre' : w.re < 1 := lt_of_not_ge fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz
    have hwS : w ∈ S := by
      simp only [S, Finset.mem_filter, Finite.mem_toFinset, mem_inter_iff,
        mem_closedBall, dist_zero_right, mem_riemannZetaZeros]
      refine ⟨⟨?_, hz⟩, ht⟩
      have := Complex.norm_le_abs_re_add_abs_im w
      rw [abs_of_pos hre] at this
      linarith
    have hn' : analyticOrderNatAt riemannZeta w = n := by simp [analyticOrderNatAt, hn]
    have hle := V.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem b' hwS))
    calc V.min' hV / (2+|w.im|)^A ≤ b' w / (2+|w.im|)^A :=
            div_le_div_of_nonneg_right hle (zero_le_one.trans hpow)
         _ ≤ b' w := div_le_self (norm_nonneg _) hpow
         _ = _ := by simp [b',hn']

/-- Uniform control of the tiny cluster cost gives exactly the global arithmetic
input of the rational finite Gram bound. The mean and count estimates are
required only at high zeros. All multiplicities and all lower heights are included. -/
theorem zetaCoeff_polynomial_of_microclusters {H B C E : ℝ} (hH : 1 ≤ H)
    (hHL : 2 ≤ Real.log (2+H)) (hC : 0 ≤ C)
    (hdata : ∀ w : ℂ, H ≤ |w.im| → riemannZeta w = 0 →
      let L := Real.log (2+|w.im|)
      (-(B*L)) ≤ Real.circleAverage (fun z ↦ Real.log ‖riemannZeta z‖) w (1/4) ∧
      (∀ r ∈ Icc (1/L^2) (1/4 : ℝ), zetaNeighborCount w r ≤ C*(r*L + L/Real.log L)) ∧
      zetaClusterCost w (1/L^2) ≤ E*L) :
    ∃ (A : ℕ) (b : ℝ), 0 < b ∧ ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b/(2+|w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖ := by
  obtain ⟨A, hA⟩ := exists_nat_ge (B+(9/4)*C+E)
  refine ⟨A, extend_high_zetaCoeff_bound (H := H) A (fun w ht hz n hn ↦ ?_)⟩
  let T := 2 + |w.im|
  have hT : 0 < T := by dsimp [T]; positivity
  have hL : 2 ≤ Real.log T := hHL.trans (Real.log_le_log (by linarith) (by dsimp [T]; linarith))
  obtain ⟨hmean,hcount,hclose⟩ := hdata w ht hz
  have hlog := zetaCoeff_log_lower_of_microcluster (hH.trans ht) hn hL hC hmean hcount hclose
  have hne : w ≠ 1 := by rintro rfl; norm_num at ht; linarith
  have hd := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticOn_riemannZeta w hne)).mp hn).2
  have hp : 0 < ‖taylorCoeff riemannZeta w n‖ :=
    norm_pos_iff.mpr (div_ne_zero hd (by exact_mod_cast Nat.factorial_ne_zero n))
  apply (Real.log_le_log_iff (div_pos zero_lt_one (pow_pos hT A)) hp).mp
  rw [Real.log_div one_ne_zero (pow_ne_zero _ hT.ne'), Real.log_one, Real.log_pow]
  exact (by linarith [mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ Real.log T)] :
    0 - A * Real.log T ≤ -((B+(9/4)*C+E)*Real.log T)).trans hlog

end MasulloResearch.StripJets
