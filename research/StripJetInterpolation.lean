import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Quantitative interpolation at a multiple zero

For the positive-width zeta component of Masullo §10.3.2 (#7455), center the
complex variable at the selected zero. Write the damped divisor function as
`z ^ m * g z`, where `g` is analytic and nonzero at zero. The finite Taylor
polynomial of its reciprocal produces an interpolant whose first `m`
derivatives form a coordinate vector. The same formula gives an exterior norm
bound uniform in the derivative index, with the factor `1 / k!` kept explicit.
Theorem `exists_cardinal_interpolant` packages the construction for a divisor
with an isolated zero. Theorem `neighbor_coefficient_bound` controls the distance
to a second zero using its normalized derivative. See equation (3) of the
companion note, `strip-zeta-jet-criterion.md`.
-/

namespace MasulloResearch.StripJets

open Filter Metric
open scoped Topology

noncomputable section

/-- Taylor coefficient of the reciprocal of the regular factor. -/
def reciprocalCoeff (g : ℂ → ℂ) (j : ℕ) : ℂ :=
  iteratedDeriv j (fun z ↦ (g z)⁻¹) 0 / (j.factorial : ℂ)

/-- Taylor polynomial through degree `n - 1` of the reciprocal germ. -/
def reciprocalTrunc (g : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, z ^ j * reciprocalCoeff g j

/-- The regularized product of the divisor function with its selected principal part. -/
def cardinalJet (g : ℂ → ℂ) (m k : ℕ) (z : ℂ) : ℂ :=
  z ^ k / (k.factorial : ℂ) * g z * reciprocalTrunc g (m - k) z

private theorem analyticAt_trunc (g : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (reciprocalTrunc g n) z := by
  unfold reciprocalTrunc
  fun_prop

/-- The error of the interpolant relative to its prescribed monomial vanishes
to order at least the full multiplicity, also when the requested jet is the last one. -/
theorem cardinalJet_error_order {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (h0 : g 0 ≠ 0)
    {m k : ℕ} (hk : k < m) :
    (m : ℕ∞) ≤ analyticOrderAt
      (fun z ↦ cardinalJet g m k z - z ^ k / (k.factorial : ℂ)) 0 := by
  have ht := analyticAt_trunc g (m - k) 0
  have ha : AnalyticAt ℂ (fun z ↦ cardinalJet g m k z - z ^ k / (k.factorial : ℂ)) 0 := by
    unfold cardinalJet
    fun_prop
  obtain ⟨E, hE, hTaylor⟩ := (hg.fun_inv h0).exists_eventuallyEq_sum_add_pow_mul (m - k)
  apply (natCast_le_analyticOrderAt ha).mpr
  refine ⟨fun z ↦ -(g z * E z) / (k.factorial : ℂ), by fun_prop, ?_⟩
  filter_upwards [hTaylor, hg.continuousAt.eventually_ne h0] with z he hz
  have hrec : (g z)⁻¹ = reciprocalTrunc g (m - k) z + z ^ (m - k) * E z := by
    simpa only [reciprocalTrunc, reciprocalCoeff, smul_eq_mul, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using he
  have hprod := congrArg (fun w : ℂ ↦ g z * w) hrec
  have hpoly : g z * reciprocalTrunc g (m - k) z = 1 - z ^ (m - k) * (g z * E z) := by
    simp only [mul_inv_cancel₀ hz, mul_add] at hprod
    linear_combination -hprod
  have hpow : z ^ m = z ^ k * z ^ (m - k) := by rw [← pow_add, Nat.add_sub_of_le hk.le]
  rw [sub_zero, smul_eq_mul, cardinalJet, mul_assoc, hpoly, hpow]
  ring

/-- Every admitted derivative at the chosen zero has the prescribed value. -/
theorem cardinalJet_derivative {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (h0 : g 0 ≠ 0)
    {m k j : ℕ} (hk : k < m) (hj : j < m) :
    iteratedDeriv j (cardinalJet g m k) 0 = if j = k then 1 else 0 := by
  have ht := analyticAt_trunc g (m - k) 0
  have hH : AnalyticAt ℂ (cardinalJet g m k) 0 := by unfold cardinalJet; fun_prop
  have hp : AnalyticAt ℂ (fun z : ℂ ↦ z ^ k / (k.factorial : ℂ)) 0 := by fun_prop
  have he := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hH.fun_sub hp)).mp
    (cardinalJet_error_order hg h0 hk) j hj
  rw [iteratedDeriv_fun_sub hH.contDiffAt hp.contDiffAt, sub_eq_zero] at he
  rw [he, iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
  split_ifs <;> simp [Nat.factorial_ne_zero]

/-- Vanishing at all other sites is inherited from the divisor's regular
factor there, to every order that factor has. -/
theorem cardinalJet_preserves_order {g : ℂ → ℂ} {w : ℂ} (hg : AnalyticAt ℂ g w)
    (m k : ℕ) : analyticOrderAt g w ≤ analyticOrderAt (cardinalJet g m k) w := by
  have hp : AnalyticAt ℂ (fun z : ℂ ↦ z ^ k / (k.factorial : ℂ)) w := by fun_prop
  unfold cardinalJet
  rw [analyticOrderAt_fun_mul (hp.fun_mul hg) (analyticAt_trunc g (m - k) w),
    analyticOrderAt_fun_mul hp hg]
  exact (le_add_self).trans (le_self_add)

/-- Cauchy's estimate bounds all coefficients by the same worst radius loss. -/
theorem reciprocalCoeff_bound {g : ℂ → ℂ} {r M : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hM : 0 ≤ M) (hg : DiffContOnCl ℂ (fun z ↦ (g z)⁻¹) (ball 0 r))
    (hb : ∀ z ∈ sphere (0 : ℂ) r, ‖(g z)⁻¹‖ ≤ M) {j m : ℕ} (hj : j ≤ m) :
    ‖reciprocalCoeff g j‖ ≤ M / r ^ m := by
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr hg hb
  rw [reciprocalCoeff, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < j.factorial)).mpr
  calc
    _ ≤ j.factorial * M / r ^ j := hc
    _ ≤ j.factorial * M / r ^ m := by
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hr _)
        (pow_le_pow_of_le_one hr.le hr1 hj)
    _ = _ := by ring

/-- Outside the unit disk the interpolant costs at most one copy of the
divisor norm per coefficient, with the full inverse factorial gain. -/
theorem cardinalJet_exterior_bound {g : ℂ → ℂ} {m k : ℕ} (hk : k < m)
    {B : ℝ} (hb : ∀ j < m - k, ‖reciprocalCoeff g j‖ ≤ B)
    {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖cardinalJet g m k z‖ ≤ (m - k : ℕ) * B * ‖z ^ m * g z‖ / (k.factorial : ℝ) := by
  rw [cardinalJet, reciprocalTrunc, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _j ∈ Finset.range (m - k), B * ‖z ^ m * g z‖ / (k.factorial : ℝ) := by
      refine Finset.sum_le_sum fun j hj ↦ ?_
      have hkj : k + j ≤ m := by have := Finset.mem_range.mp hj; omega
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      calc
        _ = (‖z‖ ^ (k + j) * ‖g z‖ * ‖reciprocalCoeff g j‖) / (k.factorial : ℝ) := by
          rw [pow_add]; ring
        _ ≤ (‖z‖ ^ m * ‖g z‖ * B) / (k.factorial : ℝ) := by
          gcongr
          exact hb j (Finset.mem_range.mp hj)
        _ = _ := by ring
    _ = _ := by simp [nsmul_eq_mul, mul_div_assoc, mul_assoc]

/-- The local reciprocal bound and the isolation radius together control the entire
exterior estimate. The constants in the estimate are independent of the jet index. -/
theorem cardinalJet_exterior_of_reciprocal_bound {g : ℂ → ℂ} {m k : ℕ} (hk : k < m)
    {r M : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hM : 0 ≤ M)
    (hg : DiffContOnCl ℂ (fun z ↦ (g z)⁻¹) (ball 0 r))
    (hb : ∀ z ∈ sphere (0 : ℂ) r, ‖(g z)⁻¹‖ ≤ M) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖cardinalJet g m k z‖ ≤ (m - k : ℕ) * (M / r ^ m) * ‖z ^ m * g z‖ / (k.factorial : ℝ) :=
  cardinalJet_exterior_bound hk (fun _ hj ↦ reciprocalCoeff_bound hr hr1 hM hg hb (by omega)) hz

/-- On the half-radius disk, a zero-free analytic function satisfies
`‖1/g(z)‖ ≤ U²/‖g(0)‖³`. Apply Borel–Carathéodory to a holomorphic function with
real part `log ‖g‖` after subtracting its value at the center. -/
theorem reciprocal_halfDisk_bound {g : ℂ → ℂ} {r U : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (ball 0 (2 * r))) (hne : ∀ z ∈ ball 0 (2 * r), g z ≠ 0)
    (hU : ∀ z ∈ ball 0 (2 * r), ‖g z‖ ≤ U) (hU0 : ‖g 0‖ < U)
    {z : ℂ} (hz : ‖z‖ ≤ r) : ‖(g z)⁻¹‖ ≤ U ^ 2 / ‖g 0‖ ^ 3 := by
  have h0 : (0 : ℂ) ∈ ball 0 (2 * r) := mem_ball_self (by linarith)
  have hz' : z ∈ ball 0 (2 * r) := mem_ball_zero_iff.mpr (by linarith)
  have h0pos := norm_pos_iff.mpr (hne 0 h0)
  have hzpos := norm_pos_iff.mpr (hne z hz')
  have hUpos := h0pos.trans hU0
  have hlog : InnerProductSpace.HarmonicOnNhd (fun w ↦ Real.log ‖g w‖) (ball 0 (2 * r)) :=
    fun w hw ↦ (hg w hw).harmonicAt_log_norm (hne w hw)
  obtain ⟨F, hF, hre⟩ := hlog.exists_analyticOnNhd_ball_re_eq
  have hreal (w) (hw : w ∈ ball 0 (2 * r)) : (F w).re = Real.log ‖g w‖ := hre hw
  let A := Real.log U - Real.log ‖g 0‖
  have hA : 0 < A := sub_pos.mpr (Real.log_lt_log h0pos hU0)
  have hRe : Set.MapsTo (fun w ↦ F w - F 0) (ball 0 (2 * r)) {v : ℂ | v.re ≤ A} := by
    intro w hw
    change (F w).re - (F 0).re ≤ Real.log U - Real.log ‖g 0‖
    rw [hreal w hw, hreal 0 h0]
    exact sub_le_sub_right (Real.log_le_log (norm_pos_iff.mpr (hne w hw)) (hU w hw)) _
  have hBC := Complex.borelCaratheodory_zero hA (hF.differentiableOn.sub_const (F 0))
    hRe (by linarith : 0 < 2 * r) hz' (sub_self _)
  have hdiff : ‖F z - F 0‖ ≤ 2 * A := hBC.trans <| (div_le_iff₀ (by linarith)).mpr (by
    nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hz)])
  have hlow := Complex.re_le_norm (F 0 - F z)
  rw [norm_sub_rev, Complex.sub_re, hreal 0 h0, hreal z hz'] at hlow
  rw [norm_inv]
  apply (Real.log_le_log_iff (inv_pos.mpr hzpos) (by positivity)).mp
  rw [Real.log_inv, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  dsimp [A] at hdiff
  norm_num only [Nat.cast_ofNat]
  linarith

/-- Exterior bound using only a zero-free disk, an upper bound on the regular
factor there, and its value at the center. -/
theorem cardinalJet_exterior_of_zeroFree {g : ℂ → ℂ} {m k : ℕ} (hk : k < m)
    {r U : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hg : AnalyticOnNhd ℂ g (ball 0 (2 * r)))
    (hne : ∀ z ∈ ball 0 (2 * r), g z ≠ 0) (hU : ∀ z ∈ ball 0 (2 * r), ‖g z‖ ≤ U)
    (hU0 : ‖g 0‖ < U) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖cardinalJet g m k z‖ ≤ (m - k : ℕ) * (U ^ 2 / ‖g 0‖ ^ 3 / r ^ m) *
      ‖z ^ m * g z‖ / (k.factorial : ℝ) := by
  have hinv : DifferentiableOn ℂ (fun w ↦ (g w)⁻¹) (ball 0 (2 * r)) :=
    hg.differentiableOn.inv hne
  apply cardinalJet_exterior_of_reciprocal_bound hk hr hr1 (by positivity)
    (hinv.diffContOnCl_ball (closedBall_subset_ball (by linarith))) _ hz
  intro w hw
  exact reciprocal_halfDisk_bound hr hg hne hU hU0 (mem_sphere_zero_iff_norm.mp hw).le

/-- Remove a prescribed part of a zero, including its removable value. -/
private theorem factor_on {D : Set ℂ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F D)
    {a : ℂ} (ha : a ∈ D) {m : ℕ} (hm : (m : ℕ∞) ≤ analyticOrderAt F a) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G D ∧ ∀ z, F z = (z - a) ^ m * G z := by
  obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt (hF a ha)).mp hm
  let G := fun z ↦ if z = a then g a else F z / (z - a) ^ m
  refine ⟨G, ?_, ?_⟩
  · intro z hzD
    by_cases hz : z = a
    · subst z
      apply hg.congr
      filter_upwards [hfg] with w hw
      by_cases hw' : w = a
      · simp [G, hw']
      · simp [G, hw', hw, smul_eq_mul, sub_ne_zero.mpr hw']
    · have hzF := hF z hzD
      have hq : AnalyticAt ℂ (fun w ↦ F w / (w - a) ^ m) z := by
        fun_prop (disch := exact pow_ne_zero _ (sub_ne_zero.mpr hz))
      apply hq.congr
      filter_upwards [eventually_ne_nhds hz] with w hw using by simp [G, hw]
  · intro z
    by_cases hz : z = a
    · subst z
      simpa [G, smul_eq_mul] using hfg.self_of_nhds
    · simp [G, hz, mul_comm ((z - a) ^ m), sub_ne_zero.mpr hz]

/-- Given the divisor itself on a domain containing the closed unit disk, construct
a holomorphic interpolant with all the desired jets. The exterior estimate depends
only on the isolating radius, the first nonzero Taylor coefficient, and a bound for
the divisor on the unit circle. The domain may exclude poles of a damping factor. -/
theorem exists_cardinal_interpolant {D : Set ℂ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F D)
    (hD : closedBall (0 : ℂ) 1 ⊆ D) {k m : ℕ} (hk : k < m) (hm : analyticOrderAt F 0 = m)
    {r U : ℝ} (hr : 0 < r) (hr2 : 2 * r ≤ 1)
    (hiso : ∀ z ∈ ball 0 (2 * r), z ≠ 0 → F z ≠ 0)
    (hU : ∀ z ∈ sphere (0 : ℂ) 1, ‖F z‖ ≤ U)
    (hU0 : ‖iteratedDeriv m F 0 / (m.factorial : ℂ)‖ < U) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H D ∧
      (∀ j < m, iteratedDeriv j H 0 = if j = k then 1 else 0) ∧
      (∀ w ∈ D, w ≠ 0 → analyticOrderAt F w ≤ analyticOrderAt H w) ∧
      ∀ z ∈ D, 1 ≤ ‖z‖ → ‖H z‖ ≤ (m - k : ℕ) *
        (U ^ 2 / ‖iteratedDeriv m F 0 / (m.factorial : ℂ)‖ ^ 3 / r ^ m) *
        ‖F z‖ / (k.factorial : ℝ) := by
  have h0 := hD (mem_closedBall_self (by norm_num))
  obtain ⟨g, hg, hfg⟩ := factor_on hF h0 hm.ge
  simp only [sub_zero] at hfg
  have hg0 := hg 0 h0
  have hpow (w : ℂ) : AnalyticAt ℂ (fun z : ℂ ↦ z ^ m) w := by fun_prop
  have hcoeff : iteratedDeriv m F 0 / (m.factorial : ℂ) = g 0 := by
    rw [funext hfg, iteratedDeriv_fun_mul (hpow 0).contDiffAt hg0.contDiffAt]
    rw [Finset.sum_eq_single m]
    · rw [iteratedDeriv_fun_pow_zero]
      simp [Nat.factorial_ne_zero]
    · intro j _ hj
      rw [iteratedDeriv_fun_pow_zero]
      simp [hj]
    · simp
  have hcg : g 0 ≠ 0 := by
    have hord : analyticOrderAt g 0 = 0 := by
      rw [funext hfg, analyticOrderAt_fun_mul (hpow 0) hg0] at hm
      have hp : analyticOrderAt (fun z : ℂ ↦ z ^ m) 0 = m := by
        exact (hpow 0).analyticOrderAt_eq_natCast.mpr
          ⟨fun _ : ℂ ↦ (1 : ℂ), by fun_prop, one_ne_zero, by simp⟩
      simpa [hp] using hm
    exact hg0.analyticOrderAt_eq_zero.mp hord
  have hbD : ball (0 : ℂ) (2 * r) ⊆ D :=
    (ball_subset_ball hr2).trans (ball_subset_closedBall.trans hD)
  have hng (w) (hw : w ∈ ball 0 (2 * r)) : g w ≠ 0 := by
    by_cases h : w = 0
    · simpa [h] using hcg
    · exact right_ne_zero_of_mul (hfg w ▸ hiso w hw h)
  have hgU (w) (hw : w ∈ ball 0 (2 * r)) : ‖g w‖ ≤ U := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hg.differentiableOn.diffContOnCl_ball hD) ?_ (subset_closure (ball_subset_ball hr2 hw))
    intro v hv
    have hv' := frontier_ball_subset_sphere hv
    simpa [hfg v, norm_mul, norm_pow, mem_sphere_zero_iff_norm.mp hv'] using hU v hv'
  refine ⟨cardinalJet g m k, ?_, fun j hj ↦ cardinalJet_derivative hg0 hcg hk hj, ?_, ?_⟩
  · intro w hw
    have ht := analyticAt_trunc g (m - k) w
    have hgw := hg w hw
    unfold cardinalJet
    fun_prop
  · intro w hw hne
    rw [funext hfg, analyticOrderAt_fun_mul (hpow w) (hg w hw),
      (hpow w).analyticOrderAt_eq_zero.mpr (pow_ne_zero _ hne), zero_add]
    exact cardinalJet_preserves_order (hg w hw) m k
  · intro z _ hz
    rw [hcoeff, hfg z]
    exact cardinalJet_exterior_of_zeroFree hk hr (by linarith) (hg.mono hbD) hng hgU
      (hcoeff ▸ hU0) hz

/-- A bound on the radius-two circle at one zero controls the normalized derivative
at another zero within distance one, with the first zero's full multiplicity in the exponent. -/
theorem neighbor_coefficient_bound {F : ℂ → ℂ} (hF : ∀ z, AnalyticAt ℂ F z)
    {a b : ℂ} (hba : b ≠ a) (hd : ‖b - a‖ ≤ 1) {m n : ℕ}
    (hm : (m : ℕ∞) ≤ analyticOrderAt F a) (hn : (n : ℕ∞) ≤ analyticOrderAt F b)
    {M : ℝ} (hM : ∀ z ∈ sphere a 2, ‖F z‖ ≤ M) :
    ‖iteratedDeriv n F b / (n.factorial : ℂ)‖ ≤ M * (‖b - a‖ / 2) ^ m := by
  obtain ⟨G, hG', hFG⟩ := factor_on (D := Set.univ) (fun z _ ↦ hF z) (Set.mem_univ a) hm
  have hG (z) := hG' z (Set.mem_univ z)
  have hp : AnalyticAt ℂ (fun z ↦ (z - a) ^ m) b := by fun_prop
  have hGord : (n : ℕ∞) ≤ analyticOrderAt G b := by
    rw [funext hFG, analyticOrderAt_fun_mul hp (hG b),
      hp.analyticOrderAt_eq_zero.mpr (pow_ne_zero _ (sub_ne_zero.mpr hba)), zero_add] at hn
    exact hn
  obtain ⟨H, hH', hGH⟩ := factor_on hG' (Set.mem_univ b) hGord
  have hH (z) := hH' z (Set.mem_univ z)
  have hHd : Differentiable ℂ H := fun z ↦ (hH z).differentiableAt
  have hHball : DiffContOnCl ℂ H (ball a 2) := hHd.diffContOnCl
  have hHb : ‖H b‖ ≤ M / 2 ^ m := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hHball ?_ ?_
    · intro z hz
      have hzs := frontier_ball_subset_sphere hz
      have hza := mem_sphere_iff_norm.mp hzs
      have hzb : 1 ≤ ‖z - b‖ := by
        have hsum := norm_add_le (z - b) (b - a)
        rw [sub_add_sub_cancel] at hsum
        linarith
      have hFm := hM z hzs
      rw [hFG, hGH, norm_mul, norm_mul, norm_pow, norm_pow, hza] at hFm
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)).mpr
      calc
        ‖H z‖ * 2 ^ m = 2 ^ m * (1 * ‖H z‖) := by ring
        _ ≤ 2 ^ m * (‖z - b‖ ^ n * ‖H z‖) := by gcongr; exact one_le_pow₀ hzb
        _ ≤ M := hFm
    · apply subset_closure
      rw [mem_ball, dist_eq_norm]
      linarith
  obtain ⟨_, _, hder⟩ := iteratedDeriv_mul_pow_sub_of_analytic (R := F)
    (R₁ := fun z ↦ (z - a) ^ m * H z) (z₀ := b) (k := n) (t := 0)
    (fun z ↦ by fun_prop) (fun z ↦ by rw [hFG, hGH]; simp; ring)
  have hcoeff : iteratedDeriv n F b / (n.factorial : ℂ) = (b - a) ^ m * H b := by
    simp [hder b, Nat.factorial_ne_zero]
  rw [hcoeff, norm_mul, norm_pow, div_pow]
  calc
    _ ≤ ‖b - a‖ ^ m * (M / 2 ^ m) := mul_le_mul_of_nonneg_left hHb (by positivity)
    _ = _ := by ring

end
end MasulloResearch.StripJets
