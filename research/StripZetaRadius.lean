import research.StripJetInterpolation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# An isolating radius from local zeta coefficients

At a zero of order `m`, the radius-two circle bounds the central coefficient
by Cauchy's inequality and the neighboring coefficients by the two-zero
estimate. Together these estimates give an isolating radius with a specified
`m`th power. Apply them to the entire pole-removed Riemann zeta function.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace MasulloResearch.StripJets

/-- The normalized derivative used in both the interpolation and two-zero estimates. -/
def taylorCoeff (f : ℂ → ℂ) (z : ℂ) (m : ℕ) : ℂ :=
  iteratedDeriv m f z / (m.factorial : ℂ)

/-- Exact radius cost for a positive lower bound on first nonzero coefficients.
The bounds concern the center and the zeros in its unit neighborhood. -/
theorem exists_isolating_radius_of_coefficients {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    (a : ℂ) {m : ℕ} (hm : 0 < m) (ho : analyticOrderAt f a = m)
    {B M : ℝ} (hB : 0 < B) (hc : B ≤ ‖taylorCoeff f a m‖)
    (hsup : ∀ z ∈ sphere a 2, ‖f z‖ ≤ M)
    (hlocal : ∀ b ∈ ball a 1, b ≠ a → f b = 0 → ∃ n : ℕ,
      (n : ℕ∞) ≤ analyticOrderAt f b ∧ B ≤ ‖taylorCoeff f b n‖) :
    ∃ r : ℝ, 0 < r ∧ 2 * r ≤ 1 ∧ r ^ m = B / M ∧
      ∀ b ∈ ball a (2 * r), b ≠ a → f b ≠ 0 := by
  have hfac : (0 : ℝ) < m.factorial := by positivity
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hder := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m
    (by norm_num : (0 : ℝ) < 2) ((show Differentiable ℂ f from fun z ↦ (hf z).differentiableAt).diffContOnCl)
    hsup
  have hcoef : ‖taylorCoeff f a m‖ ≤ M / 2 ^ m := by
    simp only [taylorCoeff, norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hfac).mpr
    calc ‖iteratedDeriv m f a‖ ≤ _ := hder
         _ = M / 2 ^ m * m.factorial := by ring
  have hprod := (le_div_iff₀ hpow).mp (hc.trans hcoef)
  have hM : 0 < M := (mul_pos hB hpow).trans_le hprod
  let r : ℝ := (B / M) ^ (m : ℝ)⁻¹
  have hr : 0 < r := Real.rpow_pos_of_pos (div_pos hB hM) _
  have hrm : r ^ m = B / M := Real.rpow_inv_natCast_pow (div_pos hB hM).le hm.ne'
  have hr2 : 2 * r ≤ 1 := by
    apply (pow_le_pow_iff_left₀ (by positivity) zero_le_one hm.ne').mp
    rw [mul_pow, hrm, one_pow, ← mul_div_assoc, div_le_one hM]
    simpa only [mul_comm] using hprod
  refine ⟨r, hr, hr2, hrm, fun b hb hba hzero ↦ ?_⟩
  have hd := mem_ball_iff_norm.mp hb
  obtain ⟨n, hn, hc'⟩ := hlocal b (ball_subset_ball hr2 hb) hba hzero
  have hle := hc'.trans (neighbor_coefficient_bound hf hba (hd.le.trans hr2) ho.ge hn hsup)
  have hlt : (‖b - a‖ / 2) ^ m < r ^ m :=
    (pow_lt_pow_iff_left₀ (by positivity) hr.le hm.ne').mpr (by linarith)
  rw [hrm] at hlt
  exact (not_lt_of_ge hle) (by simpa [mul_div_cancel₀ _ hM.ne'] using
    (mul_lt_mul_of_pos_left hlt hM))

/-- Riemann's zeta function with its pole filled using its residue. -/
def poleRemovedZeta : ℂ → ℂ := Function.update (fun w ↦ (w - 1) * riemannZeta w) 1 1

theorem analyticAt_poleRemovedZeta (z : ℂ) : AnalyticAt ℂ poleRemovedZeta z := by
  have hoff {w : ℂ} (hw : w ≠ 1) : AnalyticAt ℂ poleRemovedZeta w := by
    apply ((show AnalyticAt ℂ (fun u : ℂ ↦ u - 1) w by fun_prop).mul
      (analyticOn_riemannZeta w hw)).congr
    filter_upwards [eventually_ne_nhds hw] with u hu
    simp [poleRemovedZeta, Function.update_of_ne hu]
  rcases eq_or_ne z 1 with rfl | hz
  · apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with w hw using (hoff hw).differentiableAt
    · simpa only [poleRemovedZeta, continuousAt_update_same] using riemannZeta_residue_one
  · exact hoff hz

/-- When the lower derivatives vanish, only the value of the multiplier
contributes to the leading coefficient of the product. -/
theorem taylorCoeff_mul_at_order {f g : ℂ → ℂ} {w : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f w) (hg : AnalyticAt ℂ g w) (ho : (m : ℕ∞) ≤ analyticOrderAt f w) :
    taylorCoeff (fun z ↦ f z * g z) w m = taylorCoeff f w m * g w := by
  have hv := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp ho
  unfold taylorCoeff
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, Finset.sum_eq_single m]
  · simp
    ring
  · intro j hj hjm
    have hj' : j < m := by have := Finset.mem_range.mp hj; omega
    rw [hv j hj']
    simp
  · simp

theorem poleRemovedZeta_order {w : ℂ} (hw : w ≠ 1) :
    analyticOrderAt poleRemovedZeta w = analyticOrderAt riemannZeta w := by
  have he : poleRemovedZeta =ᶠ[𝓝 w] fun z ↦ (z - 1) * riemannZeta z := by
    filter_upwards [eventually_ne_nhds hw] with z hz using Function.update_of_ne hz _ _
  have hreg : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) w := by fun_prop
  rw [analyticOrderAt_congr he, analyticOrderAt_fun_mul hreg (analyticOn_riemannZeta w hw),
    hreg.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hw), zero_add]

theorem poleRemovedZeta_taylorCoeff {w : ℂ} (hw : w ≠ 1) {m : ℕ}
    (ho : (m : ℕ∞) ≤ analyticOrderAt riemannZeta w) :
    taylorCoeff poleRemovedZeta w m = taylorCoeff riemannZeta w m * (w - 1) := by
  have he : poleRemovedZeta =ᶠ[𝓝 w] fun z ↦ riemannZeta z * (z - 1) := by
    filter_upwards [eventually_ne_nhds hw] with z hz
    simp [poleRemovedZeta, Function.update_of_ne hz, mul_comm]
  exact (congrArg (· / (m.factorial : ℂ)) (he.iteratedDeriv_eq m)).trans
    (taylorCoeff_mul_at_order (analyticOn_riemannZeta w hw) (by fun_prop) ho)

/-- The centered divisor with the rational damping used for Mellin inversion. -/
def dampedZeta (ρ : ℂ) (L : ℕ) (v : ℂ) : ℂ :=
  poleRemovedZeta (v + ρ) * ((1 + v / 4) ^ L)⁻¹

private theorem damping_ne_zero {v : ℂ} (hv : v ≠ -4) : 1 + v / 4 ≠ 0 := by
  intro he
  apply hv
  linear_combination 4 * he

theorem analyticAt_dampedZeta (ρ : ℂ) (L : ℕ) {v : ℂ} (hv : v ≠ -4) :
    AnalyticAt ℂ (dampedZeta ρ L) v := by
  have hshift : AnalyticAt ℂ (fun w : ℂ ↦ w + ρ) v := by fun_prop
  exact ((analyticAt_poleRemovedZeta _).comp hshift).mul
    ((show AnalyticAt ℂ (fun w : ℂ ↦ (1 + w / 4) ^ L) v by fun_prop).inv
      (pow_ne_zero _ (damping_ne_zero hv)))

theorem dampedZeta_order (ρ : ℂ) (L : ℕ) {v : ℂ} (hv : v ≠ -4) (hw : v + ρ ≠ 1) :
    analyticOrderAt (dampedZeta ρ L) v = analyticOrderAt riemannZeta (v + ρ) := by
  let f := fun w : ℂ ↦ w + ρ
  let g := fun w : ℂ ↦ ((1 + w / 4) ^ L)⁻¹
  have hf : AnalyticAt ℂ f v := by dsimp [f]; fun_prop
  have h0 := pow_ne_zero L (damping_ne_zero hv)
  have hg : AnalyticAt ℂ g v := (show AnalyticAt ℂ (fun w : ℂ ↦ (1 + w / 4) ^ L) v by
    fun_prop).inv h0
  change analyticOrderAt (fun w ↦ (poleRemovedZeta ∘ f) w * g w) v = _
  rw [analyticOrderAt_fun_mul ((analyticAt_poleRemovedZeta _).comp hf) hg,
    hg.analyticOrderAt_eq_zero.mpr (inv_ne_zero h0), add_zero,
    analyticOrderAt_comp_of_deriv_ne_zero hf (by simp [f]), poleRemovedZeta_order hw]

theorem dampedZeta_center_coeff {ρ : ℂ} (hρ : ρ ≠ 1) (L : ℕ) {m : ℕ}
    (ho : (m : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    taylorCoeff (dampedZeta ρ L) 0 m = taylorCoeff riemannZeta ρ m * (ρ - 1) := by
  let f := fun w : ℂ ↦ w + ρ
  let g := fun w : ℂ ↦ ((1 + w / 4) ^ L)⁻¹
  have hf : AnalyticAt ℂ f 0 := by dsimp [f]; fun_prop
  have hg : AnalyticAt ℂ g 0 := (show AnalyticAt ℂ (fun w : ℂ ↦ (1 + w / 4) ^ L) 0 by
    fun_prop).inv (by simp)
  have hs : analyticOrderAt (poleRemovedZeta ∘ f) 0 = analyticOrderAt riemannZeta ρ := by
    rw [analyticOrderAt_comp_of_deriv_ne_zero hf (by simp [f])]
    simpa [f] using poleRemovedZeta_order hρ
  change taylorCoeff (fun w ↦ (poleRemovedZeta ∘ f) w * g w) 0 m = _
  rw [taylorCoeff_mul_at_order ((analyticAt_poleRemovedZeta _).comp hf) hg (ho.trans_eq hs.symm)]
  simp only [g, zero_div, add_zero, one_pow, inv_one, mul_one]
  change iteratedDeriv m (fun w ↦ poleRemovedZeta (w + ρ)) 0 / (m.factorial : ℂ) = _
  simp only [iteratedDeriv_comp_add_const, zero_add]
  exact poleRemovedZeta_taylorCoeff hρ ho

/-- At height at least two a lower bound on the first nonzero *ordinary zeta*
coefficient at every zero in the unit disk supplies the radius for every
damping degree. The factor `|w-1|` from removing the pole is at least one
throughout that disk. The same radius works for all the jets at the center. -/
theorem exists_dampedZeta_radius {ρ : ℂ} (ht : 2 ≤ |ρ.im|) (hzero : riemannZeta ρ = 0)
    {m : ℕ} (hm : analyticOrderAt riemannZeta ρ = m)
    {B M : ℝ} (hB : 0 < B) (hM : ∀ w ∈ sphere ρ 2, ‖poleRemovedZeta w‖ ≤ M)
    (hcoeff : ∀ w ∈ closedBall ρ 1, riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → B ≤ ‖taylorCoeff riemannZeta w n‖) :
    ∃ r : ℝ, 0 < r ∧ 2 * r ≤ 1 ∧ r ^ m = B / M ∧
      ∀ L : ℕ, ∀ v ∈ ball (0 : ℂ) (2 * r), v ≠ 0 → dampedZeta ρ L v ≠ 0 := by
  have hdist {w : ℂ} (hw : w ∈ closedBall ρ 1) : 1 ≤ ‖w - 1‖ := by
    have hdiff : |ρ.im - w.im| ≤ 1 := by
      rw [abs_sub_comm]
      exact (Complex.abs_im_le_norm (w - ρ)).trans (mem_closedBall_iff_norm.mp hw)
    have habs := (abs_sub_abs_le_abs_sub ρ.im w.im).trans hdiff
    have : 1 ≤ |w.im| := by linarith
    exact this.trans (by simpa using Complex.abs_im_le_norm (w - 1))
  have hne {w : ℂ} (hw : w ∈ closedBall ρ 1) : w ≠ 1 := by
    intro he
    have := hdist hw
    norm_num [he] at this
  have hcentral : ρ ∈ closedBall ρ 1 := mem_closedBall_self (by norm_num)
  have hb {w : ℂ} (hw : w ∈ closedBall ρ 1) (hz : riemannZeta w = 0)
      {n : ℕ} (hn : analyticOrderAt riemannZeta w = n) : B ≤ ‖taylorCoeff poleRemovedZeta w n‖ := by
    rw [poleRemovedZeta_taylorCoeff (hne hw) hn.ge, norm_mul]
    exact (hcoeff w hw hz n hn).trans (le_mul_of_one_le_right (norm_nonneg _) (hdist hw))
  have hmpos : 0 < m := by
    by_contra! h
    have hz : analyticOrderAt riemannZeta ρ = 0 := by simpa [Nat.eq_zero_of_le_zero h] using hm
    exact ((analyticOn_riemannZeta ρ (hne hcentral)).analyticOrderAt_eq_zero.mp hz) hzero
  have hfinite (w : ℂ) : analyticOrderAt poleRemovedZeta w ≠ ⊤ := by
    apply (show AnalyticOnNhd ℂ poleRemovedZeta univ from fun v _ ↦ analyticAt_poleRemovedZeta v)
      |>.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ (1 : ℂ)) (mem_univ w)
    rw [(analyticAt_poleRemovedZeta 1).analyticOrderAt_eq_zero.mpr (by simp [poleRemovedZeta])]
    exact ENat.zero_ne_top
  obtain ⟨r, hr, hr2, hcost, hiso⟩ := exists_isolating_radius_of_coefficients analyticAt_poleRemovedZeta
    ρ hmpos ((poleRemovedZeta_order (hne hcentral)).trans hm) hB (hb hcentral hzero hm) hM (by
      intro w hw _ hz
      have hw' := ball_subset_closedBall hw
      have hzw : riemannZeta w = 0 := by
        rw [poleRemovedZeta, Function.update_of_ne (hne hw')] at hz
        exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (hne hw'))
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfinite w)
      have hnat : analyticOrderAt poleRemovedZeta w = n := hn.symm
      exact ⟨n, hnat.ge, hb hw' hzw ((poleRemovedZeta_order (hne hw')).symm.trans hnat)⟩)
  refine ⟨r, hr, hr2, hcost, fun L v hv hv0 ↦ ?_⟩
  have hv' := mem_ball_zero_iff.mp hv
  have h4 : v ≠ -4 := by
    intro h
    rw [h] at hv'
    norm_num at hv'
    linarith
  apply mul_ne_zero _ (inv_ne_zero (pow_ne_zero _ (damping_ne_zero h4)))
  apply hiso (v + ρ)
  · simpa [mem_ball_iff_norm] using hv'
  · simpa using hv0

end MasulloResearch.StripJets
