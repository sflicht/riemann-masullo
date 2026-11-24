import research.StripZetaGrowth
import research.StripRadialRealization

/-!
# Quantitative radial witnesses for the ordinary zeta divisor

This specializes the radial interpolation theorem to the pole-removed zeta
function with damping degree seven. Its only arithmetic hypothesis is a lower
bound on the first nonzero Taylor coefficient at each zero of height at least
one. The constructed witness retains the inverse factorial in its norm.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology Classical
open MasulloResearch.StripJets

namespace MasulloResearch.StripRadial

/-- Under a polynomial lower bound for the first nonzero ordinary zeta
coefficients, every derivative at a critical-strip zero of height at least
two has a radial cardinal witness. A single polynomial works for all
centers, multiplicities and derivative indices. -/
theorem exists_zeta_radial_witnesses {b : ℝ} (hb : 0 < b) (A : ℕ)
    (hζ : ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b / (2 + |w.im|) ^ A ≤ ‖taylorCoeff riemannZeta w n‖) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : ℂ, ρ.re ∈ Icc (0 : ℝ) 1 → 2 ≤ |ρ.im| → riemannZeta ρ = 0 →
      ∀ m : ℕ, analyticOrderAt riemannZeta ρ = m → ∀ k < m, ∀ s : ℝ,
      ∃ (p : ℝ → ℂ) (hf : MemLp p 2 (radialMeasure s)), Continuous p ∧
        ‖hf.toLp p‖ ^ 2 ≤ (K * (10 + |ρ.im|) ^ (5 * A + 25) / (2 * k.factorial)) ^ 2 *
          ∫ x, sobolevKernel s x ∧
        let M := fun v : ℂ ↦ ∫ x : ℝ, Complex.exp ((v + (ρ - 1/2)) * x) * p x
        (∀ j < m, iteratedDeriv j M 0 = if j = k then 1 else 0) ∧
          ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w ≠ ρ → w ≠ 1 →
            analyticOrderAt riemannZeta w ≤ analyticOrderAt M (w - ρ) := by
  obtain ⟨R, hR, hradii⟩ := zeta_radius_of_polynomial_coefficients hb A hζ
  obtain ⟨E, hE, henv⟩ := dampedZeta_strip_envelope
  let K := R ^ 2 * (E + 1) ^ 2 * (b⁻¹)^3 * E
  refine ⟨K, by dsimp [K]; positivity, fun ρ hρ ht hz m hm k hk s ↦ ?_⟩
  let H := 10 + |ρ.im|
  have hH : 1 ≤ H := by dsimp [H]; linarith [abs_nonneg ρ.im]
  have hHp : 0 < H := zero_lt_one.trans_le hH
  let a : ℂ := ρ - 1/2
  have ha : |a.re| ≤ 1/2 := by
    simp [a, abs_le]; constructor <;> linarith [hρ.1, hρ.2]
  have hρ1 : ρ ≠ 1 := fun e ↦ by simp [e] at ht; linarith
  let G := dampedZeta ρ 7
  let U := (E + 1) * H^5
  have hG : AnalyticOnNhd ℂ G ({(-4 : ℂ)}ᶜ) := fun v hv ↦ analyticAt_dampedZeta _ _ hv
  have hD : closedBall (0 : ℂ) 1 ⊆ {(-4 : ℂ)}ᶜ := by
    intro v hv he
    change v = -4 at he
    norm_num [he, mem_closedBall_iff_norm] at hv
  have hstrip (z : ℂ) (hzr : z.re ∈ Icc (-(3/2) : ℝ) (3/2)) : z - a ∈ ({(-4 : ℂ)}ᶜ : Set ℂ) := by
    intro he
    change z - a = -4 at he
    have := congrArg Complex.re he
    simp [a] at this
    linarith [hzr.1, hρ.2]
  have horder : analyticOrderAt G 0 = m := by
    simpa [G] using (dampedZeta_order ρ 7 (v := 0) (by norm_num) (by simpa using hρ1)).trans
      (by simpa using hm)
  have hnorm (u : ℂ) (hu : u.re ∈ Icc (-1 : ℝ) 2) :
      ‖G (u - ρ)‖ ≤ E * H^5 / (1 + (u.im - ρ.im)^2) := by
    refine (henv ρ hρ u hu).trans ?_
    gcongr
    dsimp [H]
    linarith
  have hcircle (v : ℂ) (hv : v ∈ sphere (0 : ℂ) 1) : ‖G v‖ ≤ E * H^5 := by
    have hr := abs_le.mp ((Complex.abs_re_le_norm v).trans_eq (mem_sphere_zero_iff_norm.mp hv))
    have h := hnorm (v + ρ) ⟨by simp; linarith [hr.1, hρ.1], by simp; linarith [hr.2, hρ.2]⟩
    rw [add_sub_cancel_right] at h
    exact h.trans (div_le_self (by positivity) (by nlinarith [sq_nonneg ((v + ρ).im - ρ.im)]))
  have hsmall : E * H^5 < U := by dsimp [U]; nlinarith [pow_pos hHp 5]
  have hcenter : ‖taylorCoeff G 0 m‖ ≤ E * H^5 := by
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m (by norm_num : (0 : ℝ) < 1)
      (hG.differentiableOn.diffContOnCl_ball hD) hcircle
    simp only [taylorCoeff, norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa [mul_comm] using hc
  have hlead : b / H^A ≤ ‖taylorCoeff G 0 m‖ := by
    rw [show taylorCoeff G 0 m = _ from dampedZeta_center_coeff hρ1 7 hm.ge, norm_mul]
    have hdist : 1 ≤ ‖ρ - 1‖ := by
      have := Complex.abs_im_le_norm (ρ - 1)
      simp at this
      linarith
    refine (div_le_div_of_nonneg_left hb.le (pow_pos (by positivity) A)
      (pow_le_pow_left₀ (by positivity) (show 2 + |ρ.im| ≤ H by dsimp [H]; linarith) _)).trans ?_
    exact (hζ ρ (by linarith) hz m hm).trans (le_mul_of_one_le_right (norm_nonneg _) hdist)
  obtain ⟨r, hr, hr2, hcost, hiso⟩ := hradii ρ hρ ht hz m hm
  obtain ⟨p, hf, hp, hbound, _, hjet, hvan⟩ := exists_sobolev_cardinal_jet hG a ha hD hstrip hk
    horder hr hr2 (hiso 7) (fun v hv ↦ (hcircle v hv).trans hsmall.le) (hcenter.trans_lt hsmall)
    (C := E * H^5) (by positivity) (by
      intro σ hσ y _
      let u : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I + 1/2
      have hu : u.re ∈ Icc (-1 : ℝ) 2 := by
        simp [u]; constructor <;> linarith [hσ.1, hσ.2]
      have heq : (σ : ℂ) + (y : ℂ) * Complex.I - a = u - ρ := by dsimp [u,a]; ring
      rw [heq]
      simpa [u, a, Complex.div_im, div_eq_mul_inv] using hnorm u hu) s
  refine ⟨p, hf, hp, hbound.trans ?_, hjet, fun w hw hne hw1 ↦ ?_⟩
  · have hleadpos := (div_pos hb (pow_pos hHp A)).trans_le hlead
    have hrecip : ‖taylorCoeff G 0 m‖⁻¹ ≤ b⁻¹ * H^A := by
      simpa [div_eq_mul_inv, mul_comm] using inv_anti₀ (div_pos hb (pow_pos hHp A)) hlead
    have hmul : (↑(m - k) : ℝ) ≤ R * H ^ (A+5) := by
      have htwo : (2 : ℝ)^m ≤ (r^m)⁻¹ := by
        rw [← inv_pow]
        apply pow_le_pow_left₀ (by norm_num)
        exact (le_inv_comm₀ (by norm_num) hr).2 (by linarith)
      have hm2 := Nat.lt_two_pow_self (n := m)
      calc (↑(m - k) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m k
           _ ≤ 2^m := by exact_mod_cast hm2.le
           _ ≤ _ := htwo.trans_eq hcost
    have hpoly : (↑(m - k) : ℝ) * (U^2 / ‖taylorCoeff G 0 m‖^3 / r^m) * (E * H^5) ≤
        K * H^(5*A+25) := by
      simp only [div_eq_mul_inv, ← inv_pow, hcost]
      calc
        _ ≤ (R * H^(A+5)) * (U^2 * (b⁻¹ * H^A)^3 * (R * H^(A+5))) * (E * H^5) := by
          gcongr
        _ = _ := by dsimp [K, U]; rw [show 5*A = A*5 by omega]; simp only [pow_add, pow_mul]; ring
    have hscale : (↑(m-k) : ℝ) * (U^2 / ‖taylorCoeff G 0 m‖^3 / r^m) * (E * H^5) / k.factorial / 2 ≤
        K * H^(5*A+25) / (2 * k.factorial) := by
      rw [div_div, mul_comm (k.factorial : ℝ)]
      gcongr
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hscale 2)
      (integral_nonneg fun t ↦ by unfold sobolevKernel; positivity)
  · have h4 : w - ρ ≠ -4 := by
      intro he
      have := congrArg Complex.re he
      simp at this
      linarith [hw.1, hρ.2]
    have ho := dampedZeta_order ρ 7 h4 (by simpa using hw1 : w - ρ + ρ ≠ 1)
    rw [sub_add_cancel] at ho
    rw [← ho]
    apply hvan (w - ρ) _ (sub_ne_zero.mpr hne)
    rw [show w - ρ + a = w - 1/2 by dsimp [a]; ring]
    simp [abs_lt]
    constructor <;> linarith [hw.1, hw.2]

end MasulloResearch.StripRadial
