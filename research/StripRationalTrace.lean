import research.StripGramEstimate
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4

/-!
# The conditional rational component of the Mellin-weighted finite Gram bound

The circle radius is the radius prescribed in §10.3.2. Rapid Mellin decay on
a fixed wider vertical strip absorbs the polynomial cost of each jet. The
classical summable zero count carries the entire multiplicity at each site.
-/

noncomputable section
open Filter MeasureTheory NumberField Set RiemannMasullo
open scoped NumberField.AdeleRing Classical BigOperators
open MasulloResearch.StripJets

namespace MasulloResearch.StripRadial

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "zetaχ" => (1 : PontryaginDual Cℚ)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" ψ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL ψ) z
local notation "Z(" χ ")" => {p : ℝ × ℝ // p.1 ∈ Icc (-1 : ℝ) 1 ∧
  0 < order(χ 1, shift(1/2 + p.1, p.2))}
local notation "N(" χ ", " s ", " z ")" => spectralStripMultiplicity 1 s (z).val.1
  (order(χ 1, shift(1/2 + (z).val.1, (z).val.2))).untop₀.toNat
local notation "J(" χ ", " s ")" => SpectralStripJetIndex χ (1/2) 1 s
local notation "raw(" χ ", " j ")" => spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

/-- Uniform rapid decay on any fixed-radius circle centered in the unit strip,
measured at the ordinate of its center. -/
private theorem rational_mellin_circle_bound (φ : BruhatCompactSupport Cℚ) (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z w : ℂ, |z.re| ≤ 1 → w ∈ Metric.sphere z R →
      ‖nuclearityTestMellin zetaχ φ w‖ * (10+|z.im|)^n ≤ L := by
  obtain ⟨C, hC, hd⟩ := spectralNuclearity_trace_vertical_decay zetaχ φ (-(1+R)) (1+R) (by linarith) n hn
  obtain ⟨t, ht⟩ := eventually_atTop.mp (eventually_comap.mp hd)
  let T := max t 1
  have hT : 1 ≤ T := le_max_right ..
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0:ℂ) (1+R+T)).exists_bound_of_continuousOn
    (nuclearityTestMellin_differentiable zetaχ φ).continuous.continuousOn
  refine ⟨max (C*(11+R)^n) (B*(10+T+R)^n), (by positivity : 0 ≤ C*(11+R)^n).trans (le_max_left ..),
    fun z w hz hw ↦ ?_⟩
  have hdist : ‖w-z‖ = R := by simpa only [Metric.mem_sphere, dist_eq_norm] using hw
  have hre := (Complex.abs_re_le_norm (w-z)).trans_eq hdist
  have him := (Complex.abs_im_le_norm (w-z)).trans_eq hdist
  change |w.re-z.re| ≤ R at hre
  change |w.im-z.im| ≤ R at him
  have hwr : |w.re| ≤ 1+R := by
    calc |w.re| = |(w.re-z.re)+z.re| := by rw [sub_add_cancel]
         _ ≤ _ := (abs_add_le _ _).trans (by linarith)
  have hzi : |z.im| ≤ |w.im|+R := by
    calc |z.im| = |w.im-(w.im-z.im)| := by rw [sub_sub_cancel]
         _ ≤ _ := (abs_sub _ _).trans (by linarith)
  by_cases hy : T ≤ |w.im|
  · have h1 := hT.trans hy
    have hh := ht _ ((le_max_left t 1).trans hy) w.im rfl w.re (abs_le.mp hwr)
    rw [Complex.re_add_im] at hh
    have hypos : 0 < |w.im| := zero_lt_one.trans_le h1
    have hp : 10+|z.im| ≤ (11+R)*|w.im| := by nlinarith [mul_nonneg hR (sub_nonneg.mpr h1)]
    apply le_trans _ (le_max_left ..)
    calc _ ≤ (C / |w.im|^n) * (((11+R)*|w.im|)^n) := by gcongr
         _ = _ := by rw [mul_pow]; field_simp
  · have hwK : w ∈ Metric.closedBall (0:ℂ) (1+R+T) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (Complex.norm_le_abs_re_add_abs_im w).trans (by linarith [lt_of_not_ge hy])
    apply le_trans _ (le_max_right ..)
    exact mul_le_mul (hB w hwK) (pow_le_pow_left₀ (by positivity) (by linarith [lt_of_not_ge hy]) _)
      (by positivity) ((norm_nonneg _).trans (hB w hwK))

/-- The quadratic divisor weight is summable over the actual sites on the
rational trivial component, counting their retained derivative orders. -/
private theorem rational_site_count (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ1 : χ 1 = 1) (s : ℝ) :
    Summable (fun z : Z(χ) ↦ (N(χ,s,z) : ℝ) / (1+|z.val.2|)^2) := by
  let L := continuedCompletedHeckeL zetaχ
  let d := MeromorphicOn.divisor L univ
  let w (z : Z(χ)) : ℂ := shift(1/2 + z.val.1,z.val.2)
  obtain ⟨hL, hLe⟩ := continuedCompletedHeckeL_spec zetaχ
  have hfin (v : ℂ) : meromorphicOrderAt L v ≠ ⊤ := by
    apply hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ (2:ℂ)) (mem_univ v)
    intro h
    have h2 : 0 < order(zetaχ,(2:ℂ)) := by rw [h]; exact WithTop.coe_lt_top (0:ℤ)
    have := completedHeckeL_continuation_zeros _ _ hL hLe (by norm_num : 0 < (2:ℂ).re) h2
    norm_num at this
  have hd (z : Z(χ)) : d (w z) = (order(χ 1,w z)).untop₀ := by
    rw [hχ1]
    exact hL.meromorphicOn.divisor_apply (mem_univ _)
  have hp (z : Z(χ)) : 0 < d (w z) := by
    have h := z.property.2
    change 0 < order(χ 1, w z) at h
    rw [hχ1, ← WithTop.coe_untop₀_of_ne_top (hfin (w z))] at h
    rw [hd, hχ1]
    exact_mod_cast h
  let X := {v : ℂ // 0 < d v ∧ |v.re - 1/2| < (2:ℝ)}
  let e (z : Z(χ)) : X := ⟨w z, hp z, by
    simp [w, abs_lt]; constructor <;> linarith [z.property.1.1, z.property.1.2]⟩
  have hei : Function.Injective e := by
    intro x y h
    have hw : w x = w y := congrArg Subtype.val h
    apply Subtype.ext
    exact Prod.ext (by simpa [w] using congrArg Complex.re hw) (by simpa [w] using congrArg Complex.im hw)
  have hsum := (spectralNuclearity_trace_zero_count zetaχ 2).comp_injective hei
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun z ↦ ?_) hsum
  change (N(χ,s,z) : ℝ) / _ ≤ (d (w z) : ℝ) / (1+|(w z).im|)^2
  rw [show (w z).im = z.val.2 by simp [w]]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hle (n : ℕ) : spectralStripMultiplicity 1 s z.val.1 n ≤ n := by
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity
    split_ifs <;> omega
  have hh := hle (d (w z)).toNat
  rw [hd] at hh
  exact (by exact_mod_cast hh : (N(χ,s,z) : ℝ) ≤ ((order(χ 1,w z)).untop₀.toNat : ℝ)).trans_eq
    (by rw [← hd]; exact_mod_cast Int.toNat_of_nonneg (hp z).le)

set_option maxHeartbeats 1600000 in
/-- A polynomial bound on weighted coordinates at selected sites gives the
Mellin-weighted sum over those sites, uniformly in the full ambient Gram block. -/
theorem rational_convolution_weighted_finiteGram_bound_on {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ1 : χ 1 = 1) (φ : BruhatCompactSupport Cℚ)
    (P : Z(χ) → Prop) (weight : Z(χ) → ℝ) {C : ℝ} (hC : 0 ≤ C) (p : ℕ) :
    let u (i : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs i).toLp (raw(χ,i))
    let j (z : Z(χ)) (m : Fin (N(χ,s,z))) : J(χ,s) := ⟨(1, z.val.1, z.val.2, m.val), m.isLt⟩
    (∀ z, P z → ∀ m : Fin (N(χ,s,z)), ∀ S : Finset (J(χ,s)),
      (‖u (j z m)‖ * finiteGramCoordinate u (j z m) S) * weight z ≤ C*(10+|z.val.2|)^p) →
    ∃ B : ℝ, ∀ (T : Finset (Z(χ))) (w : Z(χ) → ℂ) (S : Finset (J(χ,s))),
      (∀ z ∈ T, P z) →
      (∀ z ∈ T, w z ∈ Metric.sphere (shift(z.val.1,z.val.2)) (2*Real.exp ((4+s)/2))) →
      ∑ z ∈ T, ‖∫ g : Cℚ, φ.val g * ideleClassNormTwist (χ 1) (w z) g ∂ideleClassTamagawaMeasure ℚ‖ *
        ∑ m, (‖u (j z m)‖ * finiteGramCoordinate u (j z m) S) * weight z ≤ B := by
  intro u j hGram
  let R := 2*Real.exp ((4+s)/2)
  obtain ⟨L,hL,hcircle⟩ := rational_mellin_circle_bound φ R (by dsimp [R]; positivity) (p+2) (by omega)
  let f (z : Z(χ)) : ℝ := (N(χ,s,z) : ℝ) / (1+|z.val.2|)^2
  have hf : Summable f := rational_site_count χ hχ1 s
  refine ⟨(C*L) * ∑' z, f z, fun T w S hT hw ↦ ?_⟩
  calc
    _ ≤ ∑ z ∈ T, (C*L) * f z := by
      apply Finset.sum_le_sum
      intro z hz
      let H := 10+|z.val.2|
      let q := ‖nuclearityTestMellin zetaχ φ (w z)‖
      have hq : 0 ≤ q := norm_nonneg _
      have hH : 0 < H := by dsimp [H]; positivity
      have hM := hcircle (shift(z.val.1,z.val.2)) (w z) (by simpa [abs_le] using z.property.1) (hw z hz)
      have hpow : q * H^(p+2) ≤ L := by simpa [q,H] using hM
      have hsum : ∑ m : Fin (N(χ,s,z)), (‖u (j z m)‖ * finiteGramCoordinate u (j z m) S) * weight z ≤
          (N(χ,s,z) : ℝ) * (C*H^p) := by
        calc _ ≤ ∑ _m : Fin (N(χ,s,z)), C*H^p :=
                Finset.sum_le_sum fun m _ ↦ hGram z (hT z hz) m S
             _ = _ := by simp
      have heval : ‖∫ g : Cℚ, φ.val g * ideleClassNormTwist (χ 1) (w z) g ∂ideleClassTamagawaMeasure ℚ‖ = q := by
        rw [hχ1]; rfl
      rw [heval]
      apply (mul_le_mul_of_nonneg_left hsum hq).trans
      have hsmall : (1+|z.val.2|)^2 ≤ H^2 := by dsimp [H]; gcongr; norm_num
      have hscaled : q * H^p * (1+|z.val.2|)^2 ≤ L :=
        (mul_le_mul_of_nonneg_left hsmall (mul_nonneg hq (pow_nonneg hH.le _))).trans
          (by rwa [mul_assoc, ← pow_add])
      change q * ((N(χ,s,z) : ℝ) * (C*H^p)) ≤ (C*L) * ((N(χ,s,z) : ℝ) / (1+|z.val.2|)^2)
      rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
      calc _ = (C * (N(χ,s,z) : ℝ)) * (q * H^p * (1+|z.val.2|)^2) := by ring
           _ ≤ _ := by
             rw [mul_right_comm C L]
             exact mul_le_mul_of_nonneg_left hscaled (mul_nonneg hC (Nat.cast_nonneg _))
    _ = (C*L) * ∑ z ∈ T, f z := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hf.sum_le_tsum T fun z _ ↦ by dsimp [f]; positivity)
      (mul_nonneg hC hL)

set_option maxHeartbeats 1600000 in
/-- A polynomial coordinate bound on selected sites gives the Mellin-weighted
sum over those sites, uniformly in the full ambient Gram block. -/
theorem rational_convolution_finiteGram_bound_on {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ1 : χ 1 = 1) (φ : BruhatCompactSupport Cℚ)
    (P : Z(χ) → Prop) {C : ℝ} (hC : 0 ≤ C) (p : ℕ) :
    let u (i : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs i).toLp (raw(χ,i))
    let j (z : Z(χ)) (m : Fin (N(χ,s,z))) : J(χ,s) := ⟨(1, z.val.1, z.val.2, m.val), m.isLt⟩
    (∀ z, P z → ∀ m : Fin (N(χ,s,z)), ∀ S : Finset (J(χ,s)),
      ‖u (j z m)‖ * finiteGramCoordinate u (j z m) S ≤ C*(10+|z.val.2|)^p) →
    ∃ B : ℝ, ∀ (T : Finset (Z(χ))) (w : Z(χ) → ℂ) (S : Finset (J(χ,s))),
      (∀ z ∈ T, P z) →
      (∀ z ∈ T, w z ∈ Metric.sphere (shift(z.val.1,z.val.2)) (2*Real.exp ((4+s)/2))) →
      ∑ z ∈ T, ‖∫ g : Cℚ, φ.val g * ideleClassNormTwist (χ 1) (w z) g ∂ideleClassTamagawaMeasure ℚ‖ *
        ∑ m, ‖u (j z m)‖ * finiteGramCoordinate u (j z m) S ≤ B := by
  intro u j hGram
  simpa only [mul_one] using rational_convolution_weighted_finiteGram_bound_on hs χ hχ1 φ P
    (fun _ ↦ 1) hC p (fun z hz m S ↦ by simpa only [mul_one] using hGram z hz m S)

set_option maxHeartbeats 1600000 in
/-- Theorem 10.3.2.1(1), pp. 453–455, rational trivial component of #7455.
Under the first-coefficient hypothesis, one constant bounds the Mellin-weighted
sum over every finite set of sites, every choice of points on the prescribed
circles, and every principal Gram block of the full ambient jet family. -/
theorem rational_convolution_finiteGram_bound {b : ℝ} (hb : 0 < b) (A : ℕ)
    (hζ : ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b / (2 + |w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖)
    {s : ℝ} (hs : 0 ≤ s) (χ : PontryaginDual C₁ → PontryaginDual Cℚ)
    (hχ : IsSpectralBasepointChoice χ) (hχ1 : χ 1 = 1) (φ : BruhatCompactSupport Cℚ) :
    let u (i : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs i).toLp (raw(χ,i))
    let j (z : Z(χ)) (m : Fin (N(χ,s,z))) : J(χ,s) := ⟨(1, z.val.1, z.val.2, m.val), m.isLt⟩
    ∃ B : ℝ, ∀ (T : Finset (Z(χ))) (w : Z(χ) → ℂ) (S : Finset (J(χ,s))),
      (∀ z ∈ T, w z ∈ Metric.sphere (shift(z.val.1,z.val.2)) (2*Real.exp ((4+s)/2))) →
      ∑ z ∈ T, ‖∫ g : Cℚ, φ.val g * ideleClassNormTwist (χ 1) (w z) g ∂ideleClassTamagawaMeasure ℚ‖ *
        ∑ m, ‖u (j z m)‖ * finiteGramCoordinate u (j z m) S ≤ B := by
  intro u j
  obtain ⟨C,hC,hGram⟩ := rational_finiteGram_polynomial hb A hζ hs χ hχ hχ1
  obtain ⟨B,hB⟩ := rational_convolution_finiteGram_bound_on hs χ hχ1 φ (fun _ ↦ True)
    hC.le (6*A+30) (fun z _ m S ↦ hGram (j z m) rfl S)
  exact ⟨B, fun T w S ↦ hB T w S (by simp)⟩

end MasulloResearch.StripRadial
