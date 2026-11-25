import research.StripRationalTrace

/-!
# The finite Gram bound at individual simple zeta zeros

Dividing the damped zeta function by the local complex coordinate at a simple
zero gives a cardinal interpolant. Its normalization costs the reciprocal
of the derivative at that zero. Every other zero retains its full order.
-/

noncomputable section

open Filter MeasureTheory Metric NumberField Set RiemannMasullo
open scoped Classical BigOperators NumberField.AdeleRing Topology
open MasulloResearch.StripJets

namespace MasulloResearch.StripRadial

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "site(" j ")" => (((j).val.2.1 : ℝ) : ℂ) + ((j).val.2.2.1 : ℂ) * Complex.I
local notation "point(" j ")" => site(j) + 1/2
local notation "jet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

set_option maxHeartbeats 1000000 in
/-- At a simple zero the removable difference quotient has value one after
normalization. Its radial norm uses only the derivative at the selected zero. -/
theorem simple_zeta_radial_witness :
    ∃ E : ℝ, 0 < E ∧ ∀ ρ : ℂ, ρ.re ∈ Icc (0 : ℝ) 1 → 2 ≤ |ρ.im| →
      analyticOrderAt riemannZeta ρ = 1 → ∀ s : ℝ,
      ∃ (p : ℝ → ℂ) (hf : MemLp p 2 (radialMeasure s)), Continuous p ∧
        ‖hf.toLp p‖^2 ≤ (E*(10+|ρ.im|)^4 / ‖deriv riemannZeta ρ‖ / 2)^2 *
          ∫ x, sobolevKernel s x ∧
        let M := fun v : ℂ ↦ ∫ x : ℝ, Complex.exp ((v+(ρ-1/2))*x) * p x
        M 0 = 1 ∧ ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w ≠ ρ → w ≠ 1 →
          analyticOrderAt riemannZeta w ≤ analyticOrderAt M (w-ρ) := by
  obtain ⟨E,hE,henv⟩ := dampedZeta_strip_envelope
  refine ⟨6*E, by positivity, fun ρ hρ ht hm s ↦ ?_⟩
  let a := ρ - 1/2
  let F := dampedZeta ρ 7
  let H (v : ℂ) := dslope F 0 v / deriv F 0
  let T := 10 + |ρ.im|
  have hT : 0 < T := by dsimp [T]; positivity
  have h₁ : ρ ≠ 1 := by rintro rfl; norm_num at ht
  have ha : |a.re| ≤ 1/2 := by
    simp [a, abs_le]; constructor <;> linarith [hρ.1,hρ.2]
  have hF : AnalyticOnNhd ℂ F {(-4:ℂ)}ᶜ := fun v hv ↦ analyticAt_dampedZeta ρ 7 hv
  have hF₀ : F 0 = 0 := by
    apply (hF 0 (by norm_num)).analyticOrderAt_ne_zero.mp
    rw [show analyticOrderAt F 0 = 1 by simpa [F] using
      (dampedZeta_order ρ 7 (v := 0) (by norm_num) (by simpa using h₁)).trans (by simpa using hm)]
    simp
  have hder : deriv F 0 = deriv riemannZeta ρ * (ρ-1) := by
    simpa [F,taylorCoeff] using dampedZeta_center_coeff h₁ 7 (m := 1) hm.ge
  have hζ' : deriv riemannZeta ρ ≠ 0 := by
    simpa using ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
      (analyticOn_riemannZeta ρ h₁) (n := 1)).mp hm).2
  have hF' : deriv F 0 ≠ 0 := hder ▸ mul_ne_zero hζ' (sub_ne_zero.mpr h₁)
  have hH : AnalyticOnNhd ℂ H {(-4:ℂ)}ᶜ := fun v hv ↦ ((hF v hv).dslope 0).div_const
  have hdomain (z : ℂ) (hz : z.re ∈ Icc (-(3/2):ℝ) (3/2)) :
      z-a ∈ ({(-4:ℂ)}ᶜ : Set ℂ) := by
    intro he
    change z-a = -4 at he
    have := congrArg Complex.re he
    simp [a] at this
    linarith [hz.1,hρ.2]
  have hscale : E*T^5 / ‖deriv F 0‖ ≤ 6*E*T^4 / ‖deriv riemannZeta ρ‖ := by
    have hdist : T ≤ 6*‖ρ-1‖ := by
      have := Complex.abs_im_le_norm (ρ-1)
      simp at this
      dsimp [T]; linarith
    rw [hder, norm_mul, div_le_div_iff₀ (mul_pos (norm_pos_iff.mpr hζ') (norm_pos_iff.mpr (sub_ne_zero.mpr h₁)))
      (norm_pos_iff.mpr hζ')]
    nlinarith only [mul_le_mul_of_nonneg_left hdist
      (show 0 ≤ E*T^4*‖deriv riemannZeta ρ‖ by positivity)]
  let K := 6*E*T^4 / ‖deriv riemannZeta ρ‖
  obtain ⟨p,hf,hp,hbound,_,hlocal⟩ := exists_sobolev_translated hH a ha hdomain
    (K := K) (by dsimp [K]; positivity) (fun σ hσ y hv ↦ by
      let u : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I + 1/2
      let v := u-ρ
      have huv : (σ : ℂ) + (y : ℂ)*Complex.I-a = v := by dsimp [v,u,a]; ring
      rw [huv] at hv ⊢
      have hv₀ : v ≠ 0 := by rintro he; norm_num [he] at hv
      have hu : u.re ∈ Icc (-1:ℝ) 2 := by simp [u]; constructor <;> linarith [hσ.1,hσ.2]
      have he := henv ρ hρ u hu
      have hnorm : ‖F v‖ ≤ (E*T^5) * (1+(y-a.im)^2)⁻¹ := by
        simp only [F,v]
        apply he.trans
        simp [u,a,div_eq_mul_inv,T]
        gcongr
        linarith
      have heq : H v = F v / v / deriv F 0 := by
        simp [H, dslope_of_ne F hv₀, slope_def_field, hF₀]
      rw [heq, norm_div, norm_div]
      calc _ ≤ ‖F v‖ / ‖deriv F 0‖ :=
               div_le_div_of_nonneg_right (div_le_self (norm_nonneg _) hv) (norm_nonneg _)
           _ ≤ ((E*T^5) * (1+(y-a.im)^2)⁻¹) / ‖deriv F 0‖ := by gcongr
           _ = E*T^5 / ‖deriv F 0‖ * (1+(y-a.im)^2)⁻¹ := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_right hscale (by positivity)) s
  refine ⟨p,hf,hp,hbound,?_,fun w hw hne hw₁ ↦ ?_⟩
  · have he := (hlocal 0 (by simpa using ha.trans_lt (by norm_num : (1/2:ℝ) < 3/2))).self_of_nhds
    exact he.trans (show H 0 = 1 by change dslope F 0 0 / deriv F 0 = 1; rw [dslope_same, div_self hF'])
  · let v := w-ρ
    have hv : v ≠ 0 := sub_ne_zero.mpr hne
    have hband : |(v+a).re| < 3/2 := by
      rw [show v+a = w-1/2 by dsimp [v,a]; ring]
      simp [abs_lt]; constructor <;> linarith [hw.1,hw.2]
    have h₄ : v ≠ -4 := by
      intro e
      have := congrArg Complex.re e
      simp [v] at this
      linarith [hw.1,hρ.2]
    have ho := dampedZeta_order ρ 7 h₄ (by simpa [v] using hw₁ : v+ρ ≠ 1)
    rw [show v+ρ = w by dsimp [v]; ring] at ho
    have he : H =ᶠ[𝓝 v] fun z ↦ F z * (z⁻¹ * (deriv F 0)⁻¹) := by
      filter_upwards [eventually_ne_nhds hv] with z hz
      simp [H,dslope_of_ne F hz,slope_def_field,hF₀,div_eq_mul_inv,mul_assoc]
    have hg : AnalyticAt ℂ (fun z : ℂ ↦ z⁻¹ * (deriv F 0)⁻¹) v := by fun_prop (disch := exact hv)
    change _ ≤ analyticOrderAt _ v
    rw [analyticOrderAt_congr (hlocal v hband), analyticOrderAt_congr he,
      analyticOrderAt_fun_mul (hF v h₄) hg, hg.analyticOrderAt_eq_zero.mpr (mul_ne_zero (inv_ne_zero hv)
        (inv_ne_zero hF')), add_zero]
    exact ho.ge

set_option maxHeartbeats 1000000 in
/-- For every simple high zero, the normalized inverse Gram diagonal is bounded
by a fixed polynomial times the reciprocal derivative at that zero. The finite
block is any subset of the entire family, including jets at multiple zeros. -/
theorem rational_simple_gram_coordinate {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ : PontryaginDual C₁ → PontryaginDual Cℚ),
      IsSpectralBasepointChoice χ → χ 1 = 1 → ∀ i : SpectralStripJetIndex χ (1/2) 1 s,
      i.val.1 = 1 → 2 ≤ |i.val.2.2.1| → analyticOrderAt riemannZeta (point(i)) = 1 →
      ∀ S : Finset (SpectralStripJetIndex χ (1/2) 1 s),
      let u := fun j : SpectralStripJetIndex χ (1/2) 1 s ↦
        (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (jet(χ, j))
      ‖u i‖ * finiteGramCoordinate u i S ≤ C*(10+|i.val.2.2.1|)^4 / ‖deriv riemannZeta (point(i))‖ := by
  obtain ⟨D,hD,hjet⟩ := inner_strip_jet_norm_bound
  obtain ⟨E,hE,hrad⟩ := simple_zeta_radial_witness
  let μ := (normOneIdeleClassTamagawaMeasure ℚ).real univ
  let I := ∫ t, sobolevKernel s t
  have hI : 0 ≤ I := integral_nonneg fun _ ↦ by unfold sobolevKernel; positivity
  refine ⟨D*E*Real.sqrt I / (2*Real.sqrt μ), by positivity, fun χ hχ hχ1 i hi ht hsimp S ↦ ?_⟩
  intro u
  obtain ⟨hstrip,_,m,hm,hk⟩ := rational_strip_jet_order hχ1 i hi
  have h1 : m = 1 := by exact_mod_cast hm.symm.trans hsimp
  have hk₀ : i.val.2.2.2 = 0 := by omega
  have hbnd : |i.val.2.1| ≤ 1/2 := by
    simp at hstrip
    rw [abs_le]; constructor <;> linarith [hstrip.1,hstrip.2]
  have hu : ‖u i‖ ≤ D := by simpa [u,hk₀] using hjet χ (1/2) s hs i hbnd
  have him : (point(i)).im = i.val.2.2.1 := by simp
  have hc : point(i) - 1/2 = site(i) := add_sub_cancel_right ..
  obtain ⟨p,hf,hp,hnorm,hcenter,hother⟩ := hrad (point(i)) ⟨hstrip.1.le,hstrip.2.le⟩
    (by rwa [him]) hsimp s
  rw [hc] at hcenter hother
  obtain ⟨y,hny,hy⟩ := rational_physical_cardinal_of_radial χ hχ hχ1 hs i hi
    (m := 1) hsimp p hp hf (fun j hj ↦ by
      have hj₀ : j = 0 := by omega
      simpa [hj₀,hk₀] using hcenter) hother
  let T := 10+|i.val.2.2.1|
  let d := ‖deriv riemannZeta (point(i))‖
  have hT : 0 < T := by dsimp [T]; positivity
  have hd : 0 ≤ d := norm_nonneg _
  have hpbound : ‖hf.toLp p‖ ≤ (E*T^4/d/2)*Real.sqrt I := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hI]
    rw [him] at hnorm
    exact hnorm
  calc
    _ ≤ ‖u i‖ * ‖y‖ := gram_le_jet_mul_witness χ hχ hs i S y hy
    _ ≤ D * (((E*T^4/d/2)*Real.sqrt I)/Real.sqrt μ) := by
      rw [hny]
      exact mul_le_mul hu (div_le_div_of_nonneg_right hpbound (Real.sqrt_nonneg _))
        (by positivity) hD.le
    _ = _ := by change _ = _ * T^4 / d; ring

local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" ψ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL ψ) z
local notation "Z(" χ ")" => {p : ℝ × ℝ // p.1 ∈ Icc (-1 : ℝ) 1 ∧
  0 < order(χ 1, shift(1/2 + p.1, p.2))}
local notation "N(" χ ", " s ", " z ")" => spectralStripMultiplicity 1 s (z).val.1
  (order(χ 1, shift(1/2 + (z).val.1, (z).val.2))).untop₀.toNat
local notation "J(" χ ", " s ")" => SpectralStripJetIndex χ (1/2) 1 s
local notation "root(" z ")" => shift((z).val.1, (z).val.2) + 1/2

/-- Each ordinary simple zero in the critical strip contributes one retained
jet at its own ordinate on the rational trivial component. -/
theorem rational_site_of_simple_zero (χ : PontryaginDual C₁ → PontryaginDual Cℚ)
    (hχ1 : χ 1 = 1) (s : ℝ) {ρ : ℂ} (hρ : ρ.re ∈ Ioo (0:ℝ) 1)
    (hm : analyticOrderAt riemannZeta ρ = 1) :
    ∃ z : Z(χ), root(z) = ρ ∧ N(χ,s,z) = 1 := by
  let b := ρ.re - 1/2
  have hb : b ∈ Ioo (-1:ℝ) 1 := ⟨by dsimp [b]; linarith [hρ.1],by dsimp [b]; linarith [hρ.2]⟩
  have he : shift(1/2+b,ρ.im) = ρ := by apply Complex.ext <;> simp [b]
  have hne : ρ ≠ 1 := fun e ↦ hρ.2.ne ((congrArg Complex.re e).trans Complex.one_re)
  have hmer : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have ho := meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual Cℚ) hmer
    (fun w ↦ by rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta w.property]) hρ.1
  rw [(analyticOn_riemannZeta ρ hne).meromorphicOrderAt_eq, hm] at ho
  have hz : order(χ 1,shift(1/2+b,ρ.im)) = 1 := by
    rw [hχ1,he]
    simpa using ho.symm
  have hpos : 0 < order(χ 1,shift(1/2+b,ρ.im)) := hz ▸ (by decide : (0 : WithTop ℤ) < 1)
  refine ⟨⟨(b,ρ.im),⟨hb.1.le,hb.2.le⟩,hpos⟩, ?_, ?_⟩
  · apply Complex.ext <;> simp [b]
  · change spectralStripMultiplicity 1 s b _ = 1
    rw [spectralStripMultiplicity_interior hb, hz]
    rfl

set_option maxHeartbeats 1000000 in
/-- At the simple high sites with a polynomial lower derivative bound, the
weighted sum of §10.3.2 is bounded uniformly over all finite site selections,
circle samples, and principal Gram blocks of the entire jet family. -/
theorem rational_convolution_simple_finiteGram_bound {b : ℝ} (hb : 0 < b) (A : ℕ)
    {s : ℝ} (hs : 0 ≤ s) (χ : PontryaginDual C₁ → PontryaginDual Cℚ)
    (hχ : IsSpectralBasepointChoice χ) (hχ1 : χ 1 = 1) (φ : BruhatCompactSupport Cℚ) :
    let u (i : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs i).toLp (jet(χ,i))
    let j (z : Z(χ)) (m : Fin (N(χ,s,z))) : J(χ,s) := ⟨(1, z.val.1, z.val.2, m.val), m.isLt⟩
    ∃ B : ℝ, ∀ (T : Finset (Z(χ))) (w : Z(χ) → ℂ) (S : Finset (J(χ,s))),
      (∀ z ∈ T, 2 ≤ |z.val.2| ∧ analyticOrderAt riemannZeta (root(z)) = 1 ∧
        b/(2+|z.val.2|)^A ≤ ‖deriv riemannZeta (root(z))‖) →
      (∀ z ∈ T, w z ∈ Metric.sphere (shift(z.val.1,z.val.2)) (2*Real.exp ((4+s)/2))) →
      ∑ z ∈ T, ‖∫ g : Cℚ, φ.val g * ideleClassNormTwist (χ 1) (w z) g ∂ideleClassTamagawaMeasure ℚ‖ *
        ∑ m, ‖u (j z m)‖ * finiteGramCoordinate u (j z m) S ≤ B := by
  intro u j
  obtain ⟨C,hC,hgram⟩ := rational_simple_gram_coordinate hs
  apply rational_convolution_finiteGram_bound_on hs χ hχ1 φ _ (div_nonneg hC hb.le) (A+4)
  intro z hz m S
  obtain ⟨ht,hm,hd⟩ := hz
  have hh := hgram χ hχ hχ1 (j z m) rfl ht hm S
  let T := 10+|z.val.2|
  let d := ‖deriv riemannZeta (root(z))‖
  have hT : 0 < T := by dsimp [T]; positivity
  have hlow : b/T^A ≤ d := (div_le_div_of_nonneg_left hb.le (by positivity)
    (pow_le_pow_left₀ (by positivity) (show 2+|z.val.2| ≤ T by dsimp [T]; linarith) A)).trans hd
  change _ ≤ C*T^4/d at hh
  apply hh.trans
  calc C*T^4/d ≤ C*T^4/(b/T^A) :=
          div_le_div_of_nonneg_left (by positivity) (div_pos hb (pow_pos hT A)) hlow
       _ = (C/b)*T^(A+4) := by rw [pow_add]; field_simp

set_option maxHeartbeats 1000000 in
/-- Weight each simple-zero row by the magnitude of its ordinary derivative.
The resulting sum is uniformly bounded at all simple zeros of height at least
two, with no separation, density or lower derivative hypothesis. -/
theorem rational_convolution_derivative_weighted_bound
    {s : ℝ} (hs : 0 ≤ s) (χ : PontryaginDual C₁ → PontryaginDual Cℚ)
    (hχ : IsSpectralBasepointChoice χ) (hχ1 : χ 1 = 1) (φ : BruhatCompactSupport Cℚ) :
    let u (i : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs i).toLp (jet(χ,i))
    let j (z : Z(χ)) (m : Fin (N(χ,s,z))) : J(χ,s) := ⟨(1, z.val.1, z.val.2, m.val), m.isLt⟩
    ∃ B : ℝ, ∀ (T : Finset (Z(χ))) (w : Z(χ) → ℂ) (S : Finset (J(χ,s))),
      (∀ z ∈ T, 2 ≤ |z.val.2| ∧ analyticOrderAt riemannZeta (root(z)) = 1) →
      (∀ z ∈ T, w z ∈ Metric.sphere (shift(z.val.1,z.val.2)) (2*Real.exp ((4+s)/2))) →
      ∑ z ∈ T, ‖∫ g : Cℚ, φ.val g * ideleClassNormTwist (χ 1) (w z) g ∂ideleClassTamagawaMeasure ℚ‖ *
        ∑ m, (‖u (j z m)‖ * finiteGramCoordinate u (j z m) S) * ‖deriv riemannZeta (root(z))‖ ≤ B := by
  intro u j
  obtain ⟨C,hC,hgram⟩ := rational_simple_gram_coordinate hs
  apply rational_convolution_weighted_finiteGram_bound_on hs χ hχ1 φ _
    (fun z ↦ ‖deriv riemannZeta (root(z))‖) hC 4
  intro z hz m S
  obtain ⟨ht,hm⟩ := hz
  have hne : root(z) ≠ 1 := by
    intro he
    have hy := congrArg Complex.im he
    simp at hy
    simp [hy] at ht
    linarith
  have hd : 0 < ‖deriv riemannZeta (root(z))‖ := norm_pos_iff.mpr (by
    simpa using ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
      (analyticOn_riemannZeta _ hne) (n := 1)).mp hm).2)
  exact (le_div_iff₀ hd).mp (hgram χ hχ hχ1 (j z m) rfl ht hm S)

end MasulloResearch.StripRadial
