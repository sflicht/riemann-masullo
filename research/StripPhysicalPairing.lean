import research.StripRadialRealization
import RiemannMasullo.Ch10_TraceSpectral.Sec2

/-!
# Physical strip jet witnesses from radial Mellin data

Apply the Haar-normalized lift of §10.2 to a continuous representative in
the positive-width space of `StripRadialRealization`. The Mellin data are
in coordinates relative to an arbitrary center, as in
`exists_sobolev_cardinal_jet`. Only jets on the chosen angular component
need to lie in the open strip.
-/

noncomputable section

open MeasureTheory NumberField Set RiemannMasullo
open scoped NumberField.AdeleRing Classical

namespace MasulloResearch.StripRadial

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "site(" j ")" => (((j).val.2.1 : ℝ) : ℂ) + ((j).val.2.2.1 : ℂ) * Complex.I
local notation "jet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

/-- The scalar moment in the physical jet pairing is the derivative in the
translated coordinates of the cardinal interpolant. -/
theorem radial_moment_eq_shifted_deriv {s : ℝ} (hs : 0 ≤ s) (p : ℝ → ℂ)
    (hf : MemLp p 2 (radialMeasure s)) (center z : ℂ) (hz : z.re ∈ Ioo (-1) 1) (k : ℕ) :
    (∫ t : ℝ, (t : ℂ)^k * p t * Complex.exp (z * (t : ℂ))) =
      iteratedDeriv k (fun v : ℂ ↦ ∫ t : ℝ, Complex.exp ((v + center) * t) * p t) (z - center) := by
  have h : MemLp p 2 (intervalSobolevMeasure volume id (-1) 1 s) := hf
  let f : CompactIntervalSobolev volume id (-1) 1 s := h.toLp p
  have hd : Measurable (radialWeight s) := by unfold radialWeight; fun_prop
  have hac : volume ≪ radialMeasure s := withDensity_absolutelyContinuous'
    hd.ennreal_ofReal.aemeasurable (.of_forall fun t ↦
      (ENNReal.ofReal_pos.mpr (by unfold radialWeight; positivity : 0 < radialWeight s t)).ne')
  have hrep : (f : ℝ → ℂ) =ᵐ[volume] p := hac.ae_eq h.coeFn_toLp
  let M (w : ℂ) := ∫ t : ℝ, f t * Complex.exp (w * (t : ℂ))
  have hshift : (fun v : ℂ ↦ ∫ t : ℝ, Complex.exp ((v + center) * t) * p t) =
      fun v ↦ M (v + center) := by
    funext v
    apply integral_congr_ae
    filter_upwards [hrep] with t ht
    rw [ht, mul_comm]
  simp only [hshift, iteratedDeriv_comp_add_const, sub_add_cancel]
  refine (integral_congr_ae ?_).trans
    (scalarIntervalSobolev_iteratedDeriv_mellin (-1) 1 s hs f k z hz).2.2.symm
  filter_upwards [hrep] with t ht
  rw [ht, mul_comm ((t : ℂ)^k)]

/-- A radial Kronecker jet gives one physical biorthogonal witness, with its
exact norm. The hypothesis on derivative values only ranges over the selected
character. The conclusion ranges over every admitted ambient jet. -/
theorem exists_physical_cardinal_of_radial
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {a s : ℝ} (hs : 0 ≤ s) (i : SpectralStripJetIndex χ a 1 s)
    (p : ℝ → ℂ) (hp : Continuous p) (hf : MemLp p 2 (radialMeasure s)) (center : ℂ)
    (hinterior : ∀ j : SpectralStripJetIndex χ a 1 s, j.val.1 = i.val.1 →
      (site(j)).re ∈ Ioo (-1) 1)
    (hjets : ∀ j : SpectralStripJetIndex χ a 1 s, j.val.1 = i.val.1 →
      iteratedDeriv j.val.2.2.2 (fun v : ℂ ↦ ∫ t : ℝ, Complex.exp ((v + center) * t) * p t)
        (site(j) - center) = if j = i then 1 else 0) :
    ∃ y : CompactIntervalSobolev (ideleClassTamagawaMeasure F) (logIdeleClassNorm F) (-1) 1 s,
      ‖y‖ = ‖hf.toLp p‖ / Real.sqrt ((normOneIdeleClassTamagawaMeasure F).real univ) ∧
      ∀ j : SpectralStripJetIndex χ a 1 s, spectralSobolevPairing y
        ((spectralStripJet_memLp χ (by norm_num : (0 : ℝ) ≤ 1) hs j).toLp (jet(χ, j))) =
          if j = i then 1 else 0 := by
  obtain ⟨y, hn, hpair⟩ := spectralStripJet_exists_normalizedRadial χ hχ i.val.1
    (a := a) (by norm_num : (0 : ℝ) ≤ 1) hs p hp hf
  refine ⟨y, hn, fun j ↦ ?_⟩
  rw [hpair]
  by_cases h : j.val.1 = i.val.1
  · rw [ite_eq_left h, radial_moment_eq_shifted_deriv hs p hf center _ (hinterior j h), hjets j h]
  · have hne : j ≠ i := fun e ↦ h (e ▸ rfl)
    rw [ite_eq_right h, ite_eq_right hne]

private theorem cardinal_span_le_ker {H ι : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [DecidableEq ι] (u : ι → H) (i : ι) (e : H →ₗ[ℂ] ℂ)
    (he : ∀ j, e (u j) = if j = i then 1 else 0) :
    Submodule.span ℂ (u '' {j | j ≠ i}) ≤ LinearMap.ker e := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  exact (he j).trans (ite_eq_right hj)

private theorem one_div_le_infDist_of_vanishing {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (v : H) (S : Submodule ℂ H) (e : H →ₗ[ℂ] ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hnorm : ∀ w, ‖e w‖ ≤ ‖w‖ * D)
    (hone : e v = 1) (hS : S ≤ e.ker) :
    1 / D ≤ Metric.infDist v (S : Set H) := by
  have hpos : 0 < D := by
    apply lt_of_le_of_ne hD
    intro hz
    have h := hnorm v
    rw [hone, norm_one, ← hz, mul_zero] at h
    exact (not_le_of_gt zero_lt_one) h
  refine (Metric.le_infDist (x := v) (s := (S : Set H)) ⟨0, S.zero_mem⟩).2 ?_
  intro w hw
  rw [div_le_iff₀ hpos, dist_eq_norm]
  have hz : e w = 0 := hS hw
  have h := hnorm (v - w)
  rwa [map_sub, hone, hz, sub_zero, norm_one] at h

/-- Any physical cardinal witness bounds the same reciprocal-weight jet
distance that occurs in (10.3.2.7). The span ranges over all the other admitted jets. -/
theorem one_div_norm_le_jet_infDist
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (i : SpectralStripJetIndex χ a α s)
    (y : CompactIntervalSobolev (ideleClassTamagawaMeasure F) (logIdeleClassNorm F) (-α) α s)
    (hpair : ∀ j : SpectralStripJetIndex χ a α s, spectralSobolevPairing y
      ((spectralStripJet_memLp χ hα hs j).toLp (jet(χ, j))) = if j = i then 1 else 0) :
    let u := fun j : SpectralStripJetIndex χ a α s ↦ (spectralStripJet_memLp χ hα hs j).toLp (jet(χ, j))
    1 / ‖y‖ ≤ Metric.infDist (u i) (Submodule.span ℂ (u '' {j | j ≠ i}) : Set _) := by
  intro u
  let m := continuousIdeleClassNorm F
  have hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let T := (modulatedIntervalSobolev_dual m hm (ideleClassTamagawaMeasure F) (-α) α s
    (neg_le_self hα) hs).exists.choose
  let e := (ContinuousLinearMap.apply ℂ ℂ y).toLinearMap.comp T.symm.toLinearEquiv.toLinearMap
  have he (j : SpectralStripJetIndex χ a α s) : e (u j) = if j = i then 1 else 0 := by
    change (T.symm (u j)) y = _
    exact ((spectralSobolevPairing_dual (neg_le_self hα) hs (T.symm (u j)) y).2.trans
      (congrArg (spectralSobolevPairing y) (T.apply_symm_apply (u j)))).trans (hpair j)
  apply one_div_le_infDist_of_vanishing (u i) _ e (norm_nonneg y) _
    ((he i).trans (ite_eq_left rfl)) (cardinal_span_le_ker u i e he)
  intro v
  calc ‖e v‖ ≤ ‖T.symm v‖ * ‖y‖ := (T.symm v).le_opNorm y
       _ = ‖v‖ * ‖y‖ := by rw [T.symm.norm_map]

private theorem eq_of_component_site_order
    {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {a s : ℝ} {i j : SpectralStripJetIndex χ a 1 s}
    (hω : j.val.1 = i.val.1) (hz : site(j) = site(i)) (hk : j.val.2.2.2 = i.val.2.2.2) : j = i := by
  apply Subtype.ext
  exact Prod.ext hω (Prod.ext (by simpa using congrArg Complex.re hz)
    (Prod.ext (by simpa using congrArg Complex.im hz) hk))

local notation "J" => Icc (-(3 / 2) : ℝ) (3 / 2)
local notation "line" => (fun (σ t : ℝ) ↦ (σ : ℂ) + (t : ℂ) * Complex.I)

/-- From bounds on a local divisor and its orders at the admitted sites to a
physical cardinal witness and a lower bound for the distance from all other
jets. The norm estimate keeps the inverse factorial for the selected jet. -/
theorem exists_physical_cardinal_of_divisor
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {a s : ℝ} (hs : 0 ≤ s) (i : SpectralStripJetIndex χ a 1 s)
    {G : ℂ → ℂ} {D : Set ℂ} (hG : AnalyticOnNhd ℂ G D)
    (hi : |(site(i)).re| ≤ 1 / 2) (hdisk : Metric.closedBall (0 : ℂ) 1 ⊆ D)
    (hstrip : ∀ z : ℂ, z.re ∈ J → z - site(i) ∈ D)
    {m : ℕ} (hk : i.val.2.2.2 < m) (hm : analyticOrderAt G 0 = m)
    {r U : ℝ} (hr : 0 < r) (hr2 : 2 * r ≤ 1)
    (hiso : ∀ v ∈ Metric.ball 0 (2 * r), v ≠ 0 → G v ≠ 0)
    (hU : ∀ v ∈ Metric.sphere (0 : ℂ) 1, ‖G v‖ ≤ U)
    (hU0 : ‖iteratedDeriv m G 0 / (m.factorial : ℂ)‖ < U)
    {C : ℝ} (hC : 0 ≤ C) (hdiv : ∀ σ ∈ J, ∀ t : ℝ, 1 ≤ ‖line σ t - site(i)‖ →
      ‖G (line σ t - site(i))‖ ≤ C * (1 + (t - (site(i)).im) ^ 2)⁻¹)
    (hinterior : ∀ j : SpectralStripJetIndex χ a 1 s, j.val.1 = i.val.1 → (site(j)).re ∈ Ioo (-1) 1)
    (horders : ∀ j : SpectralStripJetIndex χ a 1 s, j.val.1 = i.val.1 →
      ((j.val.2.2.2 + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt G (site(j) - site(i))) :
    let k := i.val.2.2.2
    let K := (m - k : ℕ) * (U ^ 2 / ‖iteratedDeriv m G 0 / (m.factorial : ℂ)‖ ^ 3 / r ^ m) *
      C / (k.factorial : ℝ)
    let u := fun j : SpectralStripJetIndex χ a 1 s ↦
      (spectralStripJet_memLp χ (by norm_num : (0 : ℝ) ≤ 1) hs j).toLp (jet(χ, j))
    ∃ y : CompactIntervalSobolev (ideleClassTamagawaMeasure F) (logIdeleClassNorm F) (-1) 1 s,
      (∀ j, spectralSobolevPairing y (u j) = if j = i then 1 else 0) ∧
      ((normOneIdeleClassTamagawaMeasure F).real univ) * ‖y‖ ^ 2 ≤ (K / 2) ^ 2 * ∫ t, sobolevKernel s t ∧
      1 / ‖y‖ ≤ Metric.infDist (u i) (Submodule.span ℂ (u '' {j | j ≠ i}) : Set _) := by
  intro k K u
  obtain ⟨p, hf, hp, hb, -, hjet, hv⟩ :=
    exists_sobolev_cardinal_jet hG (site(i)) hi hdisk hstrip hk hm hr hr2 hiso hU hU0 hC hdiv s
  let M (v : ℂ) := ∫ t : ℝ, Complex.exp ((v + site(i)) * t) * p t
  obtain ⟨y, hn, hy⟩ := exists_physical_cardinal_of_radial χ hχ hs i p hp hf (site(i)) hinterior (by
    intro j hω
    have ho := horders j hω
    by_cases hz : site(j) = site(i)
    · rw [hz, sub_self, hm] at ho
      have hj : j.val.2.2.2 < m := Nat.lt_of_succ_le (by exact_mod_cast ho)
      rw [hz, sub_self, hjet _ hj]
      exact if_congr ⟨eq_of_component_site_order hω hz, fun e ↦ e ▸ rfl⟩ rfl rfl
    · have hdiff := sub_ne_zero.mpr hz
      have hband : |((site(j) - site(i)) + site(i)).re| < 3 / 2 := by
        rw [sub_add_cancel]
        exact (abs_lt.mpr (hinterior j hω)).trans (by norm_num)
      have hoM : ((j.val.2.2.2 + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt M (site(j) - site(i)) :=
        ho.trans (hv _ hband hdiff)
      have han : AnalyticAt ℂ M (site(j) - site(i)) := by
        by_contra hn
        rw [analyticOrderAt_of_not_analyticAt hn] at hoM
        simp at hoM
      have hne : j ≠ i := fun e ↦ hz (e ▸ rfl)
      rw [ite_eq_right hne]
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).mp hoM _ (Nat.lt_succ_self _))
  refine ⟨y, hy, ?_, one_div_norm_le_jet_infDist χ (by norm_num) hs i y hy⟩
  let c := (normOneIdeleClassTamagawaMeasure F).real univ
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hc : 0 < c := measureReal_univ_pos
  change c * ‖y‖ ^ 2 ≤ _
  rw [hn]
  change c * (‖hf.toLp p‖ / Real.sqrt c) ^ 2 ≤ _
  rwa [div_pow, Real.sq_sqrt hc.le, mul_div_cancel₀ _ hc.ne']

end MasulloResearch.StripRadial
