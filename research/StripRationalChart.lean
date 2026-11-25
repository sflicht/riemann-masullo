import research.StripPhysicalPairing
import research.StripZetaCardinal
import RiemannMasullo.Ch13_ZerosHecke.Targets

/-!
# Physical cardinal witnesses on the rational zeta component

At center one half and width one, every retained jet of the trivial
rational character is an interior jet of ordinary zeta. This identifies
the multiplicities used by the radial construction with the ambient indices.
-/

noncomputable section
open MeasureTheory NumberField Set RiemannMasullo
open scoped NumberField.AdeleRing Classical
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

private theorem rational_completed_zero_strip {z : ℂ}
    (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual Cℚ)) z) :
    z.re ∈ Ioo (0 : ℝ) 1 := by
  let L := continuedCompletedHeckeL (1 : PontryaginDual Cℚ)
  obtain ⟨hL, hLeq⟩ := continuedCompletedHeckeL_spec (1 : PontryaginDual Cℚ)
  have hright (w : ℂ) (hw : 0 < meromorphicOrderAt L w) : w.re < 1 := by
    rcases le_or_gt w.re 0 with h | h
    · exact h.trans_lt zero_lt_one
    · exact completedHeckeL_continuation_zeros _ _ hL hLeq h hw
  obtain ⟨ε, hε, hne, hfe⟩ := completedHeckeL_continuation_functionalEquation
    (1 : PontryaginDual Cℚ) L L hL hLeq hL (by simpa using hLeq)
  have hcomp : meromorphicOrderAt (fun w ↦ L (1 - w)) z = meromorphicOrderAt L (1 - z) := by
    simpa [Function.comp_def] using meromorphicOrderAt_comp_of_deriv_ne_zero (f := L)
      (show AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) z by fun_prop)
      (show deriv (fun w : ℂ ↦ 1 - w) z ≠ 0 by simp)
  rw [show (fun w ↦ L (1 - w)) = ε * L from funext hfe,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at hcomp
  have hl := hright (1 - z) (hcomp ▸ hz)
  rw [Complex.sub_re, Complex.one_re] at hl
  exact ⟨by linarith, hright z hz⟩

/-- A retained jet on the component with base character one lies at an ordinary
critical-strip zeta zero, with derivative index below its exact multiplicity. -/
theorem rational_strip_jet_order
    {χ : PontryaginDual C₁ → PontryaginDual Cℚ} (hχ1 : χ 1 = 1) {s : ℝ}
    (j : SpectralStripJetIndex χ (1/2) 1 s) (hj : j.val.1 = 1) :
    (point(j)).re ∈ Ioo (0 : ℝ) 1 ∧ riemannZeta (point(j)) = 0 ∧
      ∃ m : ℕ, analyticOrderAt riemannZeta (point(j)) = m ∧ j.val.2.2.2 < m := by
  let z : ℂ := point(j)
  have hz : (((1/2 : ℝ) + j.val.2.1 : ℝ) : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I = z := by
    dsimp [z]; push_cast; ring
  have hpos := (j.mem_strip_order_pos (by norm_num : (0 : ℝ) ≤ 1)).2
  rw [hj, hχ1, hz] at hpos
  obtain ⟨hl, hr⟩ := rational_completed_zero_strip hpos
  have hne : z ≠ 1 := fun h ↦ by simp [h] at hr
  have ha := analyticOn_riemannZeta z hne
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have he := meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual Cℚ)
    hm (fun w ↦ by rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta w.property]) hl
  have ht : analyticOrderAt riemannZeta (2 : ℂ) = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (riemannZeta_ne_zero_of_one_le_re (by norm_num)))
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected (x := 2)
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
      (by simp) hne (by simp [ht]))
  rw [ha.meromorphicOrderAt_eq, ← hm, ENat.map_natCast] at he
  have hindex := j.property
  have hband : j.val.2.1 ∈ Ioo (-(1 : ℝ)) 1 := by
    simp [z] at hl hr
    constructor <;> linarith
  rw [spectralStripMultiplicity_interior hband, hj, hχ1, hz, ← he] at hindex
  simp at hindex
  refine ⟨⟨hl, hr⟩, ha.analyticOrderAt_ne_zero.mp ?_, m, hm.symm, hindex⟩
  rw [← hm]
  exact_mod_cast Nat.ne_of_gt (Nat.zero_le _ |>.trans_lt hindex)

/-- Lift a radial interpolant at a rational site. Vanishing to the ordinary
zeta orders makes it orthogonal to all other retained jets on this character.
The angular lift treats all other characters. -/
theorem rational_physical_cardinal_of_radial (χ : PontryaginDual C₁ → PontryaginDual Cℚ)
    (hχ : IsSpectralBasepointChoice χ) (hχ1 : χ 1 = 1) {s : ℝ} (hs : 0 ≤ s)
    (i : SpectralStripJetIndex χ (1/2) 1 s) (hi : i.val.1 = 1)
    {m : ℕ} (hm : analyticOrderAt riemannZeta (point(i)) = m)
    (p : ℝ → ℂ) (hp : Continuous p) (hf : MemLp p 2 (radialMeasure s)) :
    let M := fun v : ℂ ↦ ∫ t : ℝ, Complex.exp ((v + site(i)) * t) * p t
    (∀ j < m, iteratedDeriv j M 0 = if j = i.val.2.2.2 then 1 else 0) →
    (∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w ≠ point(i) → w ≠ 1 →
      analyticOrderAt riemannZeta w ≤ analyticOrderAt M (w - point(i))) →
    ∃ y : CompactIntervalSobolev (ideleClassTamagawaMeasure ℚ) (logIdeleClassNorm ℚ) (-1) 1 s,
      ‖y‖ = ‖hf.toLp p‖ / Real.sqrt ((normOneIdeleClassTamagawaMeasure ℚ).real univ) ∧
      ∀ j : SpectralStripJetIndex χ (1/2) 1 s, spectralSobolevPairing y
        ((spectralStripJet_memLp χ (by norm_num : (0 : ℝ) ≤ 1) hs j).toLp (jet(χ, j))) =
        if j = i then 1 else 0 := by
  intro M hjets hothers
  exact exists_physical_cardinal_of_radial χ hχ hs i p hp hf (site(i)) (by
    intro j hω
    obtain ⟨hband, -⟩ := rational_strip_jet_order hχ1 j (hω.trans hi)
    simp at hband ⊢
    constructor <;> linarith [hband.1, hband.2]) (by
    intro j hω
    obtain ⟨hband, -, n, hn, hkn⟩ := rational_strip_jet_order hχ1 j (hω.trans hi)
    by_cases he : site(j) = site(i)
    · have hz : point(j) = point(i) := congrArg (· + 1/2) he
      rw [hz, hm] at hn
      have hnm : m = n := by exact_mod_cast hn
      rw [he, sub_self, hjets _ (hnm ▸ hkn)]
      apply if_congr _ rfl rfl
      constructor
      · intro hk
        apply Subtype.ext
        exact Prod.ext hω (Prod.ext (by simpa using congrArg Complex.re he)
          (Prod.ext (by simpa using congrArg Complex.im he) hk))
      · rintro rfl
        rfl
    · have hne : point(j) ≠ point(i) := fun h ↦ he (add_right_cancel h)
      have h1 : point(j) ≠ 1 := fun h ↦ (ne_of_lt hband.2) ((congrArg Complex.re h).trans Complex.one_re)
      have ho := hothers (point(j)) ⟨hband.1.le, hband.2.le⟩ hne h1
      rw [hn, add_sub_add_right_eq_sub] at ho
      have hoM : ((j.val.2.2.2+1 : ℕ) : ℕ∞) ≤ analyticOrderAt M (site(j) - site(i)) :=
        (by exact_mod_cast (Nat.succ_le_of_lt hkn) : ((j.val.2.2.2+1 : ℕ) : ℕ∞) ≤ (n : ℕ∞)).trans ho
      have han : AnalyticAt ℂ M (site(j) - site(i)) := by
        by_contra h
        rw [analyticOrderAt_of_not_analyticAt h] at hoM
        simp at hoM
      have hji : j ≠ i := fun e ↦ he (e ▸ rfl)
      rw [ite_eq_right hji]
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).mp hoM _ (Nat.lt_succ_self _))

/-- On the rational trivial component, a lower bound for ordinary zeta coefficients
gives physical cardinal witnesses at every retained high jet. The pairing tests
all admitted jets, including low ones and those of other characters. -/
theorem exists_rational_physical_zeta_witnesses {b : ℝ} (hb : 0 < b) (A : ℕ)
    (hζ : ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b / (2 + |w.im|) ^ A ≤ ‖taylorCoeff riemannZeta w n‖) :
    ∃ K : ℝ, 0 < K ∧ ∀ (χ : PontryaginDual C₁ → PontryaginDual Cℚ), IsSpectralBasepointChoice χ →
      χ 1 = 1 → ∀ (s : ℝ) (hs : 0 ≤ s) (i : SpectralStripJetIndex χ (1/2) 1 s),
      i.val.1 = 1 → 2 ≤ |i.val.2.2.1| →
      let u := fun j : SpectralStripJetIndex χ (1/2) 1 s ↦
        (spectralStripJet_memLp χ (by norm_num : (0 : ℝ) ≤ 1) hs j).toLp (jet(χ, j))
      ∃ y : CompactIntervalSobolev (ideleClassTamagawaMeasure ℚ) (logIdeleClassNorm ℚ) (-1) 1 s,
        (∀ j, spectralSobolevPairing y (u j) = if j = i then 1 else 0) ∧
        (normOneIdeleClassTamagawaMeasure ℚ).real univ * ‖y‖^2 ≤
          (K * (10 + |i.val.2.2.1|)^(5*A+25) / (2 * i.val.2.2.2.factorial))^2 *
            ∫ t, sobolevKernel s t ∧
        1 / ‖y‖ ≤ Metric.infDist (u i) (Submodule.span ℂ (u '' {j | j ≠ i}) : Set _) := by
  obtain ⟨K, hK, hrad⟩ := exists_zeta_radial_witnesses hb A hζ
  refine ⟨K, hK, fun χ hχ hχ1 s hs i hi ht ↦ ?_⟩
  intro u
  obtain ⟨hiStrip, hiz, m, hm, hiOrder⟩ := rational_strip_jet_order hχ1 i hi
  have him : (point(i)).im = i.val.2.2.1 := by simp
  obtain ⟨p, hf, hp, hnorm, hjets, hothers⟩ := hrad (point(i)) ⟨hiStrip.1.le, hiStrip.2.le⟩
    (by rwa [him]) hiz m hm _ hiOrder s
  have hc : point(i) - 1/2 = site(i) := add_sub_cancel_right ..
  rw [hc] at hjets hothers
  obtain ⟨y, hny, hy⟩ :=
    rational_physical_cardinal_of_radial χ hχ hχ1 hs i hi hm p hp hf hjets hothers
  refine ⟨y, hy, ?_, one_div_norm_le_jet_infDist χ (by norm_num) hs i y hy⟩
  let c := (normOneIdeleClassTamagawaMeasure ℚ).real univ
  let : CompactSpace C₁ := (ideleClassGroup_finiteness ℚ).2.1
  let : (normOneIdeleClassTamagawaMeasure ℚ).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  have hcpos : 0 < c := measureReal_univ_pos
  change c * ‖y‖ ^ 2 ≤ _
  rw [hny]
  change c * (‖hf.toLp p‖ / Real.sqrt c)^2 ≤ _
  rw [div_pow, Real.sq_sqrt hcpos.le, mul_div_cancel₀ _ hcpos.ne']
  simpa only [him] using hnorm

end MasulloResearch.StripRadial
