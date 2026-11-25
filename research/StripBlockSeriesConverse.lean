import RiemannMasullo.Ch10_TraceSpectral.Sec3
import research.StripMellinPolynomial
import research.GramDistance

/-!
# What the block series of Theorem 10.3.2.1(1) forces on the finite Gram rows

The recorded gap `spectralStripConvolution_traceCauchy_compact_block_series` of
`Ch10_TraceSpectral/Sec3` (#7241) asks that the zero-block traces be summable
after every compact insertion. Assume this for every test and every rank-one
insertion. `spectralStripConvolution_mellin_norm_le_of_summable_rankOne_blocks`
then bounds, for each test, the Mellin value at a site times the norm of its
zeroth coordinate by the distance from that coordinate to the span of all
coordinates at the other sites. A finite Gram coordinate in a block whose other
members sit at other sites is at most the reciprocal of that distance. The
modulation argument of `StripMellinPolynomial` removes the test and leaves a
polynomial bound in the ordinate, uniform in the block.

The result holds for every number field, every strip and every norm-one
character. The blocks are those containing no second row at the site of the
selected one; rows of other characters at the same point are allowed.
-/

noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace MasulloResearch.StripBlocks

open RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " χ ", " z ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽
    (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) χ z)

variable (a : ℝ)

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

variable {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)

local notation "D" => spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)
local notation "raw(" χ ", " j ")" =>
  spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "jet(" z ", " m ")" => ⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩
local notation "J(" χ ")" => SpectralStripJetIndex (F := F) χ a α s

/-- **Rows forced by the block series.** Fix a Markushevich basis realizing the
strip jets. If the zero-block traces are summable for every compact Bruhat test
after every rank-one insertion, then for each norm-one character `η` one
polynomial in the ordinate bounds the norm of every zeroth jet of that character
times its finite Gram coordinate, over all finite blocks that contain no second
row at the site of that jet. -/
theorem spectralStrip_rankOne_blocks_require_polynomial_rows
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (η : PontryaginDual C₁)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (Λ : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (h : ∀ (φ : BruhatCompactSupport C𝔽) (v : Q(a, hStrip(hα), hs₀(hs)))
        (f : StrongDual ℂ Q(a, hStrip(hα), hs₀(hs))),
      Summable (fun z : Z(χ, α) ↦ ∑ m : Fin (N(χ, α, s, z)), Λ (jet(z, m))
        (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ
          ((f.smulRight v) (x (jet(z, m))))))) :
    let u (j : J(χ)) := (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))
    ∃ C ≥ (0 : ℝ), ∃ n : ℕ, ∀ (i : J(χ)) (S : Finset (J(χ))), i.val.1 = η → i.val.2.2.2 = 0 →
      (∀ j ∈ S, j ≠ i →
        (j.val.1, j.val.2.1, j.val.2.2.1) ≠ (i.val.1, i.val.2.1, i.val.2.2.1)) →
      ‖u i‖ * finiteGramCoordinate u i S ≤ C * (1 + |i.val.2.2.1|) ^ n := by
  classical
  intro u
  have hu : LinearIndependent ℂ u := spectralStripJet_toLp_linearIndependent χ hχ a hα hs₀(hs)
  have hD : Isometry D :=
    (spectralSobolevDualEmbedding_isometry_range (F := F) a hStrip(hα) hs₀(hs)).1
  have hnormΛ (j : J(χ)) : ‖Λ j‖ = ‖u j‖ := by
    have h1 := (AddMonoidHomClass.isometry_iff_norm D).mp hD (Λ j)
    rw [hj j] at h1
    exact h1.symm
  have hq (j : J(χ)) (S : Finset (J(χ))) : 0 ≤ finiteGramCoordinate u j S := by
    unfold finiteGramCoordinate
    split <;> positivity
  let P := {p : J(χ) × Finset (J(χ)) // p.1.val.1 = η ∧ p.1.val.2.2.2 = 0 ∧
    ∀ j ∈ p.2, j ≠ p.1 →
      (j.val.1, j.val.2.1, j.val.2.2.1) ≠ (p.1.val.1, p.1.val.2.1, p.1.val.2.2.1)}
  let b (p : P) : ℝ := p.val.1.val.2.1
  let t (p : P) : ℝ := p.val.1.val.2.2.1
  let w (p : P) : ℝ := ‖u p.val.1‖ * finiteGramCoordinate u p.val.1 p.val.2
  have hb' (p : P) : |b p| ≤ α := abs_le.mpr (p.val.1.mem_strip_order_pos hα).1
  have hw (p : P) : 0 ≤ w p := mul_nonneg (norm_nonneg _) (hq _ _)
  have htest (φ : BruhatCompactSupport C𝔽) :
      BddAbove (range fun p : P ↦ ‖nuclearityTestMellin (χ η) φ (shift(b p, t p))‖ * w p) := by
    obtain ⟨C, hC, hbound⟩ :=
      spectralStripConvolution_mellin_norm_le_of_summable_rankOne_blocks a hα hs χ x Λ hb hj φ
        (h φ)
    refine ⟨C, ?_⟩
    rintro _ ⟨⟨⟨i, S⟩, hη, hk, hadm⟩, rfl⟩
    change ‖nuclearityTestMellin (χ η) φ (shift(i.val.2.1, i.val.2.2.1))‖ *
      (‖u i‖ * finiteGramCoordinate u i S) ≤ C
    let z : Z(χ, α) := ⟨(i.val.1, i.val.2.1, i.val.2.2.1), i.mem_strip_order_pos hα⟩
    have hz : 0 < N(χ, α, s, z) := lt_of_eq_of_lt hk.symm i.property
    have hi : (jet(z, (⟨0, hz⟩ : Fin (N(χ, α, s, z)))) : J(χ)) = i :=
      Subtype.ext (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hk.symm)))
    let Pz : Submodule ℂ (StrongDual ℂ Q(a, hStrip(hα), hs₀(hs))) :=
      Submodule.span ℂ {f | ∃ (w : Z(χ, α)) (_ : w ≠ z) (m : Fin (N(χ, α, s, w))),
        f = Λ (jet(w, m))}
    have key : ‖M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ *
        ‖Λ (jet(z, (⟨0, hz⟩ : Fin (N(χ, α, s, z)))))‖ ≤
        C * Metric.infDist (Λ (jet(z, (⟨0, hz⟩ : Fin (N(χ, α, s, z)))))) (Pz : Set _) :=
      hbound z hz
    rw [hi] at key
    have hMeq : M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2)) =
        nuclearityTestMellin (χ η) φ (shift(i.val.2.1, i.val.2.2.1)) := by
      unfold modulatedFourierMellin
      rw [Set.indicator_of_mem]
      · rw [← hη]
        rfl
      · exact mem_univ (quasiCharacterAbscissa (m𝔽).toMonoidHom (hm𝔽).1 (hm𝔽).2 _)
    rw [hMeq, hnormΛ i] at key
    have hcd : finiteGramCoordinate u i S * Metric.infDist (Λ i) (Pz : Set _) ≤ 1 :=
      finiteGramCoordinate_mul_infDist_le_one (D : _ →ₗ[ℂ] _) hD Λ hj hu i S Pz
        (fun j hjS hji ↦ Submodule.subset_span
          ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), j.mem_strip_order_pos hα⟩,
            fun e ↦ hadm j hjS hji (congrArg Subtype.val e), ⟨j.val.2.2.2, j.property⟩, rfl⟩)
    have hd0 : 0 ≤ Metric.infDist (Λ i) (Pz : Set _) := Metric.infDist_nonneg
    have hmv : 0 ≤ ‖nuclearityTestMellin (χ η) φ (shift(i.val.2.1, i.val.2.2.1))‖ * ‖u i‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [← mul_assoc]
    rcases hd0.eq_or_lt with hd | hd
    · rw [← hd, mul_zero] at key
      rw [le_antisymm key hmv, zero_mul]
      exact hC.le
    · refine le_of_mul_le_mul_right ?_ hd
      calc ‖nuclearityTestMellin (χ η) φ (shift(i.val.2.1, i.val.2.2.1))‖ * ‖u i‖ *
            finiteGramCoordinate u i S * Metric.infDist (Λ i) (Pz : Set _)
          = ‖nuclearityTestMellin (χ η) φ (shift(i.val.2.1, i.val.2.2.1))‖ * ‖u i‖ *
              (finiteGramCoordinate u i S * Metric.infDist (Λ i) (Pz : Set _)) := by ring
        _ ≤ ‖nuclearityTestMellin (χ η) φ (shift(i.val.2.1, i.val.2.2.1))‖ * ‖u i‖ * 1 :=
            mul_le_mul_of_nonneg_left hcd hmv
        _ ≤ C * Metric.infDist (Λ i) (Pz : Set _) := by rw [mul_one]; exact key
  obtain ⟨C, hC, n, hbound⟩ := LineModulation.homogeneous_strip_mellin_polynomial hα χ hχ η b t w
    hb' hw (fun φ _ ↦ htest φ)
  exact ⟨C, hC, n, fun i S hη hk hadm ↦ hbound ⟨(i, S), hη, hk, hadm⟩⟩

end MasulloResearch.StripBlocks
