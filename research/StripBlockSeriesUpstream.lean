import research.StripBlockSeriesZeta
import research.StripUpstreamConsequences

/-!
# The recorded gap as stated upstream

`CompactBlockSeries` is the assertion of the private upstream theorem
`spectralStripConvolution_traceCauchy_compact_block_series` (#7241). The isolation
file restates that assertion word for word as the conclusion of
`spectralStripConvolution_traceCauchy_compact_block_series_of_summable_jetNorms`.
The first theorem checks that the two agree. The second applies the
consequence for zeta to it; it therefore depends on the open statement from
which the isolation file derives the gap.
-/

noncomputable section

open Set NumberField RiemannMasullo
open scoped NumberField.AdeleRing
open MasulloResearch.StripJets MasulloResearch.StripBlocks

namespace MasulloResearch.StripRadial

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

/-- The isolation file's copy of the gap has exactly the shape of
`CompactBlockSeries`. -/
theorem compactBlockSeries_of_isolated {F : Type*} [Field F] [NumberField F] (a : ℝ)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hχ : IsSpectralBasepointChoice χ) (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) :
    CompactBlockSeries a hα hs χ φ :=
  fun x Λ hb hj ↦
    Isolated.spectralStripConvolution_traceCauchy_compact_block_series_of_summable_jetNorms
      a χ hχ hα hs φ x Λ hb hj

/-- The zeta coefficient criterion follows from the gap as the isolation file
states it. This depends on the open statement behind that file. -/
theorem zetaCoeff_lower_of_isolated_block_series :
    ∃ (A : ℕ) (b : ℝ), 0 < b ∧ ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b/(2+|w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖ := by
  obtain ⟨χ, hχ, hχ1⟩ := exists_normalized_rational_basepoint
  exact zetaCoeff_lower_of_compact_block_series one_lt_two χ hχ hχ1
    (fun φ ↦ compactBlockSeries_of_isolated (F := ℚ) (1/2) zero_le_one one_lt_two χ hχ φ)

end MasulloResearch.StripRadial
