import research.StripBlockSeriesConverse
import research.StripTraceConverse

/-!
# The recorded gap of Theorem 10.3.2.1(1) forces the zeta coefficient criterion

Take the rational field, the line `1/2`, strip width one and any Sobolev exponent
above one. If the assertion of the recorded gap (#7241) holds for every compact
Bruhat test, the zeroth rows of the trivial character are polynomially bounded
on every finite block with no second row at their site
(`spectralStrip_compact_blocks_require_polynomial_rows`). The finite-block
Jensen obstruction and the unconditional quarter-circle mean then give a
polynomial lower bound for the first nonzero Taylor coefficient of zeta at
every zero of height at least one.
-/

noncomputable section

open Set Metric MeasureTheory NumberField RiemannMasullo
open scoped Classical BigOperators NumberField.AdeleRing
open MasulloResearch.StripJets MasulloResearch.StripBlocks

namespace MasulloResearch.StripRadial

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "J(" χ ", " s ")" => SpectralStripJetIndex χ (1/2) 1 s
local notation "point(" j ")" => shift((j).val.2.1,(j).val.2.2.1) + 1/2

/-- **The gap forces the coefficient criterion.** For a basepoint choice that is
trivial on the trivial character: if the assertion of #7241 holds at the rational
field, the line `1/2` and strip width one for every compact Bruhat test, then the
first nonzero Taylor coefficient of zeta at every zero of height at least one is
bounded below by a fixed negative power of the height. -/
theorem zetaCoeff_lower_of_compact_block_series {s : ℝ} (hs : 1 < s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (hχ1 : χ 1 = 1)
    (h : ∀ φ : BruhatCompactSupport Cℚ,
      CompactBlockSeries (F := ℚ) (1/2) zero_le_one hs χ φ) :
    ∃ (A : ℕ) (b : ℝ), 0 < b ∧ ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b/(2+|w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖ := by
  have H := spectralStrip_compact_blocks_require_polynomial_rows (F := ℚ) (1/2) zero_le_one hs
    χ hχ 1 h
  obtain ⟨C, hC, n, hrows⟩ := H
  refine rational_zeroth_gram_requires_coefficients_of_offcenter_blocks
    (le_of_lt (zero_lt_one.trans hs)) χ hχ hχ1 (K := C + 1) (by linarith) n ?_
  intro i hi hk _ S _ hadm
  have hrow := hrows i S hi hk (fun j hjS hji e ↦ hadm j hjS hji (by
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, h1, h2⟩ := e
    rw [h1, h2]))
  exact hrow.trans (mul_le_mul (by linarith)
    (pow_le_pow_left₀ (by positivity) (by linarith) n) (by positivity) (by linarith))

end MasulloResearch.StripRadial
