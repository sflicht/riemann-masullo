import research.StripTraceConverse
import RiemannMasullo.Ch10_TraceSpectral.Sec3_Isolated

/-!
# Restricting the upstream finite Gram bound to rational zeta

The first implication takes the finite Gram estimate as a hypothesis. The
last theorem applies it to the upstream declaration for the recorded gap.
-/

noncomputable section

open Set Metric MeasureTheory NumberField RiemannMasullo
open scoped Classical BigOperators NumberField.AdeleRing
open MasulloResearch.StripJets

namespace MasulloResearch.StripRadial

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" ψ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL ψ) z
local notation "Z₁(" χ ")" => {p : ℝ × ℝ // p.1 ∈ Icc (-1 : ℝ) 1 ∧
  0 < order(χ 1, shift(1/2+p.1,p.2))}
local notation "Z(" χ ")" => {p : PontryaginDual C₁ × ℝ × ℝ // p.2.1 ∈ Icc (-1 : ℝ) 1 ∧
  0 < order(χ p.1, shift(1/2+p.2.1,p.2.2))}
local notation "N(" χ ", " s ", " z ")" => spectralStripMultiplicity 1 s (z).val.2.1
  (order(χ (z).val.1, shift(1/2+(z).val.2.1,(z).val.2.2))).untop₀.toNat
local notation "J(" χ ", " s ")" => SpectralStripJetIndex χ (1/2) 1 s
local notation "raw(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

/-- A spectral basepoint choice can always use the trivial extension on the
trivial angular component. -/
theorem exists_normalized_rational_basepoint :
    ∃ χ : PontryaginDual C₁ → PontryaginDual Cℚ, IsSpectralBasepointChoice χ ∧ χ 1 = 1 := by
  obtain ⟨χ,hχ⟩ := exists_spectralBasepointChoice ℚ
  refine ⟨Function.update χ 1 1, fun ω ↦ ?_, Function.update_self ..⟩
  by_cases h : ω = 1
  · subst ω
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h]
    exact hχ ω

/-- The expression in upstream #7455 at the rational chart, with the outer
sum ranging over all angular characters. -/
def RationalAllCharacterFiniteGramBound {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) : Prop :=
  let u (i : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs i).toLp (raw(χ,i))
  let j (z : Z(χ)) (m : Fin (N(χ,s,z))) : J(χ,s) := ⟨(z.val.1,z.val.2.1,z.val.2.2,m.val),m.isLt⟩
  ∀ φ : BruhatCompactSupport Cℚ, ∃ B : ℝ, ∀ (T : Finset (Z(χ))) (w : Z(χ) → ℂ) (S : Finset (J(χ,s))),
    (∀ z ∈ T, w z ∈ sphere (shift(z.val.2.1,z.val.2.2)) (2*Real.exp ((4+s)/2))) →
    ∑ z ∈ T, ‖nuclearityTestMellin (χ z.val.1) φ (w z)‖ *
      ∑ m, ‖u (j z m)‖ * finiteGramCoordinate u (j z m) S ≤ B

/-- Restrict the outer sum and extend the sample function along the site
embedding. The test, the bound and the entire ambient block are preserved. -/
theorem rational_trivialComponent_of_allCharacters {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (h : RationalAllCharacterFiniteGramBound hs χ) :
    RationalConvolutionFiniteGramBound hs χ := by
  let e : Z₁(χ) ↪ Z(χ) := ⟨fun z ↦ ⟨(1,z.val),z.property⟩,fun a b hab ↦
    Subtype.ext (congrArg (fun z : Z(χ) ↦ z.val.2) hab)⟩
  intro φ
  obtain ⟨B,hB⟩ := h φ
  refine ⟨B,fun T w S hw ↦ ?_⟩
  let w' := Function.extend e w (fun _ ↦ 0)
  have he (z : Z₁(χ)) : w' (e z) = w z := e.injective.extend_apply ..
  have hbound := hB (T.map e) w' S (by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
    rw [he]
    exact hw a ha)
  simp only [Finset.sum_map, he] at hbound
  refine le_trans (le_of_eq ?_) hbound
  apply Finset.sum_congr rfl
  intro z _
  rfl

/-- The rational all-character assertion implies a uniform ordinary-zeta
coefficient bound. All analytic dependencies of this implication are proved. -/
theorem zetaCoeff_lower_of_allCharacter_hypothesis {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ χ, IsSpectralBasepointChoice χ → RationalAllCharacterFiniteGramBound hs χ) :
    ∃ (A : ℕ) (b : ℝ), 0 < b ∧ ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b/(2+|w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖ := by
  obtain ⟨χ,hχ,hχ1⟩ := exists_normalized_rational_basepoint
  exact (rational_convolution_finiteGram_iff_coefficients hs χ hχ hχ1).mp
    (rational_trivialComponent_of_allCharacters hs χ (h χ hχ))

/-- Applying the preceding implication to upstream's recorded #7455 gap.
This corollary inherits the upstream placeholder. -/
theorem zetaCoeff_lower_of_upstream_finiteGram_bound {s : ℝ} (hs : 1 < s) :
    ∃ (A : ℕ) (b : ℝ), 0 < b ∧ ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b/(2+|w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖ := by
  apply zetaCoeff_lower_of_allCharacter_hypothesis (zero_le_one.trans hs.le)
  intro χ hχ φ
  obtain ⟨B,hB⟩ := Isolated.spectralStripConvolution_finiteGram_bound
    (F := ℚ) (1/2) (show (0:ℝ) ≤ 1 by norm_num) hs χ hχ φ
  refine ⟨B,fun T w S hw ↦ ?_⟩
  have h := hB T w S (by simpa only [mul_one] using hw)
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro z _
  rfl

end MasulloResearch.StripRadial
