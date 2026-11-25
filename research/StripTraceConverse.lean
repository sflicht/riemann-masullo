import research.StripGramConverse
import research.StripMellinPolynomial

/-!
# The rational component of the finite Gram sum and zeta coefficients

Sample the rightmost point of each prescribed Mellin circle and select a
single site in the outer sum. Uniform boundedness for homogeneous tests
gives polynomial bounds simultaneously for every finite Gram block. The
arithmetic criterion then follows from the finite-block Jensen obstruction.
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
local notation "Z(" χ ")" => {p : ℝ × ℝ // p.1 ∈ Icc (-1 : ℝ) 1 ∧
  0 < order(χ 1, shift(1/2 + p.1, p.2))}
local notation "N(" χ ", " s ", " z ")" => spectralStripMultiplicity 1 s (z).val.1
  (order(χ 1, shift(1/2 + (z).val.1, (z).val.2))).untop₀.toNat
local notation "J(" χ ", " s ")" => SpectralStripJetIndex χ (1/2) 1 s
local notation "raw(" χ ", " j ")" => spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

/-- The project’s finite Gram formulation of (10.3.2.7) for all compact Bruhat tests
on the rational trivial component, with every finite ambient Gram block. -/
def RationalConvolutionFiniteGramBound {s : ℝ} (hs : 0 ≤ s) (χ : PontryaginDual C₁ → PontryaginDual Cℚ) : Prop :=
  let u (i : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs i).toLp (raw(χ,i))
  let j (z : Z(χ)) (m : Fin (N(χ,s,z))) : J(χ,s) := ⟨(1,z.val.1,z.val.2,m.val),m.isLt⟩
  ∀ φ : BruhatCompactSupport Cℚ, ∃ B : ℝ, ∀ (T : Finset (Z(χ))) (w : Z(χ) → ℂ) (S : Finset (J(χ,s))),
    (∀ z ∈ T, w z ∈ sphere (shift(z.val.1,z.val.2)) (2*Real.exp ((4+s)/2))) →
    ∑ z ∈ T, ‖nuclearityTestMellin (χ 1) φ (w z)‖ *
      ∑ m, ‖u (j z m)‖ * finiteGramCoordinate u (j z m) S ≤ B

private theorem gramCoordinate_nonneg {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : ι → H) (i : ι) (S : Finset ι) : 0 ≤ finiteGramCoordinate u i S := by
  unfold finiteGramCoordinate
  split <;> positivity

/-- A singleton outer sum and one fixed point on each Mellin circle suffice
to recover polynomial growth of every coordinate, uniformly in the block. -/
theorem rational_convolution_requires_polynomial_gram {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : RationalConvolutionFiniteGramBound hs χ) :
    ∃ (K : ℝ) (p : ℕ), 0 < K ∧ ∀ i : J(χ,s), i.val.1 = 1 → ∀ S : Finset (J(χ,s)),
      let u (j : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (raw(χ,j))
      ‖u i‖ * finiteGramCoordinate u i S ≤ K * (10+|i.val.2.2.1|)^p := by
  let u (i : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs i).toLp (raw(χ,i))
  let j (z : Z(χ)) (m : Fin (N(χ,s,z))) : J(χ,s) := ⟨(1,z.val.1,z.val.2,m.val),m.isLt⟩
  let P := {i : J(χ,s) // i.val.1 = 1} × Finset (J(χ,s))
  let R := 2*Real.exp ((4+s)/2)
  let b (a : P) := a.1.val.val.2.1 + R
  let t (a : P) := a.1.val.val.2.2.1
  let Q (a : P) := ‖u a.1.val‖ * finiteGramCoordinate u a.1.val a.2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hQ (a : P) : 0 ≤ Q a := mul_nonneg (norm_nonneg _) (gramCoordinate_nonneg ..)
  have hb (a : P) : |b a| ≤ 1+R := by
    have := (a.1.val.mem_strip_order_pos (by norm_num : (0:ℝ) ≤ 1)).1
    exact (abs_add_le ..).trans (add_le_add (abs_le.mpr this) (abs_of_nonneg hR).le)
  let w (z : Z(χ)) := shift(z.val.1+R,z.val.2)
  have hw (z : Z(χ)) : w z ∈ sphere (shift(z.val.1,z.val.2)) R := by
    rw [mem_sphere,dist_eq_norm]
    rw [show w z - shift(z.val.1,z.val.2) = (R:ℂ) by dsimp [w]; push_cast; ring]
    simp [abs_of_nonneg hR]
  have htest (φ : BruhatCompactSupport Cℚ) :
      BddAbove (range (fun a : P ↦ ‖nuclearityTestMellin (χ 1) φ (shift(b a,t a))‖ * Q a)) := by
    obtain ⟨B,hB⟩ := h φ
    refine ⟨B,?_⟩
    rintro _ ⟨a,rfl⟩
    let i := a.1.val
    have hi : i.val.1 = 1 := a.1.property
    let z : Z(χ) := ⟨(i.val.2.1,i.val.2.2.1),by
      simpa only [← hi] using i.mem_strip_order_pos (by norm_num : (0:ℝ) ≤ 1)⟩
    let k : Fin (N(χ,s,z)) := ⟨i.val.2.2.2,by
      change i.val.2.2.2 < spectralStripMultiplicity 1 s i.val.2.1
        (order(χ 1,shift(1/2+i.val.2.1,i.val.2.2.1))).untop₀.toNat
      rw [← hi]; exact i.property⟩
    have hj : j z k = i := by apply Subtype.ext; exact Prod.ext hi.symm rfl
    have hsum := hB {z} w a.2 (fun z _ ↦ hw z)
    simp only [Finset.sum_singleton] at hsum
    have hone := Finset.single_le_sum (s := Finset.univ)
      (f := fun n : Fin (N(χ,s,z)) ↦ ‖u (j z n)‖ * finiteGramCoordinate u (j z n) a.2)
      (fun _ _ ↦ mul_nonneg (norm_nonneg _) (gramCoordinate_nonneg ..)) (Finset.mem_univ k)
    rw [hj] at hone
    exact (mul_le_mul_of_nonneg_left hone (norm_nonneg _)).trans hsum
  obtain ⟨K,hK,p,hbound⟩ := LineModulation.homogeneous_strip_mellin_polynomial
    (show 0 ≤ 1+R by linarith) χ hχ 1 b t Q hb hQ (fun φ _ ↦ htest φ)
  refine ⟨K+1,p,by positivity,fun i hi S ↦ ?_⟩
  have hh := hbound (⟨⟨i,hi⟩,S⟩ : P)
  exact hh.trans (mul_le_mul (by linarith) (pow_le_pow_left₀ (by dsimp [t]; positivity)
    (by dsimp [t]; linarith) p) (by positivity) (by positivity))

/-- For the rational trivial character at positive width, the full Mellin-weighted
finite Gram assertion is equivalent to polynomial lower bounds on the first
nonzero ordinary zeta coefficient at every zero of absolute height at least one. -/
theorem rational_convolution_finiteGram_iff_coefficients {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (hχ1 : χ 1 = 1) :
    RationalConvolutionFiniteGramBound hs χ ↔
      ∃ (A : ℕ) (b : ℝ), 0 < b ∧ ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
        analyticOrderAt riemannZeta w = n → b / (2+|w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖ := by
  constructor
  · intro h
    exact (rational_polynomial_gram_iff_coefficients hs χ hχ hχ1).mp
      (rational_convolution_requires_polynomial_gram hs χ hχ h)
  · rintro ⟨A,b,hb,hcoeff⟩ φ
    exact rational_convolution_finiteGram_bound hb A hcoeff hs χ hχ hχ1 φ

end MasulloResearch.StripRadial
