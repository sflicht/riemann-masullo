module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct

/-! # The spectral trace statements of §10.4.2 at orders between zero and one -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSpectralQuotientPolynormableSec3

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "H₀" => spectralSobolevQuotient F a hI hs
local notation "A(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs φ
local notation "Aq(" φ ")" => spectralConvolution (F := F) a hI hs φ
local notation "M(" hc ")" => modulatedCutoffOperator m𝔽
  ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logIdeleClassNorm F g))) hc
local notation "band(" R ", " ε ")" => (0 < (R : ℝ)⁻¹ + ε ∧ R⁻¹ + ε < R - ε)

variable {Λ ε : ℝ} {ρ : IdeleClassGroup (𝓞 F) F → ℝ}

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). On a strip of width zero
at order at most one, quotient convolution is nuclear.
Deviation: This special case uses the density of theta at the strict endpoint cutoff of §10.2. -/
theorem spectralStripConvolution_nuclear_of_zero_width (hwidth : α = 0) (hs₁ : s ≤ 1)
    (φ : BruhatCompactSupport C𝔽) : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  subst α
  have line (l : ℝ) (hl : l ≤ 0) (heq : l = 0) :
      IsNuclearOperator (E := spectralSobolevQuotient F a hl hs) (F := spectralSobolevQuotient F a hl hs)
        (spectralConvolution (F := F) a hl hs φ) := by
    subst l
    have hz (q : spectralSobolevQuotient F a hl hs) : q = 0 := by
      obtain ⟨v, rfl⟩ := (globalThetaSobolev F a hl hs).mkQ_surjective q
      apply (spectralSobolevQuotient_eq_zero a hl hs v).2
      rw [globalThetaSobolev_line_eq_top_of_le_one (F := F) a s hs hs₁]
      exact Submodule.mem_top
    have hA : spectralConvolution (F := F) a hl hs φ = 0 :=
      ContinuousLinearMap.ext fun _ ↦ hz _
    rw [hA]
    exact (nuclearEndomorphisms _).zero_mem
  exact line (-0) ((neg_nonpos.mpr hα).trans hα) neg_zero

/-- Classical input: the Dixmier–Malliavin factorization theorem. Every compactly supported
Bruhat test on the idele class group is a finite sum of convolutions of two such tests, for
the Tamagawa Haar measure. J. Dixmier and P. Malliavin, *Factorisations de fonctions et de
vecteurs indéfiniment différentiables*, Bull. Sci. Math. (2) 102 (1978), 307–330,
Théorème 3.1, applied on the Lie group `G₁ / K` for an open subgroup `G₁` and a compact
subgroup `K` with respect to which the test is a Bruhat test (F. Bruhat, *Distributions sur
un groupe localement compact et applications à l'étude des représentations des groupes
℘-adiques*, Bull. Soc. Math. France 89 (1961), 43–75). The library proves the case of tests
of one angular character (`spectralHomogeneousTest_convolution_factorization` in §10.3). -/
theorem bruhatCompactSupport_convolution_factorization (φ : BruhatCompactSupport C𝔽) :
    φ ∈ AddSubmonoid.closure {θ : BruhatCompactSupport C𝔽 |
      ∃ u v : BruhatCompactSupport C𝔽, θ.val = lcaConvolution μ𝔽 u.val v.val} := by
  sorry

/-- Paper: Theorem 10.4.2.1, p. 459, at orders `0 ≤ s ≤ 1`. Every compactly supported Bruhat
test acts on the strip quotient by a Hilbert–Schmidt operator.
Reconstruction: The paper does not state this. It is the estimate of the argument posted on
#7405 for the whole range. After the Mellin transform, each angular component of the quotient
is `D_s ⊖ V` for an equivalent norm `∫_{∂S} |F|² + ∬_S |F'|² (α − |σ|)^{1−s}` on the strip
`S = {|Re z| < α}`, where `V` is the space of functions that vanish at the zeros in the open
strip. That identification is `spectralStripJet_commonKernel`; at `s ≤ 1` no boundary jet
survives. A Carleson formula with a positive measure for finite Blaschke products gives an
orthonormal basis `B_{n−1} g_n` of `D_s ⊖ V`. A positivity bound for the normalized kernels
`g_n`, uniform in the measure, gives `‖Φ g_n‖² ≪ (1 + (Im ρ_n)²)^{−M}`, and the count of zeros
with multiplicity makes the sum converge.
Gap: Not proved in Lean. The argument is posted on #7405 as mathematics and was checked there
by other contributors, not by Lean; the library has no Hardy or Dirichlet-type space of the
strip in which to carry it out. Nothing in the Lean outside this file uses this statement. -/
theorem spectralStripConvolution_hilbertSchmidt_of_le_one (_hs₁ : s ≤ 1)
    (φ : BruhatCompactSupport C𝔽) : Aq(φ) ∈ hilbertSchmidtOperators H₀ H₀ := by
  sorry

/-- Convolution of tests is composition of their actions on the strip quotient. -/
private theorem spectralConvolution_lcaConvolution (θ u v : BruhatCompactSupport C𝔽)
    (h : θ.val = lcaConvolution μ𝔽 u.val v.val) : Aq(θ) = (Aq(u)).comp (Aq(v)) := by
  obtain ⟨θ', hθ', hact⟩ := bruhatRegularizedAction_convolution μ𝔽
    (hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs)
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs).choose_spec.2 u v
  obtain rfl : θ' = θ := Subtype.ext (hθ'.trans h.symm)
  ext q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change Aq(θ') ((globalThetaSobolev F a hI hs).mkQ x) =
    Aq(u) (Aq(v) ((globalThetaSobolev F a hI hs).mkQ x))
  rw [spectralConvolution_mkQ, spectralConvolution_mkQ, spectralConvolution_mkQ]
  exact congrArg _ (hact x)

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). Every compactly supported
Bruhat test acts by a nuclear convolution operator on the strip quotient.
Deviation: The theorems of §10.4.2 print `s ≥ 0`, while p. 455 assumes `s > 1` for
the section. This statement covers `0 ≤ s ≤ 1`.
Proved from the Hilbert–Schmidt statement `spectralStripConvolution_hilbertSchmidt_of_le_one`
and the Dixmier–Malliavin factorization `bruhatCompactSupport_convolution_factorization`: a
product of two Hilbert–Schmidt operators is nuclear. At width zero the statement is also
`spectralStripConvolution_nuclear_of_zero_width`. Nothing in the Lean uses this statement, and
it is not known how it connects with the rest of the proof in Lean; in the paper it is used on
pp. 459–461, 463–464, 503, 519–520. -/
theorem spectralStripConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  have hlin := spectralConvolution_isLinear (F := F) a hI hs
  induction bruhatCompactSupport_convolution_factorization φ using
    AddSubmonoid.closure_induction with
  | mem θ h =>
    obtain ⟨u, v, huv⟩ := h
    rw [spectralConvolution_lcaConvolution a hα hs θ u v huv]
    exact nuclear_hilbertSchmidt_comp
      ⟨_, spectralStripConvolution_hilbertSchmidt_of_le_one a hα hs _hs₁ u⟩
      ⟨_, spectralStripConvolution_hilbertSchmidt_of_le_one a hα hs _hs₁ v⟩
  | zero =>
    rw [hlin.map_zero]
    exact (nuclearEndomorphisms _).zero_mem
  | add x y _ _ hx hy =>
    rw [hlin.map_add]
    exact (nuclearEndomorphisms _).add_mem hx hy

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral projection after convolution is nuclear.
This follows from the open statement `spectralStripConvolution_nuclear_of_le_one` by (10.4.2.5).
Deviation: This is the part of the printed range with `0 ≤ s ≤ 1`. The operator is independent
of the cutoff. -/
theorem spectralProjection_convolution_nuclear_of_le_one (_hs₁ : s ≤ 1) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((spectralProjection (F := F) a hα hs).comp (A(φ))) :=
  spectralProjection_convolution_nuclear a hα hs φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral projection after convolution is nuclear.
Deviation: This checks the uncut conclusion on the range `1 < s` of the strip theorem. -/
theorem spectralProjection_convolution_nuclear_of_one_lt (hs₁ : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((spectralProjection (F := F) a hα hs).comp (A(φ))) :=
  RiemannMasullo.spectralProjection_convolution_nuclear_of_one_lt a hα hs₁ φ

/-- Paper: Theorem 10.4.2.1, p. 459. At each admissible cutoff, spectral truncation
after convolution is nuclear. This follows from the open `spectralStripConvolution_nuclear_of_le_one`
by composing the projected convolution with cutoff multiplication.
Deviation: The range here is `0 ≤ s ≤ 1`. The real cutoff uses the profile of Definition 9.3.3.1. -/
theorem spectralTruncatedConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (spectralTruncatedConvolution a hα hs hρ φ) :=
  spectralTruncatedConvolution_nuclear a hα hs hρ φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral truncation after convolution is nuclear.
Deviation: At `1 < s` the existing theorem applies to real cutoffs even without the inner-band inequality. -/
theorem spectralTruncatedConvolution_nuclear_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (spectralTruncatedConvolution a hα hs hρ φ) :=
  RiemannMasullo.spectralTruncatedConvolution_nuclear_of_one_lt a hα hs₁ hρ φ

/-- Paper: Theorem 10.4.2.1, p. 459. At each admissible cutoff, geometric truncation
after convolution is nuclear. Given the open `spectralStripConvolution_nuclear_of_le_one`,
this follows by subtracting the spectral summand from cutoff convolution.
Deviation: The range here is `0 ≤ s ≤ 1`, with the real cutoff of Definition 9.3.3.1. -/
theorem geometricTruncatedConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (geometricTruncatedConvolution a hα hs hρ φ) :=
  geometricTruncatedConvolution_nuclear a hα hs hρ hband φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Geometric truncation after convolution is nuclear.
Deviation: This checks the real-cutoff conclusion at `1 < s` using the strip theorem. -/
theorem geometricTruncatedConvolution_nuclear_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (geometricTruncatedConvolution a hα hs hρ φ) :=
  RiemannMasullo.geometricTruncatedConvolution_nuclear_of_one_lt a hα hs₁ hρ hband φ

local notation "traceSplit(" hρ ", " φ ")" =>
  (let T := (M(hρ)).comp (A(φ))
   let G := geometricTruncatedConvolution a hα hs hρ φ
   let S := spectralTruncatedConvolution a hα hs hρ φ
   ∃ (hT : IsNuclearOperator T) (hG : IsNuclearOperator G) (hS : IsNuclearOperator S),
     hilbertTrace (H := W) ⟨T, hT⟩ =
       hilbertTrace (H := W) ⟨G, hG⟩ + hilbertTrace (H := W) ⟨S, hS⟩)

/-- Paper: Theorem 10.4.2.1, p. 459. At an admissible cutoff the trace of cutoff convolution
is the sum of the geometric and spectral traces, as in (10.4.2.3). The open statement
`spectralStripConvolution_nuclear_of_le_one` supplies the hypothesis for the trace split.
Deviation: The order is restricted to `0 ≤ s ≤ 1` and the three nuclearity witnesses are
part of the conclusion for the real cutoff. -/
theorem truncatedConvolution_trace_split_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    traceSplit(hρ, φ) :=
  truncatedConvolution_trace_split a hα hs hρ hband φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. The nuclear trace splits as in (10.4.2.3).
Deviation: This checks the identity with real cutoffs and all three nuclearity witnesses at `1 < s`. -/
theorem truncatedConvolution_trace_split_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    traceSplit(hρ, φ) :=
  RiemannMasullo.truncatedConvolution_trace_split_of_one_lt a hα hs₁ hρ hband φ

section Limits

variable (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) (ε : ℝ → ℝ)
  (ρ : ℝ → IdeleClassGroup (𝓞 F) F → ℝ)

local notation "traceLimit(" op ")" =>
  (∃ (hq : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ))) (t : ℝ → ℂ),
    (∀ᶠ R in atTop, ∃ hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
      let T := (op) a hα hs hc φ
      ∃ hT : IsNuclearOperator T, t R = hilbertTrace (H := W) ⟨T, hT⟩) ∧
    Tendsto t atTop (𝓝 (hilbertTrace (H := H₀) ⟨Aq(φ), hq⟩)))

variable (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
  (hρ : ∀ᶠ R in atTop, IsModulatedCutoff (continuousIdeleClassNorm F) R (ε R) (ρ R) ∧ band(R, ε R))

include hε hρ

/-- Paper: Theorem 10.4.2.2, p. 460. The traces of cutoff projection after convolution tend
to the trace of convolution on the strip quotient, as in (10.4.2.9). This follows from
the open statement `spectralStripConvolution_nuclear_of_le_one`.
Deviation: At `0 ≤ s ≤ 1` this asserts quotient nuclearity along with the limit. The proof
on p. 461 uses the strip quotient. Real cutoffs and their traces need only agree with the
prescribed data eventually as the radius tends to infinity. -/
theorem spectralTruncatedConvolution_trace_tendsto_of_le_one (_hs₁ : s ≤ 1) :
    traceLimit(spectralTruncatedConvolution) := by
  have hq := spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ
  exact ⟨hq, spectralTruncatedConvolution_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.2, p. 460. The projection-after-convolution traces tend to the strip quotient trace.
Deviation: This checks the eventual real-cutoff formulation at `1 < s` with the nuclearity witness from §10.3. -/
theorem spectralTruncatedConvolution_trace_tendsto_of_one_lt (hs₁ : 1 < s) :
    traceLimit(spectralTruncatedConvolution) :=
  ⟨spectralStripConvolution_nuclear a hα hs₁ φ,
    RiemannMasullo.spectralTruncatedConvolution_trace_tendsto_of_one_lt a hα hs₁ φ ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.8, p. 463. The traces of cutoff convolution after spectral
projection tend to the strip quotient trace, as in (10.4.2.20). This follows from the
open statement `spectralStripConvolution_nuclear_of_le_one`.
Deviation: At `0 ≤ s ≤ 1` this asserts quotient nuclearity along with the limit. The real
cutoff conditions and agreement with the nuclear traces are eventual. -/
theorem spectralRestriction_trace_tendsto_of_le_one (_hs₁ : s ≤ 1) :
    traceLimit(spectralRestriction) := by
  have hq := spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ
  exact ⟨hq, spectralRestriction_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.8, p. 463. The convolution-after-projection traces tend to the strip quotient trace.
Deviation: This checks the eventual real-cutoff formulation at `1 < s` with the nuclearity witness from §10.3. -/
theorem spectralRestriction_trace_tendsto_of_one_lt (hs₁ : 1 < s) :
    traceLimit(spectralRestriction) :=
  ⟨spectralStripConvolution_nuclear a hα hs₁ φ,
    RiemannMasullo.spectralRestriction_trace_tendsto_of_one_lt a hα hs₁ φ ε ρ hε hρ⟩

end Limits

end RiemannMasullo.Isolated
