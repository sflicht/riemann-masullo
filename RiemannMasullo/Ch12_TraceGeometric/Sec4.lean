module

public import RiemannMasullo.Ch12_TraceGeometric.Sec2
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.WeightedIntegral
public import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
public import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Unique
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import RiemannMasullo.ForMathlib.Topology.Covering.AddCircle
public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import RiemannMasullo.Ch06_LocalGlobal.Sec1
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import all RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.ForMathlib.Algebra.Module.ZLattice.Summable
import RiemannMasullo.ForMathlib.Analysis.Fourier.Translation
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.WeightedIntegral
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Unique
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.InfiniteAdeleRing
import RiemannMasullo.ForMathlib.Topology.Covering.AddCircle

/-! # S-local trace calculation

Masullo, §§12.3–12.4, pp. 514–519. The additive kernel, its sharp orbital mass,
and the diagonal integral on the idele quotient use different measures.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff ENNReal NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

-- TODO(paper-gap): §12.3, p. 514, contains only the heading and footnote 1
-- asking to include the section. No global-to-S-local comparison is stated.

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Hₛ" => sProjectedDiagonal F S
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion F S g) : C𝔽)
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ w.mult) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "volume₁" => ((sLocalNormOneQuotientMeasure F S) univ).toReal
local notation "ψₛ" => sAdeleStandardCharacter F S
local notation "fourierₛ" => tamagawaFourier νₛ ψₛ
local notation "band(" L ")" => sLocalPWProductRegion (F := F) S L
local notation "testₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "testAt(" f "," x ")" => (f : testₛ) (Multiplicative.ofAdd x)

local instance instSIdeleT2Sec4 : T2Space Iₛ := (sIdeleGroup_description F S).2.1

/-- The insertion of a projected diagonal S-unit differs from its principal idele
by an integral unit outside S. -/
private theorem sLocalTraceRestriction_invariant
    (φ : BruhatCompactSupport C𝔽)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (ξ : Hₛ) (g : Iₛ) :
    φ.val (classAtS(ξ.val * g)) = φ.val (classAtS(g)) := by
  obtain ⟨v, hv⟩ := ξ
  rw [sProjectedDiagonal, MonoidHom.map_range] at hv
  obtain ⟨u, rfl⟩ := hv
  let d := Units.map (integralAdeleDiagonal F S).toMonoidHom u
  let i := (integralAdelesOutside F S).subtype
  let a := Units.map i.toMonoidHom d
  let s := Units.map ((adeleProjection F S).comp i).toMonoidHom d
  let j := sIdeleInsertion F S s
  let o := a * j⁻¹
  obtain ⟨harch, hin, hout⟩ := sIdeleInsertion_apply F S s
  have hinv (w : V) (hw : w ∉ S) : (j⁻¹).val.2 w = 1 := by
    rw [← map_inv]
    exact (sIdeleInsertion_apply F S s⁻¹).2.2 w hw
  have hmem : o ∈ outsideIntegralIdeleUnits F S := by
    rw [mem_outsideIntegralIdeleUnits_iff]
    refine ⟨?_, ?_, ?_⟩
    · have h : a.val.1 = j.val.1 := harch.symm
      change a.val.1 * (j⁻¹).val.1 = 1
      rw [h]
      exact congrArg Prod.fst j.val_inv
    · intro w hw
      have h : a.val.2 w = j.val.2 w := (hin ⟨w, hw⟩).symm
      change a.val.2 w * (j⁻¹).val.2 w = 1
      rw [h]
      exact congrArg (fun x : AdeleRing (𝓞 F) F ↦ x.2 w) j.val_inv
    · intro w hw
      have h₁ := d.val.property
      have h₂ := d.inv.property
      simp only [integralAdelesOutside, Subring.mem_iInf] at h₁ h₂
      constructor
      · change a.val.2 w * (j⁻¹).val.2 w ∈ _
        rw [hinv w hw, mul_one]
        exact h₁ w hw
      · change (a * j⁻¹)⁻¹ |>.val.2 w ∈ _
        rw [mul_inv_rev, inv_inv]
        change j.val.2 w * (a⁻¹).val.2 w ∈ _
        rw [hout w hw, one_mul]
        exact h₂ w hw
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  have ha : q a = 1 := (QuotientGroup.eq_one_iff a).mpr
    ⟨Units.map ((S : Set V).integer F).val.toRingHom.toMonoidHom u, Units.ext rfl⟩
  have ho : q o * q j = 1 := by rw [← map_mul, show o * j = a by simp [o], ha]
  change φ.val (q (sIdeleInsertion F S (s * g))) = φ.val (q (sIdeleInsertion F S g))
  rw [map_mul, map_mul]
  have h := hOutside ⟨o, hmem⟩ (q j * q (sIdeleInsertion F S g))
  change φ.val (q o * (q j * q (sIdeleInsertion F S g))) = _ at h
  rw [← mul_assoc, ho, one_mul] at h
  exact h.symm

/-- Pullback by a continuous homomorphism preserves Bruhat smoothness. -/
private theorem sLocalTrace_comp_bruhatSmooth {G H : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (f : G →ₜ* H) {r : H → ℂ} (hr : IsBruhatSmooth r) :
    IsBruhatSmooth (r ∘ f) := by
  intro p
  obtain ⟨l, hl, hinv, hdesc⟩ := hr p
  obtain ⟨L, hL⟩ := exists_openCompactlyGeneratedSubgroup_contains hl.isCompact
  let a₀ : BruhatStructuralPair H := ⟨(L.val, OrderDual.toDual l), L.property.1, L.property.2, hl, hL⟩
  obtain ⟨k, hk, hkl⟩ := exists_good_subgroup_image_in_kernel f a₀
  change k.map f.toMonoidHom ≤ l at hkl
  refine ⟨k, hk, ?_, ?_⟩
  · intro t x
    exact (congrArg (fun y ↦ r y) (map_mul f t.val x)).trans
      (hinv ⟨f t.val, hkl ⟨t.val, t.property, rfl⟩⟩ (f x))
  · intro a ha
    obtain ⟨C, _, hc, hgen⟩ := a.property.2.1
    obtain ⟨M, hM⟩ := exists_openCompactlyGeneratedSubgroup_contains
      ((hc.image (f.continuous.comp continuous_subtype_val)).union hl.isCompact)
    have hsub : C ⊆ (M.val.comap (f.toMonoidHom.comp a.val.1.subtype) : Set a.val.1) :=
      fun x hx ↦ hM (Or.inl ⟨x, hx, rfl⟩)
    have htop : ⊤ ≤ M.val.comap (f.toMonoidHom.comp a.val.1.subtype) :=
      hgen ▸ (Subgroup.closure_le _).mpr hsub
    let b : BruhatStructuralPair H := ⟨(M.val, OrderDual.toDual l),
      M.property.1, M.property.2, hl, fun x hx ↦ hM (Or.inr hx)⟩
    let i : a.val.1 →* b.val.1 := (f.toMonoidHom.comp a.val.1.subtype).codRestrict M.val
      (fun x ↦ htop (Subgroup.mem_top x))
    let j : a.quotient →* b.quotient :=
      QuotientGroup.map _ _ i (fun x hx ↦ hkl ⟨x.val, ha ▸ hx, rfl⟩)
    have hi : Continuous i := (f.continuous.comp continuous_subtype_val).subtype_mk _
    have hj : Continuous j := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp hi)
    obtain ⟨r₀, hr₀, hsm⟩ := hdesc b rfl
    obtain ⟨e'⟩ := b.elementary
    refine ⟨r₀ ∘ j, fun x ↦ hr₀ (i x), fun e z d ↦ ?_⟩
    let P := AddMonoidHom.toMultiplicative.symm
      (e'.equiv.toMulEquiv.toMonoidHom.comp (j.comp e.equiv.symm.toMulEquiv.toMonoidHom))
    have hP : Continuous P := e'.equiv.continuous.comp (hj.comp e.equiv.symm.continuous)
    let φ := fun y ↦ r₀ (e'.equiv.symm (Multiplicative.ofAdd y))
    have hs := contDiff_comp_elementaryHom P hP (f := φ) (hsm e') z d
    convert hs using 1
    funext u
    change r₀ (j (e.equiv.symm _)) = r₀ (e'.equiv.symm (e'.equiv (j (e.equiv.symm _))))
    rw [e'.equiv.symm_apply_apply]

/-- Bruhat smoothness of the global test restricts along the S-idele insertion into
idele classes. This restriction need not have compact support on the S-ideles. -/
private theorem sLocalTraceRestriction_smooth (φ : BruhatCompactSupport C𝔽) :
    IsBruhatSmooth (fun g : Iₛ ↦ φ.val (classAtS(g))) := by
  let f : Iₛ →ₜ* C𝔽 := ⟨(QuotientGroup.mk' _).comp (sIdeleInsertion F S),
    QuotientGroup.continuous_mk.comp (isClosedEmbedding_sIdeleInsertion F S).continuous⟩
  exact sLocalTrace_comp_bruhatSmooth f ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)

private theorem sLocalTrace_comp_complex {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    {r : G → ℂ} (hr : IsBruhatSmooth r) {P : ℂ → ℂ} (hP : ContDiff ℝ (∞) P) :
    IsBruhatSmooth (P ∘ r) := by
  intro p
  obtain ⟨k, hk, hi, hd⟩ := hr p
  refine ⟨k, hk, fun t x ↦ congrArg P (hi t x), fun a ha ↦ ?_⟩
  obtain ⟨r₀, hr₀, hs⟩ := hd a ha
  exact ⟨P ∘ r₀, fun x ↦ congrArg P (hr₀ x), fun e z d ↦
    (hP.of_le (by exact_mod_cast le_top)).comp (hs e z d)⟩

/-- A compact subset of the projected S-unit quotient has a compactly supported
Bruhat test on the S-ideles whose orbit sums equal one over that subset. -/
private theorem exists_sLocalTraceCutoff
    (K : Set Jₛ) (hK : IsCompact K) :
    ∃ w : BruhatCompactSupport Iₛ, ∀ g : Iₛ, (QuotientGroup.mk g : Jₛ) ∈ K →
      HasSum (fun ξ : Hₛ ↦ w.val (ξ.val * g)) 1 := by
  classical
  let hclosed : IsClosed (Hₛ : Set Iₛ) := isClosed_sProjectedDiagonal
  let : IsClosed (Hₛ : Set Iₛ) := hclosed
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let : DiscreteTopology Hₛ := discreteTopology_sProjectedDiagonal
  let : (Measure.count : Measure Hₛ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let : (Measure.count : Measure Hₛ).Regular := count_regular_of_discreteTopology
  let d : ((S : Set V).integer F)ˣ →* Iₛ :=
    (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom).comp
      (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable (((S : Set V).integer F)ˣ) := Units.val_injective.countable
  have hdr : Hₛ = d.range := MonoidHom.map_range _ _
  let : Countable Hₛ := hdr.symm ▸ d.rangeRestrict_surjective.countable
  let q : Iₛ →ₜ* Jₛ := ⟨QuotientGroup.mk' Hₛ, QuotientGroup.continuous_mk⟩
  have hopen : IsOpenMap q := QuotientGroup.isOpenMap_coe
  let P : ℂ → ℂ := fun z ↦ Complex.ofReal (z.re * z.re)
  have hP : ContDiff ℝ (∞) P := Complex.ofRealCLM.contDiff.comp
    (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff)
  have hlocal (g : Iₛ) : ∃ u : SchwartzBruhat Iₛ, ∃ U : Set Iₛ, HasCompactSupport u.val ∧
      IsOpen U ∧ g ∈ U ∧ (∀ x ∈ U, u.val x = 1) ∧
      ∀ x, 0 ≤ (u.val x).re ∧ (u.val x).im = 0 := by
    obtain ⟨v, hcv, _, h1⟩ := schwartzBruhat_exists_local_unit
      (x := g) isOpen_univ (mem_univ g)
    obtain ⟨u, hu⟩ := compact_schwartzBruhat_comp (φ := P) hcv hP (by simp [P])
    obtain ⟨U, hU, ho, hg⟩ := mem_nhds_iff.mp h1
    refine ⟨u, U, ?_, ho, hg, fun x hx ↦ ?_, fun x ↦ ?_⟩
    · rw [hu]
      exact hcv.of_isClosed_subset isClosed_closure (tsupport_comp_subset (by simp [P]) _)
    · have hx' : v.val x = 1 := hU hx
      simp [hu, P, hx']
    · simp [hu, P, mul_self_nonneg]
  choose u U hcu hU hgU hu hpos using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun g ↦ q '' U g) (fun g ↦ hopen _ (hU g))
    (fun z _ ↦ by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
      exact mem_iUnion.mpr ⟨g, g, hgU g, rfl⟩)
  have hcompact (t : Finset Iₛ) : HasCompactSupport (∑ g ∈ t, (u g).val) := by
    induction t using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact HasCompactSupport.zero
    | insert g t hg ih =>
        rw [Finset.sum_insert hg]
        exact (hcu g).add ih
  let v := ∑ g ∈ s, (u g).val
  have hv : v ∈ schwartzBruhatSubmodule Iₛ :=
    Submodule.sum_mem _ (fun g _ ↦ (u g).property)
  let bump : SchwartzBruhat Iₛ := ⟨v, hv⟩
  have hcv : HasCompactSupport v := hcompact s
  have hvpos (x : Iₛ) : 0 ≤ (v x).re := by
    simpa only [v, Finset.sum_apply, Complex.re_sum] using Finset.sum_nonneg (fun g _ ↦ (hpos g x).1)
  have hvim (x : Iₛ) : (v x).im = 0 := by simp [v, Finset.sum_apply, Complex.im_sum, fun g ↦ (hpos g x).2]
  let W := schwartzBruhatCosetIntegral Hₛ Measure.count hclosed bump
  have hsum (g : Iₛ) : HasSum (fun ξ : Hₛ ↦ v (ξ.val * g)) (W.val (q g)) := by
    have hi := (lcaCosetIntegral_mem_schwartzBruhat Hₛ Measure.count hclosed bump).1 g
    rw [show W.val (q g) = ∫ k : Hₛ, bump (g * k.val) ∂Measure.count from
      schwartzBruhatCosetIntegral_mk Hₛ Measure.count hclosed bump g]
    rw [integral_countable hi]
    simpa only [mul_comm g, bump, count_real_singleton, one_smul] using (integrable_count_iff.mp hi).of_norm.hasSum
  have him (g : Iₛ) : (W.val (q g)).im = 0 :=
    (Complex.imCLM.hasSum (hsum g)).unique (by simpa only [Complex.imCLM_apply, hvim] using hasSum_zero)
  have hbound (g : Iₛ) (hg : q g ∈ K) : 1 ≤ (W.val (q g)).re := by
    obtain ⟨x, hx, y, hy, hyq⟩ := mem_iUnion₂.mp (hs hg)
    have hξ : y / g ∈ Hₛ := QuotientGroup.eq_iff_div_mem.mp hyq
    let ξ : Hₛ := ⟨y / g, hξ⟩
    have hy' : ξ.val * g = y := div_mul_cancel _ _
    have h₁ : 1 ≤ (v y).re := by
      rw [show (v y).re = ∑ z ∈ s, ((u z).val y).re by simp [v, Finset.sum_apply, Complex.re_sum]]
      have he := Finset.single_le_sum (f := fun z ↦ ((u z).val y).re)
        (fun z _ ↦ (hpos z y).1) hx
      simpa only [hu x y hy, Complex.one_re] using he
    have hre : HasSum (fun ξ : Hₛ ↦ (v (ξ.val * g)).re) (W.val (q g)).re :=
      Complex.reCLM.hasSum (hsum g)
    have hb := sum_le_hasSum ({ξ} : Finset Hₛ) (fun t _ ↦ hvpos (t.val * g)) hre
    exact h₁.trans (by simpa only [Finset.sum_singleton, hy'] using hb)
  -- Extend the identity on [1, ∞) to a strictly positive smooth function.
  let D (t : ℝ) := 1 + Real.smoothTransition (2 * t - 1) * (t - 1)
  have hD (t : ℝ) : 0 < D t := by
    by_cases ht : t ≤ 1 / 2
    · have he : 2 * t - 1 ≤ 0 := by linarith
      simp [D, Real.smoothTransition.zero_of_nonpos he]
    · have ht' : 0 < t := by linarith
      have ha := Real.smoothTransition.nonneg (2 * t - 1)
      have hb := Real.smoothTransition.le_one (2 * t - 1)
      by_cases h : t ≤ 1
      · have hle := mul_le_mul_of_nonpos_right hb (sub_nonpos.mpr h)
        dsimp [D]
        linarith
      · have hge := mul_nonneg ha (sub_nonneg.mpr (le_of_not_ge h))
        dsimp [D]
        linarith
  have hDeq (t : ℝ) (ht : 1 ≤ t) : D t = t := by
    rw [show D t = 1 + Real.smoothTransition (2 * t - 1) * (t - 1) from rfl,
      Real.smoothTransition.one_of_one_le (by linarith), one_mul]
    ring
  have hDs : ContDiff ℝ (∞) D :=
    contDiff_const.add ((Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul (contDiff_id.sub contDiff_const))
  let N (z : ℂ) := Complex.ofReal (D z.re)⁻¹
  have hN : ContDiff ℝ (∞) N := Complex.ofRealCLM.contDiff.comp
    ((hDs.comp Complex.reCLM.contDiff).inv (fun z ↦ (hD z.re).ne'))
  let n (g : Iₛ) := N (W.val (q g))
  have hn : IsBruhatSmooth n := sLocalTrace_comp_complex
    (sLocalTrace_comp_bruhatSmooth q (schwartzBruhat_isBruhatSmooth W)) hN
  have hw : IsBruhatSmooth (v * n) := fun p ↦
    isBruhatContDiff_mul (schwartzBruhat_isBruhatSmooth bump p) (hn p)
  refine ⟨⟨v * n, (mem_bruhatSmoothSubmodule_iff _).mpr hw,
    hcv.of_isClosed_subset isClosed_closure tsupport_mul_subset_left⟩, fun g hg ↦ ?_⟩
  change HasSum (fun ξ : Hₛ ↦ v (ξ.val * g) * n (ξ.val * g)) 1
  have hq (ξ : Hₛ) : q (ξ.val * g) = q g := by
    rw [map_mul, show q ξ.val = 1 from (QuotientGroup.eq_one_iff _).mpr ξ.property, one_mul]
  have hn' (ξ : Hₛ) : n (ξ.val * g) = n g := by simp only [n, hq]
  simp_rw [hn']
  have hb := hbound g hg
  have hw' : W.val (q g) = Complex.ofReal (W.val (q g)).re :=
    Complex.ext (by simp) (by simpa using him g)
  have heq : W.val (q g) * n g = 1 := by
    change W.val (q g) * Complex.ofReal (D (W.val (q g)).re)⁻¹ = 1
    rw [hDeq _ hb]
    conv_lhs => lhs; rw [hw']
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by linarith), Complex.ofReal_one]
  exact heq ▸ (hsum g).mul_right (n g)

/-- Paper: (12.4.1.4), p. 515. The restriction of an outside-unit-invariant test admits
a compactly supported Bruhat lift whose S-unit periodization recovers the restriction.
Deviation: The inserted S-idele evaluates the global test before taking the quotient. -/
theorem exists_sLocalTraceLift
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c) :
    ∃ f : BruhatCompactSupport Iₛ, ∀ g : Iₛ,
      HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))) := by
  let K := sIdeleQuotientNorm F S ⁻¹' (ideleClassNorm F '' tsupport φ.val)
  have hK : IsCompact K := (isProperMap_sIdeleQuotientNorm F S).isCompact_preimage
    (φ.property.2.image (isProperMap_ideleClassNorm F).continuous)
  obtain ⟨w, hw⟩ := exists_sLocalTraceCutoff K hK
  let r : Iₛ → ℂ := fun g ↦ φ.val (classAtS(g))
  have hs : IsBruhatSmooth (w.val * r) := fun p ↦
    isBruhatContDiff_mul ((mem_bruhatSmoothSubmodule_iff _).mp w.property.1 p)
      (sLocalTraceRestriction_smooth φ p)
  have hc : HasCompactSupport (w.val * r) :=
    w.property.2.of_isClosed_subset isClosed_closure tsupport_mul_subset_left
  refine ⟨⟨w.val * r, (mem_bruhatSmoothSubmodule_iff _).mpr hs, hc⟩, fun g ↦ ?_⟩
  have hEq (ξ : Hₛ) : r (ξ.val * g) = r g := sLocalTraceRestriction_invariant φ _hOutside ξ g
  change HasSum (fun ξ : Hₛ ↦ w.val (ξ.val * g) * r (ξ.val * g)) (r g)
  simp_rw [hEq]
  by_cases hg : r g = 0
  · simp [hg]
  have hmem : (QuotientGroup.mk g : Jₛ) ∈ K := by
    refine ⟨classAtS(g), subset_closure hg, ?_⟩
    rw [sIdeleQuotientNorm_mk]
    exact ideleNorm_sIdeleInsertion F S g
  simpa only [one_mul] using (hw g hmem).mul_right (r g)


-- TODO(paper-gap): The operator A on p. 515 has an extra factor |x|^(1/2)
-- in its output. Step I computes the scalar kernel with that factor removed.
-- The asserted factorization through the revised Proposition 5.3.4.4 needs a
-- comparison of the actual norm-weighted spaces and operators.

/-- Paper: (12.4.1.5) and (12.4.1.7), p. 516. Acting on a test integrates its values
at the translated points against the lift weighted by the inverse square-root norm.
Deviation: The definition gives the scalar pairing of the distributional kernel. -/
def sLocalTraceDilationKernel (f : BruhatCompactSupport Iₛ) (b : Aₛ → ℂ) (x : Aₛ) : ℂ :=
  ∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) * b ((g⁻¹).val * x) ∂μₛ

/-- Continuity of a Bruhat-smooth function follows already from order zero
(ported from the private `continuous_of_bruhatSmooth` in Ch09 Sec3). -/
private theorem sLocalTraceDilationKernel_apply_zero_continuous {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    {f : G → ℂ} (hf : IsBruhatSmooth f) : Continuous f := by
  classical
  obtain ⟨k, hk, _, hdesc⟩ := hf 0
  have hkc := hk.isCompact
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hU₁⟩ := exists_compact_mem_nhds (1 : G)
  let K := insert x (U ∪ (k : Set G))
  let H := Subgroup.closure K
  have hK : K ⊆ (H : Set G) := Subgroup.subset_closure
  have hK₁ : K ∈ 𝓝 (1 : G) := mem_of_superset hU₁ (subset_union_left.trans (subset_insert ..))
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds (mem_of_superset hK₁ hK)
  let a : BruhatStructuralPair G :=
    ⟨(H, OrderDual.toDual k), hH,
      ⟨Subtype.val ⁻¹' K, continuous_subtype_val.continuousAt.preimage_mem_nhds hK₁,
        (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage
          ((hU.union hkc).insert x), Subgroup.closure_preimage_eq_top K⟩,
      hk, subset_union_right.trans ((subset_insert ..).trans hK)⟩
  let e := Classical.choice a.elementary
  obtain ⟨f₀, hval, hsm⟩ := hdesc a rfl
  let q : EuclideanSpace ℝ (Fin e.torusDim) → (Fin e.torusDim → AddCircle (1 : ℝ)) :=
    fun t i ↦ (t i : AddCircle (1 : ℝ))
  have hq : IsOpenQuotientMap q :=
    (IsOpenQuotientMap.piMap (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin e.torusDim ↦ ℝ)).toHomeomorph.isOpenQuotientMap
  have hmodel : Continuous (fun y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor ↦
      f₀ (e.equiv.symm (Multiplicative.ofAdd y))) := by
    rw [← (Homeomorph.prodAssoc _ _ _).isOpenQuotientMap.continuous_comp_iff]
    refine continuous_prod_of_discrete_right.mpr fun zd ↦ ?_
    rw [← ((IsOpenQuotientMap.id (X := EuclideanSpace ℝ (Fin e.realDim))).prodMap hq).continuous_comp_iff]
    exact (hsm e zd.1 zd.2).continuous
  have hf₀ : Continuous f₀ := by
    simpa only [Function.comp_def, ofAdd_toAdd, ContinuousMulEquiv.symm_apply_apply]
      using hmodel.comp (show Continuous (fun z : a.quotient ↦ (e.equiv z).toAdd) from e.equiv.continuous)
  have hcont : Continuous (fun z : H ↦ f (z : G)) :=
    (hf₀.comp (QuotientGroup.continuous_mk (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))).congr hval
  exact hH.isOpenEmbedding_subtypeVal.continuousAt_iff.mp (hcont.continuousAt (x := ⟨x, hK (mem_insert ..)⟩))

/-- Paper: (12.4.1.5) and (12.4.1.7), p. 516. At the origin each translated
evaluation is the test value at zero, and the kernel has the corresponding weighted mass. -/
theorem sLocalTraceDilationKernel_apply_zero (f : BruhatCompactSupport Iₛ) (b : testₛ) :
    Integrable (fun g ↦ f.val g / (Real.sqrt (normS(g)) : ℂ)) μₛ ∧
      sLocalTraceDilationKernel f (fun y ↦ testAt(b, y)) 0 =
        (∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ) * testAt(b, 0) := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
  have : (sMultiplicativeTamagawaMeasure F S).IsHaarMeasure :=
    sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  have hc : Continuous f.val := sLocalTraceDilationKernel_apply_zero_continuous
    ((mem_bruhatSmoothSubmodule_iff _).1 f.property.1)
  have hn : Continuous fun g : Iₛ ↦ normS(g) := by
    have h : Continuous fun g : Iₛ ↦ sIdeleQuotientNorm F S (QuotientGroup.mk g) :=
      (isProperMap_sIdeleQuotientNorm F S).continuous.comp continuous_quot_mk
    exact NNReal.continuous_coe.comp (Units.continuous_val.comp h)
  have hpos (g : Iₛ) : 0 < normS(g) := NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S g))
  have hsq : Continuous fun g : Iₛ ↦ (Real.sqrt (normS(g)) : ℂ) :=
    Complex.continuous_ofReal.comp hn.sqrt
  have hne (g : Iₛ) : (Real.sqrt (normS(g)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hpos g)).ne'
  have hcs : HasCompactSupport fun g ↦ f.val g / (Real.sqrt (normS(g)) : ℂ) :=
    HasCompactSupport.mono f.property.2 fun g hg h0 ↦ hg (by simp [h0])
  refine ⟨(hc.div hsq hne).integrable_of_hasCompactSupport hcs, ?_⟩
  simp [sLocalTraceDilationKernel, integral_mul_const]

private theorem exists_sLocalTraceDilationStrongDual_exists_norm_le {H : Type*} [CommGroup H]
    [TopologicalSpace H] {g : H → ℂ} (hg : g ∈ schwartzBruhatSubmodule H) :
    ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
  let P (g : H → ℂ) : Prop := ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C
  have hzero : P 0 := ⟨0, fun x ↦ by simp⟩
  have hadd : ∀ g h, P g → P h → P (g + h) := by
    rintro g h ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C + D, fun x ↦ (norm_add_le (g x) (h x)).trans (add_le_add (hC x) (hD x))⟩
  refine Submodule.iSup_induction (motive := P) _ hg (fun a g hg ↦ ?_) hzero hadd
  refine Submodule.iSup_induction (motive := P) _ hg (fun e g hg ↦ ?_) hzero hadd
  obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hg
  have hb (z) : ‖s z‖ ≤ (elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0)).toReal := by
    have hz : (‖s z‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0) := by
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun y ↦ (‖s y‖₊ : ℝ≥0∞)) z
    exact ENNReal.toReal_mono (s.property.2 (0, 0, 0, 0)).ne hz
  refine ⟨(elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0)).toReal, fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  split_ifs
  · exact hb _
  · simp

private theorem exists_sLocalTraceDilationStrongDual_integrable
    (f : BruhatCompactSupport Iₛ) (x : Aₛ) (b : testₛ) :
    Integrable (fun g : Iₛ ↦
      f.val g / (Real.sqrt (normS(g)) : ℂ) * testAt(b, (g⁻¹).val * x)) μₛ := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
  have hweight := (sLocalTraceDilationKernel_apply_zero f 0).1
  obtain ⟨M, hM⟩ := exists_sLocalTraceDilationStrongDual_exists_norm_le b.property
  have hshift : Continuous (fun g : Iₛ ↦ Multiplicative.ofAdd ((g⁻¹).val * x)) :=
    continuous_ofAdd.comp ((Units.continuous_val.comp continuous_inv).mul continuous_const)
  exact hweight.mul_bdd ((schwartzBruhat_continuous b).comp hshift).aestronglyMeasurable
    (.of_forall fun g ↦ hM _)

private theorem exists_sLocalTraceDilationStrongDual_continuous_of_sup_bound {A : Type*} [CommGroup A]
    [TopologicalSpace A] (Λ : SchwartzBruhat A →ₗ[ℂ] ℂ) (C : ℝ≥0)
    (hΛ : ∀ (f : SchwartzBruhat A) (M : ℝ), (∀ x, ‖f x‖ ≤ M) → ‖Λ f‖ ≤ C * M) :
    Continuous Λ := by
  classical
  let p := (normSeminorm ℂ ℂ).comp Λ
  have hp : ∀ (b : BruhatStructuralPair A) (s : ElementaryLCAPresentation b.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion b s) := by
    intro b s
    let q := (normSeminorm ℂ ℂ).comp (Λ.comp (schwartzBruhatStageInclusion b s))
    change Continuous q
    let p₀ : Seminorm ℂ (SchwartzBruhatStage s) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hp₀ : Continuous p₀ :=
      (withGeneratingSeminorms_spec _ _).continuous_seminorm (0, 0, 0, 0)
    have hpt (f : SchwartzBruhatStage s) (x : A) :
        ‖schwartzBruhatStageRealization b s f x‖ ≤ p₀ f := by
      let := s.finiteGroup
      have he := schwartzBruhatStageRealization_apply b s f x
      by_cases hx : x ∈ b.val.1
      · rw [dite_eq_left hx] at he
        rw [he]
        let y := Multiplicative.toAdd (s.equiv (QuotientGroup.mk ⟨x, hx⟩))
        change (‖f y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
        have hb : (‖f y‖₊ : ENNReal) ≤ elementarySchwartzBound f.val (0, 0, 0, 0) :=
          (le_iSup (fun g ↦ (‖f.val g‖₊ : ENNReal)) y).trans_eq
            (elementarySchwartzBound_zero f.val).symm
        exact ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne hb
      · rw [dite_eq_right hx] at he
        exact ((congrArg norm he).trans (norm_zero : ‖(0 : ℂ)‖ = 0)).le.trans
          (apply_nonneg p₀ f)
    have hC : Continuous (C • p₀) := hp₀.const_smul C
    exact Seminorm.continuous_of_le hC fun f ↦
      hΛ (schwartzBruhatStageInclusion b s f) (p₀ f) (hpt f)
  let i : {q : Seminorm ℂ (schwartzBruhatSubmodule A) //
      ∀ (b : BruhatStructuralPair A) (s : ElementaryLCAPresentation b.quotient),
        Continuous (q ∘ schwartzBruhatStageInclusion b s)} := ⟨p, hp⟩
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp Λ fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm i

/-- Paper: (12.4.1.5)–(12.4.1.7), p. 516. At each output point the scalar
pairing with the test defines a continuous linear functional on additive
Schwartz–Bruhat functions. -/
theorem exists_sLocalTraceDilationStrongDual (f : BruhatCompactSupport Iₛ) (x : Aₛ) :
    ∃ K : StrongDual ℂ testₛ, ∀ b : testₛ,
      Integrable (fun g : Iₛ ↦
        f.val g / (Real.sqrt (normS(g)) : ℂ) * testAt(b, (g⁻¹).val * x)) μₛ ∧
      K b = sLocalTraceDilationKernel f (fun y ↦ testAt(b, y)) x := by
  let weight (g : Iₛ) := f.val g / (Real.sqrt (normS(g)) : ℂ)
  let shift (g : Iₛ) : Multiplicative Aₛ := Multiplicative.ofAdd ((g⁻¹).val * x)
  let Φ (b : testₛ) : ℂ := ∫ g, weight g * b (shift g) ∂μₛ
  have hint (b : testₛ) : Integrable (fun g ↦ weight g * b (shift g)) μₛ :=
    exists_sLocalTraceDilationStrongDual_integrable f x b
  have hlin : IsLinearMap ℂ Φ := by
    constructor
    · intro b c
      change (∫ g, weight g * (b + c) (shift g) ∂μₛ) =
        (∫ g, weight g * b (shift g) ∂μₛ) + ∫ g, weight g * c (shift g) ∂μₛ
      simp_rw [show ∀ g, (b + c) (shift g) = b (shift g) + c (shift g) from fun g ↦ by rfl]
      simp_rw [mul_add]
      exact integral_add (hint b) (hint c)
    · intro c b
      change (∫ g, weight g * (c • b) (shift g) ∂μₛ) =
        c • ∫ g, weight g * b (shift g) ∂μₛ
      simp_rw [show ∀ g, (c • b) (shift g) = c * b (shift g) from fun g ↦ by rfl]
      simp_rw [mul_left_comm (weight _) c]
      simpa only [smul_eq_mul] using (integral_const_mul c (fun g ↦ weight g * b (shift g)))
  let Λ : testₛ →ₗ[ℂ] ℂ := IsLinearMap.mk' Φ hlin
  have hweight : Integrable weight μₛ := (sLocalTraceDilationKernel_apply_zero f 0).1
  let C : ℝ≥0 := ⟨∫ g, ‖weight g‖ ∂μₛ, integral_nonneg fun _ ↦ norm_nonneg _⟩
  have hΛ : ∀ (b : testₛ) (M : ℝ), (∀ z, ‖b z‖ ≤ M) → ‖Λ b‖ ≤ C * M := by
    intro b M hM
    change ‖∫ g, weight g * b (shift g) ∂μₛ‖ ≤ C * M
    calc
      _ ≤ ∫ g, ‖weight g * b (shift g)‖ ∂μₛ := norm_integral_le_integral_norm _
      _ ≤ ∫ g, ‖weight g‖ * M ∂μₛ := by
        apply integral_mono (hint b).norm (hweight.norm.mul_const M)
        intro g
        change ‖weight g * b (shift g)‖ ≤ ‖weight g‖ * M
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      _ = C * M := by rw [integral_mul_const]; rfl
  refine ⟨⟨Λ, exists_sLocalTraceDilationStrongDual_continuous_of_sup_bound Λ C hΛ⟩, fun b ↦ ⟨hint b, ?_⟩⟩
  rfl

-- TODO(paper-gap): The application of (12.4.1.6) requires a kernel theorem for
-- the particular vector-valued Schwartz–Bruhat space and operator topology.
-- The scalar distribution pairing above does not establish that assertion.

-- TODO(paper-gap): Footnotes 2–4 request new one-sided smooth cutoffs and an
-- independent lower bound. In Step II the product-norm multipliers also fail
-- to have the advertised Schwartz–Bruhat mapping properties (I218 and R9).

/-- Paper: Step II, p. 516. In the rational real model, a compact smooth cutoff
vanishing near zero multiplies any Schwartz test into the flat subspace.
Deviation: A ball cutoff that is one near zero does not have this range. -/
theorem realSpatialCutoff_flat_of_eventually_zero (ρ : ℝ → ℝ)
    (_hSmooth : ContDiff ℝ (∞ : ℕ∞ω) ρ) (_hCompact : HasCompactSupport ρ)
    (_hZero : ∀ᶠ x in 𝓝 (0 : ℝ), ρ x = 0) (f : 𝓢(ℝ, ℂ)) :
    ∃ h : 𝓢(ℝ, ℂ), h ∈ realSchwartzFlatAtOrigin ∧
      ∀ x : ℝ, h x = (ρ x : ℂ) * f x := by
  have hg : (fun x : ℝ ↦ (ρ x : ℂ)).HasTemperateGrowth :=
    (_hCompact.comp_left Complex.ofReal_zero).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp _hSmooth)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (ρ x : ℂ)) f,
    (mem_realSchwartzFlatAtOrigin_iff _).2 fun k ↦ ?_, fun x ↦ ?_⟩
  · have h0 : (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (ρ x : ℂ)) f : ℝ → ℂ) =ᶠ[𝓝 0]
        fun _ ↦ 0 :=
      _hZero.mono fun x hx ↦ by simp [SchwartzMap.smulLeftCLM_apply_apply hg, hx]
    rw [h0.iteratedDeriv_eq]
    simp
  · simp [SchwartzMap.smulLeftCLM_apply_apply hg]

/-- Paper: Step II and (12.4.1.8)–(12.4.1.10), pp. 516–517. The Fourier cutoff
multiplies the Fourier transform by a symbol, then applies the inverse transform.
Deviation: This is a scalar function on the additive adeles. The definition makes
no assertion that the result belongs to the Schwartz–Bruhat test space. -/
def sLocalTraceFourierCutoff (ρ' : Aₛ → ℂ) (b : testₛ) (x : Aₛ) : ℂ :=
  fourierₛ (fun u ↦ ρ' u * testAt(sAdeleSchwartzFourier b, u)) (-x)

/-- Paper: (12.4.1.8), p. 517. The constant-one Fourier symbol recovers the test
by inversion. -/
theorem sLocalTraceFourierCutoff_one (b : testₛ) (x : Aₛ) :
    sLocalTraceFourierCutoff (fun _ ↦ 1) b x = testAt(b, x) := by
  have h := sLocal_fourier_inversion b (-x)
  rw [neg_neg] at h
  unfold sLocalTraceFourierCutoff
  simp only [one_mul]
  unfold sAdeleSchwartzFourier at h
  exact h

/-- Paper: Step II, p. 517. For an integrable symbol the inverse Fourier transform
of the symbol, evaluated at output minus input, is the Fourier cutoff kernel.
Deviation: The inverse transform gives the sign for general symbols. For the even
symbols in the paper the forward transform has the same values. -/
def sLocalTraceFourierKernel (ρ' : Aₛ → ℂ) (_hρ' : Integrable ρ' νₛ) (x y : Aₛ) : ℂ :=
  fourierₛ ρ' (y - x)

/-- Paper: Step II, p. 517. The diagonal Fourier kernel for an integrable
symbol is its integral against additive Tamagawa measure. -/
theorem sLocalTraceFourierKernel_diagonal (ρ' : Aₛ → ℂ) (hρ' : Integrable ρ' νₛ)
    (x : Aₛ) :
    sLocalTraceFourierKernel ρ' hρ' x x = ∫ u, ρ' u ∂νₛ := by
  have h0 : ψₛ 0 = 1 := by
    have h1 : ∀ w : InfinitePlace F, (0 : Aₛ).1 w = 0 := fun _ ↦ rfl
    simp [sAdeleStandardCharacter, adeleStandardCharacter_zero, finiteLocalStandardCharacter_zero,
      h1, Pi.single_zero, Prod.mk_zero_zero]
  simp [sLocalTraceFourierKernel, tamagawaFourier, h0]

/-- Paper: Step II, p. 517. With an S-idele as output, integrate the
dilation average of the Fourier phases against the frequency symbol and multiply
by the spatial cutoff.
Deviation: The dilation average is taken first. This formula can be used even
when the frequency symbol has no ordinary inverse Fourier kernel. -/
def sLocalTraceCutoffKernel (f : BruhatCompactSupport Iₛ) (ρ : Iₛ → ℂ) (ρ' : Aₛ → ℂ)
    (x : Iₛ) (y : Aₛ) : ℂ :=
  ρ x * ∫ u, ρ' u *
    sLocalTraceDilationKernel f (fun z ↦ (ψₛ ((z - y) * u) : ℂ)) x.val ∂νₛ

/-- An integrable product weight dominates the joint integrand of the two kernels. -/
private theorem sLocalTraceCutoffKernel_eq_comp_fubini
    {G A : Type*} [MeasurableSpace G] [MeasurableSpace A]
    (μ : Measure G) (ν : Measure A) [SFinite μ] [SFinite ν]
    (weight : G → ℂ) (symbol : A → ℂ) (phase : G → A → ℂ)
    (hweight : Integrable weight μ) (hsymbol : Integrable symbol ν)
    (hphase : AEStronglyMeasurable (fun p : A × G ↦ phase p.2 p.1) (ν.prod μ))
    (hunit : ∀ g u, ‖phase g u‖ = 1) :
    (∫ u, symbol u * (∫ g, weight g * phase g u ∂μ) ∂ν) =
      ∫ g, weight g * (∫ u, symbol u * phase g u ∂ν) ∂μ := by
  have hweightProd := hsymbol.mul_prod hweight
  have hprod : Integrable (uncurry fun u g ↦ symbol u * weight g * phase g u)
      (ν.prod μ) := by
    refine hweightProd.mono (hweightProd.aestronglyMeasurable.mul hphase) ?_
    exact ae_of_all _ fun p ↦ by simp [uncurry, hunit]
  simp_rw [← integral_const_mul]
  simpa only [mul_assoc, mul_left_comm] using integral_integral_swap hprod

/-- Paper: Step II, p. 517. For an integrable symbol the composed kernel
agrees with the dilation average of the inverse Fourier kernel, multiplied by the
spatial cutoff. -/
theorem sLocalTraceCutoffKernel_eq_comp (f : BruhatCompactSupport Iₛ)
    (ρ : Iₛ → ℂ) (ρ' : Aₛ → ℂ) (hρ' : Integrable ρ' νₛ) (x : Iₛ) (y : Aₛ) :
    sLocalTraceCutoffKernel f ρ ρ' x y =
      ρ x * sLocalTraceDilationKernel f (fun z ↦ sLocalTraceFourierKernel ρ' hρ' z y) x.val :=
  by
    have : BorelSpace Aₛ := sAdeleRing_borelSpace (F := F) (S := S)
    have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
    let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
    let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
      (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
    let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
    let : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
    let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
    let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
    let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
    let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
    let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
      infiniteLocalAdditiveTamagawaMeasure_haar F w
    let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
      finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
    let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    let : (νₛ).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    let weight (g : Iₛ) := f.val g / (Real.sqrt (normS(g)) : ℂ)
    have hweight : Integrable weight μₛ := (sLocalTraceDilationKernel_apply_zero f 0).1
    obtain ⟨e, he, _⟩ := sAdditiveTamagawaMeasure_selfDual F S
    let char := e (Multiplicative.ofAdd (1 : Aₛ))
    have hchar (z : Aₛ) : char (Multiplicative.ofAdd z) = ψₛ z := by
      simpa only [one_mul] using he 1 z
    have hcontinuous : Continuous (fun z : Aₛ ↦ (ψₛ z : ℂ)) := by
      simp_rw [← hchar]
      exact continuous_subtype_val.comp ((map_continuous char).comp continuous_ofAdd)
    have hneg (z : Aₛ) : star (ψₛ (-z) : ℂ) = (ψₛ z : ℂ) := by
      rw [← hchar, ofAdd_neg, map_inv, Circle.coe_inv_eq_conj,
        ← Complex.star_def, star_star, hchar]
    let phase (g : Iₛ) (u : Aₛ) := (ψₛ (((g⁻¹).val * x.val - y) * u) : ℂ)
    have hphase : Continuous (uncurry phase) := hcontinuous.comp
      (((((Units.continuous_val.comp continuous_inv).comp continuous_fst).mul
        continuous_const).sub continuous_const).mul continuous_snd)
    have hfourier (g : Iₛ) :
        sLocalTraceFourierKernel ρ' hρ' ((g⁻¹).val * x.val) y =
          ∫ u, ρ' u * phase g u ∂νₛ := by
      unfold sLocalTraceFourierKernel tamagawaFourier
      apply integral_congr_ae
      exact ae_of_all _ fun u ↦ by
        change ρ' u * star (ψₛ (u * (y - (g⁻¹).val * x.val)) : ℂ) = ρ' u * phase g u
        rw [show u * (y - (g⁻¹).val * x.val) = -(((g⁻¹).val * x.val - y) * u) by
          rw [← neg_sub ((g⁻¹).val * x.val) y, mul_neg, mul_comm u], hneg]
    unfold sLocalTraceCutoffKernel sLocalTraceDilationKernel
    apply congrArg (fun z : ℂ ↦ ρ x * z)
    simp_rw [hfourier]
    exact sLocalTraceCutoffKernel_eq_comp_fubini μₛ νₛ weight ρ' phase hweight hρ'
      (hphase.comp continuous_swap).aestronglyMeasurable (fun g u ↦ Circle.norm_coe _)

-- TODO(paper-gap): The function on additive adeles constructed in Step II
-- requires a measure conversion and a quotient kernel construction before
-- Proposition 12.2.2.2 can be applied to it. On the additive side the
-- skew-diagonal convention below puts ξx in the output slot. The resulting
-- orbit sum reindexes the S-units by inversion.

-- TODO(paper-gap): The reference to (12.4.1.4) on pp. 514, 516 and 519 should
-- refer to (12.4.1.1)–(12.4.1.3). Equation (12.4.1.4) is the lifting identity.

/-- Paper: (12.4.1.17), p. 518. The factor converting additive to
multiplicative measure is the product of q/(q−1) over the finite places. -/
def sLocalTraceMeasureFactor (S : Finset V) : ℝ :=
  ∏ v ∈ S, (v.asIdeal.absNorm : ℝ) / ((v.asIdeal.absNorm : ℝ) - 1)

/-- Paper: (12.4.1.17), p. 518. The factor for the empty finite set is one
and the factor for one finite place is the corresponding Euler factor. -/
theorem sLocalTraceMeasureFactor_empty_singleton (v : V) :
    sLocalTraceMeasureFactor (F := F) ∅ = 1 ∧
      sLocalTraceMeasureFactor {v} = (v.asIdeal.absNorm : ℝ) / ((v.asIdeal.absNorm : ℝ) - 1) := by
  constructor <;> simp [sLocalTraceMeasureFactor]

/-- The lower integral of a product of coordinate functions over a product measure on
`n` coordinates is the product of the lower integrals. -/
private theorem sLocalTrace_measure_density_lintegral_fin {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
        (MeasurableEquiv.measurableEmbedding _), Fin.prod_univ_succAbove _ 0]
      have hfun : (fun p ↦ ∏ i, f i ((MeasurableEquiv.piFinSuccAbove E 0).symm p i)) =
          fun p ↦ f 0 p.1 * ∏ j : Fin n, f (Fin.succAbove 0 j) (p.2 j) := by
        funext p
        rw [Fin.prod_univ_succAbove _ 0]
        exact congrArg₂ (· * ·) (congrArg (f 0) (Fin.insertNth_apply_same 0 p.1 p.2))
          (Finset.prod_congr rfl fun j _ ↦ congrArg _ (Fin.insertNth_apply_succAbove 0 p.1 p.2 j))
      rw [hfun, lintegral_prod_mul (f := f 0) (g := fun x : (j : Fin n) → E (Fin.succAbove 0 j) ↦
          ∏ j : Fin n, f (Fin.succAbove 0 j) (x j))
        (hf 0).aemeasurable (Finset.measurable_prod _ fun j _ ↦
          (hf (Fin.succAbove 0 j)).comp (measurable_pi_apply j)).aemeasurable,
        n_ih (fun j ↦ f (Fin.succAbove 0 j)) (fun j ↦ hf _)]

/-- The lower integral of a product of coordinate functions over a finite product measure
is the product of the lower integrals. -/
private theorem sLocalTrace_measure_density_lintegral_pi {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact sLocalTrace_measure_density_lintegral_fin (fun i ↦ f (e i)) (fun i ↦ hf (e i))

/-- A finite product of measures with densities is the product measure with the
product density. -/
private theorem sLocalTrace_measure_density_pi_withDensity {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : ι) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    sLocalTrace_measure_density_lintegral_pi f hf]
  exact Finset.prod_congr rfl fun i _ ↦ (withDensity_apply _ (hs i)).symm

/-- Paper: (12.4.1.17), p. 518. The pushforward of multiplicative Tamagawa
measure to the invertible locus has density c_S divided by the product norm.
Deviation: The density is applied to additive measure restricted to the invertible locus. -/
theorem sLocalTrace_measure_density :
    (μₛ).map (Units.val : Iₛ → Aₛ) =
      ((νₛ).restrict (range (Units.val : Iₛ → Aₛ))).withDensity
        (fun z ↦ ENNReal.ofReal (sLocalTraceMeasureFactor S / modS(z))) := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let (v : S) : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (w : InfinitePlace F) : LocallyCompactSpace w.Completionˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).locallyCompactSpace
  let (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
    infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalMultiplicativeTamagawaMeasure F v.val).IsHaarMeasure :=
    finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v.val
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let ρI (w : InfinitePlace F) (x : w.Completion) : ℝ≥0∞ := (↑(‖x‖₊ ^ w.mult) : ℝ≥0∞)⁻¹
  let c (v : S) : ℝ≥0∞ := ↑v.val.asIdeal.absNorm / (↑v.val.asIdeal.absNorm - 1)
  let ρS (v : S) (x : v.val.adicCompletion F) : ℝ≥0∞ := c v * (↑‖x‖₊ : ℝ≥0∞)⁻¹
  have hq (v : S) : 1 < v.val.asIdeal.absNorm := HeightOneSpectrum.one_lt_absNorm v.val
  have hc (v : S) : c v ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (tsub_pos_of_lt (by exact_mod_cast hq v)).ne'
  have hρI (w : InfinitePlace F) : Measurable (ρI w) :=
    ((measurable_nnNorm.pow_const _).coe_nnreal_ennreal).inv
  have hρS (v : S) : Measurable (ρS v) :=
    measurable_const.mul measurable_nnNorm.coe_nnreal_ennreal.inv
  have hRI (w : InfinitePlace F) : MeasurableSet (range (Units.val : w.Completionˣ → _)) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).isOpen_range.measurableSet
  have hRS (v : S) : MeasurableSet (range (Units.val : (v.val.adicCompletion F)ˣ → _)) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.val.adicCompletion F)).isOpen_range.measurableSet
  have hlocI (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val =
      ((infiniteLocalAdditiveTamagawaMeasure F w).restrict (range Units.val)).withDensity (ρI w) := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure,
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding.map_comap,
      restrict_withDensity (hRI w)]
  have hlocS (v : S) : (finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val =
      ((finiteLocalAdditiveTamagawaMeasure F v.val).restrict (range Units.val)).withDensity
        (ρS v) := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity, Measure.map_smul,
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.val.adicCompletion F)).measurableEmbedding.map_comap,
      restrict_withDensity (hRS v), ← withDensity_smul' _ _ (hc v)]
    · rfl
    · exact Units.continuous_val.measurable.aemeasurable
  have hsfI (w : InfinitePlace F) : SigmaFinite
      (((infiniteLocalAdditiveTamagawaMeasure F w).restrict (range Units.val)).withDensity
        (ρI w)) :=
    SigmaFinite.withDensity_of_ne_top ((ae_restrict_iff' (hRI w)).2 (ae_of_all _ fun x hx ↦ by
      obtain ⟨u, rfl⟩ := hx
      exact ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 (pow_ne_zero _
        (nnNorm_ne_zero_iff.2 u.ne_zero)))))
  have hsfS (v : S) : SigmaFinite
      (((finiteLocalAdditiveTamagawaMeasure F v.val).restrict (range Units.val)).withDensity
        (ρS v)) :=
    SigmaFinite.withDensity_of_ne_top ((ae_restrict_iff' (hRS v)).2 (ae_of_all _ fun x hx ↦ by
      obtain ⟨u, rfl⟩ := hx
      exact ENNReal.mul_ne_top (hc v) (ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2
        (nnNorm_ne_zero_iff.2 u.ne_zero)))))
  have (w : InfinitePlace F) :
      SigmaFinite ((infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val) := by
    rw [hlocI w]; exact hsfI w
  have (v : S) :
      SigmaFinite ((finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val) := by
    rw [hlocS v]; exact hsfS v
  have hAI : Measurable (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦
      (f w).val) :=
    measurable_pi_iff.2 fun w ↦ Units.continuous_val.measurable.comp (measurable_pi_apply w)
  have hAS : Measurable (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val) :=
    measurable_pi_iff.2 fun v ↦ Units.continuous_val.measurable.comp (measurable_pi_apply v)
  have hmapL : (μₛ).map (Units.val : Iₛ → Aₛ) =
      ((Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).map
        (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦ (f w).val)).prod
      ((Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val).map
        (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val)) := by
    rw [Measure.map_prod_map _ _ hAI hAS]
    unfold sMultiplicativeTamagawaMeasure
    rw [Measure.map_map]
    · rfl
    · exact fun s hs ↦ ⟨s, hs, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact (hAI.prodMap hAS) ht
  have hrange : range (Units.val : Iₛ → Aₛ) =
      (univ.pi fun w : InfinitePlace F ↦ range (Units.val : w.Completionˣ → w.Completion)) ×ˢ
        (univ.pi fun v : S ↦
          range (Units.val : (v.val.adicCompletion F)ˣ → v.val.adicCompletion F)) := by
    ext z
    simp only [Set.mem_prod, Set.mem_univ_pi]
    change IsUnit z ↔ (∀ w, IsUnit (z.1 w)) ∧ ∀ v, IsUnit (z.2 v)
    rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  have hbox : MeasurableSet ((univ.pi fun w : InfinitePlace F ↦
      range (Units.val : w.Completionˣ → w.Completion)) ×ˢ (univ.pi fun v : S ↦
          range (Units.val : (v.val.adicCompletion F)ˣ → v.val.adicCompletion F))) :=
    (MeasurableSet.univ_pi hRI).prod (MeasurableSet.univ_pi hRS)
  have hpiI : (Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).map
      (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦ (f w).val) =
      Measure.pi fun w ↦ (infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val :=
    Measure.pi_map_pi fun w ↦ Units.continuous_val.measurable.aemeasurable
  have hpiS : (Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val).map
      (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val) =
      Measure.pi fun v : S ↦ (finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val :=
    Measure.pi_map_pi fun v ↦ Units.continuous_val.measurable.aemeasurable
  rw [hmapL, hpiI, hpiS]
  simp_rw [hlocI, hlocS]
  rw [sLocalTrace_measure_density_pi_withDensity _ ρI hρI,
    sLocalTrace_measure_density_pi_withDensity _ ρS hρS,
    prod_withDensity (f := fun x : (w : InfinitePlace F) → w.Completion ↦ ∏ w, ρI w (x w))
      (g := fun x : (v : S) → v.val.adicCompletion F ↦ ∏ v, ρS v (x v))
      (Finset.measurable_prod _ fun w _ ↦ (hρI w).comp (measurable_pi_apply w))
      (Finset.measurable_prod _ fun v _ ↦ (hρS v).comp (measurable_pi_apply v)),
    ← Measure.restrict_pi_pi, ← Measure.restrict_pi_pi, Measure.prod_restrict, hrange]
  refine withDensity_congr_ae ((ae_restrict_iff' hbox).2 (ae_of_all _ fun z hz ↦ ?_))
  have hz1 (w : InfinitePlace F) : 0 < ‖z.1 w‖ := by
    obtain ⟨u, hu⟩ := (Set.mem_univ_pi.1 hz.1) w
    exact norm_pos_iff.2 (hu ▸ u.ne_zero)
  have hz2 (v : S) : 0 < ‖z.2 v‖ := by
    obtain ⟨u, hu⟩ := (Set.mem_univ_pi.1 hz.2) v
    exact norm_pos_iff.2 (hu ▸ u.ne_zero)
  have hq' (v : S) : (1 : ℝ) < v.val.asIdeal.absNorm := by exact_mod_cast hq v
  have e1 (w : InfinitePlace F) :
      ρI w (z.1 w) = ENNReal.ofReal ((‖z.1 w‖ ^ w.mult)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (pow_pos (hz1 w) _),
      show ‖z.1 w‖ ^ w.mult = ((‖z.1 w‖₊ ^ w.mult : ℝ≥0) : ℝ) by simp,
      ENNReal.ofReal_coe_nnreal]
  have e2 (v : S) : ρS v (z.2 v) =
      ENNReal.ofReal ((v.val.asIdeal.absNorm : ℝ) / ((v.val.asIdeal.absNorm : ℝ) - 1)) *
        ENNReal.ofReal ‖z.2 v‖⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (hz2 v), ENNReal.ofReal_div_of_pos (sub_pos.2 (hq' v)),
      ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one,
      ← coe_nnNorm, ENNReal.ofReal_coe_nnreal]
  simp only [e1, e2]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ ↦ inv_nonneg.2 (pow_nonneg (hz1 w).le _))]
  simp_rw [← ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hq' _)).le)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ ↦ mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hq' v)).le) (inv_nonneg.2 (hz2 v).le)),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ ↦ inv_nonneg.2 (pow_nonneg (hz1 w).le _))]
  congr 1
  rw [sLocalTraceMeasureFactor, ← Finset.prod_coe_sort S, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  ring

/-- Paper: (12.4.1.18)–(12.4.1.21), p. 518. Translate and invert the lifted test
and divide by the square-root norm after the change of variable z = gξ − 1.
Deviation: The function on the additive adeles is extended by zero where 1 + z
is not invertible. The printed domain in (12.4.1.18) is written for g. -/
def sLocalTraceEta (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (z : Aₛ) : ℂ :=
  Function.extend (Units.val : Iₛ → Aₛ)
    (fun u ↦ f.val ((ξ.val⁻¹ * u)⁻¹) / (Real.sqrt (normS(ξ.val⁻¹ * u)) : ℂ))
    (fun _ ↦ 0) (1 + z)

/-- Paper: (12.4.1.20), p. 518. The translated test has value f(ξ) at the
origin, and it is zero at minus one. -/
theorem sLocalTraceEta_zero_neg_one (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    sLocalTraceEta f ξ 0 = f.val ξ.val ∧ sLocalTraceEta f ξ (-1) = 0 := by
  have h2 : sIdeleNorm F S ξ.val = 1 := by
    obtain ⟨γ, hγ, hξ⟩ := Subgroup.mem_map.mp ξ.property
    have h1 := ((sIdeleNorm_spec F S).2 hγ)
    rw [← hξ]; exact h1
  constructor
  · unfold sLocalTraceEta
    have h : (1 : Aₛ) + 0 = ((1 : Iₛ) : Aₛ) := by simp
    rw [h, Units.val_injective.extend_apply]
    simp [h2]
  · unfold sLocalTraceEta
    have h : (1 : Aₛ) + -1 = 0 := by simp
    rw [h, Function.extend_apply']
    rintro ⟨u, hu⟩
    exact not_isUnit_zero (hu ▸ u.isUnit)

section

private theorem sLocalTrace_additiveHaar : (νₛ).IsAddHaarMeasure := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- Paper: (12.4.1.17), p. 518. For an additive integrand vanishing off the units,
its multiplicative integral weighted by the idelic norm is its additive integral
times the finite-place measure factor. -/
private theorem sLocalTrace_integral_units (a : Aₛ → ℂ) (ha : ∀ t, t ∉ range (Units.val : Iₛ → Aₛ) → a t = 0) :
    (∫ t : Iₛ, (normS(t) : ℂ) * a t.val ∂μₛ) =
      (sLocalTraceMeasureFactor S : ℂ) * ∫ t, a t ∂νₛ := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F))
  let n (t : Aₛ) := modS(t)
  have hn (t : Iₛ) : normS(t) = n t.val := by simp [n, sIdeleNorm, Units.coe_prod]
  have hm : Continuous n := by
    unfold n
    exact (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  let c := sLocalTraceMeasureFactor (F := F) S
  have hc : 0 ≤ c := by
    apply Finset.prod_nonneg
    intro v _
    have hv : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hv.le)
  let d (t : Aₛ) := ENNReal.ofReal (c / n t)
  have hd : Measurable d := (measurable_const.div hm.measurable).ennreal_ofReal
  simp_rw [hn]
  rw [← ho.measurableEmbedding.integral_map (μ := μₛ) (fun t ↦ (n t : ℂ) * a t),
    sLocalTrace_measure_density]
  change (∫ t, (n t : ℂ) * a t ∂((νₛ).restrict _).withDensity d) = _
  rw [integral_withDensity_eq_integral_toReal_smul hd (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero ha, ← integral_const_mul]
  apply integral_congr_ae
  apply (ae_restrict_iff' ho.isOpen_range.measurableSet).2
  apply ae_of_all
  rintro _ ⟨t, rfl⟩
  have hpos : 0 < n t.val := (hn t) ▸ NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S t))
  simp only [d, ENNReal.toReal_ofReal (div_nonneg hc hpos.le), Complex.real_smul,
    Complex.ofReal_div]
  change (c : ℂ) / _ * (_ * _) = (c : ℂ) * _
  field_simp [Complex.ofReal_ne_zero.mpr hpos.ne']

private theorem sLocalTraceDilationKernel_skew_frequency (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (x : Iₛ) (u : Aₛ) :
    sLocalTraceDilationKernel f (fun z ↦ (ψₛ ((z - x.val) * u) : ℂ)) (ξ.val * x).val =
      (sLocalTraceMeasureFactor S : ℂ) * fourierₛ (sLocalTraceEta f ξ) (-(x.val * u)) := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let : (μₛ).Regular := sMultiplicativeTamagawaMeasure_regular
  let : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace Aₛ := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  have hξ : sIdeleNorm F S ξ.val = 1 := by
    obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp ξ.property
    exact he ▸ (sIdeleNorm_spec F S).2 hγ
  obtain ⟨e, he, -⟩ := sAdditiveTamagawaMeasure_selfDual F S
  let char := e (Multiplicative.ofAdd (1 : Aₛ))
  have hchar (z : Aₛ) : char (Multiplicative.ofAdd z) = ψₛ z := by
    simpa only [one_mul] using he 1 z
  have hneg (z : Aₛ) : star (ψₛ (-z) : ℂ) = (ψₛ z : ℂ) := by
    rw [← hchar, ofAdd_neg, map_inv, Circle.coe_inv_eq_conj,
      ← Complex.star_def, star_star, hchar]
  let k (z : Aₛ) := sLocalTraceEta f ξ z * (ψₛ (z * (x.val * u)) : ℂ)
  let j (t : Iₛ) := (normS(t) : ℂ) * k (t.val - 1)
  have hj (g : Iₛ) : j (ξ.val * g⁻¹) = f.val g / (Real.sqrt (normS(g)) : ℂ) *
      (ψₛ (((g⁻¹).val * (ξ.val * x).val - x.val) * u) : ℂ) := by
    have ht (t : Iₛ) : (1 : Aₛ) + (t.val - 1) = t.val := by abel
    simp only [j, k, sLocalTraceEta, ht, Units.val_injective.extend_apply,
      inv_mul_cancel_left, inv_inv, map_mul, map_inv, hξ, one_mul, inv_one, Units.val_inv_eq_inv_val,
      NNReal.coe_inv, Real.sqrt_inv, Complex.ofReal_inv, div_inv_eq_mul, Units.val_mul]
    rw [show (ξ.val.val * (g⁻¹).val - 1) * (x.val * u) =
      ((g⁻¹).val * (ξ.val.val * x.val) - x.val) * u by ring]
    have hs : (Real.sqrt (normS(g)) : ℂ) ^ 2 = (normS(g) : ℂ) := by
      exact_mod_cast Real.sq_sqrt (NNReal.coe_nonneg _)
    rw [← hs]
    have hne : (Real.sqrt (normS(g)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (Units.zero_lt _))).ne'
    field_simp [hne]
  unfold sLocalTraceDilationKernel
  simp_rw [← hj]
  rw [integral_inv_eq_self (fun t ↦ j (ξ.val * t)) μₛ, integral_mul_left_eq_self]
  change (∫ t : Iₛ, (normS(t) : ℂ) * k (t.val - 1) ∂μₛ) = _
  rw [sLocalTrace_integral_units (fun t ↦ k (t - 1)) (by
    intro t ht
    simp [k, sLocalTraceEta, show (1 : Aₛ) + (t - 1) = t by abel, Function.extend_apply' _ _ _ ht]),
    integral_sub_right_eq_self]
  unfold tamagawaFourier
  simp only [mul_neg, hneg, k]

/-- Paper: (12.4.1.21)–(12.4.1.22), p. 518. On the skew diagonal, an even frequency
symbol gives the same scalar integral on the kernel and Fourier sides.
Deviation: The dilation average is taken first. This equality of Bochner integrals
holds independently of the separate integrability assertion. -/
private theorem sLocalTraceCutoffKernel_skew_eq (f : BruhatCompactSupport Iₛ) (ρ : Iₛ → ℂ) (r : Aₛ → ℂ)
    (heven : ∀ u, r (-u) = r u) (ξ : Hₛ) (x : Iₛ) :
    sLocalTraceCutoffKernel f ρ r (ξ.val * x) x.val =
      ρ (ξ.val * x) * (sLocalTraceMeasureFactor S : ℂ) *
        ∫ u, r u * fourierₛ (sLocalTraceEta f ξ) (x.val * u) ∂νₛ := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace Aₛ := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SigmaCompactSpace Aₛ := inferInstanceAs (SigmaCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : (νₛ).Regular := addHaar_regular_of_sigmaCompactSpace νₛ
  let φ (u : Aₛ) := r u * fourierₛ (sLocalTraceEta f ξ) (x.val * u)
  have h (u : Aₛ) : r u * ((sLocalTraceMeasureFactor S : ℂ) *
      fourierₛ (sLocalTraceEta f ξ) (-(x.val * u))) =
      (sLocalTraceMeasureFactor S : ℂ) * φ (-u) := by
    rw [show φ (-u) = r u * fourierₛ (sLocalTraceEta f ξ) (-(x.val * u)) by simp [φ, heven]]
    ring
  unfold sLocalTraceCutoffKernel
  simp_rw [sLocalTraceDilationKernel_skew_frequency, h]
  rw [integral_const_mul, integral_neg_eq_self, mul_assoc]

private theorem sLocalTrace_integrable_symbol_dilate (p : Aₛ → ℂ) (hp : Integrable p νₛ) (x : Iₛ) (r : Aₛ → ℂ)
    (hr : Measurable r) (M : ℝ) (hb : ∀ u, ‖r u‖ ≤ M) :
    Integrable (fun u ↦ r u * p (x.val * u)) νₛ := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace Aₛ := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let e := DistribMulAction.toAddEquiv Aₛ x
  have hc : Continuous e := continuous_const.mul continuous_id
  have hci : Continuous e.symm := continuous_const.mul continuous_id
  let m := (νₛ).map e
  let hm : m.IsAddHaarMeasure := e.isAddHaarMeasure_map νₛ hc hci
  have hi : Integrable p m := by
    rw [Measure.isAddLeftInvariant_eq_smul m νₛ]
    exact hp.smul_measure_nnreal
  have hd : Integrable (fun u ↦ p (x.val * u)) νₛ := hi.comp_measurable hc.measurable
  simpa only [mul_comm] using hd.mul_bdd hr.aestronglyMeasurable (ae_of_all _ hb)

end

namespace SLocalTraceEta

open Topology

private theorem containing {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] {K : Set G} (hK : IsCompact K) :
    ∃ H : OpenCompactlyGeneratedSubgroups G, K ⊆ (H.val : Set G) := by
  obtain ⟨U, hU, hU₁⟩ := exists_compact_mem_nhds (1 : G)
  let H := Subgroup.closure (U ∪ K)
  have hSubset : U ∪ K ⊆ (H : Set G) := Subgroup.subset_closure
  have hOpen : IsOpen (H : Set G) :=
    H.isOpen_of_mem_nhds (mem_of_superset hU₁ (subset_union_left.trans hSubset))
  refine ⟨⟨H, hOpen, ⟨Subtype.val ⁻¹' (U ∪ K), ?_, ?_, ?_⟩⟩,
    subset_union_right.trans hSubset⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds
      (mem_of_superset hU₁ subset_union_left)
  · exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' (hU.union hK)
      (Subtype.range_coe.symm ▸ hSubset)
  · exact Subgroup.closure_preimage_eq_top _

/-- Pull a joint Bruhat-smooth test back along an entire real vector group. -/
private theorem smooth_vector_pullback {G E : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Multiplicative E →* G) (hj : Continuous j) (f : G → ℂ) (hf : IsBruhatSmooth f)
    (g : G) : ContDiff ℝ (⊤ : ℕ∞) (fun v : E ↦ f (g * j (Multiplicative.ofAdd v))) := by
  classical
  rw [contDiff_infty]
  intro n
  obtain ⟨k,hk,_,hd⟩ := hf n
  obtain ⟨H,hH⟩ := containing ((isCompact_singleton (x := g)).union hk.isCompact)
  let a : BruhatStructuralPair G := ⟨(H.val, OrderDual.toDual k), H.property.1, H.property.2,
    hk, fun _ hx ↦ hH (Or.inr hx)⟩
  have hg : g ∈ a.val.1 := hH (Or.inl rfl)
  have hJ (v : Multiplicative E) : j v ∈ a.val.1 := by
    let : PreconnectedSpace (Multiplicative E) := inferInstanceAs (PreconnectedSpace E)
    apply (isPreconnected_range hj).subset_isClopen
      ⟨a.val.1.isClosed_of_isOpen a.property.1, a.property.1⟩
      ⟨1, ⟨1, j.map_one⟩, a.val.1.one_mem⟩ ⟨v,rfl⟩
  obtain ⟨e⟩ := a.elementary
  obtain ⟨f₀, heval, hs⟩ := hd a rfl
  let θm := e.equiv.toMulEquiv.toMonoidHom.comp ((QuotientGroup.mk' _).comp (j.codRestrict _ hJ))
  let θ := AddMonoidHom.toMultiplicative.symm θm
  have hθ : Continuous θ := e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp
    (hj.subtype_mk _))
  let R := (AddMonoidHom.fst _ _).comp θ
  let T := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp θ)
  choose l hl using fun i : Fin e.torusDim ↦ exists_addCircle_coe_linearMap_eq
    ((Pi.evalAddMonoidHom _ i).comp T) ((continuous_apply i).comp hθ.snd.fst)
  let L := (R.toRealLinearMap hθ.fst).prod
    ((EuclideanSpace.equiv (Fin e.torusDim) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi l))
  let c := (e.equiv (QuotientGroup.mk (⟨g,hg⟩ : a.val.1))).toAdd
  obtain ⟨t, ht⟩ := elementaryCover_surjective c.2.2.1 c.2.2.2 c.1 c.2.1
  have hv (v : E) : elementaryCover (L v + (c.1,t)) c.2.2.1 c.2.2.2 = θ v + c := by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      change ((l i v + t i : ℝ) : AddCircle (1 : ℝ)) = (θ v).2.1 i + c.2.1 i
      rw [AddCircle.coe_add, hl i v]
      exact congrArg ((θ v).2.1 i + ·) (congrArg (fun y ↦ y.2.1 i) ht)
    · have h := hθ.snd.snd.isConst_of_preconnectedSpace v 0
      rw [map_zero θ] at h
      change c.2.2 = (θ v).2.2 + c.2.2
      rw [h]; exact (zero_add _).symm
  have h := (hs e c.2.2.1 c.2.2.2).comp (L.contDiff.add (contDiff_const (c := (c.1,t))))
  convert h using 1
  funext v
  symm
  simp only [Function.comp_apply, hv, ofAdd_add]
  rw [mul_comm]
  change f₀ (e.equiv.symm (e.equiv _ * e.equiv _)) = _
  rw [← map_mul, e.equiv.symm_apply_apply]
  exact heval (⟨g,hg⟩ * ⟨j (Multiplicative.ofAdd v),hJ _⟩)

local notation "X∞" => mixedEmbedding.mixedSpace F
local notation "coord" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "Bₛ" => ((v : S) → v.val.adicCompletion F)

private def archExp : Multiplicative X∞ →* Iₛ :=
  MonoidHom.toHomUnits
    { toFun := fun v ↦ ((coord).symm (NormedSpace.exp v.toAdd), 1)
      map_one' := Prod.ext (by change (coord).symm (NormedSpace.exp 0) = 1; rw [NormedSpace.exp_zero, map_one]) rfl
      map_mul' := fun v w ↦ Prod.ext (by change (coord).symm (NormedSpace.exp (v.toAdd + w.toAdd)) = _; rw [NormedSpace.exp_add, map_mul]; rfl) (one_mul _).symm }

private theorem archExp_continuous : Continuous (archExp (F := F) (S := S)) := by
  apply (sIdeleGroup_description F S).1.continuous_iff.mpr
  exact ((continuous_infiniteAdeleRingEquivMixedSpace_symm F).comp
    ((NormedSpace.exp_continuous (𝔸 := X∞)).comp continuous_toAdd)).prodMk continuous_const

private theorem norm_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Multiplicative E →* Iₛ) (hj : Continuous j) (g : Iₛ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : E ↦ (normS(g * j (Multiplicative.ofAdd v)))) := by
  have hn : Continuous (fun t : Iₛ ↦ normS(t)) := by
    have h : Continuous fun t : Iₛ ↦ sIdeleQuotientNorm F S (QuotientGroup.mk t) :=
      (isProperMap_sIdeleQuotientNorm F S).continuous.comp continuous_quot_mk
    exact NNReal.continuous_coe.comp (Units.continuous_val.comp h)
  have hp (t : Iₛ) : 0 < normS(t) := NNReal.coe_pos.mpr (Units.zero_lt _)
  let A : E →+ ℝ :=
    { toFun := fun v ↦ Real.log (normS(j (Multiplicative.ofAdd v)))
      map_zero' := by simp
      map_add' := fun x y ↦ by simp only [ofAdd_add, map_mul, Units.val_mul, NNReal.coe_mul,
        Real.log_mul (hp _).ne' (hp _).ne'] }
  have hc : Continuous A := (hn.comp (hj.comp continuous_ofAdd)).log fun v ↦ (hp _).ne'
  have h := contDiff_const (n := (⊤ : ℕ∞)) (c := normS(g)) |>.mul
    (Real.contDiff_exp.comp (A.toRealLinearMap hc).contDiff)
  convert h using 1
  funext v
  change normS(g * j (Multiplicative.ofAdd v)) = _ * Real.exp (Real.log _)
  simp [Real.exp_log (hp _)]

private theorem archLog :
    ∃ L : X∞ → X∞, ContDiffAt ℝ (⊤ : ℕ∞) L 1 ∧ ∀ᶠ y in 𝓝 1, NormedSpace.exp (L y) = y := by
  let E := X∞
  let exp := NormedSpace.exp (𝔸 := E)
  let A := ContinuousLinearEquiv.refl ℝ E
  have hd : HasFDerivAt exp (A : E →L[ℝ] E) 0 := hasFDerivAt_exp_zero
  have hc : ContDiffAt ℝ (⊤ : ℕ∞) exp 0 := (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt
  have hs := hc.hasStrictFDerivAt hd (by simp)
  have h0 : (hs.toOpenPartialHomeomorph exp).symm (exp 0) = 0 := hs.localInverse_apply_image
  have hL := (hs.toOpenPartialHomeomorph exp).contDiffAt_symm hs.image_mem_toOpenPartialHomeomorph_target
    (by rw [h0]; exact hd) (by rw [h0]; exact hc)
  have hr := hs.eventually_right_inverse
  simpa [exp] using (show ∃ L : E → E, ContDiffAt ℝ (⊤ : ℕ∞) L (exp 0) ∧
    ∀ᶠ y in 𝓝 (exp 0), exp (L y) = y from ⟨_, hL, hr⟩)

private theorem eta_on_units (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (t : Iₛ) :
    sLocalTraceEta f ξ (t.val - 1) =
      f.val ((ξ.val⁻¹ * t)⁻¹) / (Real.sqrt (normS(ξ.val⁻¹ * t)) : ℂ) := by
  unfold sLocalTraceEta
  rw [show (1 : Aₛ) + (t.val - 1) = t.val by abel, Units.val_injective.extend_apply]

private theorem eta_log_chart (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (t : Iₛ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : X∞ ↦
      sLocalTraceEta f ξ ((t * archExp (Multiplicative.ofAdd v)).val - 1)) := by
  let j := archExp (F := F) (S := S)
  let g := ξ.val⁻¹ * t
  have hf := smooth_vector_pullback j archExp_continuous f.val
    ((mem_bruhatSmoothSubmodule_iff _).1 f.property.1) g⁻¹
  have hp (v : X∞) : 0 < normS(g * j (Multiplicative.ofAdd v)) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hn := (norm_curve j archExp_continuous g).sqrt (fun v ↦ (hp v).ne')
  have hden : ContDiff ℝ (⊤ : ℕ∞) (fun v : X∞ ↦ (Real.sqrt (normS(g * j (Multiplicative.ofAdd v))) : ℂ)) := Complex.ofRealCLM.contDiff.comp hn
  let H (v : X∞) := f.val (g⁻¹ * j (Multiplicative.ofAdd (-v))) *
    ((Real.sqrt (normS(g * j (Multiplicative.ofAdd v))) : ℂ))⁻¹
  have hs : ContDiff ℝ (⊤ : ℕ∞) H := (hf.comp (contDiff_neg (𝕜 := ℝ))).mul (hden.inv
    (fun v ↦ Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp v)).ne'))
  have he (v : X∞) : sLocalTraceEta f ξ ((t * j (Multiplicative.ofAdd v)).val - 1) = H v := by
    rw [eta_on_units, ← mul_assoc]
    change f.val ((g * j (Multiplicative.ofAdd v))⁻¹) / _ = _
    rw [mul_inv_rev, mul_comm (j _)⁻¹, div_eq_mul_inv]
    unfold H
    rw [ofAdd_neg, map_inv]
  change ContDiff ℝ (⊤ : ℕ∞) (fun v : X∞ ↦ sLocalTraceEta f ξ ((t * j (Multiplicative.ofAdd v)).val - 1))
  simp_rw [he]
  exact hs

private theorem eta_arch_slice_smooth (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (b : Bₛ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : X∞ ↦ sLocalTraceEta f ξ ((coord).symm y,b)) := by
  let Z := (fun g : Iₛ ↦ (ξ.val * g⁻¹).val - 1) '' tsupport f.val
  have hc : IsCompact Z := f.property.2.image
    ((Units.continuous_val.comp (continuous_const.mul continuous_inv)).sub continuous_const)
  let Y (y : X∞) : Aₛ := ((coord).symm y,b)
  have hY : Continuous Y := (continuous_infiniteAdeleRingEquivMixedSpace_symm F).prodMk continuous_const
  have hzero (z : Aₛ) (hz : z ∉ Z) : sLocalTraceEta f ξ z = 0 := by
    by_cases hu : 1 + z ∈ range (Units.val : Iₛ → Aₛ)
    · obtain ⟨t, ht⟩ := hu
      have he : z = t.val - 1 := by rw [ht]; abel
      rw [he, eta_on_units]
      have hnot : (ξ.val⁻¹ * t)⁻¹ ∉ tsupport f.val := fun h ↦ hz
        ⟨_, h, by simp [ht]⟩
      rw [image_eq_zero_of_notMem_tsupport hnot, zero_div]
    · exact Function.extend_apply' _ _ _ hu
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : Y y ∈ Z
  · obtain ⟨g, _, hgy⟩ := hy
    let t := ξ.val * g⁻¹
    have ht : t.val - 1 = Y y := hgy
    have h1 : coord t.val.1 = 1 + y := by
      have hh := congrArg (fun z : Aₛ ↦ coord z.1) ht
      change coord (t.val.1 - 1) = coord ((coord).symm y) at hh
      rw [map_sub, map_one, RingEquiv.apply_symm_apply] at hh
      linear_combination hh
    let a := coord ((t⁻¹).val.1)
    have ha : coord t.val.1 * a = 1 := by
      rw [show a = coord ((t⁻¹).val.1) by rfl, ← map_mul,
        show t.val.1 * (t⁻¹).val.1 = 1 from congrArg Prod.fst t.mul_inv, map_one]
    let N (w : X∞) := (1+w)*a
    have hN : ContDiff ℝ (⊤ : ℕ∞) N := (contDiff_const.add contDiff_id).mul contDiff_const
    have hNy : N y = 1 := by change (1+y)*a = 1; rwa [← h1]
    obtain ⟨L,hL,hEL⟩ := archLog (F := F)
    have hlim : Tendsto N (𝓝 y) (𝓝 1) := hNy ▸ hN.continuous.tendsto y
    have hc' := (eta_log_chart f ξ t).contDiffAt.comp y
      ((show ContDiffAt ℝ (⊤ : ℕ∞) L (N y) from hNy.symm ▸ hL).comp y hN.contDiffAt)
    refine hc'.congr_of_eventuallyEq ?_
    filter_upwards [hlim.eventually hEL] with w hw
    apply congrArg (sLocalTraceEta f ξ)
    apply Prod.ext
    · apply (coord).injective
      change coord ((coord).symm w) = coord (t.val.1 * (coord).symm (NormedSpace.exp (L (N w))) - 1)
      rw [RingEquiv.apply_symm_apply, map_sub, map_one, map_mul, RingEquiv.apply_symm_apply, hw]
      change w = coord t.val.1 * ((1+w)*a) - 1
      rw [mul_left_comm, ha, mul_one]; abel
    · change b = t.val.2 * 1 - 1
      rw [mul_one]; exact (congrArg Prod.snd ht).symm
  · let : T2Space Aₛ := inferInstanceAs (T2Space
      (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hY.continuousAt.preimage_mem_nhds (hc.isClosed.isOpen_compl.mem_nhds hy)] with w hw
    exact hzero _ hw

/-- A cyclic subgroup small on a compact generating set of the annihilator
lies in the original closed subgroup. -/
private theorem smallPowers {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (K : Subgroup G) (hK : IsBruhatGoodSubgroup K) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x : G, (∀ n : ℕ, x ^ n ∈ W) → x ∈ K := by
  let D := lcaAnnihilator K
  obtain ⟨C, _, hc, hgen⟩ := hK.2.2
  let arc := Circle.centeredArc (Real.pi / 2)
  have ha : arc ∈ 𝓝 (1 : Circle) := by
    simpa [arc] using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  let W := {x : G | ∀ χ ∈ C, (χ : D).val x ∈ arc}
  have hW : W ∈ 𝓝 (1 : G) := by
    apply hc.eventually_forall_of_forall_eventually
    intro χ _
    have hχ : Continuous (fun χ : D ↦ (χ.val : G →ₜ* Circle)) := continuous_subtype_val
    have he : Continuous (fun p : G × D ↦ p.2.val p.1) :=
      (continuous_eval (F := G →ₜ* Circle)).comp ((hχ.comp ((show Continuous (Prod.snd : G × D → D) from continuous_snd))).prodMk continuous_fst)
    exact he.continuousAt.preimage_mem_nhds (by simpa only [map_one] using ha)
  refine ⟨W, hW, fun x hx ↦ ?_⟩
  let ev : D →* Circle := ⟨⟨fun χ ↦ χ.val x, rfl⟩, fun _ _ ↦ rfl⟩
  have hg : C ⊆ ev.ker := by
    intro χ hχ
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    change χ.val x ^ n ∈ arc
    simpa only [map_pow] using hx n χ hχ
  have htop : ⊤ ≤ ev.ker := hgen ▸ (Subgroup.closure_le _).mpr hg
  rw [← lcaDualAnnihilator_annihilator K hK.1, mem_lcaDualAnnihilator_iff]
  exact fun χ ↦ htop (Subgroup.mem_top χ)

private theorem power_bound {L : Type*} [NormedField L] [IsUltrametricDist L]
    (y : L) (hy : ‖y‖ ≤ 1) (n : ℕ) : ‖y ^ n - 1‖ ≤ ‖y - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, show y ^ n * y - 1 = (y ^ n - 1) * y + (y - 1) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      (by rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans ih) le_rfl)

/-- A single finite principal-unit neighborhood fixes an arbitrary joint test. -/
private theorem finite_principal_units (f : BruhatCompactSupport Iₛ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ e : Iₛ, e.val.1 = 1 →
      (∀ v : S, ‖e.val.2 v - 1‖ < r) → ∀ g, f.val (e * g) = f.val g := by
  obtain ⟨K, hK, hfix, _⟩ := ((mem_bruhatSmoothSubmodule_iff _).1 f.property.1) 0
  obtain ⟨W, hW, hsub⟩ := smallPowers K hK
  rw [(sIdeleGroup_description F S).1.nhds_eq_comap] at hW
  obtain ⟨O, hV, hv⟩ := mem_comap.mp hW
  have hpre : (fun b : Bₛ ↦ ((1,b) : Aₛ)) ⁻¹' O ∈ 𝓝 (1 : Bₛ) :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hV
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min d 1, lt_min hd zero_lt_one, min_le_right .., fun e he he' g ↦ ?_⟩
  apply hfix ⟨e, hsub e (fun n ↦ hv ?_)⟩ g
  change (e ^ n).val ∈ O
  have harch : (e ^ n).val.1 = 1 := by simp [he]
  rw [show (e ^ n).val = (1, (e ^ n).val.2) from Prod.ext harch rfl]
  apply hball
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hd]
  intro v
  change ‖e.val.2 v ^ n - 1‖ < d
  have hy : ‖e.val.2 v‖ ≤ 1 := by
    simpa using (IsUltrametricDist.norm_add_le_max (e.val.2 v - 1) 1).trans
      (max_le ((he' v).le.trans (min_le_right ..)) (norm_one.le))
  exact (power_bound _ hy n).trans_lt ((he' v).trans_le (min_le_left ..))

private theorem eta_finite_invariance (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    ∃ (r : ℝ) (U : OpenAddSubgroup Bₛ), 0 < r ∧ (∀ h : Bₛ, h ∈ U ↔ ∀ v, ‖h v‖ < r) ∧
      ∀ (z : Aₛ) (h : Bₛ), h ∈ U → sLocalTraceEta f ξ (z + (0,h)) = sLocalTraceEta f ξ z := by
  classical
  obtain ⟨r, hr, hr1, hfix⟩ := finite_principal_units f
  let d := ξ.val
  have hct : Continuous (fun g : Iₛ ↦ ((d * g⁻¹)⁻¹).val.2) :=
    continuous_snd.comp (Units.continuous_val.comp (continuous_const.mul continuous_inv).inv)
  obtain ⟨M, hM⟩ := f.property.2.exists_bound_of_continuousOn hct.continuousOn
  let C := max 1 M
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left ..)
  let b := r / C
  have hb : 0 < b := div_pos hr hC
  let P : AddSubgroup Bₛ :=
    { carrier := {h | ∀ v, ‖h v‖ < b}
      zero_mem' := fun v ↦ by simpa using hb
      add_mem' := fun ha hb' v ↦ (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (ha v) (hb' v))
      neg_mem' := fun ha v ↦ by simpa using ha v }
  have hball : (P : Set Bₛ) = Metric.ball 0 b := by
    ext h
    simp only [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hb]
    rfl
  let U : OpenAddSubgroup Bₛ := ⟨P, by change IsOpen (P : Set Bₛ); rw [hball]; exact Metric.isOpen_ball⟩
  have hsmall (z : Aₛ) (h : Bₛ) (hh : h ∈ U) (hz : sLocalTraceEta f ξ z ≠ 0) :
      sLocalTraceEta f ξ (z + (0,h)) = sLocalTraceEta f ξ z := by
    obtain ⟨t, ht⟩ : 1 + z ∈ range (Units.val : Iₛ → Aₛ) := by
      by_contra hn
      exact hz (Function.extend_apply' _ _ _ hn)
    have he : z = t.val - 1 := by rw [ht]; abel
    subst z
    rw [eta_on_units] at hz ⊢
    let g := (d⁻¹ * t)⁻¹
    have hg : g ∈ tsupport f.val := subset_tsupport f.val (by
      intro he
      exact hz (by change f.val g / _ = 0; rw [he, zero_div]))
    have ht' : d * g⁻¹ = t := by simp [g]
    have hbound : ‖(t⁻¹).val.2‖ ≤ C := by
      simpa only [ht'] using (hM g hg).trans (le_max_right 1 M)
    let a := h * (t⁻¹).val.2
    have ha (v : S) : ‖a v‖ < r := by
      change ‖h v * (t⁻¹).val.2 v‖ < r
      rw [norm_mul]
      calc
        _ ≤ ‖h v‖ * C := mul_le_mul_of_nonneg_left
          ((norm_le_pi_norm _ v).trans hbound) (norm_nonneg _)
        _ < r := (lt_div_iff₀ hC).mp (show ‖h v‖ < b from hh v)
    have hn (v : S) : ‖1 + a v‖ = 1 := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_one, max_eq_left ((ha v).le.trans hr1)]
      rw [norm_one]
      exact ((ha v).trans_le hr1).ne'
    let m : Aₛ := (1, 1 + a)
    have hm : IsUnit m := Prod.isUnit_iff.mpr ⟨isUnit_one, Pi.isUnit_iff.mpr (fun v ↦
      isUnit_iff_ne_zero.mpr (norm_pos_iff.mp ((hn v).symm ▸ zero_lt_one)))⟩
    let e := hm.unit
    have hval : e.val = m := hm.unit_spec
    have hnorm : sIdeleNorm F S e = 1 := by
      apply Units.ext
      apply NNReal.eq
      have h1 (w : InfinitePlace F) : (1 : InfiniteAdeleRing F) w = 1 := rfl
      simp [sIdeleNorm, Units.coe_prod, hval, m, hn, h1]
    have hv : (e * t).val - 1 = t.val - 1 + (0,h) := by
      have hh' : (t⁻¹).val.2 * t.val.2 = 1 := congrArg Prod.snd t.inv_mul
      rw [Units.val_mul, hval]
      apply Prod.ext
      · simp [m]
      · change (1 + h * (t⁻¹).val.2) * t.val.2 - 1 = t.val.2 - 1 + h
        rw [add_mul, one_mul, mul_assoc, hh', mul_one]
        abel
    rw [← hv, eta_on_units]
    have hi := hfix e (by rw [hval]) (fun v ↦ by simpa [hval, m] using ha v) ((d⁻¹ * (e*t))⁻¹)
    rw [show e * (d⁻¹ * (e*t))⁻¹ = g by simp [g, mul_comm, mul_left_comm]] at hi
    change f.val ((d⁻¹ * (e*t))⁻¹) / _ = f.val g / _
    rw [← hi, show ξ.val⁻¹ * (e*t) = e * (ξ.val⁻¹*t) by ac_rfl, map_mul, hnorm, one_mul]
  refine ⟨b, U, hb, fun _ ↦ Iff.rfl, fun z h hh ↦ ?_⟩
  by_cases hz : sLocalTraceEta f ξ z = 0
  · by_contra he
    have hne : sLocalTraceEta f ξ (z + (0,h)) ≠ 0 := hz ▸ he
    apply he
    simpa only [show ((0,-h) : Aₛ) = -(0,h) by simp, add_neg_cancel_right] using (hsmall (z + (0,h)) (-h) (U.neg_mem hh) hne).symm
  · exact hsmall z h hh hz

/-- The finite coordinates descend to a discrete quotient, and only finitely
many quotient classes support a nonzero archimedean slice. -/
private theorem eta_finite_slices (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    ∃ (r : ℝ) (U : OpenAddSubgroup Bₛ), 0 < r ∧ (∀ h : Bₛ, h ∈ U ↔ ∀ v, ‖h v‖ < r) ∧
      ∃ C : Finset (Bₛ ⧸ U.toAddSubgroup),
        let slice := fun (q : Bₛ ⧸ U.toAddSubgroup) (a : InfiniteAdeleRing F) ↦ sLocalTraceEta f ξ (a,q.out)

        (∀ z : Aₛ, sLocalTraceEta f ξ z = slice (QuotientAddGroup.mk z.2) z.1) ∧
        ∀ q ∉ C, ∀ a, slice q a = 0 := by
  classical
  obtain ⟨r,U,hr,hU,hi⟩ := eta_finite_invariance f ξ
  let Q := Bₛ ⧸ U.toAddSubgroup
  let : DiscreteTopology Q := QuotientAddGroup.discreteTopology U.isOpen
  let π : Bₛ → Q := QuotientAddGroup.mk
  let c (g : Iₛ) : Q := π (((ξ.val * g⁻¹).val - 1).2)
  have hc : Continuous c := QuotientAddGroup.continuous_mk.comp (continuous_snd.comp
    ((Units.continuous_val.comp (continuous_const.mul continuous_inv)).sub continuous_const))
  let C := (f.property.2.image hc).finite_of_discrete.toFinset
  let slice (q : Q) (a : InfiniteAdeleRing F) := sLocalTraceEta f ξ (a, q.out)
  refine ⟨r,U,hr,hU,C, fun z ↦ ?_, fun q hq a ↦ ?_⟩
  · have he : π (π z.2).out = π z.2 := Quotient.out_eq _
    have hh := QuotientAddGroup.eq_iff_sub_mem.mp he
    have h := hi z _ hh
    change sLocalTraceEta f ξ z = sLocalTraceEta f ξ (z.1, (π z.2).out)
    rw [← h]
    congr 1
    exact Prod.ext (add_zero _) (by change z.2 + ((π z.2).out - z.2) = _; abel)
  · by_contra hn
    let z : Aₛ := (a, q.out)
    have hz : sLocalTraceEta f ξ z ≠ 0 := hn
    obtain ⟨t, ht⟩ : 1 + z ∈ range (Units.val : Iₛ → Aₛ) := by
      by_contra hu
      exact hz (Function.extend_apply' _ _ _ hu)
    have ht' : t.val - 1 = z := by rw [ht]; abel
    rw [← ht', eta_on_units] at hz
    let g := (ξ.val⁻¹ * t)⁻¹
    have hg : g ∈ tsupport f.val := subset_tsupport f.val (by
      intro he
      exact hz (by change f.val g / _ = 0; rw [he, zero_div]))
    apply hq
    apply (f.property.2.image hc).finite_of_discrete.mem_toFinset.mpr
    refine ⟨g, hg, ?_⟩
    change π (((ξ.val * g⁻¹).val - 1).2) = q
    rw [show ξ.val * g⁻¹ = t by simp [g], ht']
    exact Quotient.out_eq _

private theorem eta_compact (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    HasCompactSupport (sLocalTraceEta f ξ) := by
  let φ (g : Iₛ) : Aₛ := (ξ.val * g⁻¹).val - 1
  have hc : Continuous φ :=
    (Units.continuous_val.comp (continuous_const.mul continuous_inv)).sub continuous_const
  apply HasCompactSupport.intro (f.property.2.image hc)
  intro z hz
  unfold sLocalTraceEta
  by_cases hu : 1 + z ∈ range (Units.val : Iₛ → Aₛ)
  · obtain ⟨t, ht⟩ := hu
    rw [← ht, Units.val_injective.extend_apply]
    have hn : (ξ.val⁻¹ * t)⁻¹ ∉ tsupport f.val := by
      intro h
      apply hz
      refine ⟨_, h, ?_⟩
      simp [φ, ht]
    rw [image_eq_zero_of_notMem_tsupport hn, zero_div]
  · exact Function.extend_apply' _ _ _ hu

private theorem arch_test (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (b : Bₛ) :
    ∃ φ : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)), ∀ a : InfiniteAdeleRing F,
      φ (Multiplicative.ofAdd a) = sLocalTraceEta f ξ (a,b) := by
  let p (a : InfiniteAdeleRing F) := sLocalTraceEta f ξ (a,b)
  let Y (y : X∞) : Aₛ := ((coord).symm y,b)
  have hcs : HasCompactSupport (fun y ↦ sLocalTraceEta f ξ (Y y)) := by
    refine HasCompactSupport.intro ((eta_compact f ξ).image
      ((continuous_infiniteAdeleRingEquivMixedSpace F).comp continuous_fst)) fun y hy ↦ ?_
    apply image_eq_zero_of_notMem_tsupport
    exact fun h ↦ hy ⟨Y y,h, (coord).apply_symm_apply y⟩
  have hm := (mem_archimedeanSchwartzBruhat_iff (F := F) p).2
    ⟨hcs.toSchwartzMap (eta_arch_slice_smooth f ξ b), fun a ↦ by
      change sLocalTraceEta f ξ ((coord).symm (coord a), b) = _
      rw [RingEquiv.symm_apply_apply]⟩
  exact ⟨⟨_,hm⟩, fun _ ↦ rfl⟩

private theorem finite_ball_test (v : S) (a : v.val.adicCompletion F) (r : ℝ) :
    ∃ φ : SchwartzBruhat (Multiplicative (v.val.adicCompletion F)), ∀ y : v.val.adicCompletion F,
      φ (Multiplicative.ofAdd y) = if ‖y-a‖ < r then (1 : ℂ) else 0 := by
  classical
  let : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let U := Metric.ball a r
  have hc : IsClopen U := IsUltrametricDist.isClopen_ball _ _
  apply (mem_finitePlaceSchwartz_iff (F := F) v.val _).2
  constructor
  · apply (IsLocallyConstant.iff_exists_open _).2
    intro x
    by_cases h : x ∈ U
    · refine ⟨U,hc.isOpen,h,fun y hy ↦ ?_⟩
      simp only [Metric.mem_ball, dist_eq_norm, U] at h hy
      simp [h,hy]
    · refine ⟨Uᶜ,hc.isClosed.isOpen_compl,h,fun y hy ↦ ?_⟩
      change y ∉ U at hy
      simp only [Metric.mem_ball, dist_eq_norm, U] at h hy
      simp [h,hy]
  · apply HasCompactSupport.intro (isCompact_closedBall a r)
    intro x hx
    exact ite_eq_right (fun h ↦ hx (Metric.ball_subset_closedBall (by simpa [dist_eq_norm] using h)))

open scoped TensorProduct in
/-- Paper: (12.4.1.20)–(12.4.1.21), p. 518. The translated, zero-extended test
is an additive Schwartz–Bruhat function on the S-adeles.
Deviation: The input can depend jointly on all places. Compact support and finite
translation invariance give a finite expansion in compact-open coset indicators. -/
theorem eta_test (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    ∃ η : testₛ, ∀ z : Aₛ, testAt(η,z) = sLocalTraceEta f ξ z := by
  classical
  obtain ⟨r,U,_,hU,C,hval,hzero⟩ := eta_finite_slices f ξ
  let Q := Bₛ ⧸ U.toAddSubgroup
  let π : Bₛ → Q := QuotientAddGroup.mk
  choose A hA using fun q : Q ↦ arch_test f ξ q.out
  choose B hB using fun (q : Q) (v : S) ↦ finite_ball_test v (q.out v) r
  obtain ⟨T,hT⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  let t (q : Q) : testₛ := T (A q ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, B q v))
  have hprod (q : Q) (b : Bₛ) : (∀ v, ‖b v - q.out v‖ < r) ↔ π b = q := by
    calc
      _ ↔ b - q.out ∈ U := (hU _).symm
      _ ↔ π b = π q.out := QuotientAddGroup.eq_iff_sub_mem.symm
      _ ↔ π b = q := by rw [show π q.out = q from Quotient.out_eq q]
  have ht (q : Q) (z : Aₛ) : testAt(t q,z) =
      if π z.2 = q then sLocalTraceEta f ξ (z.1,q.out) else 0 := by
    change T _ _ = _
    rw [hT, hA]
    simp_rw [hB]
    simp only [Fintype.prod_ite_zero, hprod q z.2, Finset.prod_const_one]
    split_ifs <;> simp
  refine ⟨∑ q ∈ C, t q, fun z ↦ ?_⟩
  have he : ∀ D : Finset Q, testAt(∑ q ∈ D, t q,z) = ∑ q ∈ D, testAt(t q,z) := by
    intro D
    induction D using Finset.induction_on with
    | empty => rfl
    | insert q D h ih =>
      simp only [Finset.sum_insert h]
      change testAt(t q,z) + _ = _
      rw [← ih]
  rw [he]
  simp_rw [ht]
  by_cases hz : π z.2 ∈ C
  · rw [Finset.sum_eq_single_of_mem (π z.2) hz (fun q _ hq ↦ ite_eq_right (Ne.symm hq)), ite_eq_left rfl]
    exact (hval z).symm
  · rw [Finset.sum_eq_zero fun q hq ↦ ite_eq_right (show π z.2 ≠ q from fun h ↦ hz (h.symm ▸ hq)), hval z]
    exact (hzero _ hz _).symm

end SLocalTraceEta

/-- Paper: (12.4.1.21)–(12.4.1.22), p. 518. The additive Tamagawa Fourier transform
of the translated, zero-extended S-idelic test is integrable.
Deviation: Step III uses Fourier integration on p. 518. We state explicitly the
absolute integrability required for the constant frequency symbol. -/
private theorem sLocalTraceEta_fourier_integrable (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    Integrable (fourierₛ (sLocalTraceEta f ξ)) νₛ := by
  obtain ⟨η, hη⟩ := SLocalTraceEta.eta_test f ξ
  let G := Multiplicative Aₛ
  let μ : Measure G := νₛ
  have hν : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hν.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hν.toIsOpenPosMeasure
      map_mul_left_eq_self := fun y ↦ hν.map_add_left_eq_self y.toAdd }
  let (v : S) : LocallyCompactSpace (v.val.adicCompletion F) := locallyCompactSpace_adicCompletion _
  let : T2Space G := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace Aₛ)
  let : BorelSpace G := sAdeleRing_borelSpace (F := F) (S := S)
  rw [← funext hη]
  exact SchwartzBruhat.integrable μ (sAdeleSchwartzFourier η)

/-- Paper: (12.4.1.12)–(12.4.1.22), pp. 517–518. The skew diagonal of the
composed kernel is the integral of the Fourier transform of the translated test,
weighted by both cutoffs.
Deviation: Retain the cutoffs in the exact identity, and write the skew diagonal
with its output first. Measurable bounded even frequency symbols suffice here. -/
theorem sLocalTraceCutoffKernel_skew (f : BruhatCompactSupport Iₛ)
    (ρ : Iₛ → ℂ) (ρ' : Aₛ → ℂ) (_hρ' : Measurable ρ')
    (_hBound : ∃ C : ℝ, ∀ u, ‖ρ' u‖ ≤ C) (_hEven : ∀ u, ρ' (-u) = ρ' u)
    (ξ : Hₛ) (x : Iₛ) :
    Integrable (fun u ↦ ρ' u * fourierₛ (sLocalTraceEta f ξ) (x.val * u)) νₛ ∧
      sLocalTraceCutoffKernel f ρ ρ' (ξ.val * x) x.val =
        ρ (ξ.val * x) * (sLocalTraceMeasureFactor S : ℂ) *
          ∫ u, ρ' u * fourierₛ (sLocalTraceEta f ξ) (x.val * u) ∂νₛ := by
  obtain ⟨M, hM⟩ := _hBound
  exact ⟨sLocalTrace_integrable_symbol_dilate _ (sLocalTraceEta_fourier_integrable f ξ)
    x ρ' _hρ' M hM, sLocalTraceCutoffKernel_skew_eq f ρ ρ' _hEven ξ x⟩

/-- Paper: (12.4.1.23)–(12.4.1.24), p. 518. One sharp orbital mass integrates
the transformed test against the logarithmic width of the spatial norm interval.
Deviation: This defines the sharp one-sided expression for a product of radii.
The additive integral omits the null nonunit locus before taking its logarithm. -/
def sLocalTraceSharpMass (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (R : ℝ) : ℂ :=
  (volume₁ : ℂ) * ∫ w in band(R) ∩ range (Units.val : Iₛ → Aₛ),
    fourierₛ (sLocalTraceEta f ξ) w * ((Real.log R - Real.log (modS(w)) : ℝ) : ℂ) ∂νₛ

/-- Paper: (12.4.1.24), p. 518. The sharp orbital mass of the zero lift vanishes
at every radius. -/
theorem sLocalTraceSharpMass_zero (ξ : Hₛ) (R : ℝ) :
    sLocalTraceSharpMass (0 : BruhatCompactSupport Iₛ) ξ R = 0 := by
  have h0 : sLocalTraceEta (0 : BruhatCompactSupport Iₛ) ξ = 0 := by
    funext z
    have h : (0 : BruhatCompactSupport Iₛ).val = 0 := rfl
    simp only [sLocalTraceEta, h]
    simp
  have h1 : fourierₛ (0 : Aₛ → ℂ) = 0 := by
    funext w; simp [tamagawaFourier]
  simp [sLocalTraceSharpMass, h0, h1]

/-- Paper: (12.4.1.22), p. 518. On the spatial slab the skew diagonal of the sharp
kernel is the measure factor times the Fourier transform of the translated test,
integrated over the frequency band and dilated by the spatial variable. -/
private theorem sLocalTraceSharp_diag (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (L L' : ℝ)
    (x : Iₛ) (hx : normS(x) ≤ L) :
    sLocalTraceCutoffKernel f (indicator {x : Iₛ | normS(x) ≤ L} (fun _ ↦ 1))
        (indicator band(L') (fun _ ↦ 1)) (ξ.val * x) x.val =
      (sLocalTraceMeasureFactor S : ℂ) *
        ∫ u in band(L'), fourierₛ (sLocalTraceEta f ξ) (x.val * u) ∂νₛ := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have hm : Continuous fun t : Aₛ ↦ modS(t) :=
    (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  have hband : MeasurableSet (band(L')) := (isClosed_le hm continuous_const).measurableSet
  have hmeas : Measurable (indicator band(L') (fun _ : Aₛ ↦ (1 : ℂ))) :=
    measurable_const.indicator hband
  have hbd : ∃ C : ℝ, ∀ u, ‖indicator band(L') (fun _ : Aₛ ↦ (1 : ℂ)) u‖ ≤ C :=
    ⟨1, fun u ↦ by by_cases h : u ∈ band(L') <;> simp [h]⟩
  have hneg (u : Aₛ) : -u ∈ band(L') ↔ u ∈ band(L') := by
    have h1 (w : InfinitePlace F) : ‖(-u.1) w‖ = ‖u.1 w‖ := by
      rw [show (-u.1) w = -(u.1 w) from rfl, norm_neg]
    simp [sLocalPWProductRegion, h1]
  have heven (u : Aₛ) : indicator band(L') (fun _ : Aₛ ↦ (1 : ℂ)) (-u) =
      indicator band(L') (fun _ ↦ 1) u := by
    by_cases h : u ∈ band(L')
    · rw [indicator_of_mem ((hneg u).2 h), indicator_of_mem h]
    · rw [indicator_of_notMem (mt (hneg u).1 h), indicator_of_notMem h]
  have hξ : sIdeleNorm F S ξ.val = 1 := by
    obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp ξ.property
    rw [← he]
    exact (sIdeleNorm_spec F S).2 hγ
  have hn : normS(ξ.val * x) ≤ L := by rwa [map_mul, hξ, one_mul]
  rw [(sLocalTraceCutoffKernel_skew f _ _ hmeas hbd heven ξ x).2,
    indicator_of_mem (show ξ.val * x ∈ {x : Iₛ | normS(x) ≤ L} from hn), one_mul,
    ← integral_indicator hband]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
  by_cases h : u ∈ band(L')
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

/-- The S-idelic norm is continuous. -/
private theorem sLocalTrace_sIdeleNorm_continuous : Continuous (sIdeleNorm F S) := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  change Continuous (fun g : Iₛ ↦ ((sIdeleNorm F S g).val))
  simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val]
  change Continuous (fun g : Iₛ ↦ (∏ w : InfinitePlace F, ‖g.val.1 w‖₊ ^ w.mult) *
    ∏ v : S, ‖g.val.2 v‖₊)
  fun_prop

/-- Paper: (12.4.1.17), p. 518. On the S-ideles, multiplicative Tamagawa measure is
additive Tamagawa measure with density the measure factor over the norm. -/
private theorem sLocalTrace_mult_eq_withDensity :
    μₛ = ((νₛ).comap (Units.val : Iₛ → Aₛ)).withDensity
      (fun x ↦ ENNReal.ofReal (sLocalTraceMeasureFactor S / normS(x))) := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F))
  have he := ho.measurableEmbedding
  let n (t : Aₛ) := modS(t)
  have hn (t : Iₛ) : normS(t) = n t.val := by simp [n, sIdeleNorm, Units.coe_prod]
  have hm : Continuous n :=
    (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  let d (t : Aₛ) := ENNReal.ofReal (sLocalTraceMeasureFactor S / n t)
  have hd : Measurable d := (measurable_const.div hm.measurable).ennreal_ofReal
  have hdens : (fun x : Iₛ ↦ ENNReal.ofReal (sLocalTraceMeasureFactor S / normS(x))) =
      fun x ↦ d x.val := funext fun x ↦ by simp only [d, hn]
  rw [hdens]
  refine he.map_injective ?_
  rw [sLocalTrace_measure_density]
  ext t ht
  rw [he.map_apply, withDensity_apply _ (he.measurable ht), withDensity_apply _ ht,
    ← setLIntegral_map ht hd he.measurable, he.map_comap]

/-- A normed field with a nonzero element of norm less than one has no isolated zero. -/
private theorem sLocalTrace_neBot_of_norm_lt_one {K : Type*} [NormedField K] (a : K)
    (ha0 : a ≠ 0) (ha : ‖a‖ < 1) : (𝓝[≠] (0 : K)).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_of_tendsto
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ha) (Eventually.of_forall fun n ↦ pow_ne_zero n ha0))

/-- Zero is not isolated in a finite completion: the powers of a uniformizer tend to it. -/
private theorem sLocalTrace_finite_neBot (v : V) : (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  exact sLocalTrace_neBot_of_norm_lt_one (π : v.adicCompletion F) hπ.ne_zero
    (Valued.toNormedField.norm_lt_one_iff.mpr hπ.val_lt_one)

/-- Zero is not isolated in an infinite completion: the powers of one half tend to it. -/
private theorem sLocalTrace_infinite_neBot (w : InfinitePlace F) :
    (𝓝[≠] (0 : w.Completion)).NeBot := by
  let a : w.Completion := ((WithAbs.equiv w.1).symm (2⁻¹ : F) : WithAbs w.1)
  have h2 : w (2 : F) = 2 := by simpa using w.map_natCast 2
  have hval : ‖a‖ = 2⁻¹ := by
    rw [InfinitePlace.Completion.norm_coe, RingEquiv.apply_symm_apply, map_inv₀, h2]
  refine sLocalTrace_neBot_of_norm_lt_one a (fun h ↦ ?_) (by rw [hval]; norm_num)
  rw [h, norm_zero] at hval
  norm_num at hval

/-- The S-adeles with a zero coordinate form a null set for additive Tamagawa measure. -/
private theorem sLocalTrace_nonunits_null :
    νₛ (range (Units.val : Iₛ → Aₛ))ᶜ = 0 := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let (w : InfinitePlace F) : (𝓝[≠] (0 : w.Completion)).NeBot := sLocalTrace_infinite_neBot w
  let (v : S) : (𝓝[≠] (0 : v.val.adicCompletion F)).NeBot := sLocalTrace_finite_neBot v.val
  have hw (w : InfinitePlace F) : infiniteLocalAdditiveTamagawaMeasure F w {0} = 0 :=
    measure_singleton 0
  have hv (v : S) : finiteLocalAdditiveTamagawaMeasure F v.val {0} = 0 :=
    measure_singleton 0
  have hsub : (range (Units.val : Iₛ → Aₛ))ᶜ ⊆
      (⋃ w : InfinitePlace F, Prod.fst ⁻¹' (Function.eval w ⁻¹' {0})) ∪
        ⋃ v : S, Prod.snd ⁻¹' (Function.eval v ⁻¹' {0}) := by
    intro a ha
    by_contra h
    simp only [mem_union, mem_iUnion, not_or, not_exists, mem_preimage, Function.eval,
      mem_singleton_iff] at h
    have hu : IsUnit a := Prod.isUnit_iff.mpr
      ⟨Pi.isUnit_iff.mpr fun w ↦ isUnit_iff_ne_zero.mpr (h.1 w),
        Pi.isUnit_iff.mpr fun v ↦ isUnit_iff_ne_zero.mpr (h.2 v)⟩
    exact ha ⟨hu.unit, rfl⟩
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun w ↦ ?_)
    (measure_iUnion_null fun v ↦ ?_))
  · rw [← prod_univ]
    change ((Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).prod
      (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val))) (_ ×ˢ _) = 0
    rw [Measure.prod_prod, Measure.pi_eval_preimage_null _ (hw w), zero_mul]
  · rw [← univ_prod]
    change ((Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).prod
      (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val))) (_ ×ˢ _) = 0
    rw [Measure.prod_prod, Measure.pi_eval_preimage_null
      (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val) (i := v) (hv v), mul_zero]

/-- Paper: (12.4.1.22)–(12.4.1.23), p. 518. The change of variable w = xu by an S-idele
scales additive Tamagawa measure by the S-idelic norm and the frequency band by the same
factor. -/
private theorem sLocalTrace_integral_band_dilate (g : Aₛ → ℂ) (x : Iₛ) (L' : ℝ) :
    ∫ u in band(L'), g (x.val * u) ∂νₛ =
      ((normS(x))⁻¹ : ℂ) * ∫ w in band(L' * normS(x)), g w ∂νₛ := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  have hm : Continuous fun t : Aₛ ↦ modS(t) :=
    (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  have hband (r : ℝ) : MeasurableSet (band(r)) := (isClosed_le hm continuous_const).measurableSet
  have hfull : ∀ᵐ u ∂νₛ, u ∈ range (Units.val : Iₛ → Aₛ) :=
    measure_eq_zero_iff_ae_notMem.mp sLocalTrace_nonunits_null |>.mono fun _ h ↦ not_not.mp h
  let c := sLocalTraceMeasureFactor (F := F) S
  have hc : (c : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ ↦ ?_)
    have hv : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_ne_zero (by linarith) (sub_pos.mpr hv).ne'
  have hx : (normS(x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S x))).ne'
  -- The integral over a band of a function vanishing off the units, through the units.
  have key (r : ℝ) (k : Aₛ → ℂ) :
      (∫ t : Iₛ, (normS(t) : ℂ) * (range (Units.val : Iₛ → Aₛ)).indicator
          ((band(r)).indicator k) t.val ∂μₛ) = (c : ℂ) * ∫ u in band(r), k u ∂νₛ := by
    have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) := IsOpenUnits.isOpenEmbedding_unitsVal
      (M := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F))
    rw [sLocalTrace_integral_units _ (fun t ht ↦ indicator_of_notMem ht _),
      integral_indicator ho.isOpen_range.measurableSet,
      Measure.restrict_eq_self_of_ae_mem hfull, integral_indicator (hband r)]
  have hpt (t : Iₛ) : (normS(x⁻¹ * t) : ℂ) * (range (Units.val : Iₛ → Aₛ)).indicator
        ((band(L')).indicator fun u ↦ g (x.val * u)) (x⁻¹ * t).val =
      ((normS(x))⁻¹ : ℂ) * ((normS(t) : ℂ) * (range (Units.val : Iₛ → Aₛ)).indicator
        ((band(L' * normS(x))).indicator g) t.val) := by
    rw [indicator_of_mem (mem_range_self (x⁻¹ * t)), indicator_of_mem (mem_range_self t)]
    have hn : normS(x⁻¹ * t) = (normS(x))⁻¹ * normS(t) := by simp [map_mul, map_inv]
    have hpos : 0 < normS(x) := NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S x))
    have hmem : (x⁻¹ * t).val ∈ band(L') ↔ t.val ∈ band(L' * normS(x)) := by
      rw [mem_sLocalPWProductRegion_units, mem_sLocalPWProductRegion_units, hn,
        inv_mul_le_iff₀ hpos, mul_comm]
    by_cases h : t.val ∈ band(L' * normS(x))
    · rw [indicator_of_mem (hmem.2 h), indicator_of_mem h, hn]
      simp only [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
      push_cast
      ring
    · rw [indicator_of_notMem (mt hmem.1 h), indicator_of_notMem h]
      simp
  have h1 := key L' (fun u ↦ g (x.val * u))
  rw [← integral_mul_left_eq_self _ x⁻¹] at h1
  simp only [hpt, integral_const_mul] at h1
  rw [key] at h1
  apply mul_left_cancel₀ hc
  rw [← h1]
  ring

/-- Additive Tamagawa measure pulled back to the S-ideles is s-finite. -/
private theorem sLocalTrace_comap_sFinite :
    SFinite ((νₛ).comap (Units.val : Iₛ → Aₛ)) := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F))
  have : IsFiniteMeasureOnCompacts ((νₛ).comap (Units.val : Iₛ → Aₛ)) :=
    .comap' _ Units.continuous_val ho.measurableEmbedding
  infer_instance

/-- Paper: (12.4.1.17) and (12.4.1.23), p. 518. On any set of S-ideles, additive
Tamagawa measure weighted by the measure factor over the norm is multiplicative
Tamagawa measure. -/
private theorem sLocalTrace_setIntegral_comap_density (s : Set Iₛ) (H : Iₛ → ℂ)
    (hH : IntegrableOn H s μₛ) :
    IntegrableOn (fun x ↦ (sLocalTraceMeasureFactor S : ℂ) * ((normS(x))⁻¹ : ℂ) * H x) s
        ((νₛ).comap (Units.val : Iₛ → Aₛ)) ∧
      ∫ x in s, (sLocalTraceMeasureFactor S : ℂ) * ((normS(x))⁻¹ : ℂ) * H x
          ∂((νₛ).comap (Units.val : Iₛ → Aₛ)) = ∫ x in s, H x ∂μₛ := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have hc : 0 ≤ sLocalTraceMeasureFactor (F := F) S := by
    apply Finset.prod_nonneg
    intro v _
    have hv : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hv.le)
  have hnm : Measurable fun x : Iₛ ↦ normS(x) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      sLocalTrace_sIdeleNorm_continuous)).measurable
  let dd (x : Iₛ) := ENNReal.ofReal (sLocalTraceMeasureFactor S / normS(x))
  have hdd : Measurable dd := (measurable_const.div hnm).ennreal_ofReal
  have hreal (x : Iₛ) : (dd x).toReal • H x =
      (sLocalTraceMeasureFactor S : ℂ) * ((normS(x))⁻¹ : ℂ) * H x := by
    have hpos : 0 < normS(x) := NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S x))
    simp only [dd, Complex.real_smul]
    rw [ENNReal.toReal_ofReal (div_nonneg hc hpos.le)]
    push_cast
    ring
  have := sLocalTrace_comap_sFinite (F := F) (S := S)
  rw [sLocalTrace_mult_eq_withDensity] at hH ⊢
  change Integrable H ((((νₛ).comap Units.val).withDensity dd).restrict s) at hH
  rw [restrict_withDensity' s, integrable_withDensity_iff_integrable_smul' hdd
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)] at hH
  refine ⟨hH.congr (ae_of_all _ hreal), ?_⟩
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀' s hdd.aemeasurable
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  exact integral_congr_ae (ae_of_all _ fun x ↦ (hreal x).symm)

section RadialSection

open scoped Pointwise

attribute [-instance] Quotient.instMeasurableSpace

/-- Paper: (12.4.1.23), p. 518. The image in the S-idele quotient of multiplicative
Tamagawa measure restricted to an S-unit fundamental domain is the quotient Tamagawa
measure. -/
private theorem sLocalTrace_fundamentalDomain_map (D : Set Iₛ)
    (hD : IsFundamentalDomain Hₛ D μₛ) :
    ((μₛ).restrict D).map (QuotientGroup.mk : Iₛ → Jₛ) = μJ := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have : BorelSpace Jₛ := ⟨rfl⟩
  have : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  have : DiscreteTopology Hₛ := discreteTopology_sProjectedDiagonal
  have hcl : IsClosed (Hₛ : Set Iₛ) := isClosed_sProjectedDiagonal
  have : Countable Hₛ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let π : Iₛ → Jₛ := QuotientGroup.mk
  have hπ : Measurable π := Continuous.measurable (f := π) continuous_quotient_mk'
  let νD := ((μₛ).restrict D).map π
  -- The fundamental domain for the right action of the S-units.
  have hDop : IsFundamentalDomain (Subgroup.op (Hₛ)) D μₛ := by
    have h := hD.image_of_equiv (Equiv.refl Iₛ) (MeasureTheory.QuasiMeasurePreserving.id μₛ)
      (Subgroup.equivOp (Hₛ)).symm (fun g x ↦ ?_)
    · simpa using h
    · change ((g.1.unop : Iₛ)) * x = x * g.1.unop
      exact mul_comm _ _
  have : IsClosed (Hₛ : Set Iₛ) := hcl
  have : T2Space Iₛ := (sIdeleGroup_description F S).2.1
  have : T2Space Jₛ := inferInstance
  have : SecondCountableTopology Jₛ := inferInstance
  have : LocallyCompactSpace Jₛ := inferInstance
  -- Preimages of sets in the quotient are invariant under the S-units.
  have hinv (A : Set Jₛ) (g : Hₛ) : (fun x ↦ g • x) ⁻¹' (π ⁻¹' A) = π ⁻¹' A := by
    ext z
    change π ((g : Iₛ) * z) ∈ A ↔ π z ∈ A
    rw [show π ((g : Iₛ) * z) = π z from QuotientGroup.eq.mpr (by
      rw [mul_inv_rev, mul_assoc, mul_left_comm, inv_mul_cancel, mul_one]
      exact inv_mem g.2)]
  -- The image of a compact set has at most its mass.
  have hle (W : Set Iₛ) (hW : IsCompact W) : νD (π '' W) ≤ μₛ W := by
    have hm : MeasurableSet (π '' W) :=
      (IsCompact.image (f := π) hW continuous_quotient_mk').isClosed.measurableSet
    rw [Measure.map_apply hπ hm, Measure.restrict_apply (hπ hm),
      QuotientGroup.preimage_image_mk, iUnion_inter]
    refine (measure_iUnion_le _).trans (le_of_eq ?_)
    rw [hD.measure_eq_tsum W, ← (Equiv.inv Hₛ).tsum_eq]
    congr 1
    funext ξ
    congr 2
    ext y
    simp only [mem_preimage, Equiv.inv_apply, Set.mem_smul_set_iff_inv_smul_mem,
      Subgroup.coe_inv, Subgroup.smul_def, smul_eq_mul]
    rw [mul_comm]
  have hlocfin : IsLocallyFiniteMeasure νD := ⟨fun q ↦ by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨W, hWc, hWn⟩ := exists_compact_mem_nhds x
    exact ⟨π '' W, QuotientGroup.isOpenMap_coe.image_mem_nhds hWn,
      (hle W hWc).trans_lt hWc.measure_lt_top⟩⟩
  have hleft : νD.IsMulLeftInvariant := ⟨fun y ↦ by
    obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective y
    ext A hA
    have hA' : MeasurableSet ((fun z ↦ (QuotientGroup.mk x₁ : Jₛ) * z) ⁻¹' A) :=
      measurable_const_mul _ hA
    rw [Measure.map_apply (measurable_const_mul _) hA]
    simp only [νD, Measure.map_apply hπ hA', Measure.map_apply hπ hA,
      Measure.restrict_apply (hπ hA'), Measure.restrict_apply (hπ hA)]
    have hpre : π ⁻¹' ((fun z ↦ (QuotientGroup.mk x₁ : Jₛ) * z) ⁻¹' A) =
        (fun z ↦ x₁ * z) ⁻¹' (π ⁻¹' A) := rfl
    have hD1 : IsFundamentalDomain Hₛ (x₁ • D) μₛ := hD.smul_of_comm x₁
    rw [hpre]
    calc μₛ ((fun z ↦ x₁ * z) ⁻¹' (π ⁻¹' A) ∩ D)
        = μₛ ((fun z ↦ x₁ * z) ⁻¹' (π ⁻¹' A ∩ x₁ • D)) := by
          congr 1
          ext z
          simp only [mem_inter_iff, mem_preimage]
          rw [show x₁ * z = x₁ • z from rfl, smul_mem_smul_set_iff]
      _ = μₛ (π ⁻¹' A ∩ x₁ • D) := measure_preimage_mul μₛ x₁ _
      _ = μₛ (π ⁻¹' A ∩ D) := (hD.measure_set_eq hD1 (hπ hA) (hinv A)).symm⟩
  have hopen : νD.IsOpenPosMeasure := ⟨fun U hU hne h0 ↦ by
    rw [Measure.map_apply hπ hU.measurableSet, Measure.restrict_apply (hπ hU.measurableSet)] at h0
    have h1 := hD.measure_zero_of_invariant _ (fun g ↦ by
      rw [← Set.preimage_smul_inv]; exact hinv U g⁻¹) h0
    exact (hU.preimage continuous_quotient_mk').measure_ne_zero μₛ (hne.preimage
      QuotientGroup.mk_surjective) h1⟩
  have hhaar : νD.IsHaarMeasure := { }
  have hreg : νD.Regular := by
    obtain ⟨W, hWc, hWn⟩ := exists_compact_mem_nhds (1 : Iₛ)
    exact Measure.regular_of_isMulLeftInvariant (IsCompact.image (f := π) hWc continuous_quotient_mk')
      ⟨π 1, mem_interior_iff_mem_nhds.mpr (QuotientGroup.isOpenMap_coe.image_mem_nhds hWn)⟩
      ((hle W hWc).trans_lt hWc.measure_lt_top).ne
  have hweil : ∀ f : C(Iₛ, ℂ), HasCompactSupport f →
      (∫ x, f x ∂μₛ) = ∫ q, lcaCosetIntegral Hₛ Measure.count f q ∂νD := by
    intro f hf
    have : (Measure.count : Measure Hₛ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
    have : (μₛ).IsMulRightInvariant := ⟨fun g ↦ by
      rw [show (fun x : Iₛ ↦ x * g) = fun x ↦ g * x from funext fun x ↦ mul_comm x g]
      exact map_mul_left_eq_self μₛ g⟩
    have : Countable (Subgroup.op (Hₛ)) := Countable.of_equiv _ (Subgroup.equivOp (Hₛ))
    -- Near any point only finitely many S-units move it into the support of f.
    have hfin (W : Set Iₛ) (hW : IsCompact W) :
        {γ : Hₛ | (γ : Iₛ) ∈ W⁻¹ * tsupport f}.Finite :=
      (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (hW.inv.mul hf)).finite_of_discrete
    have hzero (W : Set Iₛ) (y : Iₛ) (hy : y ∈ W) (γ : Hₛ)
        (hγ : γ ∉ {γ : Hₛ | (γ : Iₛ) ∈ W⁻¹ * tsupport f}) : f (y * γ) = 0 := by
      by_contra h
      refine hγ ⟨y⁻¹, inv_mem_inv.mpr hy, y * γ, subset_tsupport f h, ?_⟩
      simp
    have hsum (x : Iₛ) : (∑' γ : Hₛ, f (x * γ)) = ∑ γ ∈ (hfin {x} isCompact_singleton).toFinset,
        f (x * γ) :=
      tsum_eq_sum fun γ hγ ↦ hzero {x} x rfl γ (by simpa using hγ)
    have hcont : Continuous fun x : Iₛ ↦ ∑' γ : Hₛ, f (x * γ) := by
      refine continuous_iff_continuousAt.mpr fun x ↦ ?_
      obtain ⟨W, hWc, hWn⟩ := exists_compact_mem_nhds x
      have heq : (fun y : Iₛ ↦ ∑ γ ∈ (hfin W hWc).toFinset, f (y * γ)) =ᶠ[𝓝 x]
          fun y ↦ ∑' γ : Hₛ, f (y * γ) :=
        Filter.mem_of_superset hWn fun y hy ↦
          (tsum_eq_sum fun γ hγ ↦ hzero W y hy γ (by simpa using hγ)).symm
      exact ((continuous_finsetSum _ fun γ _ ↦
        f.continuous.comp (continuous_id.mul continuous_const)).continuousAt).congr heq
    have hint (x : Iₛ) : Integrable (fun γ : Hₛ ↦ f (x * γ)) Measure.count :=
      integrable_count_iff.mpr (summable_of_ne_finset_zero (s := (hfin {x} isCompact_singleton).toFinset)
        fun γ hγ ↦ by rw [hzero {x} x rfl γ (by simpa using hγ), norm_zero])
    have hcoset (x : Iₛ) : lcaCosetIntegral Hₛ Measure.count f (π x) = ∑' γ : Hₛ, f (x * γ) := by
      rw [lcaCosetIntegral_mk Hₛ Measure.count (f : Iₛ → ℂ) x (hint x), integral_countable (hint x)]
      simp [Measure.real]
    have haut : QuotientGroup.automorphize (Γ := Hₛ) (f : Iₛ → ℂ) =
        lcaCosetIntegral Hₛ Measure.count f := by
      funext q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hcoset x]
      change ∑' γ : Subgroup.op (Hₛ), f (γ • x) = _
      rw [← (Subgroup.equivOp (Hₛ)).tsum_eq]
      rfl
    have hautc : Continuous (QuotientGroup.automorphize (Γ := Hₛ) (f : Iₛ → ℂ)) := by
      rw [haut]
      refine (isQuotientMap_quotient_mk' (s := QuotientGroup.leftRel (Hₛ))).continuous_iff.mpr ?_
      change Continuous fun x ↦ lcaCosetIntegral Hₛ Measure.count f (π x)
      simp_rw [hcoset]
      exact hcont
    rw [QuotientGroup.integral_eq_integral_automorphize hDop
      (f.continuous.integrable_of_hasCompactSupport hf) hautc.aestronglyMeasurable, haut]
  exact (sLocalQuotientTamagawaMeasure_existsUnique (F := F) (S := S)).unique
    ⟨hhaar, hreg, hweil⟩ sLocalQuotientTamagawaMeasure_isWeil

/-- A continuous section of the S-idelic norm, through one infinite place. -/
private theorem sLocalTrace_exists_normSection :
    ∃ τ : ℝ≥0ˣ →ₜ* Iₛ, RightInverse τ (sIdeleNorm F S) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let s := singlePlaceIdeleNormSection F w
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  refine ⟨⟨p.comp s, hp.comp (singlePlaceIdeleNormSection_continuous F w)⟩, fun t ↦ ?_⟩
  let A := integralAdelesOutside F S
  have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
    simp only [A, integralAdelesOutside, Subring.mem_iInf]
    intro v _
    exact (v.adicCompletionIntegers F).one_mem
  have ht : s t ∈ A.toSubmonoid.units :=
    ⟨hmem t, by
      change ((s t)⁻¹).val ∈ A
      rw [← map_inv]
      exact hmem t⁻¹⟩
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
  exact ((sIdeleNorm_spec F S).1 g).symm.trans (singlePlaceIdeleNormSection_rightInverse F w t)

/-- Paper: (12.4.1.23)–(12.4.1.24), p. 518. On the part of an S-unit fundamental
domain of norm at most L, a measurable function of the norm integrates to the norm-one
volume times its integral against dt/t on (0, L]. -/
private theorem sLocalTrace_fundamentalDomain_radial (D : Set Iₛ)
    (hD : IsFundamentalDomain Hₛ D μₛ) (L : ℝ) (h : ℝ → ℂ) (hm : Measurable h)
    (hh : IntegrableOn (fun t ↦ h t / (t : ℂ)) (Ioc 0 L)) :
    IntegrableOn (fun x : Iₛ ↦ h (normS(x))) (D ∩ {x : Iₛ | normS(x) ≤ L}) μₛ ∧
      ∫ x in D ∩ {x : Iₛ | normS(x) ≤ L}, h (normS(x)) ∂μₛ =
        (volume₁ : ℂ) * ∫ t in Ioc 0 L, h t / (t : ℂ) := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have : BorelSpace Jₛ := ⟨rfl⟩
  have : BorelSpace (sIdeleQuotientNorm F S).ker := ⟨rfl⟩
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  have : CompactSpace (sIdeleQuotientNorm F S).ker := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  have : (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have : IsFiniteMeasure (sLocalNormOneQuotientMeasure F S) := CompactSpace.isFiniteMeasure
  obtain ⟨τ, hτ⟩ := sLocalTrace_exists_normSection (F := F) (S := S)
  have hprod := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
  let nb : Jₛ → ℝ := fun y ↦ ((sIdeleQuotientNorm F S y : ℝ≥0) : ℝ)
  have hnb : Continuous nb := NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_sIdeleQuotientNorm F S).continuous)
  let ht : ℝ → ℂ := (Iic L).indicator h
  have htm : Measurable ht := hm.indicator measurableSet_Iic
  let P : (sIdeleQuotientNorm F S).ker × ℝ≥0ˣ → Jₛ :=
    fun x ↦ (x.1 : Jₛ) * (QuotientGroup.mk (τ x.2) : Jₛ)
  have hP : Continuous P := (continuous_subtype_val.comp continuous_fst).mul
    (continuous_quotient_mk'.comp (τ.continuous.comp continuous_snd))
  have hnP (x : (sIdeleQuotientNorm F S).ker × ℝ≥0ˣ) : nb (P x) = ((x.2 : ℝ≥0) : ℝ) := by
    change ((sIdeleQuotientNorm F S ((x.1 : Jₛ) * QuotientGroup.mk (τ x.2)) : ℝ≥0) : ℝ) = _
    rw [map_mul, MonoidHom.mem_ker.mp x.1.property, one_mul]
    change ((sIdeleNorm F S (τ x.2) : ℝ≥0) : ℝ) = _
    rw [hτ x.2]
  let e : ℝ → ℝ≥0ˣ := fun x ↦ Units.mk0 (Real.exp x).toNNReal
    (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hev (x : ℝ) : (((e x : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.exp x :=
    Real.coe_toNNReal _ (Real.exp_pos x).le
  have hpush : ((μₛ).restrict D).map (QuotientGroup.mk : Iₛ → Jₛ) = μJ :=
    sLocalTrace_fundamentalDomain_map D hD
  have hπ : Measurable (QuotientGroup.mk : Iₛ → Jₛ) :=
    Continuous.measurable (f := (QuotientGroup.mk : Iₛ → Jₛ)) continuous_quotient_mk'
  have hsnd : Measurable fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ) :=
    (NNReal.continuous_coe.comp Units.continuous_val).measurable
  -- The integrand on the slab is the cut-off function of the norm.
  have hslab : MeasurableSet {x : Iₛ | normS(x) ≤ L} :=
    measurableSet_le (hnb.comp continuous_quotient_mk').measurable measurable_const
  have hind (x : Iₛ) : {x : Iₛ | normS(x) ≤ L}.indicator (fun x ↦ h (normS(x))) x =
      ht (nb (QuotientGroup.mk x)) := by
    by_cases hx : normS(x) ≤ L
    · rw [indicator_of_mem (show x ∈ {x : Iₛ | normS(x) ≤ L} from hx)]
      exact (indicator_of_mem (show normS(x) ∈ Iic L from hx) h).symm
    · rw [indicator_of_notMem (show x ∉ {x : Iₛ | normS(x) ≤ L} from hx)]
      exact (indicator_of_notMem (show normS(x) ∉ Iic L from hx) h).symm
  -- The radial integrand on the positive reals.
  have hdiv (y : ℝ) : ht y / (y : ℂ) = (Iic L).indicator (fun t ↦ h t / (t : ℂ)) y := by
    by_cases hy : y ∈ Iic L
    · simp only [ht, indicator_of_mem hy]
    · simp only [ht, indicator_of_notMem hy, zero_div]
  have hexp (x : ℝ) : (Real.exp x) • (ht (Real.exp x) / (Real.exp x : ℂ)) = ht (Real.exp x) := by
    rw [Complex.real_smul, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne')]
  have hIoi : IntegrableOn (fun y ↦ ht y / (y : ℂ)) (Ioi 0) := by
    simp_rw [hdiv]
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi]
    exact hh
  have hR : Integrable (fun x : ℝ ↦ ht (Real.exp x)) := by
    have := (integrable_comp_exp (fun y ↦ ht y / (y : ℂ))).mpr hIoi
    simpa only [hexp] using this
  have hpos : Integrable (fun t : ℝ≥0ˣ ↦ ht ((t : ℝ≥0) : ℝ)) positiveRealHaar := by
    change Integrable (fun t : ℝ≥0ˣ ↦ ht ((t : ℝ≥0) : ℝ)) (Measure.map e volume)
    rw [integrable_map_measure (g := fun t : ℝ≥0ˣ ↦ ht ((t : ℝ≥0) : ℝ))
      (htm.comp hsnd).aestronglyMeasurable he.aemeasurable]
    exact hR.congr (ae_of_all _ fun x ↦ by simp only [Function.comp, hev])
  have hprodI : Integrable (fun x : (sIdeleQuotientNorm F S).ker × ℝ≥0ˣ ↦ ht (nb (P x)))
      ((sLocalNormOneQuotientMeasure F S).prod positiveRealHaar) := by
    simp_rw [hnP]
    exact hpos.comp_snd _
  have hJ : Integrable (fun y : Jₛ ↦ ht (nb y)) μJ := by
    rw [← hprod]
    exact (integrable_map_measure (g := fun y : Jₛ ↦ ht (nb y))
      (htm.comp hnb.measurable).aestronglyMeasurable hP.measurable.aemeasurable).mpr hprodI
  have hD' : Integrable (fun x : Iₛ ↦ ht (nb (QuotientGroup.mk x))) ((μₛ).restrict D) := by
    rw [← hpush] at hJ
    exact (integrable_map_measure (g := fun y : Jₛ ↦ ht (nb y))
      (htm.comp hnb.measurable).aestronglyMeasurable hπ.aemeasurable).mp hJ
  have hint : IntegrableOn (fun x : Iₛ ↦ h (normS(x))) (D ∩ {x : Iₛ | normS(x) ≤ L}) μₛ := by
    have h2 : Integrable ({x : Iₛ | normS(x) ≤ L}.indicator (fun x ↦ h (normS(x))))
        ((μₛ).restrict D) := hD'.congr (ae_of_all _ fun x ↦ (hind x).symm)
    rw [integrable_indicator_iff hslab, IntegrableOn, Measure.restrict_restrict hslab,
      inter_comm] at h2
    exact h2
  refine ⟨hint, ?_⟩
  rw [← setIntegral_indicator hslab]
  simp_rw [hind]
  rw [← integral_map (f := fun y : Jₛ ↦ ht (nb y)) hπ.aemeasurable
      (htm.comp hnb.measurable).aestronglyMeasurable, hpush, ← hprod,
    integral_map (f := fun y : Jₛ ↦ ht (nb y)) hP.measurable.aemeasurable
      (htm.comp hnb.measurable).aestronglyMeasurable]
  simp_rw [hnP]
  rw [integral_fun_snd (f := fun t : ℝ≥0ˣ ↦ ht ((t : ℝ≥0) : ℝ))]
  change _ * ∫ t : ℝ≥0ˣ, ht ((t : ℝ≥0) : ℝ) ∂(Measure.map e volume) = _
  rw [integral_map (f := fun t : ℝ≥0ˣ ↦ ht ((t : ℝ≥0) : ℝ)) he.aemeasurable
    (htm.comp hsnd).aestronglyMeasurable]
  simp only [hev]
  have hcv := integral_comp_exp (fun y ↦ ht y / (y : ℂ))
  simp only [hexp] at hcv
  rw [hcv]
  simp_rw [hdiv]
  rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]
  rfl

end RadialSection

/-- Paper: (12.4.1.24), p. 518. The integral of dt/t over the part of (0, L] above a
positive level a is the logarithmic width of the interval. -/
private theorem sLocalTrace_integral_inv_Ici (a L : ℝ) (ha : 0 < a) :
    ∫ t in Ioc 0 L, (Ici a).indicator (fun t : ℝ ↦ t⁻¹) t =
      if a ≤ L then Real.log L - Real.log a else 0 := by
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici a ∩ Ioc 0 L = Icc a L := by
    ext t
    simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, ha.trans_le h1, h3⟩
  rw [hset]
  split_ifs with h
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
      integral_inv_of_pos ha (ha.trans_le h), Real.log_div (ha.trans_le h).ne' ha.ne']
  · rw [Icc_eq_empty h, Measure.restrict_empty, integral_zero_measure]

section FourierLogSection

local instance instInfiniteCompletionMeasurableSpaceSec4 (w : InfinitePlace F) :
    MeasurableSpace w.Completion := borel _

/-- On a real normed space of dimension one or two, the weight `(1 + ‖t‖)⁻⁴` is integrable
for additive Haar measure, also after multiplication by `|log ‖t‖|`. -/
private theorem sLocalTrace_weight_integrable_model {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (h1 : 1 ≤ Module.finrank ℝ E)
    (h2 : Module.finrank ℝ E ≤ 2) :
    Integrable (fun t : E ↦ ((1 + ‖t‖) ^ 4)⁻¹) μ ∧
      Integrable (fun t : E ↦ |Real.log ‖t‖| * ((1 + ‖t‖) ^ 4)⁻¹) μ := by
  have hpow (t : E) : (1 + ‖t‖) ^ (Module.finrank ℝ E + 2) ≤ (1 + ‖t‖) ^ 4 :=
    pow_le_pow_right₀ (by linarith [norm_nonneg t]) (by omega)
  refine ⟨?_, ?_⟩
  · have h2' : (Module.finrank ℝ E : ℝ) ≤ 2 := by exact_mod_cast h2
    refine (integrable_one_add_norm (μ := μ) (r := 4) (by linarith)).congr
      (ae_of_all _ fun t ↦ ?_)
    change (1 + ‖t‖) ^ (-(4 : ℝ)) = ((1 + ‖t‖) ^ 4)⁻¹
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  · refine (integrable_abs_log_norm_div_one_add_norm_pow μ h1).mono'
      (((continuous_abs.measurable.comp measurable_norm.log).mul
        (by fun_prop)).aestronglyMeasurable) (ae_of_all _ fun t ↦ ?_)
    have hp : 0 < (1 + ‖t‖) ^ (Module.finrank ℝ E + 2) := by positivity
    rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hp (hpow t)

/-- At an infinite place the weight `(1 + ‖t‖)⁻⁴` is integrable for additive Tamagawa
measure, also after multiplication by `|log ‖t‖|`. -/
private theorem sLocalTrace_infinite_weight_integrable (w : InfinitePlace F) :
    Integrable (fun t : w.Completion ↦ ((1 + ‖t‖) ^ 4)⁻¹)
        (infiniteLocalAdditiveTamagawaMeasure F w) ∧
      Integrable (fun t : w.Completion ↦ |Real.log ‖t‖| * ((1 + ‖t‖) ^ 4)⁻¹)
        (infiniteLocalAdditiveTamagawaMeasure F w) := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  by_cases hw : w.IsReal
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let m := j.symm.toHomeomorph.toMeasurableEquiv
    have hμ : infiniteLocalAdditiveTamagawaMeasure F w = (volume : Measure ℝ).map m :=
      dite_eq_left hw
    have hnorm (t : ℝ) : ‖m t‖ = ‖t‖ := by
      change ‖j.symm t‖ = ‖t‖
      rw [← dist_zero_right, ← dist_zero_right t, ← j.symm.dist_eq t 0,
        show j.symm 0 = 0 from map_zero e.symm]
    obtain ⟨h1, h2⟩ := sLocalTrace_weight_integrable_model (volume : Measure ℝ) (by simp) (by simp)
    rw [hμ, integrable_map_equiv m, integrable_map_equiv m]
    exact ⟨h1.congr (ae_of_all _ fun t ↦ by simp only [Function.comp_apply, hnorm]),
      h2.congr (ae_of_all _ fun t ↦ by simp only [Function.comp_apply, hnorm])⟩
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
    let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    let m := j.symm.toHomeomorph.toMeasurableEquiv
    have hμ : infiniteLocalAdditiveTamagawaMeasure F w = (2 • (volume : Measure ℂ)).map m :=
      dite_eq_right hw
    have hnorm (t : ℂ) : ‖m t‖ = ‖t‖ := by
      change ‖j.symm t‖ = ‖t‖
      rw [← dist_zero_right, ← dist_zero_right t, ← j.symm.dist_eq t 0,
        show j.symm 0 = 0 from map_zero e.symm]
    obtain ⟨h1, h2⟩ := sLocalTrace_weight_integrable_model (volume : Measure ℂ) (by simp) (by simp)
    rw [hμ, integrable_map_equiv m, integrable_map_equiv m, two_smul]
    exact ⟨(h1.add_measure h1).congr (ae_of_all _ fun t ↦ by simp only [Function.comp_apply, hnorm]),
      (h2.add_measure h2).congr (ae_of_all _ fun t ↦ by simp only [Function.comp_apply, hnorm])⟩

/-- Additive Tamagawa measure at an infinite place is σ-finite. -/
private theorem sLocalTrace_infinite_sigmaFinite (w : InfinitePlace F) :
    SigmaFinite (infiniteLocalAdditiveTamagawaMeasure F w) := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  by_cases hw : w.IsReal
  · let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let m := j.symm.toHomeomorph.toMeasurableEquiv
    have hμ : infiniteLocalAdditiveTamagawaMeasure F w = (volume : Measure ℝ).map m :=
      dite_eq_left hw
    rw [hμ]
    exact m.sigmaFinite_map
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    let m := j.symm.toHomeomorph.toMeasurableEquiv
    have hμ : infiniteLocalAdditiveTamagawaMeasure F w = (2 • (volume : Measure ℂ)).map m :=
      dite_eq_right hw
    rw [hμ, two_smul]
    exact m.sigmaFinite_map

/-- The product over the infinite places of the weights `(1 + ‖a_w‖)⁻⁴` is integrable,
also after multiplication by `|log ‖a_u‖|` for one infinite place `u`. -/
private theorem sLocalTrace_infinite_weight_prod_integrable :
    Integrable (fun a : (w : InfinitePlace F) → w.Completion ↦ ∏ w, ((1 + ‖a w‖) ^ 4)⁻¹)
        (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)) ∧
      ∀ u : InfinitePlace F, Integrable
        (fun a : (w : InfinitePlace F) → w.Completion ↦
          (∏ w, ((1 + ‖a w‖) ^ 4)⁻¹) * |Real.log ‖a u‖|)
        (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)) := by
  classical
  let (w : InfinitePlace F) : SigmaFinite (infiniteLocalAdditiveTamagawaMeasure F w) :=
    sLocalTrace_infinite_sigmaFinite w
  refine ⟨Integrable.fintype_prod_dep fun w ↦ (sLocalTrace_infinite_weight_integrable w).1,
    fun u ↦ ?_⟩
  let g (w : InfinitePlace F) : w.Completion → ℝ :=
    fun t ↦ (if w = u then |Real.log ‖t‖| else 1) * ((1 + ‖t‖) ^ 4)⁻¹
  have hg (w : InfinitePlace F) : Integrable (g w) (infiniteLocalAdditiveTamagawaMeasure F w) := by
    by_cases h : w = u
    · simp only [g, h, ↓reduceIte]
      subst h
      exact (sLocalTrace_infinite_weight_integrable w).2
    · simp only [g, h, ↓reduceIte, one_mul]
      exact (sLocalTrace_infinite_weight_integrable w).1
  refine (Integrable.fintype_prod_dep hg).congr (ae_of_all _ fun a ↦ ?_)
  simp only [g, Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq' Finset.univ u]
  simp [mul_comm]

/-- Each coordinate of an infinite adele is bounded by the norm of its image in the
mixed space. -/
private theorem sLocalTrace_norm_le_mixed (a : InfiniteAdeleRing F) (w : InfinitePlace F) :
    ‖a w‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F a‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  by_cases hw : w.IsReal
  · refine le_trans (le_of_eq ?_) ((norm_le_pi_norm _ ⟨w, hw⟩).trans (norm_fst_le _))
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) (a w)).symm
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    refine le_trans (le_of_eq ?_) ((norm_le_pi_norm _ ⟨w, hc⟩).trans (norm_snd_le _))
    exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (a w)).symm

/-- `(1 + t) ^ k ≤ 2 ^ k (1 + t ^ k)` for `t ≥ 0`. -/
private theorem sLocalTrace_one_add_pow_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (1 + t) ^ k ≤ 2 ^ k * (1 + t ^ k) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ 2 ^ k * (1 + t ^ k) :=
          le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ht k])
  · calc (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * t ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + t ^ k) := by gcongr; linarith

/-- Paper: (12.4.1.20)–(12.4.1.21), p. 518. The Fourier transform of the translated test
is bounded by a multiple of the product of the weights `(1 + ‖y_w‖)⁻⁴` at the infinite
places times the indicator of a ball at every finite place of `S`.
Deviation: The Fourier transform of the translated test is again an S-adelic
Schwartz–Bruhat function (`sAdeleSchwartzFourier`), so the bound is its compact support
in the finite coordinates and its rapid decay in the infinite ones. -/
private theorem sLocalTrace_fourier_decay_bound (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    ∃ C R : ℝ, ∀ y : Aₛ, ‖fourierₛ (sLocalTraceEta f ξ) y‖ ≤
      C * (∏ w, ((1 + ‖y.1 w‖) ^ 4)⁻¹) *
        ∏ v : S, {b : v.val.adicCompletion F | ‖b‖ ≤ R}.indicator (fun _ ↦ (1 : ℝ)) (y.2 v) := by
  obtain ⟨η, hη⟩ := SLocalTraceEta.eta_test f ξ
  let g : testₛ := sAdeleSchwartzFourier η
  have hg (y : Aₛ) : fourierₛ (sLocalTraceEta f ξ) y = g (Multiplicative.ofAdd y) := by
    change _ = tamagawaFourier νₛ ψₛ (fun x ↦ η (Multiplicative.ofAdd x)) y
    rw [show (fun x ↦ η (Multiplicative.ofAdd x)) = sLocalTraceEta f ξ from funext hη]
  obtain ⟨K, hK, hKz, hdec⟩ := sAdeleSchwartz_exists_decay_bound F S g
  let k := 4 * Fintype.card (InfinitePlace F)
  obtain ⟨B0, hB0, h0⟩ := hdec 0
  obtain ⟨B1, hB1, h1⟩ := hdec k
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨2 ^ k * (B0 + B1), R, fun y ↦ ?_⟩
  rw [hg]
  have hW0 : 0 ≤ ∏ w, ((1 + ‖y.1 w‖) ^ 4)⁻¹ := Finset.prod_nonneg fun w _ ↦ by positivity
  by_cases hy : y.2 ∈ K
  · have hP : ∏ v : S, {b : v.val.adicCompletion F | ‖b‖ ≤ R}.indicator
        (fun _ ↦ (1 : ℝ)) (y.2 v) = 1 := by
      refine Finset.prod_eq_one fun v _ ↦ indicator_of_mem ?_ _
      exact (norm_le_pi_norm y.2 v).trans (mem_closedBall_zero_iff.mp (hR hy))
    rw [hP, mul_one, Finset.prod_inv_distrib, ← div_eq_mul_inv,
      le_div_iff₀ (Finset.prod_pos fun w _ ↦ by positivity)]
    set t := ‖InfiniteAdeleRing.ringEquiv_mixedSpace F y.1‖
    have ht : 0 ≤ t := norm_nonneg _
    have hW : ∏ w, (1 + ‖y.1 w‖) ^ 4 ≤ (1 + t) ^ k := by
      calc ∏ w, (1 + ‖y.1 w‖) ^ 4 ≤ ∏ _w : InfinitePlace F, (1 + t) ^ 4 := by
            gcongr with w
            exact sLocalTrace_norm_le_mixed y.1 w
        _ = (1 + t) ^ k := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
    have hb0 := h0 y
    have hb1 := h1 y
    rw [pow_zero, mul_one] at hb0
    have hn := norm_nonneg (g (Multiplicative.ofAdd y))
    calc ‖g (Multiplicative.ofAdd y)‖ * ∏ w, (1 + ‖y.1 w‖) ^ 4
        ≤ ‖g (Multiplicative.ofAdd y)‖ * (2 ^ k * (1 + t ^ k)) :=
          mul_le_mul_of_nonneg_left (hW.trans (sLocalTrace_one_add_pow_le ht k)) hn
      _ = 2 ^ k * (‖g (Multiplicative.ofAdd y)‖ + ‖g (Multiplicative.ofAdd y)‖ * t ^ k) := by
          ring
      _ ≤ 2 ^ k * (B0 + B1) := by gcongr
  · rw [hKz y hy, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (add_nonneg hB0 hB1)) hW0)
      (Finset.prod_nonneg fun v _ ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) _)

/-- Paper: (12.4.1.20)–(12.4.1.21), p. 518. The Fourier transform of the translated test
is dominated by a function of the infinite coordinates, integrable also against the
logarithm of each infinite absolute value, times the indicator of a ball at every finite
place of `S`. -/
private theorem sLocalTrace_fourier_product_bound (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    ∃ (Φ : ((w : InfinitePlace F) → w.Completion) → ℝ) (R : ℝ), (∀ a, 0 ≤ Φ a) ∧
      Integrable Φ (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)) ∧
      (∀ w : InfinitePlace F, Integrable (fun a ↦ Φ a * |Real.log ‖a w‖|)
        (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F))) ∧
      ∀ y : Aₛ, ‖fourierₛ (sLocalTraceEta f ξ) y‖ ≤
        Φ y.1 * ∏ v : S, {b : v.val.adicCompletion F | ‖b‖ ≤ R}.indicator (fun _ ↦ (1 : ℝ)) (y.2 v) := by
  obtain ⟨C, R, hb⟩ := sLocalTrace_fourier_decay_bound f ξ
  obtain ⟨hW, hWl⟩ := sLocalTrace_infinite_weight_prod_integrable (F := F)
  refine ⟨fun a ↦ |C| * ∏ w, ((1 + ‖a w‖) ^ 4)⁻¹, R,
    fun a ↦ mul_nonneg (abs_nonneg C) (Finset.prod_nonneg fun w _ ↦ by positivity),
    hW.const_mul |C|, fun w ↦ (((hWl w).const_mul |C|).congr
      (ae_of_all _ fun a ↦ by simp only [mul_assoc])), fun y ↦ (hb y).trans ?_⟩
  have hP : 0 ≤ ∏ v : S, {b : v.val.adicCompletion F | ‖b‖ ≤ R}.indicator
      (fun _ ↦ (1 : ℝ)) (y.2 v) :=
    Finset.prod_nonneg fun v _ ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hW0 : 0 ≤ ∏ w, ((1 + ‖y.1 w‖) ^ 4)⁻¹ := Finset.prod_nonneg fun w _ ↦ by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hW0) hP

/-- Paper: (12.4.1.24), p. 518. The Fourier transform of the translated test, weighted
by the logarithm of the product norm, is integrable for additive Tamagawa measure.
Deviation: The logarithm of zero is zero on the null locus with a zero coordinate. -/
private theorem sLocalTrace_fourier_log_integrable (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    Integrable (fun w ↦ fourierₛ (sLocalTraceEta f ξ) w * ((Real.log (modS(w)) : ℝ) : ℂ))
      νₛ := by
  classical
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  obtain ⟨Φ, R, hΦ0, hΦi, hΦl, hbd⟩ := sLocalTrace_fourier_product_bound f ξ
  let g := fourierₛ (sLocalTraceEta f ξ)
  obtain ⟨η, hη⟩ := SLocalTraceEta.eta_test f ξ
  have hgc : Continuous g := by
    change Continuous (fourierₛ (sLocalTraceEta f ξ))
    rw [← funext hη]
    exact (schwartzBruhat_continuous (sAdeleSchwartzFourier η)).comp continuous_ofAdd
  have hm : Continuous fun t : Aₛ ↦ modS(t) :=
    (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  let ind (v : S) : v.val.adicCompletion F → ℝ :=
    {b : v.val.adicCompletion F | ‖b‖ ≤ R}.indicator (fun _ ↦ (1 : ℝ))
  have hballm (v : S) : MeasurableSet {b : v.val.adicCompletion F | ‖b‖ ≤ R} :=
    measurableSet_le continuous_norm.measurable measurable_const
  have hball (v : S) : finiteLocalAdditiveTamagawaMeasure F v.val
      {b : v.val.adicCompletion F | ‖b‖ ≤ R} < ⊤ := by
    have : {b : v.val.adicCompletion F | ‖b‖ ≤ R} = Metric.closedBall 0 R := by
      ext b; simp
    rw [this]
    exact (isCompact_closedBall 0 R).measure_lt_top
  have hind (v : S) : Integrable (ind v) (finiteLocalAdditiveTamagawaMeasure F v.val) :=
    (integrable_indicator_iff (hballm v)).mpr (integrableOn_const (hball v).ne)
  -- The weights at the finite places.
  let fin (u : S) (v : S) : v.val.adicCompletion F → ℝ :=
    fun b ↦ ind v b * (if v = u then |Real.log ‖b‖| else 1)
  have hfin (u v : S) : Integrable (fin u v) (finiteLocalAdditiveTamagawaMeasure F v.val) := by
    by_cases h : v = u
    · simp only [fin, h, ↓reduceIte]
      subst h
      have := (finiteLog_abs_integrableOn_closedBall v.val R).integrable_indicator (hballm v)
      refine this.congr (ae_of_all _ fun b ↦ ?_)
      by_cases hb : b ∈ {b : v.val.adicCompletion F | ‖b‖ ≤ R}
      · simp [ind, indicator_of_mem hb]
      · simp [ind, indicator_of_notMem hb]
    · simp only [fin, h, ↓reduceIte, mul_one]
      exact hind v
  let P : ((v : S) → v.val.adicCompletion F) → ℝ := fun b ↦ ∏ v, ind v (b v)
  have hP : Integrable P (Measure.pi fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val) :=
    Integrable.fintype_prod_dep hind
  have hQ (u : S) : Integrable (fun b : (v : S) → v.val.adicCompletion F ↦ ∏ v, fin u v (b v))
      (Measure.pi fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val) :=
    Integrable.fintype_prod_dep (hfin u)
  have hQeq (u : S) (b : (v : S) → v.val.adicCompletion F) :
      ∏ v, fin u v (b v) = P b * |Real.log ‖b u‖| := by
    simp only [fin, Finset.prod_mul_distrib, P]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ u]
    simp
  -- The dominating function.
  let D : Aₛ → ℝ := fun y ↦
    (∑ w : InfinitePlace F, (w.mult : ℝ) * (Φ y.1 * |Real.log ‖y.1 w‖| * P y.2)) +
      ∑ u : S, Φ y.1 * ∏ v, fin u v (y.2 v)
  have hD : Integrable D νₛ := by
    change Integrable D ((Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).prod
      (Measure.pi fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val))
    refine Integrable.add (integrable_finsetSum _ fun w _ ↦ ((hΦl w).mul_prod hP).const_mul _)
      (integrable_finsetSum _ fun u _ ↦ hΦi.mul_prod (hQ u))
  -- The logarithm of the product norm is bounded by the sum of the local logarithms.
  have hlog (y : Aₛ) : |Real.log (modS(y))| ≤
      (∑ w : InfinitePlace F, (w.mult : ℝ) * |Real.log ‖y.1 w‖|) +
        ∑ v : S, |Real.log ‖y.2 v‖| := by
    by_cases h0 : modS(y) = 0
    · rw [h0, Real.log_zero, abs_zero]
      exact add_nonneg (Finset.sum_nonneg fun w _ ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
        (Finset.sum_nonneg fun v _ ↦ abs_nonneg _)
    have hA : (∏ w : InfinitePlace F, ‖y.1 w‖ ^ w.mult) ≠ 0 := left_ne_zero_of_mul h0
    have hB : (∏ v : S, ‖y.2 v‖) ≠ 0 := right_ne_zero_of_mul h0
    rw [Real.log_mul hA hB, Real.log_prod (fun w _ ↦ Finset.prod_ne_zero_iff.mp hA w
      (Finset.mem_univ w)), Real.log_prod (fun v _ ↦ Finset.prod_ne_zero_iff.mp hB v
      (Finset.mem_univ v))]
    refine (abs_add_le _ _).trans (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun w _ ↦ ?_)) (Finset.abs_sum_le_sum_abs _ _))
    rw [Real.log_pow, abs_mul, Nat.abs_cast]
  refine hD.mono' (hgc.measurable.mul (Complex.measurable_ofReal.comp
    (Real.measurable_log.comp hm.measurable))).aestronglyMeasurable (ae_of_all _ fun y ↦ ?_)
  have hP0 : 0 ≤ P y.2 := Finset.prod_nonneg fun v _ ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hDy : D y = Φ y.1 * P y.2 * ((∑ w : InfinitePlace F, (w.mult : ℝ) * |Real.log ‖y.1 w‖|) +
      ∑ v : S, |Real.log ‖y.2 v‖|) := by
    simp only [D, hQeq, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun w _ ↦ by ring
    · exact Finset.sum_congr rfl fun v _ ↦ by ring
  rw [hDy, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (hbd y) (hlog y) (abs_nonneg _) (mul_nonneg (hΦ0 _) hP0)

end FourierLogSection

/-- Paper: (12.4.1.23)–(12.4.1.24), p. 518. Integrating the band integrals of the
Fourier transform against dt/t on (0, L] gives the logarithmic width of the spatial
norm interval, by Fubini; the nonunit locus is null.
Deviation: The integrability of the logarithmic weight against the transform over
the band is part of the statement. -/
private theorem sLocalTrace_band_log_fubini (f : BruhatCompactSupport Iₛ) (ξ : Hₛ)
    (L L' : ℝ) (hL : 0 < L) (hL' : 0 < L') :
    IntegrableOn (fun t ↦ (∫ w in band(L' * t), fourierₛ (sLocalTraceEta f ξ) w ∂νₛ) /
        (t : ℂ)) (Ioc 0 L) ∧
      (volume₁ : ℂ) * ∫ t in Ioc 0 L,
          (∫ w in band(L' * t), fourierₛ (sLocalTraceEta f ξ) w ∂νₛ) / (t : ℂ) =
        sLocalTraceSharpMass f ξ (L * L') := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace Aₛ := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let g := fourierₛ (sLocalTraceEta f ξ)
  have hgi : Integrable g νₛ := sLocalTraceEta_fourier_integrable f ξ
  obtain ⟨η, hη⟩ := SLocalTraceEta.eta_test f ξ
  have hgc : Continuous g := by
    change Continuous (fourierₛ (sLocalTraceEta f ξ))
    rw [← funext hη]
    exact (schwartzBruhat_continuous (sAdeleSchwartzFourier η)).comp continuous_ofAdd
  have hgl := sLocalTrace_fourier_log_integrable f ξ
  let m : Aₛ → ℝ := fun w ↦ modS(w)
  have hm : Continuous m :=
    (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  have hband (r : ℝ) : MeasurableSet (band(r)) := (isClosed_le hm continuous_const).measurableSet
  have hfull : ∀ᵐ u ∂νₛ, u ∈ range (Units.val : Iₛ → Aₛ) :=
    measure_eq_zero_iff_ae_notMem.mp sLocalTrace_nonunits_null |>.mono fun _ h ↦ not_not.mp h
  have hmpos : ∀ᵐ w ∂νₛ, 0 < m w := by
    filter_upwards [hfull] with w hw
    obtain ⟨u, rfl⟩ := hw
    have h : m u.val = normS(u) := by simp [m, sIdeleNorm, Units.coe_prod]
    rw [h]
    exact NNReal.coe_pos.mpr (Units.zero_lt _)
  -- The logarithmic width, and the joint integrand.
  let φ : Aₛ → ℝ := fun w ↦ if m w / L' ≤ L then Real.log L - Real.log (m w / L') else 0
  have hφ (w : Aₛ) (hw : 0 < m w) :
      φ w = (band(L * L')).indicator (fun w ↦ Real.log (L * L') - Real.log (m w)) w := by
    have hiff : m w / L' ≤ L ↔ w ∈ band(L * L') := div_le_iff₀ hL'
    by_cases h : w ∈ band(L * L')
    · rw [indicator_of_mem h]
      simp only [φ, if_pos (hiff.2 h)]
      rw [Real.log_div hw.ne' hL'.ne', Real.log_mul hL.ne' hL'.ne']
      ring
    · rw [indicator_of_notMem h]
      simp only [φ, if_neg (mt hiff.1 h)]
  let μt := (volume : Measure ℝ).restrict (Ioc 0 L)
  let T : Set (ℝ × Aₛ) := {p | m p.2 / L' ≤ p.1}
  have hT : MeasurableSet T :=
    measurableSet_le ((hm.measurable.comp measurable_snd).div_const _) measurable_fst
  let K : ℝ × Aₛ → ℂ := fun p ↦ g p.2 * ((T.indicator (fun p ↦ p.1⁻¹) p : ℝ) : ℂ)
  have hKm : Measurable K := (hgc.measurable.comp measurable_snd).mul
    (Complex.measurable_ofReal.comp (measurable_fst.inv.indicator hT))
  have hKt (t : ℝ) (w : Aₛ) : K (t, w) = g w * (((Ici (m w / L')).indicator
      (fun t : ℝ ↦ t⁻¹) t : ℝ) : ℂ) := rfl
  have hind_nonneg (w : Aₛ) (hw : 0 < m w) (t : ℝ) :
      0 ≤ (Ici (m w / L')).indicator (fun t : ℝ ↦ t⁻¹) t := by
    by_cases ht : t ∈ Ici (m w / L')
    · rw [indicator_of_mem ht]
      exact inv_nonneg.mpr ((div_pos hw hL').le.trans ht)
    · rw [indicator_of_notMem ht]
  have hinner (w : Aₛ) (hw : 0 < m w) : ∫ t, K (t, w) ∂μt = g w * (φ w : ℂ) := by
    simp_rw [hKt]
    rw [integral_const_mul, integral_complex_ofReal,
      sLocalTrace_integral_inv_Ici _ L (div_pos hw hL')]
  have hinnerN (w : Aₛ) (hw : 0 < m w) : ∫ t, ‖K (t, w)‖ ∂μt = ‖g w‖ * φ w := by
    have h (t : ℝ) : ‖K (t, w)‖ = ‖g w‖ * (Ici (m w / L')).indicator (fun t : ℝ ↦ t⁻¹) t := by
      rw [hKt, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hind_nonneg w hw t)]
    simp_rw [h]
    rw [integral_const_mul, sLocalTrace_integral_inv_Ici _ L (div_pos hw hL')]
  -- The logarithmic weight against the transform is integrable.
  have hgφ : Integrable (fun w ↦ ‖g w‖ * φ w) νₛ := by
    have hlog : Integrable (fun w ↦ ‖g w‖ * Real.log (m w)) νₛ :=
      hgl.norm.mono' ((hgc.norm.measurable.mul (Real.measurable_log.comp hm.measurable)).aestronglyMeasurable)
        (ae_of_all _ fun w ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs])
    have hi : Integrable ((band(L * L')).indicator
        (fun w ↦ ‖g w‖ * (Real.log (L * L') - Real.log (m w)))) νₛ := by
      refine Integrable.indicator ?_ (hband _)
      simp_rw [mul_sub]
      exact (hgi.norm.mul_const _).sub hlog
    refine hi.congr ?_
    filter_upwards [hmpos] with w hw
    rw [hφ w hw]
    by_cases h : w ∈ band(L * L')
    · rw [indicator_of_mem h, indicator_of_mem h]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  have hKi : Integrable K (μt.prod νₛ) := by
    rw [integrable_prod_iff' hKm.aestronglyMeasurable]
    refine ⟨?_, hgφ.congr ?_⟩
    · filter_upwards [hmpos] with w hw
      have ha : 0 < m w / L' := div_pos hw hL'
      have hb : Integrable (fun t ↦ (Ici (m w / L')).indicator (fun t : ℝ ↦ t⁻¹) t) μt := by
        rw [integrable_indicator_iff measurableSet_Ici, IntegrableOn,
          Measure.restrict_restrict measurableSet_Ici]
        refine (ContinuousOn.integrableOn_compact (isCompact_Icc : IsCompact (Icc (m w / L') L))
          (continuousOn_inv₀.mono fun t ht ↦ (ha.trans_le ht.1).ne')).mono_set ?_
        rintro t ⟨h1, -, h3⟩
        exact ⟨h1, h3⟩
      simp_rw [hKt]
      exact (hb.ofReal).const_mul _
    · filter_upwards [hmpos] with w hw
      exact (hinnerN w hw).symm
  -- The band integral at a positive radius is the inner integral in w.
  have hlhs (t : ℝ) (ht : 0 < t) :
      (∫ w in band(L' * t), g w ∂νₛ) / (t : ℂ) = ∫ w, K (t, w) ∂νₛ := by
    rw [← integral_indicator (hband _), ← integral_div]
    refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
    change (band(L' * t)).indicator g w / (t : ℂ) = K (t, w)
    rw [hKt]
    have hiff : w ∈ band(L' * t) ↔ t ∈ Ici (m w / L') := by
      rw [mem_Ici, div_le_iff₀ hL', mul_comm]
      rfl
    by_cases h : w ∈ band(L' * t)
    · rw [indicator_of_mem h, indicator_of_mem (hiff.1 h), Complex.ofReal_inv, div_eq_mul_inv]
    · rw [indicator_of_notMem h, indicator_of_notMem (mt hiff.2 h), zero_div,
        Complex.ofReal_zero, mul_zero]
  have hcongr : ∀ᵐ t ∂μt, (∫ w in band(L' * t), g w ∂νₛ) / (t : ℂ) = ∫ w, K (t, w) ∂νₛ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hlhs t ht.1
  refine ⟨hKi.integral_prod_left.congr (hcongr.mono fun _ h ↦ h.symm), ?_⟩
  change (volume₁ : ℂ) * ∫ t, _ ∂μt = _
  rw [integral_congr_ae hcongr, integral_integral_swap (f := fun t w ↦ K (t, w)) hKi]
  unfold sLocalTraceSharpMass
  congr 1
  have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F))
  rw [← integral_indicator ((hband _).inter ho.isOpen_range.measurableSet)]
  refine integral_congr_ae ?_
  filter_upwards [hmpos, hfull] with w hw hu
  rw [hinner w hw, hφ w hw]
  by_cases h : w ∈ band(L * L')
  · rw [indicator_of_mem h, indicator_of_mem
      (show w ∈ band(L * L') ∩ range (Units.val : Iₛ → Aₛ) from ⟨h, hu⟩)]
  · rw [indicator_of_notMem h, indicator_of_notMem
      (show w ∉ band(L * L') ∩ range (Units.val : Iₛ → Aₛ) from fun h' ↦ h h'.1),
      Complex.ofReal_zero, mul_zero]

/-- Paper: (12.4.1.22), p. 518. The slab of norm at most L in an S-unit fundamental
domain is null measurable for additive Tamagawa measure on the S-ideles, which has the
same null sets as multiplicative Tamagawa measure there. -/
private theorem sLocalTrace_fundamentalDomain_slab_nullMeasurable (D : Set Iₛ)
    (hD : IsFundamentalDomain Hₛ D μₛ) (L : ℝ) :
    NullMeasurableSet (D ∩ {x : Iₛ | normS(x) ≤ L}) ((νₛ).comap (Units.val : Iₛ → Aₛ)) := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have hnm : Measurable fun x : Iₛ ↦ normS(x) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      sLocalTrace_sIdeleNorm_continuous)).measurable
  have hpos (x : Iₛ) : 0 < sLocalTraceMeasureFactor S / normS(x) := by
    refine div_pos (Finset.prod_pos fun v _ ↦ ?_)
      (NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S x)))
    have hv : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_pos (by linarith) (sub_pos.mpr hv)
  have hac : (νₛ).comap (Units.val : Iₛ → Aₛ) ≪ μₛ := by
    rw [sLocalTrace_mult_eq_withDensity]
    intro t ht
    have hdm : Measurable fun x : Iₛ ↦ ENNReal.ofReal (sLocalTraceMeasureFactor S / normS(x)) :=
      (measurable_const.div hnm).ennreal_ofReal
    rw [withDensity_apply_eq_zero hdm] at ht
    have hall : {x : Iₛ | ENNReal.ofReal (sLocalTraceMeasureFactor S / normS(x)) ≠ 0} = univ :=
      eq_univ_of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne'
    rwa [hall, univ_inter] at ht
  exact (hD.nullMeasurableSet.inter (measurableSet_le hnm measurable_const).nullMeasurableSet).mono_ac
    hac

/-- The band integral of the Fourier transform of the translated test is measurable in
the radius. -/
private theorem sLocalTrace_band_integral_measurable (f : BruhatCompactSupport Iₛ) (ξ : Hₛ)
    (L' : ℝ) :
    Measurable fun t : ℝ ↦ ∫ w in band(L' * t), fourierₛ (sLocalTraceEta f ξ) w ∂νₛ := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace Aₛ := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  obtain ⟨η, hη⟩ := SLocalTraceEta.eta_test f ξ
  have hg : Continuous (fourierₛ (sLocalTraceEta f ξ)) := by
    rw [← funext hη]
    exact (schwartzBruhat_continuous (sAdeleSchwartzFourier η)).comp continuous_ofAdd
  have hm : Continuous fun t : Aₛ ↦ modS(t) :=
    (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  let T : Set (ℝ × Aₛ) := {p | modS(p.2) ≤ L' * p.1}
  have hT : MeasurableSet T :=
    measurableSet_le (hm.measurable.comp measurable_snd) (measurable_const.mul measurable_fst)
  let G : ℝ × Aₛ → ℂ := T.indicator fun p ↦ fourierₛ (sLocalTraceEta f ξ) p.2
  have hG : Measurable G := (hg.measurable.comp measurable_snd).indicator hT
  have hband (r : ℝ) : MeasurableSet (band(r)) := (isClosed_le hm continuous_const).measurableSet
  have heq : (fun t : ℝ ↦ ∫ w in band(L' * t), fourierₛ (sLocalTraceEta f ξ) w ∂νₛ) =
      fun t ↦ ∫ w, G (t, w) ∂νₛ := by
    funext t
    rw [← integral_indicator (hband _)]
    rfl
  rw [heq]
  exact (hG.stronglyMeasurable.integral_prod_right' (ν := νₛ)).measurable

/-- Paper: (12.4.1.22)–(12.4.1.24), p. 518. With sharp upper cutoffs the orbital
mass is the skew-diagonal integral on an S-unit fundamental domain. The change
of variable w = xu converts the integral to the log-weighted Fourier integral.
Deviation: Use the sharp indicators explicitly. The spatial variable is an S-idele,
and its additive integral uses the image of the fundamental domain under the unit embedding. -/
theorem sLocalTraceSharpMass_eq_integral (f : BruhatCompactSupport Iₛ) (ξ : Hₛ)
    (D : Set Iₛ) (_hD : IsFundamentalDomain Hₛ D μₛ)
    (L L' : ℝ) (_hL : 0 < L) (_hL' : 0 < L') :
    let d := D ∩ {x : Iₛ | normS(x) ≤ L}
    let K := sLocalTraceCutoffKernel f (indicator {x : Iₛ | normS(x) ≤ L} (fun _ ↦ 1))
      (indicator band(L') (fun _ ↦ 1))
    let diag := fun x : Iₛ ↦ K (ξ.val * x) x.val
    IntegrableOn diag d ((νₛ).comap (Units.val : Iₛ → Aₛ)) ∧
      (∫ x in d, diag x ∂((νₛ).comap (Units.val : Iₛ → Aₛ))) =
        sLocalTraceSharpMass f ξ (L * L') := by
  intro d K diag
  let h : ℝ → ℂ := fun t ↦ ∫ w in band(L' * t), fourierₛ (sLocalTraceEta f ξ) w ∂νₛ
  obtain ⟨hti, hte⟩ := sLocalTrace_band_log_fubini f ξ L L' _hL _hL'
  obtain ⟨hri, hre⟩ := sLocalTrace_fundamentalDomain_radial D _hD L h
    (sLocalTrace_band_integral_measurable f ξ L') hti
  obtain ⟨hci, hce⟩ := sLocalTrace_setIntegral_comap_density d (fun x ↦ h (normS(x))) hri
  have hd (x : Iₛ) (hx : x ∈ d) :
      (sLocalTraceMeasureFactor S : ℂ) * ((normS(x))⁻¹ : ℂ) * h (normS(x)) = diag x := by
    have hk := sLocalTraceSharp_diag f ξ L L' x hx.2
    rw [sLocalTrace_integral_band_dilate] at hk
    exact (hk.trans (mul_assoc _ _ _).symm).symm
  have hdm : NullMeasurableSet d ((νₛ).comap (Units.val : Iₛ → Aₛ)) :=
    sLocalTrace_fundamentalDomain_slab_nullMeasurable D _hD L
  refine ⟨hci.congr_fun_ae ?_, ?_⟩
  · exact (ae_restrict_iff'₀ hdm).2 (ae_of_all _ hd)
  · rw [← setIntegral_congr_ae₀ hdm (ae_of_all _ hd), hce, hre, hte]

local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : S) → BruhatCompactSupport (v.val.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "principalValues(" a "," b ")" =>
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑ v : S, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finiteVolume(v.val) : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v.val 1 (b v))

/-- Summation bookkeeping for `sLocalTraceSharpMass_asymptotic`: if the masses split as the
logarithmic term, a summable constant term and a remainder that sums to something tending
to zero, then the summed masses have the stated asymptotic. -/
private theorem sLocalTraceSharpMass_asymptotic_assemble {ι : Type*} (m : ι → ℝ → ℂ)
    (y κ : ι → ℂ) (K P c : ℂ) (T : ℝ → ℂ) (hy : HasSum y c) (hκ : HasSum κ P)
    (hT : ∀ᶠ R in atTop, HasSum (fun i ↦ m i R - K * (y i * (Real.log R : ℂ) + κ i)) (T R))
    (hT0 : Tendsto T atTop (𝓝 0)) :
    ∃ M : ℝ → ℂ, (∀ᶠ R in atTop, HasSum (fun i ↦ m i R) (M R)) ∧
      Tendsto (fun R ↦ M R - K * c * (Real.log R : ℂ)) atTop (𝓝 (K * P)) := by
  refine ⟨fun R ↦ T R + K * (c * (Real.log R : ℂ) + P), ?_, ?_⟩
  · filter_upwards [hT] with R hR
    have h := hR.add (((hy.mul_right (Real.log R : ℂ)).add hκ).mul_left K)
    simpa using h
  · have h := hT0.add_const (K * P)
    rw [zero_add] at h
    refine h.congr fun R ↦ ?_
    ring

/-- Paper: (12.4.1.26)–(12.4.1.28), p. 519. The restrictions of the global test to the
local unit groups at the infinite places and at the places of S are compactly supported
Bruhat tests. -/
private theorem sLocalTraceSharpMass_asymptotic_restrict (φ : BruhatCompactSupport C𝔽) :
    ∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ),
        (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) := by
  choose A hA using fun w : InfinitePlace F ↦ idelicExplicitFormula_infiniteTestMap (F := F) w
  choose B hB using fun v : S ↦ idelicExplicitFormula_finiteTestMap (F := F) v.val
  exact ⟨fun w ↦ A w φ, fun v ↦ B v φ, fun w ↦ hA w φ, fun v ↦ hB v φ⟩

/-- The unit-locus integral of the Fourier transform is the value of the
translated test at the origin.  This is the coefficient of the logarithmic
term in both sharp-mass subgoals below. -/
private theorem sLocalTrace_fourier_integral_units (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    ∫ w in range (Units.val : Iₛ → Aₛ), fourierₛ (sLocalTraceEta f ξ) w ∂νₛ =
      f.val ξ.val := by
  classical
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  obtain ⟨η, hη⟩ := SLocalTraceEta.eta_test f ξ
  have hηfun : (fun x : Aₛ ↦ η (Multiplicative.ofAdd x)) = sLocalTraceEta f ξ := by
    funext x
    exact hη x
  have hfun : (fun x : Aₛ ↦ sAdeleSchwartzFourier η (Multiplicative.ofAdd x)) =
      (fun x : Aₛ ↦ fourierₛ (sLocalTraceEta f ξ) x) := by
    funext x
    change tamagawaFourier νₛ ψₛ (fun z : Aₛ ↦ η (Multiplicative.ofAdd z)) x =
      tamagawaFourier νₛ ψₛ (sLocalTraceEta f ξ) x
    rw [hηfun]
  have hzero := sAdeleSchwartzFourier_apply_zero (F := F) (S := S)
    (sAdeleSchwartzFourier η)
  have hinv := sLocal_fourier_inversion (F := F) (S := S) η (0 : Aₛ)
  have htotal : (∫ x : Aₛ, fourierₛ (sLocalTraceEta f ξ) x ∂νₛ) =
      f.val ξ.val := by
    rw [← integral_congr_ae (ae_of_all _ (fun x ↦ congrFun hfun x))]
    rw [← hzero]
    rw [hinv]
    simpa only [neg_zero] using (hη 0).trans (sLocalTraceEta_zero_neg_one f ξ).1
  have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) :=
    IsOpenUnits.isOpenEmbedding_unitsVal
      (M := ((w : InfinitePlace F) → w.Completion) ×
        ((v : S) → v.val.adicCompletion F))
  have hfull : ∀ᵐ w ∂νₛ, w ∈ range (Units.val : Iₛ → Aₛ) :=
    measure_eq_zero_iff_ae_notMem.mp sLocalTrace_nonunits_null |>.mono fun _ h ↦ not_not.mp h
  rw [← integral_indicator ho.isOpen_range.measurableSet]
  have hind :
      (∫ x : Aₛ, (range (Units.val : Iₛ → Aₛ)).indicator
          (fourierₛ (sLocalTraceEta f ξ)) x ∂νₛ) =
        ∫ x : Aₛ, fourierₛ (sLocalTraceEta f ξ) x ∂νₛ := by
    apply integral_congr_ae
    filter_upwards [hfull] with x hx
    rw [indicator_of_mem hx]
  rw [hind, htotal]

section SharpMassConstant

open scoped Pointwise

attribute [local instance] instInfiniteCompletionMeasurableSpaceSec4 instFiniteCompletionMeasurableSec4b

/-- Only finitely many translates of the local group by the discrete norm-one subgroup meet a fixed
compact set. -/
private theorem finite_translates_on_local_group
    {G U N : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CommGroup U] [TopologicalSpace U] [CommGroup N] [TopologicalSpace N]
    (H : Subgroup G) [DiscreteTopology H] (hH : IsClosed (H : Set G))
    (n : G →ₜ* N) (i : U →ₜ* G) (hi : IsProperMap (n ∘ i))
    (hn : ∀ ξ : H, n ξ.val = 1) (K : Set G) (hK : IsCompact K) :
    {ξ : H | ∃ u, ξ.val * i u ∈ K}.Finite := by
  let C := (n ∘ i) ⁻¹' (n '' K)
  have hC : IsCompact C := hi.isCompact_preimage (hK.image n.continuous)
  have hT := hK.mul (hC.image (i.continuous.inv))
  have hpre := (IsClosed.isClosedEmbedding_subtypeVal hH).isCompact_preimage hT
  refine hpre.finite_of_discrete.subset ?_
  rintro ξ ⟨u, hu⟩
  have huC : u ∈ C := ⟨ξ.val * i u, hu, by simp [hn]⟩
  exact ⟨ξ.val * i u, hu, (i u)⁻¹, ⟨u, huC, rfl⟩, mul_inv_cancel_right _ _⟩

/-- Pulling a multiplicative test back by inversion negates each coordinate of its elementary
presentation. -/
private theorem inv_bruhat_test {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (a : BruhatCompactSupport G) :
    ∃ b : BruhatCompactSupport G, ∀ u, b.val u = a.val u⁻¹ := by
  refine ⟨⟨fun u ↦ a.val u⁻¹, (mem_bruhatSmoothSubmodule_iff _).2 ?_,
    a.property.2.comp_homeomorph (Homeomorph.inv G)⟩, fun _ ↦ rfl⟩
  intro p
  obtain ⟨k, hk, hfix, hs⟩ := (mem_bruhatSmoothSubmodule_iff _).1 a.property.1 p
  refine ⟨k, hk, fun h x ↦ ?_, fun A hA ↦ ?_⟩
  · simpa only [mul_inv_rev, Subgroup.coe_inv, mul_comm] using hfix h⁻¹ x⁻¹
  · obtain ⟨f, hf, hcont⟩ := hs A hA
    refine ⟨fun q ↦ f q⁻¹, fun x ↦ hf x⁻¹, fun e z b ↦ ?_⟩
    have he (xt) : (e.equiv.symm (Multiplicative.ofAdd (elementaryCover xt z b)))⁻¹ =
        e.equiv.symm (Multiplicative.ofAdd (elementaryCover (-xt) (-z) (-b))) := by
      rw [← map_inv]
      rfl
    simp_rw [he]
    exact (hcont e (-z) (-b)).comp contDiff_neg

/-- A density on one coordinate that computes every integrable pairing with a weight on that
coordinate. -/
private def HasIntegralMarginal {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (p : X → Y) (g : X → ℂ) (a : Y → ℂ) : Prop :=
  Integrable a ν ∧ ∀ k : Y → ℂ, Integrable (fun x ↦ g x * k (p x)) μ →
    Integrable (fun y ↦ a y * k y) ν ∧
      (∫ x, g x * k (p x) ∂μ) = ∫ y, a y * k y ∂ν

private theorem hasIntegralMarginal_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] {g : X × Y → ℂ}
    (hg : Integrable g (μ.prod ν)) :
    HasIntegralMarginal (μ.prod ν) μ Prod.fst g (fun x ↦ ∫ y, g (x, y) ∂ν) := by
  refine ⟨hg.integral_prod_left, fun k hk ↦ ?_⟩
  have he (x : X) : (∫ y, g (x, y) * k x ∂ν) = (∫ y, g (x, y) ∂ν) * k x :=
    integral_mul_const _ _
  refine ⟨hk.integral_prod_left.congr (ae_of_all _ he), (integral_prod _ hk).trans ?_⟩
  exact integral_congr_ae (ae_of_all _ he)

private theorem HasIntegralMarginal.comp {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] {μ : Measure X} {ν : Measure Y} {τ : Measure Z}
    {p : X → Y} {q : Y → Z} {g : X → ℂ} {a : Y → ℂ} {b : Z → ℂ}
    (ha : HasIntegralMarginal μ ν p g a) (hb : HasIntegralMarginal ν τ q a b) :
    HasIntegralMarginal μ τ (q ∘ p) g b := by
  refine ⟨hb.1, fun k hk ↦ ?_⟩
  obtain ⟨h1, e1⟩ := ha.2 (k ∘ q) hk
  obtain ⟨h2, e2⟩ := hb.2 k h1
  exact ⟨h2, e1.trans e2⟩

private theorem hasIntegralMarginal_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    {g : X → ℂ} (hg : Integrable g μ) :
    HasIntegralMarginal μ ν e g (g ∘ e.symm) := by
  refine ⟨(he.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hg, fun k hk ↦ ?_⟩
  have h (x : X) : (g ∘ e.symm) (e x) * k (e x) = g x * k (e x) := by simp
  refine ⟨(he.integrable_comp_emb e.measurableEmbedding).mp ((integrable_congr (ae_of_all _ h)).2 hk), ?_⟩
  exact (integral_congr_ae (ae_of_all _ fun x ↦ (h x).symm)).trans
    (he.integral_comp' (fun y ↦ (g ∘ e.symm) y * k y))

private theorem hasIntegralMarginal_pi {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (i : ι) {g : (∀ j, X j) → ℂ} (hg : Integrable g (Measure.pi μ)) :
    ∃ a, HasIntegralMarginal (Measure.pi μ) (μ i) (fun x ↦ x i) g a := by
  classical
  let : Fintype {j // j = i} := Subtype.fintype _
  let e := MeasurableEquiv.piEquivPiSubtypeProd X (· = i)
  have he := measurePreserving_piEquivPiSubtypeProd μ (· = i)
  have h1 := hasIntegralMarginal_equiv e he hg
  have h2 := hasIntegralMarginal_fst h1.1
  let j : {j // j = i} := ⟨i, rfl⟩
  let : Unique {j // j = i} := ⟨⟨j⟩, fun x ↦ Subtype.ext x.property⟩
  let e' := MeasurableEquiv.piUnique (fun j : {j // j = i} ↦ X j.val)
  have h3 := hasIntegralMarginal_equiv e' (measurePreserving_piUnique _) h2.1
  exact ⟨_, (h1.comp h2).comp h3⟩

/-- Inversion changes the sign of the local Weil kernel paired with the difference of the two tests.
-/
private theorem integral_inv_diff_kernel {K : Type*} [NormedField K] [MeasurableSpace Kˣ] [MeasurableInv Kˣ]
    (μ : Measure Kˣ) [μ.IsInvInvariant] (a : Kˣ → ℂ) (d : ℕ) :
    (∫ u : Kˣ, (a u⁻¹ - a u) * (Real.sqrt (‖u.val‖ ^ d) : ℂ) /
      ((‖1 - u.val‖ ^ d : ℝ) : ℂ) ∂μ) = 0 := by
  let k (u : Kˣ) : ℂ := (a u⁻¹ - a u) * (Real.sqrt (‖u.val‖ ^ d) : ℂ) /
    ((‖1 - u.val‖ ^ d : ℝ) : ℂ)
  have h (u : Kˣ) : k u⁻¹ = -k u := by
    have he : (1 : K) - (u⁻¹).val = -(1 - u.val) * (u⁻¹).val := by
      rw [neg_sub, sub_mul, Units.mul_inv, one_mul]
    have hN : ‖1 - (u⁻¹).val‖ = ‖1 - u.val‖ * ‖u.val‖⁻¹ := by rw [he, norm_mul, norm_neg]; simp
    have hsq : (Real.sqrt (‖u.val‖ ^ d) : ℂ) ^ 2 = ((‖u.val‖ ^ d : ℝ) : ℂ) := by
      exact_mod_cast Real.sq_sqrt (pow_nonneg (norm_nonneg _) _)
    have hne : (Real.sqrt (‖u.val‖ ^ d) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (pow_pos (norm_pos_iff.mpr u.ne_zero) d)).ne'
    dsimp only [k]
    rw [hN]
    simp only [inv_inv, Units.val_inv_eq_inv_val, norm_inv, inv_pow, Real.sqrt_inv,
      mul_pow, Complex.ofReal_mul, Complex.ofReal_inv]
    rw [← hsq]
    ring_nf
    field_simp
  have he := integral_inv_eq_self k μ
  simp_rw [h, integral_neg] at he
  change (∫ u, k u ∂μ) = 0
  linear_combination -he / 2

private theorem finitePV_inv (v : HeightOneSpectrum (𝓞 F)) (a b : BruhatCompactSupport
    (v.adicCompletion F)ˣ) (hb : ∀ u, b.val u = a.val u⁻¹) :
    finiteConnesWeilPrincipalValue v 1 b = finiteConnesWeilPrincipalValue v 1 a := by
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have h0 : (b - a).val 1 = 0 := by change b.val 1 - a.val 1 = 0; simp [hb]
  have hD := (finiteConnesWeilPrincipalValue_of_apply_one_zero v (b - a) h0).2
  have : (finiteLocalMultiplicativeTamagawaMeasure F v).IsHaarMeasure :=
    finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : SecondCountableTopology (v.adicCompletion F)ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : (finiteLocalMultiplicativeTamagawaMeasure F v).Regular := inferInstance
  have hk := integral_inv_diff_kernel (finiteLocalMultiplicativeTamagawaMeasure F v) a.val 1
  simp only [pow_one] at hk
  apply sub_eq_zero.mp
  rw [← map_sub, hD]
  convert hk using 1
  congr 1
  funext u
  change (b.val u - a.val u) * _ / _ = _
  rw [hb]

-- The zero-at-one complex case follows the local calculation in Ch01_Introduction/Sec4.
/-- A Schwartz test vanishing at zero is integrable against the reciprocal squared radius in the plane. -/
private theorem sLocalTrace_schwartz_integrable_div_square (g : SchwartzMap ℂ ℂ)
    (hg : g 0 = 0) : Integrable (fun z : ℂ ↦ g z / ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
  let C := SchwartzMap.seminorm ℝ 0 1 g
  have hlip (z : ℂ) : ‖g z‖ ≤ C * ‖z‖ := by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := g) (s := univ) (C := C)
      (fun z _ ↦ g.differentiableAt) (fun z _ ↦ ?_) convex_univ (mem_univ 0) (mem_univ z)
    · simpa [hg] using h
    · rw [← norm_iteratedFDeriv_one]
      exact g.norm_iteratedFDeriv_le_seminorm ℝ 1 z
  let B := Metric.ball (0 : ℂ) 1
  have hi : IntegrableOn (fun z : ℂ ↦ ‖z‖⁻¹) B := by
    rw [integrableOn_fun_norm_addHaar (μ := volume) (f := fun y : ℝ ↦ y⁻¹), Complex.finrank_real_complex]
    refine (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun (fun y (hy : y ∈ Ioo 0 1) ↦ ?_)
      measurableSet_Ioo
    simp [smul_eq_mul, hy.1.ne']
  have hiB := (integrable_indicator_iff (show MeasurableSet B from measurableSet_ball)).mpr (hi.const_mul C)
  refine (hiB.add g.integrable.norm).mono'
    (g.continuous.measurable.div (by fun_prop)).aestronglyMeasurable (.of_forall fun z ↦ ?_)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  by_cases hz : z ∈ B
  · rw [indicator_of_mem hz]
    refine (le_add_of_nonneg_right (norm_nonneg _)).trans' ?_
    rcases eq_or_ne z 0 with rfl | hn
    · simp
    have hp : 0 < ‖z‖ := norm_pos_iff.mpr hn
    calc ‖g z‖ / ‖z‖ ^ 2 ≤ (C * ‖z‖) / ‖z‖ ^ 2 := by gcongr; exact hlip z
      _ = C * ‖z‖⁻¹ := by field_simp
  · rw [indicator_of_notMem hz, zero_add]
    have h1 : 1 ≤ ‖z‖ := le_of_not_gt fun h ↦ hz (mem_ball_zero_iff.mpr h)
    exact div_le_self (norm_nonneg _) (by nlinarith)

/-- At a complex place, vanishing at zero removes the finite-part cutoff. -/
private theorem sLocalTrace_complex_add (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion)) (hf : f (Multiplicative.ofAdd 0) = 0) :
    letI : MeasurableSpace w.Completion := borel _
    Integrable (fun x ↦ f (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ)) (infiniteLocalAdditiveTamagawaMeasure F w) ∧
    infiniteConnesPrincipalValue w f = (1 / (2 * (Real.pi : ℂ))) *
      ∫ x, f (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂(infiniteLocalAdditiveTamagawaMeasure F w) := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let m := j.symm.toHomeomorph.toMeasurableEquiv
  obtain ⟨g, hgf⟩ := complexModelSchwartz w hw f
  have hg (z : ℂ) : g z = f (Multiplicative.ofAdd (e.symm z)) := congrFun hgf z
  have hz : e.symm 0 = 0 := map_zero e.symm
  have hi := sLocalTrace_schwartz_integrable_div_square g
    (by rw [hg, hz]; exact hf)
  have hμ : (infiniteLocalAdditiveTamagawaMeasure F w) = (2 • (volume : Measure ℂ)).map m :=
    dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)
  have hG : Integrable (fun x ↦ f (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ)) (infiniteLocalAdditiveTamagawaMeasure F w) := by
    rw [hμ, integrable_map_equiv]
    have hsc : Integrable (fun z : ℂ ↦ g z / ((‖z‖ ^ 2 : ℝ) : ℂ)) (2 • volume) := by
      simpa only [two_smul] using hi.add_measure hi
    refine hsc.congr (ae_of_all _ fun z ↦ ?_)
    change g z / _ = f (Multiplicative.ofAdd (e.symm z)) / _
    rw [hg, show ‖m z‖ = ‖z‖ from j.symm.isometry.norm_map_of_map_zero (map_zero e.symm) z]
  refine ⟨hG, ?_⟩
  have hT := ((exists_infiniteConnesPrincipalValue w).choose_spec f).2
  change infiniteConnesPrincipalValue w f = _ at hT
  have hL := (complexLogFourier_finitePart w hw f).2.2
  simp only [hf, mul_zero, zero_mul, add_zero] at hL
  have hm (ε : ℝ) : MeasurableSet {x : w.Completion | ε ≤ ‖x‖ ^ 2} :=
    measurableSet_le measurable_const (measurable_norm.pow_const _)
  have hlim : Tendsto (fun ε : ℝ ↦ ∫ x in {x : w.Completion | ε ≤ ‖x‖ ^ 2},
      f (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂(infiniteLocalAdditiveTamagawaMeasure F w)) (𝓝[>] 0)
      (𝓝 (∫ x, f (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂(infiniteLocalAdditiveTamagawaMeasure F w))) := by
    simp_rw [← integral_indicator (hm _)]
    refine tendsto_integral_filter_of_dominated_convergence _
      (.of_forall fun ε ↦ hG.aestronglyMeasurable.indicator (hm ε))
      (.of_forall fun ε ↦ .of_forall fun x ↦ norm_indicator_le_norm_self _ _)
      hG.norm (.of_forall fun x ↦ ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Set.indicator_apply]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (sq_pos_of_pos (norm_pos_iff.mpr hx)))] with ε hε
      rw [indicator_of_mem (show ε ≤ ‖x‖ ^ 2 from hε.le)]
  rw [hT, tendsto_nhds_unique hlim hL]
  push_cast
  field_simp

/-- Multiplicative Haar integration at a complex place uses the inverse squared radius. -/
private theorem sLocalTrace_complex_haar (w : InfinitePlace F) (hw : w.IsComplex)
    (g : w.Completion → ℂ) :
    letI : MeasurableSpace w.Completion := borel _
    (Integrable (fun u : w.Completionˣ ↦ g u.val) (infiniteLocalMultiplicativeTamagawaMeasure F w) ↔
      Integrable (fun y ↦ (‖y‖ ^ 2)⁻¹ • g y) (infiniteLocalAdditiveTamagawaMeasure F w)) ∧
      ∫ u : w.Completionˣ, g u.val ∂(infiniteLocalMultiplicativeTamagawaMeasure F w) = ∫ y, (‖y‖ ^ 2)⁻¹ • g y ∂(infiniteLocalAdditiveTamagawaMeasure F w) := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  let d : w.Completion → ENNReal := fun y ↦ (↑(‖y‖₊ ^ w.mult) : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  have hdlt : ∀ᵐ y ∂((infiniteLocalAdditiveTamagawaMeasure F w).restrict (range (Units.val : w.Completionˣ → w.Completion))), d y < ⊤ := by
    refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    exact ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr (pow_pos (nnNorm_pos.mpr (hu ▸ u.ne_zero)) _))
  have hdy (y : w.Completion) : (d y).toReal = (‖y‖ ^ 2)⁻¹ := by
    simp [d, hw.mult_eq_two]
  have hs : support (fun y ↦ (‖y‖ ^ 2)⁻¹ • g y) ⊆ range (Units.val : w.Completionˣ → w.Completion) := by
    intro y hy
    have hn : y ≠ 0 := by rintro rfl; simp at hy
    exact ⟨Units.mk0 y hn, rfl⟩
  change (Integrable (g ∘ Units.val) (((infiniteLocalAdditiveTamagawaMeasure F w).withDensity d).comap Units.val) ↔ _) ∧
    ∫ u : w.Completionˣ, g u.val ∂(((infiniteLocalAdditiveTamagawaMeasure F w).withDensity d).comap Units.val) = _
  constructor
  · rw [← hval.integrable_map_iff (g := g), hval.map_comap, restrict_withDensity hval.measurableSet_range,
      integrable_withDensity_iff_integrable_smul' hd hdlt,
      ← integrableOn_iff_integrable_of_support_subset hs]
    simp_rw [hdy]
    rfl
  · rw [← hval.integral_map (g := g), hval.map_comap,
      setIntegral_withDensity_eq_setIntegral_toReal_smul hd hdlt _ hval.measurableSet_range,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := range Units.val)
        (fun y hy ↦ Function.notMem_support.mp (fun h ↦ hy (hs h)))]
    simp_rw [hdy]

/-- A test vanishing at one gives the ordinary integrable complex-place kernel, normalized by 1/(2π). -/
private theorem sLocalTrace_complex_place (w : InfinitePlace F) (hw : w.IsComplex)
    (f : BruhatCompactSupport w.Completionˣ) (hf : f.val 1 = 0) :
    Integrable (fun u : w.Completionˣ ↦ f.val u * (Real.sqrt (‖u.val‖ ^ w.mult) : ℂ) /
      ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)) (infiniteLocalMultiplicativeTamagawaMeasure F w) ∧
    infiniteConnesWeilPrincipalValue w f = (1 / (2 * (Real.pi : ℂ))) *
      ∫ u : w.Completionˣ, f.val u * (Real.sqrt (‖u.val‖ ^ w.mult) : ℂ) /
        ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ) ∂(infiniteLocalMultiplicativeTamagawaMeasure F w) := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : ((infiniteLocalAdditiveTamagawaMeasure F w)).IsAddHaarMeasure := infiniteLocalAdditiveTamagawaMeasure_haar F w
  let A := (exists_infiniteWeilTestMap w).choose
  let Fz : w.Completion → ℂ := Function.extend Units.val (f.val : _ → ℂ) (fun _ ↦ 0)
  have hA (x : w.Completion) : (A f) (Multiplicative.ofAdd x) = Fz (1 + x) /
      (Real.sqrt (‖1 + x‖ ^ w.mult) : ℂ) := (exists_infiniteWeilTestMap w).choose_spec f x
  have hFu (u : w.Completionˣ) : Fz u.val = f.val u := Units.val_injective.extend_apply _ _ u
  have h0 : (A f) (Multiplicative.ofAdd 0) = 0 := by
    rw [hA]
    rw [add_zero, ← Units.val_one, hFu, hf, zero_div]
  let Q (y : w.Completion) := Fz y * (‖y‖ : ℂ) / ((‖1 - y‖ ^ 2 : ℝ) : ℂ)
  let H (y : w.Completion) := (‖y‖ ^ 2)⁻¹ • Q y
  have hPH (x : w.Completion) : (A f) (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ) = H (1 + x) := by
    rw [hA]
    change Fz (1 + x) / (Real.sqrt (‖1 + x‖ ^ w.mult) : ℂ) / _ = (‖1 + x‖ ^ 2)⁻¹ •
      (Fz (1 + x) * (‖1 + x‖ : ℂ) / ((‖1 - (1 + x)‖ ^ 2 : ℝ) : ℂ))
    rw [hw.mult_eq_two, Real.sqrt_sq (norm_nonneg _), sub_add_cancel_left, norm_neg, Complex.real_smul]
    push_cast
    by_cases hz : ‖1 + x‖ = 0
    · simp [hz]
    · have hn : (‖1 + x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      field_simp
  have hQ : (fun u : w.Completionˣ ↦ f.val u * (Real.sqrt (‖u.val‖ ^ w.mult) : ℂ) /
      ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)) = fun u : w.Completionˣ ↦ Q u.val := by
    funext u
    dsimp only [Q]
    rw [hw.mult_eq_two, Real.sqrt_sq (norm_nonneg _), hFu]
  obtain ⟨hi, he⟩ := sLocalTrace_complex_add w hw (A f) h0
  rw [show (fun x ↦ (A f) (Multiplicative.ofAdd x) / ((‖x‖ ^ 2 : ℝ) : ℂ)) = fun x ↦ H (1+x) from funext hPH] at hi he
  have hHI : Integrable H (infiniteLocalAdditiveTamagawaMeasure F w) :=
    (hi.comp_add_left (-1)).congr (ae_of_all _ fun x ↦ congrArg H (add_neg_cancel_left 1 x))
  rw [hQ]
  refine ⟨(sLocalTrace_complex_haar w hw Q).1.mpr hHI, ?_⟩
  change infiniteConnesPrincipalValue w (A f) = _
  rw [he, integral_add_left_eq_self, (sLocalTrace_complex_haar w hw Q).2]

private theorem infinitePV_inv (w : InfinitePlace F) (a b : BruhatCompactSupport w.Completionˣ)
    (hb : ∀ u, b.val u = a.val u⁻¹) :
    infiniteConnesWeilPrincipalValue w b = infiniteConnesWeilPrincipalValue w a := by
  have h0 : (b - a).val 1 = 0 := by change b.val 1 - a.val 1 = 0; simp [hb]
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology w.Completion := (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology w.Completionˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
    infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure w
  have : (infiniteLocalMultiplicativeTamagawaMeasure F w).Regular := inferInstance
  have hk (d : ℕ) := integral_inv_diff_kernel (infiniteLocalMultiplicativeTamagawaMeasure F w) a.val d
  apply sub_eq_zero.mp
  rw [← map_sub]
  by_cases hw : w.IsReal
  · rw [realConnesWeilPrincipalValue_of_apply_one_zero w hw _ h0]
    have he := hk 1
    simp only [pow_one] at he
    change _ * (∫ u : w.Completionˣ, (b.val u - a.val u) * _ / _ ∂_) = 0
    simp_rw [hb, he, mul_zero]
  · rw [(sLocalTrace_complex_place w (InfinitePlace.not_isReal_iff_isComplex.mp hw) _ h0).2]
    change _ * (∫ u : w.Completionˣ, (b.val u - a.val u) * _ / _ ∂_) = 0
    simp_rw [hb, hk, mul_zero]

/-- Self-dual Fourier inversion gives every character moment of the local transform. -/
private theorem selfDual_fourier_moments {K : Type*} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (ψ : K → Circle)
    (hd : IsTamagawaSelfDual μ ψ) (s : SchwartzBruhat (Multiplicative K)) :
    let g := tamagawaFourier μ ψ (fun x ↦ s (Multiplicative.ofAdd x))
    Integrable g μ ∧ ∀ t : K, (∫ x, g x * (ψ (x * t) : ℂ) ∂μ) = s (Multiplicative.ofAdd t) := by
  let G := Multiplicative K
  let : T2Space G := inferInstanceAs (T2Space K)
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace K)
  let : BorelSpace G := inferInstanceAs (BorelSpace K)
  let ν : Measure G := μ
  let hH := (inferInstance : μ.IsAddHaarMeasure)
  let : ν.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hH.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hH.toIsOpenPosMeasure
      map_mul_left_eq_self := fun y ↦ hH.map_add_left_eq_self y.toAdd }
  let : ν.Regular := (inferInstance : μ.Regular)
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨e, he, hP⟩ := hd
  let m := e.toHomeomorph.toMeasurableEquiv
  let ρ := ν.map m
  let : ρ.IsHaarMeasure := hP.1
  let : ρ.Regular := hP.2.1
  let g := tamagawaFourier μ ψ (fun x ↦ s (Multiplicative.ofAdd x))
  have hFT (x : K) : g x = lcaFourier ν s (m (Multiplicative.ofAdd x)) :=
    tamagawaFourier_eq_lcaFourier _ _ _ x _ fun z ↦ (he x z).trans (congrArg ψ (mul_comm x z))
  obtain ⟨T, hT⟩ := schwartzBruhat_fourier_equiv ν
  have hi : Integrable (T s : PontryaginDual G → ℂ) ρ := SchwartzBruhat.integrable ρ (T s)
  have hi' := m.measurableEmbedding.integrable_map_iff.mp hi
  refine ⟨hi'.congr (ae_of_all _ fun x ↦ ((hT s).2 (m x)).trans (hFT x.toAdd).symm), fun t ↦ ?_⟩
  have hinv := schwartzBruhat_fourier_inversion ν _ hP s (Multiplicative.ofAdd t)
  rw [show (⇑e : G → PontryaginDual G) = m from rfl, integral_map_equiv] at hinv
  refine Eq.trans ?_ hinv.symm
  exact integral_congr_ae (ae_of_all _ fun x ↦ congrArg₂ (· * ·) (hFT x) (congrArg (fun z : Circle ↦ (z : ℂ)) (he x t).symm))

/-- The character moments identify the integrable marginal almost everywhere. -/
private theorem eq_marginal_of_moments {X K : Type*} [MeasurableSpace X] [CommRing K]
    [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K] {μ : Measure X} (ν : Measure K)
    [ν.IsAddHaarMeasure] [ν.Regular] (ψ : K → Circle) (hd : IsTamagawaSelfDual ν ψ)
    (p : X → K) (hp : Measurable p) {G : X → ℂ} (hG : Integrable G μ)
    {a : K → ℂ} (ha : HasIntegralMarginal μ ν p G a)
    (s : SchwartzBruhat (Multiplicative K))
    (h : ∀ t, (∫ x, G x * (ψ (p x * t) : ℂ) ∂μ) = s (Multiplicative.ofAdd t)) :
    a =ᵐ[ν] tamagawaFourier ν ψ (fun x ↦ s (Multiplicative.ofAdd x)) := by
  let g := tamagawaFourier ν ψ (fun x ↦ s (Multiplicative.ofAdd x))
  obtain ⟨hi, hv⟩ := selfDual_fourier_moments ν ψ hd s
  obtain ⟨e, he, _⟩ := hd
  let c (x : K) : Multiplicative K →* Circle := (e (Multiplicative.ofAdd x)).toMonoidHom
  have hC (t : Multiplicative K) : Continuous (fun x : K ↦ c x t) := by
    have heq (x : K) : c x t = e t (Multiplicative.ofAdd x) :=
      (he x t.toAdd).trans ((congrArg ψ (mul_comm x t.toAdd)).trans (he t.toAdd x).symm)
    exact ((e t).continuous.comp continuous_ofAdd).congr (fun x ↦ (heq x).symm)
  have hinj : Injective c := fun x y h ↦ Multiplicative.ofAdd.injective
    (e.injective (PontryaginDual.ext fun t ↦ DFunLike.congr_fun h t))
  have hzero := ae_eq_zero_of_integral_mul_circle_eq_zero c hC hinj (ha.1.sub hi) (fun t ↦ ?_)
  · exact hzero.mono fun x hx ↦ sub_eq_zero.mp hx
  · let k := fun x : K ↦ (c x t : ℂ)
    have hkm : Measurable k := (continuous_subtype_val.comp (hC t)).measurable
    have hk (x : K) : ‖k x‖ ≤ 1 := (Circle.norm_coe _).le
    have ha' := ha.2 k (hG.mul_bdd (hkm.comp hp).aestronglyMeasurable (ae_of_all _ fun x ↦ hk _))
    change (∫ x, (a x - g x) * k x ∂ν) = 0
    simp_rw [sub_mul]
    rw [integral_sub ha'.1 (hi.mul_bdd hkm.aestronglyMeasurable (ae_of_all _ hk)), ← ha'.2]
    have hfun : k = fun x ↦ (ψ (x * t.toAdd) : ℂ) := funext fun x ↦ congrArg (fun z : Circle ↦ (z : ℂ)) (he x t.toAdd)
    rw [hfun, h, hv, sub_self]

/-- Once the restrictions to an axis stabilize, all the weighted pairings of its Fourier marginal
stabilize. -/
private theorem hasSum_fourier_axis {H X K : Type*} [MeasurableSpace X] [CommRing K]
    [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K] {μ : Measure X} (ν : Measure K)
    [ν.IsAddHaarMeasure] [ν.Regular] (ψ : K → Circle) (hd : IsTamagawaSelfDual ν ψ)
    (p : X → K) (hp : Measurable p) (L : K → ℂ)
    (G : H → X → ℂ) (gint : ∀ ξ, Integrable (G ξ) μ)
    (wint : ∀ ξ, Integrable (fun x ↦ G ξ x * L (p x)) μ)
    (hm : ∀ g, Integrable g μ → ∃ a, HasIntegralMarginal μ ν p g a)
    (s : SchwartzBruhat (Multiplicative K))
    (hs : ∀ᶠ D : Finset H in atTop, ∀ t : K,
      (∑ ξ ∈ D, ∫ x, G ξ x * (ψ (p x * t) : ℂ) ∂μ) = s (Multiplicative.ofAdd t)) :
    HasSum (fun ξ ↦ ∫ x, G ξ x * L (p x) ∂μ)
      (∫ y, tamagawaFourier ν ψ (fun x ↦ s (Multiplicative.ofAdd x)) y * L y ∂ν) := by
  classical
  apply tendsto_const_nhds.congr'
  filter_upwards [hs] with D hD
  let b := fun x ↦ ∑ ξ ∈ D, G ξ x
  have hb : Integrable b μ := integrable_finsetSum _ fun ξ _ ↦ gint ξ
  obtain ⟨a, ha⟩ := hm b hb
  have bmul (k : K → ℂ) : (fun x ↦ b x * k (p x)) =
      fun x ↦ ∑ ξ ∈ D, G ξ x * k (p x) := by funext x; exact Finset.sum_mul _ _ _
  have hψ (t : K) : Continuous (fun x ↦ ψ (x * t)) := by
    obtain ⟨e, he, -⟩ := hd
    exact ((e (Multiplicative.ofAdd t)).continuous.comp continuous_ofAdd).congr fun x ↦
      (he t x).trans (congrArg ψ (mul_comm t x))
  have hEq := eq_marginal_of_moments ν ψ hd p hp hb ha s (fun t ↦ ?_)
  · obtain ⟨_, hv⟩ := ha.2 L (bmul L ▸ integrable_finsetSum D fun ξ _ ↦ wint ξ)
    rw [bmul, integral_finsetSum _ fun ξ _ ↦ wint ξ] at hv
    exact (integral_congr_ae (hEq.mono fun x hx ↦ congrArg (· * L x) hx)).symm.trans hv.symm
  · rw [bmul (fun y ↦ (ψ (y * t) : ℂ)), integral_finsetSum]
    · exact hD t
    · intro ξ _
      exact (gint ξ).mul_bdd ((continuous_subtype_val.comp (hψ t)).measurable.comp hp).aestronglyMeasurable
        (ae_of_all _ fun x ↦ (Circle.norm_coe _).le)

/-- The periodization on one additive axis is the weighted translate of the inverse local test. A
single finite set of translates works on the entire axis. -/
private theorem sLocalTrace_axis_test {K : Type*} [NormedField K] [LocallyCompactSpace Kˣ]
    (i : Kˣ →ₜ* Iₛ) (j : K → Aₛ) (d : ℕ) (hd : d ≠ 0) [ProperSpace K]
    (hi : ∀ u, sIdeleNorm F S (i u) = (Units.map nnNormHom.toMonoidHom u) ^ d)
    (hj : ∀ u : Kˣ, (1 : Aₛ) + j (u.val - 1) = (i u).val)
    (hz : (1 : Aₛ) + j (-1) ∉ range (Units.val : Iₛ → Aₛ))
    (f : BruhatCompactSupport Iₛ) (a : BruhatCompactSupport Kˣ)
    (hlift : ∀ u : Kˣ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * i u)) (a.val u))
    (s : SchwartzBruhat (Multiplicative K))
    (hs : ∀ t, s (Multiplicative.ofAdd t) =
      Function.extend Units.val (fun u : Kˣ ↦ a.val u⁻¹) (fun _ ↦ 0) (1 + t) /
        (Real.sqrt (‖1 + t‖ ^ d) : ℂ)) :
    ∀ᶠ D : Finset Hₛ in atTop, ∀ t : K, ∑ ξ ∈ D, sLocalTraceEta f ξ (j t) =
      s (Multiplicative.ofAdd t) := by
  classical
  let : DiscreteTopology Hₛ := discreteTopology_sProjectedDiagonal
  let n : Iₛ →ₜ* ℝ≥0ˣ := ⟨sIdeleNorm F S, sLocalTrace_sIdeleNorm_continuous⟩
  have hn (ξ : Hₛ) : n ξ.val = 1 := by
    obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp ξ.property
    exact he ▸ (sIdeleNorm_spec F S).2 hγ
  have hproper : IsProperMap (n ∘ i) := by
    have he : n ∘ i = ⇑((Units.map nnNormHom.toMonoidHom) ^ d : Kˣ →* ℝ≥0ˣ) := funext hi
    rw [he]
    exact isProperMap_units_nnNorm_pow d hd
  have hfin := finite_translates_on_local_group Hₛ isClosed_sProjectedDiagonal n i hproper
    hn (tsupport f.val) f.property.2
  filter_upwards [eventually_ge_atTop hfin.toFinset] with D hD
  intro t
  by_cases ht : 1 + t = 0
  · have ht' : t = -1 := by linear_combination ht
    subst t
    rw [hs]
    simp only [add_neg_cancel, norm_zero, zero_pow hd, Real.sqrt_zero, Complex.ofReal_zero, div_zero]
    exact Finset.sum_eq_zero fun ξ _ ↦ Function.extend_apply' _ _ _ hz
  · let u := Units.mk0 (1 + t) ht
    have hu : u.val - 1 = t := by change 1 + t - 1 = t; abel
    have hu' : 1 + j t = (i u).val := hu ▸ hj u
    have hN (ξ : Hₛ) : normS(ξ.val⁻¹ * i u) = ‖u.val‖ ^ d := by
      simp only [map_mul, map_inv, show sIdeleNorm F S ξ.val = 1 from hn ξ, inv_one,
        one_mul, hi, Units.val_pow_eq_pow_val, NNReal.coe_pow]
      rfl
    have hη (ξ : Hₛ) : sLocalTraceEta f ξ (j t) =
        f.val (ξ.val * i u⁻¹) / (Real.sqrt (‖u.val‖ ^ d) : ℂ) := by
      rw [sLocalTraceEta, hu', Units.val_injective.extend_apply, hN, mul_inv_rev, inv_inv, map_inv, mul_comm]
    have hf0 (ξ : Hₛ) (hξ : ξ ∉ D) : f.val (ξ.val * i u⁻¹) = 0 := by
      by_contra hne
      exact hξ (hD (hfin.mem_toFinset.mpr ⟨u⁻¹, subset_tsupport _ hne⟩))
    have he := (hasSum_sum_of_ne_finset_zero hf0).unique (hlift u⁻¹)
    simp_rw [hη]
    rw [← Finset.sum_div, he, hs]
    change _ = Function.extend Units.val _ _ u.val / _
    rw [Units.val_injective.extend_apply]
    rfl

/-- The archimedean unit inclusion in the S-ideles agrees with the global inclusion and the local
norm. -/
private theorem sLocalTrace_arch_axis (w : InfinitePlace F) :
    ∃ i : w.Completionˣ →ₜ* Iₛ,
      (∀ u, classAtS(i u) = archClass(w) u) ∧
      (∀ u, sIdeleNorm F S (i u) = (Units.map nnNormHom.toMonoidHom u) ^ w.mult) ∧
      (∀ u : w.Completionˣ, (1 : Aₛ) + ((Pi.single w (u.val - 1), 0) : Aₛ) = (i u).val) := by
  classical
  let h : w.Completion →* Aₛ := (MonoidHom.mulSingle (fun q : InfinitePlace F ↦ q.Completion) w).prod 1
  let i : w.Completionˣ →ₜ* Iₛ := ⟨Units.map h,
    ((continuous_mulSingle (A := fun q : InfinitePlace F ↦ q.Completion) w).prodMk
      continuous_const : Continuous h).units_map h⟩
  have hi (u : w.Completionˣ) : sIdeleInsertion F S (i u) = IdeleGroup.ofCompletion (𝓞 F) F w u := by
    apply Units.ext
    obtain ⟨ha, hin, hout⟩ := sIdeleInsertion_apply F S (i u)
    refine Prod.ext ha (Subtype.ext (funext fun v ↦ ?_))
    by_cases hv : v ∈ S
    · exact hin ⟨v, hv⟩
    · exact hout v hv
  refine ⟨i, fun u ↦ congrArg QuotientGroup.mk (hi u), fun u ↦ ?_, fun u ↦ ?_⟩
  · rw [← ideleNorm_sIdeleInsertion, hi]
    exact ideleClassNorm_ofCompletion F w u
  · refine Prod.ext (funext fun q ↦ ?_) (show (1 : (v : S) → v.val.adicCompletion F) + 0 = 1 from add_zero _)
    change 1 + Pi.single w (u.val - 1) q = Pi.mulSingle (M := fun q : InfinitePlace F ↦ q.Completion) w u.val q
    by_cases hq : q = w
    · subst q; simp
    · simp [Pi.single_eq_of_ne hq, Pi.mulSingle_eq_of_ne hq]

/-- The finite unit inclusion in the S-ideles agrees with the global inclusion and the local norm.
-/
private theorem sLocalTrace_fin_axis (v : S) :
    ∃ i : (v.val.adicCompletion F)ˣ →ₜ* Iₛ,
      (∀ u, classAtS(i u) = finiteClass(v.val) u) ∧
      (∀ u, sIdeleNorm F S (i u) = (Units.map nnNormHom.toMonoidHom u) ^ 1) ∧
      (∀ u : (v.val.adicCompletion F)ˣ, (1 : Aₛ) + ((0, Pi.single v (u.val - 1)) : Aₛ) = (i u).val) := by
  classical
  let h : (v.val.adicCompletion F) →* Aₛ := (1 : _ →* InfiniteAdeleRing F).prod
    (MonoidHom.mulSingle (fun q : S ↦ q.val.adicCompletion F) v)
  let i : (v.val.adicCompletion F)ˣ →ₜ* Iₛ := ⟨Units.map h,
    (continuous_const.prodMk (continuous_mulSingle (A := fun q : S ↦ q.val.adicCompletion F) v) :
      Continuous h).units_map h⟩
  have hi (u : (v.val.adicCompletion F)ˣ) :
      sIdeleInsertion F S (i u) = IdeleGroup.ofAdicCompletion (𝓞 F) F v.val u := by
    apply Units.ext
    obtain ⟨ha, hin, hout⟩ := sIdeleInsertion_apply F S (i u)
    refine Prod.ext ha (Subtype.ext (funext fun q ↦ ?_))
    change _ = RestrictedProduct.mulSingle _ v.val u.val q
    by_cases hq : q ∈ S
    · refine (hin ⟨q, hq⟩).trans ?_
      change Pi.mulSingle (M := fun q : S ↦ q.val.adicCompletion F) v u.val ⟨q, hq⟩ = _
      by_cases he : (⟨q, hq⟩ : S) = v
      · obtain rfl : q = v.val := congrArg Subtype.val he
        rw [Pi.mulSingle_eq_same, RestrictedProduct.mulSingle_eq_same]
      · have hne : q ≠ v.val := fun hh ↦ he (Subtype.ext hh)
        rw [Pi.mulSingle_eq_of_ne he, RestrictedProduct.mulSingle_eq_of_ne _ _ hne]
    · have hne : q ≠ v.val := fun hh ↦ hq (hh.symm ▸ v.property)
      exact (hout q hq).trans (RestrictedProduct.mulSingle_eq_of_ne _ _ hne).symm
  refine ⟨i, fun u ↦ congrArg QuotientGroup.mk (hi u), fun u ↦ ?_, fun u ↦ ?_⟩
  · rw [← ideleNorm_sIdeleInsertion, hi, pow_one]
    exact ideleClassNorm_ofAdicCompletion F v.val u
  · refine Prod.ext (show (1 : InfiniteAdeleRing F) + 0 = 1 from add_zero _) (funext fun q ↦ ?_)
    change 1 + Pi.single (M := fun q : S ↦ q.val.adicCompletion F) v (u.val - 1) q = Pi.mulSingle (M := fun q : S ↦ q.val.adicCompletion F) v u.val q
    by_cases hq : q = v
    · subst q; simp
    · simp [Pi.single_eq_of_ne hq, Pi.mulSingle_eq_of_ne hq]

/-- The Schwartz product bound remains integrable with a logarithmic weight on any single
coordinate. -/
private theorem sLocalTrace_coordinate_log_integrable (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    (∀ w : InfinitePlace F, Integrable (fun x : Aₛ ↦ fourierₛ (sLocalTraceEta f ξ) x *
      (Real.log (‖x.1 w‖ ^ w.mult) : ℂ)) νₛ) ∧
    ∀ v : S, Integrable (fun x : Aₛ ↦ fourierₛ (sLocalTraceEta f ξ) x *
      (Real.log ‖x.2 v‖ : ℂ)) νₛ := by
  classical
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  obtain ⟨Φ, R, hΦ0, hΦi, hΦl, hbd⟩ := sLocalTrace_fourier_product_bound f ξ
  let g := fourierₛ (sLocalTraceEta f ξ)
  obtain ⟨η, hη⟩ := SLocalTraceEta.eta_test f ξ
  have hgc : Continuous g := by
    change Continuous (fourierₛ (sLocalTraceEta f ξ))
    rw [← funext hη]
    exact (schwartzBruhat_continuous (sAdeleSchwartzFourier η)).comp continuous_ofAdd
  let ind (v : S) : v.val.adicCompletion F → ℝ :=
    {b : v.val.adicCompletion F | ‖b‖ ≤ R}.indicator (fun _ ↦ (1 : ℝ))
  have hballm (v : S) : MeasurableSet {b : v.val.adicCompletion F | ‖b‖ ≤ R} :=
    measurableSet_le continuous_norm.measurable measurable_const
  have hball (v : S) : finiteLocalAdditiveTamagawaMeasure F v.val
      {b : v.val.adicCompletion F | ‖b‖ ≤ R} < ⊤ := by
    have : {b : v.val.adicCompletion F | ‖b‖ ≤ R} = Metric.closedBall 0 R := by
      ext b; simp
    rw [this]
    exact (isCompact_closedBall 0 R).measure_lt_top
  have hind (v : S) : Integrable (ind v) (finiteLocalAdditiveTamagawaMeasure F v.val) :=
    (integrable_indicator_iff (hballm v)).mpr (integrableOn_const (hball v).ne)
  -- The weights at the finite places.
  let fin (u : S) (v : S) : v.val.adicCompletion F → ℝ :=
    fun b ↦ ind v b * (if v = u then |Real.log ‖b‖| else 1)
  have hfin (u v : S) : Integrable (fin u v) (finiteLocalAdditiveTamagawaMeasure F v.val) := by
    by_cases h : v = u
    · simp only [fin, h, ↓reduceIte]
      subst h
      have := (finiteLog_abs_integrableOn_closedBall v.val R).integrable_indicator (hballm v)
      refine this.congr (ae_of_all _ fun b ↦ ?_)
      by_cases hb : b ∈ {b : v.val.adicCompletion F | ‖b‖ ≤ R}
      · simp [ind, indicator_of_mem hb]
      · simp [ind, indicator_of_notMem hb]
    · simp only [fin, h, ↓reduceIte, mul_one]
      exact hind v
  let P : ((v : S) → v.val.adicCompletion F) → ℝ := fun b ↦ ∏ v, ind v (b v)
  have hP : Integrable P (Measure.pi fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val) :=
    Integrable.fintype_prod_dep hind
  have hQ (u : S) : Integrable (fun b : (v : S) → v.val.adicCompletion F ↦ ∏ v, fin u v (b v))
      (Measure.pi fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val) :=
    Integrable.fintype_prod_dep (hfin u)
  have hQeq (u : S) (b : (v : S) → v.val.adicCompletion F) :
      ∏ v, fin u v (b v) = P b * |Real.log ‖b u‖| := by
    simp only [fin, Finset.prod_mul_distrib, P]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ u]
    simp
  constructor
  · intro w
    have hbw := ((hΦl w).mul_prod hP).const_mul (w.mult : ℝ)
    refine hbw.mono' (hgc.measurable.mul (Complex.measurable_ofReal.comp
      ((measurable_norm.comp ((measurable_pi_apply w).comp measurable_fst)).pow_const _).log)).aestronglyMeasurable ?_
    refine ae_of_all _ fun x ↦ ?_
    change ‖g x * (Real.log (‖x.1 w‖ ^ w.mult) : ℂ)‖ ≤
      (w.mult : ℝ) * ((Φ x.1 * |Real.log ‖x.1 w‖|) * P x.2)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.log_pow, abs_mul, Nat.abs_cast]
    calc _ ≤ (Φ x.1 * P x.2) * ((w.mult : ℝ) * |Real.log ‖x.1 w‖|) :=
              mul_le_mul_of_nonneg_right (hbd x) (by positivity)
         _ = _ := by ring
  · intro v
    refine (hΦi.mul_prod (hQ v)).mono' (hgc.measurable.mul (Complex.measurable_ofReal.comp
      (measurable_norm.comp ((measurable_pi_apply v).comp measurable_snd)).log)).aestronglyMeasurable ?_
    refine ae_of_all _ fun x ↦ ?_
    change ‖g x * (Real.log ‖x.2 v‖ : ℂ)‖ ≤ Φ x.1 * ∏ j, fin v j (x.2 j)
    rw [hQeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hbd x) (abs_nonneg _)

private theorem sLocalTrace_fourier_moment (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (t : Aₛ) :
    (∫ x, fourierₛ (sLocalTraceEta f ξ) x * (ψₛ (x * t) : ℂ) ∂νₛ) = sLocalTraceEta f ξ t := by
  obtain ⟨s, hs⟩ := SLocalTraceEta.eta_test f ξ
  have h := sLocal_fourier_inversion s (-t)
  rw [neg_neg, hs] at h
  obtain ⟨e, he, _⟩ := sAdditiveTamagawaMeasure_selfDual F S
  have hp (x : Aₛ) : star (ψₛ (x * -t) : ℂ) = (ψₛ (x * t) : ℂ) := by
    rw [← he, ← he, ofAdd_neg, map_inv, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  change (∫ x, fourierₛ (fun y ↦ s (Multiplicative.ofAdd y)) x * star (ψₛ (x * -t) : ℂ) ∂νₛ) = _ at h
  simpa only [hs, hp] using h

private theorem sLocalTrace_local_hasSum {K : Type*} [NormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (p : Aₛ → K) (hp : Measurable p) (j : K → Aₛ)
    (i : Kˣ →ₜ* Iₛ) (d : ℕ) (hd : d ≠ 0)
    (hi : ∀ u, sIdeleNorm F S (i u) = (Units.map nnNormHom.toMonoidHom u) ^ d)
    (hj : ∀ u : Kˣ, (1 : Aₛ) + j (u.val - 1) = (i u).val)
    (hz : (1 : Aₛ) + j (-1) ∉ range (Units.val : Iₛ → Aₛ))
    (μ : Measure K) [μ.IsAddHaarMeasure] (ψ : K → Circle)
    (hμ : IsTamagawaSelfDual μ ψ) (hψ : ∀ x t, ψₛ (x * j t) = ψ (p x * t))
    (hm : ∀ g, Integrable g νₛ → ∃ a, HasIntegralMarginal νₛ μ p g a)
    (f : BruhatCompactSupport Iₛ) (a : BruhatCompactSupport Kˣ)
    (hlift : ∀ u : Kˣ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * i u)) (a.val u))
    (s : SchwartzBruhat (Multiplicative K))
    (hs : ∀ t, s (Multiplicative.ofAdd t) =
      Function.extend Units.val (fun u : Kˣ ↦ a.val u⁻¹) (fun _ ↦ 0) (1 + t) /
        (Real.sqrt (‖1 + t‖ ^ d) : ℂ))
    (L : K → ℂ)
    (hL : ∀ ξ : Hₛ, Integrable (fun x ↦ fourierₛ (sLocalTraceEta f ξ) x * L (p x)) νₛ) :
    HasSum (fun ξ : Hₛ ↦ ∫ x, fourierₛ (sLocalTraceEta f ξ) x * L (p x) ∂νₛ)
      (∫ y, tamagawaFourier μ ψ (fun x ↦ s (Multiplicative.ofAdd x)) y * L y ∂μ) := by
  apply hasSum_fourier_axis μ ψ hμ p hp L _ (sLocalTraceEta_fourier_integrable f) hL hm s
  filter_upwards [sLocalTrace_axis_test i j d hd hi hj hz f a hlift s hs] with D hD t
  simp only [← hψ, sLocalTrace_fourier_moment, hD]

local notation "A∞" => ((q : InfinitePlace F) → q.Completion)
local notation "A𝒻" => ((q : S) → q.val.adicCompletion F)

private theorem sLocalTrace_marginals (g : Aₛ → ℂ) (hg : Integrable g νₛ) :
    (∀ w : InfinitePlace F, ∃ a, HasIntegralMarginal νₛ (infiniteLocalAdditiveTamagawaMeasure F w)
      (fun x : Aₛ ↦ x.1 w) g a) ∧
    ∀ v : S, ∃ a, HasIntegralMarginal νₛ (finiteLocalAdditiveTamagawaMeasure F v.val)
      (fun x : Aₛ ↦ x.2 v) g a := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : SigmaFinite (infiniteLocalAdditiveTamagawaMeasure F w) :=
    sLocalTrace_infinite_sigmaFinite w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let μ := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)
  let ν := Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)
  change Integrable g (μ.prod ν) at hg
  constructor
  · intro w
    have h := hasIntegralMarginal_fst (μ := μ) (ν := ν) hg
    obtain ⟨_, ha⟩ := hasIntegralMarginal_pi _ w h.1
    exact ⟨_, h.comp ha⟩
  · intro v
    have h := hasIntegralMarginal_equiv (μ := μ.prod ν) (ν := ν.prod μ) MeasurableEquiv.prodComm
      Measure.measurePreserving_swap hg
    have h' := hasIntegralMarginal_fst h.1
    obtain ⟨_, ha⟩ := hasIntegralMarginal_pi _ v h'.1
    exact ⟨_, (h.comp h').comp ha⟩

private theorem sLocalTrace_arch_single (w : InfinitePlace F) (t : w.Completion) :
    ψₛ ((Pi.single w t, 0) : Aₛ) = adeleStandardCharacter F (Pi.single w t, 0) := by
  classical
  let A (q : InfinitePlace F) := adeleStandardCharacter F
    (Pi.single q (Pi.single (M := fun j : InfinitePlace F ↦ j.Completion) w t q), 0)
  have hA : ∏ q, A q = A w := Finset.prod_eq_single w
    (fun q _ hq ↦ by
      change adeleStandardCharacter F (Pi.single q (Pi.single w t q), 0) = 1
      rw [Pi.single_eq_of_ne hq, Pi.single_zero]
      exact adeleStandardCharacter_zero F) (by simp)
  have hB : (∏ v : S, finiteLocalStandardCharacter F v.val 0) = 1 :=
    Finset.prod_eq_one fun v _ ↦ finiteLocalStandardCharacter_zero F v.val
  change (∏ q, A q) * (∏ v : S, finiteLocalStandardCharacter F v.val 0) = _
  rw [hA, hB, mul_one]
  dsimp only [A]
  rw [Pi.single_eq_same]

private theorem sLocalTrace_arch_character (w : InfinitePlace F) (x : Aₛ) (t : w.Completion) :
    ψₛ (x * ((Pi.single w t, 0) : Aₛ)) = adeleStandardCharacter F (Pi.single w (x.1 w * t), 0) := by
  have h : x * ((Pi.single w t, 0) : Aₛ) = ((Pi.single w (x.1 w * t), 0) : Aₛ) :=
    Prod.ext (Pi.single_mul_right (f := (x.1 : A∞)) t).symm (mul_zero x.2)
  exact (congrArg ψₛ h).trans (sLocalTrace_arch_single w _)

private theorem sLocalTrace_fin_character (v : S) (x : Aₛ) (t : v.val.adicCompletion F) :
    ψₛ (x * ((0, Pi.single v t) : Aₛ)) = finiteLocalStandardCharacter F v.val (x.2 v * t) := by
  have h : x * ((0, Pi.single v t) : Aₛ) = ((0, Pi.single v (x.2 v * t)) : Aₛ) :=
    Prod.ext (mul_zero x.1) (Pi.single_mul_right (f := x.2) t).symm
  exact (congrArg ψₛ h).trans (sAdeleStandardCharacter_single_finite F S v _)

private theorem sLocalTrace_arch_hasSum (φ : BruhatCompactSupport C𝔽) (f : BruhatCompactSupport Iₛ)
    (hlift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (w : InfinitePlace F) (a : BruhatCompactSupport w.Completionˣ)
    (ha : ∀ u, a.val u = φ.val (archClass(w) u)) :
    HasSum (fun ξ : Hₛ ↦ -∫ x, fourierₛ (sLocalTraceEta f ξ) x *
      (Real.log (‖x.1 w‖ ^ w.mult) : ℂ) ∂νₛ) (infiniteConnesWeilPrincipalValue w a) := by
  classical
  have he := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : ProperSpace w.Completion :=
    LipschitzWith.properSpace he.isClosedEmbedding.isProperMap he.lipschitzWith
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  obtain ⟨i, hc, hi, hj⟩ := sLocalTrace_arch_axis (S := S) w
  obtain ⟨b, hb⟩ := inv_bruhat_test a
  let s := (exists_infiniteWeilTestMap w).choose b
  let j := fun t : w.Completion ↦ ((Pi.single w t, 0) : Aₛ)
  have hz : (1 : Aₛ) + j (-1) ∉ range (Units.val : Iₛ → Aₛ) := by
    rintro ⟨u, hu⟩
    have hh := congrArg (fun x : Aₛ ↦ x.1 w) u.mul_inv
    change u.val.1 w * (u⁻¹).val.1 w = 1 at hh
    have h0 : u.val.1 w = 0 := by
      rw [hu]
      change 1 + Pi.single (M := fun q : InfinitePlace F ↦ q.Completion) w (-1) w = 0
      simp
    rw [h0, zero_mul] at hh
    exact zero_ne_one hh
  have h := sLocalTrace_local_hasSum (fun x : Aₛ ↦ x.1 w) ((measurable_pi_apply w).comp measurable_fst)
    j i w.mult w.mult_ne_zero hi hj hz _ _ (infiniteLocalAdditiveTamagawaMeasure_selfDual w)
    (sLocalTrace_arch_character w) (fun g hg ↦ (sLocalTrace_marginals g hg).1 w) f a
    (fun u ↦ by rw [ha, ← hc]; exact hlift (i u)) s (fun t ↦ ?_)
    (fun y ↦ (Real.log (‖y‖ ^ w.mult) : ℂ)) (fun ξ ↦ (sLocalTrace_coordinate_log_integrable f ξ).1 w)
  · rw [← infinitePV_inv w a b hb]
    have hp := ((exists_infiniteConnesPrincipalValue w).choose_spec s).2
    change infiniteConnesWeilPrincipalValue w b = _ at hp
    rw [hp]
    simpa only [mul_comm] using h.neg
  · rw [← funext hb]
    exact (exists_infiniteWeilTestMap w).choose_spec b t

private theorem sLocalTrace_fin_hasSum (φ : BruhatCompactSupport C𝔽) (f : BruhatCompactSupport Iₛ)
    (hlift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (v : S) (a : BruhatCompactSupport (v.val.adicCompletion F)ˣ)
    (ha : ∀ u, a.val u = φ.val (finiteClass(v.val) u)) :
    HasSum (fun ξ : Hₛ ↦ -∫ x, fourierₛ (sLocalTraceEta f ξ) x * (Real.log ‖x.2 v‖ : ℂ) ∂νₛ)
      (((Real.log (v.val.asIdeal.absNorm : ℝ) / finiteVolume(v.val) : ℝ) : ℂ) *
        finiteConnesWeilPrincipalValue v.val 1 a) := by
  classical
  let : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let : MeasurableSpace (v.val.adicCompletion F) := borel _
  let : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  obtain ⟨i, hc, hi, hj⟩ := sLocalTrace_fin_axis v
  obtain ⟨b, hb⟩ := inv_bruhat_test a
  let s := (exists_finiteWeilTestMap v.val).choose b
  let j := fun t : v.val.adicCompletion F ↦ ((0, Pi.single v t) : Aₛ)
  have hz : (1 : Aₛ) + j (-1) ∉ range (Units.val : Iₛ → Aₛ) := by
    rintro ⟨u, hu⟩
    have hh := congrArg (fun x : Aₛ ↦ x.2 v) u.mul_inv
    change u.val.2 v * (u⁻¹).val.2 v = 1 at hh
    have h0 : u.val.2 v = 0 := by
      rw [hu]
      change 1 + Pi.single (M := fun q : S ↦ q.val.adicCompletion F) v (-1) v = 0
      simp
    rw [h0, zero_mul] at hh
    exact zero_ne_one hh
  have h := sLocalTrace_local_hasSum (fun x : Aₛ ↦ x.2 v) ((measurable_pi_apply v).comp measurable_snd)
    j i 1 one_ne_zero hi hj hz _ _ (finiteLocalAdditiveTamagawaMeasure_selfDual F v.val)
    (sLocalTrace_fin_character v) (fun g hg ↦ (sLocalTrace_marginals g hg).2 v) f a
    (fun u ↦ by rw [ha, ← hc]; exact hlift (i u)) s (fun t ↦ ?_)
    (fun y ↦ (Real.log ‖y‖ : ℂ)) (fun ξ ↦ (sLocalTrace_coordinate_log_integrable f ξ).2 v)
  · rw [← finitePV_inv v.val a b hb]
    have hp := existsUnique_finiteWeilFourierDistribution_principalValue v.val s
    change finiteConnesWeilPrincipalValue v.val 1 b = _ at hp
    rw [hp]
    convert h.neg using 1
    have hq : Real.log (v.val.asIdeal.absNorm : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val)).ne'
    have hV : finiteVolume(v.val) ≠ 0 := by
      rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
      refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
      refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
      exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.val).trans' zero_lt_one
    simp_rw [Complex.ofReal_div, div_mul_eq_mul_div, integral_div]
    field_simp [Complex.ofReal_ne_zero.mpr hV, Complex.ofReal_ne_zero.mpr hq]
    simp only [mul_comm]
    exact congrArg Neg.neg (mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hq))
  · rw [pow_one, ← funext hb]
    exact (exists_finiteWeilTestMap v.val).choose_spec b t

/-- On the conull unit locus the logarithm of the product norm is the sum of the local logarithms.
-/
private theorem sLocalTrace_log_pairing_decompose (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    (-∫ x in range (Units.val : Iₛ → Aₛ), fourierₛ (sLocalTraceEta f ξ) x * (Real.log (modS(x)) : ℂ) ∂νₛ) =
    (∑ w : InfinitePlace F, -∫ x, fourierₛ (sLocalTraceEta f ξ) x *
      (Real.log (‖x.1 w‖ ^ w.mult) : ℂ) ∂νₛ) +
      ∑ v : S, -∫ x, fourierₛ (sLocalTraceEta f ξ) x * (Real.log ‖x.2 v‖ : ℂ) ∂νₛ := by
  classical
  obtain ⟨ha, hb⟩ := sLocalTrace_coordinate_log_integrable f ξ
  have hfull : ∀ᵐ x ∂νₛ, x ∈ range (Units.val : Iₛ → Aₛ) :=
    measure_eq_zero_iff_ae_notMem.mp sLocalTrace_nonunits_null |>.mono fun _ h ↦ not_not.mp h
  rw [Measure.restrict_eq_self_of_ae_mem hfull, Finset.sum_neg_distrib, Finset.sum_neg_distrib,
    ← neg_add, ← integral_finsetSum _ fun w _ ↦ ha w, ← integral_finsetSum _ fun v _ ↦ hb v,
    ← integral_add (integrable_finsetSum _ fun w _ ↦ ha w) (integrable_finsetSum _ fun v _ ↦ hb v)]
  congr 1
  apply integral_congr_ae
  filter_upwards [hfull] with x hx
  obtain ⟨u, rfl⟩ := hx
  have h : modS(u.val) = normS(u) := by simp [sIdeleNorm, Units.coe_prod]
  have hn : modS(u.val) ≠ 0 := h ▸ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hA := left_ne_zero_of_mul hn
  have hB := right_ne_zero_of_mul hn
  rw [Real.log_mul hA hB, Real.log_prod (Finset.prod_ne_zero_iff.mp hA),
    Real.log_prod (Finset.prod_ne_zero_iff.mp hB)]
  simp only [Complex.ofReal_add, Complex.ofReal_sum, mul_add, Finset.mul_sum]

end SharpMassConstant

/-- Paper: (12.4.1.25)–(12.4.1.28), p. 519. Constant term of the summed sharp masses.
For each S-unit ξ the constant term of the sharp mass is minus the pairing of the Fourier
transform of the translated test with the logarithm of the S-norm. Only finitely many ξ
contribute, and the sum is the sum of the local Connes–Weil principal values of the
restrictions of φ to the local unit groups.
Deviation: The printed proof does this in one display. The route is a partial Fourier
inversion per place, discreteness of the S-units after dropping one place, the lift
identity, and invariance of the principal values under u ↦ u⁻¹ (the last step on p. 519). -/
private theorem sLocalTraceSharpMass_asymptotic_const
    (φ : BruhatCompactSupport C𝔽)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (_hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (a : archTest) (b : finiteTest)
    (_ha : ∀ (w : InfinitePlace F) (u : w.Completionˣ),
      (a w).val u = φ.val (archClass(w) u))
    (_hb : ∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
      (b v).val u = φ.val (finiteClass(v.val) u)) :
    HasSum (fun ξ : Hₛ ↦ -∫ w in range (Units.val : Iₛ → Aₛ),
        fourierₛ (sLocalTraceEta f ξ) w * ((Real.log (modS(w)) : ℝ) : ℂ) ∂νₛ)
      principalValues(a, b) := by
  have h := (hasSum_sum (s := Finset.univ) fun w _ ↦
    sLocalTrace_arch_hasSum φ f _hLift w (a w) (_ha w)).add
    (hasSum_sum (s := Finset.univ) fun v _ ↦ sLocalTrace_fin_hasSum φ f _hLift v (b v) (_hb v))
  simpa only [sLocalTrace_log_pairing_decompose] using h

section SharpMassRemainder

attribute [local instance] instInfiniteCompletionMeasurableSpaceSec4 instFiniteCompletionMeasurableSec4b

/-- The sharp logarithmic width differs from the full logarithmic pairing by an upper tail. -/
private theorem logBand_remainder {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : X → ℂ) (m : X → ℝ) (hm : Measurable m) (hg : Integrable g μ)
    (hw : Integrable (fun x ↦ g x * (Real.log (m x) : ℂ)) μ) (R : ℝ) :
    (∫ x in {x | m x ≤ R}, g x * ((Real.log R - Real.log (m x) : ℝ) : ℂ) ∂μ) -
      ((∫ x, g x ∂μ) * (Real.log R : ℂ) - ∫ x, g x * (Real.log (m x) : ℂ) ∂μ) =
    ∫ x in {x | R < m x}, g x * ((Real.log (m x) - Real.log R : ℝ) : ℂ) ∂μ := by
  let k (x : X) := g x * (Real.log R : ℂ) - g x * (Real.log (m x) : ℂ)
  have hk : Integrable k μ := (hg.mul_const _).sub hw
  have he : (∫ x, k x ∂μ) =
      (∫ x, g x ∂μ) * (Real.log R : ℂ) - ∫ x, g x * (Real.log (m x) : ℂ) ∂μ := by
    rw [← integral_mul_const, ← integral_sub (hg.mul_const _) hw]
  have hc : {x | m x ≤ R}ᶜ = {x | R < m x} := by ext; simp
  have ha := integral_add_compl (s := {x | m x ≤ R}) (measurableSet_le hm measurable_const) hk
  rw [hc] at ha
  simp_rw [Complex.ofReal_sub, mul_sub]
  rw [← he]
  change (∫ x in {x | m x ≤ R}, k x ∂μ) - _ = _
  rw [← ha, sub_add_cancel_left]
  rw [← integral_neg]
  exact integral_congr_ae (ae_of_all _ fun x ↦ neg_sub _ _)

/-- For one integrable Fourier transform the upper tail tends to zero by domination. -/
private theorem logBand_remainder_tendsto {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : X → ℂ) (m : X → ℝ) (hm : Measurable m) (hg : Integrable g μ)
    (hw : Integrable (fun x ↦ g x * (Real.log (m x) : ℂ)) μ) :
    Tendsto (fun R : ℝ ↦ ∫ x in {x | R < m x},
      g x * ((Real.log (m x) - Real.log R : ℝ) : ℂ) ∂μ) atTop (𝓝 0) := by
  classical
  let t (R : ℝ) := {x : X | R < m x}
  have ht (R : ℝ) : MeasurableSet (t R) := measurableSet_lt measurable_const hm
  let k (R : ℝ) (x : X) := g x * ((Real.log (m x) - Real.log R : ℝ) : ℂ)
  have hk (R : ℝ) : Integrable (k R) μ := by
    simp only [k, Complex.ofReal_sub, mul_sub]
    exact hw.sub (hg.mul_const (Real.log R : ℂ))
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun R ↦ (t R).indicator (k R)) (f := fun _ ↦ (0 : ℂ))
    (fun x ↦ ‖g x * (Real.log (m x) : ℂ)‖)
    (.of_forall fun R ↦ ((hk R).indicator (ht R)).aestronglyMeasurable) ?_ hw.norm ?_
  · simpa only [integral_indicator (ht _), integral_zero] using h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    refine ae_of_all _ fun x ↦ ?_
    by_cases hx : x ∈ t R
    · change R < m x at hx
      have hlog := Real.log_nonneg hR
      have hle := Real.log_le_log (zero_lt_one.trans_le hR) hx.le
      rw [indicator_of_mem hx]
      simp only [k, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonneg (hlog.trans hle)]
      gcongr
      linarith
    · rw [indicator_of_notMem hx, norm_zero]
      exact norm_nonneg _
  · refine ae_of_all _ fun x ↦ tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (m x)] with R hR
    exact (indicator_of_notMem (not_lt.mpr hR : x ∉ t R) _).symm

private theorem sLocalTrace_remainder_eq (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (R : ℝ) :
    sLocalTraceSharpMass f ξ R - (volume₁ : ℂ) * (f.val ξ.val * (Real.log R : ℂ) +
      -∫ w in range (Units.val : Iₛ → Aₛ), fourierₛ (sLocalTraceEta f ξ) w *
        (Real.log (modS(w)) : ℂ) ∂νₛ) =
    (volume₁ : ℂ) * ∫ w in {w : Aₛ | R < modS(w)}, fourierₛ (sLocalTraceEta f ξ) w *
      ((Real.log (modS(w)) - Real.log R : ℝ) : ℂ) ∂νₛ := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let m : Aₛ → ℝ := fun w ↦ modS(w)
  have hm : Continuous m :=
    (continuous_finsetProd _ fun w _ ↦ (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  have hU : (νₛ).restrict (range (Units.val : Iₛ → Aₛ)) = νₛ :=
    Measure.restrict_eq_self_of_ae_mem
      (measure_eq_zero_iff_ae_notMem.mp sLocalTrace_nonunits_null |>.mono fun _ h ↦ not_not.mp h)
  have hv := sLocalTrace_fourier_integral_units f ξ
  rw [hU] at hv
  rw [sLocalTraceSharpMass, ← Measure.restrict_restrict
    (show MeasurableSet (band(R)) from (isClosed_le hm continuous_const).measurableSet), hU,
    ← hv, ← mul_sub, ← sub_eq_add_neg]
  exact congrArg ((volume₁ : ℂ) * ·) (logBand_remainder νₛ _ m hm.measurable
    (sLocalTraceEta_fourier_integrable f ξ) (sLocalTrace_fourier_log_integrable f ξ) R)

private theorem sLocalTrace_unit_norm (ξ : Hₛ) : sIdeleNorm F S ξ.val = 1 := by
  obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp ξ.property
  exact he ▸ (sIdeleNorm_spec F S).2 hγ

/-- Inverse dilation by an S-idele introduces its modulus in the additive integral. -/
private theorem sLocalTrace_integral_inv_dilate (u : Iₛ) (g : Aₛ → ℂ) :
    (∫ y, g ((u⁻¹).val * y) ∂νₛ) = (normS(u) : ℂ) * ∫ y, g y ∂νₛ := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  let U := range (Units.val : Iₛ → Aₛ)
  have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) :=
    IsOpenUnits.isOpenEmbedding_unitsVal (M := ((w : InfinitePlace F) → w.Completion) ×
      ((v : S) → v.val.adicCompletion F))
  have hU : MeasurableSet U := ho.isOpen_range.measurableSet
  have hf : (νₛ).restrict U = νₛ := Measure.restrict_eq_self_of_ae_mem
    (measure_eq_zero_iff_ae_notMem.mp sLocalTrace_nonunits_null |>.mono fun _ h ↦ not_not.mp h)
  have key (k : Aₛ → ℂ) : (∫ t : Iₛ, (normS(t) : ℂ) * k t.val ∂μₛ) =
      (sLocalTraceMeasureFactor S : ℂ) * ∫ y, k y ∂νₛ := by
    have h := sLocalTrace_integral_units (U.indicator k) (fun _ hy ↦ indicator_of_notMem hy _)
    rw [integral_indicator hU, hf] at h
    have hh (t : Iₛ) : U.indicator k t.val = k t.val := indicator_of_mem (mem_range_self t) _
    simpa only [hh] using h
  have hc : (sLocalTraceMeasureFactor S : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ ↦ ?_)
    have hv : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_ne_zero (by linarith) (sub_pos.mpr hv).ne'
  have hpt (t : Iₛ) : (normS(u * t) : ℂ) * g ((u⁻¹).val * (u * t).val) =
      (normS(u) : ℂ) * ((normS(t) : ℂ) * g t.val) := by
    have hn : normS(u * t) = normS(u) * normS(t) := by simp [map_mul]
    rw [hn, Units.val_mul, Units.inv_mul_cancel_left, Complex.ofReal_mul, mul_assoc]
  have h := key (fun y ↦ g ((u⁻¹).val * y))
  rw [← integral_mul_left_eq_self _ u] at h
  simp only [hpt, integral_const_mul] at h
  rw [key] at h
  apply mul_left_cancel₀ hc
  rw [← h]
  ring

private theorem sLocalTrace_integral_dilate_unit (ξ : Hₛ) (g : Aₛ → ℂ) :
    (∫ y, g (ξ.val.val * y) ∂νₛ) = ∫ y, g y ∂νₛ := by
  simpa [sLocalTrace_unit_norm] using sLocalTrace_integral_inv_dilate ξ.val⁻¹ g

private theorem sLocalTrace_eta_affine (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (z : Aₛ) :
    sLocalTraceEta f ξ (ξ.val.val * (1 + z) - 1) = sLocalTraceEta f 1 z := by
  have he : 1 + (ξ.val.val * (1 + z) - 1) = ξ.val.val * (1 + z) := by abel
  simp only [sLocalTraceEta, he]
  by_cases h : 1 + z ∈ range (Units.val : Iₛ → Aₛ)
  · obtain ⟨u, hu⟩ := h
    rw [← hu, ← Units.val_mul, Units.val_injective.extend_apply, Units.val_injective.extend_apply]
    simp
  · have h' : ξ.val.val * (1 + z) ∉ range (Units.val : Iₛ → Aₛ) := by
      rintro ⟨u, hu⟩
      exact h ⟨ξ.val⁻¹ * u, by simp [Units.val_mul, hu, ← mul_assoc]⟩
    rw [Function.extend_apply' _ _ _ h', Function.extend_apply' _ _ _ h]

private theorem sLocalTrace_fourier_affine (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (w : Aₛ) :
    fourierₛ (sLocalTraceEta f ξ) w =
      fourierₛ (sLocalTraceEta f 1) (ξ.val.val * w) * (ψₛ ((1 - ξ.val.val) * w) : ℂ) := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  obtain ⟨e, he, _⟩ := sAdditiveTamagawaMeasure_selfDual F S
  let χ := e (Multiplicative.ofAdd (1 : Aₛ))
  have hχ (x : Aₛ) : χ (Multiplicative.ofAdd x) = ψₛ x := by simpa using he 1 x
  let k := fun z : Aₛ ↦ sLocalTraceEta f ξ z * star (ψₛ (z * w) : ℂ)
  have h (z : Aₛ) : k (ξ.val.val * (1 + z) - 1) =
      (sLocalTraceEta f 1 z * star (ψₛ (z * (ξ.val.val * w)) : ℂ)) *
        (ψₛ ((1 - ξ.val.val) * w) : ℂ) := by
    dsimp only [k]
    rw [sLocalTrace_eta_affine, show (ξ.val.val * (1 + z) - 1) * w =
      z * (ξ.val.val * w) + -((1 - ξ.val.val) * w) by ring]
    simp only [← hχ, ofAdd_add, map_mul, Circle.coe_mul, star_mul', ofAdd_neg, map_inv,
      Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
    ring
  change (∫ z, k z ∂νₛ) = _
  rw [← integral_sub_right_eq_self k 1, ← sLocalTrace_integral_dilate_unit ξ,
    ← integral_add_left_eq_self _ (1 : Aₛ)]
  simp_rw [h]
  exact integral_mul_const _ _

local notation "A∞" => ((w : InfinitePlace F) → w.Completion)
local notation "A𝒻" => ((v : S) → v.val.adicCompletion F)
local notation "places" => InfinitePlace F ⊕ S
-- Use the sup norm on the product. The norm on InfiniteAdeleRing itself is the product modulus.
local notation "Eₛ" => A∞ × A𝒻

private def sLocalTrace_radii (x : Eₛ) : places → ℝ :=
  Sum.elim (fun w ↦ ‖x.1 w‖) (fun v ↦ ‖x.2 v‖)

private theorem sLocalTrace_radii_bound (x : Eₛ) : ‖sLocalTrace_radii x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x : Eₛ))).mpr
  rintro (w|v)
  · simpa [sLocalTrace_radii, Real.norm_eq_abs] using
      ((norm_le_pi_norm (x.1 : A∞) w).trans (norm_fst_le (x : A∞ × A𝒻)))
  · simpa [sLocalTrace_radii, Real.norm_eq_abs] using
      ((norm_le_pi_norm x.2 v).trans (norm_snd_le (x : A∞ × A𝒻)))

private theorem sLocalTrace_radii_lipschitz (x y : Eₛ) :
    ‖sLocalTrace_radii x - sLocalTrace_radii y‖ ≤ ‖x - y‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y : Eₛ))).mpr
  rintro (w|v)
  · exact (abs_norm_sub_norm_le _ _).trans
      ((norm_le_pi_norm ((x - y).1 : A∞) w).trans (norm_fst_le ((x - y) : A∞ × A𝒻)))
  · exact (abs_norm_sub_norm_le _ _).trans
      ((norm_le_pi_norm (x - y).2 v).trans (norm_snd_le ((x - y) : A∞ × A𝒻)))

/-- The product of the normalized local absolute values has a polynomial Lipschitz bound. -/
private theorem sLocalTrace_modulus_translation_bound :
    ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (x h : Eₛ), ‖h‖ ≤ 1 →
      modS(x) ≤ C * (1 + ‖x‖) ^ d ∧
      |modS(x + h) - modS(x)| ≤ C * (1 + ‖x‖) ^ d * ‖h‖ := by
  classical
  let P (z : places → ℝ) := (∏ w : InfinitePlace F, z (.inl w) ^ w.mult) *
    ∏ v : S, z (.inr v)
  let d := (∑ w : InfinitePlace F, w.mult) + Fintype.card S
  have hP (b : ℝ) (z : places → ℝ) : P (b • z) = b ^ d * P z := by
    simp only [P, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      ← Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, d, pow_add]
    ring
  have hC : ContDiff ℝ 1 P := by dsimp only [P]; fun_prop
  let K := Metric.closedBall (0 : places → ℝ) 1
  obtain ⟨B, hB⟩ := hC.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : places → ℝ) 1) (isCompact_closedBall _ _)
  have hP0 : P 0 = 0 := by
    have ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    change (∏ w : InfinitePlace F, (0 : ℝ) ^ w.mult) * _ = _
    simp [zero_pow InfinitePlace.mult_ne_zero]
  refine ⟨d, B, B.coe_nonneg, fun x h hh ↦ ?_⟩
  let b := 1 + ‖x‖
  have hb : 1 ≤ b := le_add_of_nonneg_right (norm_nonneg _)
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  let z := sLocalTrace_radii x
  let u := sLocalTrace_radii (x + h)
  have hz : ‖z‖ ≤ b := (sLocalTrace_radii_bound _).trans (by dsimp [b]; linarith)
  have hu : ‖u‖ ≤ b := (sLocalTrace_radii_bound _).trans
    ((norm_add_le _ _).trans (by dsimp [b]; linarith))
  have hm (q : places → ℝ) (hq : ‖q‖ ≤ b) : b⁻¹ • q ∈ K := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hb0.le),
      inv_mul_le_iff₀ hb0, mul_one]
    exact hq
  have hdiff (u z : places → ℝ) (hu : ‖u‖ ≤ b) (hz : ‖z‖ ≤ b) :
      |P u - P z| ≤ B * b ^ d * ‖u - z‖ := by
    have h := hB.dist_le_mul _ (hm u hu) _ (hm z hz)
    rw [Real.dist_eq, dist_eq_norm, ← smul_sub] at h
    simp only [hP, ← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hb0.le) _),
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hb0.le)] at h
    have hi : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb
    rw [inv_pow, inv_mul_le_iff₀ (pow_pos hb0 _)] at h
    calc _ ≤ _ := h
         _ ≤ B * b ^ d * ‖u - z‖ := by
           calc _ ≤ b ^ d * (B * (1 * ‖u - z‖)) := by gcongr
                _ = _ := by ring
  constructor
  · -- Compare with zero on the unit ball, before rescaling.
    have h' := hB.dist_le_mul _ (hm z hz) _ (hm 0 (by simpa using hb0.le))
    rw [smul_zero, hP0, Real.dist_eq, sub_zero, hP, abs_mul,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hb0.le) _), dist_zero_right, inv_pow,
      inv_mul_le_iff₀ (pow_pos hb0 _)] at h'
    change P z ≤ _
    refine (le_abs_self _).trans (h'.trans ?_)
    have hk := mem_closedBall_zero_iff.mp (hm z hz)
    calc _ ≤ b ^ d * (B * 1) := by gcongr
         _ = _ := by ring
  · exact (hdiff u z hu hz).trans (mul_le_mul_of_nonneg_left
      (by simpa [u, z] using sLocalTrace_radii_lipschitz (x + h) x) (by positivity))

private def sLocalTrace_log_cut (R a : ℝ) := Real.log (max R a) - Real.log R

private theorem sLocalTrace_log_cut_lipschitz {R : ℝ} (hR : 1 ≤ R) (a b : ℝ) :
    |sLocalTrace_log_cut R a - sLocalTrace_log_cut R b| ≤ |a - b| := by
  have h (a b : ℝ) (hab : a ≤ b) :
      sLocalTrace_log_cut R a ≤ sLocalTrace_log_cut R b ∧
      sLocalTrace_log_cut R b - sLocalTrace_log_cut R a ≤ b - a := by
    let A := max R a
    let B := max R b
    have hA : 1 ≤ A := hR.trans (le_max_left ..)
    have h0 : 0 < A := zero_lt_one.trans_le hA
    have hAB : A ≤ B := max_le_max_left R hab
    have hB : 0 < B := h0.trans_le hAB
    have hdiff : B - A ≤ b - a := by dsimp [A, B]; grind
    refine ⟨sub_le_sub_right (Real.log_le_log h0 hAB) _, ?_⟩
    change (Real.log B - _) - (Real.log A - _) ≤ _
    rw [sub_sub_sub_cancel_right, ← Real.log_div hB.ne' h0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hB h0)).trans ?_
    calc B / A - 1 = (B - A) / A := by field_simp
         _ ≤ B - A := div_le_self (sub_nonneg.mpr hAB) hA
         _ ≤ _ := hdiff
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr (h a b hab).1), abs_of_nonpos (sub_nonpos.mpr hab), neg_sub, neg_sub]
    exact (h a b hab).2
  · rw [abs_of_nonneg (sub_nonneg.mpr (h b a hba).1), abs_of_nonneg (sub_nonneg.mpr hba)]
    exact (h b a hba).2

private theorem sLocalTrace_log_cut_bound {R a : ℝ} (hR : 1 ≤ R) (ha : 0 ≤ a) :
    |sLocalTrace_log_cut R a| ≤ a := by
  simpa [sLocalTrace_log_cut, max_eq_left (zero_le_one.trans hR), abs_of_nonneg ha] using
    sLocalTrace_log_cut_lipschitz hR a 0

private theorem sLocalTrace_sqrt_difference (a b : ℂ) (u v : ℝ) (hu : 0 ≤ u)
    (h : ‖a - b‖ ≤ u * v) :
    ‖a - b‖ ≤ Real.sqrt u * Real.sqrt v * (Real.sqrt ‖a‖ + Real.sqrt ‖b‖) := by
  calc ‖a - b‖ = Real.sqrt ‖a - b‖ * Real.sqrt ‖a - b‖ := (Real.mul_self_sqrt (norm_nonneg _)).symm
       _ ≤ Real.sqrt (u * v) * Real.sqrt (‖a‖ + ‖b‖) := by gcongr; exact norm_sub_le _ _
       _ ≤ _ := by
         rw [Real.sqrt_mul hu]
         gcongr
         apply (Real.sqrt_le_iff).mpr
         refine ⟨by positivity, ?_⟩
         nlinarith [Real.sq_sqrt (norm_nonneg a), Real.sq_sqrt (norm_nonneg b),
           mul_nonneg (Real.sqrt_nonneg ‖a‖) (Real.sqrt_nonneg ‖b‖)]

private theorem sLocalTrace_fourier_lipschitz {E : Type*} [NormedCommRing E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (χ : Multiplicative E →ₜ* Circle) (f : E → ℂ) (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ C ≥ 0, ∀ x y : E, ‖tamagawaFourier μ (fun t ↦ χ (Multiplicative.ofAdd t)) f x -
      tamagawaFourier μ (fun t ↦ χ (Multiplicative.ofAdd t)) f y‖ ≤ C * ‖x - y‖ := by
  obtain ⟨K, hK, hχ⟩ := exists_circleCharacter_norm_sub_one_le χ
  let g (t : E) : ℂ := χ (Multiplicative.ofAdd t)
  have gc : Continuous g := continuous_subtype_val.comp (χ.continuous.comp continuous_ofAdd)
  have gnorm (t : E) : ‖g t‖ = 1 := Circle.norm_coe _
  have gsub (u v : E) : ‖g u - g v‖ ≤ K * ‖u - v‖ := by
    have hprod : g (u - v) * g v = g u := by
      change ((χ (Multiplicative.ofAdd (u - v)) * χ (Multiplicative.ofAdd v) : Circle) : ℂ) = _
      rw [← map_mul, ← ofAdd_add, sub_add_cancel]
    rw [← hprod, ← sub_one_mul, norm_mul, gnorm, mul_one]
    exact hχ _
  let k := fun t ↦ ‖f t‖ * ‖t‖
  have hk : Integrable k μ :=
    (hf.norm.mul continuous_norm).integrable_of_hasCompactSupport (hs.norm.mul_right)
  refine ⟨K * (∫ t, k t ∂μ), mul_nonneg hK.le (integral_nonneg fun _ ↦ by dsimp [k]; positivity),
    fun x y ↦ ?_⟩
  let F (x t : E) := f t * star (g (t * x))
  have hF (x : E) : Integrable (F x) μ :=
    (hf.mul ((gc.comp (continuous_id.mul continuous_const)).star)).integrable_of_hasCompactSupport hs.mul_right
  change ‖(∫ t, F x t ∂μ) - ∫ t, F y t ∂μ‖ ≤ _
  rw [← integral_sub (hF x) (hF y)]
  calc _ ≤ ∫ t, k t * (K * ‖x - y‖) ∂μ := by
          refine norm_integral_le_of_norm_le (hk.mul_const _) (ae_of_all _ fun t ↦ ?_)
          simp only [F, ← mul_sub, ← star_sub, norm_mul, norm_star]
          calc _ ≤ ‖f t‖ * (K * ‖t * (x - y)‖) := by
                    rw [mul_sub]
                    exact mul_le_mul_of_nonneg_left (gsub _ _) (norm_nonneg _)
               _ ≤ ‖f t‖ * (K * (‖t‖ * ‖x - y‖)) := by gcongr; exact norm_mul_le _ _
               _ = _ := by dsimp [k]; ring
       _ = _ := by rw [integral_mul_const]; ring

/-- Any polynomial moment of the absolute value or its square root is integrable for an
S - adelic Schwartz test. Only the finite coordinates require a support restriction. -/
private theorem sLocalTrace_weighted_moment (s : testₛ) (d : ℕ) :
    Integrable (fun x : Eₛ ↦ (1 + ‖x‖) ^ d *
      (Real.sqrt ‖testAt(s, x)‖ + ‖testAt(s, x)‖)) νₛ := by
  classical
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let : BorelSpace Eₛ := sAdeleRing_borelSpace
  let g (x : Eₛ) := testAt(s, x)
  obtain ⟨K, hK, hzero, hdec⟩ := sAdeleSchwartz_exists_decay_bound F S s
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  let M := 1 + |R|
  have hM : 1 ≤ M := le_add_of_nonneg_right (abs_nonneg _)
  have hr (k : ℕ) : ∃ B ≥ 0, ∀ x : Eₛ, ‖g x‖ * (1 + ‖x‖) ^ k ≤ B := by
    obtain ⟨b, hb, h₀⟩ := hdec 0
    obtain ⟨c, hc, hk⟩ := hdec k
    refine ⟨M ^ k * (2 ^ k * (b + c)), by positivity, fun x ↦ ?_⟩
    by_cases hx : x.2 ∈ K
    · let t := ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x.1‖
      have ht : 0 ≤ t := norm_nonneg _
      have h₁ : ‖x.1‖ ≤ t := (pi_norm_le_iff_of_nonneg ht).mpr (sLocalTrace_norm_le_mixed x.1)
      have h₂ : ‖x.2‖ ≤ |R| := (mem_closedBall_zero_iff.mp (hR hx)).trans (le_abs_self _)
      have hx' : 1 + ‖x‖ ≤ M * (1 + t) := by
        change 1 + max ‖x.1‖ ‖x.2‖ ≤ M * (1 + t)
        have hMt : t ≤ M * t := le_mul_of_one_le_left ht hM
        dsimp [M] at *
        rcases le_total ‖x.1‖ ‖x.2‖ with hh|hh
        · rw [max_eq_right hh]; nlinarith [abs_nonneg R]
        · rw [max_eq_left hh]; nlinarith [abs_nonneg R]
      have h0 := h₀ (x : Aₛ)
      simp only [pow_zero, mul_one] at h0
      have hp := hk (x : Aₛ)
      change ‖g x‖ * t ^ k ≤ c at hp
      calc _ ≤ ‖g x‖ * (M * (1 + t)) ^ k := by gcongr
           _ ≤ M ^ k * (‖g x‖ * (2 ^ k * (1 + t ^ k))) := by
             rw [mul_pow, ← mul_assoc, mul_comm ‖g x‖, mul_assoc]
             gcongr
             exact sLocalTrace_one_add_pow_le ht k
           _ = M ^ k * (2 ^ k * (‖g x‖ + ‖g x‖ * t ^ k)) := by ring
           _ ≤ _ := by gcongr
    · change ‖s (Multiplicative.ofAdd (x : Aₛ))‖ * _ ≤ _
      rw [hzero _ hx, norm_zero, zero_mul]
      positivity
  let k := 4 * Fintype.card (InfinitePlace F)
  obtain ⟨B, hB, hb⟩ := hr (d + k)
  obtain ⟨C, hC, hc⟩ := hr (2 * (d + k))
  let P (a : A∞) := ∏ w, ((1 + ‖a w‖) ^ 4)⁻¹
  let Q : A𝒻 → ℝ := K.indicator (fun _ ↦ 1)
  have hQ : Integrable Q (Measure.pi fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val) :=
    (integrable_indicator_iff hK.measurableSet).mpr (integrableOn_const hK.measure_ne_top)
  have hP := (sLocalTrace_infinite_weight_prod_integrable (F := F)).1
  have hg : Continuous g := (schwartzBruhat_continuous s).comp continuous_ofAdd
  refine ((hP.mul_prod hQ).const_mul (Real.sqrt C + B)).mono'
    (((continuous_const.add continuous_norm).pow _).mul
      ((Real.continuous_sqrt.comp hg.norm).add hg.norm)).aestronglyMeasurable ?_
  refine ae_of_all _ fun x ↦ ?_
  change ‖(1 + ‖x‖) ^ d * (Real.sqrt ‖g x‖ + ‖g x‖)‖ ≤ (Real.sqrt C + B) * (P x.1 * Q x.2)
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hx : x.2 ∈ K
  · rw [show Q x.2 = 1 from indicator_of_mem hx _, mul_one]
    dsimp only [P]
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ (Finset.prod_pos fun _ _ ↦ by positivity)]
    have hprod : (∏ w : InfinitePlace F, (1 + ‖x.1 w‖) ^ 4) ≤ (1 + ‖x‖) ^ k := by
      calc _ ≤ ∏ _w : InfinitePlace F, (1 + ‖x‖) ^ 4 := by
                 gcongr with w
                 exact (norm_le_pi_norm x.1 w).trans (norm_fst_le x)
           _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
    have hs : Real.sqrt ‖g x‖ * (1 + ‖x‖) ^ (d + k) ≤ Real.sqrt C := by
      have h := Real.sqrt_le_sqrt (hc x)
      rwa [Real.sqrt_mul (norm_nonneg _), mul_comm 2 _, pow_mul,
        Real.sqrt_sq (by positivity)] at h
    calc _ ≤ (1 + ‖x‖) ^ d * (Real.sqrt ‖g x‖ + ‖g x‖) * (1 + ‖x‖) ^ k := by gcongr
         _ = Real.sqrt ‖g x‖ * (1 + ‖x‖) ^ (d + k) + ‖g x‖ * (1 + ‖x‖) ^ (d + k) := by rw [pow_add]; ring
         _ ≤ _ := add_le_add hs (hb x)
  · have hz : g x = 0 := hzero _ hx
    simp [hz, Q, indicator_of_notMem hx]

/-- The L¹ translation difference of the cutoff transform is bounded by a constant times the
square root of the translation length, uniformly for all cutoffs R ≥ 1. -/
private theorem sLocalTrace_cut_translation {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddLeftInvariant]
    (m : E → ℝ) (hm : Continuous m) (hm0 : ∀ x, 0 ≤ m x) (d : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hmod : ∀ x h : E, ‖h‖ ≤ 1 → m x ≤ C * (1 + ‖x‖) ^ d ∧
      |m (x + h) - m x| ≤ C * (1 + ‖x‖) ^ d * ‖h‖)
    (g : E → ℂ) (hg : Continuous g) (K : ℝ) (hK : 0 ≤ K)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ K * ‖x - y‖)
    (hW : Integrable (fun x ↦ (1 + ‖x‖) ^ d * (Real.sqrt ‖g x‖ + ‖g x‖)) μ) :
    let k (R : ℝ) (x : E) := g x * (sLocalTrace_log_cut R (m x) : ℂ)
    ∃ A ≥ 0, ∀ R : ℝ, 1 ≤ R → Integrable (k R) μ ∧ (∫ x, ‖k R x‖ ∂μ) ≤ A ∧
      ∀ h : E, ‖h‖ ≤ 1 → (∫ x, ‖k R (x + h) - k R x‖ ∂μ) ≤ A * Real.sqrt ‖h‖ := by
  intro k
  let P (x : E) := (1 + ‖x‖) ^ d
  let W (x : E) := P x * (Real.sqrt ‖g x‖ + ‖g x‖)
  have hP (x : E) : 0 ≤ P x := by dsimp [P]; positivity
  have hw (x : E) : 0 ≤ W x := by dsimp [W]; positivity
  change Integrable W μ at hW
  have hwi : 0 ≤ ∫ x, W x ∂μ := integral_nonneg hw
  let B : ℝ := C * (1 + (2 : ℝ) ^ d) * (1 + Real.sqrt K)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h1 : Real.sqrt K * C ≤ B := by
    dsimp [B]
    nlinarith [Real.sqrt_nonneg K, mul_nonneg hC (by positivity : 0 ≤ (2 : ℝ) ^ d),
      mul_nonneg (mul_nonneg hC (by positivity : 0 ≤ (2 : ℝ) ^ d)) (Real.sqrt_nonneg K)]
  have h2 : Real.sqrt K * C * (2 : ℝ) ^ d ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg hC (Real.sqrt_nonneg K), mul_nonneg hC (by positivity : 0 ≤ (2 : ℝ) ^ d)]
  have h3 : C ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg hC (by positivity : 0 ≤ (2 : ℝ) ^ d),
      mul_nonneg (by positivity : 0 ≤ C * (1 + (2 : ℝ) ^ d)) (Real.sqrt_nonneg K)]
  have hw1 (x : E) : P x * ‖g x‖ ≤ W x := mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (Real.sqrt_nonneg _)) (hP x)
  have hw2 (x : E) : P x * Real.sqrt ‖g x‖ ≤ W x := mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (norm_nonneg _)) (hP x)
  refine ⟨(C + 4 * B) * (∫ x, W x ∂μ), by positivity, fun R hR ↦ ?_⟩
  let L (x : E) := sLocalTrace_log_cut R (m x)
  have hL (x : E) : |L x| ≤ C * P x :=
    (sLocalTrace_log_cut_bound hR (hm0 x)).trans (hmod x 0 (by simp)).1
  have hkc : Continuous (k R) := hg.mul (Complex.continuous_ofReal.comp
    (((continuous_const.max hm).log (fun x ↦ (zero_lt_one.trans_le (hR.trans (le_max_left _ _))).ne')).sub continuous_const))
  have hbd (x : E) : ‖k R x‖ ≤ C * W x := by
    change ‖g x * (L x : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ ‖g x‖ * (C * P x) := by gcongr; exact hL x
         _ = C * (P x * ‖g x‖) := by ring
         _ ≤ _ := by gcongr; exact hw1 x
  have hki := (hW.const_mul C).mono' hkc.aestronglyMeasurable (ae_of_all _ hbd)
  refine ⟨hki, ?_, fun h hh ↦ ?_⟩
  · calc _ ≤ ∫ x, C * W x ∂μ := integral_mono hki.norm (hW.const_mul C) hbd
         _ ≤ _ := by rw [integral_const_mul]; gcongr; linarith
  · let t := Real.sqrt ‖h‖
    have ht : 0 ≤ t := Real.sqrt_nonneg _
    have hh' : ‖h‖ ≤ t := by
      have := Real.sq_sqrt (norm_nonneg h)
      have := Real.sqrt_le_one.mpr hh
      nlinarith
    have hdiff (x : E) : ‖k R (x + h) - k R x‖ ≤ B * t * (W (x + h) + W x + W x) := by
      let y := x + h
      have hP' : P y ≤ (2 : ℝ) ^ d * P x := by
        change (1 + ‖y‖) ^ d ≤ 2 ^ d * (1 + ‖x‖) ^ d
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        dsimp [y]
        linarith [norm_add_le x h, norm_nonneg x]
      have hg' := sLocalTrace_sqrt_difference (g y) (g x) K ‖h‖ hK
        (by simpa [y] using hlip (x + h) x)
      have hΔ : |L y - L x| ≤ C * P x * t := (sLocalTrace_log_cut_lipschitz hR _ _).trans
        ((hmod x h hh).2.trans (mul_le_mul_of_nonneg_left hh' (mul_nonneg hC (hP _))))
      change ‖g y * (L y : ℂ) - g x * (L x : ℂ)‖ ≤ _
      have he : g y * (L y : ℂ) - g x * (L x : ℂ) =
          (g y - g x) * (L y : ℂ) + g x * ((L y - L x : ℝ) : ℂ) := by push_cast; ring
      rw [he]
      apply (norm_add_le _ _).trans
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc _ ≤ (Real.sqrt K * t * (Real.sqrt ‖g y‖ + Real.sqrt ‖g x‖)) * (C * P y) + ‖g x‖ * (C * P x * t) := by
                  gcongr
                  exact hL y
           _ = (Real.sqrt K * C) * t * (P y * Real.sqrt ‖g y‖) + Real.sqrt K * C * t * (P y * Real.sqrt ‖g x‖) +
               C * t * (P x * ‖g x‖) := by ring
           _ ≤ B * t * W y + (Real.sqrt K * C) * t * (((2 : ℝ) ^ d * P x) * Real.sqrt ‖g x‖) + B * t * W x := by
                 gcongr
                 · exact hw2 y
                 · exact hw1 x
           _ = B * t * W y + (Real.sqrt K * C * (2 : ℝ) ^ d) * t * (P x * Real.sqrt ‖g x‖) + B * t * W x := by ring
           _ ≤ B * t * W y + B * t * W x + B * t * W x := by gcongr; exact hw2 x
           _ = _ := by dsimp [y]; ring
    have hW' : Integrable (fun x ↦ W (x + h)) μ := (measurePreserving_add_right μ h).integrable_comp_of_integrable hW
    have hmaj := (((hW'.add hW).add hW).const_mul (B * t))
    have hi : Integrable (fun x ↦ k R (x + h) - k R x) μ :=
      ((measurePreserving_add_right μ h).integrable_comp_of_integrable hki).sub hki
    calc _ ≤ ∫ x, B * t * (W (x + h) + W x + W x) ∂μ := integral_mono hi.norm hmaj hdiff
         _ = B * t * ((∫ x, W x ∂μ) + (∫ x, W x ∂μ) + (∫ x, W x ∂μ)) := by
                 rw [integral_const_mul, integral_add (show Integrable (fun x ↦ W (x + h) + W x) μ from hW'.add hW) hW,
                   integral_add hW' hW, integral_add_right_eq_self]
         _ ≤ _ := by dsimp [t] at *; nlinarith [mul_nonneg (mul_nonneg hC hwi) ht,
                   mul_nonneg (mul_nonneg hB hwi) ht]

-- Properness and additivity of the S - logarithm, from Appendix A.2.4.
private theorem sLocalTrace_log_proper : IsProperMap (sIdeleLog F S) := by
  let L (v : S) (u : (v.val.adicCompletion F)ˣ) := Real.log ‖u.val‖
  have hL (v : S) : IsProperMap (L v) := by
    let := properSpace_adicCompletion (K := F) v.val
    have hn : IsProperMap (fun x : v.val.adicCompletion F ↦ ‖x‖) := by
      convert isProperMap_dist (0 : v.val.adicCompletion F) using 1
      exact funext fun x ↦ (dist_zero_left x).symm
    let radii (x : ℝ) := (Real.exp x, Real.exp (-x))
    refine isProperMap_of_comp_of_t2
      (Units.continuous_val.norm.log (fun u ↦ norm_ne_zero_iff.mpr u.ne_zero))
      (g := radii) (Real.continuous_exp.prodMk (Real.continuous_exp.comp continuous_neg)) ?_
    convert (hn.prodMap (hn.comp MulOpposite.opHomeomorph.symm.isProperMap)).comp
      (Units.isClosedEmbedding_embedProduct (α := v.val.adicCompletion F)).isProperMap using 1
    funext u
    change radii (L v u) = (‖u.val‖, ‖u.inv‖)
    simp [radii, L, Real.exp_neg, Real.exp_log (norm_pos_iff.mpr u.ne_zero), Units.inv_eq_val_inv]
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)
  let ef := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  exact Homeomorph.sumArrowHomeomorphProdArrow.symm.isProperMap.comp
    (((infiniteIdeleLog_proper F).prodMap ((IsProperMap.pi_map hL).comp
      ef.toHomeomorph.isProperMap)).comp e.toHomeomorph.isProperMap)
private theorem sLocalTrace_log_mul (g h : Iₛ) :
    sIdeleLog F S (g * h) = sIdeleLog F S g + sIdeleLog F S h := by
  funext v
  rcases v with w | v
  · let p := Units.map (RingHom.fst (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)).toMonoidHom
    exact congrFun (infiniteIdeleLog_mul F (p g) (p h)) w
  · let p : Iₛ →* (v.val.adicCompletion F)ˣ :=
      Units.map ((Pi.evalRingHom _ v).comp (RingHom.snd (InfiniteAdeleRing F) _)).toMonoidHom
    change Real.log ‖(p g).val * (p h).val‖ = Real.log ‖(p g).val‖ + Real.log ‖(p h).val‖
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (p g).ne_zero) (norm_ne_zero_iff.mpr (p h).ne_zero)]

/-- The maximum of the local absolute values bounds every logarithmic coordinate on the
norm - one group. Its inverse square root is summable on the diagonal S - units. -/
private theorem sLocalTrace_height_summable :
    Summable fun ξ : Hₛ ↦ (Real.sqrt (max 1 ‖(show Eₛ from ξ.val.val)‖))⁻¹ := by
  classical
  let : DiscreteTopology Hₛ := discreteTopology_sProjectedDiagonal
  let : DiscreteTopology (Additive Hₛ) := inferInstanceAs (DiscreteTopology Hₛ)
  let l : Additive Hₛ →+ (places → ℝ) :=
    { toFun := fun ξ ↦ sIdeleLog F S ξ.toMul.val
      map_zero' := by
        have h := sLocalTrace_log_mul (F := F) (S := S) 1 1
        simpa using h
      map_add' := fun x y ↦ sLocalTrace_log_mul _ _ }
  have hl : IsProperMap l := (sLocalTrace_log_proper (F := F) (S := S)).comp
    isClosed_sProjectedDiagonal.isClosedEmbedding_subtypeVal.isProperMap
  let n : ℝ := Fintype.card (InfinitePlace F ⊕ S) + 1
  have hn : 1 ≤ n := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hsum := summable_exp_neg_mul_norm_of_isProperMap l hl (c := 1 / (4 * n)) (by positivity)
  change Summable (fun ξ : Additive Hₛ ↦ (Real.sqrt (max 1 ‖(show Eₛ from ξ.toMul.val.val)‖))⁻¹)
  apply hsum.of_nonneg_of_le (fun _ ↦ by positivity)
  intro ξ
  let a : Eₛ := ξ.toMul.val.val
  let M := max 1 ‖a‖
  have hM : 1 ≤ M := le_max_left _ _
  have hM' : 0 < M := zero_lt_one.trans_le hM
  have hMl := Real.log_nonneg hM
  have hcoord (i : places) : l ξ i ≤ 2 * Real.log M := by
    cases i with
    | inl w =>
      have h0 : 0 < ‖ξ.toMul.val.val.1 w‖ := norm_pos_iff.mpr
        (((ξ.toMul.val.isUnit.map (RingHom.fst _ _)).map (Pi.evalRingHom _ w)).ne_zero)
      have hb : ‖ξ.toMul.val.val.1 w‖ ≤ M :=
        ((norm_le_pi_norm (ξ.toMul.val.val.1 : A∞) w).trans
          (norm_fst_le a)).trans (le_max_right _ _)
      change w.mult * Real.log ‖ξ.toMul.val.val.1 w‖ ≤ _
      calc _ ≤ (w.mult : ℝ) * Real.log M := mul_le_mul_of_nonneg_left (Real.log_le_log h0 hb) (Nat.cast_nonneg _)
           _ ≤ _ := mul_le_mul_of_nonneg_right (by rw [InfinitePlace.mult]; split_ifs <;> norm_num) hMl
    | inr v =>
      have h0 : 0 < ‖ξ.toMul.val.val.2 v‖ := norm_pos_iff.mpr
        (((ξ.toMul.val.isUnit.map (RingHom.snd _ _)).map (Pi.evalRingHom _ v)).ne_zero)
      have hb : ‖ξ.toMul.val.val.2 v‖ ≤ M :=
        ((norm_le_pi_norm ξ.toMul.val.val.2 v).trans
          (norm_snd_le a)).trans (le_max_right _ _)
      exact (Real.log_le_log h0 hb).trans (by linarith)
  have hz : ∑ i, l ξ i = 0 := by
    change ∑ i, sIdeleLog F S ξ.toMul.val i = 0
    rw [sIdeleLog_sum, sLocalTrace_unit_norm]
    simp
  have hsize : ‖l ξ‖ ≤ n * (2 * Real.log M) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i ↦ ?_
    rw [Real.norm_eq_abs, abs_le]
    have H := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ ↦ hcoord j)
    have hi := Finset.sum_erase_add (s := Finset.univ) (f := l ξ) (Finset.mem_univ i)
    rw [hz] at hi
    simp only [Finset.sum_const, nsmul_eq_mul] at H
    have hcard : ((Finset.univ.erase i).card : ℝ) ≤ n := by
      refine (Nat.cast_le.mpr (Finset.card_erase_le)).trans ?_
      simp [n]
    constructor
    · linarith [mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 2 * Real.log M)]
    · exact (hcoord i).trans (le_mul_of_one_le_left (by positivity) hn)
  change (Real.sqrt M)⁻¹ ≤ Real.exp _
  rw [← Real.exp_log (inv_pos.mpr (Real.sqrt_pos.mpr hM')), Real.exp_le_exp,
    Real.log_inv, Real.log_sqrt hM'.le]
  field_simp
  linarith

private theorem sLocalTrace_character_nontrivial {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) (ψ : K → Circle)
    (h : IsTamagawaSelfDual μ ψ) : ∃ t, (ψ t : ℂ) ≠ 1 := by
  by_contra! ht
  obtain ⟨e, he, _⟩ := h
  have h1 : e (Multiplicative.ofAdd (1 : K)) = 1 := by
    ext t
    change (e (Multiplicative.ofAdd (1 : K)) t : ℂ) = 1
    exact (congrArg (fun z : Circle ↦ (z : ℂ)) (he 1 t.toAdd)).trans (ht _)
  exact (one_ne_zero : (1 : K) ≠ 0) (congrArg Multiplicative.toAdd (e.map_eq_one_iff.mp h1))

/-- A frequency with a large local coordinate has a small translation with a nontrivial
character value. The constants are uniform because there are finitely many places. -/
private theorem sLocalTrace_frequency_step :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : Eₛ, r ≠ 0 → ∃ h : Eₛ,
      ‖h‖ ≤ C / ‖r‖ ∧ 1 ≤ C * ‖(ψₛ (r * h) : ℂ) - 1‖ := by
  classical
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let χ (w : InfinitePlace F) (z : w.Completion) := adeleStandardCharacter F (Pi.single w z, 0)
  choose z hz using fun w : InfinitePlace F ↦ sLocalTrace_character_nontrivial _ _
    (infiniteLocalAdditiveTamagawaMeasure_selfDual w)
  choose t ht using fun v : S ↦ sLocalTrace_character_nontrivial _ _
    (finiteLocalAdditiveTamagawaMeasure_selfDual F v.val)
  let A (w : InfinitePlace F) := ‖z w‖ + ‖(χ w (z w) : ℂ) - 1‖⁻¹
  let B (v : S) := ‖t v‖ + ‖(finiteLocalStandardCharacter F v.val (t v) : ℂ) - 1‖⁻¹
  have hA (w) : 0 ≤ A w := by dsimp [A]; positivity
  have hB (v) : 0 ≤ B v := by dsimp [B]; positivity
  let U := 1 + (∑ w, A w) + ∑ v, B v
  have hU : 1 ≤ U := by
    dsimp only [U]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun w _ ↦ hA w),
      Finset.sum_nonneg (s := Finset.univ) (fun v _ ↦ hB v)]
  have ha (w) : A w ≤ U := by
    dsimp only [U]
    linarith [Finset.single_le_sum (fun j _ ↦ hA j) (Finset.mem_univ w),
      Finset.sum_nonneg (s := Finset.univ) (fun v _ ↦ hB v)]
  have hb (v) : B v ≤ U := by
    dsimp only [U]
    linarith [Finset.single_le_sum (fun j _ ↦ hB j) (Finset.mem_univ v),
      Finset.sum_nonneg (s := Finset.univ) (fun w _ ↦ hA w)]
  refine ⟨2 * U, by linarith, fun r hr ↦ ?_⟩
  have hr0 := norm_pos_iff.mpr hr
  have hi : ∃ i : places, ‖r‖ / 2 < sLocalTrace_radii r i := by
    by_contra! h
    have H : ‖r‖ ≤ ‖r‖ / 2 := norm_prod_le_iff.mpr
      ⟨(pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun w ↦ h (.inl w)),
       (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun v ↦ h (.inr v))⟩
    linarith
  obtain ⟨w|v, hi⟩ := hi
  · change ‖r‖ / 2 < ‖r.1 w‖ at hi
    have h0 : r.1 w ≠ 0 := norm_pos_iff.mp (by linarith)
    let h : Eₛ := (Pi.single w (z w / r.1 w), 0)
    have hv : ψₛ (r * h) = χ w (z w) := by
      have he := sLocalTrace_arch_character (S := S) w r (z w / r.1 w)
      rw [mul_div_cancel₀ _ h0] at he
      exact he
    have hzz : 0 < ‖(χ w (z w) : ℂ) - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hz w))
    refine ⟨h, ?_, ?_⟩
    · change max ‖Pi.single (M := fun w : InfinitePlace F ↦ w.Completion) w (z w / r.1 w)‖ ‖(0 : A𝒻)‖ ≤ _
      rw [norm_zero, max_eq_left (norm_nonneg _), Pi.norm_single, norm_div]
      rw [div_le_div_iff₀ (norm_pos_iff.mpr h0) hr0]
      have H : ‖z w‖ ≤ U := (le_add_of_nonneg_right (inv_nonneg.mpr hzz.le)).trans (ha w)
      nlinarith [mul_le_mul_of_nonneg_right H hr0.le, mul_nonneg (by linarith : 0 ≤ U)
        (by linarith : 0 ≤ 2 * ‖r.1 w‖ - ‖r‖)]
    · rw [hv, ← div_le_iff₀ hzz, one_div]
      have H := (le_add_of_nonneg_left (norm_nonneg (z w))).trans (ha w)
      linarith
  · change ‖r‖ / 2 < ‖r.2 v‖ at hi
    have h0 : r.2 v ≠ 0 := norm_pos_iff.mp (by linarith)
    let h : Eₛ := (0, Pi.single v (t v / r.2 v))
    have hv : ψₛ (r * h) = finiteLocalStandardCharacter F v.val (t v) := by
      have he := sLocalTrace_fin_character (F := F) v r (t v / r.2 v)
      rw [mul_div_cancel₀ _ h0] at he
      exact he
    have hzz : 0 < ‖(finiteLocalStandardCharacter F v.val (t v) : ℂ) - 1‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (ht v))
    refine ⟨h, ?_, ?_⟩
    · change max ‖(0 : A∞)‖ ‖Pi.single (M := fun v : S ↦ v.val.adicCompletion F) v (t v / r.2 v)‖ ≤ _
      rw [norm_zero, max_eq_right (norm_nonneg _), Pi.norm_single, norm_div]
      rw [div_le_div_iff₀ (norm_pos_iff.mpr h0) hr0]
      have H : ‖t v‖ ≤ U := (le_add_of_nonneg_right (inv_nonneg.mpr hzz.le)).trans (hb v)
      nlinarith [mul_le_mul_of_nonneg_right H hr0.le, mul_nonneg (by linarith : 0 ≤ U)
        (by linarith : 0 ≤ 2 * ‖r.2 v‖ - ‖r‖)]
    · rw [hv, ← div_le_iff₀ hzz, one_div]
      have H := (le_add_of_nonneg_left (norm_nonneg (t v))).trans (hb v)
      linarith

private theorem sLocalTrace_frequency_decay {E : Type*} [NormedCommRing E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddLeftInvariant]
    (χ : Multiplicative E →ₜ* Circle)
    (C : ℝ) (hC : 1 ≤ C)
    (hs : ∀ r : E, r ≠ 0 → ∃ h : E, ‖h‖ ≤ C / ‖r‖ ∧
      1 ≤ C * ‖(χ (Multiplicative.ofAdd (r * h)) : ℂ) - 1‖)
    (k : ℝ → E → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hk : ∀ R : ℝ, 1 ≤ R → Integrable (k R) μ ∧ (∫ x, ‖k R x‖ ∂μ) ≤ A ∧
      ∀ h : E, ‖h‖ ≤ 1 → (∫ x, ‖k R (x + h) - k R x‖ ∂μ) ≤ A * Real.sqrt ‖h‖) :
    ∃ B ≥ 0, ∀ R : ℝ, 1 ≤ R → ∀ r : E,
      ‖∫ x, k R x * (χ (Multiplicative.ofAdd (x * r)) : ℂ) ∂μ‖ ≤
        B * (Real.sqrt (max 1 ‖r + 1‖))⁻¹ := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  let B := A * Real.sqrt (1 + C + ‖(1 : E)‖) + C * A * Real.sqrt (C * (1 + ‖(1 : E)‖))
  refine ⟨B, by dsimp [B]; positivity, fun R hR r ↦ ?_⟩
  let I := ∫ x, k R x * (χ (Multiplicative.ofAdd (x * r)) : ℂ) ∂μ
  let M := max 1 ‖r + 1‖
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨hi, hb, hd⟩ := hk R hR
  change ‖I‖ ≤ B * (Real.sqrt M)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr hM)]
  by_cases hr : ‖r‖ ≤ C
  · have hab : ‖I‖ ≤ A := (norm_integral_le_of_norm_le hi.norm (ae_of_all _ fun x ↦ by
      simp only [norm_mul, Circle.norm_coe, mul_one, le_refl])).trans hb
    have hM' : M ≤ 1 + C + ‖(1 : E)‖ := max_le (by linarith [norm_nonneg (1 : E)])
      ((norm_add_le _ _).trans (by linarith))
    exact (mul_le_mul hab (Real.sqrt_le_sqrt hM') (Real.sqrt_nonneg _) hA).trans
      (le_add_of_nonneg_right (by positivity))
  · have hr0 : 0 < ‖r‖ := hC0.trans (lt_of_not_ge hr)
    obtain ⟨h, hsmall, hphase⟩ := hs r (norm_pos_iff.mp hr0)
    have hh : ‖h‖ ≤ 1 := hsmall.trans ((div_le_one hr0).mpr (le_of_not_ge hr))
    have hosc := (fourierIntegral_circleCharacter_translation_bound μ χ (k R) hi r h).trans (hd h hh)
    have hmain : ‖I‖ ≤ C * A * Real.sqrt ‖h‖ := by
      have hm := mul_le_mul_of_nonneg_left hphase (norm_nonneg I)
      have hm' := mul_le_mul_of_nonneg_left hosc hC0.le
      change C * (‖I‖ * _) ≤ _ at hm'
      nlinarith
    have hMul : ‖h‖ * M ≤ C * (1 + ‖(1 : E)‖) := by
      have hr1 : 1 ≤ ‖r‖ := hC.trans (le_of_not_ge hr)
      have hM' : M ≤ ‖r‖ * (1 + ‖(1 : E)‖) := by
        apply max_le
        · exact hr1.trans (le_mul_of_one_le_right hr0.le (by linarith [norm_nonneg (1 : E)]))
        · exact (norm_add_le _ _).trans (by
            nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (norm_nonneg (1 : E))])
      calc _ ≤ C / ‖r‖ * (‖r‖ * (1 + ‖(1 : E)‖)) := mul_le_mul hsmall hM' hM.le (by positivity)
           _ = _ := by field_simp
    calc _ ≤ (C * A * Real.sqrt ‖h‖) * Real.sqrt M := by gcongr
         _ = C * A * Real.sqrt (‖h‖ * M) := by rw [Real.sqrt_mul (norm_nonneg _)]; ring
         _ ≤ C * A * Real.sqrt (C * (1 + ‖(1 : E)‖)) := by gcongr
         _ ≤ B := le_add_of_nonneg_left (by positivity)

private def sLocalTrace_tail_amplitude (f : BruhatCompactSupport Iₛ) (R : ℝ) (x : Aₛ) : ℂ :=
  fourierₛ (sLocalTraceEta f 1) x * (sLocalTrace_log_cut R (modS(x)) : ℂ)

private theorem sLocalTrace_modulus_invariant (ξ : Hₛ) (x : Aₛ) :
    modS(ξ.val.val * x) = modS(x) := by
  have h : modS(ξ.val.val) = normS(ξ.val) := by simp [sIdeleNorm, Units.coe_prod]
  rw [sLocalTrace_unit_norm] at h
  change _ = 1 at h
  change (∏ w : InfinitePlace F, ‖ξ.val.val.1 w * x.1 w‖ ^ w.mult) *
    (∏ v : S, ‖ξ.val.val.2 v * x.2 v‖) = _
  simp only [norm_mul, mul_pow, Finset.prod_mul_distrib]
  calc _ = modS(ξ.val.val) * modS(x) := by ring
       _ = _ := by rw [h, one_mul]

/-- Every remainder is a Fourier coefficient of the same amplitude at the frequency ξ⁻¹ − 1. -/
private theorem sLocalTrace_tail_coefficient (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (R : ℝ) :
    (∫ w in {w : Aₛ | R < modS(w)}, fourierₛ (sLocalTraceEta f ξ) w *
      ((Real.log (modS(w)) - Real.log R : ℝ) : ℂ) ∂νₛ) =
    ∫ x, sLocalTrace_tail_amplitude f R x * (ψₛ (x * ((ξ⁻¹).val.val - 1)) : ℂ) ∂νₛ := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  have hm : Continuous fun w : Aₛ ↦ modS(w) :=
    (continuous_finsetProd _ fun w _ ↦ (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  rw [← sLocalTrace_integral_dilate_unit ξ (fun x ↦ sLocalTrace_tail_amplitude f R x * _),
    ← integral_indicator (measurableSet_lt measurable_const hm.measurable)]
  apply integral_congr_ae
  refine ae_of_all _ fun w ↦ ?_
  dsimp only [sLocalTrace_tail_amplitude]
  rw [sLocalTrace_modulus_invariant, show ξ.val.val * w * ((ξ⁻¹).val.val - 1) = (1 - ξ.val.val) * w by
    change ξ.val.val * w * ((ξ.val⁻¹).val - 1) = _
    rw [mul_sub, mul_one, show ξ.val.val * w * (ξ.val⁻¹).val = (ξ.val.val * (ξ.val⁻¹).val) * w by ring,
      Units.mul_inv, one_mul, sub_mul, one_mul]]
  by_cases hh : R < modS(w)
  · rw [indicator_of_mem hh, sLocalTrace_log_cut, max_eq_right hh.le, sLocalTrace_fourier_affine]
    ring
  · rw [indicator_of_notMem hh, sLocalTrace_log_cut, max_eq_left (le_of_not_gt hh)]
    simp

private theorem sLocalTrace_tail_bound (f : BruhatCompactSupport Iₛ) :
    ∃ B ≥ 0, ∀ (R : ℝ), 1 ≤ R → ∀ r : Eₛ,
      ‖∫ x : Eₛ, sLocalTrace_tail_amplitude f R x * (ψₛ (x * r) : ℂ) ∂νₛ‖ ≤
        B * (Real.sqrt (max 1 ‖r + 1‖))⁻¹ := by
  let : BorelSpace Eₛ := sAdeleRing_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let χ : Multiplicative Eₛ →ₜ* Circle :=
    (sAdditiveTamagawaMeasure_selfDual F S).choose (Multiplicative.ofAdd (1 : Aₛ))
  have hχ (x : Eₛ) : χ (Multiplicative.ofAdd x) = ψₛ x := by
    exact ((sAdditiveTamagawaMeasure_selfDual F S).choose_spec.1 1 x).trans (congrArg ψₛ (one_mul _))
  have he : (fun x : Eₛ ↦ χ (Multiplicative.ofAdd x)) = ψₛ := funext hχ
  obtain ⟨η, hη⟩ := SLocalTraceEta.eta_test f (1 : Hₛ)
  let s := sAdeleSchwartzFourier η
  let g (x : Eₛ) := fourierₛ (sLocalTraceEta f 1) x
  have hg (x : Eₛ) : g x = testAt(s, x) := by
    change _ = fourierₛ (fun y ↦ η (Multiplicative.ofAdd y)) x
    rw [funext hη]
  have hgc : Continuous g := ((schwartzBruhat_continuous s).comp continuous_ofAdd).congr fun x ↦ (hg x).symm
  have hc : Continuous (sLocalTraceEta f 1 : Eₛ → ℂ) :=
    ((schwartzBruhat_continuous η).comp continuous_ofAdd).congr hη
  obtain ⟨K, hK, hLip⟩ := sLocalTrace_fourier_lipschitz (E := Eₛ) νₛ χ _
    hc (SLocalTraceEta.eta_compact f 1)
  rw [he] at hLip
  obtain ⟨d, C, hC, hmod⟩ := sLocalTrace_modulus_translation_bound (F := F) (S := S)
  have hW := sLocalTrace_weighted_moment s d
  simp_rw [← hg] at hW
  have hm : Continuous fun w : Eₛ ↦ modS(w) :=
    (continuous_finsetProd _ fun w _ ↦ (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  have hm0 (x : Eₛ) : 0 ≤ modS(x) := mul_nonneg
    (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (norm_nonneg _) _) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
  obtain ⟨A, hA, hcut⟩ := sLocalTrace_cut_translation (E := Eₛ) νₛ _ hm hm0 d C hC hmod g hgc K hK hLip hW
  obtain ⟨D, hD, hs⟩ := sLocalTrace_frequency_step (F := F) (S := S)
  simp_rw [← hχ] at hs ⊢
  exact sLocalTrace_frequency_decay (E := Eₛ) νₛ χ D hD hs (sLocalTrace_tail_amplitude f) A hA hcut

end SharpMassRemainder

/-- Paper: (12.4.1.25)–(12.4.1.27), p. 519. Remainder of the summed sharp masses.
For each S-unit ξ, Fourier inversion splits the sharp mass into the logarithmic term
`f(ξ) log R`, the constant term, and an integral over the Fourier region `|w|_S > R`.
These remainders are summable over the S-units for large R and their sum tends to zero.
Deviation: The paper does not treat the sum over ξ; it cites [Co, §VII, Thm 4]. -/
private theorem sLocalTraceSharpMass_asymptotic_tail
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (f : BruhatCompactSupport Iₛ) :
    ∃ T : ℝ → ℂ, (∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R -
        (volume₁ : ℂ) * (f.val ξ.val * (Real.log R : ℂ) +
          -∫ w in range (Units.val : Iₛ → Aₛ),
            fourierₛ (sLocalTraceEta f ξ) w * ((Real.log (modS(w)) : ℝ) : ℂ) ∂νₛ)) (T R)) ∧
      Tendsto T atTop (𝓝 0) := by
  classical
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let m (x : Aₛ) := modS(x)
  have hm : Continuous m :=
    (continuous_finsetProd _ fun w _ ↦ (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  let E := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)
  let V₁ : ℂ := volume₁
  let q (R : ℝ) (ξ : Hₛ) := V₁ * ∫ w in {w : Aₛ | R < m w}, fourierₛ (sLocalTraceEta f ξ) w *
    ((Real.log (m w) - Real.log R : ℝ) : ℂ) ∂νₛ
  obtain ⟨B, hB, hb⟩ := sLocalTrace_tail_bound f
  let M (ξ : Hₛ) := max 1 ‖(show E from (ξ⁻¹).val.val)‖
  let b (ξ : Hₛ) := (‖V₁‖ * B) * (Real.sqrt (M ξ))⁻¹
  have hsum : Summable b := ((sLocalTrace_height_summable (F := F) (S := S)).comp_injective
    (inv_injective : Injective (Inv.inv : Hₛ → Hₛ))).mul_left _
  have hbound (R : ℝ) (hR : 1 ≤ R) (ξ : Hₛ) : ‖q R ξ‖ ≤ b ξ := by
    let a : E := (ξ⁻¹).val.val
    let r := a - 1
    have he : r + 1 = a := sub_add_cancel _ _
    have h := hb R hR r
    rw [he] at h
    change ‖V₁ * _‖ ≤ _
    rw [norm_mul, sLocalTrace_tail_coefficient f ξ R]
    change ‖V₁‖ * ‖∫ x : E, sLocalTrace_tail_amplitude f R x * (ψₛ (x * r) : ℂ) ∂νₛ‖ ≤
      (‖V₁‖ * B) * (Real.sqrt (max 1 ‖a‖))⁻¹
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg V₁)
  have hlim (ξ : Hₛ) : Tendsto (fun R ↦ q R ξ) atTop (𝓝 0) := by
    simpa only [mul_zero] using (logBand_remainder_tendsto νₛ _ m hm.measurable
      (sLocalTraceEta_fourier_integrable f ξ) (sLocalTrace_fourier_log_integrable f ξ)).const_mul V₁
  refine ⟨fun R ↦ ∑' ξ, q R ξ, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    simpa only [sLocalTrace_remainder_eq] using (hsum.of_norm_bounded (hbound R hR)).hasSum
  · simpa only [tsum_zero] using (tendsto_tsum_of_dominated_convergence hsum hlim
      ((eventually_ge_atTop (1 : ℝ)).mono hbound))

/-- Paper: (12.4.1.25)–(12.4.1.28), p. 519. After subtraction of the logarithmic
term the sum of sharp orbital masses tends to the norm-one volume times the local
principal values.
Deviation: Uses the sharp expression from (12.4.1.24) with R = λλ′. The replacement
of φ(g⁻¹) by φ(g) is the last step on p. 519. Appendix B.4 incorporates the real and
complex normalization factors in the archimedean distributions. -/
theorem sLocalTraceSharpMass_asymptotic
    (φ : BruhatCompactSupport C𝔽)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (_hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g)))) :
    ∃ (a : archTest) (b : finiteTest) (M : ℝ → ℂ),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ),
        (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      (∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (M R)) ∧
      Tendsto (fun R ↦ M R - (volume₁ : ℂ) * φ.val 1 * (Real.log R : ℂ))
        atTop (𝓝 ((volume₁ : ℂ) * principalValues(a, b))) := by
  obtain ⟨a, b, ha, hb⟩ := sLocalTraceSharpMass_asymptotic_restrict φ
  have hκ := sLocalTraceSharpMass_asymptotic_const φ _hPic _hRamified _hOutside f _hLift
    a b ha hb
  obtain ⟨T, hT, hT0⟩ := sLocalTraceSharpMass_asymptotic_tail _hRamified f
  have hy : HasSum (fun ξ : Hₛ ↦ f.val ξ.val) (φ.val 1) := by
    have h := _hLift 1
    simp only [mul_one, map_one, QuotientGroup.mk_one] at h
    exact h
  obtain ⟨M, hM, hlim⟩ := sLocalTraceSharpMass_asymptotic_assemble
    (fun ξ R ↦ sLocalTraceSharpMass f ξ R) (fun ξ : Hₛ ↦ f.val ξ.val) _ _ _ _ T hy hκ hT hT0
  exact ⟨a, b, M, ha, hb, hM, hlim⟩

-- TODO(paper-gap): Theorem 12.4.1.1 needs the actual smoothed PW quotient kernel
-- and a limit for its difference from the sharp orbital mass. Neither the cutoff
-- family with the independent lower bound nor the comparison is specified.
-- The following statement records the conclusion with that comparison exposed.

/-- Paper: Theorem 12.4.1.1, p. 514. The normalized quotient diagonal integral,
with its logarithmic term removed, tends to the sum of local principal values.
Deviation: The chosen quotient kernel must have integrable diagonals and agree
asymptotically with the summed sharp masses. These hypotheses expose the missing
comparison with the regularized Paley–Wiener operator. The limit is joint. -/
theorem sLocalTrace_asymptotic_of_sharp_comparison
    (φ : BruhatCompactSupport C𝔽)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (_hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (k : ℝ × ℝ → Jₛ → Jₛ → ℂ) (M : ℝ → ℂ)
    (_hSum : ∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (M R))
    (_hDiag : ∀ᶠ p in atTop ×ˢ atTop, Integrable (fun x ↦ k p x x) μJ)
    (_hComparison : Tendsto
      (fun p : ℝ × ℝ ↦ (∫ x, k p x x ∂μJ) - M (p.1 * p.2))
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ),
        (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      Tendsto (fun p : ℝ × ℝ ↦ (∫ x, k p x x ∂μJ) / (volume₁ : ℂ) -
        φ.val 1 * (Real.log (p.1 * p.2) : ℂ)) (atTop ×ˢ atTop) (𝓝 principalValues(a, b)) := by
  obtain ⟨a, b, N, ha, hb, hsum, hN⟩ :=
    sLocalTraceSharpMass_asymptotic (F := F) (S := S) φ _hPic _hRamified _hOutside f _hLift
  refine ⟨a, b, ha, hb, ?_⟩
  have heq : N =ᶠ[atTop] M := by
    filter_upwards [hsum, _hSum] with R h₁ h₂ using h₁.unique h₂
  have hM : Tendsto (fun R ↦ M R - (volume₁ : ℂ) * φ.val 1 * (Real.log R : ℂ))
      atTop (𝓝 ((volume₁ : ℂ) * principalValues(a, b))) :=
    hN.congr' (heq.mono fun R h ↦ by simp only [h])
  have hp : Tendsto (fun p : ℝ × ℝ ↦ p.1 * p.2) (atTop ×ˢ atTop) atTop :=
    tendsto_fst.atTop_mul_atTop₀ tendsto_snd
  let G := (sIdeleQuotientNorm F S).ker
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let μ := sLocalNormOneQuotientMeasure F S
  have : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hv : (volume₁ : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩)
    · exact isOpen_univ.measure_ne_zero μ univ_nonempty
    · exact measure_ne_top μ univ
  have h := (_hComparison.add (hM.comp hp)).div_const (volume₁ : ℂ)
  have hc : (0 + (volume₁ : ℂ) * principalValues(a, b)) / (volume₁ : ℂ) = principalValues(a, b) := by
    rw [zero_add, mul_comm, mul_div_cancel_right₀ _ hv]
  rw [hc] at h
  refine h.congr' (Eventually.of_forall fun p ↦ ?_)
  change ((∫ x, k p x x ∂μJ) - M (p.1 * p.2) +
    (M (p.1 * p.2) - (volume₁ : ℂ) * φ.val 1 * (Real.log (p.1 * p.2) : ℂ))) / _ = _
  field_simp
  ring

section PolarMoments

attribute [local instance] instInfiniteCompletionMeasurableSpaceSec4 instFiniteCompletionMeasurableSec4b

/-- Paper: (12.4.1.7), p. 516. Integrating the local dilation kernel against additive
Tamagawa measure multiplies the integral of the test by the positive half-Mellin moment
of the lift. Together with evaluation at zero, this identifies the two local polar
functionals before the cutoff and passage to the quotient. -/
theorem integral_sLocalTraceDilationKernel (f : BruhatCompactSupport Iₛ) (b : Aₛ → ℂ)
    (hb : Continuous b) (hbi : Integrable b νₛ) :
    Integrable (sLocalTraceDilationKernel f b) νₛ ∧
    ∫ x, sLocalTraceDilationKernel f b x ∂νₛ =
      (∫ g : Iₛ, f.val g * (Real.sqrt (normS(g)) : ℂ) ∂μₛ) * ∫ x, b x ∂νₛ := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  let W (g : Iₛ) := f.val g / (Real.sqrt (normS(g)) : ℂ)
  have hn : Continuous fun g : Iₛ ↦ normS(g) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp sLocalTrace_sIdeleNorm_continuous)
  have hp (g : Iₛ) : 0 < normS(g) := NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S g))
  have hne (g : Iₛ) : (Real.sqrt (normS(g)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp g)).ne'
  have hf : Continuous f.val := sLocalTraceDilationKernel_apply_zero_continuous
    ((mem_bruhatSmoothSubmodule_iff _).1 f.property.1)
  have hW : Continuous W := hf.div (Complex.continuous_ofReal.comp hn.sqrt) hne
  let H (p : Aₛ × Iₛ) := W p.2 * b ((p.2⁻¹).val * p.1)
  have hH : Continuous H := (hW.comp continuous_snd).mul
    (hb.comp (((Units.continuous_val.comp continuous_inv).comp continuous_snd).mul continuous_fst))
  have hnorm (g : Iₛ) : (∫ y, ‖b ((g⁻¹).val * y)‖ ∂νₛ) = normS(g) * ∫ y, ‖b y‖ ∂νₛ := by
    have h := sLocalTrace_integral_inv_dilate g (fun y ↦ (‖b y‖ : ℂ))
    simp only [integral_complex_ofReal, ← Complex.ofReal_mul] at h
    exact Complex.ofReal_injective h
  have hprod : Integrable H ((νₛ).prod μₛ) := by
    refine (integrable_prod_iff' hH.aestronglyMeasurable).2 ⟨ae_of_all _ fun g ↦ ?_, ?_⟩
    · have htrans : Integrable (fun y ↦ b ((g⁻¹).val * y)) νₛ := by
        simpa only [one_mul] using sLocalTrace_integrable_symbol_dilate b hbi g⁻¹
          (fun _ ↦ (1 : ℂ)) measurable_const 1 (fun _ ↦ norm_one.le)
      exact htrans.const_mul (W g)
    · let M (g : Iₛ) := (‖W g‖ * normS(g)) * ∫ y, ‖b y‖ ∂νₛ
      have hM : HasCompactSupport M := HasCompactSupport.mono f.property.2 fun g hg h0 ↦
        hg (by simp [M, W, h0])
      have hMi : Integrable M μₛ :=
        ((hW.norm.mul hn).mul continuous_const).integrable_of_hasCompactSupport hM
      refine hMi.congr (ae_of_all _ fun g ↦ ?_)
      dsimp only [M, H]
      simp_rw [norm_mul]
      rw [integral_const_mul, hnorm, mul_assoc]
  have hw (g : Iₛ) : W g * (normS(g) : ℂ) = f.val g * (Real.sqrt (normS(g)) : ℂ) := by
    have hs : (Real.sqrt (normS(g)) : ℂ) ^ 2 = (normS(g) : ℂ) := by
      exact_mod_cast Real.sq_sqrt (hp g).le
    dsimp only [W]
    rw [← hs]
    field_simp [hne g]
  refine ⟨hprod.integral_prod_left, ?_⟩
  change (∫ x, ∫ g, H (x, g) ∂μₛ ∂νₛ) = _
  rw [integral_integral_swap (f := fun x g ↦ H (x, g)) hprod]
  simp only [H, integral_const_mul, sLocalTrace_integral_inv_dilate, ← mul_assoc, hw,
    integral_mul_const]

/-- Paper: (12.4.1.4), p. 515. A continuous weight on the
S-idele quotient pairs with the periodized lift by integrating upstairs. In
particular both half-Mellin moments depend only on the periodization. -/
private theorem sLocalTraceLift_weighted_integral
    (f : BruhatCompactSupport Iₛ) (φJ w : Jₛ → ℂ) (hw : Continuous w)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φJ (QuotientGroup.mk g))) :
    Integrable (fun q ↦ φJ q * w q) μJ ∧
      (∫ g : Iₛ, f.val g * w (QuotientGroup.mk g) ∂μₛ) = ∫ q, φJ q * w q ∂μJ := by
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  let : (μₛ).Regular := sMultiplicativeTamagawaMeasure_regular
  let : DiscreteTopology Hₛ := discreteTopology_sProjectedDiagonal
  let : Countable Hₛ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : (Measure.count : Measure Hₛ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let : (Measure.count : Measure Hₛ).Regular := count_regular_of_discreteTopology
  let B (g : Iₛ) := f.val g * w (QuotientGroup.mk g)
  have hf : Continuous f.val := sLocalTraceDilationKernel_apply_zero_continuous
    ((mem_bruhatSmoothSubmodule_iff _).1 f.property.1)
  have hB : Integrable B μₛ :=
    (hf.mul (hw.comp continuous_quotient_mk')).integrable_of_hasCompactSupport
      (HasCompactSupport.mono f.property.2 fun g hg h0 ↦ hg (by simp [h0]))
  have hW := weilQuotientIntegral_L1 Hₛ isClosed_sProjectedDiagonal μₛ Measure.count μJ
    sLocalQuotientTamagawaMeasure_isWeil hB
  have he : lcaCosetIntegral Hₛ Measure.count B =ᵐ[μJ] fun q ↦ φJ q * w q := by
    filter_upwards [hW.1] with q hi
    have hq : (QuotientGroup.mk q.out : Jₛ) = q := QuotientGroup.out_eq' q
    calc
      lcaCosetIntegral Hₛ Measure.count B q = ∑' ξ : Hₛ, B (q.out * ξ.val) := by
        simpa only [lcaCosetIntegral, count_real_singleton, one_smul] using integral_countable hi
      _ = ∑' ξ : Hₛ, f.val (ξ.val * q.out) * w q := by
        apply tsum_congr
        intro ξ
        have hclass : (QuotientGroup.mk (q.out * ξ.val) : Jₛ) = q :=
          (QuotientGroup.mk_mul_of_mem q.out ξ.property).trans hq
        dsimp only [B]
        rw [hclass, mul_comm q.out]
      _ = φJ q * w q := by simpa only [hq] using ((hLift q.out).mul_right (w q)).tsum_eq
  exact ⟨hW.2.1.congr he, hW.2.2.trans (integral_congr_ae he)⟩

/-- With trivial S-class group, every global idele class is the product of an
outside integral unit with the insertion of a representative of its image in
the S-idele quotient. The quotient map preserves the module. -/
private theorem sLocalTraceLift_globalQuotient
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) :
    ∃ q : C𝔽 →* Jₛ, IsOpenQuotientMap q ∧
      (∀ c, sIdeleQuotientNorm F S (q c) = ideleClassNorm F c) ∧
      ∀ c : C𝔽, ∃ (a : outsideIntegralIdeleUnits F S) (g : Iₛ),
        c = QuotientGroup.mk a.val * classAtS(g) ∧ q c = QuotientGroup.mk g := by
  let := hPic
  obtain ⟨e, he, hn⟩ := sIdeleClassGroup_equiv_of_classNumberOne F S
  let A := integralAdelesOutside F S
  let i := integralIdeleInsertion F S
  let r := Units.map (adeleProjection F S).toMonoidHom
  let j := sIdeleInsertion F S
  let p := Units.map ((adeleProjection F S).comp A.subtype).toMonoidHom
  let d := (Units.map (integralAdeleDiagonal F S).toMonoidHom).range
  -- Use the coordinate projection in §3.1 so we can evaluate it on representatives.
  let π := QuotientGroup.map d (d.map p) p (Subgroup.le_comap_map _ _)
  have hp : IsOpenQuotientMap p := by
    let B := (v : {v : V // v ∉ S}) → v.val.adicCompletionIntegers F
    obtain ⟨f, hf, hf', hcoord⟩ := integralAdelesOutside_factors F S
    let E : A ≃ₜ* (Aₛ × B) :=
      { f.toMulEquiv with continuous_toFun := hf, continuous_invFun := hf' }
    let U := (Units.mapContinuousMulEquiv E).trans (ContinuousMulEquiv.prodUnits _ _)
    have hp' : (p : Aˣ → Iₛ) = Prod.fst ∘ U := funext fun u ↦
      Units.ext (hcoord u.val).1.symm
    rw [hp']
    exact isOpenQuotientMap_fst.comp U.toHomeomorph.isOpenQuotientMap
  have hπ : IsOpenQuotientMap π := by
    have hmk : IsOpenQuotientMap (QuotientGroup.mk' d) := QuotientGroup.isOpenQuotientMap_mk
    exact hmk.of_comp_iff.mp ((QuotientGroup.isOpenQuotientMap_mk (N := d.map p)).comp hp)
  let q : C𝔽 →* Jₛ := π.comp e.symm.toMulEquiv.toMonoidHom
  have he' (u : Aˣ) : e (QuotientGroup.mk u) = QuotientGroup.mk (i u) := he u
  have hqu (u : Aˣ) : q (QuotientGroup.mk (i u)) = QuotientGroup.mk (p u) := by
    rw [← he' u]
    change π (e.symm (e (QuotientGroup.mk u))) = _
    rw [e.symm_apply_apply]
    rfl
  have hrj (g : Iₛ) : r (j g) = g := Units.ext
    (Prod.ext (sIdeleInsertion_apply F S g).1 (funext (sIdeleInsertion_apply F S g).2.1))
  have hj (g : Iₛ) : j g ∈ i.range := by
    apply (mem_range_integralIdeleInsertion F S (j g)).mpr
    intro v hv
    refine ⟨(sIdeleInsertion_apply F S g).2.2 v hv ▸ (v.adicCompletionIntegers F).one_mem, ?_⟩
    have h' : (j g).inv.2 v = 1 :=
      (congrArg (fun x : IdeleGroup (𝓞 F) F ↦ x.val.2 v) (map_inv j g).symm).trans
        ((sIdeleInsertion_apply F S g⁻¹).2.2 v hv)
    exact h' ▸ (v.adicCompletionIntegers F).one_mem
  have hrep (c : C𝔽) : ∃ u : Aˣ, QuotientGroup.mk (i u) = c := by
    obtain ⟨x, rfl⟩ := e.surjective c
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨u, (he' u).symm⟩
  refine ⟨q, hπ.comp e.symm.toHomeomorph.isOpenQuotientMap, ?_, ?_⟩
  · intro c
    obtain ⟨u, rfl⟩ := hrep c
    rw [hqu, ← he' u, hn]
    rfl
  · intro c
    obtain ⟨u, rfl⟩ := hrep c
    let a := i u / j (p u)
    have ha : a ∈ outsideIntegralIdeleUnits F S := by
      refine ⟨i.range.div_mem ⟨u, rfl⟩ (hj _), ?_⟩
      change r (i u / j (p u)) = 1
      rw [map_div, hrj]
      exact div_self' _
    refine ⟨⟨a, ha⟩, p u, ?_, hqu _⟩
    let Q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
    change Q (i u) = Q a * Q (j (p u))
    rw [← map_mul, show a * j (p u) = i u from div_mul_cancel _ _]

/-- Every outside-unit-invariant test descends along this global quotient with
the prescribed value on every inserted S-idele. -/
private theorem sLocalTraceLift_globalTestDescent
    (φ : BruhatCompactSupport C𝔽)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (q : C𝔽 →* Jₛ)
    (hrep : ∀ c : C𝔽, ∃ (a : outsideIntegralIdeleUnits F S) (g : Iₛ),
      c = QuotientGroup.mk a.val * classAtS(g) ∧ q c = QuotientGroup.mk g) :
    ∃ φJ : Jₛ → ℂ, (∀ c : C𝔽, φ.val c = φJ (q c)) ∧
      ∀ g : Iₛ, φJ (QuotientGroup.mk g) = φ.val (classAtS(g)) := by
  let φJ (z : Jₛ) := φ.val (classAtS(z.out))
  have hJ (g : Iₛ) : φJ (QuotientGroup.mk g) = φ.val (classAtS(g)) := by
    let y := (QuotientGroup.mk g : Jₛ).out
    have hy : (QuotientGroup.mk y : Jₛ) = QuotientGroup.mk g := QuotientGroup.out_eq' _
    have hξ : y / g ∈ Hₛ := QuotientGroup.eq_iff_div_mem.mp hy
    have h := sLocalTraceRestriction_invariant φ hOutside ⟨y / g, hξ⟩ g
    simpa only [Subtype.coe_mk, div_mul_cancel] using h
  refine ⟨φJ, ?_, hJ⟩
  intro c
  obtain ⟨a, g, hc, hq⟩ := hrep c
  rw [hq, hJ, hc, hOutside]

/-- A norm-compatible surjection pushes global class Haar measure to S-local
quotient Haar measure with the ratio of the two norm-one masses. The norm interval from one to
exp(1) has radial mass one and determines the Haar scalar. -/
private theorem sLocalTrace_map_classMeasure (q : C𝔽 →ₜ* Jₛ) (hq : Surjective q)
    (hn : ∀ x, sIdeleQuotientNorm F S (q x) = ideleClassNorm F x) :
    (sLocalNormOneQuotientMeasure F S univ) • (ideleClassTamagawaMeasure F).map q =
      (normOneIdeleClassTamagawaMeasure F univ) • μJ := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : BorelSpace (sIdeleQuotientNorm F S).ker := ⟨rfl⟩
  let : T2Space Jₛ := instSIdeleQuotientT2Sec1
  let : LocallyCompactSpace Jₛ := instSIdeleQuotientLocallyCompactSec1
  let : SecondCountableTopology Jₛ := instSIdeleQuotientSecondCountableSec1
  let : SecondCountableTopology C𝔽 := instIdeleClassSecondCountableSec1
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let μ := ideleClassTamagawaMeasure F
  let ν := normOneIdeleClassTamagawaMeasure F
  let η := sLocalNormOneQuotientMeasure F S
  let n := ideleClassNorm F
  let m := sIdeleQuotientNorm F S
  have hc : Continuous n := (isProperMap_ideleClassNorm F).continuous
  have hm : Continuous m := (isProperMap_sIdeleQuotientNorm F S).continuous
  have heq : m ∘ q = n := funext hn
  have hw := ideleClassTamagawaMeasure_isWeil F
  have hν := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2
  let : μ.IsHaarMeasure := hw.1
  let : ν.IsHaarMeasure := hν.1
  let : CompactSpace n.ker := (ideleClassGroup_finiteness F).2.1
  let : IsFiniteMeasure ν := CompactSpace.isFiniteMeasure
  let : (μJ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  let : η.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : CompactSpace m.ker := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  have hglobal : μ.map n = (ν univ) • positiveRealHaar := by
    let σ (t : ℝ≥0ˣ) : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F t)
    have hσ : Continuous σ := continuous_quotient_mk'.comp (canonicalIdeleNormSection_continuous F)
    have hr : RightInverse σ n := canonicalIdeleNormSection_rightInverse F
    let j (p : ℝ≥0ˣ × n.ker) := σ p.1 * p.2.val
    have hj : Measurable j :=
      ((hσ.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).measurable
    have hp : (positiveRealHaar.prod ν).map j = μ :=
      normProduct_of_isWeil n hc σ hσ hr μ hw.2.1 ν hν.2.1
        (normOneIdeleClassTamagawaMeasure_isWeil F)
    have hjn : n ∘ j = Prod.fst := by
      funext p
      change n (σ p.1 * p.2.val) = p.1
      rw [map_mul, hr, MonoidHom.mem_ker.mp p.2.property, mul_one]
    rw [← hp, Measure.map_map hc.measurable hj, hjn, Measure.map_fst_prod]
  have hlocal : (μJ).map m = (η univ) • positiveRealHaar := by
    obtain ⟨τ, hτ⟩ := sLocalTrace_exists_normSection (F := F) (S := S)
    let j (p : m.ker × ℝ≥0ˣ) := p.1.val * (QuotientGroup.mk (τ p.2) : Jₛ)
    have hj : Measurable j :=
      ((continuous_subtype_val.comp continuous_fst).mul
        ((show Continuous (QuotientGroup.mk : Iₛ → Jₛ) from continuous_quotient_mk').comp
          (τ.continuous.comp continuous_snd))).measurable
    have hjm : m ∘ j = Prod.snd := by
      funext p
      change m (p.1.val * QuotientGroup.mk (τ p.2)) = p.2
      rw [map_mul, MonoidHom.mem_ker.mp p.1.property, one_mul]
      exact (sIdeleQuotientNorm_mk F S (τ p.2)).trans (hτ p.2)
    have hp : (η.prod positiveRealHaar).map j = μJ :=
      (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
    rw [← hp, Measure.map_map hm.measurable hj, hjm, Measure.map_snd_prod]
  have hp : IsProperMap q := isProperMap_of_comp_of_t2 q.continuous hm
    (by rw [heq]; exact isProperMap_ideleClassNorm F)
  let : (μ.map q).IsHaarMeasure := Measure.isHaarMeasure_map μ q.toMonoidHom q.continuous hq
    (isProperMap_iff_tendsto_cocompact.mp hp).2
  let k := (μ.map q).haarScalarFactor μJ
  have hk : μ.map q = k • μJ := Measure.isMulLeftInvariant_eq_smul (μ.map q) μJ
  have hrad := congrArg (fun m' : Measure Jₛ ↦ m'.map m) hk
  have hqMeas : Measurable (q : C𝔽 → Jₛ) := q.continuous.measurable
  rw [Measure.map_map hm.measurable hqMeas, heq, hglobal, Measure.map_smul k hm.measurable.aemeasurable,
    hlocal] at hrad
  let T : Set ℝ≥0ˣ := {t | ((t.val : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1)}
  have hT : positiveRealHaar T = 1 := by
    let t : ℝ≥0ˣ := Units.mk0 (Real.exp 1).toNNReal (by positivity)
    have ht : ((t.val : ℝ≥0) : ℝ) = Real.exp 1 := Real.coe_toNNReal _ (Real.exp_pos 1).le
    have h := positiveRealHaar_interval t (by rw [ht]; exact Real.one_le_exp zero_le_one)
    rw [ht, Real.log_exp, ENNReal.ofReal_one] at h
    exact h
  have hmass := congrArg (fun m' : Measure ℝ≥0ˣ ↦ m' T) hrad
  have hratio : ν univ = (k : ℝ≥0∞) * η univ := by
    simpa only [smul_apply, ENNReal.smul_def, smul_eq_mul, hT, mul_one] using hmass
  change (η univ) • (μ.map q) = (ν univ) • μJ
  rw [hk, hratio, ENNReal.smul_def, smul_smul, mul_comm (η univ)]

/-- Paper: (12.4.1.4), p. 515. After normalization by the respective norm-one volumes,
the Mellin moments of a compact S-local lift agree with those of its global test.
In particular the weights given by the square root of the norm and its reciprocal
recover the two global polar moments used on p. 520. -/
theorem sLocalTraceLift_global_norm_integral
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (w : ℝ≥0ˣ → ℂ) (hw : Continuous w) :
    (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) *
      (∫ g : Iₛ, f.val g * w (sIdeleNorm F S g) ∂μₛ) =
    (volume₁ : ℂ) *
      ∫ c : C𝔽, φ.val c * w (ideleClassNorm F c) ∂(ideleClassTamagawaMeasure F) := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : LocallyCompactSpace C𝔽 := instIdeleClassLocallyCompactSec1
  obtain ⟨q, hq, hn, hrep⟩ := sLocalTraceLift_globalQuotient hPic
  let Q : C𝔽 →ₜ* Jₛ := ⟨q, hq.continuous⟩
  obtain ⟨φJ, hdesc, hliftJ⟩ := sLocalTraceLift_globalTestDescent φ hOutside q hrep
  have hc : Continuous φ.val := sLocalTraceDilationKernel_apply_zero_continuous
    ((mem_bruhatSmoothSubmodule_iff _).1 φ.property.1)
  have hcJ : Continuous φJ :=
    hq.isQuotientMap.continuous_iff.mpr (hc.congr fun c ↦ hdesc c)
  let W (j : Jₛ) := w (sIdeleQuotientNorm F S j)
  have hwJ : Continuous W := hw.comp (isProperMap_sIdeleQuotientNorm F S).continuous
  let H (j : Jₛ) := φJ j * W j
  have hH : Continuous H := hcJ.mul hwJ
  have hlocal : (∫ g : Iₛ, f.val g * w (sIdeleNorm F S g) ∂μₛ) = ∫ j, H j ∂μJ := by
    have h := (sLocalTraceLift_weighted_integral f φJ W hwJ (fun g ↦ by
      rw [hliftJ]
      exact hLift g)).2
    simpa only [H, W, sIdeleQuotientNorm_mk] using h
  have hpoint (c : C𝔽) : H (Q c) = φ.val c * w (ideleClassNorm F c) := by
    change φJ (q c) * w (sIdeleQuotientNorm F S (q c)) = _
    rw [← hdesc c, hn]
  have hmap : (∫ j, H j ∂(ideleClassTamagawaMeasure F).map Q) =
      ∫ c : C𝔽, φ.val c * w (ideleClassNorm F c) ∂(ideleClassTamagawaMeasure F) := by
    have hQ : Measurable (Q : C𝔽 → Jₛ) := Q.continuous.measurable
    rw [integral_map_of_stronglyMeasurable hQ hH.stronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ hpoint)
  have h := congrArg (fun m : Measure Jₛ ↦ ∫ j, H j ∂m)
    (sLocalTrace_map_classMeasure Q hq.surjective hn)
  simpa only [integral_smul_measure, Complex.real_smul, hmap, ← hlocal] using h.symm

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The two
half-Mellin weights of the compact S-idelic lift give the sum of the two
global polar Fourier–Mellin terms, with the normalization of §12.4. -/
theorem sLocalTraceLift_global_polar_sum
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g)))) :
    let pole (s : ℂ) := modulatedFourierMellin (continuousIdeleClassNorm F) univ
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      (ideleClassTamagawaMeasure F) φ.val (ideleClassNormTwist 1 s)
    (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) *
        ((∫ g : Iₛ, f.val g * (Real.sqrt (normS(g)) : ℂ) ∂μₛ) +
         ∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ) =
      (volume₁ : ℂ) * (pole (1 / 2) + pole (-1 / 2)) := by
  let root (t : ℝ≥0ˣ) : ℂ := (Real.sqrt (t.val : ℝ) : ℂ)
  have hc : Continuous root :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp Units.continuous_val).sqrt
  have hne (t : ℝ≥0ˣ) : root t ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (Units.zero_lt t))).ne'
  have hs (t : ℝ≥0ˣ) : ((t.val : ℝ) : ℂ) ^ (1 / 2 : ℂ) = root t := by
    dsimp only [root]
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (NNReal.coe_nonneg t.val)]
    norm_num
  have hp (c : C𝔽) : ideleClassNormTwist 1 (1 / 2) c = root (ideleClassNorm F c) := by
    change (1 : ℂ) * _ = _
    rw [one_mul]
    exact hs _
  have hm (c : C𝔽) : ideleClassNormTwist 1 (-1 / 2) c = (root (ideleClassNorm F c))⁻¹ := by
    change (1 : ℂ) * (((ideleClassNorm F c).val : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = _
    rw [one_mul, neg_div, Complex.cpow_neg, hs]
  have hpole := sLocalTraceLift_global_norm_integral hPic φ hOutside f hLift root hc
  have hneg := sLocalTraceLift_global_norm_integral hPic φ hOutside f hLift
    (fun t ↦ (root t)⁻¹) (hc.inv₀ hne)
  dsimp only
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ, hp, hm,
    mul_add]
  simpa only [div_eq_mul_inv] using congrArg₂ (fun x y : ℂ ↦ x + y) hpole hneg

end PolarMoments

end RiemannMasullo
