module

public import RiemannMasullo.Ch09_HardySobolev.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec1
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.Fourier.LpSpace
import RiemannMasullo.Ch02_AdelicTheta.Sec1
import RiemannMasullo.Ch02_AdelicTheta.Sec2a
import RiemannMasullo.Ch02_AdelicTheta.Sec2b
import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1d
import RiemannMasullo.ForMathlib.Analysis.Calculus.ContDiff.LineDeriv
import RiemannMasullo.ForMathlib.Topology.Algebra.OpenSubgroup
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2a
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import RiemannMasullo.ForMathlib.Analysis.Fourier.AbelLimit
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space.TensorProduct
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ChangeVariables
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# Hardy–Sobolev spaces and Paley–Wiener conditions

Masullo, §9.2, pp. 403–419. Scalar functions on the positive reals are represented
in the coordinate `x = log t`, so multiplicative Haar measure becomes Lebesgue measure.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology TensorProduct

set_option maxSynthPendingDepth 3
-- Match the project setting when this module is checked directly by Lean.
set_option linter.unusedSectionVars false

namespace RiemannMasullo

-- TODO(paper-gap): The coordinate integrals on pp. 403 and 416 omit the
-- kernel character. Use the intrinsic transform from §D.3.3.

section Idelic

open NumberField
open scoped NumberField.AdeleRing

variable {F : Type*} [Field F] [NumberField F]

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
set_option quotPrecheck false in
local notation "m[" F "]" =>
  (continuousIdeleClassNorm F : C[F] →ₜ* ℝ≥0ˣ)
set_option quotPrecheck false in
local notation "hm[" F "]" => (show IsModulation m[F] from
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩)

local instance instT2ClassSec2 : T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instLocallyCompactClassSec2 : LocallyCompactSpace C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance instMeasurableClassSec2 : MeasurableSpace C[F] := borel _
local instance instBorelClassSec2 : BorelSpace C[F] := ⟨rfl⟩

section PolarTheta

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)

/-- Every sufficiently small finite idele fixes an adelic test under dilation. -/
private theorem theta_finite_stabilizer (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
    ∀ᶠ u : 𝔸ᶠ[F]ˣ in 𝓝 1, ∀ x : 𝔸[F],
      f (Multiplicative.ofAdd (x.1, u.val * x.2)) = f (Multiplicative.ofAdd x) := by
  classical
  let V := IsDedekindDomain.HeightOneSpectrum (𝓞 F)
  have hunit : ∀ᶠ u : 𝔸ᶠ[F]ˣ in 𝓝 1, ∀ v : V, u.val v ∈ v.adicCompletionIntegers F ∧ (u⁻¹).val v ∈ v.adicCompletionIntegers F := by
    have ho : IsOpen {z : 𝔸ᶠ[F] | ∀ v, z v ∈ v.adicCompletionIntegers F} :=
      RestrictedProduct.isOpen_forall_mem (fun v ↦ Valued.isOpen_valuationSubring _)
    have h₁ : ∀ᶠ u : 𝔸ᶠ[F]ˣ in 𝓝 1, ∀ v : V, u.val v ∈ v.adicCompletionIntegers F :=
      (ho.preimage Units.continuous_val).mem_nhds (fun v ↦ (v.adicCompletionIntegers F).one_mem)
    have h₂ : ∀ᶠ u : 𝔸ᶠ[F]ˣ in 𝓝 1, ∀ v : V, (u⁻¹).val v ∈ v.adicCompletionIntegers F :=
      (ho.preimage (Units.continuous_val.comp continuous_inv)).mem_nhds (by
        change ∀ v : V, (1 : 𝔸ᶠ[F]ˣ)⁻¹.val v ∈ v.adicCompletionIntegers F
        rw [inv_one]
        exact fun v ↦ (v.adicCompletionIntegers F).one_mem)
    filter_upwards [h₁, h₂] with u hu hv using fun v ↦ ⟨hu v, hv v⟩
  have hlocal (v : V) (S : Set (v.adicCompletion F)) (hS : IsCompact S) (hO : IsOpen S) :
      ∀ᶠ u : 𝔸ᶠ[F]ˣ in 𝓝 1, ∀ x : v.adicCompletion F, u.val v * x ∈ S ↔ x ∈ S := by
    let U : Set (𝔸ᶠ[F]ˣ × v.adicCompletion F) := {p | p.1.val v * p.2 ∈ S ∧ p.1⁻¹.val v * p.2 ∈ S}
    have hp : Continuous (fun u : 𝔸ᶠ[F]ˣ ↦ u.val v) := (RestrictedProduct.continuous_eval v).comp Units.continuous_val
    have ho : IsOpen U := (hO.preimage ((hp.comp continuous_fst).mul continuous_snd)).inter
      (hO.preimage ((hp.comp continuous_fst.inv).mul continuous_snd))
    have hsub : ({1} : Set 𝔸ᶠ[F]ˣ) ×ˢ S ⊆ U := by
      rintro ⟨u, x⟩ ⟨hu, hx⟩
      obtain rfl : u = 1 := hu
      change (1 : v.adicCompletion F) * x ∈ S ∧ 1 * x ∈ S
      simpa using hx
    obtain ⟨W, T, hW, _, h1, hT, hWT⟩ := generalized_tube_lemma isCompact_singleton hS ho hsub
    filter_upwards [hW.mem_nhds (h1 (mem_singleton 1))] with u hu
    intro x
    have he (z) (hz : z ∈ S) := hWT (show (u, z) ∈ W ×ˢ T from ⟨hu, hT hz⟩)
    refine ⟨fun hz ↦ ?_, fun hz ↦ (he x hz).1⟩
    have hinv : u⁻¹.val v * u.val v = 1 := congrArg (fun t : 𝔸ᶠ[F] ↦ t v) u.inv_val
    simpa only [← mul_assoc, hinv, one_mul] using (he _ hz).2
  obtain ⟨r, c, φ, K, g, -, hg, rfl⟩ := adeleSchwartz_eq_sum_compactOpen_rectangles F f
  have hrect (i : Fin r) : ∀ᶠ u : 𝔸ᶠ[F]ˣ in 𝓝 1, ∀ v (z : v.adicCompletion F),
      u.val v * z ∈ K i v ↔ z ∈ K i v := by
    let A : Set V := {v | K i v ≠ (v.adicCompletionIntegers F : Set _)}
    have hA : A.Finite := (hg i).2.1
    have happ := hA.eventually_all.mpr (fun v _ ↦ hlocal v (K i v) ((hg i).1 v).1 ((hg i).1 v).2)
    filter_upwards [happ, hunit] with u hu hu'
    intro v z
    by_cases hv : v ∈ A
    · exact hu _ hv z
    · have he : K i v = (v.adicCompletionIntegers F : Set _) := not_not.mp hv
      rw [he]
      have hinv : u⁻¹.val v * u.val v = 1 := congrArg (fun t : 𝔸ᶠ[F] ↦ t v) u.inv_val
      change u.val v * z ∈ (v.adicCompletionIntegers F).toSubring ↔ z ∈ (v.adicCompletionIntegers F).toSubring
      exact ⟨fun h ↦ by simpa only [← mul_assoc, hinv, one_mul] using
        (v.adicCompletionIntegers F).toSubring.mul_mem (hu' v).2 h, fun h ↦ (v.adicCompletionIntegers F).toSubring.mul_mem (hu' v).1 h⟩
  filter_upwards [eventually_all.mpr hrect] with u hu
  intro x
  change schwartzBruhatEvalCLM (Multiplicative.ofAdd (x.1, u.val * x.2)) (∑ i, c i • g i) =
    schwartzBruhatEvalCLM (Multiplicative.ofAdd x) (∑ i, c i • g i)
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (c i • ·)
  change g i (Multiplicative.ofAdd (x.1, u.val * x.2)) = g i (Multiplicative.ofAdd x)
  rw [(hg i).2.2 (x.1, u.val * x.2), (hg i).2.2 x]
  simp only [Set.indicator, Set.mem_ofPred_eq]
  exact congrArg (fun p : Prop ↦ _ * (if p then (1 : ℂ) else 0)) (propext (forall_congr' fun v ↦ hu i v (x.2 v)))

open scoped Pointwise in
/-- Lift a sufficiently small compact structural kernel through a locally injective
open quotient. Its lifted points can all be chosen inside the prescribed neighborhood. -/
private theorem theta_small_kernel_lift {P X : Type*} [CommGroup P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
    [T2Space X] [LocallyCompactSpace X] (q : P →ₜ* X) (hq : IsOpenMap q)
    (hi : IsLocallyInjective q) {U : Set P} (hU : U ∈ 𝓝 1) :
    ∃ K : Subgroup X, IsCompact (K : Set X) ∧ IsBruhatGoodSubgroup K ∧
      ∃ j : K →* P, (∀ k, j k ∈ U) ∧ ∀ k, q (j k) = k.val := by
  classical
  obtain ⟨V, hV, h1V, hiV⟩ := hi 1
  obtain ⟨W, hW, h1W, hWW⟩ := exists_open_nhds_one_mul_subset (inter_mem (hV.mem_nhds h1V) hU)
  have hWV (x : P) (hx : x ∈ W) : x ∈ V ∩ U := hWW (mul_one x ▸ Set.mul_mem_mul hx h1W)
  obtain ⟨A, hA⟩ := exists_lcaDualAnnihilator_subset_nhds ((hq W hW).mem_nhds
    (show (1 : X) ∈ q '' W from ⟨1, h1W, map_one q⟩))
  let K := lcaDualAnnihilator A.val
  have hkc : IsCompact (K : Set X) := isCompact_lcaDualAnnihilator _ A.property.1
  have hgood : IsBruhatGoodSubgroup K := by
    have he : lcaAnnihilator K = A.val := lcaAnnihilator_dualAnnihilator_of_open _ A.property.1
    exact ⟨hkc.isClosed, he.symm ▸ A.property⟩
  choose j hjW hj using fun k : K ↦ hA k.property
  let J : K →* P :=
    { toFun := j
      map_one' := hiV (hWV _ (hjW 1)).1 h1V ((hj 1).trans q.map_one.symm)
      map_mul' k l := hiV (hWV _ (hjW _)).1 (hWW (Set.mul_mem_mul (hjW k) (hjW l))).1 (by
        rw [map_mul, hj, hj, hj]; rfl) }
  exact ⟨K, hkc, hgood, J, fun k ↦ (hWV _ (hjW k)).2, hj⟩

/-- The archimedean units have an identity neighborhood containing no nontrivial subgroup. -/
private theorem theta_arch_small_powers (F : Type*) [Field F] [NumberField F] :
    ∃ U ∈ 𝓝 (1 : (InfiniteAdeleRing F)ˣ), ∀ g : (InfiniteAdeleRing F)ˣ, (∀ n : ℕ, g ^ n ∈ U) → g = 1 := by
  classical
  let V := mixedEmbedding.mixedSpace F
  let e := Units.mapEquiv (InfiniteAdeleRing.ringEquiv_mixedSpace F).toMulEquiv
  let h := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have he : Continuous e := (continuous_ringEquiv_mixedSpace (F := F)).units_map h.toMonoidHom
  let k := Module.finrank ℝ V
  let L : V ≃L[ℝ] EuclideanSpace ℝ (Fin k) := ContinuousLinearEquiv.ofFinrankEq (by simp [k])
  have hv : IsLocallyEuclidean Vˣ := by
    let E := (L.toHomeomorph.isOpenEmbedding.comp (Units.isOpenEmbedding_val (R := V))).toOpenPartialHomeomorph
    apply isLocallyEuclidean_of_chart_at_one E
    simp [E]
  obtain ⟨U, hU, hpow⟩ := exists_nhds_one_of_isLocallyEuclidean hv
  refine ⟨e ⁻¹' U, he.continuousAt.preimage_mem_nhds (map_one e ▸ hU), fun g hg ↦ e.injective ?_⟩
  rw [map_one]
  exact hpow _ fun n ↦ map_pow e g n ▸ hg n

/-- Choose a compact structural kernel which acts trivially on the theta sum. Its lifts have
trivial archimedean component and stabilize the finite part of the test. -/
private theorem theta_stable_kernel (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
    ∃ K : Subgroup C[F], IsCompact (K : Set C[F]) ∧ IsBruhatGoodSubgroup (G := C[F]) K ∧
      ∀ k : K, ∀ g : C[F], adelicTheta f (k.val * g) = adelicTheta f g := by
  let N := IdeleGroup.principalSubgroup (𝓞 F) F
  let q : 𝕀[F] →ₜ* C[F] := ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) 𝔸ᶠ[F]
  obtain ⟨W, hW, hpow⟩ := theta_arch_small_powers F
  let V : Set 𝔸ᶠ[F]ˣ := {u | ∀ x : 𝔸[F], f (Multiplicative.ofAdd (x.1, u.val * x.2)) = f (Multiplicative.ofAdd x)}
  have hV : V ∈ 𝓝 1 := theta_finite_stabilizer f
  have hU : e ⁻¹' (W ×ˢ V) ∈ 𝓝 1 := e.continuous.continuousAt.preimage_mem_nhds (by
    change _ ∈ 𝓝 (e 1); rw [map_one]; exact prod_mem_nhds hW hV)
  have hcov : IsCoveringMap q := (N.isQuotientCoveringMap ((ideleGroup_quotient.{_, 0} F).2.2.1)).isCoveringMap
  obtain ⟨K, hK, hg, j, hj, hq⟩ := theta_small_kernel_lift (P := 𝕀[F]) (X := C[F]) q (QuotientGroup.isOpenMap_coe (N := N)) hcov.isLocalHomeomorph.isLocallyInjective hU
  refine ⟨K, hK, hg, fun k g ↦ ?_⟩
  have ha : (e (j k)).1 = 1 := hpow _ fun n ↦ by
    have hh := (hj (k ^ n)).1
    simpa only [map_pow, Prod.pow_fst] using hh
  have hx (x : 𝔸[F]) : f (Multiplicative.ofAdd ((j k).val * x)) = f (Multiplicative.ofAdd x) := by
    have he : (j k).val.1 = 1 := congrArg Units.val ha
    have hh := (hj k).2 x
    change f (Multiplicative.ofAdd ((j k).val.1 * x.1, (j k).val.2 * x.2)) = _
    rw [he, one_mul]
    exact hh
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← hq k]
  change adelicTheta f (classOf (j k) * classOf a) = adelicTheta f (classOf a)
  rw [← QuotientGroup.mk_mul, adelicTheta_mk, adelicTheta_mk]
  apply tsum_congr
  intro ξ
  rw [Units.val_mul, mul_left_comm]
  apply hx

open Topology in
open scoped ContDiff in
/-- On an elementary quotient, descend just those family members which are constant on the
fibres. Differentiating the invariance identity keeps every derivative in this subfamily.
The same derivative index works across all discrete fibres of the elementary cover. -/
private theorem theta_elementary_family {X I : Type*} [CommGroup X] [TopologicalSpace X]
    {m n r : ℕ} {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
    (p : X →ₜ* Multiplicative (ElementaryLieGroup m n r B)) (hp : IsQuotientMap p)
    (Φ : I → X → ℂ) (hc : ∀ i, Continuous (Φ i))
    (hdir : ∀ v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n),
      ∃ u : Multiplicative ℝ →ₜ* X,
        (∀ t : ℝ, p (u (Multiplicative.ofAdd t)) = Multiplicative.ofAdd (elementaryCover (t • v) 0 0)) ∧
        ∀ i, ∃ j, ∀ g, HasDerivAt (fun t : ℝ ↦ Φ i (u (Multiplicative.ofAdd t) * g)) (Φ j g) 0)
    (hb : ∀ (i : I) (α : Fin m → ℕ) (δ : Fin r → ℕ), ∃ C : ℝ, ∀ g : X,
      ‖((∏ k, (((p g).toAdd.1 k : ℝ) : ℂ) ^ α k) * (∏ k, (((p g).toAdd.2.2.1 k : ℤ) : ℂ) ^ δ k)) * Φ i g‖ ≤ C)
    (i₀ : I) (hi₀ : ∀ x y, p x = p y → Φ i₀ x = Φ i₀ y) :
    ∃ s : elementarySchwartzSubmodule m n r B, ∀ g : X, s.val (p g).toAdd = Φ i₀ g := by
  classical
  let E := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let J := {i : I // ∀ x y, p x = p y → Φ i x = Φ i y}
  let s (i : J) (z : ElementaryLieGroup m n r B) := Φ i.val (hp.surjective (Multiplicative.ofAdd z)).choose
  have hs (i : J) (g : X) : s i (p g).toAdd = Φ i.val g := i.property _ _ (hp.surjective (p g)).choose_spec
  have hcs (i : J) : Continuous (s i) := by
    change Continuous (fun z : Multiplicative (ElementaryLieGroup m n r B) ↦ s i z.toAdd)
    apply hp.continuous_iff.mpr
    rw [show (fun z : Multiplicative (ElementaryLieGroup m n r B) ↦ s i z.toAdd) ∘ p = Φ i.val from funext (hs i)]
    exact hc i.val
  let φ (i : J) (b : (Fin r → ℤ) × B) (x : E) := s i (elementaryCover x b.1 b.2)
  have hφ (i : J) (b : (Fin r → ℤ) × B) : Continuous (φ i b) := by
    apply (hcs i).comp
    exact continuous_fst.prodMk ((continuous_pi fun j ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ j).comp continuous_snd)).prodMk continuous_const)
  have hd (v : E) (i : J) : ∃ j : J, ∀ b x,
      HasDerivAt (fun t : ℝ ↦ φ i b (x + t • v)) (φ j b x) 0 := by
    obtain ⟨u, hu, h⟩ := hdir v
    obtain ⟨j, hj⟩ := h i.val
    have hInv : ∀ x y, p x = p y → Φ j x = Φ j y := by
      intro x y he
      have hxy : (fun t : ℝ ↦ Φ i.val (u (Multiplicative.ofAdd t) * x)) = fun t : ℝ ↦ Φ i.val (u (Multiplicative.ofAdd t) * y) :=
        funext fun t ↦ i.property _ _ (by rw [map_mul, map_mul, he])
      exact (hxy ▸ hj x).unique (hj y)
    let d : J := ⟨j, hInv⟩
    refine ⟨d, fun b x ↦ ?_⟩
    obtain ⟨z, hz⟩ := hp.surjective (Multiplicative.ofAdd (elementaryCover x b.1 b.2))
    have heq (t : ℝ) : p (u (Multiplicative.ofAdd t) * z) = Multiplicative.ofAdd (elementaryCover (x + t • v) b.1 b.2) := by
      rw [map_mul, hu, hz]
      change elementaryCover (t • v) 0 0 + elementaryCover x b.1 b.2 = _
      have hcov := map_add (elementaryCoverZeroHom (r := r) (F := B)) (t • v) x
      rw [add_comm x]
      exact Prod.ext rfl (Prod.ext (congrArg (fun w : ElementaryLieGroup m n r B ↦ w.2.1) hcov).symm (zero_add _))
    have hfun (t : ℝ) : φ i b (x + t • v) = Φ i.val (u (Multiplicative.ofAdd t) * z) :=
      (congrArg (fun w : Multiplicative (ElementaryLieGroup m n r B) ↦ s i w.toAdd) (heq t).symm).trans (hs i _)
    have hval : φ d b x = Φ j z :=
      (congrArg (fun w : Multiplicative (ElementaryLieGroup m n r B) ↦ s d w.toAdd) hz.symm).trans (hs d _)
    simpa only [hfun, hval] using hj z
  choose D hD using hd
  obtain ⟨hsm, hder⟩ := contDiff_family_of_hasDerivAt_lines φ D hφ (fun i b x v ↦ hD v i b x)
  let i' : J := ⟨i₀, hi₀⟩
  refine ⟨⟨s i', fun a b ↦ hsm i' (a, b), fun idx ↦ ?_⟩, hs i'⟩
  let directions : List E := (List.ofFn (fun k : Fin m ↦ List.replicate (idx.2.1 k) (EuclideanSpace.single k 1, 0))).flatten ++
    (List.ofFn (fun k : Fin n ↦ List.replicate (idx.2.2.1 k) (0, EuclideanSpace.single k 1))).flatten
  obtain ⟨j, hj⟩ := hder directions.length directions.get i'
  obtain ⟨C, hC⟩ := hb j.val idx.1 idx.2.2.2
  refine lt_of_le_of_lt (iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_) (ENNReal.ofReal_lt_top (r := C))
  obtain ⟨g, hg⟩ := hp.surjective (Multiplicative.ofAdd (elementaryCover x a b))
  have he : elementaryPartial (s i') idx.2.1 idx.2.2.1 x a b = s j (elementaryCover x a b) := hj (a, b) x
  have hv := hC g
  rw [← hs j g, hg] at hv
  rw [he]
  exact (show (‖_‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖_‖ from (ENNReal.ofReal_eq_coe_nnreal _).symm).trans_le (ENNReal.ofReal_le_ofReal hv)

/-- Each real or integer coordinate on the quotient is a real homomorphism. When they factor
through one logarithmic coordinate, its moment bounds control every coordinate monomial. -/
private theorem theta_coordinate_weights {X I : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
    {m n r : ℕ} {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    (p : X →ₜ* Multiplicative (ElementaryLieGroup m n r B))
    (l : X →ₜ* Multiplicative ℝ)
    (hfac : ∀ u : X →ₜ* Multiplicative ℝ, ∃ c : ℝ, ∀ x, (u x).toAdd = c * (l x).toAdd)
    (Φ : I → X → ℂ) (hb : ∀ i (k : ℕ), ∃ C : ℝ, ∀ x, |(l x).toAdd| ^ k * ‖Φ i x‖ ≤ C)
    (i : I) (α : Fin m → ℕ) (δ : Fin r → ℕ) : ∃ C : ℝ, ∀ g : X,
      ‖((∏ k, (((p g).toAdd.1 k : ℝ) : ℂ) ^ α k) * (∏ k, (((p g).toAdd.2.2.1 k : ℤ) : ℂ) ^ δ k)) * Φ i g‖ ≤ C := by
  classical
  have hc := continuous_toAdd.comp p.continuous
  let u (k : Fin m) : X →ₜ* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd ((p x).toAdd.1 k)
      continuous_toFun := (PiLp.continuous_apply 2 _ k).comp hc.fst
      map_one' := by rw [map_one]; rfl
      map_mul' x y := by rw [map_mul]; rfl }
  let v (k : Fin r) : X →ₜ* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (((p x).toAdd.2.2.1 k : ℤ) : ℝ)
      continuous_toFun := (continuous_of_discreteTopology (f := ((↑) : ℤ → ℝ))).comp ((continuous_apply k).comp hc.snd.snd.fst)
      map_one' := by rw [map_one]; exact (Int.cast_zero : ((0 : ℤ) : ℝ) = 0)
      map_mul' x y := by rw [map_mul]; exact (Int.cast_add ((p x).toAdd.2.2.1 k) ((p y).toAdd.2.2.1 k) (R := ℝ)) }
  choose c hcr using fun k ↦ hfac (u k)
  choose d hcd using fun k ↦ hfac (v k)
  let A := (∏ k, (c k : ℂ) ^ α k) * (∏ k, (d k : ℂ) ^ δ k)
  obtain ⟨C, hC⟩ := hb i ((∑ k, α k) + (∑ k, δ k))
  refine ⟨‖A‖*C, fun g ↦ ?_⟩
  have h₁ (k) : (((p g).toAdd.1 k : ℝ) : ℂ) = (c k : ℂ) * ((l g).toAdd : ℂ) := by exact_mod_cast hcr k g
  have h₂ (k) : (((p g).toAdd.2.2.1 k : ℤ) : ℂ) = (d k : ℂ) * ((l g).toAdd : ℂ) := by
    have he := congrArg Complex.ofReal (hcd k g)
    change (((((p g).toAdd.2.2.1 k : ℤ) : ℝ)) : ℂ) = ↑(d k * (l g).toAdd) at he
    exact_mod_cast he
  have he : ((∏ k, (((p g).toAdd.1 k : ℝ) : ℂ) ^ α k) * (∏ k, (((p g).toAdd.2.2.1 k : ℤ) : ℂ) ^ δ k)) =
      A * ((l g).toAdd : ℂ) ^ ((∑ k, α k) + (∑ k, δ k)) := by
    simp only [h₁, h₂, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add, A]
    ring
  rw [he, mul_assoc, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg A)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact hC g

private theorem theta_continuous_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) :
    Continuous (fun t : ℝ ↦ t • v) := continuous_id.smul continuous_const

private def theta_cover_line {m n r : ℕ} {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    (v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    Multiplicative ℝ →ₜ* Multiplicative (ElementaryLieGroup m n r B) :=
  let E := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let c := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := B)
  ⟨(c.comp (LinearMap.toSpanSingleton ℝ E v).toAddMonoidHom).toMultiplicative,
   show Continuous (fun t : ℝ ↦ c (t • v)) from elementaryCoverZeroHom_continuous_isOpenMap.1.comp
     (theta_continuous_line v)⟩

open Topology in
/-- Realize a kernel-invariant function on a single elementary stage of a group split over
the positive reals. Compactness of the norm kernel controls the polynomial weights, and
one - parameter subgroups lift through the compact structural kernel. -/
private theorem theta_on_split_group {X I : Type*} [CommGroup X] [TopologicalSpace X]
    [IsTopologicalGroup X] [T2Space X] [LocallyCompactSpace X] (n : X →* ℝ≥0ˣ) (hn : Continuous n)
    (τ : ℝ≥0ˣ →ₜ* X) (hτ : RightInverse τ n) (hp : IsProperMap n)
    (K : Subgroup X) (hK : IsCompact (K : Set X)) (hgood : IsBruhatGoodSubgroup K)
    (Φ : I → X → ℂ) (hΦ : ∀ i, Continuous (Φ i))
    (hbound : ∀ i (k : ℕ), ∃ C : ℝ, ∀ g, |(logNormHom n hn g).toAdd| ^ k * ‖Φ i g‖ ≤ C)
    (hder : ∀ u : LCATopologicalLie X, ∀ i, ∃ j, ∀ g,
      HasDerivAt (fun t : ℝ ↦ Φ i (u (Multiplicative.ofAdd t) * g)) (Φ j g) 0)
    (i₀ : I) (hinv : ∀ k : K, ∀ g, Φ i₀ (k.val * g) = Φ i₀ g) :
    Φ i₀ ∈ schwartzBruhatSubmodule X := by
  classical
  have hk : IsCompact (n.ker : Set X) := hp.isCompact_preimage (isCompact_singleton (x := (1 : ℝ≥0ˣ)))
  have hgen := compactlyGenerated_of_split (H := X) n τ hτ hk
  let a := topWithKernel (H := X) hgen K hgood
  let e := Classical.choice a.elementary
  let A := topQuotEquiv (H := X) hgen K hgood
  let Z := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let E := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
  let q : X →ₜ* X ⧸ K := ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩
  let B : X ⧸ K ≃ₜ* Multiplicative Z := A.symm.trans e.equiv
  let p := (B : X ⧸ K →ₜ* Multiplicative Z).comp q
  have hp : IsQuotientMap p := B.toHomeomorph.isQuotientMap.comp (QuotientGroup.isQuotientMap_mk K)
  have hdir (v : E) : ∃ u : Multiplicative ℝ →ₜ* X,
      (∀ t : ℝ, p (u (Multiplicative.ofAdd t)) = Multiplicative.ofAdd (elementaryCover (t • v) 0 0)) ∧
      ∀ i, ∃ j, ∀ g, HasDerivAt (fun t : ℝ ↦ Φ i (u (Multiplicative.ofAdd t) * g)) (Φ j g) 0 := by
    let L : Multiplicative ℝ →ₜ* Multiplicative Z := theta_cover_line v
    let d := (B.symm : Multiplicative Z →ₜ* X ⧸ K).comp L
    obtain ⟨u, hu⟩ := oneParameterMap_quotient_surjective (X := X) K hK (Additive.ofMul d)
    refine ⟨u.toMul, fun t ↦ ?_, fun i ↦ ?_⟩
    · have hq (t) : q (u.toMul t) = B.symm (L t) := congrArg (fun z : OneParameterSpace (X ⧸ K) ↦ z.toMul t) hu
      change B (q _) = _
      rw [hq, B.apply_symm_apply]
      rfl
    · exact hder u.toMul i
  let r := τ.comp (posExpEquiv : Multiplicative ℝ →ₜ* ℝ≥0ˣ)
  have hr : RightInverse r (logNormHom n hn) := fun t ↦ (congrArg posExpEquiv.symm (hτ (posExpEquiv t))).trans (posExpEquiv.symm_apply_apply t)
  have hfac := realHom_factors (G := X) (logNormHom n hn) r hr (logNorm_compact_kernel (X := X) n hn hk)
  have hb := theta_coordinate_weights p (logNormHom n hn) hfac Φ hbound
  have hInv (x y : X) (he : p x = p y) : Φ i₀ x = Φ i₀ y := by
    have hxy : x / y ∈ K := QuotientGroup.eq_iff_div_mem.mp (show q x = q y from B.injective he)
    simpa only [div_mul_cancel] using hinv ⟨x / y, hxy⟩ y
  obtain ⟨s, hs⟩ := theta_elementary_family p hp Φ hΦ hdir hb i₀ hInv
  apply Submodule.mem_iSup_of_mem a
  apply Submodule.mem_iSup_of_mem e
  refine ⟨s, funext fun x ↦ ?_⟩
  let z : a.val.1 := ⟨x, Subgroup.mem_top _⟩
  have hz : A (QuotientGroup.mk z) = q x := rfl
  have he : p x = e.equiv (QuotientGroup.mk z) := by
    change e.equiv (A.symm (q x)) = _
    rw [← hz, A.symm_apply_apply]
  exact (stageRealization_of_mem a e s x (Subgroup.mem_top _)).trans ((congrArg (fun t : Multiplicative Z ↦ s.val t.toAdd) he.symm).trans (hs x))

private theorem hasDerivAt_of_exp_quotient (v : ℝ → ℂ) (d : ℂ)
    (h : Tendsto (fun t : ℝ ↦ (v t - v 0) / ((Real.exp t : ℂ) - 1)) (𝓝[≠] 0) (𝓝 d)) :
    HasDerivAt v d 0 := by
  have hs : Tendsto (fun t : ℝ ↦ ((Real.exp t : ℂ) - 1) / (t : ℂ)) (𝓝[≠] 0) (𝓝 1) := by
    have hh := (Complex.continuous_ofReal.tendsto _).comp (Real.hasDerivAt_exp 0).tendsto_slope
    simpa [slope_def_field, Function.comp_def] using hh
  rw [hasDerivAt_iff_tendsto_slope, ← mul_one d]
  apply (h.mul hs).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (Real.exp t : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (show Real.exp t ≠ 1 by simpa using (show t ≠ 0 from ht)))
  simp only [slope_def_module, sub_zero, Complex.real_smul, Complex.ofReal_inv]
  field_simp

/-- Reparametrize the positive-real theta difference quotient by exponential time. -/
private theorem theta_orbit_derivative (γ : Multiplicative ℝ →ₜ* 𝕀[F])
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) (g : C[F]) :
    HasDerivAt (fun t : ℝ ↦ adelicTheta f (classOf (γ (Multiplicative.ofAdd t)) * g))
      (adelicTheta (adeleDirectionalDeriv (γ.comp (posExpEquiv.symm : ℝ≥0ˣ →ₜ* _)) f) g) 0 := by
  let E (t : ℝ) := posExpEquiv (Multiplicative.ofAdd t)
  have h0 : E 0 = 1 := posExpEquiv.map_one
  have hlim : Tendsto E (𝓝[≠] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨h0 ▸ (posExpEquiv.continuous.comp continuous_ofAdd).continuousAt.continuousWithinAt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact fun he ↦ hs ((posExpEquiv.injective (he.trans h0.symm)) : s = 0)
  have hθ := (adelicTheta_directionalDeriv (γ.comp (posExpEquiv.symm : ℝ≥0ˣ →ₜ* _)) f g).comp hlim
  apply hasDerivAt_of_exp_quotient
  refine hθ.congr' (.of_forall fun t ↦ ?_)
  have hγ : γ.comp (posExpEquiv.symm : ℝ≥0ˣ →ₜ* _) (E t) = γ (Multiplicative.ofAdd t) :=
    congrArg γ (posExpEquiv.symm_apply_apply _)
  have hz : classOf (γ (Multiplicative.ofAdd (0 : ℝ))) * g = g := by
    change classOf (γ 1) * g = g
    exact (congrArg (fun x : 𝕀[F] ↦ classOf x * g) γ.map_one).trans (one_mul g)
  simp only [Function.comp_apply, hγ, hz]
  rfl

private def thetaLog (F : Type*) [Field F] [NumberField F] : C[F] →ₜ* Multiplicative ℝ :=
  logNormHom (X := C[F]) (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous

private theorem thetaLog_apply (g : C[F]) : ((thetaLog F) g).toAdd = Real.log (((ideleClassNorm F g).val : ℝ)) :=
  (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g)))).symm

private def thetaTwist (a : ℝ) (f : SchwartzBruhat (Multiplicative 𝔸[F])) (g : C[F]) : ℂ :=
  (Real.exp (a * ((thetaLog F) g).toAdd) : ℂ) * adelicTheta f g

private theorem thetaTwist_continuous (a : ℝ) (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
    Continuous (thetaTwist a f) :=
  (Complex.continuous_ofReal.comp ((continuous_const.mul (continuous_toAdd.comp (thetaLog F).continuous)).rexp)).mul (adelicTheta f).continuous

private theorem hasDerivAt_exp_affine_mul {v : ℝ → ℂ} {d : ℂ} (hv : HasDerivAt v d 0) (c b : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (Real.exp (c * t + b) : ℂ) * v t) (↑(Real.exp b) * ((c : ℂ) * v 0 + d)) 0 := by
  have hw : HasDerivAt (fun t : ℝ ↦ Real.exp (c * t + b)) (Real.exp b * c) 0 := by
    simpa using (((hasDerivAt_id' (0 : ℝ)).const_mul c).add_const b).exp
  have h := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hw).mul hv
  convert h using 1
  · rfl
  change ↑(Real.exp b) * ((c : ℂ) * v 0 + d) = (↑(Real.exp b * c) : ℂ) * v 0 + ↑(Real.exp (c * 0 + b)) * d
  rw [mul_zero, zero_add, Complex.ofReal_mul]
  ring

/-- Differentiating the real twist adds a scalar multiple of the original polar test to its
adelic directional derivative. Both terms belong to the polar subspace. -/
private theorem thetaTwist_derivative (a : ℝ) (γ : Multiplicative ℝ →ₜ* 𝕀[F])
    (f : adelePolarSubspace F) : ∃ d : adelePolarSubspace F, ∀ g : C[F],
      HasDerivAt (fun t : ℝ ↦ thetaTwist (F := F) a f.val (classOf (γ (Multiplicative.ofAdd t)) * g)) (thetaTwist (F := F) a d.val g) 0 := by
  let q : 𝕀[F] →ₜ* C[F] := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let u := (thetaLog F).comp (q.comp γ)
  let c := a * (u (Multiplicative.ofAdd 1)).toAdd
  let γ' := γ.comp (posExpEquiv.symm : ℝ≥0ˣ →ₜ* _)
  let d := adeleDirectionalDeriv (F := F) γ' f.val
  have hd : d ∈ adelePolarSubspace F := adeleDirectionalDeriv_preserves_polarSubspace γ' f.property
  refine ⟨⟨(c : ℂ) • f.val + d, (adelePolarSubspace F).add_mem ((adelePolarSubspace F).smul_mem _ f.property) hd⟩, fun g ↦ ?_⟩
  let L := ((thetaLog F) g).toAdd
  let v (t : ℝ) := adelicTheta (F := F) f.val (classOf (γ (Multiplicative.ofAdd t)) * g)
  have hv : HasDerivAt v (adelicTheta (F := F) d g) 0 := theta_orbit_derivative (F := F) γ f.val g
  have h0 : v 0 = adelicTheta (F := F) f.val g := by
    change adelicTheta (F := F) f.val (q (γ 1) * g) = _
    exact congrArg (adelicTheta (F := F) f.val) ((congrArg (fun x : 𝕀[F] ↦ q x * g) γ.map_one).trans
      ((congrArg (fun x : C[F] ↦ x * g) q.map_one).trans (one_mul g)))
  have heq (t : ℝ) : a * ((thetaLog F) (classOf (γ (Multiplicative.ofAdd t)) * g)).toAdd = c * t + a * L := by
    rw [map_mul, toAdd_mul]
    change a * ((u (Multiplicative.ofAdd t)).toAdd + L) = _
    rw [lcaTopologicalLie_real]
    dsimp [c]
    ring
  have ht (t : ℝ) : thetaTwist (F := F) a f.val (classOf (γ (Multiplicative.ofAdd t)) * g) =
      (Real.exp (c * t + a * L) : ℂ) * v t := congrArg (fun r : ℝ ↦ (Real.exp r : ℂ) * v t) (heq t)
  have hθ := adelicTheta_isLinear (F := F)
  have hd' : adelicTheta (F := F) ((c : ℂ) • f.val + d) g = (c : ℂ) * v 0 + adelicTheta (F := F) d g := by
    exact (congrArg (fun h : C(C[F], ℂ) ↦ h g) (hθ.map_add _ _)).trans
      (congrArg (fun h : C(C[F], ℂ) ↦ h g + adelicTheta (F := F) d g) (hθ.map_smul _ _)
        |>.trans (congrArg (fun z : ℂ ↦ (c : ℂ) * z + adelicTheta (F := F) d g) h0.symm))
  exact ((funext ht).symm ▸ (hasDerivAt_exp_affine_mul hv c (a * L))).congr_deriv
    (congrArg (fun z : ℂ ↦ (Real.exp (a * L) : ℂ) * z) hd'.symm)

/-- Lift an idele-class direction through the covering by ideles. -/
private theorem theta_class_derivative (w : ℝ) :
    ∀ u : LCATopologicalLie C[F], ∀ i : adelePolarSubspace F, ∃ j : adelePolarSubspace F, ∀ g : C[F],
      HasDerivAt (fun t : ℝ ↦ thetaTwist (F := F) w i.val (u (Multiplicative.ofAdd t) * g)) (thetaTwist (F := F) w j.val g) 0 := by
  let N := IdeleGroup.principalSubgroup (𝓞 F) F
  let π : 𝕀[F] →ₜ* C[F] := ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩
  have hcov : IsCoveringMap π := (N.isQuotientCoveringMap ((ideleGroup_quotient.{_, 0} F).2.2.1)).isCoveringMap
  intro u i
  have lift := oneParameterMap_surjective_of_covering (G := 𝕀[F]) (H := C[F]) π hcov (Additive.ofMul u)
  let γ := lift.choose
  have hγ := lift.choose_spec
  have hπ (t) : π (γ.toMul t) = u t := congrArg (fun z : OneParameterSpace C[F] ↦ z.toMul t) hγ
  have deriv := thetaTwist_derivative (F := F) w γ.toMul i
  refine ⟨deriv.choose, fun g ↦ ?_⟩
  have he : (fun t : ℝ ↦ thetaTwist (F := F) w i.val (π (γ.toMul (Multiplicative.ofAdd t)) * g)) =
      (fun t : ℝ ↦ thetaTwist (F := F) w i.val (u (Multiplicative.ofAdd t) * g)) :=
    funext fun t ↦ congrArg (fun z : C[F] ↦ thetaTwist (F := F) w i.val (z * g)) (hπ _)
  exact Eq.mp (congrArg (fun v : ℝ → ℂ ↦ HasDerivAt v (thetaTwist (F := F) w deriv.choose.val g) 0) he) (deriv.choose_spec g)

/-- Two-sided exponential bounds on the tails absorb any real twist and any logarithmic
moment. Properness bounds the remaining compact band. -/
private theorem log_weight_of_all_exp_rates {X : Type*} [TopologicalSpace X]
    (L : X → ℝ) (hL : IsProperMap L) (f : X → ℂ) (hf : Continuous f)
    (h : ∀ N : ℕ, ∃ C T : ℝ, 0 < C ∧ ∀ x, T < |L x| →
      ‖f x‖ ≤ C * Real.exp (-(N : ℝ) * |L x|)) (w : ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x, |L x| ^ k * ‖(Real.exp (w * L x) : ℂ) * f x‖ ≤ C := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((k : ℝ) + |w|)
  obtain ⟨C, T, hC, ht⟩ := h N
  let V (x : X) := |L x| ^ k * ‖(Real.exp (w * L x) : ℂ) * f x‖
  have hc : Continuous V := (hL.continuous.abs.pow k).mul
    (((Complex.continuous_ofReal.comp (continuous_const.mul hL.continuous).rexp).mul hf).norm)
  obtain ⟨B, hB⟩ := (hL.isCompact_preimage (isCompact_Icc (a := -T) (b := T))).bddAbove_image hc.continuousOn
  refine ⟨max C B, fun x ↦ ?_⟩
  by_cases hx : |L x| ≤ T
  · exact (hB (mem_image_of_mem V (show x ∈ L ⁻¹' Icc (-T) T from abs_le.mp hx))).trans (le_max_right _ _)
  have hpow : |L x| ^ k ≤ Real.exp ((k : ℝ) * |L x|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith only [Real.add_one_le_exp (|L x|)]) _
  have he : w * L x ≤ |w| * |L x| := (le_abs_self _).trans_eq (abs_mul _ _)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← mul_assoc]
  calc
    _ ≤ (Real.exp ((k : ℝ) * |L x|) * Real.exp (w * L x)) * (C * Real.exp (-(N : ℝ) * |L x|)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le) (ht x (lt_of_not_ge hx)) (norm_nonneg _) (by positivity)
    _ = C * Real.exp (((k : ℝ) * |L x| + w * L x) + (-(N : ℝ) * |L x|)) := by rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by
      nlinarith only [he, mul_nonneg (sub_nonneg.mpr hN.le) (abs_nonneg (L x))])) hC.le
    _ ≤ max C B := by simp

private theorem isProperMap_thetaLog (F : Type*) [Field F] [NumberField F] :
    IsProperMap (fun g : C[F] ↦ ((thetaLog F) g).toAdd) :=
  posExpEquiv.symm.toHomeomorph.isProperMap.comp (isProperMap_ideleClassNorm F)

private theorem theta_exp_estimate (f : adelePolarSubspace F) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ ∀ g : C[F], T < |((thetaLog F) g).toAdd| →
      ‖adelicTheta (F := F) f.val g‖ ≤ C * Real.exp (-(N : ℝ) * |((thetaLog F) g).toAdd|) := by
  have hf := (mem_adelePolarSubspace (F := F) f.val).mp f.property
  have h := adelicTheta_decay_both (F := F) f.val hf.1 hf.2 N
  let C := h.choose
  let T := h.choose_spec.choose
  refine ⟨C, T, h.choose_spec.choose_spec.1, fun g ↦ ?_⟩
  exact Eq.mpr (congrArg (fun v : ℝ ↦ T < |v| → ‖adelicTheta (F := F) f.val g‖ ≤ C * Real.exp (-(N : ℝ) * |v|)) (thetaLog_apply (F := F) g))
    (h.choose_spec.choose_spec.2.2 g)

private theorem thetaTwist_log_bound (a : ℝ) (f : adelePolarSubspace F) (k : ℕ) :
    ∃ C : ℝ, ∀ g : C[F], |((thetaLog F) g).toAdd| ^ k * ‖thetaTwist (F := F) a f.val g‖ ≤ C :=
  log_weight_of_all_exp_rates _ (isProperMap_thetaLog F) (adelicTheta (F := F) f.val)
    (adelicTheta (F := F) f.val).continuous (theta_exp_estimate f) a k

private theorem thetaTwist_invariant (w : ℝ) (f : SchwartzBruhat (Multiplicative 𝔸[F]))
    (K : Subgroup C[F]) (hK : IsCompact (K : Set C[F])) (hfixed : ∀ k : K, ∀ g : C[F],
      adelicTheta (F := F) f (k.val * g) = adelicTheta (F := F) f g) :
    ∀ k : K, ∀ g : C[F], thetaTwist (F := F) w f (k.val * g) = thetaTwist (F := F) w f g := by
  intro k g
  have hlog : thetaLog F k.val = 1 := compact_killed_by_real (G := C[F]) K hK (thetaLog F) k.property
  have hL : ((thetaLog F) (k.val * g)).toAdd = ((thetaLog F) g).toAdd := congrArg Multiplicative.toAdd
    (((thetaLog F).map_mul _ _).trans ((congrArg (fun z : Multiplicative ℝ ↦ z * thetaLog F g) hlog).trans (one_mul _)))
  exact congrArg₂ (fun t : ℝ ↦ fun z : ℂ ↦ (Real.exp (w * t) : ℂ) * z) hL (hfixed k g)

private theorem theta_norm_section (F : Type*) [Field F] [NumberField F] :
    ∃ τ : ℝ≥0ˣ →ₜ* C[F], RightInverse τ (ideleClassNorm F) := by
  have h := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.2.1
  exact ⟨⟨h.choose, h.choose_spec.1⟩, h.choose_spec.2⟩

private theorem theta_fixed_stage (w : ℝ) (i : adelePolarSubspace F) (K : Subgroup C[F])
    (hK : IsCompact (K : Set C[F])) (hgood : IsBruhatGoodSubgroup (G := C[F]) K)
    (hinv : ∀ k : K, ∀ g : C[F], thetaTwist (F := F) w i.val (k.val * g) = thetaTwist (F := F) w i.val g) :
    thetaTwist (F := F) w i.val ∈ schwartzBruhatSubmodule C[F] := by
  let s := theta_norm_section F
  let Φ (i : adelePolarSubspace F) := thetaTwist (F := F) w i.val
  have hbound (i : adelePolarSubspace F) (k : ℕ) : ∃ C : ℝ, ∀ g : C[F],
      |(logNormHom (X := C[F]) (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous g).toAdd| ^ k * ‖Φ i g‖ ≤ C := by
    exact thetaTwist_log_bound (F := F) w i k
  with_reducible
    exact theta_on_split_group (X := C[F]) (I := adelePolarSubspace F) (ideleClassNorm F)
      (isProperMap_ideleClassNorm F).continuous s.choose s.choose_spec (isProperMap_ideleClassNorm F)
      K hK hgood Φ (fun i ↦ thetaTwist_continuous (F := F) w i.val) hbound
      (theta_class_derivative (F := F) w) i hinv

open Topology in
private theorem theta_all_twists (f : SchwartzBruhat (Multiplicative 𝔸[F])) (hf : f ∈ adelePolarSubspace F) (w : ℝ) :
    thetaTwist (F := F) w f ∈ schwartzBruhatSubmodule C[F] := by
  classical
  have fixed := theta_stable_kernel (F := F) f
  let K := fixed.choose
  have hK := fixed.choose_spec.1
  have hgood := fixed.choose_spec.2.1
  have hfixed := fixed.choose_spec.2.2
  exact theta_fixed_stage (F := F) w ⟨f, hf⟩ K hK hgood (thetaTwist_invariant (F := F) w f K hK hfixed)

end PolarTheta

/-- Paper: Remark 9.2.0.1, p. 403. Theta sends a polar test into the test space of
the two-sided Fourier–Mellin transform on the idele class group. -/
theorem adelicTheta_mem_modulatedExponentialDecay_of_polar
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) (_hf : f ∈ adelePolarSubspace F) :
    (adelicTheta (F := F) f : C[F] → ℂ) ∈ modulatedExponentialDecaySubmodule m[F] univ := by
  simp only [modulatedExponentialDecaySubmodule, Submodule.mem_iInf, Submodule.mem_comap]
  intro w
  convert theta_all_twists (F := F) f _hf w.val using 1
  ext g
  change ((↑((ideleClassNorm F g).val) ^ w.val : ℝ) : ℂ) * adelicTheta f g = _
  rw [Real.rpow_def_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
  simp only [thetaTwist, thetaLog_apply, mul_comm]

-- The canonical measure in §D.2 takes second countability as a typeclass argument.
variable [SecondCountableTopology C[F]]

/-- Paper: Remark 9.2.0.1, p. 403. The idele class Tamagawa measure is the canonical
modulated Haar measure times the Tamagawa mass of the norm-one classes. -/
theorem ideleClassTamagawaMeasure_eq_smul_canonical :
    ideleClassTamagawaMeasure F =
      (normOneIdeleClassTamagawaMeasure F) univ • canonicalModulatedHaar m[F] hm[F] := by
  let K := (ideleClassNorm F).ker
  let Q := C[F] ⧸ K
  let μC := ideleClassTamagawaMeasure F
  let μ₁ := normOneIdeleClassTamagawaMeasure F
  have hV := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  have hW := hV.2.2.2.2.2.2
  obtain ⟨hKc, hKcpt, hK₂, -⟩ := ideleClassGroup_finiteness F
  have : CompactSpace K := hKcpt
  have : μC.IsHaarMeasure := hV.2.2.1.1
  have : μC.Regular := hV.2.2.1.2.1
  have : μ₁.IsHaarMeasure := hV.2.2.2.1
  have : μ₁.Regular := hV.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, hn, hsurj, ⟨s, hs, hsn⟩, -⟩ := ideleGroup_quotient.{_, 0} F
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SFinite (positiveRealHaar : Measure ℝ≥0ˣ) := by unfold positiveRealHaar; infer_instance
  -- The band of norms between 1 and e has `dt/t`-mass one.
  let S : Set ℝ≥0ˣ := {t | ((t.val : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1)}
  have hSm : MeasurableSet S :=
    (NNReal.continuous_coe.comp Units.continuous_val).measurable measurableSet_Icc
  have hPRS : positiveRealHaar S = 1 := by
    let T : ℝ≥0ˣ := Units.mk0 (Real.exp 1).toNNReal (by positivity)
    have hT : ((T.val : ℝ≥0) : ℝ) = Real.exp 1 := Real.coe_toNNReal _ (Real.exp_pos 1).le
    have h := positiveRealHaar_interval T (by rw [hT]; exact Real.one_le_exp zero_le_one)
    rw [hT, Real.log_exp, ENNReal.ofReal_one] at h
    exact h
  let B : Set C[F] := ideleClassNorm F ⁻¹' S
  have hBm : MeasurableSet B := (hn.measurable) hSm
  -- The canonical measure gives the band mass one.
  have : CompactSpace m[F].toMonoidHom.ker := isCompact_iff_compactSpace.mp hm[F].isCompact_ker
  obtain ⟨τ', hτ'⟩ := hm[F].exists_section
  let r : ℝ≥0ˣ →ₜ* m[F].toMonoidHom.range :=
    ⟨(MonoidHom.id ℝ≥0ˣ).codRestrict _ fun t ↦ hsurj t, continuous_id.subtype_mk _⟩
  let τ : ℝ≥0ˣ →ₜ* C[F] := τ'.comp r
  have hτ : RightInverse τ m[F] := fun t ↦ hτ' (r t)
  let μ₀ : Measure m[F].toMonoidHom.ker := Measure.haarMeasure ⊤
  have hcan := canonicalModulatedHaar_eq_map_prod m[F] hm[F] τ hτ μ₀ Measure.haarMeasure_self
  have hφ : Continuous fun z : m[F].toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : C[F]) * τ z.2 := by fun_prop
  have hcanB : canonicalModulatedHaar m[F] hm[F] B = 1 := by
    rw [hcan, Measure.map_apply hφ.measurable hBm]
    have hpre : (fun z : m[F].toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : C[F]) * τ z.2) ⁻¹' B =
        univ ×ˢ S := by
      ext ⟨k, t⟩
      have hk : ideleClassNorm F (k : C[F]) = 1 := k.property
      change ideleClassNorm F ((k : C[F]) * τ t) ∈ S ↔ _
      rw [map_mul, hk, one_mul, show ideleClassNorm F (τ t) = t from hτ t]
      simp
    rw [hpre, Measure.prod_prod, show μ₀ univ = 1 from Measure.haarMeasure_self, one_mul, hPRS]
  -- Weil's formula computes the class measure of the band.
  let : MeasurableSpace Q := borel Q
  have : BorelSpace Q := ⟨rfl⟩
  let e₀ := QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) s hsn
  let e : Q ≃ₜ* ℝ≥0ˣ :=
    { e₀ with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr hn
      continuous_invFun := QuotientGroup.continuous_mk.comp hs }
  have he : MeasurableEmbedding (QuotientGroup.kerLift (ideleClassNorm F)) :=
    e.toHomeomorph.measurableEmbedding
  have hkerLift (q : Q) : QuotientGroup.kerLift (ideleClassNorm F) q = ideleClassNorm F q.out := by
    conv_lhs => rw [← Quotient.out_eq' q]
    rfl
  have hScpt : IsCompact S := by
    let h := Nonneg.unitsHomeomorphPos ℝ
    have hK : IsCompact {y : {x : ℝ // 0 < x} | y.val ∈ Icc 1 (Real.exp 1)} := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      convert isCompact_Icc (a := (1 : ℝ)) (b := Real.exp 1) using 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, by linarith [hx.1]⟩, hx, rfl⟩
    have hSeq : S = h ⁻¹' {y | y.val ∈ Icc 1 (Real.exp 1)} := rfl
    rw [hSeq, ← h.image_symm]
    exact hK.image h.symm.continuous
  have hBcpt : IsCompact B := (isProperMap_ideleClassNorm F).isCompact_preimage hScpt
  let f : C[F] → ℂ := B.indicator fun _ ↦ 1
  have hfint : Integrable f μC :=
    (integrable_indicator_iff hBm).mpr (integrableOn_const hBcpt.measure_lt_top.ne)
  have hL1 := (weilQuotientIntegral_L1 K hKc μC μ₁ _ hW hfint).2.2
  let B' : Set Q := QuotientGroup.kerLift (ideleClassNorm F) ⁻¹' S
  have hB'm : MeasurableSet B' := he.measurable hSm
  have hcoset (q : Q) : lcaCosetIntegral K μ₁ f q = (μ₁.real univ : ℂ) * B'.indicator 1 q := by
    have hf (h : K) : f (q.out * (h : C[F])) = f q.out := by
      have hh : ideleClassNorm F (h : C[F]) = 1 := h.property
      simp only [f, B, indicator, mem_preimage, map_mul, hh, mul_one]
    simp only [lcaCosetIntegral, hf, integral_const, Complex.real_smul, measureReal_def]
    congr 1
    simp only [f, B, B', indicator, mem_preimage, hkerLift, Pi.one_apply]
  have hlhs : ∫ x, f x ∂μC = (μC.real B : ℂ) := by
    simp only [f, integral_indicator hBm, setIntegral_const, Complex.real_smul, mul_one]
  have hrhs : ∫ q, lcaCosetIntegral K μ₁ f q
      ∂(positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))) =
        (μ₁.real univ : ℂ) := by
    have hdt : (positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))).real B' = 1 := by
      have hsurj' : Surjective (QuotientGroup.kerLift (ideleClassNorm F)) := e.surjective
      rw [measureReal_def, he.comap_apply, show QuotientGroup.kerLift (ideleClassNorm F) '' B' = S
        from image_preimage_eq S hsurj', hPRS, ENNReal.toReal_one]
    simp only [hcoset, integral_const_mul]
    erw [integral_indicator hB'm]
    simp only [Pi.one_apply, setIntegral_const, Complex.real_smul, mul_one, hdt,
      Complex.ofReal_one]
  have hμCB : μC B = μ₁ univ := by
    have h : μC.real B = μ₁.real univ := by exact_mod_cast hlhs.symm.trans (hL1.trans hrhs)
    rwa [measureReal_def, measureReal_def,
      ENNReal.toReal_eq_toReal_iff' hBcpt.measure_lt_top.ne (measure_ne_top _ _)] at h
  -- Compare the two Haar measures on the band.
  have : (canonicalModulatedHaar m[F] hm[F]).IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m[F] hm[F]).exists).1
  have hscale := Measure.isMulLeftInvariant_eq_smul μC (canonicalModulatedHaar m[F] hm[F])
  set c := Measure.haarScalarFactor μC (canonicalModulatedHaar m[F] hm[F])
  have hc : (c : ℝ≥0∞) = μ₁ univ := by
    have h := congrArg (fun ν : Measure C[F] ↦ ν B) hscale
    simp only [smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [← hμCB, h, hcanB, mul_one]
  exact hscale.trans (by rw [ENNReal.smul_def, hc])

/-- Paper: Remark 9.2.0.1, p. 403. On the polar subspace the canonical theta integral
converges at every character and computes the entire global Z-function after rescaling. -/
theorem globalIdelicZFunction_eq_canonical_of_vanishing
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) (hf : f ∈ adelePolarSubspace F)
    (c : QuasiCharacter C[F]) :
    let μ := canonicalModulatedHaar m[F] hm[F]
    let V := (normOneIdeleClassTamagawaMeasure F).real univ
    Integrable (fun g ↦ adelicTheta (F := F) f g * c g) μ ∧
      globalIdelicZFunction f c =
        (V : ℂ) * modulatedFourierMellin m[F] univ hm[F] μ (adelicTheta (F := F) f) c := by
  obtain ⟨h₀, hF₀⟩ := (mem_adelePolarSubspace f).mp hf
  have hμ := ideleClassTamagawaMeasure_eq_smul_canonical (F := F)
  have hI := globalThetaMellinIntegral_integrable_of_vanishing f h₀ hF₀ c
  have hZ := congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing f h₀ hF₀) c
  let V := normOneIdeleClassTamagawaMeasure F univ
  have hV := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure := hV.2.2.2.1
  let : CompactSpace (ideleClassNorm F).ker := isCompact_iff_compactSpace.mp hm[F].isCompact_ker
  have hpos : V ≠ 0 := ne_of_gt (isOpen_univ.measure_pos _ univ_nonempty)
  have hfin : V ≠ ∞ := measure_ne_top _ _
  rw [hμ] at hI
  refine ⟨(integrable_smul_measure hpos hfin).mp hI, ?_⟩
  rw [← hZ, globalThetaMellinIntegral, hμ, integral_smul_measure]
  simp [modulatedFourierMellin, relativeVerticalStrip, measureReal_def, Complex.real_smul]

/-- Paper: Remark 9.2.0.1, p. 403. At a regular character the §5.1 operator agrees
with the scaled canonical transform. The quotient form follows from `globalThetaMellin_mk`.
Deviation: (5.1.1.1) names the operator Z. Its bundled target records regular values. -/
theorem globalIdelicMellin_eq_canonical_of_vanishing
    (f : SchwartzBruhat (Multiplicative 𝔸[F]))
    (hf : f (Multiplicative.ofAdd 0) = 0)
    (hFourier : adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) = 0)
    (c : {c : QuasiCharacter C[F] // 0 ≤ globalIdelicOrderBound (F := F) c}) :
    let μ := canonicalModulatedHaar m[F] hm[F]
    let V := (normOneIdeleClassTamagawaMeasure F).real univ
    Integrable (fun g ↦ adelicTheta (F := F) f g * c.val g) μ ∧
      (globalIdelicMellin (F := F) f).val c =
        (V : ℂ) * modulatedFourierMellin m[F] univ hm[F] μ (adelicTheta (F := F) f) c.val := by
  simpa only [globalIdelicMellin_apply] using
    globalIdelicZFunction_eq_canonical_of_vanishing f ((mem_adelePolarSubspace f).2 ⟨hf, hFourier⟩) c.val

end Idelic

local notation "verticalPoint" => (fun (b y : ℝ) ↦ (b : ℂ) + (y : ℂ) * Complex.I)
set_option quotPrecheck false in
local notation "logModule" =>
  (fun (m : _ →ₜ* ℝ≥0ˣ) g ↦ Real.log ((m g).val : ℝ))

/-- Paper: Definition 9.2.1.1(1), p. 404. The logarithmic weight is the sum of the
squared moment multipliers from order zero through order N, times the squared twist.
Deviation: N is the largest order included. The scalar source in (9.2.1.2) uses N − 1.

Deviation: The scalar source on p. 404 uses orders through $N-1$. The density uses orders
through $N$ and allows $N=0$, as in the group convention on p. 408.
-/
def lineSobolevDensity (b : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  Real.exp (2 * b * x) * ∑ k ∈ Finset.range (N + 1), x ^ (2 * k)

/-- Paper: Definition 9.2.1.1(1), p. 404. With order zero only, the density
is just the squared twist.
Deviation: Sanity check in logarithmic coordinates. -/
theorem lineSobolevDensity_order_zero (b x : ℝ) :
    lineSobolevDensity b 0 x = Real.exp (2 * b * x) := by
  simp [lineSobolevDensity]

/-- Paper: Definition 9.2.1.1(1), p. 404. The completion is realized as weighted L².
Deviation: The norm combines the squared norms in (9.2.1.2) by summing them. The
maximum order is an explicit parameter and the scalar case uses Lebesgue measure and `id`.

Deviation: Page 404 defines the scalar topology using the component norms through $N-1$. We use
weighted $L^2$ with the Hilbert sum of the squared component norms through $N$.
-/
abbrev LineSobolev {A : Type*} [MeasurableSpace A] (μ : Measure A) (logNorm : A → ℝ)
    (b : ℝ) (N : ℕ) :=
  Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (lineSobolevDensity b N (logNorm x)))

/-- Paper: Definition 9.2.1.1(1), p. 404. The scalar b-line Sobolev space uses the
moments of order zero through N.
Deviation: (9.2.1.2) prints 0 ≤ k ≤ N − 1. The proof of Theorem 9.2.1.2(1) on p. 405, the
target in Definition 9.2.1.1(2) and Theorem 9.2.1.5, which is the same space for a general
group, all use 0 ≤ k ≤ N.

Deviation: The scalar source on p. 404 starts at $N=1$ and uses orders through $N-1$. We take
$N\ge0$ and moments through order $N$, matching the target order.
-/
abbrev ScalarLineSobolev (b : ℝ) (N : ℕ) :=
  LineSobolev volume id b N

/-- In weighted L², the squared norm is the integral of the squared modulus against
the density. -/
private theorem weightedL2_norm_eq {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {ρ : X → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x)
    (f : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x))) :
    Integrable (fun x ↦ ‖f x‖ ^ 2 * ρ x) ν ∧ ‖f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 * ρ x ∂ν) := by
  have hdens : Measurable (fun x ↦ ENNReal.ofReal (ρ x)) := hρ.ennreal_ofReal
  have hflt : ∀ᵐ x ∂ν, ENNReal.ofReal (ρ x) < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hint_sq : Integrable (fun x ↦ ‖(f : X → ℂ) x‖ ^ 2)
      (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  refine ⟨((integrable_withDensity_iff hdens hflt).1 hint_sq).congr
    (ae_of_all _ fun x ↦ by simp only [ENNReal.toReal_ofReal (hpos x).le]), ?_⟩
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (x := f)]
  refine congrArg Real.sqrt ?_
  rw [L2.inner_def (f := f) (g := f), ← integral_re (L2.integrable_inner f f)]
  simp_rw [inner_self_eq_norm_sq]
  rw [integral_withDensity_eq_integral_toReal_smul hdens hflt]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hpos x).le, mul_comm]

private theorem scalarDecay_weighted_dense (J : Set ℝ) (c : J) (ρ : ℝ → ℝ)
    (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (T : PositiveRealExponentialDecay J →L[ℂ] SchwartzMap ℝ ℂ)
    (hT : ∀ (f : PositiveRealExponentialDecay J) x, ‖f.val x‖ ^ 2 * ρ x ≤ ‖T f x‖ ^ 2) :
    ∃ j : PositiveRealExponentialDecay J →L[ℂ] Lp ℂ 2 (volume.withDensity fun x ↦ ENNReal.ofReal (ρ x)),
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : ℝ → ℂ) =ᵐ[volume] f.val := by
  let μ := volume.withDensity fun x ↦ ENNReal.ofReal (ρ x)
  let : IsLocallyFiniteMeasure μ := IsLocallyFiniteMeasure.withDensity_ofReal hρ
  have hac : volume ≪ μ := withDensity_absolutelyContinuous' hρ.measurable.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  have cont (f : PositiveRealExponentialDecay J) : Continuous f.val := by
    have he : f.val = fun x ↦ (Real.exp (-(c : ℝ) * x) : ℂ) * logExponentialDecayTwist J c f x := by
      funext x
      rw [logExponentialDecayTwist_apply J c f x, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      simp
    rw [he]
    exact (Complex.continuous_ofReal.comp (by fun_prop)).mul (logExponentialDecayTwist J c f).continuous
  have hsq (f : PositiveRealExponentialDecay J) : Integrable (fun x ↦ ‖T f x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (T f).continuous.aestronglyMeasurable).1 ((T f).memLp 2)
  have hint (f : PositiveRealExponentialDecay J) :
      Integrable (fun x ↦ ‖f.val x‖ ^ 2 * ρ x) volume :=
    (hsq f).mono' (((cont f).norm.pow 2).mul hρ).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hpos x).le)]; exact hT f x)
  have mem (f : PositiveRealExponentialDecay J) : MemLp f.val 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm (cont f).aestronglyMeasurable).2
    apply (integrable_withDensity_iff hρ.measurable.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
    simpa only [ENNReal.toReal_ofReal (hpos _).le] using hint f
  let L : PositiveRealExponentialDecay J →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun f := (mem f).toLp f.val
      map_add' f g := MemLp.toLp_add (mem f) (mem g)
      map_smul' c f := MemLp.toLp_const_smul c (mem f) }
  have rep (f : PositiveRealExponentialDecay J) : (L f : ℝ → ℂ) =ᵐ[volume] f.val :=
    hac.ae_eq (mem f).coeFn_toLp
  let U := (SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp T
  have bound (f : PositiveRealExponentialDecay J) : ‖L f‖ ≤ ‖U f‖ := by
    rw [(weightedL2_norm_eq volume hρ.measurable hpos (L f)).2]
    change _ ≤ ‖(T f).toLp 2 volume‖
    rw [SchwartzMap.norm_toLp' two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div]
    apply Real.rpow_le_rpow (integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (hpos x).le) _ (by positivity)
    refine (integral_congr_ae ?_).le.trans (integral_mono (hint f) (hsq f) (hT f))
    filter_upwards [rep f] with x hx using by rw [hx]
  have hL : Continuous L := by
    apply continuous_of_continuousAt_zero L.toAddMonoidHom
    change Tendsto L (𝓝 0) (𝓝 (L 0))
    rw [map_zero, tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) bound (by simpa using (U.continuous.tendsto 0).norm)
  refine ⟨⟨L, hL⟩, fun f g h ↦ Subtype.ext (Measure.eq_of_ae_eq
    ((rep f).symm.trans (by change L f = L g at h; rw [h]; exact rep g)) (cont f) (cont g)), ?_, rep⟩
  apply (Lp.dense_hasCompactSupport_contDiff (μ := μ) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top).mono
  rintro u ⟨g, hu, hg, hgc⟩
  let f : PositiveRealExponentialDecay J := ⟨g, mem_logExponentialDecaySubmodule_of_hasCompactSupport J hg hgc⟩
  exact ⟨f, Lp.ext ((mem f).coeFn_toLp.trans hu.symm)⟩

private theorem scalarDecay_dense_of_weight_le (J : Set ℝ) (a b : J) (ρ P : ℝ → ℝ)
    (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (hP : P.HasTemperateGrowth)
    (hle : ∀ x, ρ x ≤ (P x * (Real.exp (a * x) + Real.exp (b * x))) ^ 2) :
    ∃ j : PositiveRealExponentialDecay J →L[ℂ] Lp ℂ 2 (volume.withDensity fun x ↦ ENNReal.ofReal (ρ x)),
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : ℝ → ℂ) =ᵐ[volume] f.val := by
  let A (d : J) : PositiveRealExponentialDecay J →L[ℂ] SchwartzMap ℝ ℂ :=
    ⟨logExponentialDecayTwist J d, (continuous_apply d).comp
      (positiveRealExponentialDecay_isEmbedding J ⟨a, a.property⟩).continuous⟩
  let T := (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (P x : ℂ))).comp (A a + A b)
  apply scalarDecay_weighted_dense J a ρ hρ hpos T
  intro f x
  change _ ≤ ‖SchwartzMap.smulLeftCLM ℂ (fun x ↦ (P x : ℂ))
    (logExponentialDecayTwist J a f + logExponentialDecayTwist J b f) x‖ ^ 2
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), add_apply,
    logExponentialDecayTwist_apply J a f x, logExponentialDecayTwist_apply J b f x, ← add_mul,
    smul_eq_mul, ← mul_assoc, ← Complex.ofReal_add, ← Complex.ofReal_mul,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hle x) (sq_nonneg _)

/-- The line density is continuous. -/
private theorem continuous_lineSobolevDensity (b : ℝ) (N : ℕ) :
    Continuous (lineSobolevDensity b N) := by
  show Continuous fun x : ℝ ↦ Real.exp (2 * b * x) * ∑ k ∈ Finset.range (N + 1), x ^ (2 * k)
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (continuous_finsetSum _ fun k _ ↦ continuous_id.pow (2 * k))

private theorem lineSobolevPoly_one_le (N : ℕ) (x : ℝ) :
    1 ≤ ∑ k ∈ Finset.range (N + 1), x ^ (2 * k) := by
  calc
    1 = x ^ (2 * (0 : ℕ)) := by norm_num
    _ ≤ _ := Finset.single_le_sum (f := fun k : ℕ ↦ x ^ (2 * k))
      (fun k _ ↦ pow_mul x 2 k ▸ pow_nonneg (sq_nonneg x) k)
      (Finset.mem_range_succ_iff.mpr (Nat.zero_le N))

private theorem lineSobolevDensity_pos (b : ℝ) (N : ℕ) (x : ℝ) : 0 < lineSobolevDensity b N x :=
  mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (lineSobolevPoly_one_le N x))

/-- Paper: Definition 9.2.1.1(1), p. 404. In the scalar model the weighted integral
gives the norm, and the exponential-decay test profiles have dense image.
Deviation: The largest order is N, see `ScalarLineSobolev`. -/
theorem scalarLineSobolev_dense (b : ℝ) (N : ℕ) :
    ∃ j : PositiveRealExponentialDecay univ →L[ℂ] ScalarLineSobolev b N,
      Injective j ∧ DenseRange j ∧
      ∀ f, (j f : ℝ → ℂ) =ᵐ[volume] f.val ∧
        Integrable (fun x ↦ ‖f.val x‖ ^ 2 * lineSobolevDensity b N x) volume ∧
        ‖j f‖ = Real.sqrt (∫ x, ‖f.val x‖ ^ 2 * lineSobolevDensity b N x) := by
  let P (x : ℝ) := ∑ k ∈ Finset.range (N + 1), x ^ (2 * k)
  have hP (x : ℝ) : 1 ≤ P x := lineSobolevPoly_one_le N x
  obtain ⟨j, hj, hd, hr⟩ := scalarDecay_dense_of_weight_le univ ⟨b, trivial⟩ ⟨b, trivial⟩
    (lineSobolevDensity b N) P (continuous_lineSobolevDensity b N) (lineSobolevDensity_pos b N)
    (by dsimp [P]; fun_prop) (fun x ↦ by
      change Real.exp (2 * b * x) * P x ≤ (P x * (Real.exp (b*x) + Real.exp (b*x))) ^ 2
      rw [show 2 * b * x = b * x + b * x by ring, Real.exp_add]
      have hp := hP x
      nlinarith [mul_nonneg (show 0 ≤ P x * (P x - 1) by positivity)
        (sq_nonneg (Real.exp (b * x))), sq_nonneg (P x * Real.exp (b * x))])
  refine ⟨j, hj, hd, fun f ↦ ⟨hr f, ?_⟩⟩
  have he : (fun x ↦ ‖j f x‖ ^ 2 * lineSobolevDensity b N x) =ᵐ[volume]
      (fun x ↦ ‖f.val x‖ ^ 2 * lineSobolevDensity b N x) := by
    filter_upwards [hr f] with x hx using by rw [hx]
  obtain ⟨hi, hn⟩ := weightedL2_norm_eq volume (continuous_lineSobolevDensity b N).measurable
    (lineSobolevDensity_pos b N) (j f)
  exact ⟨hi.congr he, hn.trans (congrArg Real.sqrt (integral_congr_ae he))⟩

/-- Paper: Definition 9.2.1.1(2), p. 404. Complete the entire Schwartz–Bergman
space by taking the closure of its derivative traces in a finite product of vertical L² spaces.
Deviation: The abscissas and largest derivative order are explicit. For one abscissa
this is (9.2.1.3) applied directly to the analytic function. The vertical measure is
a parameter, so either the printed or the Plancherel normalization can be used. For other measures the generators are the
Schwartz–Bergman functions whose indicated traces belong to L². -/
def hardySobolevTraceClosure {ι : Type*} [Fintype ι] (σ : ι → ℝ) (N : ℕ) (ν : Measure ℝ) :
    Submodule ℂ (PiLp 2 (fun _ : ι ↦ PiLp 2 (fun _ : Fin (N + 1) ↦ Lp ℂ 2 ν))) :=
  (Submodule.span ℂ {u : PiLp 2 (fun _ : ι ↦ PiLp 2 (fun _ : Fin (N + 1) ↦ Lp ℂ 2 ν)) |
    ∃ F : SchwartzBergman (univ : Set ℝ),
    ∀ i (k : Fin (N + 1)), (u i k : ℝ → ℂ) =ᵐ[ν]
      fun y ↦ iteratedDeriv (k : ℕ) F.val (verticalPoint (σ i) y)}).topologicalClosure

/-- Paper: Definition 9.2.1.1(2), p. 404. The model contains the Gaussian's
vertical derivative traces at any selected abscissas.
Deviation: Sanity check for the trace closure, using Lebesgue measure. -/
theorem gaussian_mem_hardySobolevTraceClosure {ι : Type*} [Fintype ι] (σ : ι → ℝ) (N : ℕ) :
    ∃ u : hardySobolevTraceClosure σ N volume,
      ∀ i (k : Fin (N + 1)), (u.val i k : ℝ → ℂ) =ᵐ[volume]
        fun y ↦ iteratedDeriv (k : ℕ) (fun z : ℂ ↦ Complex.exp (z ^ 2))
          (verticalPoint (σ i) y) := by
  let g (z : ℂ) := Complex.exp (z ^ 2)
  let F : SchwartzBergman (univ : Set ℝ) := ⟨g, by
    simpa [g] using gaussian_mem_schwartzBergmanSubmodule (univ : Set ℝ) isOpen_univ⟩
  have hpoly (k : ℕ) : ∃ p : Polynomial ℂ, iteratedDeriv k g = fun z ↦ p.eval z * g z := by
    induction k with
    | zero => exact ⟨1, by simp⟩
    | succ k ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p.derivative + Polynomial.C 2 * Polynomial.X * p, ?_⟩
      rw [iteratedDeriv_succ, hp]
      funext z
      have hg : HasDerivAt g (g z * (2 * z)) z := by
        simpa [g] using ((hasDerivAt_id z).pow 2).cexp
      refine ((p.hasDerivAt z).mul hg).deriv.trans ?_
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
  -- The vertical trace estimate applies to each monomial weight.
  have hweighted (a : ℝ) (p : Polynomial ℂ) :
      MemLp (fun y ↦ p.eval (verticalPoint a y) * g (verticalPoint a y)) 2 volume := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [Polynomial.eval_add, add_mul, Pi.add_def] using hp.add hq
    | monomial n c =>
      have ht := schwartzBergman_trace_memLp univ ⟨a, mem_univ a⟩ 2 (by norm_num) (by norm_num) n F
      simpa only [Polynomial.eval_monomial, weightedVerticalTrace, F, mul_assoc] using ht.const_mul c
  have htrace (i : ι) (k : Fin (N + 1)) :
      MemLp (fun y ↦ iteratedDeriv (k : ℕ) g (verticalPoint (σ i) y)) 2 volume := by
    obtain ⟨p, hp⟩ := hpoly k
    rw [hp]
    exact hweighted (σ i) p
  let u : PiLp 2 (fun _ : ι ↦ PiLp 2 (fun _ : Fin (N + 1) ↦ Lp ℂ 2 (volume : Measure ℝ))) :=
    WithLp.toLp 2 fun i ↦ WithLp.toLp 2 fun k ↦ (htrace i k).toLp _
  have hu (i : ι) (k : Fin (N + 1)) : (u i k : ℝ → ℂ) =ᵐ[volume]
      fun y ↦ iteratedDeriv (k : ℕ) g (verticalPoint (σ i) y) :=
    (htrace i k).coeFn_toLp
  refine ⟨⟨u, ?_⟩, hu⟩
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨F, hu⟩)

/-- Paper: Definition 9.2.1.1(2), p. 404. The scalar analytic space uses
one line and derivatives of order zero through N, with the Plancherel measure `dy/(2π)`.
Deviation: (9.2.1.3) prints the factor `1/(2π)` outside the square root. The proof of
Theorem 9.2.1.2(2) uses the Plancherel measure `dx/(2π)`, which is what makes the Mellin
transform isometric. The derivative is taken directly on the analytic input. The norm squares
and sums the component norms. -/
abbrev ScalarLineHardySobolev (b : ℝ) (N : ℕ) :=
  hardySobolevTraceClosure (fun _ : Unit ↦ b) N
    (ENNReal.ofReal (1 / (2 * Real.pi)) • volume)

/-- Paper: Definition 9.2.1.1(2), p. 404. The zeroth trace of the Gaussian
has the L² norm in (9.2.1.3) with the Plancherel normalization.
Deviation: Sanity check on the space and its vertical measure. -/
theorem scalarLineHardySobolev_gaussian (b : ℝ) (N : ℕ) :
    let F := fun y : ℝ ↦ Complex.exp (verticalPoint b y ^ 2)
    ∃ u : ScalarLineHardySobolev b N,
      (u.val () 0 : ℝ → ℂ) =ᵐ[volume] F ∧
      ‖u.val () 0‖ = Real.sqrt ((1 / (2 * Real.pi)) * ∫ y, ‖F y‖ ^ 2) := by
  let c := ENNReal.ofReal (1 / (2 * Real.pi))
  have hc : 0 < 1 / (2 * Real.pi) := by positivity
  let g : SchwartzBergman (univ : Set ℝ) := ⟨fun z ↦ Complex.exp (z ^ 2), by
    simpa using gaussian_mem_schwartzBergmanSubmodule (univ : Set ℝ) isOpen_univ⟩
  let trace (k : Fin (N + 1)) (y : ℝ) := iteratedDeriv (k : ℕ) g.val (verticalPoint b y)
  obtain ⟨v, hv⟩ := gaussian_mem_hardySobolevTraceClosure (fun _ : Unit ↦ b) N
  have htrace (k : Fin (N + 1)) : MemLp (trace k) 2 (c • volume) :=
    ((Lp.memLp (v.val () k)).ae_eq (hv () k)).smul_measure ENNReal.ofReal_ne_top
  let u := WithLp.toLp 2 fun _ : Unit ↦ WithLp.toLp 2 fun k ↦ (htrace k).toLp (trace k)
  have hu (i : Unit) (k : Fin (N + 1)) : (u i k : ℝ → ℂ) =ᵐ[c • volume] trace k :=
    (htrace k).coeFn_toLp
  refine ⟨⟨u, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g, hu⟩)⟩, ?_, ?_⟩
  · simpa only [Measure.ae_ennreal_smul_measure_eq (c := c) (ENNReal.ofReal_pos.mpr hc).ne',
      trace, Fin.val_zero, iteratedDeriv_zero] using hu () 0
  · change ‖(htrace 0).toLp (trace 0)‖ = _
    rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
      (htrace 0), ENNReal.toReal_ofReal (by positivity)]
    have hreal : c.toReal = 1 / (2 * Real.pi) := ENNReal.toReal_ofReal hc.le
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, integral_smul_measure, hreal, smul_eq_mul,
      trace, Fin.val_zero, iteratedDeriv_zero, g, Real.sqrt_eq_rpow, one_div]

/-- Paper: Theorem 9.2.1.2(1), p. 404. On L² the cutoff by a measurable set
is the class of the product with its indicator. -/
def hardySobolevCutoff {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {U : Set A} (hU : MeasurableSet U) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).indicator hU.nullMeasurableSet).toLp (U.indicator (f : A → ℂ))

/-- Paper: Theorem 9.2.1.2(1), p. 404. The cutoff is a continuous linear
idempotent with closed range, and its representative agrees with the pointwise cutoff.
Deviation: State the operator properties for any measurable set in the weighted L² model. -/
theorem hardySobolevCutoff_spec {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {U : Set A} (hU : MeasurableSet U) :
    ∃ P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, IsClosed (range P) ∧
      ∀ f, P (P f) = P f ∧ P f = hardySobolevCutoff hU f ∧
        (P f : A → ℂ) =ᵐ[μ] U.indicator f := by
  have hae (f : Lp ℂ 2 μ) : (hardySobolevCutoff hU f : A → ℂ) =ᵐ[μ] U.indicator f :=
    MemLp.coeFn_toLp _
  let L : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := hardySobolevCutoff hU
      map_add' := fun f g ↦ by
        refine Lp.ext ?_
        filter_upwards [hae (f + g), hae f, hae g, Lp.coeFn_add f g,
          Lp.coeFn_add (hardySobolevCutoff hU f) (hardySobolevCutoff hU g)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ U
        · simp only [Set.indicator_of_mem hx]
          exact h4
        · simp only [Set.indicator_of_notMem hx, add_zero]
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [hae (c • f), hae f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (hardySobolevCutoff hU f)] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h4, Pi.smul_apply, h2]
        by_cases hx : x ∈ U <;> simp [hx, h3] }
  have hbound (f : Lp ℂ 2 μ) : ‖L f‖ ≤ 1 * ‖f‖ := by
    rw [one_mul]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hae f] with x hx
    exact hx ▸ norm_indicator_le_norm_self _ _
  obtain ⟨P, hP⟩ : ∃ P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, ∀ f, P f = hardySobolevCutoff hU f :=
    ⟨L.mkContinuous 1 hbound, fun _ ↦ rfl⟩
  have hidem (f : Lp ℂ 2 μ) : P (P f) = P f := by
    rw [hP (P f), hP f]
    refine Lp.ext ?_
    filter_upwards [hae (hardySobolevCutoff hU f), hae f] with x h1 h2
    rw [h1]
    by_cases hx : x ∈ U <;> simp [hx, h2]
  refine ⟨P, ?_, fun f ↦ ⟨hidem f, hP f, hP f ▸ hae f⟩⟩
  convert isClosed_eq P.continuous continuous_id using 1
  ext f
  exact ⟨fun ⟨g, hg⟩ ↦ hg ▸ hidem g, fun h ↦ ⟨f, h⟩⟩

private theorem scalarDecay_cutoff_range (J : Set ℝ) (c : ℝ) (ρ : ℝ → ℝ)
    (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) :
    let μ := volume.withDensity fun x ↦ ENNReal.ofReal (ρ x)
    closure {u : Lp ℂ 2 μ | ∃ f : PositiveRealExponentialDecay J,
      tsupport f.val ⊆ Ioi c ∧ (u : ℝ → ℂ) =ᵐ[volume] f.val} =
      range (hardySobolevCutoff (μ := μ) (U := Ici c) measurableSet_Ici) := by
  intro μ
  let : IsLocallyFiniteMeasure μ := IsLocallyFiniteMeasure.withDensity_ofReal hρ
  have hw : μ ≪ volume := withDensity_absolutelyContinuous _ _
  have hv : volume ≪ μ := withDensity_absolutelyContinuous' hρ.measurable.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  let S : Submodule ℂ (Lp ℂ 2 μ) :=
    { carrier := {u | ∃ f : PositiveRealExponentialDecay J,
          tsupport f.val ⊆ Ioi c ∧ (u : ℝ → ℂ) =ᵐ[volume] f.val}
      zero_mem' := ⟨0, by change tsupport (0 : ℝ → ℂ) ⊆ _; simp, hv.ae_eq (Lp.coeFn_zero ℂ 2 μ)⟩
      add_mem' := by
        rintro u v ⟨f, hf, hu⟩ ⟨g, hg, hv'⟩
        exact ⟨f + g, (tsupport_add f.val g.val).trans (union_subset hf hg),
          (hv.ae_eq (Lp.coeFn_add u v)).trans (hu.add hv')⟩
      smul_mem' := by
        rintro d u ⟨f, hf, hu⟩
        exact ⟨d • f, (tsupport_comp_subset (g := fun z : ℂ ↦ d • z) (smul_zero d) f.val).trans hf,
          (hv.ae_eq (Lp.coeFn_smul d u)).trans (hu.const_smul d)⟩ }
  obtain ⟨P, hclosed, hP⟩ := hardySobolevCutoff_spec (μ := μ) (U := Ici c) measurableSet_Ici
  rw [show hardySobolevCutoff (μ := μ) (U := Ici c) measurableSet_Ici = P from
    funext fun u ↦ (hP u).2.1.symm]
  change closure (S : Set (Lp ℂ 2 μ)) = _
  apply le_antisymm
  · apply closure_minimal _ hclosed
    rintro u ⟨f, hf, hu⟩
    refine ⟨u, Lp.ext ?_⟩
    filter_upwards [(hP u).2.2, hw.ae_eq hu] with x hPu hx
    rw [hPu]
    by_cases h : x ∈ Ici c
    · simp [h]
    · rw [indicator_of_notMem h, hx]
      exact (image_eq_zero_of_notMem_tsupport (fun ht ↦ h (Ioi_subset_Ici_self (hf ht)))).symm
  · rintro _ ⟨u, rfl⟩
    change P u ∈ S.topologicalClosure
    rw [← S.orthogonal_orthogonal_eq_closure]
    intro z hz
    -- Orthogonality to real smooth tests supported in the open ray forces z to vanish there.
    have hz0 : ∀ᵐ x ∂μ, x ∈ Ioi c → z x = 0 := by
      apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (((Lp.memLp z).locallyIntegrable one_le_two).locallyIntegrableOn _)
      intro g hgd hgc hg
      let φ := Complex.ofRealCLM ∘ g
      have hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ := Complex.ofRealCLM.contDiff.comp hgd
      have hcφ : HasCompactSupport φ := hgc.comp_left rfl
      have hmem : MemLp φ 2 μ := hφ.continuous.memLp_of_hasCompactSupport hcφ
      have ht : hmem.toLp φ ∈ S :=
        ⟨⟨φ, mem_logExponentialDecaySubmodule_of_hasCompactSupport J hcφ hφ⟩,
          (tsupport_comp_subset (g := Complex.ofRealCLM) rfl g).trans hg,
          hv.ae_eq hmem.coeFn_toLp⟩
      refine (integral_congr_ae ?_).trans (show inner ℂ (hmem.toLp φ) z = 0 from hz _ ht)
      filter_upwards [hmem.coeFn_toLp] with x hx
      simp [hx, φ, Complex.real_smul, mul_comm]
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hz0, hw.ae_le (volume.ae_ne c), (hP u).2.2] with x hz' hxc hx
    by_cases h : x ∈ Ici c
    · rw [hz' (mem_Ioi.mpr ((mem_Ici.mp h).lt_of_ne hxc.symm)), inner_zero_left]; rfl
    · simp [hx, indicator_of_notMem h]

/-- Paper: Theorem 9.2.1.2(1), p. 404. The closure of exponential-decay tests
supported strictly above the cutoff is the range of the cutoff projection.
Deviation: Use logarithmic coordinates. -/
theorem scalarLineSobolev_cutoff_closure (a b : ℝ) (_ha : 1 < a) (N : ℕ) :
    closure {u : ScalarLineSobolev b N | ∃ f : PositiveRealExponentialDecay univ,
      tsupport f.val ⊆ Ioi (-Real.log a) ∧ (u : ℝ → ℂ) =ᵐ[volume] f.val} =
    range (hardySobolevCutoff (μ := volume.withDensity fun x ↦
      ENNReal.ofReal (lineSobolevDensity b N x))
      (U := Ici (-Real.log a)) measurableSet_Ici) := by
  exact scalarDecay_cutoff_range univ (-Real.log a) (lineSobolevDensity b N)
    (continuous_lineSobolevDensity b N) (lineSobolevDensity_pos b N)

-- TODO(paper-gap): (9.2.1.2) prints orders up to N − 1 and (9.2.1.3) prints 1/(2π)
-- outside the square root; with either as printed Theorem 9.2.1.2(2) is not an isometry.
-- In Theorem 9.2.1.2(3) the Paley–Wiener bound has no stated limiting regime and the
-- printed split square roots fail at nonpositive real parts. The direct bound for a profile
-- supported in [−log a,0] uses the factor (∫_{−log a}^0 exp(2 Re(s) x) dx)^(1/2),
-- with value (log a)^(1/2) at Re(s) = 0.

/-- Paper: Theorem 9.2.1.2(3), p. 405. The top row splits a supported L²
class into its bounded-interval part and its right-hand part.
Deviation: State the top row alone for a measurable logarithmic coordinate with no
mass on the splitting level. The analytic row has the gaps noted above. -/
theorem hardySobolevCutoff_exact {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (x : A → ℝ) (hx : Measurable x) (c : ℝ) (_hc : c ≤ 0)
    (_hzero : μ (x ⁻¹' {0}) = 0) :
    let E := Lp ℂ 2 μ
    let S := fun (U : Set ℝ) ↦ {f : E | (f : A → ℂ) =ᵐ[μ] (x ⁻¹' U).indicator (f : A → ℂ)}
    ∃ (L M R : Submodule ℂ E) (i : L →L[ℂ] M) (p : M →L[ℂ] R),
      (L : Set E) = S (Icc c 0) ∧ (M : Set E) = S (Ici c) ∧ (R : Set E) = S (Ici 0) ∧
      (∀ f, (i f).val = f.val) ∧
      (∀ f, (p f).val = hardySobolevCutoff
        (μ := μ) (hx measurableSet_Ici : MeasurableSet (x ⁻¹' Ici 0)) f.val) ∧
      Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p := by
  intro E S
  have key (U : Set ℝ) (hU : MeasurableSet U) :
      ∃ K : Submodule ℂ (Lp ℂ 2 μ), IsClosed (K : Set (Lp ℂ 2 μ)) ∧
        ∀ f : Lp ℂ 2 μ, f ∈ K ↔ (f : A → ℂ) =ᵐ[μ] (x ⁻¹' U).indicator (f : A → ℂ) := by
    obtain ⟨P, -, hP⟩ := hardySobolevCutoff_spec (μ := μ) (hx hU)
    refine ⟨LinearMap.eqLocus (P : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) LinearMap.id, ?_,
      fun f ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
    · exact isClosed_eq P.continuous continuous_id
    · have h' : P f = f := h
      have h2 := (hP f).2.2
      rw [h'] at h2
      exact h2
    · exact Lp.ext ((hP f).2.2.trans h.symm)
  obtain ⟨L, hLc, hL⟩ := key (Icc c 0) measurableSet_Icc
  obtain ⟨M, -, hM⟩ := key (Ici c) measurableSet_Ici
  obtain ⟨R, -, hR⟩ := key (Ici 0) measurableSet_Ici
  obtain ⟨P, -, hP⟩ := hardySobolevCutoff_spec (μ := μ) (hx (measurableSet_Ici (a := (0 : ℝ))))
  have hnull : ∀ᵐ a ∂μ, a ∉ x ⁻¹' {0} := measure_eq_zero_iff_ae_notMem.1 _hzero
  have hLM : ∀ f : L, f.val ∈ M := by
    intro f
    refine (hM _).2 ?_
    filter_upwards [(hL f.val).1 f.2] with a ha
    by_cases h : a ∈ x ⁻¹' Ici c
    · exact (Set.indicator_of_mem h _).symm
    · have h2 : a ∉ x ⁻¹' Icc c 0 := fun h' ↦ h (show c ≤ x a ∧ x a ≤ 0 from h').1
      exact ha.trans ((Set.indicator_of_notMem h2 _).trans (Set.indicator_of_notMem h _).symm)
  have hRM : ∀ r : R, r.val ∈ M := by
    intro r
    refine (hM _).2 ?_
    filter_upwards [(hR r.val).1 r.2] with a ha
    by_cases h : a ∈ x ⁻¹' Ici c
    · exact (Set.indicator_of_mem h _).symm
    · have h2 : a ∉ x ⁻¹' Ici 0 := fun h' ↦ h (_hc.trans (show 0 ≤ x a from h'))
      exact ha.trans ((Set.indicator_of_notMem h2 _).trans (Set.indicator_of_notMem h _).symm)
  have hPR : ∀ f : M, P f.val ∈ R := by
    intro f
    refine (hR _).2 ?_
    have h1 := (hP (P f.val)).2.2
    rw [(hP f.val).1] at h1
    exact h1
  obtain ⟨i, hi⟩ : ∃ i : L →L[ℂ] M, ∀ f, (i f).val = f.val :=
    ⟨L.subtypeL.codRestrict M hLM, fun _ ↦ rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : M →L[ℂ] R, ∀ f, (p f).val = P f.val :=
    ⟨(P.comp M.subtypeL).codRestrict R hPR, fun _ ↦ rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : R →L[ℂ] M, ∀ r, (j r).val = r.val :=
    ⟨R.subtypeL.codRestrict M hRM, fun _ ↦ rfl⟩
  have hpj : ∀ r : R, p (j r) = r := fun r ↦ Subtype.ext ((hp _).trans
    ((congrArg (fun g ↦ P g) (hj r)).trans
      (Lp.ext ((hP r.val).2.2.trans ((hR r.val).1 r.2).symm))))
  have hinj : Injective i := fun f g h ↦
    Subtype.ext ((hi f).symm.trans ((congrArg (fun m : M ↦ (m : Lp ℂ 2 μ)) h).trans (hi g)))
  have hrange : IsClosed (range i) := by
    have hr : range i = (fun m : M ↦ (m : Lp ℂ 2 μ)) ⁻¹' (L : Set (Lp ℂ 2 μ)) := by
      ext m
      constructor
      · rintro ⟨f, rfl⟩
        have h1 : (i f).val ∈ L := by
          rw [hi]
          exact f.2
        exact h1
      · intro h
        exact ⟨⟨m.val, h⟩, Subtype.ext (hi _)⟩
    rw [hr]
    exact hLc.preimage continuous_subtype_val
  have hexact : Exact i p := by
    intro y
    constructor
    · intro h0
      have h0' : P y.val = 0 := (hp y).symm.trans (congrArg (fun r : R ↦ (r : Lp ℂ 2 μ)) h0)
      have hz : ((P y.val : Lp ℂ 2 μ) : A → ℂ) =ᵐ[μ] 0 := by
        rw [h0']
        exact Lp.coeFn_zero ℂ 2 μ
      have hyL : y.val ∈ L := by
        refine (hL _).2 ?_
        filter_upwards [(hM y.val).1 y.2, (hP y.val).2.2, hz] with a h1 h2 h3
        by_cases ha : a ∈ x ⁻¹' Icc c 0
        · exact (Set.indicator_of_mem ha _).symm
        · refine Eq.trans ?_ (Set.indicator_of_notMem ha _).symm
          by_cases hc' : a ∈ x ⁻¹' Ici c
          · have h0a : 0 ≤ x a := (le_total 0 (x a)).resolve_right
              fun hle ↦ ha (show x a ∈ Icc c 0 from ⟨hc', hle⟩)
            exact (Set.indicator_of_mem (show a ∈ x ⁻¹' Ici 0 from h0a) _).symm.trans
              (h2.symm.trans h3)
          · exact h1.trans (Set.indicator_of_notMem hc' _)
      exact ⟨⟨y.val, hyL⟩, Subtype.ext (hi _)⟩
    · rintro ⟨f, rfl⟩
      have hPf0 : P f.val = 0 := by
        refine Lp.ext ?_
        filter_upwards [(hL f.val).1 f.2, (hP f.val).2.2, hnull, Lp.coeFn_zero ℂ 2 μ]
          with a h1 h2 h3 h4
        refine h2.trans (Eq.trans ?_ h4.symm)
        by_cases ha : a ∈ x ⁻¹' Ici 0
        · have ha' : a ∉ x ⁻¹' Icc c 0 := fun h ↦
            h3 (show x a = 0 from le_antisymm (show c ≤ x a ∧ x a ≤ 0 from h).2 ha)
          exact (Set.indicator_of_mem ha _).trans (h1.trans (Set.indicator_of_notMem ha' _))
        · exact Set.indicator_of_notMem ha _
      exact Subtype.ext ((hp _).trans ((congrArg (fun g ↦ P g) (hi f)).trans hPf0))
  have hopen : IsOpenMap p := by
    refine IsOpenMap.of_sections fun m ↦ ⟨fun r ↦ m + j (r - p m), ?_, ?_, fun r ↦ ?_⟩
    · have hc : Continuous fun r : R ↦ m + j (r - p m) :=
        continuous_const.add (j.continuous.comp (continuous_id.sub continuous_const))
      exact hc.continuousAt
    · show m + j (p m - p m) = m
      rw [sub_self, map_zero, add_zero]
    · show p (m + j (r - p m)) = r
      rw [map_add, hpj, add_sub_cancel]
  exact ⟨L, M, R, i, p, Set.ext hL, Set.ext hM, Set.ext hR, hi,
    fun f ↦ (hp f).trans (hP f.val).2.1, hinj, hrange, hexact, fun r ↦ ⟨j r, hpj r⟩, hopen⟩

-- TODO(paper-gap): Corollary 9.2.1.3 omits the one-sided support hypothesis used
-- in its proof. The uniform Hardy bound at order N also exceeds the printed
-- source order.

/-- A power of `|x|` times a decaying exponential of `|x|` is integrable. -/
private theorem integrable_abs_pow_mul_exp_neg (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x : ℝ ↦ |x| ^ n * Real.exp (-(δ * |x|))) volume := by
  have hcont : Continuous fun x : ℝ ↦ |x| ^ n * Real.exp (-(δ * |x|)) :=
    (continuous_abs.pow n).mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg)
  refine (integrable_inv_one_add_sq.const_mul
    ((n + 2).factorial * Real.exp δ / δ ^ (n + 2))).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  show ‖|x| ^ n * Real.exp (-(δ * |x|))‖ ≤
    (n + 2).factorial * Real.exp δ / δ ^ (n + 2) * (1 + x ^ 2)⁻¹
  have hA : 0 ≤ |x| := abs_nonneg x
  rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity),
    le_div_iff₀ (by positivity)]
  have h := Real.pow_div_factorial_le_exp (x := δ * (1 + |x|)) (by positivity) (n + 2)
  rw [div_le_iff₀ (by positivity)] at h
  have h1 : |x| ^ n * (1 + x ^ 2) ≤ (1 + |x|) ^ (n + 2) := by
    rw [pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hA (by linarith) n) (by nlinarith [sq_abs x])
      (by positivity) (by positivity)
  have h2 : δ * (1 + |x|) + -(δ * |x|) = δ := by ring
  calc |x| ^ n * Real.exp (-(δ * |x|)) * (1 + x ^ 2) * δ ^ (n + 2)
      = |x| ^ n * (1 + x ^ 2) * δ ^ (n + 2) * Real.exp (-(δ * |x|)) := by ring
    _ ≤ (1 + |x|) ^ (n + 2) * δ ^ (n + 2) * Real.exp (-(δ * |x|)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity))
          (Real.exp_pos _).le
    _ = (δ * (1 + |x|)) ^ (n + 2) * Real.exp (-(δ * |x|)) := by rw [mul_pow]; ring
    _ ≤ Real.exp (δ * (1 + |x|)) * (n + 2).factorial * Real.exp (-(δ * |x|)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = (n + 2).factorial * Real.exp δ := by
        rw [mul_right_comm, ← Real.exp_add, h2, mul_comm]

/-- Integration against a kernel whose square is integrable against the reciprocal density
is a continuous functional on a weighted L² space, by the Cauchy–Schwarz inequality. -/
private theorem weightedL2_pairing {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {ρ : X → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x) {w : X → ℂ}
    (hw : AEStronglyMeasurable w ν) (hint : Integrable (fun x ↦ ‖w x‖ ^ 2 * (ρ x)⁻¹) ν) :
    ∃ Λ : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) →L[ℂ] ℂ,
      ∀ f, Integrable (fun x ↦ f x * w x) ν ∧ Λ f = ∫ x, f x * w x ∂ν := by
  have hdens : Measurable (fun x ↦ ENNReal.ofReal (ρ x)) := hρ.ennreal_ofReal
  have hflt : ∀ᵐ x ∂ν, ENNReal.ofReal (ρ x) < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hbase : ν ≪ ν.withDensity fun x ↦ ENNReal.ofReal (ρ x) :=
    withDensity_absolutelyContinuous' hdens.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  let u : X → ℂ := fun x ↦ (((ρ x)⁻¹ : ℝ) : ℂ) * star (w x)
  have hmeas : AEStronglyMeasurable u (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) :=
    (Complex.measurable_ofReal.comp hρ.inv).aestronglyMeasurable.mul
      (hw.mono_ac (withDensity_absolutelyContinuous _ _)).star
  have hmem : MemLp u 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) := by
    apply (memLp_two_iff_integrable_sq_norm hmeas).2
    apply (integrable_withDensity_iff hdens hflt).2
    refine hint.congr (ae_of_all _ fun x ↦ ?_)
    change ‖w x‖ ^ 2 * (ρ x)⁻¹ =
      ‖(((ρ x)⁻¹ : ℝ) : ℂ) * star (w x)‖ ^ 2 * (ENNReal.ofReal (ρ x)).toReal
    rw [ENNReal.toReal_ofReal (hpos x).le, norm_mul, norm_star, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos x))]
    calc ‖w x‖ ^ 2 * (ρ x)⁻¹ = ‖w x‖ ^ 2 * (ρ x)⁻¹ * ((ρ x)⁻¹ * ρ x) := by
          rw [inv_mul_cancel₀ (hpos x).ne', mul_one]
      _ = ((ρ x)⁻¹ * ‖w x‖) ^ 2 * ρ x := by ring
  let g := hmem.toLp u
  have hcoe : (g : X → ℂ) =ᵐ[ν] u := hbase.ae_eq hmem.coeFn_toLp
  refine ⟨innerSL ℂ g, fun f ↦ ?_⟩
  have hprod : (fun x ↦ f x * w x) =ᵐ[ν]
      fun x ↦ (ENNReal.ofReal (ρ x)).toReal • inner ℂ (g x) (f x) := by
    filter_upwards [hcoe] with x hx
    have hne : (ρ x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos x).ne'
    have hstar : star (((ρ x)⁻¹ : ℝ) : ℂ) = (((ρ x)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
    rw [hx, ENNReal.toReal_ofReal (hpos x).le, RCLike.inner_apply, starRingEnd_apply]
    change f x * w x = ρ x • (f x * star ((((ρ x)⁻¹ : ℝ) : ℂ) * star (w x)))
    rw [star_mul', hstar, star_star, Complex.real_smul, Complex.ofReal_inv]
    calc f x * w x = (ρ x : ℂ) * (ρ x : ℂ)⁻¹ * (f x * w x) := by
          rw [mul_inv_cancel₀ hne, one_mul]
      _ = (ρ x : ℂ) * (f x * ((ρ x : ℂ)⁻¹ * w x)) := by ring
  refine ⟨((integrable_withDensity_iff_integrable_smul' hdens hflt).1
    (L2.integrable_inner g f)).congr hprod.symm, ?_⟩
  calc innerSL ℂ g f = inner ℂ g f := rfl
    _ = ∫ x, inner ℂ (g x) (f x) ∂(ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) :=
      L2.inner_def g f
    _ = ∫ x, (ENNReal.ofReal (ρ x)).toReal • inner ℂ (g x) (f x) ∂ν :=
      integral_withDensity_eq_integral_toReal_smul hdens hflt _
    _ = ∫ x, f x * w x ∂ν := integral_congr_ae hprod.symm

/-- The moment kernel `x ^ k * exp (z * x)`, cut off to a measurable set on which a
continuous positive density dominates it exponentially, gives a continuous functional on
the weighted L² space of that density. -/
private theorem weightedL2_moment_functional {ρ : ℝ → ℝ} (hρc : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (z : ℂ) (k : ℕ) {U : Set ℝ} (hU : MeasurableSet U) {δ K : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hlow : ∀ x ∈ U, Real.exp (2 * z.re * x + δ * |x|) ≤ K * ρ x) :
    ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦ ENNReal.ofReal (ρ x)) →L[ℂ] ℂ,
      ∀ f, Integrable (fun x : ℝ ↦ f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x) volume ∧
        Λ f = ∫ x : ℝ, f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
  have hker : Continuous fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) :=
    (Complex.continuous_ofReal.pow k).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  refine weightedL2_pairing volume hρc.measurable hpos
    (hker.measurable.indicator hU).aestronglyMeasurable ?_
  refine ((integrable_abs_pow_mul_exp_neg (2 * k) hδ).const_mul K).mono'
    (((hker.measurable.indicator hU).norm.pow_const 2).mul
      hρc.measurable.inv).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  show ‖‖U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x‖ ^ 2 *
      (ρ x)⁻¹‖ ≤ K * (|x| ^ (2 * k) * Real.exp (-(δ * |x|)))
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (hpos x).le))]
  by_cases hx : x ∈ U
  · have hre : (z * (x : ℂ)).re = z.re * x := by simp
    rw [Set.indicator_of_mem hx, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, hre]
    have key : Real.exp (z.re * x) ^ 2 * (ρ x)⁻¹ ≤ K * Real.exp (-(δ * |x|)) := by
      rw [← div_eq_mul_inv, div_le_iff₀ (hpos x)]
      calc Real.exp (z.re * x) ^ 2
          = Real.exp (-(δ * |x|)) * Real.exp (2 * z.re * x + δ * |x|) := by
            rw [← Real.exp_add, sq, ← Real.exp_add]
            congr 1
            ring
        _ ≤ Real.exp (-(δ * |x|)) * (K * ρ x) :=
            mul_le_mul_of_nonneg_left (hlow x hx) (Real.exp_pos _).le
        _ = K * Real.exp (-(δ * |x|)) * ρ x := by ring
    calc (|x| ^ k * Real.exp (z.re * x)) ^ 2 * (ρ x)⁻¹
        = |x| ^ (2 * k) * (Real.exp (z.re * x) ^ 2 * (ρ x)⁻¹) := by ring
      _ ≤ |x| ^ (2 * k) * (K * Real.exp (-(δ * |x|))) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = K * (|x| ^ (2 * k) * Real.exp (-(δ * |x|))) := by ring
  · rw [Set.indicator_of_notMem hx, norm_zero, zero_pow two_ne_zero, zero_mul]
    exact mul_nonneg hK (by positivity)

/-- Differentiation under the integral sign for exponential moments on a measure space: if
every moment of `h` against `exp (σ * ℓ x)` is integrable for `σ` in an open interval, then on
the corresponding vertical strip the integral of `h x * exp (w * ℓ x)` is holomorphic, and its
`k`th derivative is the `k`th moment. -/
private theorem iteratedDeriv_exp_moment_of_measurable {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {h : X → ℂ} {ℓ : X → ℝ} (hℓ : Measurable ℓ) {α β : ℝ}
    (hint : ∀ σ ∈ Ioo α β, ∀ n : ℕ,
      Integrable (fun x ↦ h x * (ℓ x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (ℓ x : ℂ))) μ)
    (k : ℕ) {z : ℂ} (hz : z.re ∈ Ioo α β) :
    AnalyticAt ℂ (fun w : ℂ ↦ ∫ x, h x * Complex.exp (w * (ℓ x : ℂ)) ∂μ) z ∧
      Integrable (fun x ↦ h x * (ℓ x : ℂ) ^ k * Complex.exp (z * (ℓ x : ℂ))) μ ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ x, h x * Complex.exp (w * (ℓ x : ℂ)) ∂μ) z =
        ∫ x, h x * (ℓ x : ℂ) ^ k * Complex.exp (z * (ℓ x : ℂ)) ∂μ := by
  let F : ℕ → ℂ → X → ℂ := fun n w x ↦ h x * (ℓ x : ℂ) ^ n * Complex.exp (w * (ℓ x : ℂ))
  have hℓc : Measurable fun x ↦ (ℓ x : ℂ) := Complex.measurable_ofReal.comp hℓ
  have hexpc : ∀ w : ℂ, Measurable fun x ↦ Complex.exp (w * (ℓ x : ℂ)) := fun w ↦
    Complex.measurable_exp.comp (hℓc.const_mul w)
  have hm : AEStronglyMeasurable h μ := by
    refine ((hint z.re hz 0).aestronglyMeasurable.mul
      (hexpc (-(z.re : ℂ))).aestronglyMeasurable).congr (ae_of_all _ fun x ↦ ?_)
    show h x * (ℓ x : ℂ) ^ 0 * Complex.exp ((z.re : ℂ) * (ℓ x : ℂ)) *
      Complex.exp (-(z.re : ℂ) * (ℓ x : ℂ)) = h x
    rw [pow_zero, mul_one, mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel,
      Complex.exp_zero, mul_one]
  have hFm : ∀ n w, AEStronglyMeasurable (F n w) μ := fun n w ↦
    (hm.mul (hℓc.pow_const n).aestronglyMeasurable).mul (hexpc w).aestronglyMeasurable
  have hnorm : ∀ n (w : ℂ) (x : X),
      ‖F n w x‖ = ‖h x‖ * |ℓ x| ^ n * Real.exp (w.re * ℓ x) := by
    intro n w x
    have hre : (w * (ℓ x : ℂ)).re = w.re * ℓ x := by simp
    show ‖h x * (ℓ x : ℂ) ^ n * Complex.exp (w * (ℓ x : ℂ))‖ = _
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      hre]
  have hFi : ∀ n (w : ℂ), w.re ∈ Ioo α β → Integrable (F n w) μ := fun n w hw ↦
    (hint w.re hw n).mono (hFm n w) (ae_of_all _ fun x ↦ le_of_eq (by
      show ‖F n w x‖ = ‖F n (w.re : ℂ) x‖
      rw [hnorm, hnorm, Complex.ofReal_re]))
  have hderiv : ∀ n (w : ℂ), w.re ∈ Ioo α β →
      HasDerivAt (fun w ↦ ∫ x, F n w x ∂μ) (∫ x, F (n + 1) w x ∂μ) w := by
    intro n w hw
    obtain ⟨ε, hε, hεa, hεb⟩ : ∃ ε : ℝ, 0 < ε ∧ α < w.re - ε ∧ w.re + ε < β := by
      have h0 : 0 < min (w.re - α) (β - w.re) := lt_min (sub_pos.2 hw.1) (sub_pos.2 hw.2)
      have h1 := min_le_left (w.re - α) (β - w.re)
      have h2 := min_le_right (w.re - α) (β - w.re)
      exact ⟨min (w.re - α) (β - w.re) / 2, half_pos h0, by linarith, by linarith⟩
    have hlo : ((w.re - ε : ℝ) : ℂ).re ∈ Ioo α β := by
      rw [Complex.ofReal_re]
      exact ⟨hεa, by linarith⟩
    have hhi : ((w.re + ε : ℝ) : ℂ).re ∈ Ioo α β := by
      rw [Complex.ofReal_re]
      exact ⟨by linarith, hεb⟩
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w hε)
      (Eventually.of_forall (hFm n)) (hFi n w hw) (hFm (n + 1) w)
      (ae_of_all _ fun x w' hw' ↦ ?_)
      ((hFi (n + 1) _ hlo).norm.add (hFi (n + 1) _ hhi).norm)
      (ae_of_all _ fun x w' _ ↦ ?_)).2
    · show ‖F (n + 1) w' x‖ ≤
        ‖F (n + 1) ((w.re - ε : ℝ) : ℂ) x‖ + ‖F (n + 1) ((w.re + ε : ℝ) : ℂ) x‖
      rw [hnorm, hnorm, hnorm, Complex.ofReal_re, Complex.ofReal_re]
      have h2 : ‖w' - w‖ < ε := by
        rw [← dist_eq_norm]
        exact hw'
      have h1 := (Complex.abs_re_le_norm (w' - w)).trans_lt h2
      rw [Complex.sub_re] at h1
      obtain ⟨hl, hu⟩ := abs_lt.1 h1
      have hexp : Real.exp (w'.re * ℓ x) ≤
          Real.exp ((w.re - ε) * ℓ x) + Real.exp ((w.re + ε) * ℓ x) := by
        rcases le_total 0 (ℓ x) with hx | hx
        · have hp := mul_nonneg (by linarith : (0 : ℝ) ≤ w.re + ε - w'.re) hx
          exact (Real.exp_le_exp.2 (by nlinarith)).trans
            (le_add_of_nonneg_left (Real.exp_pos _).le)
        · have hp := mul_nonneg (by linarith : (0 : ℝ) ≤ w'.re - w.re + ε) (neg_nonneg.2 hx)
          exact (Real.exp_le_exp.2 (by nlinarith)).trans
            (le_add_of_nonneg_right (Real.exp_pos _).le)
      calc ‖h x‖ * |ℓ x| ^ (n + 1) * Real.exp (w'.re * ℓ x)
          ≤ ‖h x‖ * |ℓ x| ^ (n + 1) *
            (Real.exp ((w.re - ε) * ℓ x) + Real.exp ((w.re + ε) * ℓ x)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = _ := mul_add _ _ _
    · exact (((hasDerivAt_id' w').mul_const (ℓ x : ℂ)).cexp.const_mul
        (h x * (ℓ x : ℂ) ^ n)).congr_deriv (by
          show h x * (ℓ x : ℂ) ^ n * (Complex.exp (w' * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))) =
            h x * (ℓ x : ℂ) ^ (n + 1) * Complex.exp (w' * (ℓ x : ℂ))
          ring)
  have hS : IsOpen {w : ℂ | w.re ∈ Ioo α β} := isOpen_Ioo.preimage Complex.continuous_re
  have hM : (fun w : ℂ ↦ ∫ x, h x * Complex.exp (w * (ℓ x : ℂ)) ∂μ) =
      fun w ↦ ∫ x, F 0 w x ∂μ := by
    funext w
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    show h x * Complex.exp (w * (ℓ x : ℂ)) = h x * (ℓ x : ℂ) ^ 0 * Complex.exp (w * (ℓ x : ℂ))
    rw [pow_zero, mul_one]
  have hiter : ∀ n (w : ℂ), w.re ∈ Ioo α β →
      iteratedDeriv n (fun w ↦ ∫ x, F 0 w x ∂μ) w = ∫ x, F n w x ∂μ := by
    intro n
    induction n with
    | zero =>
      intro w _
      rw [iteratedDeriv_zero]
    | succ n ih =>
      intro w hw
      have hev : iteratedDeriv n (fun w ↦ ∫ x, F 0 w x ∂μ) =ᶠ[𝓝 w]
          fun w ↦ ∫ x, F n w x ∂μ :=
        (hS.eventually_mem hw).mono fun w' hw' ↦ ih w' hw'
      rw [iteratedDeriv_succ, hev.deriv_eq]
      exact (hderiv n w hw).deriv
  rw [hM]
  exact ⟨DifferentiableOn.analyticAt (s := {w : ℂ | w.re ∈ Ioo α β}) (fun w hw ↦
    (hderiv 0 w hw).differentiableAt.differentiableWithinAt) (hS.mem_nhds hz),
    hFi k z hz, hiter k z hz⟩

/-- Integrable exponential moments on a real interval give a holomorphic
Laplace transform on its vertical strip, with all derivatives obtained under
the integral sign. -/
alias analyticAt_laplace_integral_and_iteratedDeriv := iteratedDeriv_exp_moment_of_measurable


/-- Differentiation under the integral sign for exponential moments on the real line with
Lebesgue measure. -/
private theorem iteratedDeriv_exp_moment {h : ℝ → ℂ} {α β : ℝ}
    (hint : ∀ σ ∈ Ioo α β, ∀ n : ℕ,
      Integrable (fun x : ℝ ↦ h x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) volume)
    (k : ℕ) {z : ℂ} (hz : z.re ∈ Ioo α β) :
    AnalyticAt ℂ (fun w : ℂ ↦ ∫ x : ℝ, h x * Complex.exp (w * (x : ℂ))) z ∧
      Integrable (fun x : ℝ ↦ h x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ x : ℝ, h x * Complex.exp (w * (x : ℂ))) z =
        ∫ x : ℝ, h x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) :=
  iteratedDeriv_exp_moment_of_measurable measurable_id hint k hz
/-- The line density dominates its exponential factor. -/
private theorem exp_le_lineSobolevDensity (b : ℝ) (N : ℕ) (x : ℝ) :
    Real.exp (2 * b * x) ≤ lineSobolevDensity b N x := by
  unfold lineSobolevDensity
  refine le_mul_of_one_le_right (Real.exp_pos _).le ?_
  calc (1 : ℝ) = x ^ (2 * 0) := by rw [mul_zero, pow_zero]
    _ ≤ ∑ k ∈ Finset.range (N + 1), x ^ (2 * k) :=
      Finset.single_le_sum (f := fun k ↦ x ^ (2 * k))
        (fun k _ ↦ (even_two_mul k).pow_nonneg x) (Finset.mem_range.2 N.succ_pos)

/-- To the left of the line, every moment kernel cut off above a point gives a continuous
functional on the line space. -/
private theorem lineSobolev_cutoff_moment_functional (a b : ℝ) (ha : 1 < a) (N k : ℕ)
    (z : ℂ) (hz : z.re < b) :
    ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (lineSobolevDensity b N x)) →L[ℂ] ℂ,
      ∀ f : Lp ℂ 2 (volume.withDensity fun x ↦ ENNReal.ofReal (lineSobolevDensity b N x)),
        Integrable (fun x : ℝ ↦ (Ici (-Real.log a)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
        Λ f = ∫ x : ℝ, (Ici (-Real.log a)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  have hlogA : 0 < Real.log a := Real.log_pos ha
  have hbz : 0 < b - z.re := sub_pos.2 hz
  obtain ⟨Λ, hΛ⟩ := weightedL2_moment_functional (continuous_lineSobolevDensity b N)
    (fun x ↦ (Real.exp_pos _).trans_le (exp_le_lineSobolevDensity b N x)) z k
    (measurableSet_Ici (a := -Real.log a)) (δ := 2 * (b - z.re))
    (K := Real.exp (4 * (b - z.re) * Real.log a)) (mul_pos two_pos hbz) (Real.exp_pos _).le
    fun x hx ↦ by
      have hx' : -Real.log a ≤ x := hx
      have hle : 2 * z.re * x + 2 * (b - z.re) * |x| ≤
          4 * (b - z.re) * Real.log a + 2 * b * x := by
        rcases le_total 0 x with h0 | h0
        · rw [abs_of_nonneg h0]
          nlinarith [mul_pos hbz hlogA]
        · rw [abs_of_nonpos h0]
          nlinarith [mul_nonneg hbz.le (by linarith : 0 ≤ Real.log a + x)]
      calc Real.exp (2 * z.re * x + 2 * (b - z.re) * |x|)
          ≤ Real.exp (4 * (b - z.re) * Real.log a + 2 * b * x) := Real.exp_le_exp.2 hle
        _ = Real.exp (4 * (b - z.re) * Real.log a) * Real.exp (2 * b * x) := Real.exp_add _ _
        _ ≤ Real.exp (4 * (b - z.re) * Real.log a) * lineSobolevDensity b N x :=
          mul_le_mul_of_nonneg_left (exp_le_lineSobolevDensity b N x) (Real.exp_pos _).le
  refine ⟨Λ, fun f ↦ ?_⟩
  have hfun : (fun x : ℝ ↦ (Ici (-Real.log a)).indicator (⇑f) x *
      (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) = fun x : ℝ ↦ f x *
      (Ici (-Real.log a)).indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
    funext x
    by_cases hx : x ∈ Ici (-Real.log a)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_assoc]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, zero_mul, mul_zero]
  rw [hfun]
  exact hΛ f

/-- The Mellin transform of a profile in the logarithmic coordinate is its two-sided
exponential integral. -/
private theorem mellin_comp_log_eq (h : ℝ → ℂ) (s : ℂ) :
    mellin (fun t ↦ h (Real.log t)) s = ∫ x : ℝ, h x * Complex.exp (s * (x : ℂ)) := by
  rw [mellin, ← integral_comp_exp]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  show Real.exp y • (((Real.exp y : ℝ) : ℂ) ^ (s - 1) • h (Real.log (Real.exp y))) =
    h y * Complex.exp (s * (y : ℂ))
  have hexp : (y : ℂ) + (y : ℂ) * (s - 1) = s * (y : ℂ) := by ring
  rw [Real.log_exp, Complex.real_smul, smul_eq_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (Real.exp_pos y).ne'),
    ← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp, Complex.ofReal_exp, ← mul_assoc,
    ← Complex.exp_add, hexp]
  exact mul_comm _ _

/-- Every exponential moment of an exponential-decay profile is integrable. -/
private theorem integrable_logExponentialDecay_moment (f : logExponentialDecaySubmodule univ)
    (σ : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ f.val x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) volume := by
  have hfun : (fun x : ℝ ↦ f.val x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) =
      fun x : ℝ ↦ (x : ℂ) ^ n * logExponentialDecayTwist univ ⟨σ, mem_univ σ⟩ f x := by
    funext x
    rw [logExponentialDecayTwist_apply]
    show f.val x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ)) =
      (x : ℂ) ^ n * (((Real.exp (σ * x) : ℝ) : ℂ) * f.val x)
    rw [Complex.ofReal_exp, Complex.ofReal_mul]
    ring
  rw [hfun]
  refine (SchwartzMap.integrable_pow_mul volume
    (logExponentialDecayTwist univ ⟨σ, mem_univ σ⟩ f) n).mono'
    ((Complex.continuous_ofReal.pow n).mul (SchwartzMap.continuous _)).aestronglyMeasurable
    (ae_of_all _ fun x ↦ le_of_eq ?_)
  rw [norm_mul, norm_pow, Complex.norm_real]

/-- In logarithmic coordinates the scalar Mellin transform is the bilateral exponential integral. -/
theorem mellin_logProfile (f : ℝ → ℂ) (s : ℂ) :
    mellin (fun t ↦ f (Real.log t)) s = ∫ x : ℝ, f x * Complex.exp (s * x) := by
  rw [mellin, ← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add, mul_comm]
  congr 1
  ring_nf

private def scalarMomentTwist (J : Set ℝ) (b : J) (k : ℕ) :
    PositiveRealExponentialDecay J →ₗ[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ k)).toLinearMap.comp
    (logExponentialDecayTwist J b)

private theorem scalarMomentTwist_apply (J : Set ℝ) (b : J) (k : ℕ)
    (f : PositiveRealExponentialDecay J) (x : ℝ) :
    scalarMomentTwist J b k f x = (x : ℂ) ^ k * ((Real.exp (b * x) : ℂ) * f.val x) := by
  change SchwartzMap.smulLeftCLM _ _ _ x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), smul_eq_mul]
  exact congrArg ((x : ℂ) ^ k * ·) (logExponentialDecayTwist_apply J b f x)

private theorem scalarDecay_mellin_deriv {J : Set ℝ} (hJ : IsOpen J)
    (f : PositiveRealExponentialDecay J) (k : ℕ) {z : ℂ} (hz : z.re ∈ J) :
    iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z =
      mellin (fun t ↦ (Real.log t : ℂ) ^ k * f.val (Real.log t)) z := by
  obtain ⟨α, β, hz', hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ.mem_nhds hz)
  have hint (σ : ℝ) (hσ : σ ∈ Ioo α β) (j : ℕ) :
      Integrable (fun x : ℝ ↦ f.val x * (x : ℂ) ^ j * Complex.exp ((σ : ℂ) * x)) := by
    apply (scalarMomentTwist J ⟨σ, hsub hσ⟩ j f).integrable.congr
    filter_upwards with x
    rw [scalarMomentTwist_apply, Complex.ofReal_exp, Complex.ofReal_mul]
    ring
  rw [show mellin (fun t ↦ f.val (Real.log t)) = _ from funext (mellin_logProfile f.val),
    (iteratedDeriv_exp_moment hint k hz').2.2,
    mellin_logProfile (fun x ↦ (x : ℂ) ^ k * f.val x)]
  apply integral_congr_ae
  filter_upwards with x
  ring

private def scalarMomentTrace (J : Set ℝ) (b : J) (k : ℕ) :
    PositiveRealExponentialDecay J →ₗ[ℂ] SchwartzMap ℝ ℂ :=
  let reflect := schwartzChangeVariable ℂ (F := ℂ)
    (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv
  let scale := schwartzChangeVariable ℂ (F := ℂ)
    (LinearEquiv.smulOfNeZero ℝ ℝ (2 * Real.pi)⁻¹ (by positivity)).toContinuousLinearEquiv
  (reflect.trans ((FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)).trans scale)).toLinearEquiv.toLinearMap.comp
    (scalarMomentTwist J b k)

open scoped FourierTransform in
private theorem scalarMomentTrace_apply {J : Set ℝ} (hJ : IsOpen J) (b : J) (k : ℕ)
    (f : PositiveRealExponentialDecay J) (y : ℝ) :
    scalarMomentTrace J b k f y = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t)))
      (verticalPoint b y) := by
  have hre : (verticalPoint b y).re = b := by simp
  rw [scalarDecay_mellin_deriv hJ f k (by rw [hre]; exact b.property), mellin_eq_fourier]
  let r := schwartzChangeVariable ℂ (F := ℂ)
    (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv (scalarMomentTwist J b k f)
  change 𝓕 r ((2 * Real.pi)⁻¹ * y) = _
  rw [SchwartzMap.fourier_coe]
  simp only [hre, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
    zero_add, Real.log_exp, div_eq_inv_mul]
  apply congrArg (fun h : ℝ → ℂ ↦ 𝓕 h ((2 * Real.pi)⁻¹ * y))
  funext x
  change scalarMomentTwist J b k f (-x) = _
  rw [scalarMomentTwist_apply, Complex.real_smul]
  simp only [mul_neg, neg_mul]
  ring

open scoped FourierTransform in
private theorem scalarMomentTrace_energy (J : Set ℝ) (b : J) (k : ℕ)
    (f : PositiveRealExponentialDecay J) :
    ∫ y : ℝ, ‖scalarMomentTrace J b k f y‖ ^ 2 =
      (2 * Real.pi) * ∫ x : ℝ, ‖scalarMomentTwist J b k f x‖ ^ 2 := by
  let r := schwartzChangeVariable ℂ (F := ℂ)
    (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv (scalarMomentTwist J b k f)
  change (∫ y : ℝ, ‖𝓕 r ((2 * Real.pi)⁻¹ * y)‖ ^ 2) = _
  rw [MeasureTheory.Measure.integral_comp_mul_left (fun y : ℝ ↦ ‖𝓕 r y‖ ^ 2),
    inv_inv, abs_of_pos (by positivity), smul_eq_mul, SchwartzMap.integral_norm_sq_fourier]
  congr 1
  exact integral_neg_eq_self (fun x : ℝ ↦ ‖scalarMomentTwist J b k f x‖ ^ 2) volume

private def scalarTraceFamily {ι : Type*} [Fintype ι] (σ : ι → ℝ) (N : ℕ)
    (J : Set ℝ) (hσ : ∀ i, σ i ∈ J) (ν : Measure ℝ) [ν.HasTemperateGrowth] :
    PositiveRealExponentialDecay J →ₗ[ℂ]
      PiLp 2 (fun _ : ι ↦ PiLp 2 (fun _ : Fin (N + 1) ↦ Lp ℂ 2 ν)) :=
  { toFun f := WithLp.toLp 2 fun i ↦ WithLp.toLp 2 fun k ↦
      (scalarMomentTrace J ⟨σ i, hσ i⟩ k f).toLp 2 ν
    map_add' f g := by ext i k : 2; simp [map_add]; rfl
    map_smul' d f := by ext i k : 2; simp [map_smul]; rfl }

private theorem scalarTraceFamily_rep {ι : Type*} [Fintype ι] (σ : ι → ℝ) (N : ℕ)
    {J : Set ℝ} (hJ : IsOpen J) (hσ : ∀ i, σ i ∈ J) (ν : Measure ℝ) [ν.HasTemperateGrowth]
    (f : PositiveRealExponentialDecay J) (i : ι) (k : Fin (N + 1)) :
    (scalarTraceFamily σ N J hσ ν f i k : ℝ → ℂ) =ᵐ[ν] fun y ↦
      iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t))) (verticalPoint (σ i) y) :=
  ((scalarMomentTrace J ⟨σ i, hσ i⟩ k f).coeFn_toLp 2 ν).trans
    (ae_of_all _ fun y ↦ scalarMomentTrace_apply hJ _ _ _ y)

private theorem scalarTraceFamily_closure {ι : Type*} [Fintype ι] (σ : ι → ℝ) (N : ℕ)
    (ν : Measure ℝ) [ν.HasTemperateGrowth] :
    (scalarTraceFamily σ N univ (fun _ ↦ trivial) ν).range.topologicalClosure =
      hardySobolevTraceClosure σ N ν := by
  let T := scalarTraceFamily σ N univ (fun _ ↦ trivial) ν
  obtain ⟨M, hM, -⟩ := existsUnique_positiveRealFourierMellin univ isOpen_univ
    ordConnected_univ univ_nonempty
  have eqM (f : PositiveRealExponentialDecay univ) :
      (M f).val = mellin (fun t ↦ f.val (Real.log t)) := funext fun z ↦ hM f z trivial
  congr 1
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact Submodule.subset_span ⟨M f, by rw [eqM]; exact scalarTraceFamily_rep σ N isOpen_univ _ ν f⟩
  · apply Submodule.span_le.mpr
    rintro u ⟨F, hu⟩
    obtain ⟨f, rfl⟩ := M.surjective F
    refine ⟨f, ?_⟩
    ext i k : 2
    apply Lp.ext
    exact (scalarTraceFamily_rep σ N isOpen_univ _ ν f i k).trans (eqM f ▸ hu i k).symm

private theorem scalarMomentTwist_sum_energy {J : Set ℝ} (b : J) (N : ℕ)
    (f : PositiveRealExponentialDecay J) :
    ∑ k : Fin (N + 1), ∫ x : ℝ, ‖scalarMomentTwist J b k f x‖ ^ 2 =
      ∫ x : ℝ, ‖f.val x‖ ^ 2 * lineSobolevDensity b N x := by
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards with x
    simp only [scalarMomentTwist_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), lineSobolevDensity, ← Fin.sum_univ_eq_sum_range]
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show 2 * (b : ℝ) * x = b * x + b * x by ring, Real.exp_add,
      pow_mul x 2, ← sq_abs x]
    ring
  · intro k _
    exact ((scalarMomentTwist J b k f).memLp 2 volume).norm.integrable_sq

private theorem scalarTraceFamily_energy {ι : Type*} [Fintype ι] (σ : ι → ℝ) (N : ℕ)
    {J : Set ℝ} (hσ : ∀ i, σ i ∈ J) (ν : Measure ℝ) [ν.HasTemperateGrowth] (c : ℝ)
    (hc : 0 ≤ c) (hν : ν = ENNReal.ofReal c • volume) (f : PositiveRealExponentialDecay J) :
    ‖scalarTraceFamily σ N J hσ ν f‖ ^ 2 =
      ∑ i, (c * (2 * Real.pi)) * ∫ x : ℝ, ‖f.val x‖ ^ 2 * lineSobolevDensity (σ i) N x := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  rw [PiLp.norm_sq_eq_of_L2, ← scalarMomentTwist_sum_energy ⟨σ i, hσ i⟩ N f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change ‖(scalarMomentTrace J ⟨σ i, hσ i⟩ k f).toLp 2 ν‖ ^ 2 = _
  rw [SchwartzMap.norm_toLp' two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← one_div, ← Real.sqrt_eq_rpow,
    hν, integral_smul_measure,
    ENNReal.toReal_ofReal hc, smul_eq_mul, scalarMomentTrace_energy, mul_assoc]
  exact Real.sq_sqrt (by positivity)

/-- Paper: Theorem 9.2.1.2(2), p. 404. The Mellin transform extends to an isometric
isomorphism from the b-line Sobolev space onto the b-line Hardy–Sobolev space.
Deviation: Orders 0 through N on both sides and the Plancherel measure `dy/(2π)`, see
`ScalarLineSobolev` and `ScalarLineHardySobolev`. -/
theorem scalarLineSobolev_mellin (b : ℝ) (N : ℕ) :
    ∃ M : ScalarLineSobolev b N ≃ₗᵢ[ℂ] ScalarLineHardySobolev b N,
      ∀ (f : PositiveRealExponentialDecay univ) (u : ScalarLineSobolev b N),
        (u : ℝ → ℂ) =ᵐ[volume] f.val →
        ∀ k : Fin (N + 1), ((M u).val () k : ℝ → ℂ) =ᵐ[volume]
          fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
            (verticalPoint b y) := by
  let c := 1 / (2 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  let ν := ENNReal.ofReal c • (volume : Measure ℝ)
  let : ν.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul volume (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top
  let σ : Unit → ℝ := fun _ ↦ b
  let T := scalarTraceFamily σ N univ (fun _ ↦ trivial) ν
  let H := hardySobolevTraceClosure σ N ν
  have he : T.range.topologicalClosure = H := scalarTraceFamily_closure σ N ν
  let L := T.codRestrict H (fun f ↦ he ▸ T.range.le_topologicalClosure (LinearMap.mem_range_self T f))
  obtain ⟨j, _, hd, hj⟩ := scalarLineSobolev_dense b N
  have norm_eq (f : PositiveRealExponentialDecay univ) : ‖L f‖ = ‖j f‖ := by
    change ‖T f‖ = _
    rw [(hj f).2.2]
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _)
      (lineSobolevDensity_pos b N x).le)]
    have h := scalarTraceFamily_energy σ N (fun _ ↦ mem_univ _) ν c hc.le rfl f
    have hc' : c * (2 * Real.pi) = 1 := by dsimp [c]; field_simp
    simpa only [Fintype.sum_unique, hc', one_mul] using h
  have hclosed : IsClosed (H : Set (PiLp 2 (fun _ : Unit ↦ PiLp 2 (fun _ : Fin (N + 1) ↦ Lp ℂ 2 ν)))) :=
    he ▸ T.range.isClosed_topologicalClosure
  let : CompleteSpace H := hclosed.completeSpace_coe
  let M := L.extendOfIsometry (e := j.toLinearMap) hd norm_eq
  have hsur : Surjective M := by
    apply (range_eq_univ.mp ?_)
    apply Set.eq_univ_of_forall
    intro v
    let C := range M
    have hC : IsClosed C := M.isometry.isClosedEmbedding.isClosed_range
    have hpre : IsClosed ((Subtype.val : H → _) '' C) :=
      hclosed.isClosedEmbedding_subtypeVal.isClosedMap _ hC
    have hsub : (T.range : Set _) ⊆ Subtype.val '' C := by
      rintro _ ⟨f, rfl⟩
      exact ⟨L f, ⟨j f, LinearMap.extendOfIsometry_eq _ hd norm_eq f⟩, rfl⟩
    obtain ⟨u, hu, huv⟩ := closure_minimal hsub hpre (show v.val ∈ T.range.topologicalClosure from he.symm ▸ v.property)
    exact (Subtype.ext huv : u = v) ▸ hu
  refine ⟨LinearIsometryEquiv.ofSurjective M hsur, ?_⟩
  intro f u hu k
  have hμ : (volume.withDensity fun x ↦ ENNReal.ofReal (lineSobolevDensity b N x)) ≪ volume :=
    withDensity_absolutelyContinuous _ _
  have huf : u = j f := Lp.ext (hμ.ae_eq (hu.trans (hj f).1.symm))
  subst u
  change ((M (j f)).val () k : ℝ → ℂ) =ᵐ[volume] _
  rw [show M (j f) = L f from LinearMap.extendOfIsometry_eq _ hd norm_eq f]
  have h := scalarTraceFamily_rep σ N isOpen_univ (fun _ ↦ trivial) ν f () k
  have hae : ae ν = ae volume := Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.mpr hc).ne' volume
  rw [hae] at h
  exact h

/-- Paper: Corollary 9.2.1.4, p. 407. In the left half-plane each indicated derivative
evaluation is bounded on the part supported above the cutoff and is given by the moment integral.

Deviation: The functional is extended to the full source by precomposing with the support
projection. On supported tests it gives the derivative of the Mellin transform. The
normalization uses the corrected isometry in `scalarLineSobolev_mellin`. -/
theorem scalarLineSobolev_cutoff_eval (a b : ℝ) (_ha : 1 < a)
    (N k : ℕ) (_hk : k < N) (z : ℂ) (_hz : z.re < b) :
    ∃ Λ : ScalarLineSobolev b N →L[ℂ] ℂ,
      (∀ (f : ScalarLineSobolev b N), Integrable (fun x : ℝ ↦ (Ici (-Real.log a)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
        Λ f = ∫ x : ℝ, (Ici (-Real.log a)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) ∧
      ∀ (f : PositiveRealExponentialDecay univ) (u : ScalarLineSobolev b N),
        tsupport f.val ⊆ Ioi (-Real.log a) → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z := by
  obtain ⟨Λ, hΛ⟩ := lineSobolev_cutoff_moment_functional a b _ha N k z _hz
  refine ⟨Λ, hΛ, fun f u hsupp hu ↦ ?_⟩
  have hint : ∀ σ ∈ Ioo (z.re - 1) (z.re + 1), ∀ n : ℕ, Integrable
      (fun x : ℝ ↦ f.val x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) volume :=
    fun σ _ n ↦ integrable_logExponentialDecay_moment f σ n
  have hmel : mellin (fun t ↦ f.val (Real.log t)) =
      fun w : ℂ ↦ ∫ x : ℝ, f.val x * Complex.exp (w * (x : ℂ)) :=
    funext fun w ↦ mellin_comp_log_eq f.val w
  rw [hmel, (iteratedDeriv_exp_moment hint k ⟨by linarith, by linarith⟩).2.2]
  refine (hΛ u).2.trans (integral_congr_ae ?_)
  filter_upwards [hu] with x hx
  by_cases hmem : x ∈ Ici (-Real.log a)
  · rw [Set.indicator_of_mem hmem, hx]
  · have h0 : f.val x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦ hmem (Ioi_subset_Ici_self (hsupp h))
    rw [Set.indicator_of_notMem hmem, h0]

/-- Paper: Corollary 9.2.1.4, p. 407. The cutoff Mellin integral is holomorphic to
the left of the line and has the stated derivatives for every completed source class.
Deviation: As in `scalarLineSobolev_cutoff_eval`, apply the indicator to the source. -/
theorem scalarLineSobolev_cutoff_iteratedDeriv_mellin (a b : ℝ) (_ha : 1 < a)
    (N k : ℕ) (_hk : k < N) (f : ScalarLineSobolev b N) (z : ℂ) (_hz : z.re < b) :
    let u := (Ici (-Real.log a)).indicator (f : ℝ → ℂ)
    let M := fun w : ℂ ↦ ∫ x : ℝ, u x * Complex.exp (w * (x : ℂ))
    AnalyticAt ℂ M z ∧ iteratedDeriv k M z =
      ∫ x : ℝ, u x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  intro u M
  have h := iteratedDeriv_exp_moment (h := u) (α := z.re - 1) (β := b) (fun σ hσ n ↦ by
    obtain ⟨_, hΛ⟩ := lineSobolev_cutoff_moment_functional a b _ha N n (σ : ℂ)
      (by rw [Complex.ofReal_re]; exact hσ.2)
    exact (hΛ f).1) k ⟨by linarith, _hz⟩
  exact ⟨h.1, h.2.2⟩

/-- Below the abscissa `b`, the squared moment kernel divided by a number that dominates
`exp (2 * b * x)` decays exponentially on a half-line that is bounded below. -/
private theorem sq_moment_div_le {b σ L : ℝ} (hσ : σ < b) (hL : 0 ≤ L) (k : ℕ) {x r : ℝ}
    (hx : -L ≤ x) (hr : Real.exp (2 * b * x) ≤ r) :
    (|x| ^ k * Real.exp (σ * x)) ^ 2 * r⁻¹ ≤
      ((2 * k).factorial : ℝ) / (b - σ) ^ (2 * k) * Real.exp (2 * (b - σ) * L) *
        Real.exp (-((b - σ) * x)) := by
  have hη : 0 < b - σ := sub_pos.2 hσ
  have hrpos : 0 < r := (Real.exp_pos _).trans_le hr
  have hinv : r⁻¹ ≤ Real.exp (-(2 * b * x)) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hr
  have hfact : ((b - σ) * |x|) ^ (2 * k) ≤
      Real.exp ((b - σ) * |x|) * ((2 * k).factorial : ℝ) :=
    (div_le_iff₀ (Nat.cast_pos.2 (Nat.factorial_pos _))).1
      (Real.pow_div_factorial_le_exp _ (mul_nonneg hη.le (abs_nonneg x)) (2 * k))
  have hηk : 0 < (b - σ) ^ (2 * k) := pow_pos hη _
  have habs : |x| ^ (2 * k) ≤
      ((2 * k).factorial : ℝ) / (b - σ) ^ (2 * k) * Real.exp ((b - σ) * |x|) := by
    rw [mul_pow] at hfact
    rw [div_mul_eq_mul_div, le_div_iff₀ hηk]
    linarith
  have habsle : |x| ≤ x + 2 * L := abs_le.2 ⟨by linarith, by linarith⟩
  have hexp : Real.exp ((b - σ) * |x|) ≤ Real.exp ((b - σ) * (x + 2 * L)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left habsle hη.le)
  have he : Real.exp (σ * x) ^ 2 = Real.exp (2 * σ * x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcomb : Real.exp ((b - σ) * (x + 2 * L)) *
      (Real.exp (2 * σ * x) * Real.exp (-(2 * b * x))) =
      Real.exp (2 * (b - σ) * L) * Real.exp (-((b - σ) * x)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc (|x| ^ k * Real.exp (σ * x)) ^ 2 * r⁻¹
      = |x| ^ (2 * k) * (Real.exp (2 * σ * x) * r⁻¹) := by
        rw [mul_pow, he, ← pow_mul, mul_comm k 2, mul_assoc]
    _ ≤ ((2 * k).factorial : ℝ) / (b - σ) ^ (2 * k) * Real.exp ((b - σ) * (x + 2 * L)) *
          (Real.exp (2 * σ * x) * Real.exp (-(2 * b * x))) :=
        mul_le_mul (habs.trans (mul_le_mul_of_nonneg_left hexp (by positivity)))
          (mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le)
          (mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 hrpos.le)) (by positivity)
    _ = ((2 * k).factorial : ℝ) / (b - σ) ^ (2 * k) * Real.exp (2 * (b - σ) * L) *
          Real.exp (-((b - σ) * x)) := by
        rw [mul_assoc, hcomb]
        exact (mul_assoc _ _ _).symm

/-- The norm twist of a quasi-character is the quasi-character times the exponential of the
logarithmic module. -/
private theorem quasiCharacterNormTwist_eq_exp {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (χ : QuasiCharacter G) (w : ℂ) (g : G) :
    quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g =
      χ g * Complex.exp (w * (logModule m g : ℂ)) := by
  have hpos : 0 < ((m g).val : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero (m g).ne_zero)
  change χ g * ((((m g : ℝ≥0) : ℝ) : ℂ)) ^ w =
    χ g * Complex.exp (w * (Real.log ((m g).val : ℝ) : ℂ))
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hpos.ne'),
    ← Complex.ofReal_log hpos.le, mul_comm w]

/-- Differentiation under the integral sign for the norm twists of a quasi-character: if
every logarithmic moment against the real twists in an open interval is integrable, then the
twisted integral is holomorphic on the strip, and its `k`th derivative is the `k`th moment. -/
private theorem iteratedDeriv_normTwist_moment {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G)
    (χ : QuasiCharacter G) {u : G → ℂ} {α β : ℝ}
    (hint : ∀ σ ∈ Ioo α β, ∀ n : ℕ, Integrable (fun g ↦ u g * (logModule m g : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ)
    (k : ℕ) {z : ℂ} (hz : z.re ∈ Ioo α β) :
    AnalyticAt ℂ (fun w : ℂ ↦
        ∫ g, u g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ) z ∧
      Integrable (fun g ↦ u g * (logModule m g : ℂ) ^ k *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) μ ∧
      iteratedDeriv k (fun w : ℂ ↦
          ∫ g, u g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ) z =
        ∫ g, u g * (logModule m g : ℂ) ^ k *
          quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g ∂μ := by
  have hlog : Measurable (fun g ↦ Real.log ((m g).val : ℝ)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable.log
  have hmom (n : ℕ) (w : ℂ) : (fun g ↦ u g * (logModule m g : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g) =
      fun g ↦ u g * χ g * (logModule m g : ℂ) ^ n * Complex.exp (w * (logModule m g : ℂ)) := by
    funext g
    rw [quasiCharacterNormTwist_eq_exp]
    ring
  have hM : (fun w : ℂ ↦
      ∫ g, u g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ) =
      fun w ↦ ∫ g, u g * χ g * Complex.exp (w * (logModule m g : ℂ)) ∂μ := by
    funext w
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    show u g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g = _
    rw [quasiCharacterNormTwist_eq_exp, ← mul_assoc]
  have key := iteratedDeriv_exp_moment_of_measurable (μ := μ) (h := fun g ↦ u g * χ g) hlog
    (fun σ hσ n ↦ (hmom n (σ : ℂ)) ▸ hint σ hσ n) k hz
  rw [hM, hmom k z]
  exact key

section ModulatedLine

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ)

/-- For a Haar measure, a decaying exponential of the logarithmic module is integrable on
the part of the group where the logarithmic module is bounded below: translation by an
element of nontrivial module moves one compact band onto the next. -/
private theorem integrableOn_exp_neg_logModule (hm : IsModulation m) (μ : Measure G)
    [μ.IsHaarMeasure] {η : ℝ} (hη : 0 < η) (c : ℝ) :
    IntegrableOn (fun g ↦ Real.exp (-(η * logModule m g))) (logModule m ⁻¹' Ici c) μ := by
  let f (g : G) := Real.log ((m g).val : ℝ)
  have hpos (g : G) : 0 < ((m g).val : ℝ) :=
    NNReal.coe_pos.mpr (pos_of_ne_zero (m g).ne_zero)
  have hmul (g h : G) : f (g * h) = f g + f h := by
    simp only [f, map_mul, Units.val_mul, NNReal.coe_mul]
    exact Real.log_mul (hpos g).ne' (hpos h).ne'
  have hone : f 1 = 0 := by simp [f]
  have hproper : IsProperMap f := by
    let e : ℝ≥0ˣ ≃ₜ ℝ :=
      (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
    have he : (e ∘ m) = f := funext fun g ↦ (Real.log_of_pos (hpos g)).symm
    exact he ▸ e.isProperMap.comp hm.1
  have hfm : Measurable f := hproper.continuous.measurable
  obtain ⟨u, hu⟩ : ∃ u : G, 0 < f u := by
    obtain ⟨g, hg⟩ := hm.2
    have hn : f g ≠ 0 := by
      intro hz
      apply hg
      apply Units.ext
      apply NNReal.eq
      change ((m g).val : ℝ) = 1
      calc ((m g).val : ℝ) = Real.exp (f g) := (Real.exp_log (hpos g)).symm
        _ = 1 := by rw [hz, Real.exp_zero]
    rcases hn.lt_or_gt with h | h
    · refine ⟨g⁻¹, ?_⟩
      have hsum := hmul g⁻¹ g
      rw [inv_mul_cancel, hone] at hsum
      linarith
    · exact ⟨g, h⟩
  have hpow (j : ℕ) (g : G) : f (u ^ j * g) = j * f u + f g := by
    induction j with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc, hmul, ih]
      push_cast
      ring
  let B (j : ℕ) : Set G := f ⁻¹' Icc (c + j * f u) (c + (j + 1) * f u)
  have hB0 : μ (f ⁻¹' Icc c (c + f u)) < ⊤ :=
    (hproper.isCompact_preimage isCompact_Icc).measure_lt_top
  have hBj (j : ℕ) : μ (B j) = μ (f ⁻¹' Icc c (c + f u)) := by
    rw [← measure_preimage_mul μ (u ^ j) (B j)]
    congr 1
    ext g
    simp only [B, mem_preimage, mem_Icc, hpow]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hcover : f ⁻¹' Ici c ⊆ ⋃ j, B j := by
    intro g hg
    have hg' : c ≤ f g := hg
    have h0 : 0 ≤ (f g - c) / f u := div_nonneg (sub_nonneg.2 hg') hu.le
    have h1 := Nat.floor_le h0
    have h2 := Nat.lt_floor_add_one ((f g - c) / f u)
    rw [le_div_iff₀ hu] at h1
    rw [div_lt_iff₀ hu] at h2
    have hmem : f g ∈ Icc (c + (⌊(f g - c) / f u⌋₊ : ℝ) * f u)
        (c + ((⌊(f g - c) / f u⌋₊ : ℝ) + 1) * f u) := ⟨by linarith, by linarith⟩
    exact mem_iUnion.2 ⟨_, hmem⟩
  have hr : Real.exp (-(η * f u)) < 1 :=
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (mul_pos hη hu))
  have hsum : Summable fun j : ℕ ↦ Real.exp (-(η * (c + j * f u))) := by
    refine ((summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left
      (Real.exp (-(η * c)))).congr fun j ↦ ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hfin : ∫⁻ g in f ⁻¹' Ici c, ENNReal.ofReal (Real.exp (-(η * f g))) ∂μ < ⊤ :=
    calc ∫⁻ g in f ⁻¹' Ici c, ENNReal.ofReal (Real.exp (-(η * f g))) ∂μ
        ≤ ∫⁻ g in ⋃ j, B j, ENNReal.ofReal (Real.exp (-(η * f g))) ∂μ :=
          lintegral_mono_set hcover
      _ ≤ ∑' j, ∫⁻ g in B j, ENNReal.ofReal (Real.exp (-(η * f g))) ∂μ :=
          lintegral_iUnion_le B _
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (Real.exp (-(η * (c + j * f u)))) *
            μ (f ⁻¹' Icc c (c + f u)) := by
          refine tsum_le_tsum fun j ↦ ?_
          rw [← hBj j, ← setLIntegral_const]
          refine setLIntegral_mono' (hfm measurableSet_Icc) fun g hg ↦ ?_
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
            (neg_le_neg (mul_le_mul_of_nonneg_left hg.1 hη.le)))
      _ < ⊤ := by
          rw [ENNReal.tsum_mul_right]
          exact ENNReal.mul_lt_top hsum.tsum_ofReal_ne_top.lt_top hB0
  have hint : Integrable (fun g ↦ Real.exp (-(η * f g))) (μ.restrict (f ⁻¹' Ici c)) :=
    ⟨(Real.measurable_exp.comp (hfm.const_mul η).neg).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun g ↦ (Real.exp_pos _).le)).2 hfin⟩
  exact hint

/-- Above a cutoff of the logarithmic module, the moment kernel of a unitary quasi-character
twisted to an abscissa below `b` gives a continuous functional on the weighted L² space of a
Haar measure, for every density that dominates `exp (2 * b * x)`. -/
private theorem modulated_cutoff_moment_functional (hm : IsModulation m) (μ : Measure G)
    [μ.IsHaarMeasure] {ρ : ℝ → ℝ} (hρ : Measurable ρ) {b : ℝ}
    (hρge : ∀ x, Real.exp (2 * b * x) ≤ ρ x) {A : ℝ} (hA : 1 < A) (z : ℂ) (hz : z.re < b)
    (k : ℕ) (χ : QuasiCharacter G) (hχ : ∀ g, ‖χ g‖ = 1) :
    ∃ Λ : Lp ℂ 2 (μ.withDensity fun g ↦ ENNReal.ofReal (ρ (logModule m g))) →L[ℂ] ℂ,
      ∀ f : Lp ℂ 2 (μ.withDensity fun g ↦ ENNReal.ofReal (ρ (logModule m g))),
        Integrable (fun g ↦ (logModule m ⁻¹' Ici (-Real.log A)).indicator (⇑f) g *
          (logModule m g : ℂ) ^ k *
          quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) μ ∧
        Λ f = ∫ g, (logModule m ⁻¹' Ici (-Real.log A)).indicator (⇑f) g *
          (logModule m g : ℂ) ^ k *
          quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g ∂μ := by
  have hρpos (x : ℝ) : 0 < ρ x := (Real.exp_pos _).trans_le (hρge x)
  have hlog : Measurable (fun g ↦ Real.log ((m g).val : ℝ)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable.log
  have hρm : Measurable fun g ↦ ρ (logModule m g) := hρ.comp hlog
  have hU : MeasurableSet (logModule m ⁻¹' Ici (-Real.log A)) := hlog measurableSet_Ici
  have hker : Measurable fun g ↦ (logModule m g : ℂ) ^ k *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g :=
    ((Complex.measurable_ofReal.comp hlog).pow_const k).mul (map_continuous _).measurable
  have hη : 0 < b - z.re := sub_pos.2 hz
  have hint : Integrable (fun g ↦ ‖(logModule m ⁻¹' Ici (-Real.log A)).indicator
      (fun g ↦ (logModule m g : ℂ) ^ k *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) g‖ ^ 2 *
      (ρ (logModule m g))⁻¹) μ := by
    refine ((integrable_indicator_iff hU).2 (Integrable.const_mul
      (integrableOn_exp_neg_logModule m hm μ hη (-Real.log A))
      (((2 * k).factorial : ℝ) / (b - z.re) ^ (2 * k) *
        Real.exp (2 * (b - z.re) * Real.log A)))).mono'
      (((hker.indicator hU).norm.pow_const 2).mul hρm.inv).aestronglyMeasurable
      (Eventually.of_forall fun g ↦ ?_)
    beta_reduce
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (hρpos _).le))]
    by_cases hg : g ∈ logModule m ⁻¹' Ici (-Real.log A)
    · have hc : ‖quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g‖ =
          Real.exp (z.re * logModule m g) := by
        rw [quasiCharacterNormTwist_eq_exp, norm_mul, hχ g, one_mul, Complex.norm_exp]
        simp
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, norm_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, hc]
      exact sq_moment_div_le hz (Real.log_pos hA).le k
        (show -Real.log A ≤ logModule m g from hg) (hρge _)
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, norm_zero]
      simp
  obtain ⟨Λ, hΛ⟩ := weightedL2_pairing μ hρm (fun g ↦ hρpos _)
    (hker.indicator hU).aestronglyMeasurable hint
  refine ⟨Λ, fun f ↦ ?_⟩
  have hfun : (fun g ↦ (logModule m ⁻¹' Ici (-Real.log A)).indicator (⇑f) g *
      (logModule m g : ℂ) ^ k * quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) =
      fun g ↦ f g * (logModule m ⁻¹' Ici (-Real.log A)).indicator (fun g ↦
        (logModule m g : ℂ) ^ k *
          quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) g := by
    funext g
    by_cases hg : g ∈ logModule m ⁻¹' Ici (-Real.log A)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, mul_assoc]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul, zero_mul, mul_zero]
  rw [hfun]
  exact hΛ f

/-- Over the full exponent line, the Fourier–Mellin integral is the integral against the
quasi-character. -/
private theorem modulatedFourierMellin_univ (hm : IsModulation m) (μ : Measure G)
    (f : G → ℂ) (c : QuasiCharacter G) :
    modulatedFourierMellin m univ hm μ f c = ∫ g, f g * c g ∂μ := by
  unfold modulatedFourierMellin
  rw [Set.indicator_of_mem]
  exact mem_univ (quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 c)

section

private def sobolevLogEquiv : ℝ ≃ₜ ℝ≥0ˣ :=
  Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm

private theorem sobolevLogEquiv_log (x : ℝ) : Real.log (((sobolevLogEquiv x).val : ℝ≥0) : ℝ) = x := by
  change Real.log (Real.exp x) = x
  exact Real.log_exp x

private theorem sobolevLogEquiv_preserving : MeasurePreserving sobolevLogEquiv volume positiveRealHaar := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  refine ⟨sobolevLogEquiv.continuous.measurable, ?_⟩
  unfold positiveRealHaar
  congr 1
  funext x
  apply Units.ext
  exact Subtype.ext (Real.coe_toNNReal _ (Real.exp_pos x).le).symm

private theorem sobolevLog_ae {p : ℝ → Prop} (hp : ∀ᵐ x ∂volume, p x) :
    ∀ᵐ t ∂positiveRealHaar, p (Real.log (t.val : ℝ)) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let e := sobolevLogEquiv.toMeasurableEquiv
  have he : MeasurePreserving e volume positiveRealHaar := sobolevLogEquiv_preserving
  filter_upwards [(he.symm e).quasiMeasurePreserving.ae hp] with t ht
  obtain ⟨x, rfl⟩ := e.surjective t
  change p (Real.log ((sobolevLogEquiv x).val : ℝ))
  rw [sobolevLogEquiv_log]
  simpa only [e.symm_apply_apply] using ht

private def sobolevSplitEquiv (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m) :
    m.toMonoidHom.ker × ℝ≥0ˣ ≃ₜ G where
  toFun p := (p.1 : G) * τ p.2
  invFun x := (⟨x / τ (m x), by change m (x / τ (m x)) = 1; simp [map_div, hτ _]⟩, m x)
  left_inv p := by
    have hk : m (p.1 : G) = 1 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      change (p.1 : G) * τ p.2 / τ (m ((p.1 : G) * τ p.2)) = p.1
      rw [map_mul, hk, one_mul, hτ, mul_div_cancel_right]
    · change m ((p.1 : G) * τ p.2) = p.2
      rw [map_mul, hk, one_mul, hτ]
  right_inv x := by change x / τ (m x) * τ (m x) = x; simp [div_eq_mul_inv, mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by simp only [div_eq_mul_inv]; fun_prop

private theorem sobolev_log_proper (hm : IsModulation m) : IsProperMap (logModule m) := by
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he : (e ∘ m) = logModule m := funext fun g ↦
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (m g)))).symm
  exact he ▸ e.isProperMap.comp hm.1

/-- Cut off a Schwartz–Bruhat test in the log coordinate. Every real twist of the resulting
function is again Schwartz–Bruhat. -/
private theorem modulatedDecay_local (hm : IsModulation m) (J A : Set ℝ) (hA : IsOpen A)
    (x : G) (hx : logModule m x ∈ A) :
    ∃ f : ModulatedExponentialDecay m J, Continuous f.val ∧ HasCompactSupport f.val ∧
      tsupport f.val ⊆ (logModule m) ⁻¹' A ∧ f.val x ≠ 0 := by
  classical
  obtain ⟨δ, hδ, hv, _⟩ := schwartzBruhat_dirac_support x
  obtain ⟨F, hF⟩ : ∃ F : SchwartzBruhat G, F x ≠ 0 := by
    by_contra! h
    have hmem : x ∈ schwartzBruhatVanishingLocus δ :=
      Set.mem_sUnion.mpr ⟨univ, ⟨isOpen_univ, fun f _ ↦ (hδ f).trans (h f)⟩, trivial⟩
    simp only [hv, mem_compl_iff, mem_singleton_iff, not_true_eq_false] at hmem
  obtain ⟨φ, hφA, hcφ, hφ, _, hφx⟩ := exists_contDiff_tsupport_subset (n := ⊤) (hA.mem_nhds hx)
  let ψ := Complex.ofRealCLM ∘ φ
  have hcψ : HasCompactSupport ψ := hcφ.comp_left rfl
  have hsψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ := Complex.ofRealCLM.contDiff.comp hφ
  let l := logModule m
  let f (g : G) := ψ (l g) * F g
  have hf : f ∈ modulatedExponentialDecaySubmodule m J := by
    apply (Submodule.mem_iInf _).2
    intro b
    let v (y : ℝ) : ℂ := Real.exp (y * (b : ℝ))
    have hd : ContDiff ℝ (↑(⊤ : ℕ∞)) v := Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_id.mul contDiff_const))
    have hd' := hd.mul hsψ
    have hc : HasCompactSupport (v * ψ) := hcψ.mul_left
    have hb (k : ℕ) := (hc.iteratedFDeriv (𝕜 := ℝ) k).exists_bound_of_continuous (hd'.continuous_iteratedFDeriv (by simp))
    have hh := logModulation_mul_mem_schwartzBruhat m hd' hb F.property
    change modulationWeight m b f ∈ schwartzBruhatSubmodule G
    convert hh using 1
    funext g
    change (((((m g).val : ℝ) ^ (b : ℝ)) : ℝ) : ℂ) * (ψ (l g) * F g) =
      ((Real.exp (l g * (b : ℝ)) : ℂ) * ψ (l g)) * F g
    rw [Real.rpow_def_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (m g))), mul_assoc]
  have hp := sobolev_log_proper m hm
  have hsup : tsupport f ⊆ l ⁻¹' tsupport ψ :=
    tsupport_mul_subset_left.trans (tsupport_comp_subset_preimage ψ hp.continuous)
  refine ⟨⟨f, hf⟩, (hsψ.continuous.comp hp.continuous).mul (continuous_schwartzBruhat F),
    (hp.isCompact_preimage hcψ).of_isClosed_subset (isClosed_tsupport _) hsup,
    hsup.trans (preimage_mono ((tsupport_comp_subset (g := Complex.ofRealCLM) rfl φ).trans hφA)), ?_⟩
  change (φ (logModule m x) : ℂ) * F x ≠ 0
  simpa only [hφx, Complex.ofReal_one, one_mul] using hF

/-- Local tests and their character multiples determine the supported part of weighted L². -/
private theorem modulatedDecay_supported_closure (J : Set ℝ) {μ ν : Measure G} [ν.Regular]
    (hμ : μ ≪ ν) (hν : ν ≪ μ) (U V : Set G) (hUV : U ⊆ V) (hV : MeasurableSet V)
    (hboundary : ∀ᵐ x ∂ν, x ∈ V → x ∈ U)
    (hlocal : ∀ x ∈ U, ∃ f : ModulatedExponentialDecay m J,
      Continuous f.val ∧ MemLp f.val 2 ν ∧ tsupport f.val ⊆ U ∧ f.val x ≠ 0) :
    closure {u : Lp ℂ 2 ν | ∃ f : ModulatedExponentialDecay m J,
      tsupport f.val ⊆ U ∧ (u : G → ℂ) =ᵐ[μ] f.val} =
        {u : Lp ℂ 2 ν | (u : G → ℂ) =ᵐ[μ] V.indicator (u : G → ℂ)} := by
  classical
  let S : Submodule ℂ (Lp ℂ 2 ν) :=
    { carrier := {u | ∃ f : ModulatedExponentialDecay m J,
          tsupport f.val ⊆ U ∧ (u : G → ℂ) =ᵐ[μ] f.val}
      zero_mem' := ⟨0, by change tsupport (0 : G → ℂ) ⊆ _; simp, hμ.ae_eq (Lp.coeFn_zero ℂ 2 ν)⟩
      add_mem' := by
        rintro u v ⟨f, hf, hu⟩ ⟨g, hg, hv⟩
        exact ⟨f + g, (tsupport_add f.val g.val).trans (union_subset hf hg),
          (hμ.ae_eq (Lp.coeFn_add u v)).trans (hu.add hv)⟩
      smul_mem' := by
        rintro d u ⟨f, hf, hu⟩
        exact ⟨d • f, (tsupport_comp_subset (g := fun z : ℂ ↦ d • z) (smul_zero d) f.val).trans hf,
          (hμ.ae_eq (Lp.coeFn_smul d u)).trans (hu.const_smul d)⟩ }
  obtain ⟨P, _, hP⟩ := hardySobolevCutoff_spec (μ := ν) hV
  have hfix (u : Lp ℂ 2 ν) : P u = u ↔ (u : G → ℂ) =ᵐ[μ] V.indicator u := by
    constructor
    · intro h; simpa only [h] using hμ.ae_eq (hP u).2.2
    · intro h; exact Lp.ext ((hP u).2.2.trans (hν.ae_eq h).symm)
  change closure (S : Set (Lp ℂ 2 ν)) = _
  apply le_antisymm
  · apply closure_minimal
    · rintro u ⟨f, hf, hu⟩
      filter_upwards [hu] with x hx
      by_cases h : x ∈ V
      · simp [h]
      · rw [Set.indicator_of_notMem h, hx]
        exact image_eq_zero_of_notMem_tsupport (fun ht ↦ h (hUV (hf ht)))
    · simpa only [id_eq, ← hfix] using isClosed_eq P.continuous continuous_id
  · intro u hu
    change u ∈ S.topologicalClosure
    rw [← S.orthogonal_orthogonal_eq_closure]
    intro z hz
    choose f hc hm₂ hs hn using fun x : U ↦ hlocal x x.property
    have hzero (i : U) : ∀ᵐ x ∂ν, (f i).val x ≠ 0 → z x = 0 := by
      let t := (hm₂ i).toLp _
      have hi : Integrable (fun x ↦ z x * star ((f i).val x)) ν :=
        (L2.integrable_inner (𝕜 := ℂ) t z).congr ((hm₂ i).coeFn_toLp.mono fun x hx ↦ by
          simp only [RCLike.inner_apply, t, hx, Complex.star_def])
      apply (ae_eq_zero_of_lcaFourier_eq_zero ν hi ?_).mono
      · intro x hx hf
        exact (mul_eq_zero.mp (show z x * star ((f i).val x) = 0 from hx)).resolve_right (by simpa using hf)
      · intro χ
        let χf (x : G) := (χ x : ℂ) * (f i).val x
        have hχ : Continuous (fun x ↦ (χ x : ℂ)) := continuous_subtype_val.comp χ.continuous
        have hχ₂ : MemLp χf 2 ν := (hm₂ i).mono (hχ.mul (hc i)).aestronglyMeasurable
          (ae_of_all _ fun x ↦ by simp [χf])
        have hχf : χf ∈ modulatedExponentialDecaySubmodule m J := by
          apply (Submodule.mem_iInf _).2
          intro b
          obtain ⟨M, hM⟩ := schwartzBruhat_mul_unitaryCharacter χ
          let F := modulatedExponentialDecayTwist m J b (f i)
          have h : (M F).val = modulationWeight m b χf := by
            funext x
            rw [show (M F).val x = _ from hM F x]
            change (χ x : ℂ) * ((((m x).val : ℝ) ^ (b : ℝ) : ℝ) * (f i).val x) =
              ((((m x).val : ℝ) ^ (b : ℝ) : ℝ) : ℂ) * ((χ x : ℂ) * (f i).val x)
            ring
          change modulationWeight m b χf ∈ schwartzBruhatSubmodule G
          rw [← h]
          exact (M F).property
        have ht : hχ₂.toLp χf ∈ S := ⟨⟨χf, hχf⟩, tsupport_mul_subset_right.trans (hs i),
          hμ.ae_eq hχ₂.coeFn_toLp⟩
        refine (integral_congr_ae ?_).trans (show inner ℂ (hχ₂.toLp χf) z = 0 from hz _ ht)
        filter_upwards [hχ₂.coeFn_toLp] with x hx
        simp only [RCLike.inner_apply, hx, χf, Complex.star_def, map_mul]
        ring
    obtain ⟨T, hT, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable (fun i : U ↦ Function.support (f i).val)
      (fun i ↦ isOpen_ne_fun (hc i) continuous_const)
    have hall := (ae_ball_iff hT).2 (fun i _ ↦ hzero i)
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hall, hboundary, hν.ae_eq (show (u : G → ℂ) =ᵐ[μ] V.indicator u from hu)] with x hx hb hp
    by_cases hv : x ∈ V
    · let i : U := ⟨x, hb hv⟩
      have hmem : x ∈ ⋃ i ∈ T, Function.support (f i).val := hcover.symm ▸ mem_iUnion.mpr ⟨i, hn i⟩
      obtain ⟨i, hi, hfx⟩ := mem_iUnion₂.mp hmem
      rw [hx i hi hfx, inner_zero_left]; rfl
    · rw [Set.indicator_of_notMem hv] at hp
      rw [hp, inner_zero_right]; rfl

private theorem sobolev_log_preserving (hm : IsModulation m) (hsurj : Surjective m) :
    MeasurePreserving (logModule m) (canonicalModulatedHaar m hm) volume := by
  obtain ⟨τ, hτ⟩ := exists_section_of_surjective hm.1 hsurj
  let : CompactSpace m.toMonoidHom.ker := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure m.toMonoidHom.ker := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μ₁ := ⟨Measure.haarMeasure_self⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let e := (sobolevSplitEquiv m τ hτ).toMeasurableEquiv
  have he : MeasurePreserving e (μ₁.prod positiveRealHaar) (canonicalModulatedHaar m hm) :=
    ⟨e.measurable, (canonicalModulatedHaar_eq_map_prod m hm τ hτ μ₁ Measure.haarMeasure_self).symm⟩
  let d := sobolevLogEquiv.toMeasurableEquiv
  have hd : MeasurePreserving d volume positiveRealHaar := sobolevLogEquiv_preserving
  have h := ((hd.symm d).comp (measurePreserving_snd (μ := μ₁) (ν := positiveRealHaar))).comp (he.symm e)
  convert h using 1
  funext x
  change Real.log ((m x).val : ℝ) = d.symm (m x)
  obtain ⟨t, ht⟩ := d.surjective (m x)
  rw [← ht, d.symm_apply_apply]
  exact sobolevLogEquiv_log t

private theorem modulatedDecay_cutoff (hm : IsModulation m) (hsurj : Surjective m) (c : ℝ)
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hpos : ∀ t, 0 < ρ t) :
    let l := logModule m
    let μ := canonicalModulatedHaar m hm
    let ν := μ.withDensity fun x ↦ ENNReal.ofReal (ρ (l x))
    closure {u : Lp ℂ 2 ν | ∃ f : ModulatedExponentialDecay m univ,
      tsupport f.val ⊆ l ⁻¹' Ioi c ∧ (u : G → ℂ) =ᵐ[μ] f.val} =
        {u : Lp ℂ 2 ν | (u : G → ℂ) =ᵐ[μ] (l ⁻¹' Ici c).indicator (u : G → ℂ)} := by
  intro l μ ν
  let : μ.IsHaarMeasure := (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have hlog := (sobolev_log_proper m hm).continuous
  let : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal (hρ.comp hlog)
  have hw : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hv : μ ≪ ν := withDensity_absolutelyContinuous' (hρ.comp hlog).measurable.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos _)).ne')
  apply modulatedDecay_supported_closure m univ hv hw _ _ (preimage_mono Ioi_subset_Ici_self)
    (hlog.measurable measurableSet_Ici)
  · filter_upwards [hw.ae_le ((sobolev_log_preserving m hm hsurj).quasiMeasurePreserving.ae (volume.ae_ne c))] with x hx
    exact fun h ↦ (mem_Ici.mp h).lt_of_ne hx.symm
  · intro x hx
    obtain ⟨f, hf, hc, hs, hn⟩ := modulatedDecay_local m hm univ _ isOpen_Ioi x hx
    exact ⟨f, hf, hf.memLp_of_hasCompactSupport hc, hs, hn⟩

end

section

private theorem sobolev_stage_bound {A : Type*} [CommGroup A] [TopologicalSpace A]
    (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient)
    (f : SchwartzBruhatStage e) (x : A) :
    ‖schwartzBruhatStageRealization a e f x‖ ≤ elementarySchwartzSeminorm (0, 0, 0, 0) f := by
  classical
  rw [schwartzBruhatStageRealization_apply]
  split_ifs with hx
  · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
    change (‖f.val y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
    apply ENNReal.toReal_mono (f.property.2 _).ne
    rw [elementarySchwartzBound_zero]
    exact le_iSup (fun z ↦ (‖f.val z‖₊ : ENNReal)) _
  · exact norm_zero.le.trans (apply_nonneg _ _)

private theorem sobolev_bruhat_uniform {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] :
    ∃ q : Seminorm ℂ (SchwartzBruhat A), Continuous q ∧
      (∀ f x, ‖f x‖ ≤ q f) ∧ (∀ f C, 0 ≤ C → (∀ x, ‖f x‖ ≤ C) → q f ≤ C) := by
  have hbound (f : SchwartzBruhat A) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
    obtain ⟨a, e, v, hv⟩ := (mem_schwartzBruhatSubmodule_iff _).mp f.property
    exact ⟨_, fun x ↦ congrFun hv x ▸ sobolev_stage_bound a e v x⟩
  let L : SchwartzBruhat A →ₗ[ℂ] BoundedContinuousFunction A ℂ :=
    { toFun f := BoundedContinuousFunction.ofNormedAddCommGroup f.val (continuous_schwartzBruhat f)
        (hbound f).choose (hbound f).choose_spec
      map_add' f g := by ext; rfl
      map_smul' c f := by ext; rfl }
  let q := (normSeminorm ℂ (BoundedContinuousFunction A ℂ)).comp L
  have hq (f : SchwartzBruhat A) (C : ℝ) (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C) : q f ≤ C :=
    (BoundedContinuousFunction.norm_le (f := L f) hC).mpr h
  refine ⟨q, ?_, fun f x ↦ (L f).norm_coe_le_norm x, hq⟩
  apply (withGeneratingSeminorms_spec _ _).continuous_seminorm
    (⟨q, ?_⟩ : {p : Seminorm ℂ (schwartzBruhatSubmodule A) //
      ∀ a e, Continuous (p ∘ schwartzBruhatStageInclusion a e)})
  intro a e
  change Continuous (q.comp (schwartzBruhatStageInclusion a e) : Seminorm ℂ (SchwartzBruhatStage e))
  let Q : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
  have hQ : Continuous Q := elementarySchwartz_withSeminorms.continuous_seminorm _
  exact Seminorm.continuous_of_le (E := SchwartzBruhatStage e) hQ
    (fun f ↦ hq _ _ (apply_nonneg Q _) (sobolev_stage_bound a e f))

/-- Each fixed twist has a continuous uniform bound. At a compact-quotient stage the
bound follows from the corresponding Schwartz–Bruhat seminorm on the quotient. -/
private theorem sobolev_twist_seminorm (J : Set ℝ) (b : J) :
    ∃ p : Seminorm ℂ (ModulatedExponentialDecay m J), Continuous p ∧
      ∀ f g, Real.exp ((b : ℝ) * logModule m g) * ‖f.val g‖ ≤ p f := by
  refine (sobolev_bruhat_uniform (A := G)).elim fun q H ↦ ?_
  have hle := H.2.1
  have hq := H.2.2
  let p : Seminorm ℂ (ModulatedExponentialDecay m J) := q.comp (modulatedExponentialDecayTwist m J b)
  let K := {k : Subgroup G // IsCompact (k : Set G) ∧ IsCompactlyGeneratedGroup (lcaAnnihilator k)}
  have hp (k : K) : Continuous (p ∘ modulatedExponentialDecayStageInclusion m J k) := by
    let : IsClosed (k.val : Set G) := k.property.1.isClosed
    let : T1Space (G ⧸ k.val) := QuotientGroup.t1Space_iff.mpr k.property.1.isClosed
    let n := quotientModulation m k.val k.property.1
    refine (sobolev_bruhat_uniform (A := G ⧸ k.val)).elim fun q' H' ↦ ?_
    have hc' := H'.1
    have hle' := H'.2.1
    let Q : Seminorm ℂ (ModulatedExponentialDecayStage m J k) := q'.comp (modulatedExponentialDecayTwist n J b)
    have hQ : Continuous Q :=
      (withGeneratingSeminorms_spec _ _).continuous_seminorm (b, (⟨q', hc'⟩ : {p : Seminorm ℂ (SchwartzBruhat (G ⧸ k.val)) // Continuous p}))
    let P : Seminorm ℂ (ModulatedExponentialDecayStage m J k) := p.comp (modulatedExponentialDecayStageInclusion m J k)
    change Continuous P
    refine Seminorm.continuous_of_le (E := ModulatedExponentialDecayStage m J k) hQ (p := P) ?_
    intro f
    exact hq (modulatedExponentialDecayTwist m J b (modulatedExponentialDecayStageInclusion m J k f))
      (Q f) (apply_nonneg Q f) (fun x ↦ hle' (modulatedExponentialDecayTwist n J b f) (x : G ⧸ k.val))
  refine ⟨p, (withGeneratingSeminorms_spec _ _).continuous_seminorm
    (⟨p, hp⟩ : {q : Seminorm ℂ (modulatedExponentialDecaySubmodule m J) //
      ∀ k : K, Continuous (q ∘ modulatedExponentialDecayStageInclusion m J k)}), fun f g ↦ ?_⟩
  have hval := congrArg norm (modulatedExponentialDecayTwist_apply m J b f g)
  have hpos := NNReal.coe_pos.mpr (Units.zero_lt (m g))
  have hreal : ‖(((((m g).val : ℝ) ^ (b : ℝ)) : ℝ) : ℂ) * f.val g‖ =
      Real.exp ((b : ℝ) * logModule m g) * ‖f.val g‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _),
      Real.rpow_def_of_pos hpos, mul_comm (Real.log _) _]
  exact (hval.trans hreal).symm.le.trans (hle (modulatedExponentialDecayTwist m J b f) g)

/-- A nontrivial modulus tiles the log axis by translates of one compact band. -/
private theorem modulated_integrable_exp_neg_abs (hm : IsModulation m) (μ : Measure G) [μ.IsHaarMeasure]
    {δ : ℝ} (hδ : 0 < δ) : Integrable (fun x : G ↦ Real.exp (-δ * |logModule m x|)) μ := by
  let l := logModule m
  have hp := sobolev_log_proper m hm
  have hpos (g : G) : 0 < ((m g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hmul (g h : G) : l (g * h) = l g + l h := by
    simp only [l, map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos g).ne' (hpos h).ne']
  have hone : l 1 = 0 := by simp [l]
  obtain ⟨u, hu⟩ : ∃ u : G, 0 < l u := by
    obtain ⟨g, hg⟩ := hm.2
    have hne : l g ≠ 0 := by
      intro h
      apply hg
      apply Units.ext
      apply NNReal.eq
      change ((m g).val : ℝ) = 1
      rw [← Real.exp_log (hpos g), show Real.log ((m g).val : ℝ) = 0 from h, Real.exp_zero]
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨g⁻¹, by have hh := hmul g⁻¹ g; rw [inv_mul_cancel, hone] at hh; linarith⟩
    · exact ⟨g, h⟩
  let a := l u
  have ha : 0 < a := hu
  let s (k : ℤ) := l ⁻¹' Ico ((k : ℝ) * a) ((k : ℝ) * a + a)
  let f (g : G) := Real.exp (-δ * |l g|)
  have hf : Continuous f := Real.continuous_exp.comp (continuous_const.mul hp.continuous.abs)
  have hsm (k : ℤ) : MeasurableSet (s k) := hp.continuous.measurable measurableSet_Ico
  have hsc (k : ℤ) : IntegrableOn f (s k) μ :=
    (hf.continuousOn.integrableOn_compact (hp.isCompact_preimage isCompact_Icc)).mono_set
      (preimage_mono Ico_subset_Icc_self)
  have hseq (k : ℤ) : μ.real (s k) = μ.real (s 0) := by
    have ht : (fun g : G ↦ u ^ k * g) ⁻¹' s k = s 0 := by
      ext g
      change ((k : ℝ) * a ≤ l (u ^ k * g) ∧ l (u ^ k * g) < (k : ℝ) * a + a) ↔ _
      have hpow : l (u ^ k) = (k : ℝ) * a := by
        simp [l, a, map_zpow, Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, Real.log_zpow]
      simp [hmul, hpow, s]
    simpa only [ht, measureReal_def] using
      (congrArg ENNReal.toReal (measure_preimage_mul μ (u ^ k) (s k))).symm
  let q := Real.exp (-δ * a)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hδ) ha)
  have hgeom : Summable (fun n : ℕ ↦ q ^ n) := summable_geometric_of_lt_one (Real.exp_pos _).le hq
  have hsum : Summable (fun k : ℤ ↦ Real.exp (-δ * |(k : ℝ)| * a)) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;> convert hgeom using 1 <;> ext n <;>
      simp [q, ← Real.exp_nat_mul, mul_comm, mul_left_comm, mul_assoc]
  have hall : ⋃ k, s k = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro g
    refine ⟨⌊l g / a⌋, ?_⟩
    exact ⟨(le_div_iff₀ ha).mp (Int.floor_le _), by
      have hh := (div_lt_iff₀ ha).mp (Int.lt_floor_add_one (l g / a)); linarith⟩
  have hbound (k : ℤ) :
      (∫ g in s k, ‖f g‖ ∂μ) ≤ Real.exp (-δ * |(k : ℝ)| * a) * (Real.exp (δ * a) * μ.real (s 0)) := by
    have hle (g : G) (hg : g ∈ s k) : ‖f g‖ ≤ Real.exp (-δ * |(k : ℝ)| * a) * Real.exp (δ * a) := by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hg' : (k : ℝ) * a ≤ l g ∧ l g < (k : ℝ) * a + a := hg
      have h := abs_sub_abs_le_abs_sub ((k : ℝ) * a) (l g)
      rw [abs_mul, abs_of_pos ha, abs_of_nonpos (sub_nonpos.mpr hg'.1)] at h
      nlinarith [mul_le_mul_of_nonneg_left (show |(k : ℝ)| * a - |l g| ≤ a by linarith) hδ.le]
    have hfin : μ (s k) < ∞ := (measure_mono (preimage_mono Ico_subset_Icc_self)).trans_lt
      (hp.isCompact_preimage (isCompact_Icc (a := (k : ℝ) * a) (b := (k : ℝ) * a + a))).measure_lt_top
    calc
      _ ≤ _ := setIntegral_mono_on (hsc k).norm (integrableOn_const hfin.ne) (hsm k) hle
      _ = _ := by rw [setIntegral_const, hseq]; simp [mul_assoc, mul_left_comm, mul_comm]
  have hI := integrableOn_iUnion_of_summable_integral_norm hsc
    (Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hbound (hsum.mul_right _))
  rwa [hall, integrableOn_univ] at hI

private theorem sobolev_poly_exp_bound (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, (1 + |x|) ^ n ≤ C * Real.exp (δ * |x|) := by
  refine ⟨(n.factorial : ℝ) * Real.exp δ / δ ^ n, by positivity, fun x ↦ ?_⟩
  have h := (div_le_iff₀ (show 0 < (n.factorial : ℝ) by positivity)).mp
    (Real.pow_div_factorial_le_exp _ (mul_nonneg hδ.le (by positivity : 0 ≤ 1 + |x|)) n)
  rw [mul_pow, mul_add, mul_one, Real.exp_add] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hδ n)]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

private theorem sobolev_margin {J : Set ℝ} (hJ : IsOpen J) {a b : ℝ} (ha : a ∈ J) (hb : b ∈ J) :
    ∃ δ : ℝ, 0 < δ ∧ a - δ ∈ J ∧ b + δ ∈ J := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds ha)
  obtain ⟨η, hη, hηs⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds hb)
  let δ := min ε η / 2
  have hd : 0 < δ := half_pos (lt_min hε hη)
  refine ⟨δ, hd, hεs ?_, hηs ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hd]
    linarith [min_le_left ε η, show δ = min ε η / 2 from rfl]
  · rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hd]
    linarith [min_le_right ε η, show δ = min ε η / 2 from rfl]

private theorem sobolev_exp_margin {a b δ x t Q : ℝ} (hab : a ≤ b) (ht : 0 ≤ t)
    (h₁ : Real.exp ((a - δ) * x) * t ≤ Q) (h₂ : Real.exp ((b + δ) * x) * t ≤ Q) :
    t ^ 2 * (max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) * Real.exp (δ * |x|)) ≤
      Q ^ 2 * Real.exp (-δ * |x|) := by
  have h (d e : ℝ) (he : d * x + δ * |x| = e * x) (hQ : Real.exp (e * x) * t ≤ Q) :
      t ^ 2 * (Real.exp (2 * d * x) * Real.exp (δ * |x|)) ≤ Q ^ 2 * Real.exp (-δ * |x|) := by
    have hsq := pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le ht) hQ 2
    calc
      _ = (Real.exp (e * x) * t) ^ 2 * Real.exp (-δ * |x|) := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_right_comm _ (t ^ 2), ← Real.exp_add, ← Real.exp_add,
          mul_comm (t ^ 2)]
        congr 2
        push_cast
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
  rcases le_total 0 x with hx | hx
  · rw [max_eq_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hx))]
    exact h b (b + δ) (by rw [abs_of_nonneg hx]; ring) h₂
  · rw [max_eq_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith) hx))]
    exact h a (a - δ) (by rw [abs_of_nonpos hx]; ring) h₁

private theorem weightedL2_le_majorant {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ρ : X → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x)
    (u : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (ρ x))) (f : X → ℂ)
    (hf : (u : X → ℂ) =ᵐ[μ] f) (H : X → ℝ) (hi : Integrable H μ)
    (q : ℝ) (hq : 0 ≤ q) (h : ∀ x, ‖f x‖ ^ 2 * ρ x ≤ q ^ 2 * H x) :
    ‖u‖ ≤ q * Real.sqrt (∫ x, H x ∂μ) := by
  obtain ⟨h₂, he⟩ := weightedL2_norm_eq μ hρ hpos u
  have hle : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 * ρ x ≤ q ^ 2 * H x :=
    hf.mono fun x hx ↦ (congrArg (fun z : ℂ ↦ ‖z‖ ^ 2 * ρ x) hx).le.trans (h x)
  have hmono := integral_mono_ae h₂ (hi.const_mul (q ^ 2)) hle
  rw [integral_const_mul] at hmono
  exact he.le.trans ((Real.sqrt_le_sqrt hmono).trans_eq (by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq]))

private theorem sobolev_continuous_of_bound {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →ₗ[ℂ] F) (q : Seminorm ℂ E) (hq : Continuous q) (C : ℝ) (h : ∀ f, ‖L f‖ ≤ q f * C) :
    Continuous L := by
  apply continuous_of_continuousAt_zero L.toAddMonoidHom
  change Tendsto L (𝓝 0) (𝓝 (L 0))
  rw [map_zero, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) h (by simpa only [map_zero, zero_mul] using (hq.tendsto 0).mul_const C)

/-- A continuous seminorm bound by an integrable majorant gives the weighted L² inclusion.
The local test criterion supplies its dense range. -/
private theorem modulatedDecay_embed (hm : IsModulation m) (J : Set ℝ) (c : J)
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (q : Seminorm ℂ (ModulatedExponentialDecay m J)) (hq : Continuous q)
    (H : G → ℝ) (hi : Integrable H (canonicalModulatedHaar m hm))
    (hbound : ∀ (f : ModulatedExponentialDecay m J) x, ‖f.val x‖ ^ 2 * ρ (logModule m x) ≤ (q f) ^ 2 * H x) :
    let μ := canonicalModulatedHaar m hm
    let ν := μ.withDensity fun x ↦ ENNReal.ofReal (ρ (logModule m x))
    ∃ j : ModulatedExponentialDecay m J →L[ℂ] Lp ℂ 2 ν,
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : G → ℂ) =ᵐ[μ] f.val := by
  intro μ ν
  let : μ.IsHaarMeasure := (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have hl := (sobolev_log_proper m hm).continuous
  have hρ' := hρ.comp hl
  let : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hρ'
  have hw : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hv : μ ≪ ν := withDensity_absolutelyContinuous' hρ'.measurable.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos _)).ne')
  have cont (f : ModulatedExponentialDecay m J) : Continuous f.val := by
    let F := modulatedExponentialDecayTwist m J c f
    have h (x : G) : (Real.exp (-(logModule m x * (c : ℝ))) : ℂ) * F x = f.val x := by
      rw [show F x = _ from modulatedExponentialDecayTwist_apply m J c f x,
        Real.rpow_def_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (m x))), ← mul_assoc, ← Complex.ofReal_mul,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]
    exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hl.mul continuous_const).neg)).mul
      (continuous_schwartzBruhat F)).congr h
  have hint (f : ModulatedExponentialDecay m J) :
      Integrable (fun x ↦ ‖f.val x‖ ^ 2 * ρ (logModule m x)) μ := by
    apply (hi.const_mul ((q f) ^ 2)).mono' (((cont f).norm.pow 2).mul hρ').aestronglyMeasurable
    exact ae_of_all _ fun x ↦ (Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hpos _).le)).le.trans (hbound f x)
  have mem (f : ModulatedExponentialDecay m J) : MemLp f.val 2 ν := by
    apply (memLp_two_iff_integrable_sq_norm (cont f).aestronglyMeasurable).2
    apply (integrable_withDensity_iff hρ'.measurable.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
    simpa only [comp_apply, ENNReal.toReal_ofReal (hpos _).le] using hint f
  let L : ModulatedExponentialDecay m J →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun f := (mem f).toLp f.val
      map_add' f g := MemLp.toLp_add (mem f) (mem g)
      map_smul' d f := MemLp.toLp_const_smul d (mem f) }
  have rep (f : ModulatedExponentialDecay m J) : (L f : G → ℂ) =ᵐ[μ] f.val := hv.ae_eq (mem f).coeFn_toLp
  have bound (f : ModulatedExponentialDecay m J) : ‖L f‖ ≤ q f * Real.sqrt (∫ x, H x ∂μ) :=
    weightedL2_le_majorant (ρ := fun x ↦ ρ (logModule m x)) hρ'.measurable (fun x ↦ hpos _) (L f) f.val
      (rep f) H hi (q f) (apply_nonneg q f) (hbound f)
  have hL : Continuous L := sobolev_continuous_of_bound L q hq _ bound
  refine ⟨⟨L, hL⟩, ?_, ?_, rep⟩
  · intro f g h
    change L f = L g at h
    exact Subtype.ext (Measure.eq_of_ae_eq ((rep f).symm.trans
      ((congrArg (fun v : Lp ℂ 2 ν ↦ (v : G → ℂ)) h).eventuallyEq.trans (rep g))) (cont f) (cont g))
  intro u
  have hh := modulatedDecay_supported_closure m J hv hw univ univ (Subset.rfl) MeasurableSet.univ
    (ae_of_all _ fun _ h ↦ h) (fun x _ ↦ by
      obtain ⟨f, hf, _, _, hn⟩ := modulatedDecay_local m hm J univ isOpen_univ x trivial
      exact ⟨f, hf, mem f, subset_univ _, hn⟩)
  have hu : u ∈ {y : Lp ℂ 2 ν | (y : G → ℂ) =ᵐ[μ] univ.indicator y} := by
    change (u : G → ℂ) =ᵐ[μ] univ.indicator u
    rw [indicator_univ]
  rw [← hh] at hu
  apply closure_mono _ hu
  rintro t ⟨f, _, ht⟩
  exact ⟨f, Lp.ext (hw.ae_eq ((rep f).trans ht.symm))⟩

private theorem modulatedDecay_dense_of_weight (hm : IsModulation m) (J : Set ℝ) (hJ : IsOpen J)
    (a b : ℝ) (hab : a ≤ b) (ha : a ∈ J) (hb : b ∈ J) (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (D : ℝ) (hD : 0 ≤ D) (n : ℕ)
    (hle : ∀ x, ρ x ≤ D * (1 + |x|) ^ n * max (Real.exp (2 * a * x)) (Real.exp (2 * b * x))) :
    let μ := canonicalModulatedHaar m hm
    let ν := μ.withDensity fun x ↦ ENNReal.ofReal (ρ (logModule m x))
    ∃ j : ModulatedExponentialDecay m J →L[ℂ] Lp ℂ 2 ν,
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : G → ℂ) =ᵐ[μ] f.val := by
  intro μ ν
  let margin := sobolev_margin hJ ha hb
  let δ := margin.choose
  have hd : 0 < δ := margin.choose_spec.1
  let poly := sobolev_poly_exp_bound n hd
  let C := poly.choose
  have hC : 0 ≤ C := poly.choose_spec.1
  have hpoly := poly.choose_spec.2
  let pa := sobolev_twist_seminorm m J ⟨a - δ, margin.choose_spec.2.1⟩
  let pb := sobolev_twist_seminorm m J ⟨b + δ, margin.choose_spec.2.2⟩
  let p := pa.choose
  let q := pb.choose
  have hp : Continuous p := pa.choose_spec.1
  have hq : Continuous q := pb.choose_spec.1
  have hpa := pa.choose_spec.2
  have hqb := pb.choose_spec.2
  let : μ.IsHaarMeasure := (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have hi := modulated_integrable_exp_neg_abs m hm μ hd
  have hpoint (f : ModulatedExponentialDecay m J) (g : G) :
      ‖f.val g‖ ^ 2 * ρ (logModule m g) ≤ ((p + q) f) ^ 2 * (D * C * Real.exp (-δ * |logModule m g|)) := by
    let x := logModule m g
    let t := ‖f.val g‖
    let W := max (Real.exp (2 * a * x)) (Real.exp (2 * b * x))
    have hW : 0 ≤ W := (Real.exp_pos _).le.trans (le_max_left _ _)
    have hh := sobolev_exp_margin (δ := δ) (x := x) hab (norm_nonneg (f.val g))
      ((hpa f g).trans (le_add_of_nonneg_right (apply_nonneg q f)))
      ((hqb f g).trans (le_add_of_nonneg_left (apply_nonneg p f)))
    change t ^ 2 * ρ x ≤ (p f + q f) ^ 2 * (D * C * Real.exp (-δ * |x|))
    calc
      _ ≤ t ^ 2 * (D * (C * Real.exp (δ * |x|)) * W) :=
        mul_le_mul_of_nonneg_left ((hle x).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hpoly x) hD) hW)) (sq_nonneg _)
      _ = D * C * (t ^ 2 * (W * Real.exp (δ * |x|))) := by ring
      _ ≤ D * C * ((p f + q f) ^ 2 * Real.exp (-δ * |x|)) :=
        mul_le_mul_of_nonneg_left hh (mul_nonneg hD hC)
      _ = _ := by ring
  exact modulatedDecay_embed m hm J ⟨a, ha⟩ ρ hρ hpos (p + q) (hp.add hq)
    (fun g ↦ (D * C) * Real.exp (-δ * |logModule m g|)) (hi.const_mul _) hpoint

private theorem sobolev_line_poly_bound (b : ℝ) (N : ℕ) (x : ℝ) : lineSobolevDensity b N x ≤ ((N : ℝ) + 1) * (1 + |x|) ^ (2 * N) *
    max (Real.exp (2 * b * x)) (Real.exp (2 * b * x)) := by
  rw [max_self, lineSobolevDensity, mul_comm (Real.exp _)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    _ ≤ ∑ _k ∈ Finset.range (N + 1), (1 + |x|) ^ (2 * N) := by
      apply Finset.sum_le_sum
      intro k hk
      calc x ^ (2 * k) ≤ |x| ^ (2 * k) := le_abs_self _ |>.trans_eq (abs_pow x _)
           _ ≤ (1 + |x|) ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg x) (by linarith) _
           _ ≤ _ := pow_le_pow_right₀ (by linarith [abs_nonneg x]) (by have := Finset.mem_range.mp hk; omega)
    _ = _ := by simp

end

/-- Paper: Theorem 9.2.1.5(1), p. 408. With canonical Haar measure, the
exponential-decay tests complete to the weighted L² on the group.
Deviation: The squared norm sums the squared moments through order N in (9.2.1.19). -/
theorem modulatedLineSobolev_dense (hm : IsModulation m) (_hms : Surjective m)
    (b : ℝ) (N : ℕ) :
    let μ := canonicalModulatedHaar m hm
    ∃ j : ModulatedExponentialDecay m univ →L[ℂ] LineSobolev μ (logModule m) b N,
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : G → ℂ) =ᵐ[μ] f.val := by
  intro μ
  let h := modulatedDecay_dense_of_weight m hm univ isOpen_univ b b le_rfl trivial trivial
    (lineSobolevDensity b N) (continuous_lineSobolevDensity b N) (lineSobolevDensity_pos b N) (N + 1) (by positivity) (2 * N) (sobolev_line_poly_bound b N)
  exact h

/-- Paper: Theorem 9.2.1.5(1), p. 408. On a split modulated group the closed
cutoff range is the closure of the tests with support strictly above the cutoff.
Deviation: The section to all positive reals in the paper entails surjectivity. -/
theorem modulatedLineSobolev_cutoff_closure (hm : IsModulation m) (_hms : Surjective m)
    (a b : ℝ) (_ha : 1 < a) (N : ℕ) :
    let μ := canonicalModulatedHaar m hm
    closure {u : LineSobolev μ (logModule m) b N |
      ∃ f : ModulatedExponentialDecay m univ,
        tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log a) ∧
          (u : G → ℂ) =ᵐ[μ] f.val} =
      {u : LineSobolev μ (logModule m) b N |
        (u : G → ℂ) =ᵐ[μ] ((logModule m) ⁻¹' Ici (-Real.log a)).indicator (u : G → ℂ)} := by
  exact modulatedDecay_cutoff m hm _hms (-Real.log a) _ (continuous_lineSobolevDensity b N)
    (lineSobolevDensity_pos b N)

section

private theorem sobolevSplit_tensor (hm : IsModulation m) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    [mK : MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (hμ₁ : μ₁ univ = 1)
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) :
    let μ := canonicalModulatedHaar m hm
    let η := volume.withDensity fun x ↦ ENNReal.ofReal (ρ x)
    let μw := μ.withDensity fun g ↦ ENNReal.ofReal (ρ (logModule m g))
    ∃ P : Lp ℂ 2 μw ≃ₗᵢ[ℂ] UniformSpace.Completion (Lp ℂ 2 η ⊗[ℂ] Lp ℂ 2 μ₁),
      ∀ (f : Lp ℂ 2 η) (g : Lp ℂ 2 μ₁) (u : Lp ℂ 2 μw),
        (fun p : m.toMonoidHom.ker × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[μ₁.prod positiveRealHaar]
          (fun p ↦ f (Real.log (p.2.val : ℝ)) * g p.1) → P u = ↑(f ⊗ₜ[ℂ] g) := by
  have hmK : mK = Subtype.instMeasurableSpace := by
    apply Eq.trans (BorelSpace.measurable_eq (α := m.toMonoidHom.ker))
    let : MeasurableSpace m.toMonoidHom.ker := Subtype.instMeasurableSpace
    exact (BorelSpace.measurable_eq (α := m.toMonoidHom.ker)).symm
  subst mK
  intro μ η μw
  let : CompactSpace m.toMonoidHom.ker := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let d := (MeasurableEquiv.prodComm : ℝ × m.toMonoidHom.ker ≃ᵐ _).trans
    ((MeasurableEquiv.refl _).prodCongr sobolevLogEquiv.toMeasurableEquiv)
  have hd : MeasurePreserving d (volume.prod μ₁) (μ₁.prod positiveRealHaar) :=
    ((MeasurePreserving.id μ₁).prod sobolevLogEquiv_preserving).comp Measure.measurePreserving_swap
  let e := (sobolevSplitEquiv m τ hτ).toMeasurableEquiv
  have he : MeasurePreserving e (μ₁.prod positiveRealHaar) μ :=
    ⟨e.measurable, (canonicalModulatedHaar_eq_map_prod m hm τ hτ μ₁ hμ₁).symm⟩
  let φ := d.trans e
  have hφ : MeasurePreserving φ (volume.prod μ₁) μ := he.comp hd
  have hlog (p : ℝ × m.toMonoidHom.ker) : logModule m (φ p) = p.1 := by
    change Real.log ((m ((p.2 : G) * τ (sobolevLogEquiv p.1))).val : ℝ) = _
    rw [map_mul, show m (p.2 : G) = 1 from p.2.property, one_mul, hτ]
    exact sobolevLogEquiv_log _
  have hw : MeasurePreserving φ (η.prod μ₁) μw := by
    refine ⟨φ.measurable, ?_⟩
    ext s hs
    rw [Measure.map_apply φ.measurable hs, show η.prod μ₁ = _ from
      prod_withDensity_left (μ := volume) (ν := μ₁) hρ.measurable.ennreal_ofReal,
      withDensity_apply _ (φ.measurable hs), withDensity_apply _ hs,
      ← hφ.setLIntegral_comp_preimage_emb φ.measurableEmbedding _ s]
    simp only [hlog]
  let L := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ φ hw
  have hsur : Surjective L := by
    intro v
    refine ⟨Lp.compMeasurePreserving φ.symm (hw.symm φ) v, ?_⟩
    change Lp.compMeasurePreserving φ hw _ = _
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.symm_comp_self] using Lp.compMeasurePreserving_id_apply v
  obtain ⟨A, hA⟩ := exists_l2TensorProduct_isometry η μ₁
  refine ⟨(LinearIsometryEquiv.ofSurjective L hsur).trans A.symm, fun f g u hu ↦ ?_⟩
  apply A.injective
  change A (A.symm (L u)) = _
  rw [A.apply_symm_apply]
  apply Lp.ext
  have hac : η.prod μ₁ ≪ volume.prod μ₁ := by
    rw [show η.prod μ₁ = _ from prod_withDensity_left (μ := volume) (ν := μ₁) hρ.measurable.ennreal_ofReal]
    exact withDensity_absolutelyContinuous _ _
  filter_upwards [Lp.coeFn_compMeasurePreserving u hw, hA f g, hac.ae_le (hd.quasiMeasurePreserving.ae hu)] with p hx hy hz
  change (L u) p = _
  rw [show (L u) p = u (φ p) from hx, hy]
  change u (φ p) = f (Real.log ((sobolevLogEquiv p.1).val : ℝ)) * g p.2 at hz
  simpa only [sobolevLogEquiv_log] using hz

open UniformSpace in
private theorem exists_completion_isometry {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) :
    ∃ P : Completion E ≃ₗᵢ[ℂ] Completion F, ∀ x : E, P ↑x = ↑(e x) := by
  let i : E →ₗ[ℂ] Completion E := Completion.toComplL.toLinearMap
  let j : F →ₗ[ℂ] Completion F := Completion.toComplL.toLinearMap
  have h (x : E) : ‖j (e x)‖ = ‖i x‖ := by
    change ‖(↑(e x) : Completion F)‖ = ‖(↑x : Completion E)‖
    simp
  exact ⟨e.toLinearEquiv.extendOfIsometry i j Completion.denseRange_coe Completion.denseRange_coe h,
    e.toLinearEquiv.extendOfIsometry_eq i j Completion.denseRange_coe Completion.denseRange_coe h⟩

end

/-- Paper: Theorem 9.2.1.5(2), p. 408. In split coordinates the Hilbert tensor
extension takes an elementary product to the kernel factor tensored with its scalar
vertical derivative traces.
Deviation: The kernel L² stays in the physical coordinates of the displayed target.
The source includes order N as printed in (9.2.1.19). The vertical measure is
`dy/(2π)` and both Hilbert norms sum the squared norms through order N. -/
theorem modulatedLineSobolev_mellin (hm : IsModulation m)
    (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (a b : ℝ) (_ha : 1 < a) (N : ℕ) :
    let μ := canonicalModulatedHaar m hm
    let ν : Measure ℝ := ENNReal.ofReal (1 / (2 * Real.pi)) • volume
    let H := ScalarLineHardySobolev b N
    ∃ M : LineSobolev μ (logModule m) b N ≃ₗᵢ[ℂ]
        UniformSpace.Completion (Lp ℂ 2 μ₁ ⊗[ℂ] H),
      ∀ (g : Lp ℂ 2 μ₁) (f : PositiveRealExponentialDecay univ)
        (u : LineSobolev μ (logModule m) b N),
        (fun p : m.toMonoidHom.ker × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[
          μ₁.prod positiveRealHaar] (fun p ↦ g p.1 * f.val (Real.log (p.2.val : ℝ))) →
        ∃ v : H, (∀ k : Fin (N + 1), (v.val () k : ℝ → ℂ) =ᵐ[ν]
            fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
              (verticalPoint b y)) ∧ M u = ↑(g ⊗ₜ[ℂ] v) := by
  intro μ ν H
  let : InnerProductSpace ℂ H := Submodule.innerProductSpace H
  have hPex := sobolevSplit_tensor m hm τ _hτ μ₁ _hμ₁ (lineSobolevDensity b N) (continuous_lineSobolevDensity b N)
  let P := hPex.choose
  have hP := hPex.choose_spec
  have hSex := scalarLineSobolev_mellin b N
  let S := hSex.choose
  have hS := hSex.choose_spec
  have hjex := scalarLineSobolev_dense b N
  let j := hjex.choose
  have hj := hjex.choose_spec.2.2
  let e := (TensorProduct.commIsometry ℂ (ScalarLineSobolev b N) (Lp ℂ 2 μ₁)).trans (S.lTensor (Lp ℂ 2 μ₁))
  have hQex := exists_completion_isometry e
  let Q := hQex.choose
  have hQ := hQex.choose_spec
  refine ⟨P.trans Q, fun g f u hu ↦ ⟨S (j f), fun k ↦ ?_, ?_⟩⟩
  · exact (show ν ≪ volume from Measure.smul_absolutelyContinuous).ae_eq (hS f (j f) (hj f).1 k)
  · change Q (P u) = _
    refine (congrArg Q (hP (j f) g u ?_)).trans (hQ _)
    filter_upwards [hu, (Measure.quasiMeasurePreserving_snd (μ := μ₁) (ν := positiveRealHaar)).ae
          (sobolevLog_ae (hj f).1)] with p hp hf
    change (j f) (Real.log (p.2.val : ℝ)) = f.val _ at hf
    simpa only [hf, mul_comm] using hp

-- The coefficient only uses the probability measure on the kernel. Keep the ambient hypotheses.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem 9.2.1.5(2), p. 408, and Equation (9.2.1.25), p. 409.
Taking the isotype coefficient of a line Mellin tensor multiplies the scalar trace
by the kernel Fourier coefficient at the inverse character, as in (D.3.3.14).

Deviation: The split Mellin formulas on pp. 403 and 416 omit the compact character. We take the
coefficient with the positive character factor of (9.2.1.25), expressed as Fourier evaluation at
the inverse character.
-/
theorem modulatedLineSobolev_mellin_isotype
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (b : ℝ) (N : ℕ) (ω : PontryaginDual m.toMonoidHom.ker) :
    let H := ScalarLineHardySobolev b N
    ∃ coefficient : UniformSpace.Completion (Lp ℂ 2 μ₁ ⊗[ℂ] H) →L[ℂ] H,
      ∀ (g : Lp ℂ 2 μ₁) (v : H),
        coefficient ↑(g ⊗ₜ[ℂ] v) = lcaFourier μ₁ g ω⁻¹ • v := by
  intro H
  let : IsProbabilityMeasure μ₁ := ⟨_hμ₁⟩
  let ψ (x : m.toMonoidHom.ker) : ℂ := (ω⁻¹ x : Circle)
  have hψ : MemLp ψ 2 μ₁ := MemLp.of_bound
    (continuous_subtype_val.comp (ω⁻¹).continuous).aestronglyMeasurable 1
    (.of_forall fun x ↦ (Circle.norm_coe (ω⁻¹ x)).le)
  let L := innerSL ℂ (hψ.toLp ψ)
  have hL (g : Lp ℂ 2 μ₁) : L g = lcaFourier μ₁ g ω⁻¹ := by
    rw [lcaFourier]
    change (∫ x, inner ℂ (hψ.toLp ψ x) (g x) ∂μ₁) = _
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp] with x hx
    rw [hx]
    rfl
  let A : (Lp ℂ 2 μ₁ ⊗[ℂ] H) →L[ℂ] H :=
    (TensorProduct.lidIsometry ℂ H).toContinuousLinearEquiv.toContinuousLinearMap.comp (L.rTensor H)
  let : CompleteSpace H := inferInstanceAs (CompleteSpace (Submodule.topologicalClosure _))
  refine ⟨A.fromCompletion, fun g v ↦ ?_⟩
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  simp [A, hL]

-- TODO(paper-gap): Theorem 9.2.1.5(3) switches from the Hilbert tensor product
-- to the projective tensor product in the middle of the bottom row. Its right-hand
-- space is printed H^{N,2}. The scalar specialization (9.2.1.6) requires H^{2N,2}.
-- TODO(paper-gap): Corollary 9.2.1.6 also omits the one-sided support condition.

/-- Paper: Corollary 9.2.1.7, p. 409. Each quasi-character of abscissa below b
gives a continuous moment functional after the cutoff.

Deviation: The functional is extended to the full source by precomposing with the support
projection. The integral uses the canonical Haar measure and the intrinsic quasi-character.
In split coordinates this gives (9.2.1.25) with the radial exponent of that quasi-character.
A change of section changes the coordinates of the same quasi-character. -/
theorem modulatedLineSobolev_cutoff_eval (hm : IsModulation m) (_hms : Surjective m)
    (a b : ℝ) (_ha : 1 < a) (N k : ℕ) (_hk : k < N) (z : ℂ) (_hz : z.re < b)
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let E := LineSobolev μ (logModule m) b N
    let U := (logModule m) ⁻¹' Ici (-Real.log a)
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    ∃! Λ : E →L[ℂ] ℂ,
      (∀ f : E, Integrable (fun g ↦ U.indicator (⇑f) g *
          (logModule m g : ℂ) ^ k * c z g) μ ∧
        Λ f = ∫ g, U.indicator (⇑f) g * (logModule m g : ℂ) ^ k * c z g ∂μ) ∧
      ∀ (f : ModulatedExponentialDecay m univ) (u : E),
        tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log a) →
        (u : G → ℂ) =ᵐ[μ] f.val →
        Λ u = iteratedDeriv k (fun w ↦ modulatedFourierMellin m univ hm μ f.val (c w)) z := by
  intro μ E U c
  have hμ : μ.IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  obtain ⟨Λ, hΛ⟩ := modulated_cutoff_moment_functional m hm μ
    (continuous_lineSobolevDensity b N).measurable (exp_le_lineSobolevDensity b N) _ha z _hz
    k χ _hχ
  refine ⟨Λ, ⟨hΛ, fun f u hsupp hu ↦ ?_⟩,
    fun Λ' hΛ' ↦ ContinuousLinearMap.ext fun f ↦ (hΛ'.1 f).2.trans (hΛ f).2.symm⟩
  have hind : (logModule m ⁻¹' Ici (-Real.log a)).indicator (⇑u) =ᵐ[μ] f.val := by
    filter_upwards [hu] with g hg
    by_cases hgU : g ∈ logModule m ⁻¹' Ici (-Real.log a)
    · rw [Set.indicator_of_mem hgU, hg]
    · rw [Set.indicator_of_notMem hgU]
      exact (image_eq_zero_of_notMem_tsupport fun h ↦ hgU (Ioi_subset_Ici_self
        (show logModule m g ∈ Ioi (-Real.log a) from hsupp h))).symm
  have hint : ∀ σ ∈ Ioo (z.re - 1) b, ∀ n : ℕ,
      Integrable (fun g ↦ f.val g * (logModule m g : ℂ) ^ n *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := fun σ hσ n ↦ by
    obtain ⟨_, hΛσ⟩ := modulated_cutoff_moment_functional m hm μ
      (continuous_lineSobolevDensity b N).measurable (exp_le_lineSobolevDensity b N) _ha
      (σ : ℂ) (by rw [Complex.ofReal_re]; exact hσ.2) n χ _hχ
    refine (hΛσ u).1.congr ?_
    filter_upwards [hind] with g hg
    exact congrArg (fun t : ℂ ↦ t * (logModule m g : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) hg
  have hFM : (fun w ↦ modulatedFourierMellin m univ hm μ f.val (c w)) = fun w ↦
      ∫ g, f.val g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ :=
    funext fun w ↦ modulatedFourierMellin_univ m hm μ f.val _
  obtain ⟨_, _, hderiv⟩ := iteratedDeriv_normTwist_moment m μ χ hint k
    (show z.re ∈ Ioo (z.re - 1) b from ⟨by linarith, _hz⟩)
  refine ((hΛ u).2.trans (integral_congr_ae ?_)).trans
    (hderiv.symm.trans (congrArg (fun F : ℂ → ℂ ↦ iteratedDeriv k F z) hFM.symm))
  filter_upwards [hind] with g hg
  exact congrArg (fun t : ℂ ↦ t * (logModule m g : ℂ) ^ k *
    quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) hg
/-- Paper: Corollary 9.2.1.7, p. 409. In each unitary chart the cutoff Mellin
integral of a completed line class is holomorphic and its derivatives are log moments.
Deviation: Apply the source cutoff as in `modulatedLineSobolev_cutoff_eval`. -/
theorem modulatedLineSobolev_cutoff_iteratedDeriv_mellin (hm : IsModulation m) (_hms : Surjective m)
    (a b : ℝ) (_ha : 1 < a) (N k : ℕ) (_hk : k < N) (z : ℂ) (_hz : z.re < b)
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1)
    (f : LineSobolev (canonicalModulatedHaar m hm) (logModule m) b N) :
    let μ := canonicalModulatedHaar m hm
    let u := ((logModule m) ⁻¹' Ici (-Real.log a)).indicator (f : G → ℂ)
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    let M := fun w : ℂ ↦ modulatedFourierMellin m univ hm μ u (c w)
    AnalyticAt ℂ M z ∧ iteratedDeriv k M z =
      ∫ g, u g * (logModule m g : ℂ) ^ k * c z g ∂μ := by
  intro μ u c M
  have hμ : μ.IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have hint : ∀ σ ∈ Ioo (z.re - 1) b, ∀ n : ℕ,
      Integrable (fun g ↦ u g * (logModule m g : ℂ) ^ n *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := fun σ hσ n ↦ by
    obtain ⟨_, hΛ⟩ := modulated_cutoff_moment_functional m hm μ
      (continuous_lineSobolevDensity b N).measurable (exp_le_lineSobolevDensity b N) _ha
      (σ : ℂ) (by rw [Complex.ofReal_re]; exact hσ.2) n χ _hχ
    exact (hΛ f).1
  have hM : M = fun w ↦
      ∫ g, u g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ :=
    funext fun w ↦ modulatedFourierMellin_univ m hm μ u _
  obtain ⟨h1, _, h3⟩ := iteratedDeriv_normTwist_moment m μ χ hint k
    (show z.re ∈ Ioo (z.re - 1) b from ⟨by linarith, _hz⟩)
  rw [hM]
  exact ⟨h1, h3⟩

end ModulatedLine
section Interval

/-- Paper: Proposition 9.2.1.8, p. 410. The density on a compact base interval
uses the larger of the squared endpoint weights and the logarithmic Sobolev factor.
Deviation: The argument is in logarithmic coordinates. -/
def intervalSobolevDensity (a b s x : ℝ) : ℝ :=
  max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) * (1 + x ^ 2) ^ (s / 2)

/-- Paper: Proposition 9.2.1.8, p. 410. At the unit of the positive reals the
density is one for every base interval and degree.
Deviation: Sanity check at logarithmic coordinate zero. -/
theorem intervalSobolevDensity_at_unit (a b s : ℝ) :
    intervalSobolevDensity a b s 0 = 1 := by
  simp [intervalSobolevDensity]

/-- The weighted measure of `CompactIntervalSobolev`: `μ` with the density
`intervalSobolevDensity a b s ∘ logNorm`, or its reciprocal when `dual`. Named so that the
instance arguments of the space mention one constant: written out, the measure and `logNorm`
are copied into each of them, and statements over the space grow to 10¹⁰–10¹¹ nodes as trees. -/
abbrev intervalSobolevMeasure {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (a b s : ℝ) (dual : Bool := false) : Measure A :=
  μ.withDensity fun x ↦ ENNReal.ofReal
    (if dual then (intervalSobolevDensity a b s (logNorm x))⁻¹
     else intervalSobolevDensity a b s (logNorm x))

/-- The logarithm of the idele class norm, the coordinate in which the Sobolev weights of
Chapters 10–12 are taken. Named for the same reason as `intervalSobolevMeasure`. -/
abbrev logIdeleClassNorm (F : Type*) [Field F] [NumberField F] :
    NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F → ℝ :=
  fun g ↦ Real.log ((ideleClassNorm F g).val : ℝ)

/-- The logarithm of the norm on the S-idele quotient. Named for the same reason as
`intervalSobolevMeasure`. -/
abbrev logSIdeleQuotientNorm (F : Type*) [Field F] [NumberField F]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) :
    SIdeleQuotient F S → ℝ :=
  fun g ↦ Real.log ((sIdeleQuotientNorm F S g).val : ℝ)

/-- Paper: Proposition 9.2.1.8, p. 410. The compact-interval space has the positive
endpoint density, and its dual model uses the reciprocal density.
Deviation: Both spaces are realized as weighted L². The measure and logarithmic
coordinate are explicit, and `dual = true` selects the reciprocal density.

Deviation: Propositions 9.2.1.8 and 9.2.2.11 complete all of the second copy of $\mathcal S_J$
in the reciprocal norm, which may be infinite on those tests. The dual branch is the reciprocal
weighted $L^2$ space.
-/
abbrev CompactIntervalSobolev {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (a b s : ℝ) (dual : Bool := false) :=
  Lp ℂ 2 (intervalSobolevMeasure μ logNorm a b s dual)

/-- Paper: Definition 9.2.2.9, p. 416, with §10.2.1, p. 439. For the base interval {0} the
weighted measure is the Sobolev measure of Definition 9.1.2.1, so the space is W^{s,2}(G).
Deviation: Sanity check tying the density to §9.1. -/
theorem intervalSobolev_zero_eq_sobolevMeasure {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (s : ℝ) :
    (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logModule m x))) =
      sobolevMeasure μ (modulatedSobolevWeight m) s := by
  unfold sobolevMeasure
  congr 1
  funext x
  have hw : ((modulatedSobolevWeight m x : ℝ≥0) : ℝ) ^ 2 = Real.log ((m x).val : ℝ) ^ 2 :=
    sq_abs _
  rw [hw]
  simp [intervalSobolevDensity]

/-- Paper: Proposition 9.2.2.11, p. 417, with Corollary 10.2.2.3, p. 447. For the base interval
{0} the reciprocal-density measure is the Sobolev measure of degree −s of Proposition 9.1.2.5.
Deviation: Sanity check tying the dual density to §9.1. -/
theorem intervalSobolev_zero_dual_eq_sobolevMeasure {G : Type*} [CommGroup G]
    [TopologicalSpace G] [MeasurableSpace G] (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (s : ℝ) :
    (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logModule m x))⁻¹) =
      sobolevMeasure μ (modulatedSobolevWeight m) (-s) := by
  unfold sobolevMeasure
  congr 1
  funext x
  have hw : ((modulatedSobolevWeight m x : ℝ≥0) : ℝ) ^ 2 = Real.log ((m x).val : ℝ) ^ 2 :=
    sq_abs _
  have h : (0 : ℝ) ≤ 1 + Real.log ((m x).val : ℝ) ^ 2 := by positivity
  rw [hw, neg_div, Real.rpow_neg h]
  simp [intervalSobolevDensity]

/-- Paper: Definition 9.2.1.1, p. 404. The b-line density and the density of the base
interval {b} in degree 2N bound each other, so the two spaces have the same elements and
topology.
Deviation: Sanity check comparing the two norms the paper uses for W_b^{2N,2}. -/
theorem lineSobolevDensity_le_interval (b : ℝ) (N : ℕ) (x : ℝ) :
    lineSobolevDensity b N x ≤ intervalSobolevDensity b b (2 * (N : ℝ)) x ∧
      intervalSobolevDensity b b (2 * (N : ℝ)) x ≤ 2 ^ N * lineSobolevDensity b N x := by
  have he : 0 ≤ Real.exp (2 * b * x) := (Real.exp_pos _).le
  have hx (k : ℕ) : 0 ≤ x ^ (2 * k) := pow_mul x 2 k ▸ pow_nonneg (sq_nonneg x) k
  have hpow : (1 + x ^ 2) ^ (2 * (N : ℝ) / 2) =
      ∑ k ∈ Finset.range (N + 1), x ^ (2 * k) * (N.choose k : ℝ) := by
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.rpow_natCast, add_comm, add_pow]
    simp [pow_mul]
  rw [lineSobolevDensity, intervalSobolevDensity, max_self, hpow]
  refine ⟨mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk ↦ ?_) he, ?_⟩
  · exact le_mul_of_one_le_right (hx k)
      (by exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
  · rw [mul_left_comm, Finset.mul_sum _ _ ((2 : ℝ) ^ N)]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ ?_) he
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_two_pow N k) (hx k)

-- TODO(paper-gap): The proposed test pairing on all of S_J × S_J can
-- diverge, and S_J need not be contained in the reciprocal-density space.

/-- The compact-interval density is positive. -/
private theorem intervalSobolevDensity_pos (a b s t : ℝ) : 0 < intervalSobolevDensity a b s t :=
  mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

/-- The compact-interval density is continuous. -/
private theorem continuous_intervalSobolevDensity' (a b s : ℝ) :
    Continuous (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
  positivity

/-- The unweighted product pairing identifies the strong dual of a weighted L² space with
the L² space for the reciprocal density. -/
private theorem weightedL2_dual {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {ρ₁ ρ₂ : X → ℝ} (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂)
    (hpos₁ : ∀ x, 0 < ρ₁ x) (hpos₂ : ∀ x, 0 < ρ₂ x) (hrecip : ∀ x, ρ₁ x * ρ₂ x = 1) :
    ∃! T : StrongDual ℂ (Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ₁ x))) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ₂ x)),
      ∀ Λ f, Integrable (fun x ↦ f x * T Λ x) ν ∧ Λ f = ∫ x, f x * T Λ x ∂ν := by
  let E₁ := Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ₁ x))
  let E₂ := Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ₂ x))
  have hdens₁ : Measurable (fun x ↦ ENNReal.ofReal (ρ₁ x)) := hρ₁.ennreal_ofReal
  have hflt₁ : ∀ᵐ x ∂ν, ENNReal.ofReal (ρ₁ x) < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hbase {ρ : X → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x) :
      ν ≪ ν.withDensity fun x ↦ ENNReal.ofReal (ρ x) :=
    withDensity_absolutelyContinuous' hρ.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  have hweighted (ρ : X → ℝ) : (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) ≪ ν :=
    withDensity_absolutelyContinuous _ _
  -- Conjugation times the density maps one weighted space isometrically onto the other.
  have hmap {ρ ρ' : X → ℝ} (hρ : Measurable ρ) (hρ' : Measurable ρ') (hpos : ∀ x, 0 < ρ x)
      (hpos' : ∀ x, 0 < ρ' x) (hr : ∀ x, ρ x * ρ' x = 1)
      (f : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x))) :
      ∃ g : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)),
        (g : X → ℂ) =ᵐ[ν] (fun x ↦ (ρ x : ℂ) * star (f x)) ∧ ‖g‖ = ‖f‖ := by
    let u : X → ℂ := fun x ↦ (ρ x : ℂ) * star (f x)
    have hsq (x : X) : ‖u x‖ ^ 2 * ρ' x = ‖f x‖ ^ 2 * ρ x := by
      calc
        _ = ‖f x‖ ^ 2 * (ρ x * (ρ x * ρ' x)) := by
          dsimp only [u]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos x), norm_star]
          ring
        _ = _ := by rw [hr, mul_one]
    have hmeas : AEStronglyMeasurable u (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)) :=
      (Complex.measurable_ofReal.comp hρ).aestronglyMeasurable.mul
        (((Lp.aestronglyMeasurable f).mono_ac (hbase hρ hpos)).mono_ac (hweighted ρ')).star
    have hmem : MemLp u 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)) := by
      apply (memLp_two_iff_integrable_sq_norm hmeas).2
      apply (integrable_withDensity_iff hρ'.ennreal_ofReal
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
      refine (weightedL2_norm_eq ν hρ hpos f).1.congr (ae_of_all _ fun x ↦ ?_)
      change ‖f x‖ ^ 2 * ρ x = ‖u x‖ ^ 2 * (ENNReal.ofReal (ρ' x)).toReal
      rw [ENNReal.toReal_ofReal (hpos' x).le, hsq]
    have hcoe : (hmem.toLp u : X → ℂ) =ᵐ[ν] u := (hbase hρ' hpos').ae_eq hmem.coeFn_toLp
    refine ⟨hmem.toLp u, hcoe, ?_⟩
    rw [(weightedL2_norm_eq ν hρ' hpos' _).2, (weightedL2_norm_eq ν hρ hpos f).2]
    congr 1
    apply integral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [hx, hsq]
  choose S hS hSnorm using hmap hρ₁ hρ₂ hpos₁ hpos₂ hrecip
  choose S' hS' _ using hmap hρ₂ hρ₁ hpos₂ hpos₁ (fun x ↦ (mul_comm _ _).trans (hrecip x))
  let C : E₁ →ₗᵢ⋆[ℂ] E₂ :=
    { toFun := S
      map_add' := fun f g ↦ Lp.ext <| (hweighted ρ₂).ae_eq <| by
        filter_upwards [hS (f + g), hS f, hS g,
          (hbase hρ₁ hpos₁).ae_eq (Lp.coeFn_add f g),
          (hbase hρ₂ hpos₂).ae_eq (Lp.coeFn_add (S f) (S g))] with x hfg hf hg hx hsum
        rw [hfg, hsum, Pi.add_apply, hf, hg, hx, Pi.add_apply, star_add, mul_add]
      map_smul' := fun c f ↦ Lp.ext <| (hweighted ρ₂).ae_eq <| by
        filter_upwards [hS (c • f), hS f, (hbase hρ₁ hpos₁).ae_eq (Lp.coeFn_smul c f),
          (hbase hρ₂ hpos₂).ae_eq (Lp.coeFn_smul ((starRingEnd ℂ) c) (S f))]
          with x hcf hf hx hsmul
        rw [hcf, hsmul, Pi.smul_apply, hf, hx, Pi.smul_apply]
        simp only [starRingEnd_apply, smul_eq_mul, star_mul', mul_left_comm]
      norm_map' := hSnorm }
  have hSurj : Function.Surjective C := by
    intro g
    refine ⟨S' g, Lp.ext ((hweighted ρ₂).ae_eq ?_)⟩
    change (S (S' g) : X → ℂ) =ᵐ[ν] g
    filter_upwards [hS (S' g), hS' g] with x hSx hS'x
    have hstar : star (ρ₂ x : ℂ) = (ρ₂ x : ℂ) := Complex.conj_ofReal _
    rw [hSx, hS'x, star_mul', hstar, star_star, ← mul_assoc, ← Complex.ofReal_mul, hrecip,
      Complex.ofReal_one, one_mul]
  let R := InnerProductSpace.toDual ℂ E₁
  let T : StrongDual ℂ E₁ ≃ₗᵢ[ℂ] E₂ := R.symm.trans (LinearIsometryEquiv.ofSurjective C hSurj)
  have hPair (Λ : StrongDual ℂ E₁) (f : E₁) :
      Integrable (fun x ↦ f x * T Λ x) ν ∧ Λ f = ∫ x, f x * T Λ x ∂ν := by
    let g := R.symm Λ
    have hprod : (fun x ↦ f x * T Λ x) =ᵐ[ν]
        fun x ↦ (ENNReal.ofReal (ρ₁ x)).toReal • inner ℂ (g x) (f x) := by
      filter_upwards [hS g] with x hx
      change f x * S g x = _
      rw [hx, ENNReal.toReal_ofReal (hpos₁ x).le, RCLike.inner_apply, starRingEnd_apply]
      simp only [Complex.real_smul, mul_left_comm]
    refine ⟨?_, ?_⟩
    · exact ((integrable_withDensity_iff_integrable_smul' hdens₁ hflt₁).1
        (L2.integrable_inner g f)).congr hprod.symm
    · calc
        Λ f = inner ℂ g f := InnerProductSpace.toDual_symm_apply.symm
        _ = ∫ x, inner ℂ (g x) (f x) ∂(ν.withDensity fun x ↦ ENNReal.ofReal (ρ₁ x)) :=
          L2.inner_def g f
        _ = ∫ x, (ENNReal.ofReal (ρ₁ x)).toReal • inner ℂ (g x) (f x) ∂ν :=
          integral_withDensity_eq_integral_toReal_smul hdens₁ hflt₁ _
        _ = ∫ x, f x * T Λ x ∂ν := integral_congr_ae hprod.symm
  refine ⟨T, hPair, fun T' hT' ↦ LinearIsometryEquiv.ext fun Λ ↦ ?_⟩
  apply T.symm.injective
  rw [T.symm_apply_apply]
  apply ContinuousLinearMap.ext
  intro f
  rw [(hPair (T.symm (T' Λ)) f).2, T.apply_symm_apply, (hT' Λ f).2]

/-- Paper: Proposition 9.2.1.8, p. 409. The strong dual of the scalar compact-interval
space is represented isometrically by integration against the reciprocal-density space.
Deviation: The duality is stated on the weighted L² spaces. The pairing on all of
S_J × S_J in (9.2.1.27) can diverge. The paper assumes a < b, but §10.2–10.4 apply the
duality to I = [−α, α] with α ≥ 0, so the one-point base is included. -/
theorem scalarIntervalSobolev_dual (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) :
    ∃! T : StrongDual ℂ (CompactIntervalSobolev volume id a b s) ≃ₗᵢ[ℂ]
        CompactIntervalSobolev volume id a b s true,
      ∀ Λ f, Integrable (fun x ↦ f x * T Λ x) volume ∧
        Λ f = ∫ x, f x * T Λ x :=
  weightedL2_dual volume (continuous_intervalSobolevDensity' a b s).measurable
    (continuous_intervalSobolevDensity' a b s).measurable.inv
    (intervalSobolevDensity_pos a b s) (fun x ↦ inv_pos.mpr (intervalSobolevDensity_pos a b s x))
    (fun x ↦ mul_inv_cancel₀ (intervalSobolevDensity_pos a b s x).ne')

-- TODO(paper-gap): The topology generated by individual interior line norms in
-- (9.2.2.2) is strictly coarser than the uniform Hardy norm in (9.2.2.1).

/-- Paper: Definition 9.2.2.1, p. 412. Take the supremum of the endpoint weighted
L² norms over pairs of abscissas in the base interval.
Deviation: The supremum is extended-valued. It can be infinite on the paper's test
space for unbounded I. For an interval, every pair determines a subinterval. -/
def intervalSobolevENorm {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (I : Set ℝ) (s : ℝ) (f : A → ℂ) : ℝ≥0∞ :=
  ⨆ (a : I) (b : I), eLpNorm f 2
    (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (logNorm x)))

/-- Paper: Lemma 9.2.2.2(1), p. 412. On a compact base interval the exponential-decay
test space and every open-interval test space containing the base have the same completion.
Deviation: This states the compact case by identifying each dense continuous
inclusion into weighted L², with agreement on function representatives. -/
theorem scalarIntervalSobolev_dense (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (J : Set ℝ) (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    ∃ j : PositiveRealExponentialDecay J →L[ℂ] CompactIntervalSobolev volume id a b s,
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : ℝ → ℂ) =ᵐ[volume] f.val := by
  obtain ⟨n, hn⟩ := exists_nat_ge (s / 2)
  apply scalarDecay_dense_of_weight_le J ⟨a, _hsub (left_mem_Icc.mpr _hab)⟩
    ⟨b, _hsub (right_mem_Icc.mpr _hab)⟩ _ (fun x ↦ (1 + x ^ 2) ^ n)
    (continuous_intervalSobolevDensity' a b s) (intervalSobolevDensity_pos a b s) (by fun_prop)
  intro x
  have hp : 1 ≤ 1 + x ^ 2 := by linarith [sq_nonneg x]
  have hw : (1 + x ^ 2) ^ (s / 2) ≤ ((1 + x ^ 2) ^ n) ^ 2 := calc
    _ ≤ (1 + x ^ 2) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hp hn
    _ = (1 + x ^ 2) ^ n := Real.rpow_natCast _ _
    _ ≤ _ := by nlinarith [one_le_pow₀ hp (n := n)]
  have ht (d : ℝ) : Real.exp (2 * d * x) = Real.exp (d * x) ^ 2 := by
    rw [show 2 * d * x = d * x + d * x by ring, Real.exp_add, sq]
  change max _ _ * _ ≤ ((1 + x ^ 2) ^ n * (Real.exp (a * x) + Real.exp (b * x))) ^ 2
  rw [ht, ht, mul_pow, mul_comm]
  apply mul_le_mul hw _ (by positivity) (by positivity)
  apply max_le <;> nlinarith [Real.exp_pos (a * x), Real.exp_pos (b * x),
    mul_pos (Real.exp_pos (a * x)) (Real.exp_pos (b * x)), sq_nonneg (Real.exp (a * x)),
    sq_nonneg (Real.exp (b * x))]

/-- The square of a Schwartz function is integrable against every real power of `1 + x ^ 2`. -/
private theorem integrable_schwartz_sq_mul_rpow (g : SchwartzMap ℝ ℂ) (s : ℝ) :
    Integrable (fun x ↦ ‖g x‖ ^ 2 * (1 + x ^ 2) ^ (s / 2)) volume := by
  obtain ⟨n, hn⟩ := exists_nat_ge (s / 2)
  have h1 : ∀ x : ℝ, (1 + x ^ 2) ^ (s / 2) ≤ (1 + ‖x‖) ^ (2 * n) := fun x ↦ by
    have hx : 1 + x ^ 2 ≤ (1 + ‖x‖) ^ 2 := by
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg x, sq_abs x]
    calc (1 + x ^ 2) ^ (s / 2) ≤ (1 + x ^ 2) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) hn
      _ = (1 + x ^ 2) ^ n := Real.rpow_natCast _ _
      _ ≤ ((1 + ‖x‖) ^ 2) ^ n := pow_le_pow_left₀ (by positivity) hx n
      _ = (1 + ‖x‖) ^ (2 * n) := (pow_mul _ _ _).symm
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x : ℝ, (1 + ‖x‖) ^ (2 * n) * ‖g x‖ ≤ C := by
    refine ⟨2 ^ (2 * n) * (Finset.Iic (2 * n, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) g,
      fun x ↦ ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2 * n, 0))
      le_rfl le_rfl g x
    rw [norm_iteratedFDeriv_zero] at h
    exact h
  have hmeas : AEStronglyMeasurable (fun x ↦ ‖g x‖ ^ 2 * (1 + x ^ 2) ^ (s / 2)) volume :=
    ((g.continuous.norm.pow 2).mul ((continuous_const.add (continuous_pow 2)).rpow_const
      fun x ↦ Or.inl (by positivity : (0 : ℝ) < 1 + x ^ 2).ne')).aestronglyMeasurable
  refine ((g.integrable (μ := volume)).norm.const_mul C).mono' hmeas
    (Eventually.of_forall fun x ↦ ?_)
  have h0 : 0 ≤ ‖g x‖ ^ 2 * (1 + x ^ 2) ^ (s / 2) := by positivity
  rw [Real.norm_of_nonneg h0]
  calc ‖g x‖ ^ 2 * (1 + x ^ 2) ^ (s / 2) ≤ ‖g x‖ ^ 2 * (1 + ‖x‖) ^ (2 * n) :=
        mul_le_mul_of_nonneg_left (h1 x) (by positivity)
    _ = (1 + ‖x‖) ^ (2 * n) * ‖g x‖ * ‖g x‖ := by ring
    _ ≤ C * ‖g x‖ := mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Paper: Lemma 9.2.2.2(2), p. 412. For a compact base interval the supremum
is attained at the two extreme abscissas and yields the stated weighted integral.
Deviation: Use the logarithmic coordinate and record finiteness before taking the real norm. -/
theorem scalarIntervalSobolev_norm (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) :
    Integrable (fun x ↦ ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x) volume ∧
      intervalSobolevENorm volume id (Icc a b) s f.val =
        ENNReal.ofReal (Real.sqrt (∫ x, ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x)) := by
  have hDpos : ∀ x : ℝ, 0 < intervalSobolevDensity a b s x := fun x ↦
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  -- Shrinking the endpoints inside `[a, b]` only lowers the density.
  have hmono : ∀ a' ∈ Icc a b, ∀ b' ∈ Icc a b, ∀ x : ℝ,
      intervalSobolevDensity a' b' s x ≤ intervalSobolevDensity a b s x := by
    intro a' ha' b' hb' x
    have key : ∀ c ∈ Icc a b,
        Real.exp (2 * c * x) ≤ max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) := by
      intro c hc
      rcases le_total 0 x with hx | hx
      · exact le_max_of_le_right (Real.exp_le_exp.2 (by nlinarith [hc.2]))
      · exact le_max_of_le_left (Real.exp_le_exp.2 (by nlinarith [hc.1]))
    exact mul_le_mul_of_nonneg_right (max_le (key a' ha') (key b' hb')) (by positivity)
  have hval : ∀ c x : ℝ, logExponentialDecayTwist univ ⟨c, mem_univ c⟩ f x =
      (Real.exp (c * x) : ℂ) * f.val x := fun c x ↦
    logExponentialDecayTwist_apply univ ⟨c, mem_univ c⟩ f x
  have hcont : Continuous f.val := by
    have h : ⇑(logExponentialDecayTwist univ ⟨0, mem_univ 0⟩ f) = f.val := by
      funext x
      rw [hval, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [← h]
    exact SchwartzMap.continuous _
  -- Each exponential twist of `f` is a Schwartz function.
  have hg : ∀ c : ℝ, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ,
      ‖g x‖ ^ 2 = Real.exp (2 * c * x) * ‖f.val x‖ ^ 2 := fun c ↦
    ⟨logExponentialDecayTwist univ ⟨c, mem_univ c⟩ f, fun x ↦ by
      rw [hval, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring⟩
  obtain ⟨ga, hga⟩ := hg a
  obtain ⟨gb, hgb⟩ := hg b
  have hDmeas : Measurable fun x : ℝ ↦ intervalSobolevDensity a b s x := by
    unfold intervalSobolevDensity
    fun_prop
  have hint : Integrable (fun x ↦ ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x) volume := by
    refine ((integrable_schwartz_sq_mul_rpow ga s).add
      (integrable_schwartz_sq_mul_rpow gb s)).mono'
      ((hcont.measurable.norm.pow_const 2).mul hDmeas).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hDpos x).le), Pi.add_apply, hga, hgb]
    unfold intervalSobolevDensity
    have hw : 0 ≤ (1 + x ^ 2) ^ (s / 2) := by positivity
    have hmax : max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) ≤
        Real.exp (2 * a * x) + Real.exp (2 * b * x) :=
      max_le_add_of_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmax hw)
      (sq_nonneg ‖f.val x‖)]
  have hρ : AEMeasurable (fun x ↦ (intervalSobolevDensity a b s x).toNNReal) volume :=
    hDmeas.real_toNNReal.aemeasurable
  have hsmul : ∀ x, (intervalSobolevDensity a b s x).toNNReal • ‖f.val x‖ ^ 2 =
      ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x := fun x ↦ by
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hDpos _).le, mul_comm]
  have hf2 : Integrable (fun x ↦ ‖f.val x‖ ^ 2)
      (volume.withDensity fun x ↦ ((intervalSobolevDensity a b s x).toNNReal : ℝ≥0∞)) :=
    (integrable_withDensity_iff_integrable_smul₀ hρ).2
      (hint.congr (Eventually.of_forall fun x ↦ (hsmul x).symm))
  have hmem : MemLp f.val 2
      (volume.withDensity fun x ↦ ((intervalSobolevDensity a b s x).toNNReal : ℝ≥0∞)) :=
    (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 hf2
  have hI : ∫ x, ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x = ∫ x, ‖f.val x‖ ^ 2
      ∂volume.withDensity fun x ↦ ((intervalSobolevDensity a b s x).toNNReal : ℝ≥0∞) := by
    rw [integral_withDensity_eq_integral_smul₀ hρ]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ (hsmul x).symm)
  have hE : intervalSobolevENorm volume id (Icc a b) s f.val =
      eLpNorm f.val 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) := by
    unfold intervalSobolevENorm
    refine le_antisymm (iSup₂_le fun a' b' ↦ eLpNorm_mono_measure _ (withDensity_mono
      (Eventually.of_forall fun x ↦ ENNReal.ofReal_le_ofReal (hmono _ a'.2 _ b'.2 _)))) ?_
    exact le_iSup₂_of_le (⟨a, left_mem_Icc.2 _hab⟩ : Icc a b) ⟨b, right_mem_Icc.2 _hab⟩ le_rfl
  refine ⟨hint, ?_⟩
  rw [hE, hI, Real.sqrt_eq_rpow]
  refine (MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hmem).trans ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]

private theorem scalarTraceFamily_interval_bounds (a b : ℝ) (N : ℕ) {J : Set ℝ} (ha : a ∈ J) (hb : b ∈ J)
    (f : PositiveRealExponentialDecay J) (u : CompactIntervalSobolev volume id a b (2 * (N : ℝ)))
    (hu : (u : ℝ → ℂ) =ᵐ[volume] f.val) :
    let σ : Bool → ℝ := fun i ↦ if i then b else a
    let T := scalarTraceFamily σ N J (fun i ↦ by cases i <;> assumption) volume
    ‖u‖ ≤ Real.sqrt (2 ^ N / (2 * Real.pi)) * ‖T f‖ ∧
      ‖T f‖ ≤ Real.sqrt (4 * Real.pi) * ‖u‖ := by
  intro σ T
  let ρ := intervalSobolevDensity a b (2 * (N : ℝ))
  let w (d x : ℝ) := lineSobolevDensity d N x
  let q (d : ℝ) := ∫ x : ℝ, ‖u x‖ ^ 2 * w d x
  have h (x : ℝ) : max (w a x) (w b x) ≤ ρ x ∧ ρ x ≤ 2 ^ N * (w a x + w b x) := by
    have hmax : ρ x = max (intervalSobolevDensity a a (2 * (N : ℝ)) x)
        (intervalSobolevDensity b b (2 * (N : ℝ)) x) := by
      simp only [ρ, intervalSobolevDensity, max_self]
      exact max_mul_of_nonneg _ _ (by positivity)
    rw [hmax]
    obtain ⟨ha₁, ha₂⟩ := lineSobolevDensity_le_interval a N x
    obtain ⟨hb₁, hb₂⟩ := lineSobolevDensity_le_interval b N x
    exact ⟨max_le_max ha₁ hb₁, max_le
      (ha₂.trans <| mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (lineSobolevDensity_pos b N x).le) (by positivity))
      (hb₂.trans <| mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (lineSobolevDensity_pos a N x).le) (by positivity))⟩
  obtain ⟨hi, hn⟩ := weightedL2_norm_eq volume (continuous_intervalSobolevDensity' a b _).measurable
    (intervalSobolevDensity_pos a b _) u
  have hw (d : ℝ) (hd : ∀ x, w d x ≤ ρ x) :
      Integrable (fun x ↦ ‖u x‖ ^ 2 * w d x) volume := by
    apply hi.mono' ((u.1.stronglyMeasurable.aestronglyMeasurable.norm.pow 2).mul
      (continuous_lineSobolevDensity d N).aestronglyMeasurable)
    filter_upwards with x
    change ‖‖u x‖ ^ 2 * lineSobolevDensity d N x‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (lineSobolevDensity_pos d N x).le)]
    exact mul_le_mul_of_nonneg_left (hd x) (sq_nonneg _)
  have A (x : ℝ) : w a x ≤ ρ x := (le_max_left _ _).trans (h x).1
  have B (x : ℝ) : w b x ≤ ρ x := (le_max_right _ _).trans (h x).1
  have I := hw a A
  have K := hw b B
  have norm_sq : ‖u‖ ^ 2 = ∫ x : ℝ, ‖u x‖ ^ 2 * ρ x := by
    rw [hn, Real.sq_sqrt (integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _)
      (intervalSobolevDensity_pos a b _ x).le)]
  have upper : q a + q b ≤ 2 * ‖u‖ ^ 2 := by
    rw [two_mul, norm_sq]
    exact add_le_add (integral_mono I hi fun x ↦ mul_le_mul_of_nonneg_left (A x) (sq_nonneg _))
      (integral_mono K hi fun x ↦ mul_le_mul_of_nonneg_left (B x) (sq_nonneg _))
  have lower : ‖u‖ ^ 2 ≤ 2 ^ N * (q a + q b) := by
    dsimp only [q]
    rw [norm_sq, ← integral_add I K, ← integral_const_mul]
    apply integral_mono hi ((I.add K).const_mul _)
    intro x
    calc _ ≤ ‖u x‖ ^ 2 * (2 ^ N * (w a x + w b x)) :=
          mul_le_mul_of_nonneg_left (h x).2 (sq_nonneg _)
      _ = _ := by simp only [Pi.add_apply]; ring
  have qf (d : ℝ) : (∫ x, ‖f.val x‖ ^ 2 * lineSobolevDensity d N x) = q d :=
    integral_congr_ae (hu.mono fun x hx ↦ by simp [hx, w])
  have energy : ‖T f‖ ^ 2 = 2 * Real.pi * (q a + q b) := by
    have he := scalarTraceFamily_energy σ N (J := J) (fun i ↦ by cases i <;> assumption)
      volume 1 zero_le_one (by simp) f
    simpa only [σ, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, one_mul, qf,
      mul_add, add_comm] using he
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), energy, ← mul_assoc, div_mul_cancel₀ _ (by positivity)]
    exact lower
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), energy]
    nlinarith [mul_le_mul_of_nonneg_left upper (show 0 ≤ 2 * Real.pi by positivity)]

private theorem piLp_norm_le_sum {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    (x : PiLp 2 V) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)

/-- Paper: Lemma 9.2.2.2(2), p. 412. For even order the endpoint derivative
traces and the compact-interval weighted norm induce the same topology on the tests.
Deviation: Express equivalence by two-sided comparison with the sum of the finitely
many norms in (9.2.2.5). -/
theorem scalarIntervalSobolev_mellin_norm_bounds (a b : ℝ) (_hab : a ≤ b) (N : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ f : PositiveRealExponentialDecay univ,
      let F := mellin (fun t ↦ f.val (Real.log t))
      let w := (intervalSobolevENorm volume id (Icc a b) (2 * (N : ℝ)) f.val).toReal
      let q := fun σ : ℝ ↦ ∑ k ∈ Finset.range (N + 1),
        (eLpNorm (fun y : ℝ ↦ iteratedDeriv k F (verticalPoint σ y)) 2 volume).toReal
      (∀ σ ∈ ({a, b} : Set ℝ), ∀ k ≤ N,
        MemLp (fun y : ℝ ↦ iteratedDeriv k F (verticalPoint σ y)) 2 volume) ∧
        w ≤ C * (q a + q b) ∧ q a + q b ≤ D * w := by
  let C := Real.sqrt (2 ^ N / (2 * Real.pi))
  let D := Real.sqrt (4 * Real.pi)
  refine ⟨C, (2 * (N + 1 : ℕ) : ℝ) * D, by dsimp [C]; positivity, by dsimp [D]; positivity, ?_⟩
  intro f F w q
  let σ : Bool → ℝ := fun i ↦ if i then b else a
  let T := scalarTraceFamily σ N univ (fun _ ↦ trivial) volume
  let v := T f
  have hk (d : ℝ) (k : ℕ) : MemLp (fun y : ℝ ↦ iteratedDeriv k F (verticalPoint d y)) 2 volume :=
    ((scalarMomentTrace univ ⟨d, trivial⟩ k f).memLp 2 volume).ae_eq (ae_of_all _ fun y ↦
      scalarMomentTrace_apply isOpen_univ _ _ _ y)
  refine ⟨fun d _ k _ ↦ hk d k, ?_⟩
  obtain ⟨j, _, _, hj⟩ := scalarIntervalSobolev_dense a b (2 * (N : ℝ)) _hab (by positivity)
    univ isOpen_univ ordConnected_univ (subset_univ _)
  obtain ⟨hC, hD⟩ := scalarTraceFamily_interval_bounds a b N (mem_univ _) (mem_univ _) f (j f) (hj f)
  have hw : w = ‖j f‖ := by
    obtain ⟨_, hnorm⟩ := scalarIntervalSobolev_norm a b (2 * (N : ℝ)) _hab (by positivity) f
    dsimp [w]
    rw [hnorm, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      (weightedL2_norm_eq volume (continuous_intervalSobolevDensity' _ _ _).measurable
        (intervalSobolevDensity_pos _ _ _) (j f)).2]
    apply congrArg Real.sqrt
    exact integral_congr_ae ((hj f).mono fun x hx ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2 * _) hx.symm)
  have hq (i : Bool) : q (σ i) = ∑ k : Fin (N + 1), ‖v i k‖ := by
    dsimp only [q]
    rw [ ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    rw [Lp.norm_def, eLpNorm_congr_ae (scalarTraceFamily_rep σ N isOpen_univ (fun _ ↦ trivial) volume f i k)]
  have hsum : q a + q b = ∑ i : Bool, ∑ k : Fin (N + 1), ‖v i k‖ := by
    rw [Fintype.sum_bool, ← hq false, ← hq true]; exact add_comm _ _
  change ‖j f‖ ≤ C * ‖v‖ at hC
  change ‖v‖ ≤ D * ‖j f‖ at hD
  rw [hw, hsum]
  constructor
  · exact hC.trans (mul_le_mul_of_nonneg_left ((piLp_norm_le_sum v).trans (Finset.sum_le_sum fun i _ ↦ piLp_norm_le_sum (v i)))
      (Real.sqrt_nonneg _))
  · calc
      _ ≤ ∑ i : Bool, ∑ _k : Fin (N + 1), ‖v‖ := Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum
          fun k _ ↦ (PiLp.norm_apply_le (v i) k).trans (PiLp.norm_apply_le v i)
      _ = (2 * (N + 1 : ℕ) : ℝ) * ‖v‖ := by simp [two_mul, add_mul]; ring
      _ ≤ (2 * (N + 1 : ℕ) : ℝ) * (D * ‖j f‖) := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = _ := (mul_assoc _ _ _).symm

/-- On a right half-line the supremum over pairs of abscissas equals the supremum over pairs
whose first abscissa is the left endpoint. -/
private theorem intervalSobolevENorm_Ici {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (a s : ℝ) (f : A → ℂ) :
    intervalSobolevENorm μ logNorm (Ici a) s f =
      ⨆ σ : Ici a, eLpNorm f 2 (μ.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a σ s (logNorm x))) := by
  unfold intervalSobolevENorm
  refine le_antisymm (iSup₂_le fun a' b' ↦ ?_)
    (iSup_le fun σ ↦ le_iSup₂_of_le (⟨a, self_mem_Ici⟩ : Ici a) σ le_rfl)
  have hσ : max (a' : ℝ) b' ∈ Ici a := le_max_of_le_left a'.2
  refine le_iSup_of_le (⟨_, hσ⟩ : Ici a) (eLpNorm_mono_measure _ (withDensity_mono
    (Eventually.of_forall fun g ↦ ENNReal.ofReal_le_ofReal ?_)))
  have key : ∀ c : ℝ, a ≤ c → c ≤ max (a' : ℝ) b' → ∀ x : ℝ, Real.exp (2 * c * x) ≤
      max (Real.exp (2 * a * x)) (Real.exp (2 * max (a' : ℝ) b' * x)) := by
    intro c hac hc x
    rcases le_total 0 x with hx | hx
    · exact le_max_of_le_right
        (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hc hx]))
    · exact le_max_of_le_left
        (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonpos_right hac hx]))
  unfold intervalSobolevDensity
  exact mul_le_mul_of_nonneg_right
    (max_le (key _ a'.2 (le_max_left _ _) _) (key _ b'.2 (le_max_right _ _) _)) (by positivity)

/-- On a left half-line the supremum over pairs of abscissas equals the supremum over pairs
whose second abscissa is the right endpoint. -/
private theorem intervalSobolevENorm_Iic {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (b s : ℝ) (f : A → ℂ) :
    intervalSobolevENorm μ logNorm (Iic b) s f =
      ⨆ σ : Iic b, eLpNorm f 2 (μ.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity σ b s (logNorm x))) := by
  unfold intervalSobolevENorm
  refine le_antisymm (iSup₂_le fun a' b' ↦ ?_)
    (iSup_le fun σ ↦ le_iSup₂_of_le σ (⟨b, self_mem_Iic⟩ : Iic b) le_rfl)
  have hσ : min (a' : ℝ) b' ∈ Iic b := min_le_of_left_le a'.2
  refine le_iSup_of_le (⟨_, hσ⟩ : Iic b) (eLpNorm_mono_measure _ (withDensity_mono
    (Eventually.of_forall fun g ↦ ENNReal.ofReal_le_ofReal ?_)))
  have key : ∀ c : ℝ, min (a' : ℝ) b' ≤ c → c ≤ b → ∀ x : ℝ, Real.exp (2 * c * x) ≤
      max (Real.exp (2 * min (a' : ℝ) b' * x)) (Real.exp (2 * b * x)) := by
    intro c hc hcb x
    rcases le_total 0 x with hx | hx
    · exact le_max_of_le_right
        (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hcb hx]))
    · exact le_max_of_le_left
        (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonpos_right hc hx]))
  unfold intervalSobolevDensity
  exact mul_le_mul_of_nonneg_right
    (max_le (key _ (min_le_left _ _) a'.2 _) (key _ (min_le_right _ _) b'.2 _)) (by positivity)

/-- Paper: Lemma 9.2.2.2(3)(a), p. 412. For a right half-line the endpoint
supremum uses the left endpoint and an arbitrary point in the interval.
Deviation: The identity is extended-valued, since the supremum can be infinite. -/
theorem scalarIntervalSobolev_enorm_Ici (a s : ℝ) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) :
    intervalSobolevENorm volume id (Ici a) s f.val =
      ⨆ σ : Ici a, eLpNorm f.val 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a σ s x)) :=
  intervalSobolevENorm_Ici volume id a s f.val

/-- Paper: Lemma 9.2.2.2(3)(b), p. 412. For a left half-line the endpoint
supremum uses an arbitrary point in the interval and the right endpoint.
Deviation: The identity is extended-valued, since the supremum can be infinite. -/
theorem scalarIntervalSobolev_enorm_Iic (b s : ℝ) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) :
    intervalSobolevENorm volume id (Iic b) s f.val =
      ⨆ σ : Iic b, eLpNorm f.val 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity σ b s x)) :=
  intervalSobolevENorm_Iic volume id b s f.val

/-- Paper: Definition 9.2.2.1, p. 412. A nonzero smooth test supported on a
compact subset of the positive logarithmic axis has infinite norm for a right half-line.
Deviation: This is a counterexample to the finiteness of the proposed norm. -/
theorem scalarIntervalSobolev_enorm_Ici_eq_top (a s : ℝ) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) (_hf : f.val ≠ 0)
    (_hcompact : HasCompactSupport f.val) (_hsupport : tsupport f.val ⊆ Ioi 0) :
    intervalSobolevENorm volume id (Ici a) s f.val = ∞ := by
  have hcont : Continuous f.val := by
    have h : ⇑(logExponentialDecayTwist univ ⟨0, mem_univ 0⟩ f) = f.val := by
      funext x
      simpa only [Subtype.coe_mk, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
        logExponentialDecayTwist_apply univ ⟨0, mem_univ (0 : ℝ)⟩ f x
    rw [← h]
    exact SchwartzMap.continuous _
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f.val x₀ ≠ 0 := by
    by_contra h
    exact _hf (funext fun x ↦ not_not.1 fun hx ↦ h ⟨x, hx⟩)
  have hx₀pos : 0 < x₀ := _hsupport (subset_tsupport _ hx₀)
  obtain ⟨c, hc, hcx⟩ : ∃ c : ℝ, 0 < c ∧ c < ‖f.val x₀‖ :=
    ⟨_, half_pos (norm_pos_iff.2 hx₀), half_lt_self (norm_pos_iff.2 hx₀)⟩
  -- An open set of positive measure on which `f` and the coordinate stay away from zero.
  obtain ⟨U, hUo, hx₀U, hUc, hUx⟩ : ∃ U : Set ℝ, IsOpen U ∧ x₀ ∈ U ∧
      (∀ x ∈ U, c < ‖f.val x‖) ∧ ∀ x ∈ U, x₀ / 2 < x :=
    ⟨{x | c < ‖f.val x‖} ∩ Ioi (x₀ / 2), (isOpen_lt continuous_const hcont.norm).inter isOpen_Ioi,
      ⟨hcx, half_lt_self hx₀pos⟩, fun x hx ↦ hx.1, fun x hx ↦ hx.2⟩
  have hUpos : volume U ≠ 0 := (hUo.measure_pos volume ⟨x₀, hx₀U⟩).ne'
  have hε : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  -- Chebyshev's inequality for the pair `(a, σ)` bounds an exponential in `σ` by the supremum.
  have hbound : ∀ σ : ℝ, max a 0 ≤ σ → ENNReal.ofReal (Real.exp (σ * x₀)) * volume U ≤
      (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal *
        intervalSobolevENorm volume id (Ici a) s f.val ^ (2 : ℝ≥0∞).toReal := by
    intro σ hσ
    have hσa : a ≤ σ := (le_max_left _ _).trans hσ
    have hσ0 : 0 ≤ σ := (le_max_right _ _).trans hσ
    have hle : eLpNorm f.val 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a σ s x)) ≤
        intervalSobolevENorm volume id (Ici a) s f.val := by
      unfold intervalSobolevENorm
      exact le_iSup₂_of_le (⟨a, self_mem_Ici⟩ : Ici a) (⟨σ, hσa⟩ : Ici a) le_rfl
    have hdens : ∀ x ∈ U, ENNReal.ofReal (Real.exp (σ * x₀)) ≤
        ENNReal.ofReal (intervalSobolevDensity a σ s x) := by
      intro x hx
      have h1 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (s / 2) :=
        Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by positivity)
      have h2 : Real.exp (σ * x₀) ≤ Real.exp (2 * σ * x) :=
        Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left (hUx x hx).le hσ0])
      refine ENNReal.ofReal_le_ofReal ?_
      unfold intervalSobolevDensity
      exact (h2.trans (le_max_right _ _)).trans
        (le_mul_of_one_le_right (le_max_of_le_right (Real.exp_pos _).le) h1)
    calc ENNReal.ofReal (Real.exp (σ * x₀)) * volume U
        = ∫⁻ _ in U, ENNReal.ofReal (Real.exp (σ * x₀)) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in U, ENNReal.ofReal (intervalSobolevDensity a σ s x) :=
          setLIntegral_mono' hUo.measurableSet hdens
      _ = (volume.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity a σ s x)) U :=
          (withDensity_apply _ hUo.measurableSet).symm
      _ ≤ (volume.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity a σ s x))
            {x | ENNReal.ofReal c ≤ ‖f.val x‖ₑ} := measure_mono fun x hx ↦ by
          rw [mem_ofPred_eq, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hUc x hx).le
      _ ≤ (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal * eLpNorm f.val 2 (volume.withDensity fun x ↦
            ENNReal.ofReal (intervalSobolevDensity a σ s x)) ^ (2 : ℝ≥0∞).toReal :=
          meas_ge_le_mul_pow_eLpNorm_eNorm _ two_ne_zero ENNReal.ofNat_ne_top hε
            fun h ↦ absurd h ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  by_contra htop
  have hBtop : (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal *
      intervalSobolevENorm volume id (Ici a) s f.val ^ (2 : ℝ≥0∞).toReal ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by simp) (ENNReal.inv_ne_top.2 hε))
      (ENNReal.rpow_ne_top_of_nonneg (by simp) htop)
  obtain ⟨K, hK, hKle⟩ : ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ σ : ℝ, max a 0 ≤ σ → ENNReal.ofReal (Real.exp (σ * x₀)) ≤ K :=
    ⟨_, ENNReal.div_ne_top hBtop hUpos, fun σ hσ ↦
      (ENNReal.le_div_iff_mul_le (Or.inl hUpos) (Or.inr hBtop)).2 (hbound σ hσ)⟩
  have hlt : K.toReal < Real.exp (max (max a 0) (K.toReal / x₀) * x₀) := by
    have h := (div_le_iff₀ hx₀pos).1 (le_max_right (max a 0) (K.toReal / x₀))
    linarith [Real.add_one_le_exp (max (max a 0) (K.toReal / x₀) * x₀)]
  exact absurd (hKle _ (le_max_left _ _)) (not_le.2 ((ENNReal.lt_ofReal_iff_toReal_lt hK).2 hlt))

/-- An integrable function on the real line whose Fourier transform vanishes identically is
zero almost everywhere: pair it with the Fourier transforms of Schwartz functions. -/
private theorem ae_eq_zero_of_fourier_eq_zero {h : ℝ → ℂ} (hh : Integrable h)
    (hF : ∀ y : ℝ, FourierTransform.fourier h y = 0) : h =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hh.locallyIntegrable fun g hg hgc ↦ ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  let ψ : SchwartzMap ℝ ℂ := hg₁.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
  let φ : SchwartzMap ℝ ℂ := FourierTransform.fourierInv ψ
  have hφ : FourierTransform.fourier φ = ψ := FourierTransform.fourier_fourierInv_eq ψ
  have key : ∫ ξ, FourierTransform.fourier (φ : ℝ → ℂ) ξ • h ξ =
      ∫ x, φ x • FourierTransform.fourier h x := by
    simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.lsmul ℂ ℂ) (L := innerₗ ℝ) Real.continuous_fourierChar
      continuous_inner φ.integrable hh
  calc ∫ x, g x • h x = ∫ x, ψ x • h x := by
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        exact (Complex.coe_smul (g x) (h x)).symm
    _ = ∫ ξ, FourierTransform.fourier (φ : ℝ → ℂ) ξ • h ξ := by
        rw [← SchwartzMap.fourier_coe, hφ]
    _ = ∫ x, φ x • FourierTransform.fourier h x := key
    _ = 0 := by simp [hF]

/-- On the open strip of a compact base interval, each moment of a weighted L² class against
a real exponential is integrable. -/
private theorem intervalSobolev_integrable_moment (a b s : ℝ) (hs : 0 ≤ s)
    (f : CompactIntervalSobolev volume id a b s) {σ : ℝ} (hσ : σ ∈ Ioo a b) (n : ℕ) :
    Integrable (fun x : ℝ ↦ f x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) volume := by
  obtain ⟨δ, hδ, hδa, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ σ - a ∧ δ ≤ b - σ :=
    ⟨min (σ - a) (b - σ), lt_min (sub_pos.2 hσ.1) (sub_pos.2 hσ.2),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨_, hΛ⟩ := weightedL2_moment_functional (continuous_intervalSobolevDensity' a b s)
    (intervalSobolevDensity_pos a b s) (σ : ℂ) n MeasurableSet.univ (δ := 2 * δ) (K := 1)
    (mul_pos two_pos hδ) zero_le_one fun x _ ↦ by
      have h1 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (s / 2) :=
        Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith)
      rw [one_mul, Complex.ofReal_re]
      unfold intervalSobolevDensity
      refine le_trans ?_ (le_mul_of_one_le_right (le_max_of_le_left (Real.exp_pos _).le) h1)
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_max_of_le_right (Real.exp_le_exp.2
          (by nlinarith [mul_nonneg (sub_nonneg.2 hδb) hx]))
      · rw [abs_of_nonpos hx]
        exact le_max_of_le_left (Real.exp_le_exp.2
          (by nlinarith [mul_nonneg (sub_nonneg.2 hδa) (neg_nonneg.2 hx)]))
  simpa only [Set.indicator_univ, mul_assoc] using (hΛ f).1
-- TODO(paper-gap): Lemma 9.2.2.2(3) treats the infinite supremum as a finite
-- norm and identifies it with the topology of individual line norms.
-- TODO(paper-gap): Definition 9.2.2.3 does not specify how the derivative index k
-- should depend on s or restrict the sampled abscissas to I. The boundary
-- accumulation requirement alone does not determine the topology in 9.2.2.4(1).
-- TODO(paper-gap): The derivative range on p. 417 only samples integer orders.
-- For 1 < s < 2 it sees just the zeroth trace. On I = [−1,0] the Mellin
-- transforms of R⁻¹ φ(x/R), with φ smooth of integral one supported in (1,2),
-- tend to zero in every such line norm, including both endpoints, but equal
-- one at z = 0. The fractional-degree endpoint evaluations below concern
-- the weighted source. An analytic counterpart needs fractional trace control.
-- TODO(paper-gap): Proposition 9.2.2.4(2) does not supply an interior from which
-- to take boundary values for a singleton interval.

/-- Paper: Proposition 9.2.2.4(2), p. 414. A weighted L² class on a nondegenerate
compact base interval gives a holomorphic Mellin transform on its open strip.
Deviation: State the compact-base assertion in the weighted source model.

Deviation: Proposition 9.2.2.4 uses the analytic completion sampled along vertical lines. We
construct the holomorphic function from the physical weighted $L^2$ space controlling both
endpoints.
-/
theorem scalarIntervalSobolev_mellin_holomorphic (a b s : ℝ) (_hab : a < b) (_hs : 0 ≤ s) :
    let E := CompactIntervalSobolev volume id a b s
    let strip := Complex.re ⁻¹' Ioo a b
    let M := fun (f : E) z ↦ ∫ x : ℝ, f x * Complex.exp (z * (x : ℂ))
    (∀ f : E, (∀ z ∈ strip, Integrable (fun x : ℝ ↦ f x * Complex.exp (z * (x : ℂ)))) ∧
      DifferentiableOn ℂ (M f) strip) ∧ Injective (fun f ↦ fun z : strip ↦ M f z.val) := by
  intro E strip M
  have hmom (f : E) (z : ℂ) (hz : z ∈ strip) :=
    iteratedDeriv_exp_moment (h := (f : ℝ → ℂ))
      (fun σ hσ n ↦ intervalSobolev_integrable_moment a b s _hs f hσ n) 0 (z := z) hz
  have hint (f : E) (z : ℂ) (hz : z ∈ strip) :
      Integrable (fun x : ℝ ↦ f x * Complex.exp (z * (x : ℂ))) := by
    simpa only [pow_zero, mul_one] using (hmom f z hz).2.1
  refine ⟨fun f ↦ ⟨hint f, fun z hz ↦ ?_⟩, fun f₁ f₂ heq ↦ ?_⟩
  · exact (hmom f z hz).1.differentiableAt.differentiableWithinAt
  · have hσ : ((a + b) / 2 : ℝ) ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have hzmem (y : ℝ) : (((a + b) / 2 : ℝ) : ℂ) + ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.I ∈
        strip := by
      change (_ : ℂ).re ∈ Ioo a b
      simpa using hσ
    have hσmem : (((a + b) / 2 : ℝ) : ℂ) ∈ strip := by
      change (_ : ℂ).re ∈ Ioo a b
      simpa using hσ
    have hh : Integrable (fun x : ℝ ↦ (f₁ x - f₂ x) *
        Complex.exp ((((a + b) / 2 : ℝ) : ℂ) * (x : ℂ))) :=
      ((hint f₁ _ hσmem).sub (hint f₂ _ hσmem)).congr
        (ae_of_all _ fun x ↦ (sub_mul _ _ _).symm)
    have hzero := ae_eq_zero_of_fourier_eq_zero hh fun y ↦ by
      rw [Real.fourier_real_eq_integral_exp_smul]
      have hfun : (fun v : ℝ ↦ Complex.exp (((-2 * Real.pi * v * y : ℝ) : ℂ) * Complex.I) •
          ((f₁ v - f₂ v) * Complex.exp ((((a + b) / 2 : ℝ) : ℂ) * (v : ℂ)))) = fun v : ℝ ↦
          f₁ v * Complex.exp (((((a + b) / 2 : ℝ) : ℂ) +
            ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.I) * (v : ℂ)) -
          f₂ v * Complex.exp (((((a + b) / 2 : ℝ) : ℂ) +
            ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.I) * (v : ℂ)) := by
        funext v
        have hz : ((((a + b) / 2 : ℝ) : ℂ) + ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.I) * (v : ℂ) =
            ((-2 * Real.pi * v * y : ℝ) : ℂ) * Complex.I + (((a + b) / 2 : ℝ) : ℂ) * (v : ℂ) := by
          push_cast
          ring
        rw [smul_eq_mul, hz, Complex.exp_add]
        ring
      rw [hfun, integral_sub (hint f₁ _ (hzmem y)) (hint f₂ _ (hzmem y))]
      exact sub_eq_zero.2 (congrFun heq ⟨_, hzmem y⟩)
    have hvol : (f₁ : ℝ → ℂ) =ᵐ[volume] f₂ := by
      filter_upwards [hzero] with x hx
      have hx' : (f₁ x - f₂ x) * Complex.exp ((((a + b) / 2 : ℝ) : ℂ) * (x : ℂ)) = 0 := hx
      exact sub_eq_zero.1 ((mul_eq_zero.1 hx').resolve_right (Complex.exp_ne_zero _))
    exact Lp.ext ((withDensity_absolutelyContinuous _ _).ae_le hvol)

/-- Paper: Proposition 9.2.2.4(3), p. 414. For even degree and compact base,
Mellin gives a topological linear equivalence with the closure of the two endpoint traces.
Deviation: Use the endpoint topology of Lemma 9.2.2.2(2). The sampling rule of
Definition 9.2.2.3 does not define a sequence-independent topology as stated. -/
theorem scalarIntervalSobolev_mellin_endpoints (a b : ℝ) (_hab : a ≤ b) (N : ℕ)
    (J : Set ℝ) (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    let E := CompactIntervalSobolev volume id a b (2 * (N : ℝ))
    let σ : Bool → ℝ := fun i ↦ if i then b else a
    ∃ M : E ≃L[ℂ] hardySobolevTraceClosure σ N volume,
      ∀ (f : PositiveRealExponentialDecay J) (u : E),
        (u : ℝ → ℂ) =ᵐ[volume] f.val →
        ∀ i (k : Fin (N + 1)), ((M u).val i k : ℝ → ℂ) =ᵐ[volume]
          fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
            (verticalPoint (σ i) y) := by
  intro E σ
  have ha := _hsub (left_mem_Icc.mpr _hab)
  have hb := _hsub (right_mem_Icc.mpr _hab)
  have hσ (i) : σ i ∈ J := by cases i <;> assumption
  let T := scalarTraceFamily σ N J hσ volume
  let T₀ := scalarTraceFamily σ N univ (fun _ ↦ trivial) volume
  let H := hardySobolevTraceClosure σ N volume
  have he : T₀.range.topologicalClosure = H := scalarTraceFamily_closure σ N volume
  obtain ⟨j, _, hd, hj⟩ := scalarIntervalSobolev_dense a b (2 * (N : ℝ)) _hab (by positivity) J _hJ _hInt _hsub
  have bounds (f : PositiveRealExponentialDecay J) := scalarTraceFamily_interval_bounds a b N ha hb f (j f) (hj f)
  let B := PiLp 2 (fun _ : Bool ↦ PiLp 2 (fun _ : Fin (N + 1) ↦ Lp ℂ 2 (volume : Measure ℝ)))
  let V : E →L[ℂ] B := T.extendOfNorm j.toLinearMap
  have hV (f : PositiveRealExponentialDecay J) : V (j f) = T f :=
    LinearMap.extendOfNorm_eq hd ⟨_, fun f ↦ (bounds f).2⟩ f
  let C : ℝ≥0 := ⟨Real.sqrt (2 ^ N / (2 * Real.pi)), Real.sqrt_nonneg _⟩
  have hlow : ∀ x : E, ‖x‖ ≤ (C : ℝ) * ‖V x‖ := by
    refine hd.induction ?_ ?_
    · rintro _ ⟨f, rfl⟩; rw [hV]; exact (bounds f).1
    · exact isClosed_le continuous_norm (continuous_const.mul V.continuous.norm)
  have hanti := V.antilipschitz_of_bound hlow
  have hclosed : IsClosed (V.toLinearMap.range : Set B) := hanti.isClosed_range V.uniformContinuous
  obtain ⟨j₀, _, hd₀, hj₀⟩ := scalarIntervalSobolev_dense a b (2 * (N : ℝ)) _hab (by positivity)
    univ isOpen_univ ordConnected_univ (subset_univ _)
  have hμ : (volume.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b (2 * (N : ℝ)) x)) ≪ volume :=
    withDensity_absolutelyContinuous _ _
  have hV₀ (f : PositiveRealExponentialDecay univ) : V (j₀ f) = T₀ f := by
    let g : PositiveRealExponentialDecay J := ⟨f.val, (Submodule.mem_iInf _).2 fun c ↦
      (Submodule.mem_iInf _).1 f.property ⟨c, trivial⟩⟩
    have heq : j₀ f = j g := Lp.ext (hμ.ae_eq ((hj₀ f).trans (hj g).symm))
    rw [heq, hV]
    ext i k : 2
    exact Lp.ext ((scalarTraceFamily_rep σ N _hJ hσ volume g i k).trans
      (scalarTraceFamily_rep σ N isOpen_univ (fun _ ↦ trivial) volume f i k).symm)
  have hin : ∀ x : E, V x ∈ H := by
    refine hd₀.induction ?_ ?_
    · rintro _ ⟨f, rfl⟩; rw [hV₀, ← he]
      exact T₀.range.le_topologicalClosure (LinearMap.mem_range_self T₀ f)
    · exact (he ▸ T₀.range.isClosed_topologicalClosure).preimage V.continuous
  have hout : H ≤ V.toLinearMap.range := by
    rw [← he]
    refine T₀.range.topologicalClosure_minimal ?_ hclosed
    rintro _ ⟨f, rfl⟩
    exact ⟨_, hV₀ f⟩
  let : CompleteSpace H := (he ▸ T₀.range.isClosed_topologicalClosure).completeSpace_coe
  let L := V.codRestrict H hin
  let M := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr (fun x y h ↦ hanti.injective (congrArg Subtype.val h)))
    (LinearMap.range_eq_top.mpr (fun y ↦ by
      obtain ⟨x, hx⟩ := hout y.property
      exact ⟨x, Subtype.ext hx⟩))
  refine ⟨M, fun f u hu i k ↦ ?_⟩
  have huf : u = j f := Lp.ext (hμ.ae_eq (hu.trans (hj f).symm))
  change (V u i k : ℝ → ℂ) =ᵐ[volume] _
  rw [huf, hV]
  exact scalarTraceFamily_rep σ N _hJ hσ volume f i k

/-- The moment kernel, cut off to a measurable set on which the endpoint exponentials
dominate it exponentially, gives a continuous functional on the compact-interval space. -/
private theorem intervalSobolev_moment_functional (a b s : ℝ) (hs : 0 ≤ s) (z : ℂ) (k : ℕ)
    {U : Set ℝ} (hU : MeasurableSet U) {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hlow : ∀ x ∈ U, Real.exp (2 * z.re * x + δ * |x|) ≤
      K * max (Real.exp (2 * a * x)) (Real.exp (2 * b * x))) :
    ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) →L[ℂ] ℂ,
      ∀ f, Integrable (fun x : ℝ ↦ f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x) volume ∧
        Λ f = ∫ x : ℝ, f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
  refine weightedL2_moment_functional (continuous_intervalSobolevDensity' a b s)
    (intervalSobolevDensity_pos a b s) z k hU hδ hK fun x hx ↦ (hlow x hx).trans
      (mul_le_mul_of_nonneg_left ?_ hK)
  have h1 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (s / 2) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith)
  unfold intervalSobolevDensity
  exact le_mul_of_one_le_right (le_max_of_le_left (Real.exp_pos _).le) h1

/-- Paper: Corollary 9.2.2.5(1), p. 414. On a compact base interval, every
interior derivative evaluation has a continuous extension given by the Mellin moment.
Deviation: State it in the weighted source model, which also allows nonintegral degree. -/
theorem scalarIntervalSobolev_eval_interior (a b s : ℝ) (_hs : 0 ≤ s)
    (z : ℂ) (_hz : z.re ∈ Ioo a b) (k : ℕ) :
    ∃ Λ : CompactIntervalSobolev volume id a b s →L[ℂ] ℂ,
      ∀ f, Integrable (fun x : ℝ ↦ f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
        Λ f = ∫ x : ℝ, f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  obtain ⟨δ, hδ, hδa, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ z.re - a ∧ δ ≤ b - z.re :=
    ⟨min (z.re - a) (b - z.re), lt_min (sub_pos.2 _hz.1) (sub_pos.2 _hz.2),
      min_le_left _ _, min_le_right _ _⟩
  change ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
      ENNReal.ofReal (intervalSobolevDensity a b s x)) →L[ℂ] ℂ,
    ∀ f, Integrable (fun x : ℝ ↦ f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
      Λ f = ∫ x : ℝ, f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))
  obtain ⟨Λ, hΛ⟩ := intervalSobolev_moment_functional a b s _hs z k MeasurableSet.univ
    (δ := 2 * δ) (K := 1) (mul_pos two_pos hδ) zero_le_one fun x _ ↦ by
      rw [one_mul]
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_max_of_le_right (Real.exp_le_exp.2
          (by nlinarith [mul_nonneg (sub_nonneg.2 hδb) hx]))
      · rw [abs_of_nonpos hx]
        exact le_max_of_le_left (Real.exp_le_exp.2
          (by nlinarith [mul_nonneg (sub_nonneg.2 hδa) (neg_nonneg.2 hx)]))
  refine ⟨Λ, fun f ↦ ?_⟩
  simpa only [Set.indicator_univ, mul_assoc] using hΛ f

private def endpointFourierInput (c : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (2*Real.pi : ℝ) * f (-(2*Real.pi)*x) * (Real.exp (c * (-(2*Real.pi)*x)) : ℂ)

private theorem endpointFourierInput_mem (a b s : ℝ) (hs : 0 ≤ s) (c : ℝ) (hc : c ∈ ({a,b} : Set ℝ))
    (f : CompactIntervalSobolev volume id a b s) :
    let g := endpointFourierInput c f
    MemLp g 2 volume ∧ MemLp g 2 (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal ((1 + x^2) ^ (s/2))) := by
  intro g
  let θ (x : ℝ) := (1+x^2)^(s/2)
  let t := -(2*Real.pi)
  have ht : t ≠ 0 := by dsimp [t]; exact neg_ne_zero.mpr (mul_pos two_pos Real.pi_pos).ne'
  have hpi : 0 < 2*Real.pi := by positivity
  have hθ₁ (x : ℝ) : 1 ≤ θ x := Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith)
  have hθ (x : ℝ) : θ x ≤ θ (t*x) := by
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    have h : 1 ≤ t^2 := by dsimp [t]; nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi-3)]
    rw [mul_pow]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg x)]
  have hm : Measurable (f : ℝ → ℂ) := (Lp.stronglyMeasurable f).measurable
  have hg : Measurable g := by
    change Measurable (fun x : ℝ ↦ ((2*Real.pi : ℝ) : ℂ) * f (t*x) * (Real.exp (c*(t*x)) : ℂ))
    fun_prop
  have hmθ : Measurable θ := by dsimp [θ]; fun_prop
  have he (z : ℝ) : Real.exp (2*c*z) ≤ max (Real.exp (2*a*z)) (Real.exp (2*b*z)) := by
    rcases hc with (rfl | hc)
    · exact le_max_left _ _
    · rw [Set.mem_singleton_iff.mp hc]
      exact le_max_right _ _
  have hf := (weightedL2_norm_eq volume (continuous_intervalSobolevDensity' a b s).measurable
    (intervalSobolevDensity_pos a b s) f).1
  have H : Integrable (fun x ↦ ‖g x‖^2 * θ x) := by
    apply ((hf.comp_mul_left' ht).const_mul ((2*Real.pi)^2)).mono'
      ((hg.norm.pow_const 2).mul hmθ).aestronglyMeasurable
    filter_upwards with x
    simp only [Pi.mul_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (zero_le_one.trans (hθ₁ x)))]
    change ‖((2*Real.pi : ℝ) : ℂ) * f (t*x) * (Real.exp (c*(t*x)) : ℂ)‖^2 * θ x ≤
      (2*Real.pi)^2 * (‖f (t*x)‖^2 * intervalSobolevDensity a b s (t*x))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hpi.le,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, mul_pow, ← Real.exp_nat_mul]
    change ((2*Real.pi)^2 * ‖f (t*x)‖^2) * Real.exp ((2 : ℝ)*(c*(t*x))) * θ x ≤ _
    rw [← mul_assoc (2 : ℝ) c, mul_assoc _ (Real.exp _) (θ x), intervalSobolevDensity, ← mul_assoc ((2*Real.pi)^2)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (he _) (hθ x) (zero_le_one.trans (hθ₁ x)) (le_max_of_le_left (Real.exp_pos _).le)) (by positivity)
  refine ⟨(memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 (H.mono' (hg.norm.pow_const 2).aestronglyMeasurable ?_),
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 ?_⟩
  · filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (hθ₁ x)
  · apply (integrable_withDensity_iff hmθ.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
    simpa only [Pi.mul_apply, ENNReal.toReal_ofReal (zero_le_one.trans (hθ₁ _))] using H

private theorem endpointFourierInput_abel (c : ℝ) (f : ℝ → ℂ)
    (v : Lp ℂ 2 (volume : Measure ℝ)) (hv : (v : ℝ → ℂ) =ᵐ[volume] endpointFourierInput c f)
    (δ y : ℝ) :
    (∫ x : ℝ, v x * Complex.exp (↑(-(2*Real.pi*δ*|x|) : ℝ) - ↑(2*Real.pi*y*x : ℝ)*Complex.I)) =
      ∫ t : ℝ, f t * Complex.exp (↑(c*t-δ*|t| : ℝ) + ↑(y*t : ℝ)*Complex.I) := by
  let C := 2*Real.pi
  have hC : 0 < C := by dsimp [C]; positivity
  let F (t : ℝ) := f t * Complex.exp (↑(c*t-δ*|t| : ℝ) + ↑(y*t : ℝ)*Complex.I)
  calc
    _ = ∫ x : ℝ, C • F (-C*x) := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx, endpointFourierInput, Complex.real_smul, Complex.ofReal_exp]
      change ((C : ℂ)*f (-C*x)*Complex.exp (↑(c*(-C*x) : ℝ))) *
        Complex.exp (↑(-(C*δ*|x|) : ℝ) - ↑(C*y*x : ℝ)*Complex.I) =
          (C : ℂ)*(f (-C*x)*Complex.exp (↑(c*(-C*x)-δ*|-C*x| : ℝ) + ↑(y*(-C*x) : ℝ)*Complex.I))
      rw [mul_assoc _ (Complex.exp _) _, ← Complex.exp_add, abs_mul, abs_neg, abs_of_pos hC, ← mul_assoc (C : ℂ) (f (-C*x))]
      congr 2
      push_cast
      ring
    _ = _ := by
      rw [integral_smul, Measure.integral_comp_mul_left F, smul_smul, inv_neg, abs_neg,
        abs_of_pos (inv_pos.mpr hC), mul_inv_cancel₀ hC.ne', one_smul]

private theorem strip_abel_comparison {a b c σ : ℝ} (hab : a < b) (hc : c ∈ ({a,b} : Set ℝ))
    (hσ : σ ∈ Ioo a b) (hnear : |σ-c| < (b-a)/2) (x : ℝ) :
    σ*x = c*x - |σ-c| * |x| ∨
      (σ*x ≤ ((a+b)/2)*x ∧ c*x - |σ-c| * |x| ≤ ((a+b)/2)*x) := by
  rcases hc with (rfl | hc)
  · rw [abs_of_nonneg (sub_nonneg.mpr hσ.1.le)] at *
    rcases le_total 0 x with hx | hx
    · right
      constructor
      · exact mul_le_mul_of_nonneg_right (by linarith) hx
      · exact (sub_le_self _ (mul_nonneg (sub_nonneg.mpr hσ.1.le) (abs_nonneg _))).trans
          (mul_le_mul_of_nonneg_right (by linarith) hx)
    · left
      rw [abs_of_nonpos hx]
      ring
  · obtain rfl := Set.mem_singleton_iff.mp hc
    rw [abs_of_nonpos (sub_nonpos.mpr hσ.2.le)] at *
    rcases le_total 0 x with hx | hx
    · left
      rw [abs_of_nonneg hx]
      ring
    · right
      constructor
      · exact mul_le_mul_of_nonpos_right (by linarith) hx
      · exact (sub_le_self _ (mul_nonneg (neg_nonneg.mpr (sub_nonpos.mpr hσ.2.le)) (abs_nonneg _))).trans
          (mul_le_mul_of_nonpos_right (by linarith) hx)

private theorem strip_abel_boundary {a b c : ℝ} (hab : a < b) (hc : c ∈ ({a,b} : Set ℝ))
    (f : ℝ → ℂ) (hm : Measurable f) (y : ℝ)
    (hin : ∀ d ∈ Ioo a b, Integrable (fun x : ℝ ↦ f x * Complex.exp (verticalPoint d y * (x : ℂ))))
    (w : ℂ) (hw : Tendsto (fun δ : ℝ ↦ ∫ x : ℝ, f x *
      Complex.exp (↑(c*x-δ*|x| : ℝ) + ↑(y*x : ℝ)*Complex.I)) (𝓝[>] 0) (𝓝 w)) :
    Tendsto (fun d : ℝ ↦ ∫ x : ℝ, f x * Complex.exp (verticalPoint d y * (x : ℂ))) (𝓝[Ioo a b] c) (𝓝 w) := by
  let l := 𝓝[Ioo a b] c
  let m := (a+b)/2
  let K (r x : ℝ) := Complex.exp ((r : ℂ) + ↑(y*x : ℝ)*Complex.I)
  have hK (r x : ℝ) : ‖K r x‖ = Real.exp r := by simp [K, Complex.norm_exp]
  have hM (d x : ℝ) : Complex.exp (verticalPoint d y * (x : ℂ)) = K (d*x) x := by
    unfold K
    congr 1
    push_cast
    ring
  let F (d x : ℝ) := f x * K (d*x) x - f x * K (c*x-|d-c| * |x|) x
  have hδ : Tendsto (fun d : ℝ ↦ |d-c|) l (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun d : ℝ ↦ |d-c|) := by fun_prop
      simpa only [sub_self, abs_zero] using (hcont.tendsto c).mono_left nhdsWithin_le_nhds
    · filter_upwards [show ∀ᶠ d in l, d ∈ Ioo a b from self_mem_nhdsWithin] with d hd
      apply abs_pos.mpr
      apply sub_ne_zero.mpr
      rcases hc with (rfl | hc)
      · exact hd.1.ne'
      · exact (Set.mem_singleton_iff.mp hc).symm ▸ hd.2.ne
  have near : ∀ᶠ d in l, d ∈ Ioo a b ∧ |d-c| < (b-a)/2 :=
    (show ∀ᶠ d in l, d ∈ Ioo a b from self_mem_nhdsWithin).and
      ((tendsto_nhdsWithin_iff.mp hδ).1.eventually (gt_mem_nhds (by linarith)))
  let H (x : ℝ) := 2*(‖f x‖*Real.exp (m*x))
  have hH : Integrable H := by
    have hi := (hin m ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩).norm.const_mul 2
    simpa only [H, norm_mul, hM, hK] using hi
  have hFm (d : ℝ) : Measurable (F d) := by dsimp [F,K]; fun_prop
  have hBd {d : ℝ} (hd : d ∈ Ioo a b ∧ |d-c| < (b-a)/2) (x : ℝ) : ‖F d x‖ ≤ H x := by
    rcases strip_abel_comparison hab hc hd.1 hd.2 x with heq | ⟨h₁,h₂⟩
    · simp only [F, heq, sub_self, norm_zero, H]
      positivity
    · refine (norm_sub_le _ _).trans ?_
      simp only [norm_mul, hK, H, two_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h₁) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h₂) (norm_nonneg _))
  have hlim := tendsto_integral_filter_of_dominated_convergence (l := l) (F := F) (f := fun _ ↦ (0 : ℂ)) H
    (Eventually.of_forall fun d ↦ (hFm d).aestronglyMeasurable) (near.mono fun _ hd ↦ ae_of_all _ (hBd hd))
    hH (ae_of_all _ fun x ↦ ?_)
  · have hsum := (hlim.add (hw.comp hδ))
    simp only [integral_zero, zero_add] at hsum
    apply hsum.congr' (near.mono fun d hd ↦ ?_)
    let M (x : ℝ) := f x * K (d*x) x
    let D (x : ℝ) := f x * K (c*x-|d-c| * |x|) x
    have hiM : Integrable M := (hin d hd.1).congr (ae_of_all _ fun x ↦ by simp only [M,hM])
    have hiF := hH.mono' (hFm d).aestronglyMeasurable (ae_of_all _ (hBd hd))
    have hiD : Integrable D := (hiM.sub hiF).congr (ae_of_all _ fun x ↦ by dsimp [M,F,D]; abel)
    change (∫ x, M x-D x) + (∫ x, D x) = _
    rw [integral_sub hiM hiD, sub_add_cancel]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by simp only [M,hM])
  · have hcont : Continuous (fun d : ℝ ↦ F d x) := by dsimp [F,K]; fun_prop
    simpa only [F, sub_self, abs_zero, zero_mul, sub_zero] using (hcont.tendsto c).mono_left nhdsWithin_le_nhds

/-- Paper: Proposition 9.2.2.4(2), p. 414. On either endpoint line of a
nondegenerate compact base interval, the interior Mellin integral has an almost-everywhere
limit, whose inverse Fourier transform has the required Sobolev weight.
Deviation: State the compact-base assertion using the weighted source model.

Deviation: Proposition 9.2.2.4(2) asserts boundary values for every element of the sampled
completion. We use endpoint-weighted physical data and identify the almost-everywhere limits by
the corresponding weighted inverse Fourier transforms.
-/
theorem scalarIntervalSobolev_boundary_values (a b s : ℝ) (_hab : a < b) (_hs : 0 ≤ s)
    (c : ℝ) (_hc : c ∈ ({a, b} : Set ℝ)) (f : CompactIntervalSobolev volume id a b s) :
    ∃ u : Lp ℂ 2 (volume : Measure ℝ),
      (∀ᵐ y : ℝ ∂volume, Tendsto
        (fun σ : ℝ ↦ ∫ x : ℝ, f x * Complex.exp (verticalPoint σ y * (x : ℂ)))
        (𝓝[Ioo a b] c) (𝓝 (u y))) ∧
      MemLp ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u : ℝ → ℂ) 2
        (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal ((1 + x ^ 2) ^ (s / 2))) := by
  obtain ⟨hg, hg'⟩ := endpointFourierInput_mem a b s _hs c _hc f
  let v := hg.toLp (endpointFourierInput c f)
  let u := (Lp.fourierTransformₗᵢ ℝ ℂ) v
  refine ⟨u, ?_, ?_⟩
  · filter_upwards [fourier_L2_abel_limit v] with y hy
    apply strip_abel_boundary _hab _hc _ (Lp.stronglyMeasurable f).measurable y _ (u y)
    · exact hy.congr (fun δ ↦ endpointFourierInput_abel c f v hg.coeFn_toLp δ y)
    · intro d hd
      obtain ⟨_, hΛ⟩ := scalarIntervalSobolev_eval_interior a b s _hs (verticalPoint d y) (by simpa using hd) 0
      simpa only [pow_zero, mul_one] using (hΛ f).1
  · rw [show (Lp.fourierTransformₗᵢ ℝ ℂ).symm u = v from (Lp.fourierTransformₗᵢ ℝ ℂ).symm_apply_apply _]
    exact hg'.ae_eq ((withDensity_absolutelyContinuous volume _).ae_eq hg.coeFn_toLp.symm)

/-- A pointwise comparison of squared multipliers gives a contraction between weighted
L² spaces, with the stated representatives in the original measure. -/
private theorem weightedL2_multiply {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {ρ θ : X → ℝ} (hρ : Measurable ρ) (hθ : Measurable θ)
    (hρpos : ∀ x, 0 < ρ x) (hθpos : ∀ x, 0 < θ x) (w : X → ℂ) (hw : Measurable w)
    (hle : ∀ x, ‖w x‖ ^ 2 * θ x ≤ ρ x) :
    let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (ρ x))
    let η := μ.withDensity (fun x ↦ ENNReal.ofReal (θ x))
    ∃ L : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 η, ∀ f, ‖L f‖ ≤ ‖f‖ ∧ (L f : X → ℂ) =ᵐ[μ] (fun x ↦ f x * w x) := by
  intro ν η
  have hμν : μ ≪ ν := withDensity_absolutelyContinuous' hρ.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hρpos x)).ne')
  have hμη : μ ≪ η := withDensity_absolutelyContinuous' hθ.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hθpos x)).ne')
  have hην : η ≪ ν := (withDensity_absolutelyContinuous _ _).trans hμν
  have hpt (f : Lp ℂ 2 ν) (x : X) : ‖f x * w x‖ ^ 2 * θ x ≤ ‖f x‖ ^ 2 * ρ x := by
    rw [norm_mul, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hle x) (sq_nonneg _)
  have hint (f : Lp ℂ 2 ν) : Integrable (fun x ↦ ‖f x * w x‖ ^ 2 * θ x) μ :=
    (weightedL2_norm_eq μ hρ hρpos f).1.mono'
      ((((Lp.aestronglyMeasurable f).mono_ac hμν).mul hw.aestronglyMeasurable).norm.pow 2 |>.mul hθ.aestronglyMeasurable)
      (ae_of_all _ fun x ↦ (Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hθpos x).le)).le.trans (hpt f x))
  have mem (f : Lp ℂ 2 ν) : MemLp (fun x ↦ f x * w x) 2 η := by
    apply (memLp_two_iff_integrable_sq_norm (((Lp.aestronglyMeasurable f).mono_ac hην).mul hw.aestronglyMeasurable)).2
    apply (integrable_withDensity_iff hθ.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
    simpa only [Pi.mul_apply, ENNReal.toReal_ofReal (hθpos _).le] using hint f
  let L : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 η :=
    { toFun f := (mem f).toLp _
      map_add' f g := by
        apply Lp.ext
        filter_upwards [(mem (f + g)).coeFn_toLp, hην.ae_eq (Lp.coeFn_add f g),
          Lp.coeFn_add ((mem f).toLp _) ((mem g).toLp _), (mem f).coeFn_toLp, (mem g).coeFn_toLp] with x ha hb hc hd he
        simp only [ha, hb, hc, hd, he, Pi.add_apply, add_mul]
      map_smul' d f := by
        apply Lp.ext
        filter_upwards [(mem (d • f)).coeFn_toLp, hην.ae_eq (Lp.coeFn_smul d f),
          Lp.coeFn_smul d ((mem f).toLp _), (mem f).coeFn_toLp] with x ha hb hc hd
        change ((mem (d • f)).toLp _) x = (d • (mem f).toLp _) x
        rw [ha, hb, hc]
        change d * f x * w x = d * (((mem f).toLp _) x)
        rw [hd, mul_assoc] }
  have rep (f : Lp ℂ 2 ν) : (L f : X → ℂ) =ᵐ[μ] (fun x ↦ f x * w x) := hμη.ae_eq (mem f).coeFn_toLp
  have bound (f : Lp ℂ 2 ν) : ‖L f‖ ≤ ‖f‖ := by
    rw [(weightedL2_norm_eq μ hθ hθpos (L f)).2, (weightedL2_norm_eq μ hρ hρpos f).2]
    apply Real.sqrt_le_sqrt
    exact integral_mono_ae (weightedL2_norm_eq μ hθ hθpos (L f)).1 (weightedL2_norm_eq μ hρ hρpos f).1
      ((rep f).mono fun x hx ↦ (congrArg (fun t : ℂ ↦ ‖t‖ ^ 2 * θ x) hx).le.trans (hpt f x))
  exact ⟨L.mkContinuous 1 (by simpa only [one_mul] using bound), fun f ↦ ⟨bound f, rep f⟩⟩

private def boundaryMoment (d : ℝ) (k : ℕ) (x : ℝ) : ℂ := (x : ℂ) ^ k * (Real.exp (d * x) : ℂ)

private theorem continuous_boundaryMoment (d : ℝ) (k : ℕ) : Continuous (boundaryMoment d k) :=
  (Complex.continuous_ofReal.pow k).mul (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)))

private theorem boundaryMoment_le {a b d : ℝ} (hd : d ∈ Icc a b) (N : ℕ) (k : Fin (N + 1)) (x : ℝ) :
    ‖boundaryMoment d k x‖ ^ 2 ≤ intervalSobolevDensity a b (2 * (N : ℝ)) x := by
  have he : Real.exp (2 * d * x) ≤ max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) := by
    rcases le_total 0 x with hx | hx
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [hd.2]) hx)).trans (le_max_right _ _)
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith [hd.1]) hx)).trans (le_max_left _ _)
  have hk : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
  have hp : (|x| ^ (k : ℕ)) ^ 2 ≤ (1 + x ^ 2) ^ N := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, sq_abs]
    exact (pow_le_pow_left₀ (sq_nonneg _) (by linarith) (k : ℕ)).trans
      (pow_le_pow_right₀ (by nlinarith [sq_nonneg x]) hk)
  rw [boundaryMoment, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, ← Real.exp_nat_mul, intervalSobolevDensity,
    mul_div_cancel_left₀ _ two_ne_zero, Real.rpow_natCast, mul_comm _ ((1 + x ^ 2) ^ N)]
  push_cast
  rw [← mul_assoc]
  exact mul_le_mul hp he (Real.exp_pos _).le (by positivity)

private theorem boundaryMoment_operator (a b d : ℝ) (hd : d ∈ Icc a b) (N : ℕ) (k : Fin (N + 1)) :
    let E := CompactIntervalSobolev volume id a b (2 * (N : ℝ))
    ∃ L : E →L[ℂ] Lp ℂ 2 (volume : Measure ℝ), ∀ f,
      (L f : ℝ → ℂ) =ᵐ[volume] fun x ↦ f x * boundaryMoment d k x := by
  intro E
  have h := weightedL2_multiply volume (θ := fun _ ↦ 1) (continuous_intervalSobolevDensity' a b _).measurable
    measurable_const (intervalSobolevDensity_pos _ _ _) (fun _ ↦ zero_lt_one) (boundaryMoment d k)
    (continuous_boundaryMoment _ _).measurable (fun x ↦ (mul_one _).le.trans (boundaryMoment_le hd N k x))
  have hη : volume.withDensity (fun _ : ℝ ↦ ENNReal.ofReal 1) = volume := by simp
  rw [hη] at h
  exact ⟨h.choose, fun f ↦ (h.choose_spec f).2⟩

private def sobolevAngularHaar : Measure ℝ := ENNReal.ofReal (1 / (2 * Real.pi)) • volume

private theorem angularFrequency_preserving :
    MeasurePreserving (fun y : ℝ ↦ (-(2 * Real.pi)⁻¹) * y) sobolevAngularHaar volume := by
  let d := (2 * Real.pi)⁻¹
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨by fun_prop, ?_⟩
  simp only [sobolevAngularHaar, one_div]
  change (ENNReal.ofReal d • (volume : Measure ℝ)).map (fun y ↦ (-d) • y) = volume
  rw [Measure.map_smul, Measure.map_addHaar_smul _ (neg_ne_zero.mpr hd.ne'), Module.finrank_self,
    pow_one, inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hd), smul_smul,
    ← ENNReal.ofReal_mul hd.le, mul_inv_cancel₀ hd.ne', ENNReal.ofReal_one, one_smul]
  fun_prop

open scoped FourierTransform in
private def angularFourier : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 sobolevAngularHaar :=
  (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ _ angularFrequency_preserving).toContinuousLinearMap.comp
    (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap

private theorem angularFourier_apply (f : Lp ℂ 2 (volume : Measure ℝ)) {g : ℝ → ℂ}
    (hg : Integrable g) (hf : (f : ℝ → ℂ) =ᵐ[volume] g) :
    (angularFourier f : ℝ → ℂ) =ᵐ[sobolevAngularHaar] fun y ↦ ∫ x, g x * Complex.exp ((y * x : ℝ) * Complex.I) := by
  open scoped FourierTransform in
  have hF := fourier_L2_coeFn_of_integrable f (hg.congr hf.symm)
  filter_upwards [Lp.coeFn_compMeasurePreserving ((Lp.fourierTransformₗᵢ ℝ ℂ) f) angularFrequency_preserving,
    angularFrequency_preserving.quasiMeasurePreserving.ae hF] with y h₁ h₂
  refine h₁.trans (h₂.trans ?_)
  rw [Real.fourier_eq']
  apply integral_congr_ae (hf.mono fun x hx ↦ ?_)
  rw [hx, smul_eq_mul, mul_comm (g x)]
  congr 2
  rw [real_inner_comm, Real.inner_apply]
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem boundaryMoment_kernel (v : ℂ) (d y x : ℝ) (k : ℕ) :
    v * boundaryMoment d k x * Complex.exp ((y*x : ℝ) * Complex.I) =
      v * (x : ℂ)^k * Complex.exp (verticalPoint d y * (x : ℂ)) := by
  unfold boundaryMoment
  rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_mul]
  rw [show verticalPoint d y * (x : ℂ) = (d : ℂ)*x + ((y : ℂ)*x)*Complex.I by ring, Complex.exp_add]
  ring

private theorem boundaryMoment_limit_exists (a b : ℝ) (hab : a < b) (N : ℕ)
    (c : ℝ) (hc : c ∈ ({a,b} : Set ℝ))
    (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))) (k : Fin (N+1)) :
    ∃ w : Lp ℂ 2 (volume : Measure ℝ), ∀ᵐ y ∂volume, Tendsto
      (fun d : ℝ ↦ ∫ x : ℝ, f x * (x : ℂ) ^ (k : ℕ) * Complex.exp (verticalPoint d y * (x : ℂ)))
      (𝓝[Ioo a b] c) (𝓝 (w y)) := by
  have hp (x : ℝ) : (|x| ^ (k : ℕ)) ^ 2 ≤ (1 + x ^ 2) ^ N := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, sq_abs]
    exact (pow_le_pow_left₀ (sq_nonneg _) (by linarith) (k : ℕ)).trans
      (pow_le_pow_right₀ (by nlinarith [sq_nonneg x]) (Nat.lt_succ_iff.mp k.isLt))
  have h := weightedL2_multiply volume (continuous_intervalSobolevDensity' a b (2 * (N : ℝ))).measurable
    (continuous_intervalSobolevDensity' a b 0).measurable (intervalSobolevDensity_pos _ _ _)
    (intervalSobolevDensity_pos _ _ _) (fun x : ℝ ↦ (x : ℂ) ^ (k : ℕ)) (by fun_prop) (fun x ↦ ?_)
  · let q := h.choose f
    obtain ⟨w, hw, -⟩ := scalarIntervalSobolev_boundary_values a b 0 hab le_rfl c hc q
    refine ⟨w, hw.mono fun y hy ↦ ?_⟩
    apply hy.congr fun d ↦ integral_congr_ae ?_
    exact ((h.choose_spec f).2).mono fun x hx ↦ congrArg (· * Complex.exp (verticalPoint d y * (x : ℂ))) hx
  · simp only [intervalSobolevDensity, zero_div, Real.rpow_zero, mul_one, show 2 * (N : ℝ) / 2 = (N : ℝ) by ring,
      Real.rpow_natCast, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hp x) (le_max_of_le_left (Real.exp_pos _).le)

private theorem boundaryMoment_tendsto {a b c : ℝ} (hc : c ∈ Icc a b) (N : ℕ) (k : Fin (N+1))
    (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))) {d : ℕ → ℝ}
    (hd : ∀ n, d n ∈ Icc a b) (hdc : Tendsto d atTop (𝓝 c))
    (u : ℕ → Lp ℂ 2 (volume : Measure ℝ)) (v : Lp ℂ 2 (volume : Measure ℝ))
    (hu : ∀ n, (u n : ℝ → ℂ) =ᵐ[volume] fun x ↦ f x * boundaryMoment (d n) k x)
    (hv : (v : ℝ → ℂ) =ᵐ[volume] fun x ↦ f x * boundaryMoment c k x) : Tendsto u atTop (𝓝 v) := by
  let ρ := intervalSobolevDensity a b (2 * (N : ℝ))
  have hρ := (weightedL2_norm_eq volume (continuous_intervalSobolevDensity' a b _).measurable
    (intervalSobolevDensity_pos a b _) f).1
  have hb (e : ℝ) (he : e ∈ Icc a b) (x : ℝ) : ‖f x * boundaryMoment e k x‖^2 ≤ ‖f x‖^2 * ρ x := by
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left (boundaryMoment_le he N k x) (sq_nonneg _)
  let F (n : ℕ) (x : ℝ) := ‖(u n - v) x‖ ^ 2
  have hrep (n : ℕ) : ∀ᵐ x : ℝ, (u n - v) x = f x * boundaryMoment (d n) k x - f x * boundaryMoment c k x := by
    filter_upwards [Lp.coeFn_sub (u n) v, hu n, hv] with x h₁ h₂ h₃
    simpa only [Pi.sub_apply, h₂, h₃] using h₁
  have h := tendsto_integral_of_dominated_convergence (F := F) (f := fun _ ↦ (0 : ℝ))
    (fun x ↦ 4 * (‖f x‖^2 * ρ x)) (fun n ↦ (Lp.aestronglyMeasurable (u n - v)).norm.pow 2)
    (hρ.const_mul 4) (fun n ↦ ?_) ?_
  · apply tendsto_iff_dist_tendsto_zero.mpr
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simpa only [Function.comp_def, F, L2.integral_sq_norm (𝕜 := ℂ), Real.sqrt_sq (norm_nonneg _),
      integral_zero, Real.sqrt_zero, dist_eq_norm] using ht
  · filter_upwards [hrep n] with x hx
    simp only [F, Real.norm_of_nonneg (sq_nonneg _), hx]
    have hh := sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2
      (norm_sub_le (f x * boundaryMoment (d n) k x) (f x * boundaryMoment c k x))
    nlinarith [hb _ (hd n) x, hb _ hc x,
      sq_nonneg (‖f x * boundaryMoment (d n) k x‖ - ‖f x * boundaryMoment c k x‖)]
  · filter_upwards [ae_all_iff.mpr hrep] with x hx
    have hcont : Continuous (fun e : ℝ ↦ ‖f x * boundaryMoment e k x - f x * boundaryMoment c k x‖ ^ 2) := by
      unfold boundaryMoment
      fun_prop
    have hh := (hcont.tendsto c).comp hdc
    simpa only [Function.comp_def, F, hx, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hh

private theorem boundaryMoment_mem_trace (a b : ℝ) (hab : a ≤ b) (N : ℕ) (c : ℝ)
    (L : Fin (N+1) → CompactIntervalSobolev volume id a b (2 * (N : ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hL : ∀ k f, (L k f : ℝ → ℂ) =ᵐ[volume] fun x ↦ f x * boundaryMoment c k x)
    (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))) :
    (WithLp.toLp 2 (fun _ : Unit ↦ WithLp.toLp 2 (fun k ↦ angularFourier (L k f)))) ∈
      hardySobolevTraceClosure (fun _ : Unit ↦ c) N sobolevAngularHaar := by
  let ν := sobolevAngularHaar
  have hc : 0 < 1 / (2 * Real.pi) := by positivity
  let : ν.IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul volume
    (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top
  let E := CompactIntervalSobolev volume id a b (2 * (N : ℝ))
  let T (v : E) := WithLp.toLp 2 (fun _ : Unit ↦ WithLp.toLp 2 (fun k ↦ angularFourier (L k v)))
  have ht : Continuous T := by
    dsimp only [T]
    fun_prop
  let H := hardySobolevTraceClosure (fun _ : Unit ↦ c) N ν
  have hclosed : IsClosed (H : Set (PiLp 2 (fun _ : Unit ↦ PiLp 2 (fun _ : Fin (N+1) ↦ Lp ℂ 2 ν)))) := by
    apply Submodule.isClosed_topologicalClosure
  obtain ⟨j, -, hj, hrep⟩ := scalarIntervalSobolev_dense a b (2 * (N : ℝ)) hab (by positivity)
    univ isOpen_univ ordConnected_univ (subset_univ _)
  apply hj.induction_on (p := fun v ↦ T v ∈ H) f (hclosed.preimage ht)
  intro φ
  let S := scalarTraceFamily (fun _ : Unit ↦ c) N univ (fun _ ↦ trivial) ν
  have heq : T (j φ) = S φ := by
    ext i k : 2
    apply Lp.ext
    have hφ (x : ℝ) : scalarMomentTwist univ ⟨c, trivial⟩ k φ x = φ.val x * boundaryMoment c k x := by
      rw [scalarMomentTwist_apply, boundaryMoment]
      ring
    have hi : Integrable (fun x ↦ φ.val x * boundaryMoment c k x) :=
      (scalarMomentTwist univ ⟨c, trivial⟩ k φ).integrable.congr (ae_of_all _ hφ)
    have hinput := (hL k (j φ)).trans ((hrep φ).mono fun x hx ↦ congrArg (· * boundaryMoment c k x) hx)
    have hf := angularFourier_apply (L k (j φ)) hi hinput
    have hs := scalarTraceFamily_rep (fun _ : Unit ↦ c) N isOpen_univ (fun _ ↦ trivial) ν φ i k
    apply hf.trans
    apply Filter.EventuallyEq.trans _ hs.symm
    filter_upwards with y
    rw [scalarDecay_mellin_deriv isOpen_univ φ k (mem_univ _), mellin_logProfile (fun x ↦ (x : ℂ)^(k : ℕ) * φ.val x)]
    exact integral_congr_ae (ae_of_all _ fun x ↦ (boundaryMoment_kernel _ _ _ _ _).trans (by ring))
  rw [heq]
  have he := scalarTraceFamily_closure (fun _ : Unit ↦ c) N ν
  change S φ ∈ hardySobolevTraceClosure _ _ _
  rw [← he]
  exact S.range.le_topologicalClosure (LinearMap.mem_range_self S φ)

private theorem boundaryMoment_identify (a b : ℝ) (hab : a < b) (N : ℕ)
    (c : ℝ) (hc : c ∈ ({a,b} : Set ℝ)) (hc' : c ∈ Icc a b)
    (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))) (k : Fin (N+1))
    (v : Lp ℂ 2 (volume : Measure ℝ)) (hv : (v : ℝ → ℂ) =ᵐ[volume] fun x ↦ f x * boundaryMoment c k x) :
    ∀ᵐ y ∂volume, Tendsto
      (fun d : ℝ ↦ ∫ x : ℝ, f x * (x : ℂ) ^ (k : ℕ) * Complex.exp (verticalPoint d y * (x : ℂ)))
      (𝓝[Ioo a b] c) (𝓝 (angularFourier v y)) := by
  have hcl : c ∈ closure (Ioo a b) := (closure_Ioo hab.ne).symm ▸ hc'
  obtain ⟨d, hd, hdc⟩ := mem_closure_iff_seq_limit.mp hcl
  have hd' (n) : d n ∈ Icc a b := ⟨(hd n).1.le, (hd n).2.le⟩
  let u (n : ℕ) := (boundaryMoment_operator a b (d n) (hd' n) N k).choose f
  have hu (n) := (boundaryMoment_operator a b (d n) (hd' n) N k).choose_spec f
  have hl := boundaryMoment_tendsto hc' N k f hd' hdc u v hu hv
  obtain ⟨ψ, hψ, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp ((angularFourier.continuous.tendsto v).comp hl)).exists_seq_tendsto_ae
  let M (d y : ℝ) := ∫ x : ℝ, f x * (x : ℂ) ^ (k : ℕ) * Complex.exp (verticalPoint d y * (x : ℂ))
  have hi (n) : (angularFourier (u n) : ℝ → ℂ) =ᵐ[sobolevAngularHaar] M (d n) := by
    obtain ⟨_, hn⟩ := scalarIntervalSobolev_eval_interior a b (2 * (N : ℝ)) (by positivity) (d n : ℂ)
      (by simpa using hd n) k
    have hg : Integrable (fun x ↦ f x * boundaryMoment (d n) k x) := by
      apply (hn f).1.congr (ae_of_all _ fun x ↦ ?_)
      rw [boundaryMoment, Complex.ofReal_exp, Complex.ofReal_mul]
      exact mul_assoc _ _ _
    exact (angularFourier_apply _ hg (hu n)).trans (ae_of_all _ fun y ↦
      integral_congr_ae (ae_of_all _ fun x ↦ boundaryMoment_kernel _ _ _ _ _))
  have hae : ae sobolevAngularHaar = ae (volume : Measure ℝ) :=
    Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.mpr (by positivity : 0 < 1 / (2 * Real.pi))).ne' _
  have hi' (n) : ∀ᵐ y ∂volume, angularFourier (u n) y = M (d n) y := by
    simpa only [Filter.EventuallyEq, hae] using hi n
  rw [hae] at hlim
  obtain ⟨w, hw⟩ := boundaryMoment_limit_exists a b hab N c hc f k
  have hseq := (tendsto_nhdsWithin_iff.mpr ⟨hdc, Eventually.of_forall hd⟩).comp hψ.tendsto_atTop
  filter_upwards [ae_all_iff.mpr hi', hlim, hw] with y hy hy' hw'
  have hboundary : w y = angularFourier v y := tendsto_nhds_unique (hw'.comp hseq)
    (hy'.congr fun i ↦ hy (ψ i))
  rwa [← hboundary]

/-- Paper: Proposition 9.2.2.4(2), p. 414. At even degree the almost-everywhere endpoint
limits of the moments from order zero through N are the traces of one element of the
Hardy–Sobolev space on that line.
Deviation: State the compact nondegenerate case in the weighted source model.

Deviation: Proposition 9.2.2.4(2) gives a line-space trace on the sampled completion, though
interior sampling can produce a limit with no $L^2$ endpoint trace. The even-degree line-space
traces here use the physical norm controlling both endpoints.
-/
theorem scalarIntervalSobolev_boundary_traces (a b : ℝ) (_hab : a < b) (N : ℕ)
    (c : ℝ) (_hc : c ∈ ({a, b} : Set ℝ))
    (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))) :
    ∃ u : ScalarLineHardySobolev c N,
      ∀ k : Fin (N + 1), ∀ᵐ y : ℝ ∂volume, Tendsto
        (fun σ : ℝ ↦ ∫ x : ℝ, f x * (x : ℂ) ^ (k : ℕ) *
          Complex.exp (verticalPoint σ y * (x : ℂ)))
        (𝓝[Ioo a b] c) (𝓝 (u.val () k y)) := by
  have hc : c ∈ Icc a b := by
    rcases _hc with (rfl | hc)
    · exact left_mem_Icc.mpr _hab.le
    · rw [Set.mem_singleton_iff.mp hc]
      exact right_mem_Icc.mpr _hab.le
  let L (k : Fin (N+1)) := (boundaryMoment_operator a b c hc N k).choose
  have hL (k : Fin (N+1)) := (boundaryMoment_operator a b c hc N k).choose_spec
  exact ⟨⟨_, boundaryMoment_mem_trace a b _hab.le N c L hL f⟩,
    fun k ↦ boundaryMoment_identify a b _hab N c _hc hc f k _ (hL k f)⟩

/-- Paper: Corollary 9.2.2.5(1), p. 414. The kth complex derivative of the
Mellin integral on the open strip equals the absolutely convergent kth moment.
Deviation: State the compact-base assertion in logarithmic coordinates. -/
theorem scalarIntervalSobolev_iteratedDeriv_mellin (a b s : ℝ) (_hs : 0 ≤ s)
    (f : CompactIntervalSobolev volume id a b s) (k : ℕ) (z : ℂ) (_hz : z.re ∈ Ioo a b) :
    AnalyticAt ℂ (fun w : ℂ ↦ ∫ x : ℝ, f x * Complex.exp (w * (x : ℂ))) z ∧
      Integrable (fun x : ℝ ↦ f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ x : ℝ, f x * Complex.exp (w * (x : ℂ))) z =
        ∫ x : ℝ, f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  refine iteratedDeriv_exp_moment (fun σ hσ n ↦ ?_) k _hz
  obtain ⟨_, hΛ⟩ := scalarIntervalSobolev_eval_interior a b s _hs (σ : ℂ)
    (by rwa [Complex.ofReal_re]) n
  exact (hΛ f).1

/-- A class that agrees almost everywhere with a test profile vanishing outside `U` has the
Mellin derivative of the profile as its moment against the kernel cut off to `U`. -/
private theorem integral_cutoff_moment_eq_iteratedDeriv_mellin
    (f : PositiveRealExponentialDecay univ) {u : ℝ → ℂ} (hu : u =ᵐ[volume] f.val)
    {U : Set ℝ} (hU : ∀ x, x ∉ U → f.val x = 0) (k : ℕ) (z : ℂ) :
    ∫ x : ℝ, u x * U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x =
      iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z := by
  have hint : ∀ σ ∈ Ioo (z.re - 1) (z.re + 1), ∀ n : ℕ, Integrable
      (fun x : ℝ ↦ f.val x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) volume :=
    fun σ _ n ↦ integrable_logExponentialDecay_moment f σ n
  have hmel : mellin (fun t ↦ f.val (Real.log t)) =
      fun w : ℂ ↦ ∫ x : ℝ, f.val x * Complex.exp (w * (x : ℂ)) :=
    funext fun w ↦ mellin_comp_log_eq f.val w
  rw [hmel, (iteratedDeriv_exp_moment hint k ⟨by linarith, by linarith⟩).2.2]
  refine integral_congr_ae ?_
  filter_upwards [hu] with x hx
  by_cases hmem : x ∈ U
  · rw [Set.indicator_of_mem hmem, hx, mul_assoc]
  · rw [Set.indicator_of_notMem hmem, hU x hmem, mul_zero, zero_mul, zero_mul]

/-- The squared modulus of the moment kernel. -/
private theorem norm_sq_moment_kernel (k : ℕ) (z : ℂ) (x : ℝ) :
    ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ ^ 2 = x ^ (2 * k) * Real.exp (2 * z.re * x) := by
  have hre : (z * (x : ℂ)).re = z.re * x := by simp
  have h1 : ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ = |x| ^ k * Real.exp (z.re * x) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre]
  have h2 : (|x| ^ k) ^ 2 = x ^ (2 * k) := by
    rw [← pow_mul, mul_comm, pow_mul, sq_abs, ← pow_mul]
  have h3 : Real.exp (z.re * x) ^ 2 = Real.exp (2 * z.re * x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h1, mul_pow, h2, h3]

/-- For an abscissa in the base interval, the squared moment kernel divided by the
compact-interval density is at most a quotient of powers. -/
private theorem sq_moment_kernel_div_density_le {a b s : ℝ} (k : ℕ) (z : ℂ)
    (hz : z.re ∈ Icc a b) (x : ℝ) :
    ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ ^ 2 * (intervalSobolevDensity a b s x)⁻¹ ≤
      x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
  have hy : 0 < (1 + x ^ 2) ^ (s / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hmpos : 0 < max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) :=
    lt_max_of_lt_left (Real.exp_pos _)
  have hm : Real.exp (2 * z.re * x) ≤ max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) := by
    rcases le_total 0 x with hx | hx
    · exact le_max_of_le_right (Real.exp_le_exp.2
        (by nlinarith [mul_nonneg (sub_nonneg.2 hz.2) hx]))
    · exact le_max_of_le_left (Real.exp_le_exp.2
        (by nlinarith [mul_nonneg (sub_nonneg.2 hz.1) (neg_nonneg.2 hx)]))
  rw [norm_sq_moment_kernel]
  unfold intervalSobolevDensity
  rw [mul_inv, mul_assoc, ← mul_assoc (Real.exp _)]
  refine mul_le_mul_of_nonneg_left ?_ (Even.pow_nonneg (even_two_mul k) x)
  refine mul_le_of_le_one_left (inv_nonneg.2 hy.le) ?_
  rw [← div_eq_mul_inv]
  exact (div_le_one hmpos).2 hm

/-- On the half-line where the exponential of an endpoint abscissa is the larger endpoint
weight, the squared moment kernel divided by the density is a quotient of powers. -/
private theorem sq_moment_kernel_div_density_eq {a b s : ℝ} (hab : a ≤ b) (k : ℕ) (z : ℂ)
    {x : ℝ} (hx : (z.re = b ∧ 0 ≤ x) ∨ (z.re = a ∧ x ≤ 0)) :
    ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ ^ 2 * (intervalSobolevDensity a b s x)⁻¹ =
      x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
  have hmax : max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) = Real.exp (2 * z.re * x) := by
    rcases hx with ⟨h, hx⟩ | ⟨h, hx⟩
    · rw [h]
      exact max_eq_right (Real.exp_le_exp.2
        (by nlinarith [mul_nonneg (sub_nonneg.2 hab) hx]))
    · rw [h]
      exact max_eq_left (Real.exp_le_exp.2
        (by nlinarith [mul_nonneg (sub_nonneg.2 hab) (neg_nonneg.2 hx)]))
  rw [norm_sq_moment_kernel]
  unfold intervalSobolevDensity
  rw [hmax, mul_inv, mul_assoc, ← mul_assoc (Real.exp _),
    mul_inv_cancel₀ (Real.exp_pos _).ne', one_mul]

/-- The quotient of powers is integrable exactly above the critical degree: sufficiency. -/
private theorem integrable_pow_mul_rpow_inv {k : ℕ} {s : ℝ} (h : 2 * (k : ℝ) + 1 < s) :
    Integrable (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < s - 2 * k := by
    rw [Module.finrank_self]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hr).mono'
    ((measurable_id.pow_const (2 * k)).mul
      ((measurable_const.add (measurable_id.pow_const 2)).pow_const
        (s / 2)).inv).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hy : 0 < 1 + x ^ 2 := by positivity
  have h1 : x ^ (2 * k) ≤ (1 + x ^ 2) ^ k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg x) (by linarith) k
  have h2 : (1 + x ^ 2) ^ (-(s - 2 * k) / 2) = (1 + x ^ 2) ^ k * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
    rw [← Real.rpow_natCast (1 + x ^ 2) k, ← Real.rpow_neg hy.le, ← Real.rpow_add hy]
    congr 1
    ring
  rw [Real.norm_of_nonneg (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
    (inv_nonneg.2 (Real.rpow_nonneg hy.le _))), Real.norm_eq_abs, sq_abs, h2]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 (Real.rpow_nonneg hy.le _))

/-- The quotient of powers is integrable exactly above the critical degree: necessity. -/
private theorem lt_of_integrableOn_pow_mul_rpow_inv {k : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (h : IntegrableOn (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) (Ioi 1)) :
    2 * (k : ℝ) + 1 < s := by
  have key : IntegrableOn (fun x : ℝ ↦ x ^ (2 * (k : ℝ) - s)) (Ioi 1) := by
    refine Integrable.mono' (Integrable.const_mul h ((2 : ℝ) ^ (s / 2)))
      (measurable_id.pow_const _).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun x hx ↦ ?_))
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : 0 < x := by linarith
    have hpos : 0 < (1 + x ^ 2) ^ (s / 2) := Real.rpow_pos_of_pos (by positivity) _
    have hcast : ((2 : ℕ) : ℝ) * (s / 2) = s := by
      push_cast
      ring
    have h1 : (1 + x ^ 2) ^ (s / 2) ≤ 2 ^ (s / 2) * x ^ s :=
      calc (1 + x ^ 2) ^ (s / 2) ≤ (2 * x ^ 2) ^ (s / 2) :=
            Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
        _ = 2 ^ (s / 2) * x ^ s := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast x 2,
              ← Real.rpow_mul hx0.le, hcast]
    have e : x ^ (2 * (k : ℝ) - s) = x ^ (2 * k) / x ^ s := by
      rw [Real.rpow_sub hx0, ← Real.rpow_natCast x (2 * k)]
      push_cast
      rfl
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), e, div_eq_mul_inv, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Even.pow_nonneg (even_two_mul k) x)
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, ← div_eq_inv_mul,
      div_le_iff₀ (Real.rpow_pos_of_pos hx0 s)]
    exact h1
  have hlt := (integrableOn_Ioi_rpow_iff zero_lt_one).1 key
  linarith

/-- At an abscissa of the base interval and above the critical degree, the moment kernel cut
off to a measurable set gives a continuous functional on the compact-interval space. -/
private theorem intervalSobolev_boundary_moment_functional (a b s : ℝ) (k : ℕ) (z : ℂ)
    (hz : z.re ∈ Icc a b) (hk : 2 * (k : ℝ) + 1 < s) {U : Set ℝ} (hU : MeasurableSet U) :
    ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) →L[ℂ] ℂ,
      ∀ f, Integrable (fun x : ℝ ↦ f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x) volume ∧
        Λ f = ∫ x : ℝ, f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
  have hker : Continuous fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) :=
    (Complex.continuous_ofReal.pow k).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hρm := (continuous_intervalSobolevDensity' a b s).measurable
  refine weightedL2_pairing volume hρm (intervalSobolevDensity_pos a b s)
    (hker.measurable.indicator hU).aestronglyMeasurable ?_
  refine (integrable_pow_mul_rpow_inv hk).mono'
    (((hker.measurable.indicator hU).norm.pow_const 2).mul hρm.inv).aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  have hpos := intervalSobolevDensity_pos a b s x
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 hpos.le))]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
    (norm_indicator_le_norm_self _ _) 2) (inv_nonneg.2 hpos.le)).trans
    (sq_moment_kernel_div_density_le k z hz x)

/-- Below the upper endpoint, the moment kernel cut off above a point gives a continuous
functional on the compact-interval space. -/
private theorem intervalSobolev_cutoff_moment_functional (a b s : ℝ) (hs : 0 ≤ s) {A : ℝ}
    (hA : 1 < A) (z : ℂ) (hz : z.re < b) (k : ℕ) :
    ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) →L[ℂ] ℂ,
      ∀ f, Integrable (fun x : ℝ ↦ f x * (Ici (-Real.log A)).indicator
          (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x) volume ∧
        Λ f = ∫ x : ℝ, f x * (Ici (-Real.log A)).indicator
          (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hbz : 0 < b - z.re := sub_pos.2 hz
  exact intervalSobolev_moment_functional a b s hs z k
    (measurableSet_Ici (a := -Real.log A)) (δ := 2 * (b - z.re))
    (K := Real.exp (4 * (b - z.re) * Real.log A)) (mul_pos two_pos hbz) (Real.exp_pos _).le
    fun x hx ↦ by
      have hx' : -Real.log A ≤ x := hx
      have hle : 2 * z.re * x + 2 * (b - z.re) * |x| ≤
          4 * (b - z.re) * Real.log A + 2 * b * x := by
        rcases le_total 0 x with h0 | h0
        · rw [abs_of_nonneg h0]
          nlinarith [mul_pos hbz hlogA]
        · rw [abs_of_nonpos h0]
          nlinarith [mul_nonneg hbz.le (by linarith : 0 ≤ Real.log A + x)]
      calc Real.exp (2 * z.re * x + 2 * (b - z.re) * |x|)
          ≤ Real.exp (4 * (b - z.re) * Real.log A + 2 * b * x) := Real.exp_le_exp.2 hle
        _ = Real.exp (4 * (b - z.re) * Real.log A) * Real.exp (2 * b * x) := Real.exp_add _ _
        _ ≤ Real.exp (4 * (b - z.re) * Real.log A) *
            max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos _).le

/-- If a continuous functional on the compact-interval space evaluates the Mellin derivative
of each test supported in an open set, then the squared moment kernel is integrable on that
set against the reciprocal density: the functional is integration against a class of the dual
space, and this class agrees with the kernel almost everywhere on the set. -/
private theorem integrableOn_sq_moment_kernel_of_eval (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (k : ℕ) (z : ℂ) {V : Set ℝ} (hV : IsOpen V)
    (Λ : CompactIntervalSobolev volume id a b s →L[ℂ] ℂ)
    (hΛ : ∀ (f : PositiveRealExponentialDecay univ)
      (u : CompactIntervalSobolev volume id a b s),
      tsupport f.val ⊆ V → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) :
    IntegrableOn (fun x : ℝ ↦ ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ ^ 2 *
      (intervalSobolevDensity a b s x)⁻¹) V := by
  have hρc := continuous_intervalSobolevDensity' a b s
  have hρpos := intervalSobolevDensity_pos a b s
  have hρi : Measurable fun x ↦ (intervalSobolevDensity a b s x)⁻¹ := hρc.measurable.inv
  have hρipos : ∀ x, 0 < (intervalSobolevDensity a b s x)⁻¹ := fun x ↦ inv_pos.2 (hρpos x)
  have hker : Continuous fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) :=
    (Complex.continuous_ofReal.pow k).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  obtain ⟨T, hT, -⟩ := scalarIntervalSobolev_dual a b s hab hs
  have hv2 := (weightedL2_norm_eq volume hρi hρipos (T Λ)).1
  have hvloc : LocallyIntegrable (T Λ : ℝ → ℂ) volume := by
    refine locallyIntegrable_iff.2 fun K hK ↦ ?_
    obtain ⟨_, hpair⟩ := weightedL2_pairing volume hρi hρipos
      (w := K.indicator fun _ ↦ (1 : ℂ))
      (measurable_const.indicator hK.measurableSet).aestronglyMeasurable
      (((integrable_indicator_iff hK.measurableSet).2
        (hρc.continuousOn.integrableOn_compact hK (μ := volume))).congr
        (ae_of_all _ fun x ↦ by
          by_cases hx : x ∈ K
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]))
    refine (integrable_indicator_iff hK.measurableSet).1
      ((hpair (T Λ)).1.congr (ae_of_all _ fun x ↦ ?_))
    by_cases hx : x ∈ K
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hloc : LocallyIntegrableOn
      (fun x : ℝ ↦ T Λ x - (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) V volume :=
    (hvloc.sub hker.locallyIntegrable).locallyIntegrableOn V
  have hae := hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgV ↦ by
    have hg₁ : HasCompactSupport fun x ↦ (g x : ℂ) := hgc.comp_left Complex.ofReal_zero
    have hcont : Continuous fun x ↦ (g x : ℂ) := Complex.continuous_ofReal.comp hg.continuous
    let fT : PositiveRealExponentialDecay univ := ⟨fun x ↦ (g x : ℂ),
      mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hg₁
        (Complex.ofRealCLM.contDiff.comp hg)⟩
    have : IsLocallyFiniteMeasure (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) :=
      IsLocallyFiniteMeasure.withDensity_ofReal hρc
    have hmem : MemLp (fun x ↦ (g x : ℂ)) 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) :=
      hcont.memLp_of_hasCompactSupport hg₁
    have hbase : (volume : Measure ℝ) ≪ volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x) :=
      withDensity_absolutelyContinuous' hρc.measurable.ennreal_ofReal.aemeasurable
        (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hρpos x)).ne')
    let u : CompactIntervalSobolev volume id a b s := hmem.toLp _
    have hu : (u : ℝ → ℂ) =ᵐ[volume] fun x ↦ (g x : ℂ) := hbase.ae_le hmem.coeFn_toLp
    have h1 := hΛ fT u ((tsupport_comp_subset Complex.ofReal_zero g).trans hgV) hu
    have h3 := integral_cutoff_moment_eq_iteratedDeriv_mellin fT
      (u := fun x ↦ (g x : ℂ)) (ae_eq_refl _) (U := univ)
      (fun x hx ↦ absurd (mem_univ x) hx) k z
    have hint1 : Integrable (fun x ↦ (g x : ℂ) * T Λ x) volume :=
      (hT Λ u).1.congr (hu.mono fun x hx ↦ congrArg (· * T Λ x) hx)
    have hint2 : Integrable (fun x : ℝ ↦ (g x : ℂ) *
        ((x : ℂ) ^ k * Complex.exp (z * (x : ℂ)))) volume :=
      (hcont.mul hker).integrable_of_hasCompactSupport hg₁.mul_right
    have heq : ∫ x, (g x : ℂ) * T Λ x =
        ∫ x : ℝ, (g x : ℂ) * ((x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) :=
      calc ∫ x, (g x : ℂ) * T Λ x = ∫ x, u x * T Λ x :=
            (integral_congr_ae (hu.mono fun x hx ↦ congrArg (· * T Λ x) hx)).symm
        _ = Λ u := (hT Λ u).2.symm
        _ = iteratedDeriv k (mellin (fun t ↦ fT.val (Real.log t))) z := h1
        _ = ∫ x : ℝ, (g x : ℂ) * (univ : Set ℝ).indicator
              (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := h3.symm
        _ = _ := by simp only [Set.indicator_univ]
    calc ∫ x, g x • (T Λ x - (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)))
        = ∫ x, ((g x : ℂ) * T Λ x -
            (g x : ℂ) * ((x : ℂ) ^ k * Complex.exp (z * (x : ℂ)))) :=
          integral_congr_ae (ae_of_all _ fun x ↦ by
            simp only [Complex.real_smul, mul_sub])
      _ = 0 := by rw [integral_sub hint1 hint2, heq, sub_self]
  refine hv2.integrableOn.congr
    ((ae_restrict_iff' hV.measurableSet).2 (hae.mono fun x hx hxV ↦ ?_))
  beta_reduce
  rw [sub_eq_zero.1 (hx hxV)]

/-- On supported tests the Mellin derivative evaluation at an endpoint abscissa extends
continuously exactly below the upper endpoint or above the critical degree. -/
private theorem intervalSobolev_cutoff_eval_endpoints_iff (a b A s : ℝ)
    (hab : a ≤ b) (hA : 1 < A) (hs : 0 ≤ s) (k : ℕ) (z : ℂ)
    (hz : z.re ∈ ({a, b} : Set ℝ)) :
    (∃ Λ : CompactIntervalSobolev volume id a b s →L[ℂ] ℂ,
      ∀ (f : PositiveRealExponentialDecay univ) (u : CompactIntervalSobolev volume id a b s),
      tsupport f.val ⊆ Ioi (-Real.log A) → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔
      z.re < b ∨ 2 * (k : ℝ) + 1 < s := by
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hzI : z.re ∈ Icc a b := by
    rcases hz with h | h
    · rw [h]
      exact ⟨le_rfl, hab⟩
    · rw [show z.re = b from h]
      exact ⟨hab, le_rfl⟩
  constructor
  · rintro ⟨Λ, hΛ⟩
    by_cases hzb : z.re < b
    · exact Or.inl hzb
    · have h : z.re = b := le_antisymm hzI.2 (not_lt.1 hzb)
      have hint := integrableOn_sq_moment_kernel_of_eval a b s hab hs k z (V := Ioi 1)
        isOpen_Ioi Λ fun f u hsupp hu ↦
          hΛ f u (hsupp.trans (Ioi_subset_Ioi (by linarith))) hu
      exact Or.inr (lt_of_integrableOn_pow_mul_rpow_inv hs (hint.congr_fun (fun x hx ↦
        sq_moment_kernel_div_density_eq hab k z
          (Or.inl ⟨h, by linarith [show (1 : ℝ) < x from hx]⟩)) measurableSet_Ioi))
  · intro h
    have hfun : ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) →L[ℂ] ℂ,
        ∀ f, Integrable (fun x : ℝ ↦ f x * (Ici (-Real.log A)).indicator
            (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x) volume ∧
          Λ f = ∫ x : ℝ, f x * (Ici (-Real.log A)).indicator
            (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
      rcases h with h | h
      · exact intervalSobolev_cutoff_moment_functional a b s hs hA z h k
      · exact intervalSobolev_boundary_moment_functional a b s k z hzI h measurableSet_Ici
    obtain ⟨Λ, hΛ⟩ := hfun
    refine ⟨Λ, fun f u hsupp hu ↦ ?_⟩
    exact (hΛ u).2.trans (integral_cutoff_moment_eq_iteratedDeriv_mellin f hu (fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h' ↦ hx (Ioi_subset_Ici_self (hsupp h'))) k z)
-- TODO(paper-gap): Corollary 9.2.2.5(2) includes the divergent critical case s = 2k + 1.

/-- Paper: Corollary 9.2.2.5(2), p. 414. At either endpoint, a Mellin derivative
evaluation on the unrestricted tests extends continuously exactly when the degree
exceeds twice the derivative order plus one.
Deviation: The compact weighted model includes a singleton base. The critical
equality in the printed bound is excluded. -/
theorem scalarIntervalSobolev_eval_boundary_iff (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (k : ℕ) (z : ℂ) (_hz : z.re ∈ ({a, b} : Set ℝ)) :
    let E := CompactIntervalSobolev volume id a b s
    (∃ Λ : E →L[ℂ] ℂ, ∀ (f : PositiveRealExponentialDecay univ) (u : E),
      (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔ 2 * (k : ℝ) + 1 < s :=
  by
  intro E
  have hzI : z.re ∈ Icc a b := by
    rcases _hz with h | h
    · rw [h]
      exact ⟨le_rfl, _hab⟩
    · rw [show z.re = b from h]
      exact ⟨_hab, le_rfl⟩
  constructor
  · rintro ⟨Λ, hΛ⟩
    rcases _hz with h | h
    · have hint := integrableOn_sq_moment_kernel_of_eval a b s _hab _hs k z (V := Iio (-1))
        isOpen_Iio Λ fun f u _ hu ↦ hΛ f u hu
      have hG : IntegrableOn (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
          (Iio (-1)) :=
        hint.congr_fun (fun x hx ↦ sq_moment_kernel_div_density_eq _hab k z
          (Or.inr ⟨h, by linarith [show x < -1 from hx]⟩)) measurableSet_Iio
      refine lt_of_integrableOn_pow_mul_rpow_inv _hs
        (hG.comp_neg_Ioi.congr_fun (fun x _ ↦ ?_) measurableSet_Ioi)
      simp only [Even.neg_pow (even_two_mul k), neg_sq]
    · have hint := integrableOn_sq_moment_kernel_of_eval a b s _hab _hs k z (V := Ioi 1)
        isOpen_Ioi Λ fun f u _ hu ↦ hΛ f u hu
      exact lt_of_integrableOn_pow_mul_rpow_inv _hs (hint.congr_fun (fun x hx ↦
        sq_moment_kernel_div_density_eq _hab k z
          (Or.inl ⟨h, by linarith [show (1 : ℝ) < x from hx]⟩)) measurableSet_Ioi)
  · intro hk
    obtain ⟨Λ, hΛ⟩ := intervalSobolev_boundary_moment_functional a b s k z hzI hk
      MeasurableSet.univ
    refine ⟨Λ, fun f u hu ↦ ?_⟩
    exact (hΛ u).2.trans (integral_cutoff_moment_eq_iteratedDeriv_mellin f hu
      (fun x hx ↦ absurd (mem_univ x) hx) k z)

/-- Paper: Theorem 9.2.2.6(1), p. 415. On a compact base interval of even
degree the supported test closure is the same as the indicator range.
Deviation: Restrict the base to the case where the printed norm is finite on the tests. -/
theorem scalarIntervalSobolev_cutoff_closure (a b A : ℝ) (_hab : a ≤ b) (_hA : 1 < A)
    (N : ℕ) (J : Set ℝ) (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    closure {u : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) |
      ∃ f : PositiveRealExponentialDecay J,
        tsupport f.val ⊆ Ioi (-Real.log A) ∧ (u : ℝ → ℂ) =ᵐ[volume] f.val} =
      {u : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) |
        (u : ℝ → ℂ) =ᵐ[volume] (Ici (-Real.log A)).indicator (u : ℝ → ℂ)} := by
  let ρ := intervalSobolevDensity a b (2 * (N : ℝ))
  let μ := volume.withDensity fun x ↦ ENNReal.ofReal (ρ x)
  have hρ : Continuous ρ := continuous_intervalSobolevDensity' _ _ _
  have hpos : ∀ x, 0 < ρ x := intervalSobolevDensity_pos _ _ _
  refine (scalarDecay_cutoff_range J (-Real.log A) ρ hρ hpos).trans ?_
  have hv : volume ≪ μ := withDensity_absolutelyContinuous' hρ.measurable.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  have hw : μ ≪ volume := withDensity_absolutelyContinuous _ _
  let U := Ici (-Real.log A)
  have rep (f : Lp ℂ 2 μ) :
      (hardySobolevCutoff (U := U) measurableSet_Ici f : ℝ → ℂ) =ᵐ[μ] U.indicator f :=
    MemLp.coeFn_toLp _
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    change _ =ᵐ[volume] U.indicator _
    filter_upwards [hv.ae_eq (rep v)] with x hx
    by_cases h : x ∈ U
    · simp [h]
    · simpa [h] using hx
  · intro hu
    exact ⟨u, Lp.ext ((rep u).trans (hw.ae_eq (show (u : ℝ → ℂ) =ᵐ[volume] U.indicator u from hu).symm))⟩

-- TODO(paper-gap): Theorem 9.2.2.6(2) uses the undefined absolute spaces and
-- (9.2.2.28) has the same unspecified growth condition as (9.2.1.7).
-- TODO(paper-gap): Definition 9.2.2.7 refers back to that growth condition.

/-- Paper: Corollary 9.2.2.8(1), p. 415. In the supported space, derivative
evaluations have continuous extensions to all fixed abscissas below the upper endpoint.
Deviation: Use the compact-interval source model and the extension by the indicator. -/
theorem scalarIntervalSobolev_cutoff_eval (a b A : ℝ) (_hab : a ≤ b) (_hA : 1 < A)
    (N k : ℕ) (z : ℂ) (_hz : z.re < b) :
    ∃ Λ : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) →L[ℂ] ℂ,
      ∀ (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))),
        Integrable (fun x : ℝ ↦ (Ici (-Real.log A)).indicator (⇑f) x *
        (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
        Λ f = ∫ x : ℝ, (Ici (-Real.log A)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  change ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
      ENNReal.ofReal (intervalSobolevDensity a b (2 * (N : ℝ)) x)) →L[ℂ] ℂ,
    ∀ f : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b (2 * (N : ℝ)) x)),
      Integrable (fun x : ℝ ↦ (Ici (-Real.log A)).indicator (⇑f) x *
        (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
      Λ f = ∫ x : ℝ, (Ici (-Real.log A)).indicator (⇑f) x *
        (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))
  have hlogA : 0 < Real.log A := Real.log_pos _hA
  have hbz : 0 < b - z.re := sub_pos.2 _hz
  obtain ⟨Λ, hΛ⟩ := intervalSobolev_moment_functional a b (2 * (N : ℝ)) (by positivity) z k
    (measurableSet_Ici (a := -Real.log A)) (δ := 2 * (b - z.re))
    (K := Real.exp (4 * (b - z.re) * Real.log A)) (mul_pos two_pos hbz) (Real.exp_pos _).le
    fun x hx ↦ by
      have hx' : -Real.log A ≤ x := hx
      have hle : 2 * z.re * x + 2 * (b - z.re) * |x| ≤
          4 * (b - z.re) * Real.log A + 2 * b * x := by
        rcases le_total 0 x with h0 | h0
        · rw [abs_of_nonneg h0]
          nlinarith [mul_pos hbz hlogA]
        · rw [abs_of_nonpos h0]
          nlinarith [mul_nonneg hbz.le (by linarith : 0 ≤ Real.log A + x)]
      calc Real.exp (2 * z.re * x + 2 * (b - z.re) * |x|)
          ≤ Real.exp (4 * (b - z.re) * Real.log A + 2 * b * x) := Real.exp_le_exp.2 hle
        _ = Real.exp (4 * (b - z.re) * Real.log A) * Real.exp (2 * b * x) := Real.exp_add _ _
        _ ≤ Real.exp (4 * (b - z.re) * Real.log A) *
            max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos _).le
  refine ⟨Λ, fun f ↦ ?_⟩
  have hfun : (fun x : ℝ ↦ (Ici (-Real.log A)).indicator (⇑f) x *
      (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) = fun x : ℝ ↦ f x *
      (Ici (-Real.log A)).indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
    funext x
    by_cases hx : x ∈ Ici (-Real.log A)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_assoc]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, zero_mul, mul_zero]
  rw [hfun]
  exact hΛ f

/-- Paper: Corollary 9.2.2.8(1), p. 415. On the open half-plane below the upper
endpoint, the kth derivative of the supported Mellin integral is its kth moment.
Deviation: Use the cutoff in logarithmic coordinates on the compact-base source. -/
theorem scalarIntervalSobolev_cutoff_iteratedDeriv_mellin
    (a b A : ℝ) (_hab : a ≤ b) (_hA : 1 < A) (N k : ℕ)
    (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))) (z : ℂ) (_hz : z.re < b) :
    let g := (Ici (-Real.log A)).indicator (f : ℝ → ℂ)
    AnalyticAt ℂ (fun w : ℂ ↦ ∫ x : ℝ, g x * Complex.exp (w * (x : ℂ))) z ∧
      Integrable (fun x : ℝ ↦ g x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ x : ℝ, g x * Complex.exp (w * (x : ℂ))) z =
        ∫ x : ℝ, g x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  intro g
  refine iteratedDeriv_exp_moment (α := z.re - 1) (β := b) (fun σ hσ n ↦ ?_) k
    ⟨by linarith, _hz⟩
  obtain ⟨_, hΛ⟩ := scalarIntervalSobolev_cutoff_eval a b A _hab _hA N n (σ : ℂ)
    (by rw [Complex.ofReal_re]; exact hσ.2)
  exact (hΛ f).1

/-- Paper: Corollary 9.2.2.8(2), p. 416. At the upper endpoint a derivative
evaluation of an even-degree supported space is bounded exactly below order N.
Deviation: State bounded extendibility of the evaluation on supported tests in the
compact-interval source model. Here the degree is 2N, so there is no critical equality.

Deviation: The source of the upper-endpoint assertion in Corollary 9.2.2.8(2) is implicit after
the construction on p. 415. We use the physical endpoint norm. In this norm bounded
extendibility for even degree agrees with the printed range.
-/
theorem scalarIntervalSobolev_cutoff_eval_boundary_iff (a b A : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (N k : ℕ) (z : ℂ) (_hz : z.re = b) :
    (∃ Λ : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) →L[ℂ] ℂ,
      ∀ (f : PositiveRealExponentialDecay univ) (u : CompactIntervalSobolev volume id a b (2 * (N : ℝ))),
        tsupport f.val ⊆ Ioi (-Real.log A) → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔ k < N := by
  refine (intervalSobolev_cutoff_eval_endpoints_iff a b A (2 * (N : ℝ)) _hab _hA
    (by positivity) k z (by rw [_hz]; simp)).trans ⟨fun h ↦ ?_, fun h ↦ Or.inr ?_⟩
  · rcases h with h | h
    · exact absurd h (by rw [_hz]; exact lt_irrefl b)
    · have h2 : 2 * k + 1 < 2 * N := by exact_mod_cast h
      omega
  · have h2 : 2 * k + 1 < 2 * N := by omega
    exact_mod_cast h2

/-- Paper: Corollary 9.2.2.8(1)–(2), p. 415. On supported scalar tests every order
extends at a distinct lower endpoint. At the upper endpoint the degree must exceed
twice the derivative order plus one.
Deviation: State the endpoint criterion in the compact weighted model for all nonnegative
degrees. The corollary states the even-degree case, with part (2) on p. 416.

Deviation: The source of the upper-endpoint assertion on p. 416 is implicit after the
construction on p. 415. In the physical endpoint norm the supported functional extends exactly
when $\Re z<b$ or $2k+1<s$.
-/
theorem scalarIntervalSobolev_cutoff_eval_endpoints_iff (a b A s : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) (k : ℕ) (z : ℂ)
    (_hz : z.re ∈ ({a, b} : Set ℝ)) :
    let E := CompactIntervalSobolev volume id a b s
    (∃ Λ : E →L[ℂ] ℂ, ∀ (f : PositiveRealExponentialDecay univ) (u : E),
      tsupport f.val ⊆ Ioi (-Real.log A) → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔
      z.re < b ∨ 2 * (k : ℝ) + 1 < s := by
  intro E
  exact intervalSobolev_cutoff_eval_endpoints_iff a b A s _hab _hA _hs k z _hz

end Interval

section ModulatedInterval

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)

local notation "K" => m.toMonoidHom.ker

local instance instMeasurableSpaceDualKerSec2 : MeasurableSpace (PontryaginDual K) := borel _

/-- Paper: Definition 9.2.2.9, p. 416. For a compact base interval the
canonical group-side Sobolev space is weighted L² for the canonical Haar measure.
Deviation: Only compact base intervals give a finite norm on all the stated tests.
Use `intervalSobolevENorm` for the supremum expression on other intervals. -/
abbrev ModulatedIntervalSobolev (a b s : ℝ) :=
  CompactIntervalSobolev (canonicalModulatedHaar m hm) (logModule m) a b s

private theorem sobolev_interval_poly_bound (a b s : ℝ) :
    ∃ n : ℕ, ∀ x : ℝ, intervalSobolevDensity a b s x ≤ 1 * (1 + |x|) ^ n *
      max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (s / 2)
  refine ⟨2 * n, fun x ↦ ?_⟩
  rw [one_mul, intervalSobolevDensity, mul_comm (max _ _)]
  apply mul_le_mul_of_nonneg_right _ ((Real.exp_pos _).le.trans (le_max_left _ _))
  calc
    (1 + x ^ 2) ^ (s / 2) ≤ (1 + x ^ 2) ^ (n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) hn
    _ = (1 + x ^ 2) ^ n := Real.rpow_natCast _ _
    _ ≤ ((1 + |x|) ^ 2) ^ n := pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg x, sq_abs x]) n
    _ = _ := (pow_mul _ _ _).symm

/-- Paper: Lemma 9.2.2.10(1), p. 416. On a compact base interval each open-interval
test space containing the base embeds continuously and densely in the weighted space.
Deviation: This states the compact case, with the canonical choice of Haar measure. -/
theorem modulatedIntervalSobolev_dense
    (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) (J : Set ℝ)
    (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    ∃ j : ModulatedExponentialDecay m J →L[ℂ] ModulatedIntervalSobolev m hm a b s,
      Injective j ∧ DenseRange j ∧
      ∀ f, (j f : G → ℂ) =ᵐ[canonicalModulatedHaar m hm] f.val := by
  let hpoly := sobolev_interval_poly_bound a b s
  let h := modulatedDecay_dense_of_weight m hm J _hJ a b _hab (_hsub (left_mem_Icc.mpr _hab))
    (_hsub (right_mem_Icc.mpr _hab)) (intervalSobolevDensity a b s) (continuous_intervalSobolevDensity' a b s)
    (intervalSobolevDensity_pos a b s) 1 zero_le_one hpoly.choose hpoly.choose_spec
  exact h

/-- Paper: Lemma 9.2.2.10(1), p. 416. For a compact base interval and an even degree,
pullback to split coordinates followed by the unitary kernel Fourier transform
identifies the space with the completed Hilbert tensor product.
Deviation: The pullback in (9.2.2.32) lands in physical kernel coordinates
before applying the compact Fourier transform. Use the weighted norm of (9.2.2.34). -/
theorem modulatedIntervalSobolev_tensor (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace K] [BorelSpace K] (μ₁ : Measure K) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (ν₁ : Measure (PontryaginDual K)) (hν₁ : IsLCAPlancherelMeasure μ₁ ν₁)
    (a b : ℝ) (_hab : a ≤ b) (N : ℕ) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
    let U := Classical.choose (lcaFourier_unitary μ₁ ν₁ hν₁).exists
    let E := ModulatedIntervalSobolev m hm a b (2 * (N : ℝ))
    let E₀ := CompactIntervalSobolev volume id a b (2 * (N : ℝ))
    ∃ P : E ≃ₗᵢ[ℂ] UniformSpace.Completion (E₀ ⊗[ℂ] Lp ℂ 2 ν₁),
      ∀ (f : E₀) (g : Lp ℂ 2 μ₁) (u : E),
        (fun p : K × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[μ₁.prod positiveRealHaar]
          (fun p ↦ f (Real.log (p.2.val : ℝ)) * g p.1) →
        P u = ↑(f ⊗ₜ[ℂ] U g) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  intro U E E₀
  obtain ⟨P, hP⟩ := sobolevSplit_tensor m hm τ _hτ μ₁ _hμ₁ _
    (continuous_intervalSobolevDensity' a b (2 * (N : ℝ)))
  obtain ⟨Q, hQ⟩ := exists_completion_isometry (U.lTensor E₀)
  refine ⟨P.trans Q, fun f g u h ↦ ?_⟩
  change Q (P u) = _
  rw [hP f g u h, hQ]
  rfl

/-- Paper: Lemma 9.2.2.10(1), p. 416. For a compact base interval and an even degree,
pullback to split coordinates followed by the unitary kernel Fourier transform and dual inversion
identifies the space with the completed Hilbert tensor product.
Deviation: The pullback in (9.2.2.32) lands in physical kernel coordinates
before applying the compact Fourier transform at the inverse character, as in (9.2.1.25).
Use the weighted norm of (9.2.2.34). -/
theorem modulatedIntervalSobolev_tensor_isotype (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace K] [BorelSpace K] (μ₁ : Measure K) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (ν₁ : Measure (PontryaginDual K)) (hν₁ : IsLCAPlancherelMeasure μ₁ ν₁)
    (a b : ℝ) (_hab : a ≤ b) (N : ℕ) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
    letI : BorelSpace (PontryaginDual K) := ⟨rfl⟩
    letI : ν₁.IsHaarMeasure := hν₁.1
    letI : ν₁.Regular := hν₁.2.1
    let U := Classical.choose (lcaFourier_unitary μ₁ ν₁ hν₁).exists
    let invert := Lp.compMeasurePreserving (E := ℂ) (p := 2) Inv.inv
      (Measure.measurePreserving_inv ν₁)
    let E := ModulatedIntervalSobolev m hm a b (2 * (N : ℝ))
    let E₀ := CompactIntervalSobolev volume id a b (2 * (N : ℝ))
    ∃ P : E ≃ₗᵢ[ℂ] UniformSpace.Completion (E₀ ⊗[ℂ] Lp ℂ 2 ν₁),
      ∀ (f : E₀) (g : Lp ℂ 2 μ₁) (u : E),
        (fun p : K × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[μ₁.prod positiveRealHaar]
          (fun p ↦ f (Real.log (p.2.val : ℝ)) * g p.1) →
        P u = ↑(f ⊗ₜ[ℂ] invert (U g)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : BorelSpace (PontryaginDual K) := ⟨rfl⟩
  let : ν₁.IsHaarMeasure := hν₁.1
  let : ν₁.Regular := hν₁.2.1
  intro U invert E E₀
  obtain ⟨P, hP⟩ := modulatedIntervalSobolev_tensor m hm τ _hτ μ₁ _hμ₁ ν₁ hν₁ a b _hab N
  let invL : Lp ℂ 2 ν₁ →ₗᵢ[ℂ] Lp ℂ 2 ν₁ :=
    Lp.compMeasurePreservingₗᵢ ℂ Inv.inv (Measure.measurePreserving_inv ν₁)
  have hinv (w : Lp ℂ 2 ν₁) : invL (invL w) = w := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ w) = w
    rw [← Lp.compMeasurePreserving_comp_apply]
    simpa only [inv_comp_inv] using Lp.compMeasurePreserving_id_apply w
  let V := LinearIsometryEquiv.ofSurjective invL fun w ↦ ⟨invL w, hinv w⟩
  obtain ⟨Q, hQ⟩ := exists_completion_isometry (V.lTensor E₀)
  refine ⟨P.trans Q, fun f g u h ↦ ?_⟩
  change Q (P u) = _
  rw [hP f g u h, hQ]
  rfl

open UniformSpace in
private theorem exists_completion_equiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃L[ℂ] F) :
    ∃ P : Completion E ≃L[ℂ] Completion F, ∀ x : E, P ↑x = ↑(e x) := by
  let i : E →ₗ[ℂ] Completion E := Completion.toComplL.toLinearMap
  let j : F →ₗ[ℂ] Completion F := Completion.toComplL.toLinearMap
  have h₁ (x : E) : ‖j (e x)‖ ≤ ‖e.toContinuousLinearMap‖ * ‖i x‖ := by
    change ‖(↑(e x) : Completion F)‖ ≤ _ * ‖(↑x : Completion E)‖
    rw [Completion.norm_coe, Completion.norm_coe]
    exact e.toContinuousLinearMap.le_opNorm x
  have h₂ (x : F) : ‖i (e.symm x)‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖j x‖ := by
    change ‖(↑(e.symm x) : Completion E)‖ ≤ _ * ‖(↑x : Completion F)‖
    rw [Completion.norm_coe, Completion.norm_coe]
    exact e.symm.toContinuousLinearMap.le_opNorm x
  exact ⟨e.toLinearEquiv.extend i j Completion.denseRange_coe ⟨_, h₁⟩ Completion.denseRange_coe ⟨_, h₂⟩,
    e.toLinearEquiv.extend_eq i j Completion.denseRange_coe ⟨_, h₁⟩ Completion.denseRange_coe ⟨_, h₂⟩⟩

/-- Paper: Lemma 9.2.2.10(1), p. 416. For compact bases and even degrees,
the scalar Mellin transform on split elementary tensors acts by vertical derivative
traces and the Fourier transform acts on the kernel factor.
Deviation: Use the two endpoint traces of Lemma 9.2.2.2(2) and the Hilbert norm
which sums their squared norms. The compact Fourier transform follows the positive
character convention of (9.2.1.25), so the character in `lcaFourier` is inverted. -/
theorem modulatedIntervalSobolev_mellin_endpoints (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace K] [BorelSpace K] (μ₁ : Measure K) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (ν₁ : Measure (PontryaginDual K)) (_hν₁ : IsLCAPlancherelMeasure μ₁ ν₁)
    (a b : ℝ) (_hab : a ≤ b) (N : ℕ) :
    let E := ModulatedIntervalSobolev m hm a b (2 * (N : ℝ))
    let σ : Bool → ℝ := fun i ↦ if i then b else a
    let H := hardySobolevTraceClosure σ N volume
    ∃ M : E ≃L[ℂ] UniformSpace.Completion (H ⊗[ℂ] Lp ℂ 2 ν₁),
      ∀ (f : PositiveRealExponentialDecay univ) (g : Lp ℂ 2 μ₁) (u : E),
        Integrable (g : K → ℂ) μ₁ →
        (fun p : K × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[μ₁.prod positiveRealHaar]
          (fun p ↦ f.val (Real.log (p.2.val : ℝ)) * g p.1) →
        ∃ (v : H) (w : Lp ℂ 2 ν₁),
          (∀ i (k : Fin (N + 1)), (v.val i k : ℝ → ℂ) =ᵐ[volume]
            fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
              (verticalPoint (σ i) y)) ∧
          (w : PontryaginDual K → ℂ) =ᵐ[ν₁] (fun χ ↦ lcaFourier μ₁ g χ⁻¹) ∧
          M u = ↑(v ⊗ₜ[ℂ] w) := by
  intro E σ H
  let : InnerProductSpace ℂ H := Submodule.innerProductSpace H
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : BorelSpace (PontryaginDual K) := ⟨rfl⟩
  let : ν₁.IsHaarMeasure := _hν₁.1
  let : ν₁.Regular := _hν₁.2.1
  let U := Classical.choose (lcaFourier_unitary μ₁ ν₁ _hν₁).exists
  let invert := Lp.compMeasurePreserving (E := ℂ) (p := 2) Inv.inv (Measure.measurePreserving_inv ν₁)
  have hPex := modulatedIntervalSobolev_tensor_isotype m hm τ _hτ μ₁ _hμ₁ ν₁ _hν₁ a b _hab N
  let P := hPex.choose
  have hP := hPex.choose_spec
  have hSex := scalarIntervalSobolev_mellin_endpoints a b _hab N univ isOpen_univ ordConnected_univ (subset_univ _)
  let S := hSex.choose
  have hS := hSex.choose_spec
  have hjex := scalarIntervalSobolev_dense a b (2 * (N : ℝ)) _hab (by positivity)
    univ isOpen_univ ordConnected_univ (subset_univ _)
  let j := hjex.choose
  have hj := hjex.choose_spec.2.2
  have hQex := exists_completion_equiv (TensorProduct.congrL S (ContinuousLinearEquiv.refl ℂ (Lp ℂ 2 ν₁)))
  let Q := hQex.choose
  have hQ := hQex.choose_spec
  refine ⟨P.toContinuousLinearEquiv.trans Q, fun f g u hg hu ↦
    ⟨S (j f), invert (U g), hS f (j f) (hj f), ?_, ?_⟩⟩
  · have hUg : (U g : PontryaginDual K → ℂ) =ᵐ[ν₁] lcaFourier μ₁ g := by
      simpa only [Lp.toLp_coeFn] using
        (Classical.choose_spec (lcaFourier_unitary μ₁ ν₁ _hν₁).exists) g hg (Lp.memLp g)
    exact (Lp.coeFn_compMeasurePreserving (U g) (Measure.measurePreserving_inv ν₁)).trans
      ((Measure.measurePreserving_inv ν₁).quasiMeasurePreserving.ae hUg)
  · change Q (P u) = _
    refine (congrArg Q (hP (j f) g u ?_)).trans (hQ _)
    filter_upwards [hu, (Measure.quasiMeasurePreserving_snd (μ := μ₁) (ν := positiveRealHaar)).ae
          (sobolevLog_ae (hj f))] with p hp hf
    change (j f) (Real.log (p.2.val : ℝ)) = f.val _ at hf
    simpa only [hf] using hp

/-- Paper: Lemma 9.2.2.10(2), p. 417. For a compact base the norm of a completed
element is the square root of the integral with the maximum endpoint weight.
Deviation: The formula holds for the L² representative in the completed space. -/
theorem modulatedIntervalSobolev_norm (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (f : ModulatedIntervalSobolev m hm a b s) :
    let μ := canonicalModulatedHaar m hm
    let integrand := fun g ↦ ‖f g‖ ^ 2 * intervalSobolevDensity a b s (logModule m g)
    Integrable integrand μ ∧ ‖f‖ = Real.sqrt (∫ g, integrand g ∂μ) ∧
      intervalSobolevENorm μ (logModule m) (Icc a b) s (⇑f) = ENNReal.ofReal ‖f‖ := by
  intro μ integrand
  have hDpos : ∀ x : ℝ, 0 < intervalSobolevDensity a b s x := fun x ↦
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  -- Shrinking the endpoints inside `[a, b]` only lowers the density.
  have hmono : ∀ a' ∈ Icc a b, ∀ b' ∈ Icc a b, ∀ x : ℝ,
      intervalSobolevDensity a' b' s x ≤ intervalSobolevDensity a b s x := by
    intro a' ha' b' hb' x
    have key : ∀ c ∈ Icc a b,
        Real.exp (2 * c * x) ≤ max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) := by
      intro c hc
      rcases le_total 0 x with hx | hx
      · exact le_max_of_le_right (Real.exp_le_exp.2 (by nlinarith [hc.2]))
      · exact le_max_of_le_left (Real.exp_le_exp.2 (by nlinarith [hc.1]))
    exact mul_le_mul_of_nonneg_right (max_le (key a' ha') (key b' hb')) (by positivity)
  have hcont : Continuous fun g : G ↦ ((m g).val : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hDmeas : Measurable fun g : G ↦ intervalSobolevDensity a b s (logModule m g) := by
    have hlog : Measurable (logModule m) := Real.measurable_log.comp hcont.measurable
    unfold intervalSobolevDensity
    fun_prop
  have hρ : AEMeasurable (fun g ↦ (intervalSobolevDensity a b s (logModule m g)).toNNReal) μ :=
    hDmeas.real_toNNReal.aemeasurable
  have hf2 : Integrable (fun g ↦ ‖f g‖ ^ 2)
      (μ.withDensity fun g ↦
        ((intervalSobolevDensity a b s (logModule m g)).toNNReal : ℝ≥0∞)) := by
    have h := (Lp.memLp f).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    exact h
  have hsmul : ∀ g, (intervalSobolevDensity a b s (logModule m g)).toNNReal • ‖f g‖ ^ 2 =
      integrand g := fun g ↦ by
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hDpos _).le, mul_comm]
  have hint : ∫ g, integrand g ∂μ = ∫ g, ‖f g‖ ^ 2
      ∂μ.withDensity fun g ↦
        ((intervalSobolevDensity a b s (logModule m g)).toNNReal : ℝ≥0∞) := by
    rw [integral_withDensity_eq_integral_smul₀ hρ]
    exact integral_congr_ae (Eventually.of_forall fun g ↦ (hsmul g).symm)
  refine ⟨?_, ?_, ?_⟩
  · exact ((integrable_withDensity_iff_integrable_smul₀ hρ).1 hf2).congr
      (Eventually.of_forall hsmul)
  · rw [hint, Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero
      ENNReal.ofNat_ne_top (Lp.memLp f), ENNReal.toReal_ofReal (by positivity),
      Real.sqrt_eq_rpow]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]
    rfl
  · have hE : intervalSobolevENorm μ (logModule m) (Icc a b) s (⇑f) =
        eLpNorm f 2 (μ.withDensity fun g ↦
          ENNReal.ofReal (intervalSobolevDensity a b s (logModule m g))) := by
      unfold intervalSobolevENorm
      refine le_antisymm (iSup₂_le fun a' b' ↦ eLpNorm_mono_measure _ (withDensity_mono
        (Eventually.of_forall fun g ↦ ENNReal.ofReal_le_ofReal (hmono _ a'.2 _ b'.2 _)))) ?_
      exact le_iSup₂_of_le (⟨a, left_mem_Icc.2 _hab⟩ : Icc a b) ⟨b, right_mem_Icc.2 _hab⟩ le_rfl
    rw [hE, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
    rfl

/-- Paper: Lemma 9.2.2.10(3)(a), p. 417. The right half-line supremum can
be indexed using the left endpoint and one varying abscissa.
Deviation: Use extended values and read `t` in (9.2.2.35) as the module of g. -/
theorem modulatedIntervalSobolev_enorm_Ici (a s : ℝ) (_hs : 0 ≤ s)
    (f : ModulatedExponentialDecay m univ) :
    let μ := canonicalModulatedHaar m hm
    intervalSobolevENorm μ (logModule m) (Ici a) s f.val =
      ⨆ σ : Ici a, eLpNorm f.val 2 (μ.withDensity fun g ↦
        ENNReal.ofReal (intervalSobolevDensity a σ s (logModule m g))) :=
  intervalSobolevENorm_Ici _ (logModule m) a s f.val

/-- Paper: Lemma 9.2.2.10(3)(b), p. 417. The left half-line supremum can
be indexed using one varying abscissa and the right endpoint.
Deviation: Use extended values for the supremum in (9.2.2.36). -/
theorem modulatedIntervalSobolev_enorm_Iic (b s : ℝ) (_hs : 0 ≤ s)
    (f : ModulatedExponentialDecay m univ) :
    let μ := canonicalModulatedHaar m hm
    intervalSobolevENorm μ (logModule m) (Iic b) s f.val =
      ⨆ σ : Iic b, eLpNorm f.val 2 (μ.withDensity fun g ↦
        ENNReal.ofReal (intervalSobolevDensity σ b s (logModule m g))) :=
  intervalSobolevENorm_Iic _ (logModule m) b s f.val

-- TODO(paper-gap): As in Proposition 9.2.1.8, the test pairing and the
-- reciprocal-density norm are not defined on all the stated inputs.

/-- Paper: Proposition 9.2.2.11, p. 417. The weighted space pairs with the
reciprocal-density space via the unweighted integral and represents its strong dual.
Deviation: Use the Haar measure from the proposition on both sides. The test pairing
on all of S_J × S_J and the reciprocal-norm completion of all of S_J can fail. The paper
assumes a < b, but §10.2–10.4 apply (9.2.2.42) to I = [−α, α] with α ≥ 0, so the one-point
base is included. -/
theorem modulatedIntervalSobolev_dual (_hm : IsModulation m)
    (μ : Measure G) [μ.IsHaarMeasure] (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) :
    ∃! T : StrongDual ℂ (CompactIntervalSobolev μ (logModule m) a b s) ≃ₗᵢ[ℂ]
        CompactIntervalSobolev μ (logModule m) a b s true,
      ∀ Λ f, Integrable (fun g ↦ f g * T Λ g) μ ∧
        Λ f = ∫ g, f g * T Λ g ∂μ := by
  have hlog : Measurable (fun g ↦ Real.log ((m g).val : ℝ)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable.log
  have hρ := (continuous_intervalSobolevDensity' a b s).measurable.comp hlog
  exact weightedL2_dual μ hρ hρ.inv (fun g ↦ intervalSobolevDensity_pos a b s _)
    (fun g ↦ inv_pos.mpr (intervalSobolevDensity_pos a b s _))
    (fun g ↦ mul_inv_cancel₀ (intervalSobolevDensity_pos a b s _).ne')

/-- For a nonnegative degree, the compact-interval density dominates the exponential of its
upper endpoint. -/
private theorem exp_le_intervalSobolevDensity (a b s : ℝ) (hs : 0 ≤ s) (x : ℝ) :
    Real.exp (2 * b * x) ≤ intervalSobolevDensity a b s x := by
  have h1 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (s / 2) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith)
  unfold intervalSobolevDensity
  exact (le_max_right _ _).trans
    (le_mul_of_one_le_right (le_max_of_le_left (Real.exp_pos _).le) h1)
-- TODO(paper-gap): Corollary 9.2.2.12(1) omits the kernel character in the integral
-- for a general isotype and uses m rather than k for the power of the logarithm.

/-- Paper: Corollary 9.2.2.12(1), p. 418. Each isotype has a bounded
interior derivative evaluation on the supported compact-interval space.
Deviation: Use the weighted source model and the intrinsic quasi-character for
the chosen isotype. The printed formula corresponds to the trivial character.

Deviation: Equation (9.2.2.43) omits the kernel character and uses log power $m$ for the $k$th
derivative. We use the intrinsic twisted character, including the phase of its lift, and log
power $k$.
-/
theorem modulatedIntervalSobolev_cutoff_eval (a b A s : ℝ)
    (_hA : 1 < A) (_hs : 0 ≤ s) (z : ℂ) (_hz : z.re ∈ Ioo a b) (k : ℕ)
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let E := ModulatedIntervalSobolev m hm a b s
    let U := (logModule m) ⁻¹' Ici (-Real.log A)
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ z
    ∃! Λ : E →L[ℂ] ℂ,
      ∀ f : E, Integrable (fun g ↦ U.indicator (⇑f) g * (logModule m g : ℂ) ^ k * c g) μ ∧
        Λ f = ∫ g, U.indicator (⇑f) g * (logModule m g : ℂ) ^ k * c g ∂μ := by
  intro μ E U c
  have hμ : μ.IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  obtain ⟨Λ, hΛ⟩ := modulated_cutoff_moment_functional m hm μ
    (continuous_intervalSobolevDensity' a b s).measurable
    (exp_le_intervalSobolevDensity a b s _hs) _hA z _hz.2 k χ _hχ
  exact ⟨Λ, hΛ, fun Λ' hΛ' ↦ ContinuousLinearMap.ext fun f ↦ (hΛ' f).2.trans (hΛ f).2.symm⟩

/-- Paper: Corollary 9.2.2.12(1), p. 418. In the norm-twist coordinate of a unitary
quasi-character, the kth derivative of the cutoff Mellin integral equals its kth moment.
Deviation: The intrinsic quasi-character includes the character missing in (9.2.2.43),
and the cutoff gives convergence throughout the open half-plane below the upper endpoint. -/
theorem modulatedIntervalSobolev_cutoff_iteratedDeriv_mellin (a b A s : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) (k : ℕ)
    (f : ModulatedIntervalSobolev m hm a b s) (z : ℂ) (_hz : z.re < b)
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let u := ((logModule m) ⁻¹' Ici (-Real.log A)).indicator (f : G → ℂ)
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    AnalyticAt ℂ (fun w : ℂ ↦ ∫ g, u g * c w g ∂μ) z ∧
      Integrable (fun g ↦ u g * (logModule m g : ℂ) ^ k * c z g) μ ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ g, u g * c w g ∂μ) z =
        ∫ g, u g * (logModule m g : ℂ) ^ k * c z g ∂μ := by
  intro μ u c
  have hμ : μ.IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have hint : ∀ σ ∈ Ioo (z.re - 1) b, ∀ n : ℕ,
      Integrable (fun g ↦ u g * (logModule m g : ℂ) ^ n *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := fun σ hσ n ↦ by
    obtain ⟨_, hΛ⟩ := modulated_cutoff_moment_functional m hm μ
      (continuous_intervalSobolevDensity' a b s).measurable
      (exp_le_intervalSobolevDensity a b s _hs) _hA (σ : ℂ)
      (by rw [Complex.ofReal_re]; exact hσ.2) n χ _hχ
    exact (hΛ f).1
  exact iteratedDeriv_normTwist_moment m μ χ hint k
    (show z.re ∈ Ioo (z.re - 1) b from ⟨by linarith, _hz⟩)
-- TODO(paper-gap): Corollary 9.2.2.12(2) includes the divergent critical case
-- s = 2k + 1 at the upper endpoint, even for the trivial kernel character.

section

private theorem sobolev_radial_decay (hm : IsModulation m) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (f : PositiveRealExponentialDecay univ) :
    (f.val ∘ (logModule m)) ∈ modulatedExponentialDecaySubmodule m univ := by
  let K₀ := m.toMonoidHom.ker
  let : T1Space (G ⧸ K₀) := QuotientGroup.t1Space_iff.mpr hm.isCompact_ker.isClosed
  let d : (G ⧸ K₀) ≃ₜ* ℝ≥0ˣ :=
    { QuotientGroup.quotientKerEquivOfRightInverse m.toMonoidHom τ hτ with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk K₀).continuous_iff.mpr m.continuous
      continuous_invFun := QuotientGroup.continuous_mk.comp τ.continuous }
  obtain ⟨S, hS⟩ := schwartzBruhat_realCoordinate_equiv (d.trans positiveRealLogEquiv)
  apply (Submodule.mem_iInf _).2
  intro b
  let F := S (logExponentialDecayTwist univ b f)
  have hF (x : G) : F (x : G ⧸ K₀) = modulationWeight m b (f.val ∘ (logModule m)) x := by
    rw [show F _ = _ from hS _ _]
    change logExponentialDecayTwist univ b f (positiveRealLogEquiv (m x)).toAdd = _
    rw [positiveRealLogEquiv_apply, logExponentialDecayTwist_apply univ b f _]
    change (Real.exp ((b : ℝ) * logModule m x) : ℂ) * f.val (logModule m x) =
      (((((m x).val : ℝ) ^ (b : ℝ)) : ℝ) : ℂ) * f.val (logModule m x)
    rw [Real.rpow_def_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (m x))), mul_comm (b : ℝ)]
  change modulationWeight m b (f.val ∘ (logModule m)) ∈ schwartzBruhatSubmodule G
  rw [← funext hF]
  exact schwartzBruhatSubmodule_compactQuotient_pullback_mem K₀ hm.isCompact_ker F.property

private theorem sobolev_unitary_mul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (v : X → ℂ) (hv : Measurable v) (h1 : ∀ x, ‖v x‖ = 1) :
    ∃ L : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, ∀ f, (L f : X → ℂ) =ᵐ[μ] (fun x ↦ v x * f x) := by
  have hm (f : Lp ℂ 2 μ) : MemLp (fun x ↦ v x * f x) 2 μ :=
    (Lp.memLp f).mono (hv.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (ae_of_all _ fun x ↦ by simp [h1])
  let L : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun f := (hm f).toLp _
      map_add' f g := by
        apply Lp.ext
        filter_upwards [(hm (f + g)).coeFn_toLp, Lp.coeFn_add f g,
          Lp.coeFn_add ((hm f).toLp _) ((hm g).toLp _), (hm f).coeFn_toLp, (hm g).coeFn_toLp] with x h₁ h₂ h₃ h₄ h₅
        simp only [h₁, h₂, h₃, h₄, h₅, Pi.add_apply, mul_add]
      map_smul' d f := by
        apply Lp.ext
        filter_upwards [(hm (d • f)).coeFn_toLp, Lp.coeFn_smul d f,
          Lp.coeFn_smul d ((hm f).toLp _), (hm f).coeFn_toLp] with x h₁ h₂ h₃ h₄
        change ((hm (d • f)).toLp _) x = (d • (hm f).toLp _) x
        rw [h₁, h₂, h₃]
        change v x * (d * f x) = d * (((hm f).toLp _) x)
        rw [h₄, mul_left_comm] }
  have hnorm (f : Lp ℂ 2 μ) : ‖L f‖ = ‖f‖ := by
    change ‖(hm f).toLp _‖ = _
    rw [Lp.norm_toLp, Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae (hm f).aestronglyMeasurable
      (Lp.aestronglyMeasurable f) (ae_of_all _ fun x ↦ by simp [h1]))
  exact ⟨L.mkContinuous 1 (fun f ↦ by rw [one_mul, hnorm]), fun f ↦ (hm f).coeFn_toLp⟩

private theorem sobolev_character_pull (hm : IsModulation m) (hsurj : Surjective m)
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (v : G → ℂ) (hv : Continuous v) (h1 : ∀ x, ‖v x‖ = 1) :
    let l := logModule m
    let μ := canonicalModulatedHaar m hm
    let η := volume.withDensity fun x ↦ ENNReal.ofReal (ρ x)
    let ν := μ.withDensity fun x ↦ ENNReal.ofReal (ρ (l x))
    ∃ L : Lp ℂ 2 η →L[ℂ] Lp ℂ 2 ν, ∀ f, (L f : G → ℂ) =ᵐ[μ] (fun x ↦ v x * f (l x)) := by
  intro l μ η ν
  have hl := sobolev_log_preserving m hm hsurj
  have hw : MeasurePreserving l ν η := by
    refine ⟨hl.measurable, ?_⟩
    ext s hs
    rw [Measure.map_apply hl.measurable hs, withDensity_apply _ (hl.measurable hs), withDensity_apply _ hs]
    exact hl.setLIntegral_comp_preimage hs hρ.measurable.ennreal_ofReal
  have hac : μ ≪ ν := withDensity_absolutelyContinuous' (hρ.measurable.comp hl.measurable).ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos _)).ne')
  let T := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ l hw
  obtain ⟨M, hM⟩ := sobolev_unitary_mul ν v hv.measurable h1
  refine ⟨M.comp T.toContinuousLinearMap, fun f ↦ hac.ae_eq ?_⟩
  filter_upwards [hM (T f), Lp.coeFn_compMeasurePreserving f hw] with x hx hx'
  exact hx.trans (congrArg (fun z ↦ v x * z) hx')

/-- Pullback along the logarithmic modulation with a unitary character sends scalar
interval Sobolev vectors continuously to the canonical group interval space. On
exponential-decay tests the pullback has an ordinary Schwartz–Bruhat representative. -/
theorem exists_modulatedIntervalSobolev_characterLogPullback (hm : IsModulation m) (hms : Surjective m)
    (χ : PontryaginDual G) (a b s : ℝ) :
    ∃ L : CompactIntervalSobolev volume id a b s →L[ℂ] ModulatedIntervalSobolev m hm a b s,
      (∀ u, (L u : G → ℂ) =ᵐ[canonicalModulatedHaar m hm] (fun g ↦ (χ g : ℂ) * u (logModule m g))) ∧
      ∀ f : PositiveRealExponentialDecay univ, ∃ v : SchwartzBruhat G,
        ∀ g, v g = (χ g : ℂ) * f.val (logModule m g) := by
  obtain ⟨L,hL⟩ := sobolev_character_pull m hm hms _ (continuous_intervalSobolevDensity' a b s)
    (intervalSobolevDensity_pos a b s) (fun g ↦ (χ g : ℂ))
    (continuous_subtype_val.comp χ.continuous) (fun _ ↦ Circle.norm_coe _)
  refine ⟨L,hL,fun f ↦ ?_⟩
  obtain ⟨τ,hτ⟩ := exists_section_of_surjective hm.1 hms
  let u : ModulatedExponentialDecay m univ := ⟨f.val ∘ logModule m, sobolev_radial_decay m hm τ hτ f⟩
  have hu : u.val ∈ schwartzBruhatSubmodule G := by
    simpa only [modulationWeight_zero] using modulationWeight_mem_schwartzBruhat m univ ⟨0,mem_univ _⟩ u
  obtain ⟨M,hM⟩ := schwartzBruhat_mul_unitaryCharacter χ
  exact ⟨M ⟨u.val,hu⟩,hM _⟩

/-- On the upper tail the reciprocal weight supplies either exponential decay or an
integrable power. At the critical power the latter argument requires a strict inequality. -/
private theorem sobolev_endpoint_kernel (a b c s : ℝ) (hs : 0 ≤ s) (z : ℂ)
    (hz : z.re ≤ b) (k : ℕ) (hcrit : z.re < b ∨ 2 * (k : ℝ) + 1 < s) :
    IntegrableOn (fun x : ℝ ↦ ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ ^ 2 *
      (intervalSobolevDensity a b s x)⁻¹) (Ici c) := by
  let w (x : ℝ) := ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ ^ 2 * (intervalSobolevDensity a b s x)⁻¹
  have hc : Continuous w := ((Complex.continuous_ofReal.pow k).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).norm.pow 2 |>.mul
      ((continuous_intervalSobolevDensity' a b s).inv₀ fun x ↦ (intervalSobolevDensity_pos _ _ _ _).ne')
  let R := max c 1
  rw [← Icc_union_Ioi_eq_Ici (le_max_left c 1)]
  apply (hc.continuousOn.integrableOn_compact isCompact_Icc).union
  have hr : 0 < R := zero_lt_one.trans_le (le_max_right c 1)
  have hbound (x : ℝ) (hx : x ∈ Ioi R) :
      ‖w x‖ ≤ (x ^ (2 * k) * Real.exp (2 * (z.re - b) * x)) / (1 + x ^ 2) ^ (s / 2) := by
    have hx' := hr.trans hx
    have hP : 0 < (1 + x ^ 2) ^ (s / 2) := by positivity
    have hn : 0 ≤ w x := mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (intervalSobolevDensity_pos _ _ _ _).le)
    rw [Real.norm_of_nonneg hn]
    dsimp only [w]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx', Complex.norm_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_pow,
      ← pow_mul, Nat.mul_comm k 2, ← Real.exp_nat_mul, ← div_eq_mul_inv,
      div_le_div_iff₀ (intervalSobolevDensity_pos _ _ _ _) hP]
    push_cast
    have hW := mul_le_mul_of_nonneg_right (le_max_right (Real.exp (2 * a * x)) (Real.exp (2 * b * x))) hP.le
    change _ ≤ _ * intervalSobolevDensity a b s x
    apply le_trans _ (mul_le_mul_of_nonneg_left hW (by positivity))
    rw [show (2 : ℝ) * (z.re * x) = 2 * (z.re - b) * x + 2 * b * x by ring, Real.exp_add]
    exact le_of_eq (by ring)
  rcases hcrit with hz' | hk
  · have he := (integrable_abs_pow_mul_exp_neg (2 * k) (show 0 < 2 * (b - z.re) by linarith)).integrableOn (s := Ioi R)
    apply he.mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' := hr.trans hx
    apply (hbound x hx).trans
    rw [abs_of_pos hx', show -(2 * (b - z.re) * x) = 2 * (z.re - b) * x by ring]
    exact div_le_self (by positivity) (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
  · apply (integrableOn_Ioi_rpow_of_lt (a := 2 * (k : ℝ) - s) (by linarith) hr).mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' := hr.trans hx
    apply (hbound x hx).trans
    have hpow : x ^ s ≤ (1 + x ^ 2) ^ (s / 2) := calc
      x ^ s = (x ^ (2 : ℝ)) ^ (s / 2) := by rw [← Real.rpow_mul hx'.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by rw [Real.rpow_two]; linarith) (by linarith)
    rw [Real.rpow_sub hx', show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    apply div_le_div₀ (by positivity) _ (by positivity) hpow
    exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) hx'.le]))

private theorem sobolev_twist_apply (χ : QuasiCharacter G) (z : ℂ) (g : G) :
    quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g =
      χ g * Complex.exp (z * (logModule m g : ℂ)) := by
  have hpos := NNReal.coe_pos.mpr (Units.zero_lt (m g))
  change χ g * (((((m g).val : ℝ) : ℂ)) ^ z) = _
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, mul_comm _ z]

private theorem modulatedDecay_endpoint_necessary (hm : IsModulation m) (hsurj : Surjective m)
    (a b A s : ℝ) (hab : a ≤ b) (hA : 1 < A) (hs : 0 ≤ s) (k : ℕ)
    (z : ℂ) (hz : z.re ∈ ({a,b} : Set ℝ)) (χ : QuasiCharacter G) (hχ : ∀ g, ‖χ g‖ = 1)
    (Λ : ModulatedIntervalSobolev m hm a b s →L[ℂ] ℂ)
    (hΛ : ∀ (f : ModulatedExponentialDecay m univ) (u : ModulatedIntervalSobolev m hm a b s),
      tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log A) →
      (u : G → ℂ) =ᵐ[canonicalModulatedHaar m hm] f.val →
      Λ u = iteratedDeriv k (fun w ↦ modulatedFourierMellin m univ hm (canonicalModulatedHaar m hm)
        f.val (quasiCharacterNormTwist m.toMonoidHom m.continuous χ w)) z) :
    z.re < b ∨ 2 * (k : ℝ) + 1 < s := by
  let μ := canonicalModulatedHaar m hm
  let l := logModule m
  let η : PontryaginDual G :=
    { toFun := fun g ↦ ⟨χ g, mem_sphere_zero_iff_norm.mpr (hχ g)⟩
      map_one' := Circle.ext (map_one χ)
      map_mul' := fun g h ↦ Circle.ext (map_mul χ _ _)
      continuous_toFun := χ.continuous.subtype_mk _ }
  let v (g : G) : ℂ := (η⁻¹ g : Circle)
  have hv : Continuous v := continuous_subtype_val.comp η⁻¹.continuous
  have hvχ (g : G) : v g * χ g = 1 := by
    change (((η g)⁻¹ : Circle) : ℂ) * (η g : ℂ) = 1
    exact congrArg (fun t : Circle ↦ (t : ℂ)) (inv_mul_cancel (η g))
  have hv1 (g : G) : ‖v g‖ = 1 := Circle.norm_coe _
  obtain ⟨L, hL⟩ := sobolev_character_pull m hm hsurj _ (continuous_intervalSobolevDensity' a b s)
    (intervalSobolevDensity_pos a b s) v hv hv1
  obtain ⟨τ, hτ⟩ := exists_section_of_surjective hm.1 hsurj
  obtain ⟨T, hT⟩ := schwartzBruhat_mul_unitaryCharacter (η⁻¹)
  let M := modulatedExponentialDecayUnitaryMultiplication univ m (η⁻¹) T hT
  have hp := sobolev_log_preserving m hm hsurj
  apply (scalarIntervalSobolev_cutoff_eval_endpoints_iff a b A s hab hA hs k z hz).mp
  refine ⟨Λ.comp L, fun f u hf hu ↦ ?_⟩
  let g := M ⟨f.val ∘ l, sobolev_radial_decay m hm τ hτ f⟩
  have hsup : tsupport g.val ⊆ l ⁻¹' Ioi (-Real.log A) :=
    tsupport_mul_subset_right.trans ((tsupport_comp_subset_preimage f.val (sobolev_log_proper m hm).continuous).trans (preimage_mono hf))
  have hrep : (L u : G → ℂ) =ᵐ[μ] g.val := by
    filter_upwards [hL u, hp.quasiMeasurePreserving.ae hu] with x hx hy
    exact hx.trans (congrArg (fun w ↦ v x * w) hy)
  have hEq (w : ℂ) : modulatedFourierMellin m univ hm μ g.val
      (quasiCharacterNormTwist m.toMonoidHom m.continuous χ w) = mellin (fun t ↦ f.val (Real.log t)) w := by
    rw [mellin_logProfile]
    simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
    have h : ∀ x, g.val x * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w x =
        f.val (l x) * Complex.exp (w * (l x : ℂ)) := by
      intro x
      rw [sobolev_twist_apply]
      change v x * f.val (l x) * (χ x * _) = _
      rw [mul_mul_mul_comm, hvχ, one_mul]
    simp_rw [h]
    have hc : Continuous f.val := by
      let F := logExponentialDecayTwist univ ⟨0, trivial⟩ f
      apply F.continuous.congr
      intro x
      simpa only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
        logExponentialDecayTwist_apply univ ⟨0, trivial⟩ f x
    have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ f.val t * Complex.exp (w * (t : ℂ))) volume :=
      (hc.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
    exact (integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hmeas)).symm.trans
      (congrArg (fun ν : Measure ℝ ↦ ∫ t, f.val t * Complex.exp (w * (t : ℂ)) ∂ν) hp.map_eq)
  exact (hΛ g (L u) hsup hrep).trans (congrArg (fun φ : ℂ → ℂ ↦ iteratedDeriv k φ z) (funext hEq))

private theorem sobolev_indicator_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (U : Set X) (f u v p q : X → ℂ) (hu : u =ᵐ[μ] f) (hv : U.indicator v =ᵐ[μ] f) :
    (∫ x, u x * U.indicator (fun t ↦ p t * q t) x ∂μ) =
      ∫ x, U.indicator v x * p x * q x ∂μ := by
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  by_cases h : x ∈ U
  · rw [indicator_of_mem h, hx, hy, mul_assoc]
  · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero, zero_mul, zero_mul]

private theorem modulatedDecay_endpoint_sufficient (hm : IsModulation m) (hsurj : Surjective m)
    (a b A s : ℝ) (hs : 0 ≤ s) (hA : 1 < A) (k : ℕ) (z : ℂ) (hz : z.re ≤ b)
    (χ : QuasiCharacter G) (hχ : ∀ x, ‖χ x‖ = 1) (ht : z.re < b ∨ 2 * (k : ℝ) + 1 < s) :
    let μ := canonicalModulatedHaar m hm
    let E := ModulatedIntervalSobolev m hm a b s
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    ∃ Λ : E →L[ℂ] ℂ, ∀ (f : ModulatedExponentialDecay m univ) (u : E),
      tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log A) → (u : G → ℂ) =ᵐ[μ] f.val →
        Λ u = iteratedDeriv k (fun w ↦ modulatedFourierMellin m univ hm μ f.val (c w)) z := by
  intro μ E c
  let l := logModule m
  let d := -Real.log A
  let U := l ⁻¹' Ici d
  let ρ := intervalSobolevDensity a b s
  let w (g : G) := U.indicator (fun x ↦ (l x : ℂ) ^ k * c z x) g
  have hl := (sobolev_log_proper m hm).continuous
  have hp := sobolev_log_preserving m hm hsurj
  have hU : MeasurableSet U := hl.measurable measurableSet_Ici
  have hw : Measurable w :=
    (((Complex.continuous_ofReal.comp hl).pow k).mul (c z).continuous).measurable.indicator hU
  have hρ := (continuous_intervalSobolevDensity' a b s).comp hl
  have hpos (g : G) : 0 < ρ (l g) := intervalSobolevDensity_pos _ _ _ _
  let F (x : ℝ) := ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ ^ 2 * (ρ x)⁻¹
  have hI : Integrable ((Ici d).indicator F) volume :=
    (sobolev_endpoint_kernel a b d s hs z hz k ht).integrable_indicator measurableSet_Ici
  obtain ⟨Λ, hΛ⟩ := weightedL2_pairing μ (ρ := fun g ↦ ρ (l g)) hρ.measurable hpos
    (w := w) hw.aestronglyMeasurable (show Integrable (fun g ↦ ‖w g‖ ^ 2 * (ρ (l g))⁻¹) μ by
      apply (hp.integrable_comp_of_integrable hI).congr
      filter_upwards with g
      by_cases hx : g ∈ U
      · change (Ici d).indicator F (l g) = ‖U.indicator _ g‖ ^ 2 * _
        rw [indicator_of_mem (show l g ∈ Ici d from hx), indicator_of_mem hx]
        dsimp only [F]
        rw [show c z g = _ from sobolev_twist_apply m χ z g, norm_mul, norm_mul, norm_mul, hχ, one_mul]
      · change (Ici d).indicator F (l g) = ‖U.indicator _ g‖ ^ 2 * _
        rw [indicator_of_notMem (show l g ∉ Ici d from hx), indicator_of_notMem hx, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul])
  refine ⟨Λ, fun f u hf hu ↦ ?_⟩
  let B := z.re + 1
  obtain ⟨j, _, _, hj⟩ := modulatedIntervalSobolev_dense m hm B B 0 le_rfl le_rfl univ
    isOpen_univ ordConnected_univ (subset_univ _)
  have hcut : U.indicator (j f : G → ℂ) =ᵐ[μ] f.val := by
    filter_upwards [hj f] with x hx
    by_cases h : x ∈ U
    · rw [indicator_of_mem h, hx]
    · rw [indicator_of_notMem h]
      exact (image_eq_zero_of_notMem_tsupport (fun ht ↦ h (Ioi_subset_Ici_self (hf ht)))).symm
  have hder := (modulatedIntervalSobolev_cutoff_iteratedDeriv_mellin m hm B B A 0 le_rfl hA le_rfl k
    (j f) z (by dsimp [B]; linarith) χ hχ).2.2
  have hEq (v : ℂ) : (∫ x, U.indicator (j f : G → ℂ) x * c v x ∂μ) =
      modulatedFourierMellin m univ hm μ f.val (c v) := by
    simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
    exact integral_congr_ae (hcut.mul EventuallyEq.rfl)
  change iteratedDeriv k (fun v ↦ ∫ x, U.indicator (j f : G → ℂ) x * c v x ∂μ) z = _ at hder
  have hd := congrArg (fun φ : ℂ → ℂ ↦ iteratedDeriv k φ z) (funext hEq)
  have hpair := sobolev_indicator_integral μ U f.val u (j f) (fun x ↦ (l x : ℂ) ^ k) (c z) hu hcut
  exact ((hΛ u).2.trans hpair).trans (hder.symm.trans hd)

end

/-- Paper: Corollary 9.2.2.12(2), p. 418. A Mellin derivative evaluation in any
isotype extends from supported tests at the endpoints of the compact base.
Deviation: At the upper endpoint the condition is strict. At a distinct lower
endpoint the cutoff allows all orders. The modulation is onto as in §9.2.

Deviation: Corollary 9.2.2.12(2) asserts continuity at every boundary point in the printed range
on the supported analytic tensor space. We use the physical endpoint norm, with criterion $\Re
z<b$ or $2k+1<s$.
-/
theorem modulatedIntervalSobolev_cutoff_eval_endpoints_iff (_hms : Surjective m)
    (a b A s : ℝ) (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) (k : ℕ)
    (z : ℂ) (_hz : z.re ∈ ({a, b} : Set ℝ))
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let E := ModulatedIntervalSobolev m hm a b s
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    (∃ Λ : E →L[ℂ] ℂ, ∀ (f : ModulatedExponentialDecay m univ) (u : E),
      tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log A) → (u : G → ℂ) =ᵐ[μ] f.val →
        Λ u = iteratedDeriv k (fun w ↦ modulatedFourierMellin m univ hm μ f.val (c w)) z) ↔
      z.re < b ∨ 2 * (k : ℝ) + 1 < s := by
  intro μ E c
  constructor
  · rintro ⟨Λ, hΛ⟩
    exact modulatedDecay_endpoint_necessary m hm _hms a b A s _hab _hA _hs k z _hz χ _hχ Λ hΛ
  · intro h
    have hz : z.re ≤ b := by
      rcases (show z.re = a ∨ z.re = b by simpa only [mem_insert_iff, mem_singleton_iff] using _hz) with ha | hb
      · exact ha ▸ _hab
      · exact hb.le
    exact modulatedDecay_endpoint_sufficient m hm _hms a b A s _hs _hA k z hz χ _hχ h

/-- Paper: Theorem 9.2.2.13(1), p. 418. For compact bases and surjective module,
the support-restricted tests are dense in the indicator range.
Deviation: State the range as the fixed points of the cutoff on representatives.
A discrete modulation can have positive Haar mass at the cutoff itself. -/
theorem modulatedIntervalSobolev_cutoff_closure (_hms : Surjective m) (a b A s : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) :
    let μ := canonicalModulatedHaar m hm
    let E := ModulatedIntervalSobolev m hm a b s
    closure {u : E | ∃ f : ModulatedExponentialDecay m univ,
      tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log A) ∧
        (u : G → ℂ) =ᵐ[μ] f.val} =
      {u : E | (u : G → ℂ) =ᵐ[μ] ((logModule m) ⁻¹' Ici (-Real.log A)).indicator (u : G → ℂ)} :=
  by
  intro μ E
  exact modulatedDecay_cutoff m hm _hms (-Real.log A) (intervalSobolevDensity a b s)
    (continuous_intervalSobolevDensity' a b s)
    (intervalSobolevDensity_pos a b s)

-- TODO(paper-gap): Theorem 9.2.2.13(2) uses the unspecified analytic space of
-- Definition 9.2.2.3. The cited Lemma 9.2.2.10(1) treats only even degrees.
-- TODO(paper-gap): Theorem 9.2.2.13(3) gives the unrestricted tensor space as
-- right target even though the induced Mellin map on that arrow has one-sided source.

end ModulatedInterval

/-- On the closed base interval, each admissible Mellin derivative is represented
by one continuous functional on the weighted scalar space. Its action agrees
with the Mellin derivative on profiles from every larger open strip. -/
theorem scalarIntervalSobolev_admitted_mellin_functional (a b s : ℝ) (hs : 0 ≤ s)
    (z : ℂ) (k : ℕ) (hz : z.re ∈ Ioo a b ∨ z.re ∈ Icc a b ∧ 2 * (k : ℝ) + 1 < s) :
    let E := CompactIntervalSobolev volume id a b s
    ∃ Λ : StrongDual ℂ E, ∀ (I : Set ℝ), IsOpen I → z.re ∈ I →
      ∀ (p : PositiveRealExponentialDecay I) (x : E), (x : ℝ → ℂ) =ᵐ[volume] p.val →
        Λ x = iteratedDeriv k (mellin (fun t ↦ p.val (Real.log t))) z := by
  intro E
  have hintegral : ∃ Λ : StrongDual ℂ E, ∀ x : E,
      Λ x = ∫ t : ℝ, x t * (t : ℂ)^k * Complex.exp (z * (t : ℂ)) := by
    rcases hz with h | ⟨h,hk⟩
    · obtain ⟨Λ,hΛ⟩ := scalarIntervalSobolev_eval_interior a b s hs z h k
      exact ⟨Λ, fun x ↦ (hΛ x).2⟩
    · obtain ⟨Λ,hΛ⟩ := intervalSobolev_boundary_moment_functional a b s k z h hk MeasurableSet.univ
      refine ⟨Λ, fun x ↦ ?_⟩
      simpa only [Set.indicator_univ, mul_assoc] using (hΛ x).2
  obtain ⟨Λ,hΛ⟩ := hintegral
  refine ⟨Λ, fun I hI hz p x hx ↦ ?_⟩
  rw [hΛ, scalarDecay_mellin_deriv hI p k hz, mellin_logProfile (fun t : ℝ ↦ (t : ℂ)^k * p.val t)]
  apply integral_congr_ae
  filter_upwards [hx] with t ht
  rw [ht]
  ring

end RiemannMasullo
