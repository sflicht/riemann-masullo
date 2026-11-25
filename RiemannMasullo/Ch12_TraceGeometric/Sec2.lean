module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.Extension
public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Lebesgue differentiation along the diagonal

Masullo, §12.2, pp. 504–513. Completed-measure measurability is expressed as
`AEMeasurable` on the Borel measure space. Kernel smoothenings use the extension
by zero from §12.1, with regularity hypotheses where the paper uses their values.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped CompactlySupported ENNReal Pointwise

namespace RiemannMasullo

local instance instQuotientMeasurableSpaceSec2 {G : Type*} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : MeasurableSpace (G ⧸ H) := borel _

section Indentations

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
  (H : Subgroup G)

local notation "Q" => G ⧸ H
local notation "π" => QuotientGroup.mk' H

/-- Paper: Definition 12.2.1.3, p. 506. An indentation is a continuous nonnegative real
function whose support meets the saturation of every compact set in a compact set, and
whose integral over each subgroup fibre converges and equals one. -/
def IsIndentation (μH : Measure H) (b : G → ℝ) : Prop :=
  Continuous b ∧ (∀ x, 0 ≤ b x) ∧
    (∀ K : Set G, IsCompact K → IsCompact (tsupport b ∩ π ⁻¹' (π '' K))) ∧
    ∀ x : G, Integrable (fun h : H ↦ b ((h : G)⁻¹ * x)) μH ∧
      (∫ h : H, b ((h : G)⁻¹ * x) ∂μH) = 1

/-- Paper: Definition 12.2.1.3, p. 506. For the trivial subgroup with unit counting
measure, the indentations are exactly the constant one function. -/
theorem isIndentation_bot_iff (b : G → ℝ) :
    IsIndentation (⊥ : Subgroup G) Measure.count b ↔ b = fun _ ↦ 1 := by
  have hcount := Subsingleton.count_eq_dirac (1 : (⊥ : Subgroup G))
  constructor
  · intro hb
    funext x
    simpa [hcount] using (hb.2.2.2 x).2
  · rintro rfl
    refine ⟨continuous_const, fun _ ↦ zero_le_one, ?_, ?_⟩
    · intro K hK
      have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup G)) :=
        (QuotientGroup.quotientBot (G := G)).symm.injective
      rw [Set.preimage_image_eq _ hinj]
      exact hK.inter_left (isClosed_tsupport _)
    · intro x
      simp [hcount]

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G]
  (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure]

/-- Fibre integrals of a compactly supported real function are the values of its
pushforward to the quotient. -/
private theorem exists_indentation_fibre {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] (H : Subgroup G) [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G]
    (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure] (f : C_c(G, ℝ)) (x : G) :
    Integrable (fun h : H ↦ f ((h : G)⁻¹ * x)) μH ∧
      (∫ h : H, f ((h : G)⁻¹ * x) ∂μH) =
        (TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH f
          (QuotientGroup.mk' H x) := by
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace H :=
    hH.isClosedEmbedding_subtypeVal.isInducing.pseudoMetrizableSpace
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  have hinv (h : H) : e.pullback f x h⁻¹ = f ((h : G)⁻¹ * x) := by
    rw [e.pullback_def]
    simp [mul_comm]
  constructor
  · simpa only [hinv] using ((e.pullback f x).integrable (μ := μH)).comp_inv
  · change _ = e.pushforward μH f (QuotientGroup.mk' H x)
    rw [e.pushforward_apply_apply]
    simpa only [hinv] using (integral_inv_eq_self (e.pullback f x) μH)

include hH in
/-- Paper: Lemma 12.2.1.1(1)–(3), p. 504. Every closed subgroup with a choice of
Haar measure has an indentation. The fibre integral is identically one on the group,
which entails continuity and invariance. -/
theorem exists_indentation : ∃ b : G → ℝ, IsIndentation H μH b := by
  classical
  have : IsClosed (H : Set G) := hH
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  have hπc : Continuous π := continuous_quot_mk
  have hπ (x : G) (h : H) : π ((h : G)⁻¹ * x) = π x := by
    have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    rw [map_mul, map_inv, h1, inv_one, one_mul]
  have hbump : ∀ q : Q, ∃ g : C_c(G, ℝ), 0 ≤ (g : G → ℝ) ∧ g q.out ≠ 0 := by
    intro q
    obtain ⟨g, hgc, hg0, hgx⟩ := exists_continuous_nonneg_pos (q.out)
    exact ⟨⟨g, hgc⟩, hg0, hgx⟩
  choose g hg0 hgx using hbump
  let U : Q → Set Q := fun q ↦ π '' Function.support (g q)
  have hUo : ∀ q, IsOpen (U q) := fun q ↦
    QuotientGroup.isOpenMap_coe _ (g q).continuous.isOpen_support
  have hUc : (univ : Set Q) ⊆ ⋃ q, U q := fun q _ ↦
    mem_iUnion.2 ⟨q, q.out, hgx q, by simp⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hUo hUc
  let P : Q → Q → ℝ := fun q y ↦ e.pushforward μH (g q) y
  let φ : G → ℝ := fun x ↦ ∑ᶠ q, ρ q (π x) * g q x
  let A : G → ℝ := fun x ↦ ∑ᶠ q, ρ q (π x) * P q (π x)
  have hφc : Continuous φ := by
    refine continuous_finsum (fun q ↦ ((ρ q).continuous.comp hπc).mul (g q).continuous) ?_
    exact (ρ.locallyFinite.preimage_continuous hπc).subset fun q ↦
      Function.support_mul_subset_left _ _
  have hAc : Continuous A := by
    have := ρ.continuous_finsum_smul (g := P) (fun q x _ ↦ (e.pushforward μH (g q)).continuous.continuousAt)
    exact this.comp hπc
  have hφ0 : ∀ x, 0 ≤ φ x := fun x ↦
    finsum_nonneg fun q ↦ mul_nonneg (ρ.nonneg _ _) (hg0 q x)
  -- the fibre integral of φ is A
  have hfib : ∀ x, Integrable (fun h : H ↦ φ ((h : G)⁻¹ * x)) μH ∧
      (∫ h : H, φ ((h : G)⁻¹ * x) ∂μH) = A x := by
    intro x
    set S := (ρ.locallyFinite.point_finite (π x)).toFinset
    have hS (y : G) (hy : π y = π x) (F : Q → ℝ) :
        (∑ᶠ q, ρ q (π y) * F q) = ∑ q ∈ S, ρ q (π x) * F q := by
      rw [hy]
      refine finsum_eq_sum_of_support_subset _ fun q hq ↦ ?_
      simp only [S, Set.Finite.coe_toFinset, mem_ofPred_eq]
      exact left_ne_zero_of_mul hq
    have hφS (h : H) : φ ((h : G)⁻¹ * x) = ∑ q ∈ S, ρ q (π x) * g q ((h : G)⁻¹ * x) :=
      hS _ (hπ x h) fun q ↦ g q ((h : G)⁻¹ * x)
    simp only [hφS]
    refine ⟨integrable_finsetSum _ fun q _ ↦
      ((exists_indentation_fibre H hH μH (g q) x).1.const_mul _), ?_⟩
    rw [integral_finsetSum _ fun q _ ↦
      ((exists_indentation_fibre H hH μH (g q) x).1.const_mul _)]
    simp only [integral_const_mul, (exists_indentation_fibre H hH μH (g _) x).2]
    exact (hS x rfl fun q ↦ P q (π x)).symm
  have hP0 : ∀ q x, 0 ≤ P q (π x) := fun q x ↦ by
    show 0 ≤ e.pushforward μH (g q) (π x)
    rw [← (exists_indentation_fibre H hH μH (g q) x).2]
    exact integral_nonneg fun h ↦ hg0 q _
  have hApos : ∀ x, 0 < A x := by
    intro x
    obtain ⟨q, hq⟩ := ρ.exists_pos (mem_univ (π x))
    obtain ⟨y, hy, hyx⟩ := hρ q (subset_tsupport _ hq.ne')
    have hyx' : x * y⁻¹ ∈ H := by
      have := QuotientGroup.eq.mp hyx
      simpa [mul_comm] using this
    have hP : 0 < P q (π x) := by
      obtain ⟨hint, heq⟩ := exists_indentation_fibre H hH μH (g q) x
      show 0 < e.pushforward μH (g q) (π x)
      rw [← heq]
      refine integral_pos_of_integrable_nonneg_ne_zero (x := ⟨x * y⁻¹, hyx'⟩) ?_ hint
        (fun h ↦ hg0 q _) ?_
      · exact (g q).continuous.comp ((continuous_subtype_val.inv).mul continuous_const)
      · simpa using hy
    have hfin : (Function.support fun q ↦ ρ q (π x) * P q (π x)).Finite :=
      (ρ.locallyFinite.point_finite (π x)).subset fun q hq ↦ left_ne_zero_of_mul hq
    refine lt_of_lt_of_le (mul_pos hq hP) ?_
    exact single_le_finsum q hfin fun j ↦ mul_nonneg (ρ.nonneg _ _) (hP0 j x)
  let b : G → ℝ := fun x ↦ φ x / A x
  have hT : IsClosed (⋃ q, π ⁻¹' tsupport (ρ q) ∩ tsupport (g q)) :=
    ((ρ.locallyFinite_tsupport.preimage_continuous hπc).subset
      fun q ↦ inter_subset_left).isClosed_iUnion
      fun q ↦ ((isClosed_tsupport _).preimage hπc).inter (isClosed_tsupport _)
  have hsupp : tsupport b ⊆ ⋃ q, π ⁻¹' tsupport (ρ q) ∩ tsupport (g q) := by
    refine closure_minimal (fun x hx ↦ ?_) hT
    have hφx : φ x ≠ 0 := fun h ↦ hx (by simp [b, h])
    by_contra hnot
    apply hφx
    have hzero : ∀ q, ρ q (π x) * g q x = 0 := by
      intro q
      by_contra hq
      exact hnot (mem_iUnion.2 ⟨q, subset_tsupport _ (left_ne_zero_of_mul hq),
        subset_tsupport _ (right_ne_zero_of_mul hq)⟩)
    simp only [φ, hzero, finsum_zero]
  refine ⟨b, hφc.div hAc fun x ↦ (hApos x).ne', fun x ↦ div_nonneg (hφ0 x) (hApos x).le,
    ?_, ?_⟩
  · intro K hK
    have hL : IsCompact (π '' K) := hK.image hπc
    have hF := ρ.locallyFinite_tsupport.finite_nonempty_inter_compact hL
    refine (hF.isCompact_biUnion fun q _ ↦ (g q).hasCompactSupport).of_isClosed_subset
      ((isClosed_tsupport _).inter (hL.isClosed.preimage hπc)) ?_
    rintro x ⟨hx, hxK⟩
    obtain ⟨q, hq1, hq2⟩ := mem_iUnion.1 (hsupp hx)
    exact mem_biUnion ⟨π x, hq1, hxK⟩ hq2
  · intro x
    have hAx (h : H) : A ((h : G)⁻¹ * x) = A x := by simp only [A, hπ]
    obtain ⟨hint, heq⟩ := hfib x
    simp only [b, hAx]
    refine ⟨hint.div_const _, ?_⟩
    rw [integral_div, heq, div_self (hApos x).ne']

/-- Paper: (12.2.1.8), p. 506. Lift a quotient function by pulling it back and
multiplying by the indentation. -/
def indentationLift (b : G → ℝ) (u : Q → ℂ) (x : G) : ℂ :=
  (b x : ℂ) * u (π x)

include hH in
/-- Paper: Lemma 12.2.1.1, p. 505. The lift of a continuous quotient function is
integrable on every subgroup fibre and its fibre integral recovers the quotient value. -/
theorem integral_indentationLift {b : G → ℝ} (hb : IsIndentation H μH b)
    (u : C(Q, ℂ)) (x : G) :
    Integrable (fun h : H ↦ indentationLift H b u ((h : G)⁻¹ * x)) μH ∧
      (∫ h : H, indentationLift H b u ((h : G)⁻¹ * x) ∂μH) = u (π x) := by
  obtain ⟨hi, he⟩ := hb.2.2.2 x
  have hcoset (h : H) : π ((h : G)⁻¹ * x) = π x := by
    have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    rw [map_mul, map_inv, h1, inv_one, one_mul]
  simp only [indentationLift, hcoset]
  refine ⟨hi.ofReal.mul_const _, ?_⟩
  rw [integral_mul_const, integral_complex_ofReal, he, Complex.ofReal_one, one_mul]

/-- Paper: (12.2.1.5), p. 505. Fibre integration of a compactly supported test
commutes with complex scalar multiplication. -/
theorem indentationAverage_smul (c : ℂ) (f : C_c(G, ℂ)) :
    (TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH (c • f) =
      c • (TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH f := by
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  apply DFunLike.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
  change e.pushforward μH (c • f) (π x) = c • e.pushforward μH f (π x)
  rw [e.pushforward_apply_apply, e.pushforward_apply_apply]
  simp only [TopologicalGroup.IsSES.pullback_def, CompactlySupportedContinuousMap.smul_apply,
    integral_smul]

/-- Paper: (12.2.1.5), p. 505. The quotient average of a compactly supported
continuous function integrates over the subgroup fibres and is a complex-linear
map into compactly supported continuous functions. -/
def indentationAverage : C_c(G, ℂ) →ₗ[ℂ] C_c(Q, ℂ) where
  toFun := (TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH
  map_add' := ((TopologicalGroup.IsSES.ofClosedSubgroup H hH).pushforward μH).map_add
  map_smul' := indentationAverage_smul H hH μH

/-- Paper: (12.2.1.5), p. 506. Evaluate the quotient average at the coset of any
representative by integrating its inverse subgroup translates. -/
theorem indentationAverage_apply (f : C_c(G, ℂ)) (x : G) :
    Integrable (fun h : H ↦ f ((h : G)⁻¹ * x)) μH ∧
      indentationAverage H hH μH f (π x) = ∫ h : H, f ((h : G)⁻¹ * x) ∂μH := by
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace H :=
    hH.isClosedEmbedding_subtypeVal.isInducing.pseudoMetrizableSpace
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  have hinv (h : H) : e.pullback f x h⁻¹ = f ((h : G)⁻¹ * x) := by
    rw [e.pullback_def]
    simp [mul_comm]
  constructor
  · simpa only [hinv] using ((e.pullback f x).integrable (μ := μH)).comp_inv
  · change e.pushforward μH f (π x) = _
    rw [e.pushforward_apply_apply]
    simpa only [hinv] using (integral_inv_eq_self (e.pullback f x) μH).symm

/-- Paper: (12.2.1.6), p. 506. A regular positive measure upstairs lifts a quotient
measure if its integrals on compactly supported continuous tests agree with the
quotient integrals of the fibre averages. -/
def IsIndentationMeasureLift (ν₀ : Measure Q) (μ₀ : Measure G) : Prop :=
  μ₀.Regular ∧
    ∀ f : C_c(G, ℂ), (∫ q, indentationAverage H hH μH f q ∂ν₀) = ∫ x, f x ∂μ₀

/-- Paper: (12.2.1.6), p. 506. Weil-normalized Haar measures give an instance of the
measure lift from the quotient. -/
theorem isIndentationMeasureLift_of_weil {μ : Measure G} [μ.IsHaarMeasure]
    {ν : Measure Q} (hν : IsWeilQuotientMeasure H μ μH ν) :
    IsIndentationMeasureLift H hH μH ν μ := by
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  refine ⟨inferInstance, fun f ↦ ?_⟩
  refine Eq.trans ?_ (hν.2.2 f.toContinuousMap f.hasCompactSupport).symm
  apply integral_congr_ae
  apply ae_of_all
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change _ = lcaCosetIntegral H μH f (QuotientGroup.mk x)
  rw [lcaCosetIntegral_mk H μH f x]
  · exact e.pushforward_apply_apply μH f x
  · exact (e.pullback f x).integrable

/-- Paper: Corollary 12.2.1.2(1), p. 506. Each positive Radon measure on the quotient
has a unique positive Radon lift satisfying the normalization on compact tests.
Deviation: Regularity of the lift is explicit, as in the proof. -/
theorem existsUnique_indentationMeasureLift (ν₀ : Measure Q) [ν₀.Regular] :
    ∃! μ₀ : Measure G, IsIndentationMeasureLift H hH μH ν₀ μ₀ := by
  let : BorelSpace Q := ⟨rfl⟩
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let L : C_c(G, ℝ) →ₚ[ℝ] ℝ :=
    ⟨{ toFun := fun f ↦ ∫ q, e.pushforward μH f q ∂ν₀
       map_add' := fun f g ↦ by
         rw [map_add]
         exact integral_add (e.pushforward μH f).integrable (e.pushforward μH g).integrable
       map_smul' := fun c f ↦ by
         rw [map_smul]
         exact integral_smul c (e.pushforward μH f) },
      fun f g h ↦ integral_mono (e.pushforward μH f).integrable
        (e.pushforward μH g).integrable (e.pushforward_mono μH h)⟩
  let μ := RealRMK.rieszMeasure L
  have hreal (f : C_c(G, ℝ)) :
      (∫ x, f x ∂μ) = ∫ q, e.pushforward μH f q ∂ν₀ :=
    RealRMK.integral_rieszMeasure L f
  have hcomplex (f : C_c(G, ℂ)) :
      (∫ x, f x ∂μ) = ∫ q, indentationAverage H hH μH f q ∂ν₀ := by
    let fr : C_c(G, ℝ) := ⟨⟨fun x ↦ (f x).re, Complex.continuous_re.comp f.continuous⟩,
      f.hasCompactSupport.comp_left (g := Complex.re) (by simp)⟩
    let fi : C_c(G, ℝ) := ⟨⟨fun x ↦ (f x).im, Complex.continuous_im.comp f.continuous⟩,
      f.hasCompactSupport.comp_left (g := Complex.im) (by simp)⟩
    apply Complex.ext
    · change RCLike.re (∫ x, f x ∂μ) = RCLike.re (∫ q, indentationAverage H hH μH f q ∂ν₀)
      rw [← integral_re f.integrable, ← integral_re (indentationAverage H hH μH f).integrable]
      change (∫ x, fr x ∂μ) = ∫ q, (indentationAverage H hH μH f q).re ∂ν₀
      rw [hreal fr]
      apply integral_congr_ae
      apply ae_of_all
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
      change e.pushforward μH fr (π x) = (e.pushforward μH f (π x)).re
      rw [e.pushforward_apply_apply, e.pushforward_apply_apply]
      simpa only [TopologicalGroup.IsSES.pullback_def, fr, CompactlySupportedContinuousMap.coe_mk,
        ContinuousMap.coe_mk, RCLike.re_eq_complex_re] using
        (integral_re ((e.pullback f x).integrable (μ := μH)))
    · change RCLike.im (∫ x, f x ∂μ) = RCLike.im (∫ q, indentationAverage H hH μH f q ∂ν₀)
      rw [← integral_im f.integrable, ← integral_im (indentationAverage H hH μH f).integrable]
      change (∫ x, fi x ∂μ) = ∫ q, (indentationAverage H hH μH f q).im ∂ν₀
      rw [hreal fi]
      apply integral_congr_ae
      apply ae_of_all
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
      change e.pushforward μH fi (π x) = (e.pushforward μH f (π x)).im
      rw [e.pushforward_apply_apply, e.pushforward_apply_apply]
      simpa only [TopologicalGroup.IsSES.pullback_def, fi, CompactlySupportedContinuousMap.coe_mk,
        ContinuousMap.coe_mk, RCLike.im_eq_complex_im] using
        (integral_im ((e.pullback f x).integrable (μ := μH)))
  refine ⟨μ, ⟨inferInstance, fun f ↦ (hcomplex f).symm⟩, ?_⟩
  intro μ' hμ'
  let : μ'.Regular := hμ'.1
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let F : C_c(G, ℂ) := ⟨⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩,
    f.hasCompactSupport.comp_left Complex.ofReal_zero⟩
  apply Complex.ofReal_injective
  simpa only [F, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk,
    integral_complex_ofReal] using (hμ'.2 F).symm.trans (hcomplex F).symm

/-- Paper: Corollary 12.2.1.2(1), p. 506. The lifted measure is invariant under
left translation by every subgroup element. -/
theorem map_mul_indentationMeasureLift {ν₀ : Measure Q} [ν₀.Regular] {μ₀ : Measure G}
    (hμ₀ : IsIndentationMeasureLift H hH μH ν₀ μ₀) (h : H) :
    μ₀.map (fun x : G ↦ (h : G) * x) = μ₀ := by
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let L := Homeomorph.mulLeft (h : G)
  let : μ₀.Regular := hμ₀.1
  let : (μ₀.map L).Regular := Measure.Regular.map L
  change μ₀.map L = μ₀
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let F : C_c(G, ℂ) := ⟨⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩,
    f.hasCompactSupport.comp_left Complex.ofReal_zero⟩
  let Fh := F.comp L.toCocompactMap
  have havg (q : Q) : indentationAverage H hH μH Fh q = indentationAverage H hH μH F q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change e.pushforward μH Fh (π x) = e.pushforward μH F (π x)
    rw [e.pushforward_apply_apply, e.pushforward_apply_apply]
    change (∫ k : H, F ((h : G) * (x * (k : G))) ∂μH) = ∫ k : H, F (x * (k : G)) ∂μH
    simpa only [Subgroup.coe_mul, mul_left_comm (h : G) x] using
      (integral_mul_left_eq_self (μ := μH) (fun k : H ↦ F (x * (k : G))) h)
  have hint := (hμ₀.2 Fh).symm.trans ((integral_congr_ae (ae_of_all ν₀ havg)).trans (hμ₀.2 F))
  refine (integral_map (μ := μ₀) (f := fun x ↦ f x) L.continuous.measurable.aemeasurable
    (map_continuous f).aestronglyMeasurable).trans ?_
  apply Complex.ofReal_injective
  simpa only [integral_complex_ofReal] using
    (show (∫ x, (f (L x) : ℂ) ∂μ₀) = ∫ x, (f x : ℂ) ∂μ₀ from hint)

include hH in
omit [T2Space G] [BorelSpace G] [μH.IsHaarMeasure] in
private theorem exists_indentationLiftL1_compact {b : G → ℝ} (hb : IsIndentation H μH b)
    {K : Set Q} (hK : IsCompact K) : IsCompact (tsupport b ∩ π ⁻¹' K) := by
  let : IsClosed (H : Set G) := hH
  let E := CompactExhaustion.choice G
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n ↦ π '' interior (E n))
    (fun _ ↦ QuotientGroup.isOpenMap_coe _ isOpen_interior) (by
      rintro q -
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨n, hx⟩ := E.exists_mem x
      exact mem_iUnion.mpr ⟨n + 1, x, E.subset_interior_succ _ hx, rfl⟩)
    (Monotone.directed_le fun _ _ h ↦ image_mono (interior_mono (E.subset h)))
  refine (hb.2.2.1 (E n) (E.isCompact n)).of_isClosed_subset
    ((isClosed_tsupport _).inter (hK.isClosed.preimage QuotientGroup.continuous_mk)) ?_
  exact inter_subset_inter_right _ (preimage_mono (hn.trans (image_mono interior_subset)))

include hH in
omit [T2Space G] [BorelSpace G] [μH.IsHaarMeasure] in
/-- The support of an indentation is compact above every compact subset of the quotient. -/
theorem IsIndentation.isCompact_tsupport_inter_preimage {b : G → ℝ}
    (hb : IsIndentation H μH b) {K : Set Q} (hK : IsCompact K) :
    IsCompact (tsupport b ∩ π ⁻¹' K) :=
  exists_indentationLiftL1_compact H hH μH hb hK

private theorem exists_indentationLiftL1_test {b : G → ℝ} (hb : IsIndentation H μH b)
    (f : C_c(Q, ℂ)) : ∃ F : C_c(G, ℂ), (⇑F = indentationLift H b f) ∧
      indentationAverage H hH μH F = f := by
  have hF : HasCompactSupport (indentationLift H b f) := by
    refine exists_compact_iff_hasCompactSupport.mp ⟨_,
      exists_indentationLiftL1_compact H hH μH hb f.hasCompactSupport, ?_⟩
    intro x hx
    by_cases hb' : x ∈ tsupport b
    · have hx' : π x ∉ tsupport f := fun h ↦ hx ⟨hb', h⟩
      exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hx')
    · simp [indentationLift, image_eq_zero_of_notMem_tsupport hb']
  let F : C_c(G, ℂ) := ⟨⟨indentationLift H b f,
    (Complex.continuous_ofReal.comp hb.1).mul (f.continuous.comp QuotientGroup.continuous_mk)⟩, hF⟩
  refine ⟨F, rfl, ?_⟩
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  let e := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  change e.pushforward μH F (π x) = f (π x)
  rw [e.pushforward_apply_apply]
  change (∫ h : H, (b (x * h) : ℂ) * f (π (x * h)) ∂μH) = _
  have hf (h : H) : π (x * h) = π x := by simp
  simp_rw [hf]
  rw [integral_mul_const, integral_complex_ofReal]
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  have hb1 : (∫ h : H, b (x * h) ∂μH) = 1 := by
    rw [← integral_inv_eq_self]
    simpa only [Subgroup.coe_inv, mul_comm x] using (hb.2.2.2 x).2
  rw [hb1, Complex.ofReal_one, one_mul]

private theorem exists_indentationLiftL1_measure {ν₀ : Measure Q} [ν₀.Regular] {μ₀ : Measure G}
    (hμ₀ : IsIndentationMeasureLift H hH μH ν₀ μ₀) {b : G → ℝ} (hb : IsIndentation H μH b) :
    MeasurePreserving π (μ₀.withDensity fun x ↦ ENNReal.ofReal (b x)) ν₀ := by
  let : IsClosed (H : Set G) := hH
  let : μ₀.Regular := hμ₀.1
  have : BorelSpace Q := ⟨rfl⟩
  let w (x : G) := (b x).toNNReal
  have hw : Measurable w := hb.1.measurable.real_toNNReal
  let m := μ₀.withDensity fun x ↦ (w x : ℝ≥0∞)
  have hπ : Measurable π := QuotientGroup.continuous_mk.measurable
  have hs : ∀ᵐ x ∂m, x ∈ tsupport b := by
    apply (ae_withDensity_iff hw.coe_nnreal_ennreal).2
    filter_upwards with x hx
    apply subset_tsupport b
    intro h
    exact hx (by simp [w, h])
  have : IsFiniteMeasureOnCompacts (m.map π) := ⟨fun {K} hK ↦ by
    rw [Measure.map_apply hπ hK.measurableSet, ← Measure.measure_inter_eq_of_ae hs]
    have hC := exists_indentationLiftL1_compact H hH μH hb hK
    change μ₀.withDensity (fun x ↦ (w x : ℝ≥0∞)) _ < ∞
    rw [withDensity_apply _ hC.measurableSet]
    have hi := (hb.1.continuousOn.integrableOn_compact (μ := μ₀) hC).hasFiniteIntegral
    simpa only [hasFiniteIntegral_def, Real.eNorm_of_nonneg, hb.2.1, w, ENNReal.ofReal] using hi⟩
  refine ⟨hπ, ?_⟩
  change m.map π = ν₀
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let f' : C_c(Q, ℂ) := ⟨⟨fun q ↦ (f q : ℂ), Complex.continuous_ofReal.comp f.continuous⟩,
    f.hasCompactSupport.comp_left Complex.ofReal_zero⟩
  obtain ⟨F, hF, havg⟩ := exists_indentationLiftL1_test H hH μH hb f'
  have hi := (hμ₀.2 F).symm
  rw [havg] at hi
  rw [integral_map (f := (⇑f : Q → ℝ)) hπ.aemeasurable (map_continuous f).aestronglyMeasurable]
  change (∫ x, f (π x) ∂μ₀.withDensity (fun x ↦ (w x : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul hw]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  convert hi using 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  rw [hF]
  change (((w x : ℝ) * f (π x) : ℝ) : ℂ) = (b x : ℂ) * (f (π x) : ℂ)
  rw [Complex.ofReal_mul, show (w x : ℝ) = b x from Real.coe_toNNReal _ (hb.2.1 x)]

/-- Paper: Corollary 12.2.1.2(2), p. 506. Multiplying the pulled-back L¹ representative
by any indentation defines an isometric continuous linear right inverse to the L¹ extension. -/
theorem exists_indentationLiftL1 {ν₀ : Measure Q} [ν₀.Regular] {μ₀ : Measure G}
    (hμ₀ : IsIndentationMeasureLift H hH μH ν₀ μ₀)
    (A : Lp ℂ 1 μ₀ →L[ℂ] Lp ℂ 1 ν₀)
    (hA : ∀ (f : C_c(G, ℂ)) (F : Lp ℂ 1 μ₀), (F : G → ℂ) =ᵐ[μ₀] f →
      (A F : Q → ℂ) =ᵐ[ν₀] indentationAverage H hH μH f)
    {b : G → ℝ} (hb : IsIndentation H μH b) :
    ∃ L : Lp ℂ 1 ν₀ →L[ℂ] Lp ℂ 1 μ₀,
      Isometry L ∧ Function.RightInverse L A ∧
        ∀ u : Lp ℂ 1 ν₀, (L u : G → ℂ) =ᵐ[μ₀] indentationLift H b u := by
  have : IsClosed (H : Set G) := hH
  have : BorelSpace Q := ⟨rfl⟩
  let w (x : G) := (b x).toNNReal
  have hw : Measurable w := hb.1.measurable.real_toNNReal
  let m := μ₀.withDensity fun x ↦ (w x : ℝ≥0∞)
  have hπ : MeasurePreserving π m ν₀ := exists_indentationLiftL1_measure H hH μH hμ₀ hb
  let P : Lp ℂ 1 ν₀ →ₗᵢ[ℂ] Lp ℂ 1 m := Lp.compMeasurePreservingₗᵢ ℂ π hπ
  let B := withDensitySMulLI (E := ℂ) μ₀ hw
  have hrep (u : Lp ℂ 1 ν₀) (v : Q → ℂ) (hv : ⇑u =ᵐ[ν₀] v) :
      ⇑(B (P u)) =ᵐ[μ₀] indentationLift H b v := by
    have he : ⇑(P u) =ᵐ[m] v ∘ π := (Lp.coeFn_compMeasurePreserving u hπ).trans
      (hπ.quasiMeasurePreserving.ae_eq_comp hv)
    have hw' : ⇑(B (P u)) =ᵐ[μ₀] fun x ↦ w x • P u x :=
      (memL1_smul_of_L1_withDensity hw (P u)).coeFn_toLp
    filter_upwards [hw', (ae_withDensity_iff hw.coe_nnreal_ennreal).1 he] with x hx he'
    rw [hx, NNReal.smul_def, Complex.real_smul, show (w x : ℝ) = b x from
      Real.coe_toNNReal _ (hb.2.1 x)]
    by_cases hz : w x = 0
    · have hbz : b x = 0 := (Real.coe_toNNReal _ (hb.2.1 x)).symm.trans (congrArg NNReal.toReal hz)
      simp [indentationLift, hbz]
    · rw [he' (by simpa using hz)]
      rfl
  let L : Lp ℂ 1 ν₀ →ₗᵢ[ℂ] Lp ℂ 1 μ₀ := {
    toFun := fun u ↦ B (P u)
    map_add' := by intro u v; rw [map_add, map_add]
    map_smul' := by
      intro c u
      apply Lp.ext
      refine (hrep (c • u) _ (Lp.coeFn_smul c u)).trans ?_
      filter_upwards [Lp.coeFn_smul c (B (P u)), hrep u u .rfl] with x hx hu
      rw [RingHom.id_apply, hx, Pi.smul_apply, hu]
      exact mul_left_comm _ _ _
    norm_map' := fun u ↦ (B.norm_map _).trans (P.norm_map u) }
  refine ⟨L.toContinuousLinearMap, L.isometry, ?_, fun u ↦ hrep u u .rfl⟩
  let D := {u : Lp ℂ 1 ν₀ | ∃ f : C_c(Q, ℂ), ⇑u =ᵐ[ν₀] f}
  have hd : Dense D := by
    intro u
    apply EMetric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    obtain ⟨f, hc, he, hf, hm⟩ := (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le
      ENNReal.one_ne_top hδ.ne'
    refine ⟨hm.toLp f, ⟨⟨⟨f, hf⟩, hc⟩, hm.coeFn_toLp⟩, ?_⟩
    rw [Lp.edist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub hm.coeFn_toLp)]
    exact he.trans_lt hδε
  have heq : (A ∘ L) = id := by
    apply Continuous.ext_on hd (A.continuous.comp L.continuous) continuous_id
    rintro u ⟨f, huf⟩
    obtain ⟨F, hF, havg⟩ := exists_indentationLiftL1_test H hH μH hb f
    apply Lp.ext
    have hLF : ⇑(L u) =ᵐ[μ₀] F := hF ▸ hrep u f huf
    exact (hA F (L u) hLF).trans (havg ▸ huf.symm)
  exact fun u ↦ congrFun heq u

include hH in
/-- Fibre averaging of a compactly supported test does not increase the L¹ norm. -/
private theorem exists_indentationAverageL1_norm {ν₀ : Measure Q} [ν₀.Regular] {μ₀ : Measure G}
    (hμ₀ : IsIndentationMeasureLift H hH μH ν₀ μ₀) (f : C_c(G, ℂ)) :
    ∫ q, ‖indentationAverage H hH μH f q‖ ∂ν₀ ≤ ∫ x, ‖f x‖ ∂μ₀ := by
  have : BorelSpace Q := ⟨rfl⟩
  let : μ₀.Regular := hμ₀.1
  let fn : C_c(G, ℂ) := ⟨⟨fun x ↦ (‖f x‖ : ℂ), Complex.continuous_ofReal.comp f.continuous.norm⟩,
    f.hasCompactSupport.comp_left (g := fun z : ℂ ↦ (‖z‖ : ℂ)) (by simp)⟩
  have hint := hμ₀.2 fn
  have hpt (q : Q) : ‖indentationAverage H hH μH f q‖ ≤ (indentationAverage H hH μH fn q).re := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨-, h1⟩ := indentationAverage_apply H hH μH f x
    obtain ⟨-, h2⟩ := indentationAverage_apply H hH μH fn x
    change ‖indentationAverage H hH μH f (π x)‖ ≤ (indentationAverage H hH μH fn (π x)).re
    rw [h1, h2]
    change _ ≤ (∫ h : H, ((‖f ((h : G)⁻¹ * x)‖ : ℝ) : ℂ) ∂μH).re
    rw [integral_complex_ofReal, Complex.ofReal_re]
    exact norm_integral_le_integral_norm _
  calc ∫ q, ‖indentationAverage H hH μH f q‖ ∂ν₀
      ≤ ∫ q, (indentationAverage H hH μH fn q).re ∂ν₀ :=
        integral_mono (indentationAverage H hH μH f).integrable.norm
          (indentationAverage H hH μH fn).integrable.re hpt
    _ = (∫ q, indentationAverage H hH μH fn q ∂ν₀).re :=
        integral_re (indentationAverage H hH μH fn).integrable
    _ = (∫ x, fn x ∂μ₀).re := by rw [hint]
    _ = ∫ x, ‖f x‖ ∂μ₀ := by
        refine (show (∫ x, fn x ∂μ₀).re = ∫ x, (fn x).re ∂μ₀ from
          (integral_re fn.integrable).symm).trans ?_
        rfl

/-- Paper: Corollary 12.2.1.2(2), p. 506. Fibre integration extends to a surjective
continuous complex-linear map of L¹ spaces, agreeing with the original map on compact tests. -/
theorem exists_indentationAverageL1 {ν₀ : Measure Q} [ν₀.Regular] {μ₀ : Measure G}
    (hμ₀ : IsIndentationMeasureLift H hH μH ν₀ μ₀) :
    ∃ A : Lp ℂ 1 μ₀ →L[ℂ] Lp ℂ 1 ν₀,
      Function.Surjective A ∧
        ∀ (f : C_c(G, ℂ)) (F : Lp ℂ 1 μ₀), (F : G → ℂ) =ᵐ[μ₀] f →
          (A F : Q → ℂ) =ᵐ[ν₀] indentationAverage H hH μH f := by
  have : BorelSpace Q := ⟨rfl⟩
  let : μ₀.Regular := hμ₀.1
  let S : C_c(G, ℂ) →ₗ[ℂ] Lp ℂ 1 μ₀ :=
    { toFun := fun f ↦ (f.integrable (μ := μ₀)).toL1 f
      map_add' := fun f g ↦ Integrable.toL1_add _ _ f.integrable g.integrable
      map_smul' := fun c f ↦ Integrable.toL1_smul _ f.integrable c }
  let T : C_c(G, ℂ) →ₗ[ℂ] Lp ℂ 1 ν₀ :=
    { toFun := fun f ↦ ((indentationAverage H hH μH f).integrable (μ := ν₀)).toL1 _
      map_add' := fun f g ↦ by
        simp only [map_add]
        exact Integrable.toL1_add _ _ (indentationAverage H hH μH f).integrable
          (indentationAverage H hH μH g).integrable
      map_smul' := fun c f ↦ by
        simp only [map_smul]
        exact Integrable.toL1_smul _ (indentationAverage H hH μH f).integrable c }
  have hS (f : C_c(G, ℂ)) : ‖S f‖ = ∫ x, ‖f x‖ ∂μ₀ :=
    L1.norm_of_fun_eq_integral_norm f.integrable
  have hT (f : C_c(G, ℂ)) : ‖T f‖ = ∫ q, ‖indentationAverage H hH μH f q‖ ∂ν₀ :=
    L1.norm_of_fun_eq_integral_norm (indentationAverage H hH μH f).integrable
  have hle (f : C_c(G, ℂ)) : ‖T f‖ ≤ ‖S f‖ := by
    rw [hS, hT]
    exact exists_indentationAverageL1_norm H hH μH hμ₀ f
  have hker : LinearMap.ker S ≤ LinearMap.ker T := fun f hf ↦ by
    rw [LinearMap.mem_ker] at hf ⊢
    exact norm_le_zero_iff.mp ((hle f).trans (by rw [hf, norm_zero]))
  let A₀ : LinearMap.range S →ₗ[ℂ] Lp ℂ 1 ν₀ :=
    ((LinearMap.ker S).liftQ T hker).comp S.quotKerEquivRange.symm.toLinearMap
  have hA₀ (f : C_c(G, ℂ)) : A₀ ⟨S f, f, rfl⟩ = T f := by
    have : S.quotKerEquivRange.symm ⟨S f, f, rfl⟩ = (LinearMap.ker S).mkQ f :=
      S.quotKerEquivRange.symm_apply_eq.mpr rfl
    simp only [A₀, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    exact Submodule.liftQ_apply _ _ _
  have hbound (v : LinearMap.range S) : ‖A₀ v‖ ≤ 1 * ‖v‖ := by
    obtain ⟨_, f, rfl⟩ := v
    rw [hA₀, one_mul]
    exact hle f
  let A₀c : LinearMap.range S →L[ℂ] Lp ℂ 1 ν₀ := A₀.mkContinuous 1 hbound
  have hD : Dense (LinearMap.range S : Set (Lp ℂ 1 μ₀)) := by
    rw [Metric.dense_iff]
    intro F r hr
    obtain ⟨v, hvs, hv, hvc, -⟩ := (Lp.memLp F).exists_hasCompactSupport_eLpNorm_sub_le
      ENNReal.one_ne_top (ENNReal.ofReal_pos.mpr (half_pos hr)).ne'
    let f : C_c(G, ℂ) := ⟨⟨v, hvc⟩, hvs⟩
    refine ⟨S f, ?_, f, rfl⟩
    rw [Metric.mem_ball, dist_comm, dist_eq_norm, Lp.norm_def]
    have hae : ⇑(F - S f) =ᵐ[μ₀] ⇑F - v :=
      (Lp.coeFn_sub F (S f)).trans ((Integrable.coeFn_toL1 f.integrable).mono fun x hx ↦ by
        change F x - (S f) x = F x - v x
        rw [show (S f) x = v x from hx])
    rw [eLpNorm_congr_ae hae]
    calc (eLpNorm (⇑F - v) 1 μ₀).toReal ≤ (ENNReal.ofReal (r / 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
      _ = r / 2 := ENNReal.toReal_ofReal (half_pos hr).le
      _ < r := half_lt_self hr
  have hdense : DenseRange (LinearMap.range S).subtypeL := hD.denseRange_val
  let A := A₀c.extend (LinearMap.range S).subtypeL
  have hAS (f : C_c(G, ℂ)) : A (S f) = T f := by
    have := A₀c.extend_eq hdense isUniformEmbedding_subtype_val.isUniformInducing ⟨S f, f, rfl⟩
    exact this.trans (hA₀ f)
  have hAF : ∀ (f : C_c(G, ℂ)) (F : Lp ℂ 1 μ₀), (F : G → ℂ) =ᵐ[μ₀] f →
      (A F : Q → ℂ) =ᵐ[ν₀] indentationAverage H hH μH f := by
    intro f F hF
    have hFS : F = S f := Lp.ext (hF.trans (Integrable.coeFn_toL1 f.integrable).symm)
    rw [hFS, hAS]
    exact Integrable.coeFn_toL1 (indentationAverage H hH μH f).integrable
  obtain ⟨b, hb⟩ := exists_indentation H hH μH
  obtain ⟨L, -, hL, -⟩ := exists_indentationLiftL1 H hH μH hμ₀ A hAF hb
  exact ⟨A, hL.surjective, hAF⟩


end Indentations

section ProperActions

variable {A X : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [T2Space A] [LocallyCompactSpace A] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MulAction A X] [ContinuousSMul A X] [ProperSMul A X]
  [IsCancelSMul A X] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace X] [BorelSpace X]

local notation "Ω" => MulAction.orbitRel.Quotient A X
local instance instOrbitQuotientMeasurableSpaceSec2 : MeasurableSpace Ω := borel _

-- Mathlib supplies the Hausdorff orbit quotient of a proper action, the open quotient map,
-- and second countability of the quotient of a second countable space.
/-- For a compactly supported continuous function, the orbit integrand has compact support,
its integral is invariant along orbits, and the orbit integral is continuous. -/
private theorem existsUnique_properActionQuotientMeasure_fibre (μA : Measure A)
    [μA.IsHaarMeasure] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E]
    (f : C_c(X, E)) :
    (∀ x : X, Continuous (fun a : A ↦ f (a • x)) ∧ HasCompactSupport (fun a : A ↦ f (a • x))) ∧
      (∀ (c : A) (x : X), ∫ a : A, f (a • c • x) ∂μA = ∫ a : A, f (a • x) ∂μA) ∧
      Continuous (fun x : X ↦ ∫ a : A, f (a • x) ∂μA) := by
  have hcomp (K : Set X) (hK : IsCompact K) :
      IsCompact {a : A | (a • K ∩ tsupport f).Nonempty} :=
    ProperSMul.isCompact_setOfPred_inter_nonempty hK f.hasCompactSupport
  have hvan (K : Set X) (y : X) (hy : y ∈ K) (a : A)
      (ha : a ∉ {a : A | (a • K ∩ tsupport f).Nonempty}) : f (a • y) = 0 := by
    by_contra hne
    exact ha ⟨a • y, smul_mem_smul_set hy, subset_tsupport _ hne⟩
  refine ⟨fun x ↦ ⟨f.continuous.comp (continuous_id.smul continuous_const),
    HasCompactSupport.intro (hcomp {x} isCompact_singleton) fun a ha ↦
      hvan {x} x (mem_singleton x) a ha⟩, fun c x ↦ ?_, ?_⟩
  · simp_rw [smul_smul]
    exact integral_mul_right_eq_self (fun a ↦ f (a • x)) c
  · rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x₀
    let C := {a : A | (a • K ∩ tsupport f).Nonempty}
    have hcont : Continuous (fun p : X × A ↦ f (p.2 • p.1)) :=
      f.continuous.comp (continuous_snd.smul continuous_fst)
    have hg := continuous_parametric_integral_of_continuous (μ := μA)
      (f := fun (y : X) (a : A) ↦ f (a • y)) hcont (hcomp K hK)
    refine hg.continuousAt.congr ?_
    filter_upwards [hKn] with y hy
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha ↦ hvan K y hy a ha

/-- A proper action admits a Bruhat function: a continuous nonnegative function whose support
meets the preimage of each compact set of orbits in a compact set, and whose integral along
every orbit is one. -/
private theorem existsUnique_properActionQuotientMeasure_bruhat (μA : Measure A)
    [μA.IsHaarMeasure] :
    ∃ b : X → ℝ, Continuous b ∧ (∀ x, 0 ≤ b x) ∧
      (∀ K : Set Ω, IsCompact K →
        IsCompact (tsupport b ∩ Quotient.mk (MulAction.orbitRel A X) ⁻¹' K)) ∧
      ∀ x : X, HasCompactSupport (fun a : A ↦ b (a • x)) ∧ ∫ a : A, b (a • x) ∂μA = 1 := by
  classical
  let π : X → Ω := Quotient.mk (MulAction.orbitRel A X)
  have hπq : IsOpenQuotientMap π := MulAction.isOpenQuotientMap_quotientMk
  have hπc : Continuous π := hπq.continuous
  have : LocallyCompactSpace Ω := hπq.locallyCompactSpace
  have : SigmaCompactSpace Ω := isSigmaCompact_univ_iff.mp (by
    rw [← hπq.surjective.range_eq]
    exact isSigmaCompact_range hπc)
  have hπ (a : A) (x : X) : π (a • x) = π x := Quotient.sound (MulAction.mem_orbit x a)
  have hbump : ∀ q : Ω, ∃ g : C_c(X, ℝ), 0 ≤ (g : X → ℝ) ∧ g q.out ≠ 0 := by
    intro q
    obtain ⟨g, hgc, hg0, hgx⟩ := exists_continuous_nonneg_pos (q.out)
    exact ⟨⟨g, hgc⟩, hg0, hgx⟩
  choose g hg0 hgx using hbump
  let U : Ω → Set Ω := fun q ↦ π '' Function.support (g q)
  have hUo (q : Ω) : IsOpen (U q) := hπq.isOpenMap _ (g q).continuous.isOpen_support
  have hUc : (univ : Set Ω) ⊆ ⋃ q, U q := fun q _ ↦
    mem_iUnion.2 ⟨q, q.out, hgx q, Quotient.out_eq q⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hUo hUc
  have hfib (q : Ω) := existsUnique_properActionQuotientMeasure_fibre μA (g q)
  let P : Ω → X → ℝ := fun q x ↦ ∫ a : A, g q (a • x) ∂μA
  let φ : X → ℝ := fun x ↦ ∑ᶠ q, ρ q (π x) * g q x
  let Av : X → ℝ := fun x ↦ ∑ᶠ q, ρ q (π x) * P q x
  have hlf : LocallyFinite fun q ↦ Function.support fun x ↦ ρ q (π x) :=
    ρ.locallyFinite.preimage_continuous hπc
  have hφc : Continuous φ :=
    continuous_finsum (fun q ↦ ((ρ q).continuous.comp hπc).mul (g q).continuous)
      (hlf.subset fun q ↦ Function.support_mul_subset_left _ _)
  have hAc : Continuous Av :=
    continuous_finsum (fun q ↦ ((ρ q).continuous.comp hπc).mul (hfib q).2.2)
      (hlf.subset fun q ↦ Function.support_mul_subset_left _ _)
  have hφ0 (x : X) : 0 ≤ φ x := finsum_nonneg fun q ↦ mul_nonneg (ρ.nonneg _ _) (hg0 q x)
  have hP0 (q : Ω) (x : X) : 0 ≤ P q x := integral_nonneg fun a ↦ hg0 q _
  have hfibφ (x : X) : HasCompactSupport (fun a : A ↦ φ (a • x)) ∧
      ∫ a : A, φ (a • x) ∂μA = Av x := by
    set S := (ρ.locallyFinite.point_finite (π x)).toFinset
    have hS (y : X) (hy : π y = π x) (F : Ω → ℝ) :
        (∑ᶠ q, ρ q (π y) * F q) = ∑ q ∈ S, ρ q (π x) * F q := by
      rw [hy]
      refine finsum_eq_sum_of_support_subset _ fun q hq ↦ ?_
      simp only [S, Set.Finite.coe_toFinset, mem_ofPred_eq]
      exact left_ne_zero_of_mul hq
    have hφS (a : A) : φ (a • x) = ∑ q ∈ S, ρ q (π x) * g q (a • x) :=
      hS _ (hπ a x) fun q ↦ g q (a • x)
    simp only [hφS]
    have hint (q : Ω) : Integrable (fun a : A ↦ g q (a • x)) μA :=
      ((hfib q).1 x).1.integrable_of_hasCompactSupport ((hfib q).1 x).2
    refine ⟨HasCompactSupport.intro (S.isCompact_biUnion fun q _ ↦ ((hfib q).1 x).2)
      fun a ha ↦ Finset.sum_eq_zero fun q hq ↦ ?_, ?_⟩
    · have : g q (a • x) = 0 := image_eq_zero_of_notMem_tsupport (f := fun a : A ↦ g q (a • x))
        fun h ↦ ha (mem_biUnion hq h)
      rw [this, mul_zero]
    · rw [integral_finsetSum _ fun q _ ↦ (hint q).const_mul _]
      simp only [integral_const_mul]
      exact (hS x rfl fun q ↦ P q x).symm
  have hApos (x : X) : 0 < Av x := by
    obtain ⟨q, hq⟩ := ρ.exists_pos (mem_univ (π x))
    obtain ⟨y, hy, hyx⟩ := hρ q (subset_tsupport _ hq.ne')
    obtain ⟨c, hc⟩ := Quotient.exact hyx
    have hP : 0 < P q x :=
      Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero ((hfib q).1 x).1
        ((hfib q).1 x).2 (fun a ↦ hg0 q _) (x := c) (by
          change g q (c • x) ≠ 0
          rw [show c • x = y from hc]
          exact hy)
    have hfin : (Function.support fun q ↦ ρ q (π x) * P q x).Finite :=
      (ρ.locallyFinite.point_finite (π x)).subset fun q hq ↦ left_ne_zero_of_mul hq
    refine lt_of_lt_of_le (mul_pos hq hP) ?_
    exact single_le_finsum q hfin fun j ↦ mul_nonneg (ρ.nonneg _ _) (hP0 j x)
  have hAinv (a : A) (x : X) : Av (a • x) = Av x := by
    simp only [Av, P, hπ, (hfib _).2.1]
  let b : X → ℝ := fun x ↦ φ x / Av x
  have hT : IsClosed (⋃ q, π ⁻¹' tsupport (ρ q) ∩ tsupport (g q)) :=
    ((ρ.locallyFinite_tsupport.preimage_continuous hπc).subset
      fun q ↦ inter_subset_left).isClosed_iUnion
      fun q ↦ ((isClosed_tsupport _).preimage hπc).inter (isClosed_tsupport _)
  have hsupp : tsupport b ⊆ ⋃ q, π ⁻¹' tsupport (ρ q) ∩ tsupport (g q) := by
    refine closure_minimal (fun x hx ↦ ?_) hT
    have hφx : φ x ≠ 0 := fun h ↦ hx (by simp [b, h])
    by_contra hnot
    apply hφx
    have hzero : ∀ q, ρ q (π x) * g q x = 0 := by
      intro q
      by_contra hq
      exact hnot (mem_iUnion.2 ⟨q, subset_tsupport _ (left_ne_zero_of_mul hq),
        subset_tsupport _ (right_ne_zero_of_mul hq)⟩)
    simp only [φ, hzero, finsum_zero]
  refine ⟨b, hφc.div hAc fun x ↦ (hApos x).ne', fun x ↦ div_nonneg (hφ0 x) (hApos x).le,
    fun K hK ↦ ?_, fun x ↦ ?_⟩
  · have hF := ρ.locallyFinite_tsupport.finite_nonempty_inter_compact hK
    refine (hF.isCompact_biUnion fun q _ ↦ (g q).hasCompactSupport).of_isClosed_subset
      ((isClosed_tsupport _).inter (hK.isClosed.preimage hπc)) ?_
    rintro x ⟨hx, hxK⟩
    obtain ⟨q, hq1, hq2⟩ := mem_iUnion.1 (hsupp hx)
    exact mem_biUnion ⟨π x, hq1, hxK⟩ hq2
  · have hb (a : A) : b (a • x) = φ (a • x) * (Av x)⁻¹ := by
      simp only [b, hAinv, div_eq_mul_inv]
    simp only [hb]
    refine ⟨(hfibφ x).1.mul_right, ?_⟩
    rw [integral_mul_const, (hfibφ x).2, mul_inv_cancel₀ (hApos x).ne']

/-- The orbit integral of a compactly supported test, evaluated at a representative of each
orbit, is the orbit integral at every point of the orbit, and is a continuous compactly
supported function on the orbit space. -/
private theorem existsUnique_properActionQuotientMeasure_descent (μA : Measure A)
    [μA.IsHaarMeasure] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] (f : C_c(X, E)) :
    (∀ x : X, ∫ a : A, f (a • (Quotient.mk (MulAction.orbitRel A X) x).out) ∂μA =
      ∫ a : A, f (a • x) ∂μA) ∧
      Continuous (fun q : Ω ↦ ∫ a : A, f (a • q.out) ∂μA) ∧
      HasCompactSupport (fun q : Ω ↦ ∫ a : A, f (a • q.out) ∂μA) := by
  let π : X → Ω := Quotient.mk (MulAction.orbitRel A X)
  have hπq : IsOpenQuotientMap π := MulAction.isOpenQuotientMap_quotientMk
  obtain ⟨-, hinv, hcont⟩ := existsUnique_properActionQuotientMeasure_fibre μA f
  have h1 (x : X) : ∫ a : A, f (a • (π x).out) ∂μA = ∫ a : A, f (a • x) ∂μA := by
    obtain ⟨c, hc⟩ := Quotient.exact (Quotient.out_eq (π x))
    rw [← show c • x = (π x).out from hc, hinv]
  refine ⟨h1, ?_, ?_⟩
  · refine hπq.isQuotientMap.continuous_iff.mpr ?_
    exact hcont.congr fun x ↦ (h1 x).symm
  · refine HasCompactSupport.intro (f.hasCompactSupport.image hπq.continuous) fun q hq ↦ ?_
    refine integral_eq_zero_of_ae (.of_forall fun a ↦ ?_)
    by_contra hne
    refine hq ⟨a • q.out, subset_tsupport _ hne, ?_⟩
    exact (Quotient.sound (MulAction.mem_orbit q.out a)).trans (Quotient.out_eq q)

/-- Multiplying the pullback of a compactly supported continuous function on the orbit space
by a Bruhat function gives a compactly supported continuous function. -/
private theorem existsUnique_properActionQuotientMeasure_weighted {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {b : X → ℝ} (hbc : Continuous b)
    (hbK : ∀ K : Set Ω, IsCompact K →
      IsCompact (tsupport b ∩ Quotient.mk (MulAction.orbitRel A X) ⁻¹' K))
    {ψ : Ω → E} (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) :
    Continuous (fun x ↦ b x • ψ (Quotient.mk (MulAction.orbitRel A X) x)) ∧
      HasCompactSupport (fun x ↦ b x • ψ (Quotient.mk (MulAction.orbitRel A X) x)) := by
  have hπc : Continuous (Quotient.mk (MulAction.orbitRel A X)) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := A) (T := X)).continuous
  refine ⟨hbc.smul (hψ.comp hπc), HasCompactSupport.intro (hbK _ hψs) fun x hx ↦ ?_⟩
  by_contra hne
  refine hx ⟨subset_tsupport _ (left_ne_zero_of_smul hne), ?_⟩
  exact subset_tsupport _ (right_ne_zero_of_smul hne)

/-- Paper: Remark 12.2.1.4, p. 507. For a free proper action, an invariant Radon measure
and a choice of Haar measure determine a unique Radon measure on the orbit space.
Deviation: The normalization formula is tested on compactly supported continuous functions. -/
theorem existsUnique_properActionQuotientMeasure (μA : Measure A) [μA.IsHaarMeasure]
    (μX : Measure X) [μX.Regular] [SMulInvariantMeasure A X μX] :
    ∃! ν : Measure Ω, ν.Regular ∧
      ∀ f : C_c(X, ℂ),
        Integrable (fun q : Ω ↦ ∫ a : A, f (a • q.out) ∂μA) ν ∧
          (∫ x, f x ∂μX) = ∫ q : Ω, ∫ a : A, f (a • q.out) ∂μA ∂ν := by
  classical
  let π : X → Ω := Quotient.mk (MulAction.orbitRel A X)
  have hπq : IsOpenQuotientMap π := MulAction.isOpenQuotientMap_quotientMk
  have hπc : Continuous π := hπq.continuous
  have : LocallyCompactSpace Ω := hπq.locallyCompactSpace
  have : BorelSpace Ω := ⟨rfl⟩
  have hπ (a : A) (x : X) : π (a • x) = π x := Quotient.sound (MulAction.mem_orbit x a)
  obtain ⟨b, hbc, hb0, hbK, hbfib⟩ := existsUnique_properActionQuotientMeasure_bruhat (X := X) μA
  -- the positive functional on the orbit space and its Riesz measure
  have hw (φ : C_c(Ω, ℝ)) :=
    existsUnique_properActionQuotientMeasure_weighted hbc hbK φ.continuous φ.hasCompactSupport
  have hwi (φ : C_c(Ω, ℝ)) : Integrable (fun x ↦ b x * φ (π x)) μX :=
    (hw φ).1.integrable_of_hasCompactSupport (hw φ).2
  let L : C_c(Ω, ℝ) →ₚ[ℝ] ℝ :=
    ⟨{ toFun := fun φ ↦ ∫ x, b x * φ (π x) ∂μX
       map_add' := fun φ ψ ↦ by
         simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply, mul_add]
         exact integral_add (hwi φ) (hwi ψ)
       map_smul' := fun c φ ↦ by
         simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
           RingHom.id_apply, mul_left_comm (b _) c]
         exact integral_const_mul c _ },
      fun φ ψ h ↦ integral_mono (hwi φ) (hwi ψ) fun x ↦
        mul_le_mul_of_nonneg_left (h (π x)) (hb0 x)⟩
  let ν := RealRMK.rieszMeasure L
  have hreal (φ : C_c(Ω, ℝ)) : ∫ q, φ q ∂ν = ∫ x, b x * φ (π x) ∂μX :=
    RealRMK.integral_rieszMeasure L φ
  -- the complex form of the defining identity
  have hcplx (ψ : Ω → ℂ) (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) :
      ∫ q, ψ q ∂ν = ∫ x, (b x : ℂ) * ψ (π x) ∂μX := by
    have hwψ := existsUnique_properActionQuotientMeasure_weighted hbc hbK hψ hψs
    have hiψ : Integrable (fun x ↦ (b x : ℂ) * ψ (π x)) μX := by
      refine (hwψ.1.integrable_of_hasCompactSupport hwψ.2).congr (.of_forall fun x ↦ ?_)
      exact Complex.real_smul
    let ψr : C_c(Ω, ℝ) := ⟨⟨fun q ↦ (ψ q).re, Complex.continuous_re.comp hψ⟩,
      hψs.comp_left (g := Complex.re) (by simp)⟩
    let ψi : C_c(Ω, ℝ) := ⟨⟨fun q ↦ (ψ q).im, Complex.continuous_im.comp hψ⟩,
      hψs.comp_left (g := Complex.im) (by simp)⟩
    have hiν : Integrable ψ ν := hψ.integrable_of_hasCompactSupport hψs
    apply Complex.ext
    · change RCLike.re (∫ q, ψ q ∂ν) = RCLike.re (∫ x, (b x : ℂ) * ψ (π x) ∂μX)
      rw [← integral_re hiν, ← integral_re hiψ]
      refine (hreal ψr).trans (integral_congr_ae (.of_forall fun x ↦ ?_))
      change b x * (ψ (π x)).re = ((b x : ℂ) * ψ (π x)).re
      rw [Complex.re_ofReal_mul]
    · change RCLike.im (∫ q, ψ q ∂ν) = RCLike.im (∫ x, (b x : ℂ) * ψ (π x) ∂μX)
      rw [← integral_im hiν, ← integral_im hiψ]
      refine (hreal ψi).trans (integral_congr_ae (.of_forall fun x ↦ ?_))
      change b x * (ψ (π x)).im = ((b x : ℂ) * ψ (π x)).im
      rw [Complex.im_ofReal_mul]
  -- unfolding: the weighted pullback of the orbit integral integrates to the original test
  have hunfold (f : C_c(X, ℂ)) :
      ∫ x, (b x : ℂ) * ∫ a : A, f (a • x) ∂μA ∂μX = ∫ x, f x ∂μX := by
    have hK1 := hbK _ (f.hasCompactSupport.image hπc)
    let K1 := tsupport b ∩ π ⁻¹' (π '' tsupport f)
    have hC1 := ProperSMul.isCompact_setOfPred_inter_nonempty (G := A) hK1 f.hasCompactSupport
    have hC2 := ProperSMul.isCompact_setOfPred_inter_nonempty (G := A) f.hasCompactSupport hK1
    have hbf (x : X) (a : A) (hb : b x ≠ 0) (hf : f (a • x) ≠ 0) : x ∈ K1 :=
      ⟨subset_tsupport _ hb, a • x, subset_tsupport _ hf, hπ a x⟩
    have hs1 : HasCompactSupport (Function.uncurry fun (x : X) (a : A) ↦ (b x : ℂ) * f (a • x)) := by
      refine HasCompactSupport.intro (hK1.prod hC1) fun p hp ↦ ?_
      by_contra hne
      have hb : b p.1 ≠ 0 := fun h ↦ hne (by simp [Function.uncurry, h])
      have hf : f (p.2 • p.1) ≠ 0 := fun h ↦ hne (by simp [Function.uncurry, h])
      exact hp ⟨hbf p.1 p.2 hb hf, p.2 • p.1, smul_mem_smul_set (hbf p.1 p.2 hb hf),
        subset_tsupport _ hf⟩
    have hs2 : HasCompactSupport
        (Function.uncurry fun (a : A) (y : X) ↦ (b (a⁻¹ • y) : ℂ) * f y) := by
      refine HasCompactSupport.intro (hC2.inv.prod f.hasCompactSupport) fun p hp ↦ ?_
      by_contra hne
      have hb : b (p.1⁻¹ • p.2) ≠ 0 := fun h ↦ hne (by simp [Function.uncurry, h])
      have hf : f p.2 ≠ 0 := fun h ↦ hne (by simp [Function.uncurry, h])
      have hK : p.1⁻¹ • p.2 ∈ K1 := hbf _ p.1 hb (by rwa [smul_inv_smul])
      exact hp ⟨Set.mem_inv.mpr ⟨p.1⁻¹ • p.2, smul_mem_smul_set (subset_tsupport _ hf), hK⟩,
        subset_tsupport _ hf⟩
    have hc1 : Continuous (Function.uncurry fun (x : X) (a : A) ↦ (b x : ℂ) * f (a • x)) :=
      (Complex.continuous_ofReal.comp (hbc.comp continuous_fst)).mul
        (f.continuous.comp (continuous_snd.smul continuous_fst))
    have hc2 : Continuous
        (Function.uncurry fun (a : A) (y : X) ↦ (b (a⁻¹ • y) : ℂ) * f y) :=
      (Complex.continuous_ofReal.comp (hbc.comp (continuous_fst.inv.smul continuous_snd))).mul
        (f.continuous.comp continuous_snd)
    calc ∫ x, (b x : ℂ) * ∫ a : A, f (a • x) ∂μA ∂μX
        = ∫ x, ∫ a : A, (b x : ℂ) * f (a • x) ∂μA ∂μX := by
          simp_rw [integral_const_mul]
      _ = ∫ a : A, ∫ x, (b x : ℂ) * f (a • x) ∂μX ∂μA :=
          integral_integral_swap_of_hasCompactSupport hc1 hs1
      _ = ∫ a : A, ∫ y, (b (a⁻¹ • y) : ℂ) * f y ∂μX ∂μA := by
          refine integral_congr_ae (.of_forall fun a ↦ ?_)
          refine Eq.trans ?_
            (integral_smul_eq_self (μ := μX) (fun y ↦ (b (a⁻¹ • y) : ℂ) * f y) (g := a))
          simp only [inv_smul_smul]
      _ = ∫ y, ∫ a : A, (b (a⁻¹ • y) : ℂ) * f y ∂μA ∂μX :=
          integral_integral_swap_of_hasCompactSupport hc2 hs2
      _ = ∫ y, f y ∂μX := by
          refine integral_congr_ae (.of_forall fun y ↦ ?_)
          have : SecondCountableTopology A := by
            have hcl : IsClosedMap (fun a : A ↦ a • y) := by
              refine (isProperMap_iff_isCompact_preimage.mpr
                ⟨continuous_id.smul continuous_const, fun K hK ↦ ?_⟩).isClosedMap
              change IsCompact ((fun a : A ↦ a • y) ⁻¹' K)
              have he : (fun a : A ↦ a • y) ⁻¹' K = {a : A | (a • {y} ∩ K).Nonempty} := by
                ext a
                simp [Set.smul_set_singleton]
              rw [he]
              exact ProperSMul.isCompact_setOfPred_inter_nonempty isCompact_singleton hK
            exact (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
              (continuous_id.smul continuous_const)
              (fun a c h ↦ IsCancelSMul.right_cancel' a c y h) hcl).isEmbedding.secondCountableTopology
          simp only
          rw [integral_mul_const, integral_complex_ofReal,
            integral_inv_eq_self (fun a ↦ b (a • y)) μA, (hbfib y).2, Complex.ofReal_one,
            one_mul]
  -- the formula for ν
  have hform (f : C_c(X, ℂ)) :
      Integrable (fun q : Ω ↦ ∫ a : A, f (a • q.out) ∂μA) ν ∧
        (∫ x, f x ∂μX) = ∫ q : Ω, ∫ a : A, f (a • q.out) ∂μA ∂ν := by
    obtain ⟨hd, hdc, hds⟩ := existsUnique_properActionQuotientMeasure_descent μA f
    refine ⟨hdc.integrable_of_hasCompactSupport hds, ?_⟩
    rw [hcplx _ hdc hds, ← hunfold f]
    exact integral_congr_ae (.of_forall fun x ↦ congrArg _ (hd x).symm)
  refine ⟨ν, ⟨inferInstance, hform⟩, fun ν' ⟨hreg, hform'⟩ ↦ ?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  obtain ⟨hwc, hws⟩ := hw φ
  let f : C_c(X, ℂ) := ⟨⟨fun x ↦ ((b x * φ (π x) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp hwc⟩, hws.comp_left Complex.ofReal_zero⟩
  have hF (q : Ω) : ∫ a : A, f (a • q.out) ∂μA = (φ q : ℂ) := by
    change ∫ a : A, ((b (a • q.out) * φ (π (a • q.out)) : ℝ) : ℂ) ∂μA = _
    simp only [hπ]
    rw [integral_complex_ofReal, integral_mul_const, (hbfib q.out).2, one_mul]
    exact congrArg (fun z ↦ ((φ z : ℝ) : ℂ)) (Quotient.out_eq q)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  refine (integral_congr_ae (.of_forall fun q ↦ (hF q).symm)).trans
    (((hform' f).2.symm).trans ((hform f).2.trans
      (integral_congr_ae (.of_forall fun q ↦ hF q))))

end ProperActions

section FundamentalDomains

variable {A X : Type*} [Group A] [MulAction A X] [TopologicalSpace X] [MeasurableSpace X]

-- TODO(paper-gap): (12.2.1.13) lies in X but is assigned a measure on X/G.
-- For the discrete subgroup cases below, a null overlap upstairs is equivalent
-- to its image being null for the corresponding normalized quotient measure.
/-- Paper: Remark 12.2.1.4, p. 507. The domain has nonempty interior, each point has
a unique translate in it, and the closure has null overlap with each of its
nonidentity translates.
Deviation: The overlap is measured upstairs. We drop connectedness for §12.2.2:
already for the rational ideles a connected set has singleton projection to ℚₚˣ
at every finite place, and hence has empty interior. -/
def IsIndentationFundamentalDomain (A : Type*) [Group A] [MulAction A X]
    (μ : Measure X) (D : Set X) : Prop :=
  (interior D).Nonempty ∧
    (∀ x : X, ∃! a : A, a • x ∈ D) ∧
    ∀ a : A, a ≠ 1 → μ (closure D ∩ a • closure D) = 0

/-- Paper: Remark 12.2.1.4, p. 507. With the trivial group acting, the whole space is
a fundamental domain exactly when it is nonempty under the relaxed definition. -/
theorem isIndentationFundamentalDomain_univ_punit (μ : Measure X) :
    IsIndentationFundamentalDomain PUnit μ (univ : Set X) ↔
      (univ : Set X).Nonempty := by
  unfold IsIndentationFundamentalDomain
  rw [interior_univ]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ ↦ ⟨PUnit.unit, mem_univ _, fun _ _ ↦ rfl⟩,
    fun a ha ↦ absurd (Subsingleton.elim a 1) ha⟩⟩

/-- Paper: Remark 12.2.1.4, p. 507. With countably many translates and a Borel
measure, the paper's exact tiling gives a measure-theoretic fundamental domain. -/
theorem IsIndentationFundamentalDomain.isFundamentalDomain [Countable A] [BorelSpace X]
    {μ : Measure X} {D : Set X} (hD : IsIndentationFundamentalDomain A μ D) :
    IsFundamentalDomain A D μ := by
  have hnull : μ (closure D \ D) = 0 := by
    refine measure_mono_null (t := ⋃ a : {g : A // g ≠ 1}, closure D ∩ a.val • closure D) ?_
      (measure_iUnion_null fun a ↦ hD.2.2 a.val a.property)
    rintro x ⟨hx, hxD⟩
    obtain ⟨g, hg, -⟩ := hD.2.1 x
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hxD (by simpa only [one_smul] using hg)
    refine mem_iUnion.mpr ⟨⟨g⁻¹, inv_ne_one.mpr hg1⟩, hx, ?_⟩
    exact ⟨g • x, subset_closure hg, inv_smul_smul g x⟩
  have heq : closure D =ᵐ[μ] D := ae_eq_set.mpr
    ⟨hnull, by rw [sdiff_eq_empty.mpr subset_closure, measure_empty]⟩
  exact IsFundamentalDomain.mk' (isClosed_closure.measurableSet.nullMeasurableSet.congr heq)
    hD.2.1

end FundamentalDomains

section Diagonal

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

local notation "Q" => G ⧸ H
local notation "π" => QuotientGroup.mk' H
local notation "q₂" => (Prod.map (QuotientGroup.mk' H) (QuotientGroup.mk' H))
local notation "countH" => (Measure.count : Measure H)

/-- Paper: Situation 12.2.2.1, p. 508. The domain for the translation action contains a
D′-sequence of relatively compact open symmetric neighborhoods of the identity. The discrete
closed subgroup and the compatible Haar measures are the standing hypotheses of the results. -/
def IsDiagonalIndentationSituation (μ : Measure G) (D : Set G) (U : ℕ → Set G) : Prop :=
  IsIndentationFundamentalDomain H μ D ∧ IsDPrimeSequence μ U ∧
    ∀ n, U n ⊆ D ∧ IsOpen (U n) ∧ IsCompact (closure (U n)) ∧ (U n)⁻¹ = U n

/-- Paper: Situation 12.2.2.1, p. 508. On the one-element group, the whole space
is a fundamental domain and also supplies the constant neighborhood sequence. -/
theorem isDiagonalIndentationSituation_subsingleton [Subsingleton G] :
    IsDiagonalIndentationSituation (⊥ : Subgroup G) Measure.count univ (fun _ ↦ univ) := by
  have hmass : (Measure.count : Measure G) univ = 1 := by
    simp [Subsingleton.count_eq_dirac (1 : G)]
  refine ⟨⟨by simp, fun x ↦ ⟨1, mem_univ _, fun h _ ↦ Subsingleton.elim _ _⟩,
    fun h hh ↦ (hh (Subsingleton.elim _ _)).elim⟩, ⟨⟨?_, antitone_const, ?_⟩, ?_⟩, ?_⟩
  · intro n
    simp [hmass]
  · refine ⟨2, by norm_num, fun n ↦ ?_⟩
    simp [hmass]
  · intro W hW
    refine ⟨0, fun x _ ↦ ?_⟩
    simpa only [Subsingleton.elim x (1 : G)] using mem_of_mem_nhds hW
  · intro n
    simp

variable [DiscreteTopology H] (hH : IsClosed (H : Set G))
  {μ : Measure G} [μ.IsHaarMeasure] {ν : Measure (G ⧸ H)}
  (hν : IsWeilQuotientMeasure H μ Measure.count ν)
  {D : Set G} {U : ℕ → Set G} (hS : IsDiagonalIndentationSituation H μ D U)

local notation "Ū" => (fun n ↦ (QuotientGroup.mk' H) '' U n)

include hH hν hS in
/-- Paper: Situation 12.2.2.1, p. 508. The quotient images of the neighborhoods in
the fundamental domain form a D′-sequence for the normalized quotient Haar measure. -/
theorem IsDiagonalIndentationSituation.quotient :
    IsDPrimeSequence ν Ū := by
  have : Countable H :=
    (TopologicalSpace.separableSpace_iff_countable).mp inferInstance
  have : IsClosed (H : Set G) := hH
  have : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have : ν.IsHaarMeasure := hν.1
  obtain ⟨hD, ⟨⟨hU1, hUanti, C, hC, hUC⟩, hUcof⟩, hU⟩ := hS
  have hFD : IsFundamentalDomain H D μ := hD.isFundamentalDomain
  let p := QuotientGroup.mk' H
  have hpc : Continuous p := QuotientGroup.continuous_mk
  have hpm : Measurable p := hpc.measurable
  have hpo : IsOpenMap p := QuotientGroup.isOpenMap_coe
  have hpH (h : H) : p h = 1 := (QuotientGroup.eq_one_iff _).mpr h.2
  let ν' : Measure (G ⧸ H) := (μ.restrict D).map p
  have hν'_apply (S : Set (G ⧸ H)) (hS : MeasurableSet S) : ν' S = μ (p ⁻¹' S ∩ D) := by
    rw [Measure.map_apply hpm hS, Measure.restrict_apply (hpm hS)]
  have hpre (V : Set G) : p ⁻¹' (p '' V) = ⋃ h : H, h • V := by
    ext x
    simp only [mem_preimage, mem_image, mem_iUnion, Subgroup.smul_def]
    constructor
    · rintro ⟨v, hv, hvx⟩
      have hm : v⁻¹ * x ∈ H := QuotientGroup.eq.mp hvx
      refine ⟨⟨v⁻¹ * x, hm⟩, mem_smul_set.mpr ⟨v, hv, ?_⟩⟩
      simp [smul_eq_mul, mul_comm]
    · rintro ⟨h, hx⟩
      obtain ⟨v, hv, rfl⟩ := mem_smul_set.mp hx
      refine ⟨v, hv, ?_⟩
      simp only [smul_eq_mul, map_mul]
      rw [hpH h, one_mul]
  -- the quotient image of an open set has at most its measure
  have hle (V : Set G) (hV : IsOpen V) : ν' (p '' V) ≤ μ V := by
    rw [hν'_apply _ (hpo V hV).measurableSet, hpre, iUnion_inter, hFD.measure_eq_tsum V]
    exact measure_iUnion_le _
  -- equality on subsets of the domain
  have heq (V : Set G) (hV : IsOpen V) (hVD : V ⊆ D) : ν' (p '' V) = μ V := by
    rw [hν'_apply _ (hpo V hV).measurableSet]
    congr 1
    ext x
    refine ⟨fun ⟨⟨v, hv, hvx⟩, hxD⟩ ↦ ?_, fun hx ↦ ⟨⟨x, hx, rfl⟩, hVD hx⟩⟩
    have hm : v⁻¹ * x ∈ H := QuotientGroup.eq.mp hvx
    obtain ⟨a, -, ha⟩ := hD.2.1 v
    have h1 : (⟨x * v⁻¹, by simpa [mul_comm] using hm⟩ : H) = 1 :=
      (ha _ (by simpa [Subgroup.smul_def, smul_eq_mul] using hxD)).trans
        (ha 1 (by simpa using hVD hv)).symm
    have : x * v⁻¹ = 1 := congrArg Subtype.val h1
    rwa [mul_inv_eq_one.mp this]
  have hinv : ν'.IsMulLeftInvariant := by
    refine ⟨fun g ↦ ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H g
    ext S hS
    rw [Measure.map_apply (measurable_const_mul _) hS, hν'_apply _ (measurable_const_mul _ hS),
      hν'_apply _ hS]
    have hT : MeasurableSet (p ⁻¹' S) := hpm hS
    have h1 : p ⁻¹' ((fun y ↦ p x * y) ⁻¹' S) ∩ D =
        (fun y ↦ x * y) ⁻¹' (p ⁻¹' S ∩ x • D) := by
      ext y
      simp only [mem_inter_iff, mem_preimage, map_mul]
      rw [← smul_eq_mul x y, smul_mem_smul_set_iff]
    rw [h1, measure_preimage_mul]
    refine (hFD.smul_of_comm x).measure_set_eq hFD hT fun h ↦ ?_
    ext y
    simp only [mem_preimage, Subgroup.smul_def, smul_eq_mul, map_mul]
    rw [hpH h, one_mul]
  have hfin : IsFiniteMeasureOnCompacts ν' := by
    refine ⟨fun K hK ↦ ?_⟩
    let E := CompactExhaustion.choice G
    obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n ↦ p '' interior (E n))
      (fun _ ↦ hpo _ isOpen_interior) (by
        rintro q -
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
        obtain ⟨n, hx⟩ := E.exists_mem x
        exact mem_iUnion.mpr ⟨n + 1, x, E.subset_interior_succ _ hx, rfl⟩)
      (Monotone.directed_le fun _ _ h ↦ image_mono (interior_mono (E.subset h)))
    exact ((measure_mono hn).trans ((hle _ isOpen_interior).trans
      (measure_mono interior_subset))).trans_lt (E.isCompact n).measure_lt_top
  have hcl (V : Set G) (hV : IsCompact (closure V)) : IsCompact (closure (p '' V)) :=
    (hV.image hpc).of_isClosed_subset isClosed_closure
      (closure_minimal (image_mono subset_closure) (hV.image hpc).isClosed)
  set c := Measure.haarScalarFactor ν' ν
  have hscale (V : Set G) (hV : IsCompact (closure V)) : ν' (p '' V) = c • ν (p '' V) :=
    Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν' ν (hcl V hV)
  have hUo (k : ℕ) : IsOpen (p '' U k) := hpo _ (hU k).2.1
  have hUUo (k : ℕ) : IsOpen (U k * (U k)⁻¹) := (hU k).2.1.mul_right
  have hUUc (k : ℕ) : IsCompact (closure (U k * (U k)⁻¹)) := by
    have hK := (hU k).2.2.1
    exact (hK.mul hK.inv).of_isClosed_subset isClosed_closure
      (closure_minimal (mul_subset_mul subset_closure (inv_subset_inv.mpr subset_closure))
        (hK.mul hK.inv).isClosed)
  have himg (k : ℕ) : p '' U k * (p '' U k)⁻¹ = p '' (U k * (U k)⁻¹) := by
    rw [image_mul, image_inv]
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h0
    have := hscale (U 0) (hU 0).2.2.1
    rw [heq _ (hU 0).2.1 (hU 0).1, ENNReal.smul_def, smul_eq_mul, h0, zero_mul] at this
    exact (hU1 0).2.2.1.ne' this
  refine ⟨⟨fun k ↦ ⟨⟨1, (hU1 k).1, map_one p⟩, (hUo k).measurableSet.nullMeasurableSet,
    (hUo k).measure_pos ν ⟨1, 1, (hU1 k).1, map_one p⟩,
    (measure_mono subset_closure).trans_lt (hcl _ (hU k).2.2.1).measure_lt_top⟩,
    fun a b hab ↦ image_mono (hUanti hab), C, hC, fun k ↦ ⟨?_, ?_⟩⟩, ?_⟩
  · rw [himg]
    exact (hpo _ (hUUo k)).measure_pos ν ⟨1, 1, ⟨1, (hU1 k).1, 1, by simpa using (hU1 k).1,
      by simp⟩, map_one p⟩
  · rw [himg]
    have h1 := hscale _ (hUUc k)
    have h2 := hscale _ (hU k).2.2.1
    rw [ENNReal.smul_def, smul_eq_mul] at h1 h2
    rw [heq _ (hU k).2.1 (hU k).1] at h2
    have h3 : (c : ℝ≥0∞) * ν (p '' (U k * (U k)⁻¹)) <
        (c : ℝ≥0∞) * (ENNReal.ofReal C * ν (p '' U k)) := by
      rw [← h1, mul_left_comm, ← h2]
      exact (hle _ (hUUo k)).trans_lt (hUC k).2
    exact (ENNReal.mul_lt_mul_iff_right hc0 ENNReal.coe_ne_top).mp h3
  · intro W hW
    obtain ⟨k, hk⟩ := hUcof _ (hpc.continuousAt.preimage_mem_nhds (by simpa using hW))
    exact ⟨k, image_subset_iff.mpr hk⟩

/-- Paper: (12.2.2.1), p. 508. Multiply the two indentation factors and integrate
their simultaneous subgroup translates. -/
def diagonalIndentationWeight (μH : Measure H) (b : G → ℝ) (p : G × G) : ℝ :=
  ∫ h : H, b ((h : G)⁻¹ * p.1) * b ((h : G)⁻¹ * p.2) ∂μH

/-- Paper: (12.2.2.1), p. 508. Averaging over the trivial subgroup with unit counting
measure returns the product of the two indentation factors. -/
theorem diagonalIndentationWeight_bot (b : G → ℝ) (p : G × G) :
    diagonalIndentationWeight (⊥ : Subgroup G) Measure.count b p = b p.1 * b p.2 := by
  simp [diagonalIndentationWeight, Subsingleton.count_eq_dirac (1 : (⊥ : Subgroup G))]

variable {b : G → ℝ} (hb : IsIndentation H Measure.count b)

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. The product of simultaneous translates is
integrable in the subgroup variable at every pair. -/
theorem integrable_diagonalIndentationWeight (p : G × G) :
    Integrable (fun h : H ↦ b ((h : G)⁻¹ * p.1) * b ((h : G)⁻¹ * p.2)) countH := by
  have hx := (hb.2.2.2 p.1).1
  have hy := (hb.2.2.2 p.2).1
  have hs := integrable_count_iff.mp hy
  exact hx.mul_bdd hy.aestronglyMeasurable
    (ae_of_all _ fun h ↦ hs.le_tsum h fun k _ ↦ norm_nonneg _)

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. The averaged indentation weight is continuous. -/
theorem continuous_diagonalIndentationWeight :
    Continuous (diagonalIndentationWeight H countH b) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨C, hC, hp⟩ := exists_compact_mem_nhds p.1
  let K := tsupport b ∩ π ⁻¹' (π '' C)
  have hK : IsCompact K := hb.2.2.1 C hC
  let T := (Subtype.val : H → G) ⁻¹' ((fun z : G × G ↦ z.1 * z.2⁻¹) '' (C ×ˢ K))
  have hT : T.Finite := (hH.isClosedEmbedding_subtypeVal.isCompact_preimage
    ((hC.prod hK).image (continuous_fst.mul continuous_snd.inv))).finite_of_discrete
  let term (h : H) (q : G × G) := b ((h : G)⁻¹ * q.1) * b ((h : G)⁻¹ * q.2)
  have hc (h : H) : Continuous (term h) :=
    (hb.1.comp (continuous_const.mul continuous_fst)).mul
      (hb.1.comp (continuous_const.mul continuous_snd))
  apply (continuous_finsetSum hT.toFinset fun h _ ↦ hc h).continuousAt.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt hp] with q hq
  have hzero (h : H) (hh : h ∉ hT.toFinset) : term h q = 0 := by
    suffices hz : b ((h : G)⁻¹ * q.1) = 0 by simp [term, hz]
    by_contra hn
    apply hh
    refine hT.mem_toFinset.mpr ⟨(q.1, (h : G)⁻¹ * q.1), ⟨hq, ?_⟩, ?_⟩
    · refine ⟨subset_tsupport b hn, q.1, hq, ?_⟩
      have hπ : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
      simp [map_mul, map_inv, hπ]
    · change q.1 * ((h : G)⁻¹ * q.1)⁻¹ = (h : G)
      simp [mul_inv_rev, ← mul_assoc]
  have hi : Integrable (fun h ↦ term h q) countH := integrable_count_iff.mpr
    (summable_of_ne_finset_zero (s := hT.toFinset) fun h hh ↦ by simp [hzero h hh])
  change (∫ h, term h q ∂countH) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (hT.toFinset : Set H)) hzero,
    setIntegral_finset hT.toFinset hi.integrableOn]
  simp only [count_real_singleton, one_smul]

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. The averaged indentation weight is nonnegative. -/
theorem diagonalIndentationWeight_nonneg (p : G × G) :
    0 ≤ diagonalIndentationWeight H countH b p := by
  exact integral_nonneg fun h ↦ mul_nonneg (hb.2.1 _) (hb.2.1 _)

include hH hν hS hb in
/-- Paper: Proposition 12.2.2.2(1), p. 508. Translating both coordinates by the same
subgroup element leaves the averaged weight invariant. -/
theorem diagonalIndentationWeight_mul (h : H) (p : G × G) :
    diagonalIndentationWeight H countH b ((h : G) * p.1, (h : G) * p.2) =
      diagonalIndentationWeight H countH b p := by
  let w (k : H) := b ((k : G)⁻¹ * p.1) * b ((k : G)⁻¹ * p.2)
  change (∫ k : H, b ((k : G)⁻¹ * ((h : G) * p.1)) *
    b ((k : G)⁻¹ * ((h : G) * p.2)) ∂countH) = ∫ k, w k ∂countH
  calc
    _ = ∫ k : H, w (h⁻¹ * k) ∂countH := by
      apply integral_congr_ae
      exact ae_of_all _ fun k ↦ by simp [w, mul_assoc]
    _ = _ := integral_mul_left_eq_self w h⁻¹

/-- Paper: (12.2.2.2), p. 508. Lift a quotient kernel by pulling it back in both
coordinates and multiplying by the subgroup-averaged indentation weight. -/
def diagonalIndentationLift (μH : Measure H) (b : G → ℝ) (u : Q × Q → ℂ)
    (p : G × G) : ℂ :=
  (diagonalIndentationWeight H μH b p : ℂ) * u (q₂ p)

/-- Paper: (12.2.2.2), p. 508. For the trivial subgroup with unit counting measure,
the kernel lift is a product of the two indentation factors and the pulled-back value. -/
theorem diagonalIndentationLift_bot (b : G → ℝ)
    (u : (G ⧸ (⊥ : Subgroup G)) × (G ⧸ (⊥ : Subgroup G)) → ℂ) (x y : G) :
    diagonalIndentationLift (⊥ : Subgroup G) Measure.count b u (x, y) =
      (b x : ℂ) * (b y : ℂ) * u (QuotientGroup.mk x, QuotientGroup.mk y) := by
  simp [diagonalIndentationLift, diagonalIndentationWeight,
    Subsingleton.count_eq_dirac (1 : (⊥ : Subgroup G))]

variable {u : (G ⧸ H) × (G ⧸ H) → ℂ} (hu : LocallyIntegrable u (ν.prod ν))

local notation "uSmooth" => (dSequenceKernelSmoothening ν Ū u)
local notation "Ψ" => (diagonalIndentationLift H (Measure.count : Measure H) b)

/-- Weil's formula makes the preimage of a quotient-null set null. -/
private theorem aemeasurable_diagonalIndentationLift_quotient_qmp
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    [DiscreteTopology H] (hH : IsClosed (H : Set G))
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ Measure.count ν) :
    QuasiMeasurePreserving (QuotientGroup.mk' H) μ ν := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : (Measure.count : Measure H).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let qmap : G → G ⧸ H := QuotientGroup.mk' H
  have hqmap : Measurable qmap := QuotientGroup.continuous_mk.measurable
  refine ⟨hqmap.aemeasurable, Measure.AbsolutelyContinuous.mk ?_⟩
  intro S hS hnull
  rw [Measure.map_apply hqmap hS]
  let f : G → ℂ := (qmap ⁻¹' S).indicator (fun _ ↦ 1)
  have hpre : MeasurableSet (qmap ⁻¹' S) := hS.preimage hqmap
  have hf : Measurable f := measurable_const.indicator hpre
  have hnot : ∀ᵐ q ∂ν, q ∉ S := measure_eq_zero_iff_ae_notMem.mp hnull
  have hquot (q : G ⧸ H) (h : H) : qmap (q.out * (h : G)) = q := by
    have hh : qmap (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    change (QuotientGroup.mk' H) (q.out * (h : G)) = q
    dsimp only [qmap] at hh
    rw [map_mul, hh, mul_one]
    exact Quotient.out_eq' q
  have hzero (q : G ⧸ H) (hq : q ∉ S) (h : H) :
      f (q.out * (h : G)) = 0 := by
    exact indicator_of_notMem (by simpa only [mem_preimage, hquot] using hq) _
  have hnorm :
      (∫⁻ q, ∫⁻ h : H, ‖f (q.out * (h : G))‖₊ ∂Measure.count ∂ν) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hnot] with q hq
    simp [hzero q hq]
  obtain ⟨hi, he⟩ := integrable_of_weilNormIntegral H hH μ Measure.count ν hν hf
    (by rw [hnorm]; exact ENNReal.zero_lt_top)
  have hfib : lcaCosetIntegral H Measure.count f =ᵐ[ν] fun _ ↦ 0 := by
    filter_upwards [hnot] with q hq
    simp [lcaCosetIntegral, hzero q hq]
  rw [integral_congr_ae hfib, integral_zero] at he
  have hfinite : μ (qmap ⁻¹' S) < ∞ := by
    simpa using ((integrable_indicator_iff hpre).mp hi)
  have hreal : μ.real (qmap ⁻¹' S) = 0 := by
    apply Complex.ofReal_injective
    simpa only [f, integral_indicator_const (1 : ℂ) hpre,
      Complex.real_smul, mul_one, Complex.ofReal_zero] using he
  exact (measureReal_eq_zero_iff hfinite.ne).mp hreal

include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The lifted kernel is measurable for
completed product Haar measure.
Deviation: The local integrability hypothesis uses the product measure as in the proof. -/
theorem aemeasurable_diagonalIndentationLift :
    AEMeasurable (Ψ u) (μ.prod μ) := by
  let : IsClosed (H : Set G) := hH
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  have hq := aemeasurable_diagonalIndentationLift_quotient_qmp H hH μ ν hν
  exact (continuous_diagonalIndentationWeight H hH hν hS hb).measurable.complex_ofReal.aemeasurable.mul
    (hu.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving (hq.prodMap hq))

variable (hdiag : ∀ᵐ q ∂ν, (q, q) ∈
    dSequenceRegularSet (ν.prod ν)
      (fun n ↦ (QuotientGroup.mk' H '' U n) ×ˢ (QuotientGroup.mk' H '' U n)) u)

/-- Translated averages of a measurable function are measurable in the center. -/
private theorem aemeasurable_dSequenceKernelSmoothening_diagonal_average
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    (m : Measure A) [m.IsHaarMeasure] [SFinite m]
    (V : Set A) (g : A → ℂ) (hg : Measurable g) :
    Measurable (fun x : A ↦ dSequenceAverage m V g x) := by
  have hprod : StronglyMeasurable (fun p : A × A ↦ g (p.1 * p.2)) := by
    simpa only [Function.comp_def, Pi.mul_apply] using
      (hg.comp (measurable_fst.mul measurable_snd)).stronglyMeasurable
  have hint : Measurable (fun x : A ↦ ∫ y in V, g (x * y) ∂m) :=
    hprod.integral_prod_right'.measurable
  have havg (x : A) : dSequenceAverage m V g x =
      (m.real V)⁻¹ • ∫ y in V, g (x * y) ∂m := by
    rw [dSequenceAverage, setAverage_eq,
      show m.real (x • V) = m.real V by simp only [Measure.real, measure_smul]]
    congr 1
    exact (measurePreserving_smul x m).setIntegral_image_emb
      (measurableEmbedding_const_smul x) g V
  have hfun : (fun x : A ↦ dSequenceAverage m V g x) =
      (fun x : A ↦ (m.real V)⁻¹ • ∫ y in V, g (x * y) ∂m) := funext havg
  rw [hfun]
  simpa only [Pi.smul_def] using hint.const_smul (m.real V)⁻¹

include hH hν hS hu hdiag in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The smoothened quotient diagonal is
measurable for the completed quotient Haar measure. -/
theorem aemeasurable_dSequenceKernelSmoothening_diagonal :
    AEMeasurable (fun q ↦ uSmooth (q, q)) ν := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : IsClosed (H : Set G) := hH
  let : ν.IsHaarMeasure := hν.1
  obtain ⟨g, hg, hug⟩ := hu.aestronglyMeasurable.aemeasurable
  have havg (n : ℕ) (p : Q × Q) :
      dSequenceAverage (ν.prod ν) (Ū n ×ˢ Ū n) u p =
        dSequenceAverage (ν.prod ν) (Ū n ×ˢ Ū n) g p := by
    exact average_congr (ae_restrict_of_ae hug)
  have hm (n : ℕ) : Measurable (fun q : Q ↦
      dSequenceAverage (ν.prod ν) (Ū n ×ˢ Ū n) u (q, q)) := by
    have h := (aemeasurable_dSequenceKernelSmoothening_diagonal_average
      (ν.prod ν) (Ū n ×ˢ Ū n) g hg).comp (measurable_id.prodMk measurable_id)
    simpa only [havg, Function.comp_def, id_eq] using h
  refine aemeasurable_of_tendsto_metrizable_ae atTop (fun n ↦ (hm n).aemeasurable) ?_
  filter_upwards [hdiag] with q hq
  simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero,
    dite_eq_left hq, dSequenceSmoothening] using (tendsto_nhds_limUnder hq)

include hH hν hS hu hdiag in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The quotient points used on both skew
diagonals of the lift are regular for almost every group coordinate. -/
theorem ae_quotient_diagonal_mem_dSequenceRegularSet :
    ∀ᵐ x ∂μ, (π x, π x) ∈ dSequenceRegularSet (ν.prod ν) (fun n ↦ Ū n ×ˢ Ū n) u := by
  exact (aemeasurable_diagonalIndentationLift_quotient_qmp H hH μ ν hν).tendsto_ae.eventually hdiag

variable (hi : Integrable (fun q ↦
  dSequenceKernelSmoothening ν (fun n ↦ QuotientGroup.mk' H '' U n) u (q, q)) ν)

include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. Translating the first diagonal coordinate
gives a function measurable for the completed product measure.
Deviation: The product measure follows the coordinate order `(x, h)`. -/
theorem aemeasurable_diagonalIndentationLift_left :
    AEMeasurable (fun p : G × H ↦ Ψ uSmooth ((p.2 : G)⁻¹ * p.1, p.1)) (μ.prod countH) :=
  by
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hq := aemeasurable_diagonalIndentationLift_quotient_qmp H hH μ ν hν
  have hd := hi.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving hq
  have hpull := hd.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := countH))
  have hw : Continuous (fun p : G × H ↦
      diagonalIndentationWeight H countH b ((p.2 : G)⁻¹ * p.1, p.1)) :=
    (continuous_diagonalIndentationWeight H hH hν hS hb).comp
      (((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst).prodMk continuous_fst)
  have hm := hw.measurable.complex_ofReal.aemeasurable.mul hpull
  convert hm using 1
  funext p
  have h1 : π (p.2 : G) = 1 := (QuotientGroup.eq_one_iff _).mpr p.2.property
  have hπ : π ((p.2 : G)⁻¹ * p.1) = π p.1 := by
    rw [map_mul, map_inv, h1, inv_one, one_mul]
  simp only [diagonalIndentationLift, Prod.map_apply, hπ, Function.comp_def, Pi.mul_apply]

include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. Translating the second diagonal coordinate
gives a function measurable for the completed product measure.
Deviation: The product measure follows the coordinate order `(x, h)`. -/
theorem aemeasurable_diagonalIndentationLift_right :
    AEMeasurable (fun p : G × H ↦ Ψ uSmooth (p.1, (p.2 : G)⁻¹ * p.1)) (μ.prod countH) :=
  by
  have hweight (x y : G) :
      diagonalIndentationWeight H countH b (x, y) = diagonalIndentationWeight H countH b (y, x) :=
    integral_congr_ae (ae_of_all _ fun k ↦ mul_comm _ _)
  have hswap (h : H) (x : G) :
      Ψ uSmooth ((h : G)⁻¹ * x, x) = Ψ uSmooth (x, (h : G)⁻¹ * x) := by
    have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    have hπ : π ((h : G)⁻¹ * x) = π x := by rw [map_mul, map_inv, h1, inv_one, one_mul]
    simp only [diagonalIndentationLift, Prod.map_apply, hπ, hweight ((h : G)⁻¹ * x) x]
  simpa only [hswap] using
    aemeasurable_diagonalIndentationLift_left H hH hν hS hb hu hdiag hi

/-- Summing the averaged indentation weight over the translates of the first coordinate gives
one, since the indentation sums to one over each orbit. -/
private theorem integral_diagonalIndentationLift_left_weight [Countable H]
    (hb₀ : IsIndentation H Measure.count b) (x : G) :
    Integrable (fun h : H ↦ diagonalIndentationWeight H countH b ((h : G)⁻¹ * x, x)) countH ∧
      ∫ h : H, diagonalIndentationWeight H countH b ((h : G)⁻¹ * x, x) ∂countH = 1 := by
  obtain ⟨hβi, hβ1⟩ := hb₀.2.2.2 x
  let β : H → ℝ := fun h ↦ b ((h : G)⁻¹ * x)
  have hβ0 (h : H) : 0 ≤ β h := hb₀.2.1 _
  have hcount (f : H → ℝ) (hf : Integrable f countH) : ∫ h, f h ∂countH = ∑' h, f h := by
    rw [integral_countable hf]
    simp
  have hβs : Summable β := (integrable_count_iff.mp hβi).of_norm
  have hβsum : ∑' h, β h = 1 := (hcount β hβi).symm.trans hβ1
  have hβle (k : H) : β k ≤ 1 := hβsum ▸ hβs.le_tsum k fun j _ ↦ hβ0 j
  have hts (h : H) : Summable fun k ↦ β (h * k) * β k :=
    Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (hβ0 _) (hβ0 _))
      (fun k ↦ mul_le_of_le_one_left (hβ0 k) (hβle _)) hβs
  have hW (h : H) : diagonalIndentationWeight H countH b ((h : G)⁻¹ * x, x) =
      ∑' k, β (h * k) * β k := by
    have hfun : (fun k : H ↦ b ((k : G)⁻¹ * ((h : G)⁻¹ * x)) * b ((k : G)⁻¹ * x)) =
        fun k ↦ β (h * k) * β k := by
      funext k
      simp only [β, Subgroup.coe_mul, mul_inv_rev, mul_assoc]
    change (∫ k : H, b ((k : G)⁻¹ * ((h : G)⁻¹ * x)) * b ((k : G)⁻¹ * x) ∂countH) = _
    rw [hfun]
    exact hcount _ (integrable_count_iff.mpr ((hts h).congr fun k ↦
      (Real.norm_of_nonneg (mul_nonneg (hβ0 _) (hβ0 _))).symm))
  have hW0 (h : H) : 0 ≤ ∑' k, β (h * k) * β k :=
    tsum_nonneg fun k ↦ mul_nonneg (hβ0 _) (hβ0 _)
  have hβE : ∑' k, ENNReal.ofReal (β k) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hβ0 hβs, hβsum, ENNReal.ofReal_one]
  have htot : ∑' h, ENNReal.ofReal (∑' k, β (h * k) * β k) = 1 := by
    have hE (h : H) : ENNReal.ofReal (∑' k, β (h * k) * β k) =
        ∑' k, ENNReal.ofReal (β (h * k)) * ENNReal.ofReal (β k) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k ↦ mul_nonneg (hβ0 _) (hβ0 _)) (hts h)]
      exact tsum_congr fun k ↦ ENNReal.ofReal_mul (hβ0 _)
    have hshift (k : H) : ∑' h, ENNReal.ofReal (β (h * k)) = 1 :=
      ((Equiv.mulRight k).tsum_eq fun h ↦ ENNReal.ofReal (β h)).trans hβE
    simp_rw [hE]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_right, hshift, one_mul]
    exact hβE
  have hne (h : H) : ENNReal.ofReal (∑' k, β (h * k) * β k) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsum : Summable fun h ↦ ∑' k, β (h * k) * β k := by
    simpa only [ENNReal.toReal_ofReal (hW0 _)] using
      ENNReal.summable_toReal (htot.trans_ne ENNReal.one_ne_top)
  have hint : Integrable (fun h : H ↦ diagonalIndentationWeight H countH b ((h : G)⁻¹ * x, x))
      countH := by
    simp only [hW]
    exact integrable_count_iff.mpr (hsum.congr fun h ↦ (Real.norm_of_nonneg (hW0 _)).symm)
  refine ⟨hint, ?_⟩
  rw [hcount _ hint]
  simp only [hW]
  have := ENNReal.tsum_toReal_eq hne
  rw [htot, ENNReal.toReal_one] at this
  simpa only [ENNReal.toReal_ofReal (hW0 _)] using this.symm

/-- Two elements lie in the same orbit of the subgroup acting by left multiplication exactly
when they have the same coset. -/
private theorem integral_diagonalIndentationLift_left_orbit (x y : G) :
    Quotient.mk (MulAction.orbitRel H G) x = Quotient.mk (MulAction.orbitRel H G) y ↔
      (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk y := by
  rw [Quotient.eq, MulAction.orbitRel_apply, QuotientGroup.eq]
  constructor
  · rintro ⟨h, hh⟩
    have hx : (h : G) * y = x := hh
    have e : ((h : G) * y)⁻¹ * y = (h : G)⁻¹ := by
      rw [mul_inv_rev, mul_comm y⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [← hx, e]
    exact H.inv_mem h.property
  · intro hxy
    refine ⟨⟨(x⁻¹ * y)⁻¹, H.inv_mem hxy⟩, ?_⟩
    change (x⁻¹ * y)⁻¹ * y = x
    rw [mul_inv_rev, inv_inv, mul_comm y⁻¹ x, mul_assoc, inv_mul_cancel, mul_one]

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.3), p. 508. The first skew-diagonal evaluation is absolutely
integrable on the fundamental domain times the subgroup. -/
theorem integrable_diagonalIndentationLift_left :
    Integrable (fun p : G × H ↦ Ψ uSmooth ((p.2 : G)⁻¹ * p.1, p.1))
      ((μ.restrict D).prod countH) := by
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hq (p : G × H) : q₂ ((p.2 : G)⁻¹ * p.1, p.1) = (π p.1, π p.1) := by
    have h1 : π ((p.2 : G)) = 1 := (QuotientGroup.eq_one_iff _).mpr p.2.property
    simp only [Prod.map_apply, map_mul, map_inv, h1, inv_one, one_mul]
  have hw0 (p : G × H) :
      0 ≤ diagonalIndentationWeight H countH b ((p.2 : G)⁻¹ * p.1, p.1) :=
    integral_nonneg fun h ↦ mul_nonneg (hb.2.1 _) (hb.2.1 _)
  have hnorm (p : G × H) : ‖Ψ uSmooth ((p.2 : G)⁻¹ * p.1, p.1)‖ =
      diagonalIndentationWeight H countH b ((p.2 : G)⁻¹ * p.1, p.1) *
        ‖uSmooth (π p.1, π p.1)‖ := by
    simp only [diagonalIndentationLift, hq p, norm_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg (hw0 p)]
  have hW (x : G) := integral_diagonalIndentationLift_left_weight H hb x
  have hWlin (x : G) : ∫⁻ h : H,
      ENNReal.ofReal (diagonalIndentationWeight H countH b ((h : G)⁻¹ * x, x)) ∂countH = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hW x).1
      (ae_of_all _ fun h ↦ integral_nonneg fun k ↦ mul_nonneg (hb.2.1 _) (hb.2.1 _)),
      (hW x).2, ENNReal.ofReal_one]
  have hpt (x : G) (h : H) : ENNReal.ofReal ‖Ψ uSmooth ((h : G)⁻¹ * x, x)‖ =
      ENNReal.ofReal (diagonalIndentationWeight H countH b ((h : G)⁻¹ * x, x)) *
        ENNReal.ofReal ‖uSmooth (π x, π x)‖ := by
    rw [hnorm (x, h), ENNReal.ofReal_mul (hw0 (x, h))]
  have hlin (x : G) : ∫⁻ h : H, ENNReal.ofReal ‖Ψ uSmooth ((h : G)⁻¹ * x, x)‖ ∂countH =
      ENNReal.ofReal ‖uSmooth (π x, π x)‖ := by
    have hm : AEMeasurable (fun h : H ↦ ENNReal.ofReal
        (diagonalIndentationWeight H countH b ((h : G)⁻¹ * x, x))) countH :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hW x).1.aestronglyMeasurable.aemeasurable
    calc ∫⁻ h : H, ENNReal.ofReal ‖Ψ uSmooth ((h : G)⁻¹ * x, x)‖ ∂countH
        = ∫⁻ h : H, ENNReal.ofReal (diagonalIndentationWeight H countH b ((h : G)⁻¹ * x, x)) *
            ENNReal.ofReal ‖uSmooth (π x, π x)‖ ∂countH := lintegral_congr (hpt x)
      _ = (∫⁻ h : H, ENNReal.ofReal
            (diagonalIndentationWeight H countH b ((h : G)⁻¹ * x, x)) ∂countH) *
            ENNReal.ofReal ‖uSmooth (π x, π x)‖ := lintegral_mul_const'' _ hm
      _ = ENNReal.ofReal ‖uSmooth (π x, π x)‖ := by rw [hWlin x, one_mul]
  -- a Borel fundamental domain for the subgroup and the quotient map on it
  have hD : IsIndentationFundamentalDomain H μ D := hS.1
  have hFD : IsFundamentalDomain H D μ := hD.isFundamentalDomain
  obtain ⟨M, hMD, hMm, -⟩ := hFD.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hinjM : Set.InjOn (Quotient.mk (MulAction.orbitRel H G)) M := by
    intro x hx y hy hxy
    obtain ⟨h, hh⟩ := Quotient.eq.mp hxy
    have hx' : (h : G) * y = x := hh
    obtain ⟨a, -, ha⟩ := hD.2.1 y
    have h1 : h = 1 := (ha h (show h • y ∈ D by
        rw [Subgroup.smul_def, smul_eq_mul, hx']; exact hMD hx)).trans
      (ha 1 (show (1 : H) • y ∈ D by rw [one_smul]; exact hMD hy)).symm
    rw [← hx', h1, OneMemClass.coe_one, one_mul]
  obtain ⟨Δ, hΔm, -, hΔb⟩ := exists_borel_orbit_transversal hMm hinjM
  have hbij : Function.Bijective (fun x : Δ ↦ (QuotientGroup.mk x.val : G ⧸ H)) := by
    refine ⟨fun x y hxy ↦ hΔb.injective
      ((integral_diagonalIndentationLift_left_orbit H _ _).mpr hxy), fun q ↦ ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx⟩ := hΔb.surjective (Quotient.mk (MulAction.orbitRel H G) g)
    exact ⟨x, (integral_diagonalIndentationLift_left_orbit H _ _).mp hx⟩
  have hΔFD : IsFundamentalDomain H Δ μ := by
    refine IsFundamentalDomain.mk' hΔm.nullMeasurableSet fun x ↦ ?_
    obtain ⟨y, hy⟩ := hΔb.surjective (Quotient.mk (MulAction.orbitRel H G) x)
    obtain ⟨h, hh⟩ := Quotient.eq.mp hy
    have hh' : h • x = y.val := hh
    refine ⟨h, show h • x ∈ Δ by rw [hh']; exact y.property, fun h' hh₂ ↦ ?_⟩
    have hh₂' : h' • x ∈ Δ := hh₂
    have hsame : (⟨h' • x, hh₂'⟩ : Δ) = y :=
      hΔb.injective ((Quotient.sound (s := MulAction.orbitRel H G) (a := h' • x) (b := x)
        ⟨h', rfl⟩).trans hy.symm)
    have hxy : (h' : G) * x = (h : G) * x := (congrArg Subtype.val hsame).trans hh'.symm
    exact Subtype.ext (mul_right_cancel hxy)
  -- integrability on the transversal and the value of its norm integral
  have hfg : Integrable (fun q : G ⧸ H ↦ ((‖uSmooth (q, q)‖ : ℝ) : ℂ)) ν := hi.norm.ofReal
  have hind : Integrable (fun x : G ↦ ((‖uSmooth (π x, π x)‖ : ℝ) : ℂ)) (μ.restrict Δ) :=
    (integrable_indicator_iff hΔm).1
      ((weilFundamentalDomain_integrable_iff H hH μ hΔm hbij ν hν _).1 hfg)
  have hIntΔ : Integrable (fun x : G ↦ ‖uSmooth (π x, π x)‖) (μ.restrict Δ) := by
    simpa using MeasureTheory.Integrable.norm hind
  have hvalΔ : ∫ x in Δ, ‖uSmooth (π x, π x)‖ ∂μ = ∫ q, ‖uSmooth (q, q)‖ ∂ν := by
    have h := weilFundamentalDomain_integral H hH μ hΔm hbij ν hν hfg
    have hL : ∫ q, ((‖uSmooth (q, q)‖ : ℝ) : ℂ) ∂ν =
        ((∫ q, ‖uSmooth (q, q)‖ ∂ν : ℝ) : ℂ) := integral_ofReal
    have hR : ∫ x in Δ, ((‖uSmooth (QuotientGroup.mk x, QuotientGroup.mk x)‖ : ℝ) : ℂ) ∂μ =
        ((∫ x in Δ, ‖uSmooth (QuotientGroup.mk x, QuotientGroup.mk x)‖ ∂μ : ℝ) : ℂ) :=
      integral_ofReal
    rw [hL, hR] at h
    exact Complex.ofReal_injective h.symm
  -- the upper bound
  have hinv : ∀ (h : H) (x : G),
      ENNReal.ofReal ‖uSmooth (π ((h : G) * x), π ((h : G) * x))‖ =
        ENNReal.ofReal ‖uSmooth (π x, π x)‖ := by
    intro h x
    have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    rw [map_mul, h1, one_mul]
  have hsm : AEMeasurable (fun q : G ⧸ H ↦ ENNReal.ofReal ‖uSmooth (q, q)‖) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_dSequenceKernelSmoothening_diagonal H hH hν hS hu hdiag).norm
  have hprod : ∫⁻ p : G × H, ENNReal.ofReal ‖Ψ uSmooth ((p.2 : G)⁻¹ * p.1, p.1)‖
      ∂((μ.restrict D).prod countH) ≤ ENNReal.ofReal (∫ q, ‖uSmooth (q, q)‖ ∂ν) := by
    calc ∫⁻ p : G × H, ENNReal.ofReal ‖Ψ uSmooth ((p.2 : G)⁻¹ * p.1, p.1)‖
          ∂((μ.restrict D).prod countH)
        ≤ ∫⁻ x, ∫⁻ h : H, ENNReal.ofReal ‖Ψ uSmooth ((h : G)⁻¹ * x, x)‖ ∂countH
            ∂(μ.restrict D) := lintegral_prod_le _
      _ = ∫⁻ x, ENNReal.ofReal ‖uSmooth (π x, π x)‖ ∂(μ.restrict D) := by simp_rw [hlin]
      _ = ∫⁻ x, ENNReal.ofReal ‖uSmooth (π x, π x)‖ ∂(μ.restrict Δ) :=
          hFD.setLIntegral_eq hΔFD (fun x ↦ ENNReal.ofReal ‖uSmooth (π x, π x)‖) hinv
      _ = ENNReal.ofReal (∫ x in Δ, ‖uSmooth (π x, π x)‖ ∂μ) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hIntΔ (ae_of_all _ fun x ↦ norm_nonneg _)]
      _ = ENNReal.ofReal (∫ q, ‖uSmooth (q, q)‖ ∂ν) := by rw [hvalΔ]
  refine ⟨?_, ?_⟩
  · exact ((aemeasurable_diagonalIndentationLift_left H hH hν hS hb hu hdiag hi).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_norm]
    exact lt_of_le_of_lt hprod ENNReal.ofReal_lt_top


include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The second skew-diagonal evaluation is
absolutely integrable on the fundamental domain times the subgroup. -/
theorem integrable_diagonalIndentationLift_right :
    Integrable (fun p : G × H ↦ Ψ uSmooth (p.1, (p.2 : G)⁻¹ * p.1))
      ((μ.restrict D).prod countH) := by
  have hweight (x y : G) :
      diagonalIndentationWeight H countH b (x, y) = diagonalIndentationWeight H countH b (y, x) :=
    integral_congr_ae (ae_of_all _ fun k ↦ mul_comm _ _)
  have hswap (h : H) (x : G) :
      Ψ uSmooth ((h : G)⁻¹ * x, x) = Ψ uSmooth (x, (h : G)⁻¹ * x) := by
    have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    have hπ : π ((h : G)⁻¹ * x) = π x := by rw [map_mul, map_inv, h1, inv_one, one_mul]
    simp only [diagonalIndentationLift, Prod.map_apply, hπ, hweight ((h : G)⁻¹ * x) x]
  simpa only [hswap] using
    integrable_diagonalIndentationLift_left H hH hν hS hb hu hdiag hi



include hH hν hS hb hu hdiag hi in
/-- Paper: Proposition 12.2.2.2(2), p. 508. The integral of the smoothened quotient diagonal
equals the integral of the first skew diagonal, integrating subgroup translates first. -/
theorem integral_diagonalIndentationLift_left :
    (∫ q, uSmooth (q, q) ∂ν) =
      ∫ x in D, ∫ h : H, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂countH ∂μ := by
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : IsClosed (H : Set G) := hH
  have hinner (x : G) : ∫ h : H, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂countH = uSmooth (π x, π x) := by
    have hπ (h : H) : q₂ ((h : G)⁻¹ * x, x) = (π x, π x) := by
      have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
      simp only [Prod.map_apply, map_mul, map_inv, h1, inv_one, one_mul]
    simp only [diagonalIndentationLift, hπ]
    rw [integral_mul_const, integral_complex_ofReal,
      (integral_diagonalIndentationLift_left_weight H hb x).2, Complex.ofReal_one, one_mul]
  simp_rw [hinner]
  obtain ⟨hD, -, -⟩ := hS
  have hFD : IsFundamentalDomain H D μ := hD.isFundamentalDomain
  obtain ⟨M, hMD, hMm, -⟩ := hFD.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hinjM : Set.InjOn (Quotient.mk (MulAction.orbitRel H G)) M := by
    intro x hx y hy hxy
    obtain ⟨h, hh⟩ := Quotient.eq.mp hxy
    have hx' : (h : G) * y = x := hh
    obtain ⟨a, -, ha⟩ := hD.2.1 y
    have h1 : h = 1 := (ha h (show h • y ∈ D by
        rw [Subgroup.smul_def, smul_eq_mul, hx']; exact hMD hx)).trans
      (ha 1 (show (1 : H) • y ∈ D by rw [one_smul]; exact hMD hy)).symm
    rw [← hx', h1, OneMemClass.coe_one, one_mul]
  obtain ⟨Δ, hΔm, -, hΔb⟩ := exists_borel_orbit_transversal hMm hinjM
  have hbij : Function.Bijective (fun x : Δ ↦ (QuotientGroup.mk x.val : G ⧸ H)) := by
    refine ⟨fun x y hxy ↦ hΔb.injective
      ((integral_diagonalIndentationLift_left_orbit H _ _).mpr hxy), fun q ↦ ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx⟩ := hΔb.surjective (Quotient.mk (MulAction.orbitRel H G) g)
    exact ⟨x, (integral_diagonalIndentationLift_left_orbit H _ _).mp hx⟩
  have hΔFD : IsFundamentalDomain H Δ μ := by
    refine IsFundamentalDomain.mk' hΔm.nullMeasurableSet fun x ↦ ?_
    obtain ⟨y, hy⟩ := hΔb.surjective (Quotient.mk (MulAction.orbitRel H G) x)
    obtain ⟨h, hh⟩ := Quotient.eq.mp hy
    have hh' : h • x = y.val := hh
    refine ⟨h, show h • x ∈ Δ by rw [hh']; exact y.property, fun h' hh₂ ↦ ?_⟩
    have hh₂' : h' • x ∈ Δ := hh₂
    have hsame : (⟨h' • x, hh₂'⟩ : Δ) = y :=
      hΔb.injective ((Quotient.sound (s := MulAction.orbitRel H G) (a := h' • x) (b := x)
        ⟨h', rfl⟩).trans hy.symm)
    have hxy : (h' : G) * x = (h : G) * x := (congrArg Subtype.val hsame).trans hh'.symm
    exact Subtype.ext (mul_right_cancel hxy)
  rw [weilFundamentalDomain_integral H hH μ hΔm hbij ν hν hi]
  refine hΔFD.setIntegral_eq hFD fun h x ↦ ?_
  have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
  change uSmooth (π ((h : G) * x), π ((h : G) * x)) = uSmooth (π x, π x)
  rw [map_mul, h1, one_mul]

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.5), p. 508. The first skew-diagonal integral is unchanged by
exchanging the order of integration. -/
theorem integral_diagonalIndentationLift_left_swap :
    (∫ x in D, ∫ h : H, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂countH ∂μ) =
      ∫ h : H, ∫ x in D, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂μ ∂countH := by
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact (integral_integral_swap (integrable_diagonalIndentationLift_left H hH hν hS hb hu hdiag hi))

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.6), p. 508. Translating the second coordinate gives the same
integral as translating the first. -/
theorem integral_diagonalIndentationLift_swap_coordinates :
    (∫ h : H, ∫ x in D, Ψ uSmooth ((h : G)⁻¹ * x, x) ∂μ ∂countH) =
      ∫ h : H, ∫ x in D, Ψ uSmooth (x, (h : G)⁻¹ * x) ∂μ ∂countH := by
  have hweight (x y : G) :
      diagonalIndentationWeight H countH b (x, y) = diagonalIndentationWeight H countH b (y, x) :=
    integral_congr_ae (ae_of_all _ fun k ↦ mul_comm _ _)
  have hswap (h : H) (x : G) :
      Ψ uSmooth ((h : G)⁻¹ * x, x) = Ψ uSmooth (x, (h : G)⁻¹ * x) := by
    have h1 : π (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    have hπ : π ((h : G)⁻¹ * x) = π x := by rw [map_mul, map_inv, h1, inv_one, one_mul]
    simp only [diagonalIndentationLift, Prod.map_apply, hπ, hweight ((h : G)⁻¹ * x) x]
  simp only [hswap]

include hH hν hS hb hu hdiag hi in
/-- Paper: (12.2.2.7), p. 508. The second skew-diagonal integral is unchanged by
exchanging the order of integration. -/
theorem integral_diagonalIndentationLift_right_swap :
    (∫ h : H, ∫ x in D, Ψ uSmooth (x, (h : G)⁻¹ * x) ∂μ ∂countH) =
      ∫ x in D, ∫ h : H, Ψ uSmooth (x, (h : G)⁻¹ * x) ∂countH ∂μ := by
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact (integral_integral_swap (integrable_diagonalIndentationLift_right H hH hν hS hb hu hdiag hi)).symm

include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(3), p. 508. Multiplication by a compactly supported
continuous quotient function commutes almost everywhere with the kernel lift after
pullback of the multiplier. -/
theorem diagonalIndentationLift_mul (ρ : C_c(Q × Q, ℂ)) :
    Ψ (fun p ↦ ρ p * u p) =ᵐ[μ.prod μ] fun p ↦ ρ (q₂ p) * Ψ u p := by
  apply ae_of_all
  intro p
  exact mul_left_comm _ _ _

/-- Weil's formula bounds the pushforward of a compact restriction by a multiple of the
restricted quotient measure. -/
private theorem ae_tendsto_diagonalIndentationLift_average_map_le
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    [DiscreteTopology H] (hH : IsClosed (H : Set G))
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ Measure.count ν) {K : Set G} (hK : IsCompact K) :
    ∃ N : ℝ≥0∞, N ≠ ∞ ∧
      (μ.restrict K).map (QuotientGroup.mk' H) ≤
        N • ν.restrict (QuotientGroup.mk' H '' K) := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : IsClosed (H : Set G) := hH
  let : ν.IsHaarMeasure := hν.1
  let : (Measure.count : Measure H).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let qmap : G → G ⧸ H := QuotientGroup.mk' H
  have hqmap : Measurable qmap := QuotientGroup.continuous_mk.measurable
  let B : Set H := (Subtype.val : H → G) ⁻¹' (K⁻¹ * K)
  have hB : B.Finite := (hH.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hK.inv.mul hK)).finite_of_discrete
  have hBfin : Measure.count B ≠ ∞ := (Measure.count_apply_lt_top.mpr hB).ne
  refine ⟨Measure.count B, hBfin, ?_⟩
  have hπK : IsCompact (qmap '' K) := hK.image QuotientGroup.continuous_mk
  have hcount (x : G) : Measure.count {h : H | x * (h : G) ∈ K} ≤ Measure.count B := by
    rcases eq_empty_or_nonempty {h : H | x * (h : G) ∈ K} with he | ⟨h0, hh0⟩
    · simp [he]
    · calc _ ≤ Measure.count ((fun h ↦ h0 * h) '' B) := measure_mono ?_
        _ = _ := Measure.count_injective_image (mul_right_injective h0) B
      intro h hh
      refine ⟨h0⁻¹ * h, ?_, by simp⟩
      change ((h0 : G)⁻¹ * (h : G)) ∈ K⁻¹ * K
      refine ⟨(x * h0)⁻¹, by simpa using hh0, x * h, hh, ?_⟩
      simp only [mul_inv_rev]
      rw [mul_assoc, inv_mul_cancel_left]
  have hquot (q : G ⧸ H) (h : H) : qmap (q.out * (h : G)) = q := by
    have hh : qmap (h : G) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    change (QuotientGroup.mk' H) (q.out * (h : G)) = q
    dsimp only [qmap] at hh
    rw [map_mul, hh, mul_one]
    exact Quotient.out_eq' q
  rw [Measure.le_iff]
  intro S hS
  rw [Measure.map_apply hqmap hS, Measure.restrict_apply (hqmap hS), smul_apply,
    Measure.restrict_apply hS, smul_eq_mul]
  let E := qmap ⁻¹' S ∩ K
  have hE : MeasurableSet E := (hqmap hS).inter hK.isClosed.measurableSet
  let f : G → ℂ := E.indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator hE
  have hfib (q : G ⧸ H) : (∫⁻ h : H, ‖f (q.out * (h : G))‖ₑ ∂Measure.count) ≤
      (S ∩ qmap '' K).indicator (fun _ ↦ Measure.count B) q := by
    by_cases hq : q ∈ S ∩ qmap '' K
    · rw [indicator_of_mem hq]
      have hmeasK : MeasurableSet {h : H | q.out * (h : G) ∈ K} :=
        hK.isClosed.measurableSet.preimage
          (continuous_const.mul continuous_subtype_val).measurable
      calc _ ≤ ∫⁻ h : H, {h : H | q.out * (h : G) ∈ K}.indicator 1 h ∂Measure.count := by
            refine lintegral_mono fun h ↦ ?_
            by_cases hy : q.out * (h : G) ∈ E
            · have hyK : q.out * (h : G) ∈ K := (show _ ∈ qmap ⁻¹' S ∩ K from hy).2
              simp [f, hy, hyK]
            · simp [f, hy]
        _ = Measure.count {h : H | q.out * (h : G) ∈ K} := lintegral_indicator_one hmeasK
        _ ≤ _ := hcount _
    · rw [indicator_of_notMem hq]
      have hz (h : H) : f (q.out * (h : G)) = 0 := by
        refine indicator_of_notMem (fun hy ↦ ?_) _
        obtain ⟨hy1, hy2⟩ := (show _ ∈ qmap ⁻¹' S ∩ K from hy)
        rw [mem_preimage, hquot q h] at hy1
        exact hq ⟨hy1, q.out * (h : G), hy2, hquot q h⟩
      simp [hz]
  have hlint : (∫⁻ q, ∫⁻ h : H, ‖f (q.out * (h : G))‖ₑ ∂Measure.count ∂ν) ≤
      Measure.count B * ν (S ∩ qmap '' K) :=
    (lintegral_mono hfib).trans
      (lintegral_indicator_const (hS.inter hπK.isClosed.measurableSet) _).le
  have hfin : (∫⁻ q, ∫⁻ h : H, ‖f (q.out * (h : G))‖₊ ∂Measure.count ∂ν) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq_of_le ?_ hlint) (ENNReal.mul_lt_top hBfin.lt_top
      ((measure_mono inter_subset_right).trans_lt hπK.measure_lt_top))
    simp only [eNorm_eq_nnNorm]
  obtain ⟨-, he⟩ := integrable_of_weilNormIntegral H hH μ Measure.count ν hν hf hfin
  have hμE : μ E < ∞ := (measure_mono inter_subset_right).trans_lt hK.measure_lt_top
  calc μ E = ‖∫ x, f x ∂μ‖ₑ := by
        rw [integral_indicator_const _ hE]
        simp only [Measure.real, Complex.real_smul, mul_one]
        rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hμE.ne]
    _ = ‖∫ q, lcaCosetIntegral H Measure.count f q ∂ν‖ₑ := by rw [he]
    _ ≤ ∫⁻ q, ‖lcaCosetIntegral H Measure.count f q‖ₑ ∂ν := eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ q, ∫⁻ h : H, ‖f (q.out * (h : G))‖ₑ ∂Measure.count ∂ν :=
        lintegral_mono fun q ↦ eNorm_integral_le_lintegral_eNorm _
    _ ≤ _ := hlint


/-- Termwise squares of a D′-sequence form a D′-sequence for product Haar measure. -/
private theorem ae_tendsto_diagonalIndentationLift_average_prodSeq
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] {m : Measure A} [m.IsHaarMeasure]
    {V : ℕ → Set A} (hV : IsDPrimeSequence m V) :
    IsDPrimeSequence (m.prod m) (fun n ↦ V n ×ˢ V n) := by
  have rectSeq [mA : MeasurableSpace (A × A)] (hm : mA = borel _)
      (η : Measure (A × A)) [η.IsHaarMeasure]
      (hrect : ∀ s t : Set A, MeasurableSet s → MeasurableSet t → η (s ×ˢ t) = m s * m t) :
      IsDPrimeSequence η (fun n ↦ V n ×ˢ V n) := by
    subst mA
    exact IsDPrimeSequence.prod hrect hV hV
  exact rectSeq BorelSpace.measurable_eq _ (fun s t _ _ ↦ Measure.prod_prod s t)

/-- The pullback of a locally integrable quotient kernel, times the continuous averaged
weight, is locally integrable for product Haar measure. -/
private theorem ae_tendsto_diagonalIndentationLift_average_locallyIntegrable
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    [DiscreteTopology H] (hH : IsClosed (H : Set G))
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ Measure.count ν) {b : G → ℝ}
    (hw : Continuous (diagonalIndentationWeight H Measure.count b))
    {u : (G ⧸ H) × (G ⧸ H) → ℂ} (hu : LocallyIntegrable u (ν.prod ν)) :
    LocallyIntegrable (diagonalIndentationLift H Measure.count b u) (μ.prod μ) := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : IsClosed (H : Set G) := hH
  let : ν.IsHaarMeasure := hν.1
  have hqm : Measurable (QuotientGroup.mk' H) := QuotientGroup.continuous_mk.measurable
  have hcomp : LocallyIntegrable
      (fun p : G × G ↦ u (Prod.map (QuotientGroup.mk' H) (QuotientGroup.mk' H) p))
      (μ.prod μ) := by
    refine (locallyIntegrable_iff (μ := μ.prod μ)).mpr fun C hC ↦ ?_
    have hC1 : IsCompact (Prod.fst '' C) := hC.image continuous_fst
    have hC2 : IsCompact (Prod.snd '' C) := hC.image continuous_snd
    obtain ⟨N1, hN1, h1⟩ := ae_tendsto_diagonalIndentationLift_average_map_le H hH μ ν hν hC1
    obtain ⟨N2, hN2, h2⟩ := ae_tendsto_diagonalIndentationLift_average_map_le H hH μ ν hν hC2
    refine IntegrableOn.mono_set ?_ (subset_prod (s := C))
    rw [IntegrableOn, ← Measure.prod_restrict]
    have hR : IntegrableOn u
        ((QuotientGroup.mk' H '' (Prod.fst '' C)) ×ˢ (QuotientGroup.mk' H '' (Prod.snd '' C)))
        (ν.prod ν) :=
      hu.integrableOn_isCompact
        ((hC1.image QuotientGroup.continuous_mk).prod (hC2.image QuotientGroup.continuous_mk))
    have hmap : Integrable u ((((μ.restrict (Prod.fst '' C)).prod
        (μ.restrict (Prod.snd '' C)))).map
          (Prod.map (QuotientGroup.mk' H) (QuotientGroup.mk' H))) := by
      rw [← Measure.map_prod_map _ _ hqm hqm]
      refine (hR.smul_measure (ENNReal.mul_ne_top hN1 hN2)).mono_measure ?_
      calc _ ≤ (N1 • ν.restrict (QuotientGroup.mk' H '' (Prod.fst '' C))).prod
            (N2 • ν.restrict (QuotientGroup.mk' H '' (Prod.snd '' C))) :=
            Measure.prod_mono h1 h2
        _ = _ := by
          rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict, smul_smul]
    exact hmap.comp_measurable (hqm.prodMap hqm)
  refine (hcomp.continuous_smul (hw.comp continuous_id)).congr (ae_of_all _ fun p ↦ ?_)
  simp [diagonalIndentationLift, Complex.real_smul]


-- TODO(paper-gap): The continuous multiplier step on p. 511 applies Corollary
-- A.5.4.3 at every regular point. The printed equivalence fails (ERRATA R8).
include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(4), p. 509. On product-Haar-almost every pair,
the averages of the lifted kernel converge to the lift of the quotient smoothening. -/
theorem ae_tendsto_diagonalIndentationLift_average :
    ∀ᵐ p ∂μ.prod μ, Tendsto (fun n ↦
      dSequenceAverage (μ.prod μ) (U n ×ˢ U n) (Ψ u) p) atTop (𝓝 (Ψ uSmooth p)) := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : IsClosed (H : Set G) := hH
  let : ν.IsHaarMeasure := hν.1
  have hq := aemeasurable_diagonalIndentationLift_quotient_qmp H hH μ ν hν
  have hseqQ := ae_tendsto_diagonalIndentationLift_average_prodSeq
    (IsDiagonalIndentationSituation.quotient H hH hν hS)
  have hloc := ae_tendsto_diagonalIndentationLift_average_locallyIntegrable H hH μ ν hν
    (continuous_diagonalIndentationWeight H hH hν hS hb) hu
  have hsmooth : ∀ᵐ y ∂ν.prod ν, uSmooth y = u y := by
    filter_upwards [ae_tendsto_dSequenceAverage hseqQ hu] with y hy
    have hreg : y ∈ dSequenceRegularSet (ν.prod ν) (fun n ↦ Ū n ×ˢ Ū n) u := ⟨u y, hy⟩
    simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg,
      dSequenceSmoothening] using hy.limUnder_eq
  filter_upwards [ae_tendsto_dSequenceAverage
    (ae_tendsto_diagonalIndentationLift_average_prodSeq hS.2.1) hloc,
    (hq.prodMap hq).ae hsmooth] with p hp hpu
  simpa only [diagonalIndentationLift, hpu] using hp

include hH hν hS hb hu in
/-- Paper: Proposition 12.2.2.2(4), p. 509. Regularity of a pair for the lifted kernel
agrees with regularity of its quotient pair for product-Haar-almost every pair.
Deviation: Product-almost-everywhere equivalence replaces the printed every-pair claim. -/
theorem ae_diagonalIndentationLift_regular_iff :
    ∀ᵐ p ∂μ.prod μ,
      p ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) (Ψ u) ↔
        q₂ p ∈ dSequenceRegularSet (ν.prod ν) (fun n ↦ Ū n ×ˢ Ū n) u := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : IsClosed (H : Set G) := hH
  let : ν.IsHaarMeasure := hν.1
  have hq := aemeasurable_diagonalIndentationLift_quotient_qmp H hH μ ν hν
  have hseqQ := ae_tendsto_diagonalIndentationLift_average_prodSeq
    (IsDiagonalIndentationSituation.quotient H hH hν hS)
  have hloc := ae_tendsto_diagonalIndentationLift_average_locallyIntegrable H hH μ ν hν
    (continuous_diagonalIndentationWeight H hH hν hS hb) hu
  filter_upwards [ae_tendsto_dSequenceAverage
    (ae_tendsto_diagonalIndentationLift_average_prodSeq hS.2.1) hloc,
    (hq.prodMap hq).ae (mem_ae_iff.mpr (measure_compl_dSequenceRegularSet hseqQ hu))]
    with p hp hpq
  exact iff_of_true ⟨_, hp⟩ hpq

-- Remark 12.2.2.3, p. 509. Mathlib's AEMeasurable.nullMeasurable and
-- NullMeasurable.aemeasurable identify measurability on the completed source
-- with almost-everywhere measurability on the Borel source for complex functions.

/-- Paper: (12.2.2.26), p. 512. The tail kernel restricts the lifted smoothened
kernel to second coordinates outside the indicated subgroup. -/
def diagonalIndentationTail (μH : Measure H) (b : G → ℝ) (v : Q × Q → ℂ)
    (K : Subgroup G) (p : G × G) : ℂ :=
  ((K : Set G)ᶜ).indicator (fun y ↦ diagonalIndentationLift H μH b v (p.1, y)) p.2

/-- Paper: (12.2.2.26), p. 512. Outside the indicated subgroup in the second
coordinate, the tail kernel equals the lifted kernel. -/
theorem diagonalIndentationTail_of_notMem (μH : Measure H) (b : G → ℝ) (v : Q × Q → ℂ)
    {K : Subgroup G} {x y : G} (hy : y ∉ K) :
    diagonalIndentationTail H μH b v K (x, y) =
      diagonalIndentationLift H μH b v (x, y) := by
  simp [diagonalIndentationTail, hy]

/-- Integrals for the counting measure transported along an injective map whose range
contains the support. -/
private theorem exists_indentation_tendsto_tail_count {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [Countable A] [Countable B] [MeasurableSingletonClass A]
    [MeasurableSingletonClass B] (j : A → B) (hj : Function.Injective j) (f : B → ℝ)
    (hf : ∀ y ∉ range j, f y = 0) (hint : Integrable (fun x ↦ f (j x)) Measure.count) :
    Integrable f Measure.count ∧ (∫ y, f y ∂Measure.count) = ∫ x, f (j x) ∂Measure.count := by
  have hs : Summable fun y ↦ ‖f y‖ :=
    (hj.summable_iff (f := fun y ↦ ‖f y‖) fun y hy ↦ by simp [hf y hy]).mp
      (integrable_count_iff.mp hint)
  have hI : Integrable f Measure.count := integrable_count_iff.mpr hs
  refine ⟨hI, ?_⟩
  rw [integral_countable hI, integral_countable hint]
  simp only [count_real_singleton, one_smul]
  exact (hj.tsum_eq fun y hy ↦ by_contra fun h ↦ hy (hf y h)).symm

/-- Extension by zero of an indentation along an open embedding of groups whose range
meets every coset of the subgroup. -/
private theorem exists_indentation_tendsto_tail_extend {L A : Type*} [CommGroup L]
    [TopologicalSpace L] [IsTopologicalGroup L] [MeasurableSpace L]
    [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [MeasurableSpace A]
    (HL : Subgroup L) (HA : Subgroup A) [Countable HL] [Countable HA]
    [MeasurableSingletonClass HL] [MeasurableSingletonClass HA]
    (hHL : IsClosed (HL : Set L)) (ι : A →* L) (hι : IsOpenEmbedding ι)
    (hHA : ∀ a, a ∈ HA ↔ ι a ∈ HL) (c : L → ℝ) (u : A → ℝ) (hc : Continuous c)
    (hcu : ∀ a, c (ι a) = u a) (hc0 : ∀ x ∉ range ι, c x = 0)
    (hcover : ∀ x, ∃ h ∈ HL, h⁻¹ * x ∈ range ι) (hu : IsIndentation HA Measure.count u) :
    IsIndentation HL Measure.count c := by
  have : IsClosed (HL : Set L) := hHL
  have hRc : IsClosed (range ι) := by
    have h := Subgroup.isClosed_of_isOpen ι.range (by simpa using hι.isOpen_range)
    simpa using h
  have hsuppR : tsupport c ⊆ range ι :=
    closure_minimal (fun x hx ↦ by_contra fun h ↦ hx (hc0 x h)) hRc
  have htsupp : ι ⁻¹' tsupport c = tsupport u := by
    rw [tsupport, hι.isOpenMap.preimage_closure_eq_closure_preimage hι.continuous]
    congr 1
    ext a
    simp [hcu]
  refine ⟨hc, fun x ↦ ?_, fun K hK ↦ ?_, fun x ↦ ?_⟩
  · by_cases hx : x ∈ range ι
    · obtain ⟨a, rfl⟩ := hx
      rw [hcu]
      exact hu.2.1 a
    · rw [hc0 x hx]
  · have hπ : Continuous (QuotientGroup.mk' HL) := continuous_quot_mk
    have hcov : K ⊆ ⋃ k : L, (fun z ↦ k * z) '' range ι := fun k _ ↦
      mem_iUnion.2 ⟨k, 1, ⟨1, map_one ι⟩, mul_one _⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover _
      (fun k ↦ isOpenMap_mul_left (k : L) _ hι.isOpen_range) hcov
    choose hk hhk hk' using hcover
    let Kk : L → Set A := fun k ↦
      ι ⁻¹' ((fun z ↦ (hk k)⁻¹ * z) '' (K ∩ (fun z ↦ (k : L) * z) '' range ι))
    have hKk : ∀ k, IsCompact (Kk k) := by
      intro k
      refine hι.isInducing.isCompact_preimage' ?_ ?_
      · refine (hK.inter_right ?_).image (continuous_const.mul continuous_id)
        exact (Homeomorph.mulLeft (k : L)).isClosedMap _ hRc
      · rintro _ ⟨_, ⟨-, _, ⟨b', rfl⟩, rfl⟩, rfl⟩
        obtain ⟨a', ha'⟩ := hk' k
        exact ⟨a' * b', by rw [map_mul, ha', mul_assoc]⟩
    have hsub : tsupport c ∩ QuotientGroup.mk' HL ⁻¹' (QuotientGroup.mk' HL '' K) ⊆
        ⋃ k ∈ t, ι '' (tsupport u ∩ QuotientGroup.mk' HA ⁻¹' (QuotientGroup.mk' HA '' Kk k)) := by
      rintro y ⟨hy, z, hzK, hzy⟩
      obtain ⟨a, rfl⟩ := hsuppR hy
      obtain ⟨k, hkt, hzk⟩ := mem_iUnion₂.1 (ht hzK)
      obtain ⟨_, ⟨b', rfl⟩, rfl⟩ := hzk
      obtain ⟨a', ha'⟩ := hk' k
      refine mem_iUnion₂.2 ⟨k, hkt, a, ⟨?_, a' * b', ?_, ?_⟩, rfl⟩
      · rw [← htsupp]
        exact hy
      · exact ⟨(k : L) * ι b', ⟨hzK, ι b', ⟨b', rfl⟩, rfl⟩, by rw [map_mul, ha', mul_assoc]⟩
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hHA]
        have h1 := HL.mul_mem (hhk k) (QuotientGroup.eq.mp hzy)
        convert h1 using 1
        rw [map_mul, map_inv, map_mul, ha']
        simp only [mul_inv_rev, inv_inv]
        ac_rfl
    refine (t.isCompact_biUnion fun k _ ↦ ((hu.2.2.1 _ (hKk k)).image hι.continuous))
      |>.of_isClosed_subset ?_ hsub
    exact (isClosed_tsupport c).inter
      ((hK.image hπ).isClosed.preimage hπ)
  · obtain ⟨h₀, hh₀, a₀, ha₀⟩ := hcover x
    let j : HA → HL := fun a ↦ ⟨h₀ * ι a, HL.mul_mem hh₀ ((hHA a).1 a.2)⟩
    have hj : Function.Injective j := fun a b hab ↦
      Subtype.ext (hι.injective (mul_left_cancel (congrArg Subtype.val hab)))
    have hval (a : HA) : c ((j a : L)⁻¹ * x) = u ((a : A)⁻¹ * a₀) := by
      rw [← hcu, map_mul, map_inv, ha₀]
      simp only [j, mul_inv_rev]
      rw [mul_assoc]
    have hf : ∀ h ∉ range j, c ((h : L)⁻¹ * x) = 0 := by
      intro h hh
      by_contra hne
      obtain ⟨a, ha⟩ : (h : L)⁻¹ * x ∈ range ι := by_contra fun h' ↦ hne (hc0 _ h')
      have hmem : a₀ * a⁻¹ ∈ HA := by
        rw [hHA, map_mul, map_inv, ha₀, ha]
        convert HL.mul_mem (HL.inv_mem hh₀) h.2 using 1
        group
      refine hh ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
      simp only [j, map_mul, map_inv, ha₀, ha]
      group
    obtain ⟨hint, heq⟩ := hu.2.2.2 a₀
    have key := exists_indentation_tendsto_tail_count j hj (fun h : HL ↦ c ((h : L)⁻¹ * x)) hf
      (by simpa only [hval] using hint)
    simp only [hval] at key
    exact ⟨key.1, key.2.trans heq⟩

-- TODO(paper-gap): The closing citation on p. 513 refers to the tail definition
-- (12.2.2.26); the convergence claim is (12.2.2.27).
-- TODO(paper-gap): In (12.2.2.31), u₁ is only defined on G₀, but the inner integral
-- evaluates u₁(h⁻¹ x) for arbitrary x in G. It needs a fibre representative in G₀.
include hH hν hS hu hdiag hi in
/-- Paper: Proposition 12.2.2.4, p. 512. For an exhaustive filtration by open
subgroups with cyclic infinite successive quotients and a common fundamental domain in
the first stage, there is a compatible indentation whose integrated skew-diagonal tails
tend to zero. On each stage the indicator times the indentation is its restriction.
Deviation: The absolute integrability of each tail is explicit, as in the proof. -/
theorem exists_indentation_tendsto_tail (K : ℕ → Subgroup G)
    (hKopen : ∀ n, IsOpen (K n : Set G)) (hKmono : Monotone K)
    (hKexhaust : (⋃ n, (K n : Set G)) = univ) (hD₀ : D ⊆ (K 0 : Set G))
    (hDk : ∀ n, IsIndentationFundamentalDomain (H.comap (K n).subtype)
      (μ.comap (Subtype.val : K n → G)) ((Subtype.val : K n → G) ⁻¹' D))
    (hKrank : ∀ n, Nonempty
      ((K (n + 1) ⧸ (K n).comap (K (n + 1)).subtype) ≃* Multiplicative ℤ)) :
    ∃ c : G → ℝ, IsIndentation H countH c ∧
      (∀ n, IsIndentation (H.comap (K n).subtype) Measure.count (fun x : K n ↦ c x)) ∧
      (∀ n, Integrable (fun p : G × H ↦
        diagonalIndentationTail H countH c uSmooth (K n) (p.1, (p.2 : G)⁻¹ * p.1))
          ((μ.restrict D).prod countH)) ∧
      Tendsto (fun n ↦ ∫ x in D, ∫ h : H,
        diagonalIndentationTail H countH c uSmooth (K n) (x, (h : G)⁻¹ * x) ∂countH ∂μ)
          atTop (𝓝 0) := by
  -- the stage-wise fundamental domains and the rank condition are not needed
  have _ := hDk
  have _ := hKrank
  classical
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hK0c : IsClosed (K 0 : Set G) := Subgroup.isClosed_of_isOpen _ (hKopen 0)
  have hcover : ∀ x : G, ∃ h ∈ H, h⁻¹ * x ∈ (K 0 : Set G) := by
    intro x
    obtain ⟨a, ha, -⟩ := hS.1.2.1 x
    refine ⟨(a : G)⁻¹, H.inv_mem a.2, ?_⟩
    rw [inv_inv]
    exact hD₀ ha
  let H₀ : Subgroup (K 0) := H.comap (K 0).subtype
  let jH : H₀ → H := fun h ↦ ⟨h.1.1, h.2⟩
  have hjH : Function.Injective jH := fun a b hab ↦
    Subtype.ext (Subtype.ext (congrArg (fun h : H ↦ (h : G)) hab))
  have : LocallyCompactSpace (K 0) := (hKopen 0).isOpenEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (K 0) :=
    (hKopen 0).isOpenEmbedding_subtypeVal.isInducing.secondCountableTopology
  have : DiscreteTopology H₀ := DiscreteTopology.of_continuous_injective
    (f := jH) (by fun_prop) hjH
  have : Countable H₀ := hjH.countable
  have : (Measure.count : Measure H₀).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  obtain ⟨u₁, hu₁⟩ := exists_indentation H₀ (hH.preimage continuous_subtype_val)
    (Measure.count : Measure H₀)
  let c : G → ℝ := fun x ↦ if hx : x ∈ K 0 then u₁ ⟨x, hx⟩ else 0
  have hcK (x : K 0) : c x = u₁ x := by simp [c]
  have hc0 (x : G) (hx : x ∉ K 0) : c x = 0 := by simp [c, hx]
  have hcont : Continuous c := by
    refine continuous_iff_continuousAt.2 fun x ↦ ?_
    by_cases hx : x ∈ K 0
    · have h1 : ContinuousAt (c ∘ Subtype.val) (⟨x, hx⟩ : K 0) := by
        have : c ∘ Subtype.val = u₁ := funext hcK
        rw [this]
        exact hu₁.1.continuousAt
      exact (hKopen 0).isOpenEmbedding_subtypeVal.continuousAt_iff.1 h1
    · refine continuousAt_const.congr (f := fun _ ↦ (0 : ℝ)) ?_
      filter_upwards [hK0c.isOpen_compl.mem_nhds hx] with y hy
      exact (hc0 y hy).symm
  have hc : IsIndentation H countH c := by
    refine exists_indentation_tendsto_tail_extend H H₀ hH (K 0).subtype
      (hKopen 0).isOpenEmbedding_subtypeVal (fun a ↦ Iff.rfl) c u₁ hcont hcK
      (fun x hx ↦ hc0 x fun hx0 ↦ hx ⟨⟨x, hx0⟩, rfl⟩) (fun x ↦ ?_) hu₁
    obtain ⟨h, hh, hx⟩ := hcover x
    exact ⟨h, hh, ⟨⟨_, hx⟩, rfl⟩⟩
  have hrestrict : ∀ n, IsIndentation (H.comap (K n).subtype) Measure.count
      (fun x : K n ↦ c x) := by
    intro n
    have hle : K 0 ≤ K n := hKmono (Nat.zero_le n)
    let ι : K 0 →* K n := Subgroup.inclusion hle
    have hι : IsOpenEmbedding ι := by
      rw [← IsOpenEmbedding.of_comp_iff ι (hKopen n).isOpenEmbedding_subtypeVal]
      exact (hKopen 0).isOpenEmbedding_subtypeVal
    let jn : H.comap (K n).subtype → H := fun h ↦ ⟨h.1.1, h.2⟩
    have hjn : Function.Injective jn := fun a b hab ↦
      Subtype.ext (Subtype.ext (congrArg (fun h : H ↦ (h : G)) hab))
    have : Countable (H.comap (K n).subtype) := hjn.countable
    refine exists_indentation_tendsto_tail_extend (H.comap (K n).subtype) H₀
      (hH.preimage continuous_subtype_val) ι hι (fun a ↦ Iff.rfl) _ u₁
      (hcont.comp continuous_subtype_val) (fun a ↦ hcK a) ?_ ?_ hu₁
    · intro x hx
      exact hc0 x fun hx0 ↦ hx ⟨⟨x, hx0⟩, rfl⟩
    · intro x
      obtain ⟨h, hh, hx⟩ := hcover x
      have hhn : h ∈ K n := by
        have := (K n).mul_mem x.2 ((K n).inv_mem (hle hx))
        simpa using this
      exact ⟨⟨h, hhn⟩, hh, ⟨⟨_, hx⟩, rfl⟩⟩
  have hF := integrable_diagonalIndentationLift_right H hH hν hS hc hu hdiag hi
  have htail (n : ℕ) : (fun p : G × H ↦
      diagonalIndentationTail H countH c uSmooth (K n) (p.1, (p.2 : G)⁻¹ * p.1)) =
      ((fun p : G × H ↦ (p.2 : G)⁻¹ * p.1) ⁻¹' (K n : Set G)ᶜ).indicator
        (fun p ↦ diagonalIndentationLift H countH c uSmooth (p.1, (p.2 : G)⁻¹ * p.1)) := by
    funext p
    simp only [diagonalIndentationTail, Set.indicator_apply, mem_preimage]
  have hmeas (n : ℕ) :
      MeasurableSet ((fun p : G × H ↦ (p.2 : G)⁻¹ * p.1) ⁻¹' (K n : Set G)ᶜ) :=
    ((Subgroup.isClosed_of_isOpen _ (hKopen n)).isOpen_compl.preimage
      (by fun_prop)).measurableSet
  have hint (n : ℕ) : Integrable (fun p : G × H ↦
      diagonalIndentationTail H countH c uSmooth (K n) (p.1, (p.2 : G)⁻¹ * p.1))
        ((μ.restrict D).prod countH) := by
    rw [htail n]
    exact hF.indicator (hmeas n)
  refine ⟨c, hc, hrestrict, hint, ?_⟩
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun n (p : G × H) ↦
      diagonalIndentationTail H countH c uSmooth (K n) (p.1, (p.2 : G)⁻¹ * p.1))
    (f := 0) (μ := (μ.restrict D).prod countH)
    (fun p ↦ ‖diagonalIndentationLift H countH c uSmooth (p.1, (p.2 : G)⁻¹ * p.1)‖)
    (fun n ↦ (hint n).aestronglyMeasurable) hF.norm
    (fun n ↦ ae_of_all _ fun p ↦ by
      simp only [diagonalIndentationTail]
      exact norm_indicator_le_norm_self _ _)
    (ae_of_all _ fun p ↦ by
      obtain ⟨N, hN⟩ := mem_iUnion.1 (hKexhaust.symm ▸ mem_univ ((p.2 : G)⁻¹ * p.1))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have hpn : (p.2 : G)⁻¹ * p.1 ∈ K n := hKmono hn hN
      simp [diagonalIndentationTail, hpn])
  simp only [Pi.zero_apply, integral_zero] at hlim
  refine hlim.congr fun n ↦ ?_
  exact integral_prod _ (hint n)

end Diagonal

end RiemannMasullo
