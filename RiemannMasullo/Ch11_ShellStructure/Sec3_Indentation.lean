module

public import RiemannMasullo.Ch11_ShellStructure.Sec3
public import RiemannMasullo.Ch12_TraceGeometric.Sec2
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.AppD_SchwartzBruhat.Sec1d

/-! # Normalized indentations for the idelic shells of §11.3

Proposition 12.2.2.2, p. 508, sums over all translates. Here the support of the
individual translates gives a pointwise vanishing result for the shells used on p. 520.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal Pointwise

variable {F : Type*} [Field F] [NumberField F]

local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "H𝔽" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "π𝔽" => QuotientGroup.mk' H𝔽
local notation "W(" b ")" => diagonalIndentationWeight H𝔽 Measure.count b
local instance instIdeleMeasurableSpaceSec3Indentation : MeasurableSpace I𝔽 := borel _

/-- Paper: Proposition 12.2.2.2(2), p. 508, as used in (11.3.2.1), p. 495.
For a fixed indentation and a compact set of idele classes, there is one finite set of
places outside which the relative idele of every pair with nonzero weight is a unit.
Deviation: This support bound concerns the individual translates of the normalized lift. -/
theorem diagonalIndentationWeight_unit_outside_finite
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b)
    {K : Set (IdeleClassGroup (𝓞 F) F)} (hK : IsCompact K) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ x y : I𝔽, π𝔽 x ∈ K → π𝔽 y ∈ K →
      W(b) (x, y) ≠ 0 → ∀ v ∉ T, Valued.v ((y / x).val.2 v) = 1 := by
  let := (ideleGroup_topology F).2.1
  let := idele_secondCountable F
  have hH : IsClosed (H𝔽 : Set I𝔽) := (ideleGroup_quotient.{_, 0} F).2.1
  let C := tsupport b ∩ π𝔽 ⁻¹' K
  have hC : IsCompact C := IsIndentation.isCompact_tsupport_inter_preimage H𝔽 hH Measure.count hb hK
  have hcomp := hC.mul hC.inv
  obtain ⟨hmono, hcover⟩ := integralIdeleInsertion_exhaustive F
  obtain ⟨T, hT⟩ := hcomp.elim_directed_cover (fun T ↦ range (integralIdeleInsertion F T))
    (fun T ↦ (integralIdeleInsertion_isOpenEmbedding F T).isOpen_range)
    (fun z _ ↦ mem_iUnion.mpr (hcover z)) hmono.directed_le
  refine ⟨T, fun x y hx hy hw v hv ↦ ?_⟩
  unfold diagonalIndentationWeight at hw
  obtain ⟨k, hk⟩ := exists_ne_zero_of_integral_ne_zero hw
  obtain ⟨hkx, hky⟩ := mul_ne_zero_iff.mp hk
  have hπ : π𝔽 (k : I𝔽) = 1 := (QuotientGroup.eq_one_iff _).mpr k.property
  have hmem (z : I𝔽) (hz : π𝔽 z ∈ K) (hn : b ((k : I𝔽)⁻¹ * z) ≠ 0) :
      (k : I𝔽)⁻¹ * z ∈ C := by
    refine ⟨subset_tsupport b hn, ?_⟩
    change π𝔽 ((k : I𝔽)⁻¹ * z) ∈ K
    rwa [map_mul, map_inv, hπ, inv_one, one_mul]
  have hratio : y / x ∈ C * C⁻¹ :=
    ⟨_, hmem y hy hky, _, inv_mem_inv.mpr (hmem x hx hkx), by
      simpa only [div_eq_mul_inv] using mul_div_mul_left_eq_div y x (k : I𝔽)⁻¹⟩
  have hu := hT hratio
  rw [← sLocalDivisorialStratum_eq_range_integralIdeleInsertion] at hu
  exact hu v hv

/-- Paper: Theorem 11.3.2.1, (11.3.2.1)–(11.3.2.2), p. 495.
If a normalized lift preserves the printed weight's invariance under simultaneous norm
dilation, every pair of equal norm with nonzero weight has relative idele integral and
invertible outside a fixed finite set of places, independent of the norm and the test.
Deviation: This is a necessary restriction on a proposed replacement for (11.3.2.2). -/
theorem diagonalIndentationWeight_normSection_unit_outside_finite
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b)
    (hinv : ∀ (t : ℝ≥0ˣ) (x y : I𝔽), W(b)
      (x * canonicalIdeleNormSection F t, y * canonicalIdeleNormSection F t) = W(b) (x, y)) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ x y : I𝔽, ideleNorm F x = ideleNorm F y →
      W(b) (x, y) ≠ 0 → y / x ∈ sLocalDivisorialStratum F T := by
  have hK : IsCompact ((ideleClassNorm F).ker : Set (IdeleClassGroup (𝓞 F) F)) :=
    isCompact_iff_compactSpace.mpr (ideleClassGroup_finiteness F).2.1
  obtain ⟨T, hT⟩ := diagonalIndentationWeight_unit_outside_finite hb hK
  refine ⟨T, fun x y hxy hw ↦ ?_⟩
  let t := ideleNorm F x
  let z := canonicalIdeleNormSection F t
  have hz : ideleNorm F z = t := canonicalIdeleNormSection_rightInverse F t
  have hmem (w : I𝔽) (h : ideleNorm F w = t) : π𝔽 (w / z) ∈ (ideleClassNorm F).ker := by
    change ideleNorm F (w / z) = 1
    rw [map_div, h, hz, div_self']
  have he := hinv t (x / z) (y / z)
  change W(b) (x / z * z, y / z * z) = _ at he
  simp only [div_mul_cancel] at he
  have hu := hT (x / z) (y / z) (hmem x rfl) (hmem y hxy.symm) (he ▸ hw)
  rwa [div_div_div_cancel_right] at hu

variable (F) in
/-- Paper: (11.3.2.2), p. 495, and Definition 12.2.1.3, p. 506. There is a normalized
principal-idele indentation invariant under norm dilation.
Reconstruction: Restrict any indentation to norm one and extend it constantly along the
canonical norm section. -/
theorem exists_normSection_invariant_indentation :
    ∃ b : I𝔽 → ℝ, IsIndentation H𝔽 Measure.count b ∧
      ∀ (t : ℝ≥0ˣ) (x : I𝔽), b (x * canonicalIdeleNormSection F t) = b x := by
  classical
  let := (ideleGroup_topology F).1
  let := (ideleGroup_topology F).2.1
  let := idele_secondCountable F
  let : BorelSpace I𝔽 := ⟨rfl⟩
  have hH : IsClosed (H𝔽 : Set I𝔽) := (ideleGroup_quotient.{_, 0} F).2.1
  let : DiscreteTopology H𝔽 := (isDiscrete_iff_discreteTopology.mp
    (ideleGroup_quotient.{_, 0} F).2.2.1)
  let : (Measure.count : Measure H𝔽).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ h ↦ Measure.count_apply_lt_top.mpr h.finite_of_discrete
      open_pos := fun _ _ h ↦ Measure.count_ne_zero h }
  obtain ⟨a, ha⟩ := exists_indentation H𝔽 hH Measure.count
  let τ := canonicalIdeleNormSection F
  let r (x : I𝔽) := x / τ (ideleNorm F x)
  have hτ := canonicalIdeleNormSection_rightInverse F
  have hτn := (canonicalIdeleNormSection_continuous F).comp (ideleGroup_topology F).2.2.2.2.1
  have hr : Continuous r := continuous_id.div' hτn
  let b := a ∘ r
  have hinv (t : ℝ≥0ˣ) (x : I𝔽) : b (x * τ t) = b x := by
    change a (_ / _) = a (_ / _)
    rw [map_mul (ideleNorm F), hτ, map_mul τ, mul_div_mul_right_eq_div]
  let C := tsupport a ∩ π𝔽 ⁻¹' ((ideleClassNorm F).ker : Set _)
  have hC : IsCompact C := IsIndentation.isCompact_tsupport_inter_preimage H𝔽 hH Measure.count ha
    (isCompact_iff_compactSpace.mpr (ideleClassGroup_finiteness F).2.1)
  have hsub : tsupport b ⊆ r ⁻¹' C := by
    refine closure_minimal (fun x hx ↦ ⟨subset_tsupport a hx, ?_⟩) (hC.isClosed.preimage hr)
    change ideleNorm F (x / τ (ideleNorm F x)) = 1
    rw [map_div, hτ, div_self']
  have hb : IsIndentation H𝔽 Measure.count b := by
    refine ⟨ha.1.comp hr, fun x ↦ ha.2.1 _, fun K hK ↦ ?_, fun x ↦ ?_⟩
    · have hπ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.1.continuous
      let : T2Space (IdeleClassGroup (𝓞 F) F) := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
      refine (hC.mul (hK.image hτn)).of_isClosed_subset
        ((isClosed_tsupport _).inter ((hK.image hπ).isClosed.preimage hπ)) ?_
      rintro z ⟨hz, k, hk, he⟩
      have hn : ideleNorm F k = ideleNorm F z := congrArg (ideleClassNorm F) he
      exact ⟨r z, hsub hz, τ (ideleNorm F k), ⟨k, hk, rfl⟩, by
        rw [hn]; exact div_mul_cancel _ _⟩
    · have he (k : H𝔽) : b ((k : I𝔽)⁻¹ * x) = a ((k : I𝔽)⁻¹ * r x) := by
        have hn : ideleNorm F (k : I𝔽) = 1 := (ideleNorm_spec F).2 k.property
        simp [b, r, map_mul, map_inv, hn, div_eq_mul_inv, mul_assoc]
      simpa only [he] using ha.2.2.2 (r x)
  exact ⟨b, hb, hinv⟩

variable (F) in
/-- Paper: Theorem 12.5.1.1, p. 520, invoking (11.3.2.1), p. 495. For one normalized
indentation, after enlarging the saturated base to contain a fixed finite set of places,
every off-base shell of the lifted quotient kernel vanishes on the sampled pairs.
Reconstruction: Use the canonical norm section and the normalized lift of (12.2.2.2).
This applies to (11.3.2.1) for the canonical section, and to representatives of the same
quotient point when the first representative is a unit outside the base.
Identifying the retained part with the arithmetic trace requires a separate argument. -/
theorem exists_indentation_divisorialKernelDifference_eq_zero :
    ∃ (b : I𝔽 → ℝ) (T : Finset (HeightOneSpectrum (𝓞 F))), IsIndentation H𝔽 Measure.count b ∧
      ∀ S, T ⊆ S → (∀ v ∈ S, ∀ w : HeightOneSpectrum (𝓞 F),
        w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
      ∀ k (K : (IdeleClassGroup (𝓞 F) F) × (IdeleClassGroup (𝓞 F) F) → ℂ)
        (x y : I𝔽), x ∈ sLocalDivisorialStratum F S → ideleNorm F x = ideleNorm F y →
        divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K) (x, y) = 0 := by
  obtain ⟨b, hb, hinv⟩ := exists_normSection_invariant_indentation F
  obtain ⟨T, hT⟩ := diagonalIndentationWeight_normSection_unit_outside_finite hb (by
    intro t x y
    unfold diagonalIndentationWeight
    simp only [← mul_assoc, hinv])
  refine ⟨b, T, hb, fun S hTS hS k K x y hx hn ↦ ?_⟩
  by_cases hw : W(b) (x, y) = 0
  · simp only [divisorialKernelDifference, diagonalIndentationLift, hw, Complex.ofReal_zero,
      zero_mul, mul_zero]
  · have hr : y / x ∈ sLocalDivisorialStratum F S :=
      fun v hv ↦ hT x y hn hw v (fun h ↦ hv (hTS h))
    have hy : y ∈ sLocalDivisorialStratum F S := by
      rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion] at hx hr ⊢
      exact div_mul_cancel y x ▸ (integralIdeleInsertion F S).range.mul_mem hr hx
    rw [← iInter_primaryDivisorialStratum S hS] at hy
    have hall := mem_iInter.mp hy
    simp only [divisorialKernelDifference, divisorialIndicator_eq_indicator,
      indicator_of_mem (hall _), sub_self, zero_mul]

variable (F) in
/-- Paper: the sampled left-hand side of (11.3.2.1), p. 495, as used on p. 520.
For every continuous norm section, the off-base shell sum for the normalized lift
vanishes once the saturated base contains a fixed finite set.
Reconstruction: Use the normalized indentation lift instead of the printed weight.
This does not identify the sampled sum or the retained part with the arithmetic trace. -/
theorem exists_indentation_divisorialSkewIntegral_eq_zero :
    ∃ (b : I𝔽 → ℝ) (T : Finset (HeightOneSpectrum (𝓞 F))), IsIndentation H𝔽 Measure.count b ∧
      ∀ S, T ⊆ S → (∀ v ∈ S, ∀ w : HeightOneSpectrum (𝓞 F),
        w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) →
      ∀ (τ : ℝ≥0ˣ →* I𝔽), Continuous τ →
      ∀ (E : Set (ideleNorm F).ker) k
        (K : (IdeleClassGroup (𝓞 F) F) × (IdeleClassGroup (𝓞 F) F) → ℂ),
        (∑' ξ : Fˣ, ∫ t, ∫ g in E,
          divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
            (τ t, IdeleGroup.unitEmbedding (𝓞 F) F ξ * g.val * τ t)
          ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) = 0 := by
  obtain ⟨b, T, hb, hT⟩ := exists_indentation_divisorialKernelDifference_eq_zero F
  refine ⟨b, T, hb, fun S hTS hS τ hτ E k K ↦ ?_⟩
  let U := (integralIdeleInsertion F S).range
  have hU : IsOpen (U : Set I𝔽) := (integralIdeleInsertion_isOpenEmbedding F S).isOpen_range
  have : ConnectedSpace ℝ≥0ˣ := (Real.expOrderIso.toHomeomorph.trans
    (Nonneg.unitsHomeomorphPos ℝ).symm).surjective.connectedSpace (by fun_prop)
  have hpre : IsClopen (τ ⁻¹' (U : Set I𝔽)) :=
    ⟨(U.isClosed_of_isOpen hU).preimage hτ, hU.preimage hτ⟩
  have hmem (t : ℝ≥0ˣ) : τ t ∈ sLocalDivisorialStratum F S := by
    rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion]
    change t ∈ τ ⁻¹' (U : Set I𝔽)
    rw [hpre.eq_univ ⟨1, by change τ 1 ∈ U; rw [map_one]; exact U.one_mem⟩]
    exact mem_univ t
  have hvanish (ξ : Fˣ) (t : ℝ≥0ˣ) (g : (ideleNorm F).ker) :
      divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
        (τ t, IdeleGroup.unitEmbedding (𝓞 F) F ξ * g.val * τ t) = 0 := by
    apply hT S hTS hS k K _ _ (hmem t)
    have hp : ideleNorm F (IdeleGroup.unitEmbedding (𝓞 F) F ξ) = 1 :=
      (ideleNorm_spec F).2 ⟨ξ, rfl⟩
    have hg : ideleNorm F g.val = 1 := g.property
    simp only [map_mul, hp, hg, one_mul]
  simp only [hvanish, integral_zero, tsum_zero]

end RiemannMasullo
