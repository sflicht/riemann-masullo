module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # The geometric part of the projective kernel in Theorem 10.4.3.5 -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

/-- Applying a bounded map to every output of convergent projective rectangles gives a Cauchy net. -/
private theorem cauchy_rectangles_map_output {Z J E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (u : J → E) (v : J → V) (P : V →L[ℂ] V)
    {K : Completion (ProjectiveTensor E V)} (hK : Tendsto (spectralKernelRectangle e N jet u v) atTop (𝓝 K)) :
    Cauchy (Filter.map (spectralKernelRectangle e N jet u (fun i ↦ P (v i))) atTop) := by
  let idE := ContinuousLinearMap.id ℂ E
  let L : ProjectiveTensor E V →L[ℂ] ProjectiveTensor E V :=
    ⟨projectiveTensorMap idE.toLinearMap P.toLinearMap, projectiveTensorMap_continuous idE P⟩
  apply Filter.Tendsto.cauchy_map (a := L.completion K)
  apply ((L.completion.continuous.tendsto K).comp hK).congr
  intro ij
  unfold Function.comp spectralKernelRectangle
  rw [ContinuousLinearMap.completion_apply_coe]
  apply congrArg ((↑) : ProjectiveTensor E V → Completion (ProjectiveTensor E V))
  change projectiveTensorMap idE.toLinearMap P.toLinearMap _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (map_sum (TensorProduct.map idE.toLinearMap P.toLinearMap)
    (fun m : Fin (N z) ↦ u (jet z m) ⊗ₜ[ℂ] v (jet z m)) Finset.univ).trans
    (Finset.sum_congr rfl fun m _ ↦ TensorProduct.map_tmul _ _ _ _)

open scoped ComplexOrder in
/-- The projective gauge of the unit pure tensors controls every zero-neighborhood.
A copy of the private `spectralLineQuotientKernel_tendsto_gauge` of `Sec4b`. -/
private theorem spectralStripGeometricKernel_cauchy_gauge {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (U : Set (ProjectiveTensor X Y)) (hU : U ∈ 𝓝 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ProjectiveTensor X Y,
      gauge (convexHull ℝ (image2 (TensorProduct.tmul ℂ)
        (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))) z < ε → z ∈ U := by
  let B (r s : ℝ) : Set (ProjectiveTensor X Y) :=
    image2 (TensorProduct.tmul ℂ) (Metric.closedBall 0 r) (Metric.closedBall 0 s)
  let : PolynormableSpace ℂ X := (norm_withSeminorms ℂ X).toPolynormableSpace
  let : PolynormableSpace ℂ Y := (norm_withSeminorms ℂ Y).toPolynormableSpace
  let : IsScalarTower ℝ ℂ (ProjectiveTensor X Y) := IsScalarTower.restrictScalars ℝ ℂ _
  let : ContinuousSMul ℂ (ProjectiveTensor X Y) := PolynormableSpace.continuousSMul ℂ _
  let : ContinuousSMul ℝ (ProjectiveTensor X Y) := IsScalarTower.continuousSMul ℂ
  have hb := projectiveTensor_zero_basis (E := X) (F := Y) (Metric.nhds_basis_closedBall (x := (0 : X)))
    (Metric.nhds_basis_closedBall (x := (0 : Y)))
  have hbal : Balanced ℂ (B 1 1) := by
    intro c hc
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    refine ⟨c • x, ?_, y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg x)).trans
      (by simpa using hx)
  have hrect : absConvexHull ℂ (B 1 1) ⊆ convexHull ℝ (B 1 1) := by
    rw [absConvexHull_eq_convexHull_balancedHull, show balancedHull ℂ (B 1 1) = B 1 1 from
      le_antisymm (hbal.balancedHull_subset_of_subset Subset.rfl) (subset_balancedHull ℂ)]
    exact convexHull_min (subset_convexHull ..) (convex_RCLike_iff_convex_real.mpr (convex_convexHull ..))
  have hunit : convexHull ℝ (B 1 1) ∈ 𝓝 (0 : ProjectiveTensor X Y) :=
    Filter.mem_of_superset (hb.mem_of_mem (i := (1, 1)) ⟨one_pos, one_pos⟩) hrect
  obtain ⟨⟨r, s⟩, ⟨hr, hs⟩, hsub⟩ := hb.mem_iff.mp hU
  refine ⟨r * s, mul_pos hr hs, fun z hz ↦ ?_⟩
  obtain ⟨t, ht, htrs, hz⟩ := exists_lt_of_gauge_lt (absorbent_nhds_zero hunit) hz
  apply hsub
  rw [← convexHull_smul] at hz
  refine convexHull_min ?_ (convex_absConvexHull.lift ℝ) hz
  rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  apply subset_absConvexHull
  refine ⟨(t / s : ℝ) • x, ?_, s • y, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (div_nonneg ht.le hs.le)]
    exact (mul_le_of_le_one_right (div_nonneg ht.le hs.le) (by simpa using hx)).trans
      ((div_lt_iff₀ hs).mpr htrs).le
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hs.le]
    exact mul_le_of_le_one_right hs.le (by simpa using hy)
  · rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, div_mul_cancel₀ _ hs.ne']
    rfl

/-- Trace-norm Cauchy rectangles of finite-rank operators give Cauchy tensor rectangles.
A copy of the private `spectralLineQuotientKernel_tendsto_of_traceCauchy` of `Sec4b`. -/
private theorem spectralStripGeometricKernel_cauchy_of_traceCauchy {H Z J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (f : J → StrongDual ℂ H) (e : Z ↪ ℕ × ℕ)
    (N : Z → ℕ) (i : (z : Z) → Fin (N z) → J)
    (hc : SpectralRectanglesTraceCauchy (fun ij ↦ spectralConvolutionFiniteSum A x f
      (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn) N i)) :
    ∃ K, Tendsto (spectralKernelRectangle e N i (fun j ↦ (f j).comp A) x) atTop (𝓝 K) := by
  classical
  let P := ProjectiveTensor (StrongDual ℂ H) H
  let box (ij : ℕ × ℕ) := ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
  let w (ij : ℕ × ℕ) : P := ∑ z ∈ box ij, ∑ m : Fin (N z), (f (i z m)).comp A ⊗ₜ[ℂ] x (i z m)
  have hop (ij) : tensorToFiniteRank (w ij) = spectralConvolutionFiniteSum A x f (box ij) N i := by
    change tensorToFiniteRank (∑ z ∈ box ij, ∑ m : Fin (N z), (f (i z m)).comp A ⊗ₜ[ℂ] x (i z m)) = _
    simp only [map_sum, spectralConvolutionFiniteSum]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro m _
    exact ContinuousLinearMap.ext fun y ↦ tensorToFiniteRank_tmul _ _ y
  obtain ⟨huc, equiv, hval, hnorm⟩ := exists_projectiveTensorCompletion_traceClassIsometry (E := H) (F := H)
  have hcauchy : CauchySeq w := by
    apply (cauchySeq_iff_sub_mem w).mpr
    intro U hU
    obtain ⟨ε, hε, hball⟩ := spectralStripGeometricKernel_cauchy_gauge U hU
    obtain ⟨b, hb⟩ := hc ε hε
    refine ⟨b, fun j hj k hk ↦ hball _ ?_⟩
    obtain ⟨T, hT, hsmall⟩ := hb j k hj hk
    have heq : (equiv ((w j - w k : P) : Completion P)).val = T.val := by
      rw [hval, completedProjectiveTensorToOperators_coe]
      exact (map_sub tensorToFiniteRank (w j : StrongDual ℂ H ⊗[ℂ] H) (w k)).trans
        ((congrArg₂ (· - ·) (hop j) (hop k)).trans hT.symm)
    have hnorm' := (hnorm ((w j - w k : P) : Completion P)).trans (Completion.extension_coe huc _)
    exact hnorm'.symm.trans_lt ((congrArg schattenNorm (Subtype.ext heq)).trans_lt
      ((schattenNorm_one_eq_traceNorm T).trans_lt hsmall))
  exact cauchySeq_tendsto_of_complete
    (UniformContinuous.comp_cauchySeq (Completion.uniformContinuous_coe (α := P)) hcauchy)

/-- In a C*-algebra, positive elements with product zero have square roots with product zero.
The element `√b a √b` is self-adjoint with square zero, so it is zero. -/
private theorem traceClass_blockSums_tails_of_bddAbove_sqrt_mul_sqrt
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = 0) :
    CFC.sqrt a * CFC.sqrt b = 0 := by
  have hba : b * a = 0 := by
    have := congrArg star hab
    rwa [star_mul, star_zero, ha.star_eq, hb.star_eq] at this
  set z := CFC.sqrt b * a * CFC.sqrt b with hz
  have hzsa : star z = z := by
    rw [hz, star_mul, star_mul, (CFC.sqrt_nonneg b).star_eq, ha.star_eq, mul_assoc]
  have hz2 : z * z = 0 := by
    have hsb : CFC.sqrt b * CFC.sqrt b = b := CFC.sqrt_mul_sqrt_self b hb
    calc z * z = CFC.sqrt b * a * (CFC.sqrt b * CFC.sqrt b) * a * CFC.sqrt b := by
          rw [hz]; noncomm_ring
      _ = 0 := by rw [hsb, mul_assoc (CFC.sqrt b * a), hba]; simp
  have hz0 : z = 0 := by
    have h := CStarRing.norm_star_mul_self (x := z)
    rw [hzsa, hz2, norm_zero] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg z])
  set w := CFC.sqrt a * CFC.sqrt b
  have hw : star w * w = z := by
    have hsa : CFC.sqrt a * CFC.sqrt a = a := CFC.sqrt_mul_sqrt_self a ha
    simp only [w, star_mul, (CFC.sqrt_nonneg a).star_eq, (CFC.sqrt_nonneg b).star_eq, hz]
    rw [mul_assoc, ← mul_assoc (CFC.sqrt a), hsa, mul_assoc]
  have h := CStarRing.norm_star_mul_self (x := w)
  rw [hw, hz0, norm_zero] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])

/-- The square root of a sum of positive elements with product zero is the sum of the
square roots. -/
private theorem traceClass_blockSums_tails_of_bddAbove_sqrt_add
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = 0) :
    CFC.sqrt (a + b) = CFC.sqrt a + CFC.sqrt b := by
  have h1 := traceClass_blockSums_tails_of_bddAbove_sqrt_mul_sqrt ha hb hab
  have hba : b * a = 0 := by
    have := congrArg star hab
    rwa [star_mul, star_zero, ha.star_eq, hb.star_eq] at this
  have h2 := traceClass_blockSums_tails_of_bddAbove_sqrt_mul_sqrt hb ha hba
  refine CFC.sqrt_unique ?_ (add_nonneg (CFC.sqrt_nonneg a) (CFC.sqrt_nonneg b))
  rw [add_mul, mul_add, mul_add, h1, h2, CFC.sqrt_mul_sqrt_self a ha,
    CFC.sqrt_mul_sqrt_self b hb, add_zero, zero_add]

/-- The trace norm is additive on operators with orthogonal ranges and orthogonal coranges. -/
private theorem traceClass_blockSums_tails_of_bddAbove_add_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (X Y : nuclearEndomorphisms H)
    (h1 : X.val.adjoint * Y.val = 0) (h2 : X.val * Y.val.adjoint = 0) :
    traceNorm (X + Y) = traceNorm X + traceNorm Y := by
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  have h1' : Y.val.adjoint * X.val = 0 := by
    have := congrArg star h1
    rwa [star_mul, star_zero, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] at this
  have hpos (T : H →L[ℂ] H) : 0 ≤ T.adjoint * T :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self T)
  have hsum : (X + Y).val.adjoint * (X + Y).val =
      X.val.adjoint * X.val + Y.val.adjoint * Y.val := by
    simp only [Submodule.coe_add, map_add, add_mul, mul_add, h1, h1']
    abel
  have hprod : (X.val.adjoint * X.val) * (Y.val.adjoint * Y.val) = 0 := by
    rw [mul_assoc, ← mul_assoc X.val, h2]
    simp
  have hsq : CFC.sqrt ((X + Y).val.adjoint * (X + Y).val) =
      CFC.sqrt (X.val.adjoint * X.val) + CFC.sqrt (Y.val.adjoint * Y.val) := by
    rw [hsum]
    exact traceClass_blockSums_tails_of_bddAbove_sqrt_add (hpos _) (hpos _) hprod
  refine (hasSum_traceNorm_diagonal b (X + Y)).unique
    (((hasSum_traceNorm_diagonal b X).add (hasSum_traceNorm_diagonal b Y)).congr_fun fun i ↦ ?_)
  simp only [hsq, FunLike.coe_add, Pi.add_apply, inner_add_right, Complex.add_re]


/-- The triangle inequality for the trace norm. -/
private theorem traceClass_blockSums_tails_of_bddAbove_add_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T S : nuclearEndomorphisms H) : traceNorm (T + S) ≤ traceNorm T + traceNorm S := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := H)).norm_triangle T S

/-- The trace norm of a difference is at most the sum of the trace norms. -/
private theorem traceClass_blockSums_tails_of_bddAbove_sub_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T S : nuclearEndomorphisms H) : traceNorm (T - S) ≤ traceNorm T + traceNorm S := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hneg : traceNorm (-S) = traceNorm S := by
    have h := (traceNorm_normedSpaceCore (H := H)).norm_smul (-1 : ℂ) S
    simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using h
  rw [sub_eq_add_neg, ← hneg]
  exact traceClass_blockSums_tails_of_bddAbove_add_le _ _

/-- Compression by a projection of norm at most one does not increase the trace norm. -/
private theorem traceClass_blockSums_tails_of_bddAbove_compress_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : H →L[ℂ] H) (hE : ‖E‖ ≤ 1) (T : nuclearEndomorphisms H) :
    traceNorm ⟨E * (T.val * E), mul_mem_nuclearEndomorphisms_left E
      ⟨T.val * E, mul_mem_nuclearEndomorphisms_right E T⟩⟩ ≤ traceNorm T := by
  have h1 := traceNorm_mul_left_le E ⟨T.val * E, mul_mem_nuclearEndomorphisms_right E T⟩
  have h2 := traceNorm_mul_right_le E T
  have h0 : 0 ≤ traceNorm (⟨T.val * E, mul_mem_nuclearEndomorphisms_right E T⟩ :
      nuclearEndomorphisms H) := by
    let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
    exact (traceNorm_normedSpaceCore (H := H)).norm_nonneg _
  have hT : 0 ≤ traceNorm T := by
    let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
    exact (traceNorm_normedSpaceCore (H := H)).norm_nonneg _
  calc _ ≤ ‖E‖ * traceNorm (⟨T.val * E, mul_mem_nuclearEndomorphisms_right E T⟩ :
        nuclearEndomorphisms H) := h1
    _ ≤ 1 * (‖E‖ * traceNorm T) := mul_le_mul hE h2 h0 zero_le_one
    _ ≤ traceNorm T := by nlinarith [norm_nonneg E]

/-- Every nuclear operator is close in trace norm to its compression by the orthogonal
projection onto some finite-dimensional subspace containing a given one. -/
private theorem traceClass_blockSums_tails_of_bddAbove_compress
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (V₀ : Submodule ℂ H)
    [FiniteDimensional ℂ V₀] {δ : ℝ} (hδ : 0 < δ) :
    ∃ V : Submodule ℂ H, ∃ _ : FiniteDimensional ℂ V, V₀ ≤ V ∧
      traceNorm (T - ⟨V.starProjection * (T.val * V.starProjection),
        mul_mem_nuclearEndomorphisms_left _
          ⟨T.val * V.starProjection, mul_mem_nuclearEndomorphisms_right _ T⟩⟩) < δ := by
  obtain ⟨z, hz⟩ := exists_tensorToFiniteRank_traceNorm_sub_lt T (half_pos hδ)
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset z
  let u : StrongDual ℂ H × H → H := fun i ↦ (InnerProductSpace.toDual ℂ H).symm i.1
  let V : Submodule ℂ H := V₀ ⊔ (Submodule.span ℂ (Set.range fun i : S ↦ i.val.2) ⊔
    Submodule.span ℂ (Set.range fun i : S ↦ u i.val))
  have hV : FiniteDimensional ℂ V := by
    have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i : S ↦ i.val.2)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i : S ↦ u i.val)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    infer_instance
  refine ⟨V, hV, le_sup_left, ?_⟩
  let E := V.starProjection
  let F := tensorToFiniteRank (E := H) (F := H) z
  have hFx (x : H) : F x = ∑ i ∈ S, i.1 x • i.2 := by
    simp only [F, hS, map_sum, FunLike.coe_sum, Finset.sum_apply,
      tensorToFiniteRank_tmul]
  have hEF : E * F = F := by
    ext x
    change E (F x) = F x
    rw [Submodule.starProjection_eq_self_iff, hFx]
    refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ ?_
    exact Submodule.mem_sup_right (Submodule.mem_sup_left
      (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩))
  have hFE : F * E = F := by
    ext x
    change F (E x) = F x
    rw [hFx, hFx]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hu : u i ∈ V := Submodule.mem_sup_right (Submodule.mem_sup_right
      (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩))
    have h1 (y : H) : i.1 y = inner ℂ (u i) y := (InnerProductSpace.toDual_symm_apply).symm
    rw [h1, h1, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hu]
  let Fn : nuclearEndomorphisms H := ⟨F, tensorToFiniteRank_mem_nuclearEndomorphisms z⟩
  let D := T - Fn
  have hD : T - ⟨E * (T.val * E), mul_mem_nuclearEndomorphisms_left _
      ⟨T.val * E, mul_mem_nuclearEndomorphisms_right _ T⟩⟩ =
      D - ⟨E * (D.val * E), mul_mem_nuclearEndomorphisms_left _
        ⟨D.val * E, mul_mem_nuclearEndomorphisms_right _ D⟩⟩ := by
    apply Subtype.ext
    simp only [D, Fn, Submodule.coe_sub, sub_mul, mul_sub, ← mul_assoc, hEF]
    rw [hFE]
    abel
  rw [hD]
  calc _ ≤ traceNorm D + traceNorm D :=
        (traceClass_blockSums_tails_of_bddAbove_sub_le _ _).trans (add_le_add le_rfl
          (traceClass_blockSums_tails_of_bddAbove_compress_le E
            (Submodule.starProjection_norm_le V) D))
    _ < δ := by linarith [hz]


/-- The trace norm is nonnegative. -/
private theorem traceClass_blockSums_tails_of_bddAbove_nonneg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) : 0 ≤ traceNorm T := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := H)).norm_nonneg _

/-- The trace norm of zero is zero. -/
private theorem traceClass_blockSums_tails_of_bddAbove_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    : traceNorm (0 : nuclearEndomorphisms H) = 0 := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  exact ((traceNorm_normedSpaceCore (H := H)).norm_eq_zero_iff 0).mpr rfl

/-- The trace norm of a finite sum is at most the sum of the trace norms. -/
private theorem traceClass_blockSums_tails_of_bddAbove_sum_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (s : Finset ι) (T : ι → nuclearEndomorphisms H) :
    traceNorm (∑ i ∈ s, T i) ≤ ∑ i ∈ s, traceNorm (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [traceClass_blockSums_tails_of_bddAbove_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (traceClass_blockSums_tails_of_bddAbove_add_le _ _).trans (add_le_add le_rfl ih)

/-- A nuclear operator moves a vector by at most its trace norm times the norm of the vector. -/
private theorem traceClass_blockSums_tails_of_bddAbove_apply_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (x : H) :
    ‖T.val x‖ ≤ traceNorm T * ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  let φ : StrongDual ℂ H := InnerProductSpace.toDual ℂ H x
  have hφ : ‖φ‖ = ‖x‖ := (InnerProductSpace.toDual ℂ H).norm_map x
  let P : H →L[ℂ] H := φ.smulRight x
  have hP : ‖P‖ = ‖x‖ * ‖x‖ := by rw [ContinuousLinearMap.norm_smulRight_apply, hφ]
  have hTP : T.val * P = φ.smulRight (T.val x) := by
    ext y
    simp [P, map_smul]
  have h := traceNorm_mul_right_le P T
  have heq : (⟨T.val * P, mul_mem_nuclearEndomorphisms_right P T⟩ : nuclearEndomorphisms H) =
      ⟨φ.smulRight (T.val x), smulRight_mem_nuclearEndomorphisms φ _⟩ := Subtype.ext hTP
  rw [heq, traceNorm_smulRight, hφ, hP] at h
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine le_of_mul_le_mul_left ?_ hx0
  calc ‖x‖ * ‖T.val x‖ ≤ ‖x‖ * ‖x‖ * traceNorm T := h
    _ = ‖x‖ * (traceNorm T * ‖x‖) := by ring

/-- The adjoint of a nuclear operator moves a vector by at most the trace norm times the
norm of the vector. -/
private theorem traceClass_blockSums_tails_of_bddAbove_adjoint_apply_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (x : H) :
    ‖T.val.adjoint x‖ ≤ traceNorm T * ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  let φ : StrongDual ℂ H := InnerProductSpace.toDual ℂ H x
  have hφ : ‖φ‖ = ‖x‖ := (InnerProductSpace.toDual ℂ H).norm_map x
  let ψ : StrongDual ℂ H := InnerProductSpace.toDual ℂ H (T.val.adjoint x)
  have hψ : ‖ψ‖ = ‖T.val.adjoint x‖ := (InnerProductSpace.toDual ℂ H).norm_map _
  let P : H →L[ℂ] H := φ.smulRight x
  have hP : ‖P‖ = ‖x‖ * ‖x‖ := by rw [ContinuousLinearMap.norm_smulRight_apply, hφ]
  have hPT : P * T.val = ψ.smulRight x := by
    ext y
    simp only [P, ψ, φ, mul_apply_eq_comp,
      ContinuousLinearMap.smulRight_apply,
      InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]
  have h := traceNorm_mul_left_le P T
  have heq : (⟨P * T.val, mul_mem_nuclearEndomorphisms_left P T⟩ : nuclearEndomorphisms H) =
      ⟨ψ.smulRight x, smulRight_mem_nuclearEndomorphisms ψ _⟩ := Subtype.ext hPT
  rw [heq, traceNorm_smulRight, hψ, hP] at h
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine le_of_mul_le_mul_left ?_ hx0
  calc ‖x‖ * ‖T.val.adjoint x‖ = ‖T.val.adjoint x‖ * ‖x‖ := by ring
    _ ≤ ‖x‖ * ‖x‖ * traceNorm T := h
    _ = ‖x‖ * (traceNorm T * ‖x‖) := by ring

/-- Greedy choice of signs: some signed sum has squared norm at least the sum of the squared
norms. -/
private theorem traceClass_blockSums_tails_of_bddAbove_signs
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (g : ℕ → H) (s : Finset ℕ) :
    ∃ t ⊆ s,
      ∑ n ∈ s, ‖g n‖ ^ 2 ≤ ‖∑ n ∈ t, g n - ∑ n ∈ s \ t, g n‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t, hts, h⟩ := ih
    have hat : a ∉ t := fun h ↦ ha (hts h)
    have hst : a ∉ s \ t := fun h ↦ ha (Finset.mem_sdiff.mp h).1
    by_cases hre : 0 ≤ RCLike.re (inner ℂ (∑ n ∈ t, g n - ∑ n ∈ s \ t, g n) (g a))
    · refine ⟨insert a t, Finset.insert_subset_insert a hts, ?_⟩
      have e2 : insert a s \ insert a t = s \ t := by
        rw [Finset.insert_sdiff_insert]
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun h3 ↦ h2 (Or.inr h3)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun h3 ↦ h3.elim (fun h4 ↦ ha (h4 ▸ h1)) h2⟩
      rw [Finset.sum_insert ha, Finset.sum_insert hat, e2]
      have hn := norm_add_sq (𝕜 := ℂ) (∑ n ∈ t, g n - ∑ n ∈ s \ t, g n) (g a)
      have hr : g a + ∑ n ∈ t, g n - ∑ n ∈ s \ t, g n =
          (∑ n ∈ t, g n - ∑ n ∈ s \ t, g n) + g a := by abel
      rw [hr, hn]
      linarith
    · refine ⟨t, hts.trans (Finset.subset_insert a s), ?_⟩
      rw [Finset.sum_insert ha, Finset.insert_sdiff_of_notMem s hat, Finset.sum_insert hst]
      have hn := norm_sub_sq (𝕜 := ℂ) (∑ n ∈ t, g n - ∑ n ∈ s \ t, g n) (g a)
      have hr : ∑ n ∈ t, g n - (g a + ∑ n ∈ s \ t, g n) =
          (∑ n ∈ t, g n - ∑ n ∈ s \ t, g n) - g a := by abel
      rw [hr, hn]
      have hre' := not_le.mp hre
      linarith

/-- In a Hilbert space, vectors whose finite sums are bounded tend to zero. -/
private theorem traceClass_blockSums_tails_of_bddAbove_vectors
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (g : ℕ → H) (C : ℝ) (h : ∀ s : Finset ℕ, ‖∑ n ∈ s, g n‖ ≤ C) :
    Tendsto (fun n ↦ ‖g n‖) atTop (𝓝 0) := by
  have hsq (s : Finset ℕ) : ∑ n ∈ s, ‖g n‖ ^ 2 ≤ (2 * C) ^ 2 := by
    obtain ⟨t, -, ht⟩ := traceClass_blockSums_tails_of_bddAbove_signs g s
    have h1 := norm_sub_le (∑ n ∈ t, g n) (∑ n ∈ s \ t, g n)
    have h2 := h t
    have h3 := h (s \ t)
    have h0 : 0 ≤ ‖∑ n ∈ t, g n - ∑ n ∈ s \ t, g n‖ := norm_nonneg _
    nlinarith
  have hsum : Summable (fun n ↦ ‖g n‖ ^ 2) :=
    summable_of_sum_le (fun n ↦ by positivity) hsq
  have hs := hsum.tendsto_atTop_zero.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using hs

/-- For a sequence of nuclear operators with bounded finite sums, the compressions on either
side by a fixed finite-rank orthogonal projection eventually have small trace norm. -/
private theorem traceClass_blockSums_tails_of_bddAbove_sides
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : ℕ → nuclearEndomorphisms H) (C : ℝ)
    (hB : ∀ s : Finset ℕ, traceNorm (∑ n ∈ s, B n) ≤ C) (V : Submodule ℂ H)
    [FiniteDimensional ℂ V] {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop,
      traceNorm (⟨V.starProjection * (B n).val,
        mul_mem_nuclearEndomorphisms_left _ (B n)⟩ : nuclearEndomorphisms H) < η ∧
      traceNorm (⟨(B n).val * V.starProjection,
        mul_mem_nuclearEndomorphisms_right _ (B n)⟩ : nuclearEndomorphisms H) < η := by
  let b := stdOrthonormalBasis ℂ V
  have hb (i) : ‖(b i : H)‖ = 1 := by rw [Submodule.norm_coe]; exact b.orthonormal.1 i
  have hproj (x : H) : V.starProjection x = ∑ i, inner ℂ (b i : H) x • (b i : H) := by
    rw [Submodule.starProjection_apply, b.orthogonalProjectionOnto_apply_eq_sum,
      Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  have hv (i) : Tendsto (fun n ↦ ‖(B n).val (b i)‖) atTop (𝓝 0) := by
    refine traceClass_blockSums_tails_of_bddAbove_vectors _ C fun s ↦ ?_
    have : ∑ n ∈ s, (B n).val (b i) = (∑ n ∈ s, B n).val (b i) := by
      rw [Submodule.coe_sum, sum_apply]
    rw [this]
    exact traceClass_blockSums_tails_of_bddAbove_apply_le (∑ n ∈ s, B n) (b i) |>.trans
      (by rw [hb i, mul_one]; exact hB s)
  have hw (i) : Tendsto (fun n ↦ ‖(B n).val.adjoint (b i)‖) atTop (𝓝 0) := by
    refine traceClass_blockSums_tails_of_bddAbove_vectors _ C fun s ↦ ?_
    have : ∑ n ∈ s, (B n).val.adjoint (b i) = (∑ n ∈ s, B n).val.adjoint (b i) := by
      rw [Submodule.coe_sum, map_sum, sum_apply]
    rw [this]
    exact traceClass_blockSums_tails_of_bddAbove_adjoint_apply_le (∑ n ∈ s, B n) (b i) |>.trans
      (by rw [hb i, mul_one]; exact hB s)
  have hV := (tendsto_finsetSum Finset.univ fun i _ ↦ hv i).eventually (gt_mem_nhds
    (by simpa using hη))
  have hW := (tendsto_finsetSum Finset.univ fun i _ ↦ hw i).eventually (gt_mem_nhds
    (by simpa using hη))
  filter_upwards [hV, hW] with n hn hn'
  constructor
  · let ψ (i) : StrongDual ℂ H := InnerProductSpace.toDual ℂ H ((B n).val.adjoint (b i))
    have heq : (⟨V.starProjection * (B n).val, mul_mem_nuclearEndomorphisms_left _ (B n)⟩ :
        nuclearEndomorphisms H) = ∑ i, ⟨(ψ i).smulRight (b i : H),
          smulRight_mem_nuclearEndomorphisms _ _⟩ := by
      apply Subtype.ext
      ext x
      simp only [Submodule.coe_sum, sum_apply,
        ContinuousLinearMap.smulRight_apply, mul_apply_eq_comp,
        hproj, ψ, InnerProductSpace.toDual_apply_apply,
        ContinuousLinearMap.adjoint_inner_left]
    rw [heq]
    refine (traceClass_blockSums_tails_of_bddAbove_sum_le _ _).trans_lt
      (lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦ ?_) hn')
    rw [traceNorm_smulRight, hb i, mul_one]
    exact ((InnerProductSpace.toDual ℂ H).norm_map _).le
  · let φ (i) : StrongDual ℂ H := InnerProductSpace.toDual ℂ H (b i : H)
    have heq : (⟨(B n).val * V.starProjection, mul_mem_nuclearEndomorphisms_right _ (B n)⟩ :
        nuclearEndomorphisms H) = ∑ i, ⟨(φ i).smulRight ((B n).val (b i)),
          smulRight_mem_nuclearEndomorphisms _ _⟩ := by
      apply Subtype.ext
      ext x
      simp only [Submodule.coe_sum, sum_apply,
        ContinuousLinearMap.smulRight_apply, mul_apply_eq_comp,
        hproj, φ, InnerProductSpace.toDual_apply_apply,
        map_sum, map_smul]
    rw [heq]
    refine (traceClass_blockSums_tails_of_bddAbove_sum_le _ _).trans_lt
      (lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦ ?_) hn)
    rw [traceNorm_smulRight]
    have : ‖φ i‖ = 1 := ((InnerProductSpace.toDual ℂ H).norm_map _).trans (hb i)
    rw [this, one_mul]

/-- A sequence of nuclear operators whose finite sums are bounded in trace norm cannot stay
bounded away from zero in trace norm. -/
private theorem traceClass_blockSums_tails_of_bddAbove_seq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : ℕ → nuclearEndomorphisms H) (C ε : ℝ) (hε : 0 < ε)
    (hB : ∀ s : Finset ℕ, traceNorm (∑ n ∈ s, B n) ≤ C)
    (hlow : ∀ n, ε ≤ traceNorm (B n)) :
    False := by
  have hδ : 0 < ε / 12 := by positivity
  set δ := ε / 12 with hδdef
  have step (N : ℕ) :
      ∃ s : Finset ℕ, ∃ V : Submodule ℂ H, ∃ _ : FiniteDimensional ℂ V,
      ∃ Y : nuclearEndomorphisms H, V.starProjection * Y.val = Y.val ∧
        Y.val * V.starProjection = Y.val ∧
        traceNorm (∑ n ∈ s, B n - Y) ≤ 3 * δ * N ∧ N * (ε - 3 * δ) ≤ traceNorm Y := by
    induction N with
    | zero =>
      exact ⟨∅, ⊥, inferInstance, 0, by simp, by simp,
        by simp [traceClass_blockSums_tails_of_bddAbove_zero],
        by simp [traceClass_blockSums_tails_of_bddAbove_zero]⟩
    | succ N ih =>
      obtain ⟨s, V, hV, Y, hY1, hY2, hY3, hY4⟩ := ih
      obtain ⟨n, ⟨hn1, hn2⟩, hns⟩ :=
        ((traceClass_blockSums_tails_of_bddAbove_sides B C hB V hδ).and
          (eventually_gt_atTop (s.sup id))).exists
      have hnotin : n ∉ s := fun h ↦ (Finset.le_sup (f := id) h).not_gt hns
      obtain ⟨V', hV', hle, hc⟩ := traceClass_blockSums_tails_of_bddAbove_compress (B n) V hδ
      have hpE := isStarProjection_starProjection (U := V)
      have hpE' := isStarProjection_starProjection (U := V')
      set E := V.starProjection with hE
      set E' := V'.starProjection with hE'
      have hEE' : E * E' = E := Submodule.starProjection_comp_starProjection_of_le hle
      have hE'E : E' * E = E := by
        have := congrArg star hEE'
        rwa [star_mul, hpE.isSelfAdjoint.star_eq, hpE'.isSelfAdjoint.star_eq] at this
      set Q := E' - E with hQ
      have hpQ : IsStarProjection Q := hpE.sub_of_mul_eq_left hpE' hEE'
      have hQn : ‖Q‖ ≤ 1 := IsStarProjection.norm_le Q hpQ
      have hE'n : ‖E'‖ ≤ 1 := Submodule.starProjection_norm_le V'
      have hEQ : E * Q = 0 := by rw [hQ, mul_sub, hEE', hpE.isIdempotentElem.eq, sub_self]
      have hE'Q : E' * Q = Q := by rw [hQ, mul_sub, hpE'.isIdempotentElem.eq, hE'E]
      have hQE' : Q * E' = Q := by rw [hQ, sub_mul, hpE'.isIdempotentElem.eq, hEE']
      let Yn : nuclearEndomorphisms H := ⟨Q * ((B n).val * Q), mul_mem_nuclearEndomorphisms_left _
        ⟨(B n).val * Q, mul_mem_nuclearEndomorphisms_right _ _⟩⟩
      let X1 : nuclearEndomorphisms H := B n - ⟨E' * ((B n).val * E'),
        mul_mem_nuclearEndomorphisms_left _
          ⟨(B n).val * E', mul_mem_nuclearEndomorphisms_right _ _⟩⟩
      let BE : nuclearEndomorphisms H := ⟨(B n).val * E, mul_mem_nuclearEndomorphisms_right _ _⟩
      let EB : nuclearEndomorphisms H := ⟨E * (B n).val, mul_mem_nuclearEndomorphisms_left _ _⟩
      let X2 : nuclearEndomorphisms H := ⟨E' * BE.val, mul_mem_nuclearEndomorphisms_left _ BE⟩
      let X3 : nuclearEndomorphisms H := ⟨EB.val * Q, mul_mem_nuclearEndomorphisms_right _ EB⟩
      have hsplit : B n - Yn = X1 + X2 + X3 := by
        apply Subtype.ext
        simp only [X1, X2, X3, BE, EB, Yn, Submodule.coe_add, Submodule.coe_sub, hQ]
        noncomm_ring
      have h2 : traceNorm X2 ≤ δ := by
        have := traceNorm_mul_left_le E' BE
        nlinarith [traceClass_blockSums_tails_of_bddAbove_nonneg BE, norm_nonneg E']
      have h3 : traceNorm X3 ≤ δ := by
        have := traceNorm_mul_right_le Q EB
        nlinarith [traceClass_blockSums_tails_of_bddAbove_nonneg EB, norm_nonneg Q]
      have hYn : traceNorm (B n - Yn) ≤ 3 * δ := by
        rw [hsplit]
        have := (traceClass_blockSums_tails_of_bddAbove_add_le (X1 + X2) X3).trans
          (add_le_add (traceClass_blockSums_tails_of_bddAbove_add_le X1 X2) le_rfl)
        linarith [hc.le]
      have hadd : traceNorm (Y + Yn) = traceNorm Y + traceNorm Yn := by
        apply traceClass_blockSums_tails_of_bddAbove_add_eq
        · rw [← ContinuousLinearMap.star_eq_adjoint, ← hY1, star_mul,
            hpE.isSelfAdjoint.star_eq]
          change star Y.val * E * (Q * ((B n).val * Q)) = 0
          rw [mul_assoc, ← mul_assoc E Q, hEQ, zero_mul, mul_zero]
        · rw [← ContinuousLinearMap.star_eq_adjoint, ← hY2]
          change Y.val * E * star (Q * ((B n).val * Q)) = 0
          rw [star_mul, star_mul, hpQ.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc E,
            ← mul_assoc E Q, hEQ]
          simp
      refine ⟨insert n s, V', hV', Y + Yn, ?_, ?_, ?_, ?_⟩
      · have hy : E' * Y.val = Y.val := by rw [← hY1, ← mul_assoc, hE'E]
        have hq : E' * (Q * ((B n).val * Q)) = Q * ((B n).val * Q) := by
          rw [← mul_assoc, hE'Q]
        change E' * (Y.val + Q * ((B n).val * Q)) = Y.val + Q * ((B n).val * Q)
        rw [mul_add, hy, hq]
      · have hy : Y.val * E' = Y.val := by rw [← hY2, mul_assoc, hEE']
        have hq : Q * ((B n).val * Q) * E' = Q * ((B n).val * Q) := by
          rw [mul_assoc, mul_assoc, hQE']
        change (Y.val + Q * ((B n).val * Q)) * E' = Y.val + Q * ((B n).val * Q)
        rw [add_mul, hy, hq]
      · have he : ∑ k ∈ insert n s, B k - (Y + Yn) = (∑ k ∈ s, B k - Y) + (B n - Yn) := by
          rw [Finset.sum_insert hnotin]
          abel
        rw [he]
        have := traceClass_blockSums_tails_of_bddAbove_add_le (∑ k ∈ s, B k - Y) (B n - Yn)
        push_cast
        linarith
      · rw [hadd]
        have hb : traceNorm (B n) ≤ traceNorm (B n - Yn) + traceNorm Yn := by
          have := traceClass_blockSums_tails_of_bddAbove_add_le (B n - Yn) Yn
          rwa [sub_add_cancel] at this
        have := hlow n
        push_cast
        nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * C / ε)
  obtain ⟨s, V, hV, Y, -, -, h3, h4⟩ := step N
  have hYle : traceNorm Y ≤ C + 3 * δ * N := by
    have := traceClass_blockSums_tails_of_bddAbove_sub_le (∑ n ∈ s, B n) (∑ n ∈ s, B n - Y)
    rw [sub_sub_cancel] at this
    linarith [hB s]
  have hN' : 2 * C < N * ε := by
    have := (div_lt_iff₀ hε).mp hN
    linarith
  rw [hδdef] at h4 hYle
  nlinarith

/-- In the trace class of a Hilbert space, a family whose finite sums are
bounded in trace norm (a weakly unconditionally Cauchy family) is unconditionally summable, so
its finite sums away from a large finite set are small. Proved here directly, by a gliding-hump
argument in the trace class (#7459). Classically, by the theorem of Bessaga and
Pełczyński (Studia Math. 17 (1958), 151–164; Albiac–Kalton, *Topics in Banach Space Theory*,
Theorem 2.4.11) this holds in every Banach space containing no copy of `c₀`. The trace class
contains none: it has cotype 2 (N. Tomczak-Jaegermann, Studia Math. 50 (1974), 163–182), and it
is weakly sequentially complete as the predual of `B(H)` (Takesaki, *Theory of Operator
Algebras I*, Ch. III §5). Only countably many members of such a family are nonzero, and the
countable case is the cited one.
Deviation: Stated for an arbitrary index type, with tails taken over finite sets disjoint from
a finite exceptional set. -/
theorem traceClass_blockSums_tails_of_bddAbove {H Z : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : Z → nuclearEndomorphisms H)
    (hbound : BddAbove (range fun K : Finset Z ↦ traceNorm (∑ z ∈ K, R z))) :
    ∀ ε > (0 : ℝ), ∃ F : Finset Z, ∀ K : Finset Z, Disjoint K F →
      traceNorm (∑ z ∈ K, R z) < ε := by
  classical
  intro ε hε
  by_contra hcon
  simp only [not_exists, not_forall, not_lt] at hcon
  obtain ⟨C, hC⟩ := hbound
  choose next hdisj hbig using hcon
  let acc : ℕ → Finset Z := fun n ↦ Nat.rec ∅ (fun _ A ↦ A ∪ next A) n
  let K : ℕ → Finset Z := fun n ↦ next (acc n)
  have hacc : ∀ n m, m < n → K m ⊆ acc n := by
    intro n
    induction n with
    | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
    | succ n ih =>
      intro m hm
      change K m ⊆ acc n ∪ next (acc n)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | rfl
      · exact (ih m h).trans Finset.subset_union_left
      · exact Finset.subset_union_right
  have hK : Pairwise (Function.onFun Disjoint K) := by
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact Disjoint.mono_left (hacc n m h) (hdisj (acc n)).symm
    · exact Disjoint.mono_right (hacc m n h) (hdisj (acc m))
  let B : ℕ → nuclearEndomorphisms H := fun n ↦ ∑ z ∈ K n, R z
  have hB (s : Finset ℕ) : traceNorm (∑ n ∈ s, B n) ≤ C := by
    rw [← Finset.sum_biUnion (hK.set_pairwise _)]
    exact hC ⟨_, rfl⟩
  exact traceClass_blockSums_tails_of_bddAbove_seq B C ε hε hB fun n ↦ hbig (acc n)

/-- Small tails of a family of nuclear operators make its rectangular sums Cauchy in trace norm. -/
private theorem spectralStripGeometricKernel_traceCauchy_of_tails {H Z : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : Z → nuclearEndomorphisms H) (e : Z ↪ ℕ × ℕ)
    (htail : ∀ ε > (0 : ℝ), ∃ F : Finset Z, ∀ K : Finset Z, Disjoint K F →
      traceNorm (∑ z ∈ K, R z) < ε) :
    SpectralRectanglesTraceCauchy (fun ij : ℕ × ℕ ↦
      (∑ z ∈ ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn, R z).val) := by
  classical
  intro ε hε
  obtain ⟨F, hF⟩ := htail (ε / 2) (half_pos hε)
  let box (ij : ℕ × ℕ) := ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
  have hsub (ij : ℕ × ℕ) (h : F.sup e ≤ ij) : F ⊆ box ij := by
    intro z hz
    have hle : e z ≤ ij := (Finset.le_sup (f := e) hz).trans h
    simp only [box, Finset.mem_preimage]
    exact Finset.mem_product.mpr ⟨Finset.mem_Iic.mpr hle.1, Finset.mem_Iic.mpr hle.2⟩
  refine ⟨F.sup e, fun j k hj hk ↦ ?_⟩
  let X := ∑ z ∈ box j \ box k, R z
  let Y := ∑ z ∈ box k \ box j, R z
  refine ⟨X - Y, ?_, ?_⟩
  · have h := Finset.sum_sdiff_sub_sum_sdiff (s₁ := box k) (s₂ := box j) (f := R)
    change (X - Y).val = (∑ z ∈ box j, R z).val - (∑ z ∈ box k, R z).val
    rw [← Submodule.coe_sub, ← h]
  · let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
    have hc := traceNorm_normedSpaceCore (H := H)
    have hneg : traceNorm (-Y) = traceNorm Y := by
      rw [← neg_one_smul ℂ Y]
      simpa only [norm_neg, norm_one, one_mul] using hc.norm_smul (-1 : ℂ) Y
    have htr := hc.norm_triangle X (-Y)
    change traceNorm (X + -Y) ≤ traceNorm X + traceNorm (-Y) at htr
    rw [← sub_eq_add_neg, hneg] at htr
    have hX := hF (box j \ box k) (Finset.disjoint_of_subset_right (hsub k hk) Finset.sdiff_disjoint)
    have hY := hF (box k \ box j) (Finset.disjoint_of_subset_right (hsub j hj) Finset.sdiff_disjoint)
    change traceNorm X < ε / 2 at hX
    change traceNorm Y < ε / 2 at hY
    linarith

/-- Bounded block sums of the rank-one operators `v ↦ f_j(q v) • v_j` make the rectangles of the
tensors `d(f_j ∘ q) ⊗ v_j` Cauchy, by `traceClass_blockSums_tails_of_bddAbove` and the
trace-class isometry. -/
private theorem spectralStripGeometricKernel_cauchy_of_blocks {W W' H Z J : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup W'] [NormedSpace ℂ W'] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (d : StrongDual ℂ W →L[ℂ] W') (q : W →L[ℂ] H)
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (i : (z : Z) → Fin (N z) → J)
    (u : J → W') (f : J → StrongDual ℂ H) (v : J → W) (hu : ∀ j, d ((f j).comp q) = u j)
    (hbound : BddAbove (range fun K : Finset Z ↦ traceNorm (∑ z ∈ K, ∑ m : Fin (N z),
      (⟨((f (i z m)).comp q).smulRight (v (i z m)), smulRight_mem_nuclearEndomorphisms _ _⟩ :
        nuclearEndomorphisms W)))) :
    Cauchy (Filter.map (spectralKernelRectangle e N i u v) atTop) := by
  classical
  have hrect := spectralStripGeometricKernel_traceCauchy_of_tails _ e
    (traceClass_blockSums_tails_of_bddAbove _ hbound)
  have hc : SpectralRectanglesTraceCauchy (fun ij : ℕ × ℕ ↦ spectralConvolutionFiniteSum
      (ContinuousLinearMap.id ℂ W) v (fun j ↦ (f j).comp q)
      (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn) N i) := by
    convert hrect using 2 with ij
    simp only [spectralConvolutionFiniteSum, Submodule.coe_sum, ContinuousLinearMap.comp_id]
  obtain ⟨K, hK⟩ := spectralStripGeometricKernel_cauchy_of_traceCauchy _ v _ e N i hc
  let idW := ContinuousLinearMap.id ℂ W
  let L : ProjectiveTensor (StrongDual ℂ W) W →L[ℂ] ProjectiveTensor W' W :=
    ⟨projectiveTensorMap d.toLinearMap idW.toLinearMap, projectiveTensorMap_continuous d idW⟩
  apply Filter.Tendsto.cauchy_map (a := L.completion K)
  apply ((L.completion.continuous.tendsto K).comp hK).congr
  intro ij
  unfold Function.comp spectralKernelRectangle
  rw [ContinuousLinearMap.completion_apply_coe]
  apply congrArg ((↑) : ProjectiveTensor W' W → Completion (ProjectiveTensor W' W))
  change projectiveTensorMap d.toLinearMap idW.toLinearMap _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  refine (map_sum (TensorProduct.map d.toLinearMap idW.toLinearMap) _ Finset.univ).trans
    (Finset.sum_congr rfl fun m _ ↦ ?_)
  rw [TensorProduct.map_tmul]
  change d (((f (i z m)).comp q).comp idW) ⊗ₜ[ℂ] v (i z m) = u (i z m) ⊗ₜ[ℂ] v (i z m)
  rw [ContinuousLinearMap.comp_id, hu]

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) (ha : 0 < a)
  (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))

local notation "hs₀" => (zero_le_one.trans hs.le)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "Θ₀" => globalThetaSobolev F a hI hs₀
local notation "H(" F ", " a ", " hα ", " hs ")" =>
  spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans (le_of_lt hs))
local notation "Sₐ(" v ")" => ((Θ₀).quotientEquivOrthogonal v).val
local notation "Aφ" => hardySobolevTestAction (ideleClassTamagawaMeasure F) (continuousIdeleClassNorm F)
  (-α) α s hI hs₀ φ
local notation "Gₐ" => geometricProjection (F := F) a hα hs₀
local notation "Pₐ" => spectralProjection (F := F) a hα hs₀
local notation "Dₐ" => spectralSobolevDualEmbedding F a hI hs₀

local notation "order(" χ ", " a ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (χ (z).1))
  (((a + (z).2.1 : ℝ) : ℂ) + ((z).2.2 : ℂ) * Complex.I)
local notation "zeros(" F ", " χ ", " a ", " α ")" => {z : PontryaginDual (ideleClassNorm F).ker × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ, a, z)}
local notation "jetCount(" z ")" => spectralStripMultiplicity α s (z).val.2.1 (order(χ, a, (z).val)).untop₀.toNat
local notation "jets" => SpectralStripJetIndex (F := F) χ a α s

variable (eχ : PontryaginDual (ideleClassNorm F).ker ↪ ℕ) (e : zeros(F, χ, a, α) ↪ ℕ × ℕ)
  (x : SpectralStripJetIndex χ a α s → H(F, a, hα, hs))
  (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(F, a, hα, hs))
  (hχ : IsSpectralBasepointChoice χ) (he : ∀ z, (e z).1 = eχ z.val.1)
  (horder : ∀ z z' : zeros(F, χ, a, α), z.val.1 = z'.val.1 → (e z).2 ≤ (e z').2 → |z.val.2.2| ≤ |z'.val.2.2|)
  (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j,
    spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans hs.le) (f j) =
    (spectralStripJet_memLp χ hα (zero_le_one.trans hs.le) j).toLp
      (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))

local notation "rectangles(" output ")" =>
  spectralKernelRectangle e (fun z ↦ jetCount(z))
    (fun z m ↦ (⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩ : jets))
    (fun j ↦ Dₐ (f j)) (output)
local notation "geometricRectangles" => rectangles((fun j ↦ Gₐ (Aφ (Sₐ(x j)))))
local notation "ambientRectangles" => rectangles((fun j ↦ Aφ (Sₐ(x j))))

include ha hχ he horder hb

local notation "jet(" z ", " m ")" =>
  (⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩ : jets)
local notation "geometricBlock(" z ")" =>
  (∑ m : Fin (jetCount(z)),
    (⟨((f jet(z, m)).comp (Θ₀).mkQL).smulRight (Gₐ (Aφ (Sₐ(x jet(z, m))))),
      smulRight_mem_nuclearEndomorphisms _ _⟩ : nuclearEndomorphisms _))

omit ha hχ he horder hb in
private theorem spectralStripGeometricKernel_traceNorm_sum_le {W ι : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (S : Finset ι) (A : ι → nuclearEndomorphisms W) :
    traceNorm (∑ i ∈ S, A i) ≤ ∑ i ∈ S, traceNorm (A i) := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  have hc := traceNorm_normedSpaceCore (H := W)
  have hzero : traceNorm (0 : nuclearEndomorphisms W) = 0 := (hc.norm_eq_zero_iff 0).mpr rfl
  exact S.le_sum_of_subadditive traceNorm hzero.le hc.toCore.norm_triangle A

omit ha hχ he horder hb in
private theorem spectralStripGeometricKernel_bddAbove_of_rankOne_rows
    {W Z : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (N : Z → ℕ) (u : (z : Z) → Fin (N z) → StrongDual ℂ W)
    (v : (z : Z) → Fin (N z) → W)
    (hrows : Summable (fun z ↦ ∑ m : Fin (N z), ‖u z m‖ * ‖v z m‖)) :
    BddAbove (range fun K : Finset Z ↦ traceNorm (∑ z ∈ K, ∑ m : Fin (N z),
      (⟨(u z m).smulRight (v z m), smulRight_mem_nuclearEndomorphisms _ _⟩ :
        nuclearEndomorphisms W))) := by
  classical
  let T (z : Z) (m : Fin (N z)) : nuclearEndomorphisms W :=
    ⟨(u z m).smulRight (v z m), smulRight_mem_nuclearEndomorphisms _ _⟩
  let c (z : Z) : ℝ := ∑ m : Fin (N z), ‖u z m‖ * ‖v z m‖
  let R (z : Z) : nuclearEndomorphisms W := ∑ m : Fin (N z), T z m
  have hc₀ (z : Z) : 0 ≤ c z := Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hR (z : Z) : traceNorm (R z) ≤ c z :=
    (spectralStripGeometricKernel_traceNorm_sum_le Finset.univ (T z)).trans_eq
      (Finset.sum_congr rfl fun m _ ↦ traceNorm_smulRight (u z m) (v z m))
  refine ⟨∑' z, c z, ?_⟩
  rintro _ ⟨K, rfl⟩
  change traceNorm (∑ z ∈ K, R z) ≤ ∑' z, c z
  calc
    traceNorm (∑ z ∈ K, R z) ≤ ∑ z ∈ K, traceNorm (R z) := spectralStripGeometricKernel_traceNorm_sum_le K R
    _ ≤ ∑ z ∈ K, c z := Finset.sum_le_sum fun z _ ↦ hR z
    _ ≤ ∑' z, c z := hrows.sum_le_tsum K fun z _ ↦ hc₀ z

/-- Reconstruction of Theorem 10.4.3.5(2), p. 472. Summability of the scalar costs of the actual projected rank-one rows controls every
finite selection of strip zeros in trace norm. -/
theorem spectralStripGeometricKernel_blocks_bddAbove_of_summable_rows
    (hrows : Summable (fun z : zeros(F, χ, a, α) ↦ ∑ m : Fin (jetCount(z)),
      ‖(f jet(z, m)).comp (Θ₀).mkQL‖ * ‖Gₐ (Aφ (Sₐ(x jet(z, m))))‖)) :
    BddAbove (range fun K : Finset zeros(F, χ, a, α) ↦ traceNorm (∑ z ∈ K, geometricBlock(z))) :=
  spectralStripGeometricKernel_bddAbove_of_rankOne_rows (fun z : zeros(F, χ, a, α) ↦ jetCount(z))
    (fun z m ↦ (f jet(z, m)).comp (Θ₀).mkQL) (fun z m ↦ Gₐ (Aφ (Sₐ(x jet(z, m))))) hrows

omit ha hχ he horder hb in
private theorem spectralStripGeometricKernel_eq_of_coords
    {J Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (basis : J → Q) (coords : J → StrongDual ℂ Q) (h : IsSpectralMarkushevichBasis basis coords)
    {v w : Q} (heq : ∀ j, coords j v = coords j w) : v = w := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  have hall : ContinuousLinearMap.apply ℂ ℂ v = ContinuousLinearMap.apply ℂ ℂ w := by
    apply ContinuousLinearMap.ext_on h.2.2.2
    rintro _ ⟨j, rfl⟩
    exact heq j
  exact fun ℓ ↦ DFunLike.congr_fun hall ℓ

local notation "mellinAt(" z ")" =>
  (∫ g : IdeleClassGroup (𝓞 F) F, φ.val g * ideleClassNormTwist (χ (z).val.1)
    (((z).val.2.1 : ℂ) + ((z).val.2.2 : ℂ) * Complex.I) g ∂ideleClassTamagawaMeasure F)

/-- At any strip zero with a single retained jet, its quotient basis vector is an eigenvector
of convolution. The exact geometric output subtracts the corresponding scalar times its lift.
The multiplicities at other sites are unrestricted. -/
theorem spectralStripGeometricKernel_output_eq_sub_of_one_jet
    (z : zeros(F, χ, a, α)) (m : Fin (jetCount(z))) (hcount : jetCount(z) ≤ 1) :
    Gₐ (Aφ (Sₐ(x jet(z, m)))) = Aφ (Sₐ(x jet(z, m))) - mellinAt(z) • Sₐ(x jet(z, m)) := by
  let T := spectralConvolution (F := F) a hI hs₀ φ
  let lift := (Θ₀).orthogonal.subtypeL.comp
    (Θ₀).quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hcoeff := spectralStripConvolution_jetCoefficients a hα hs χ x f hb.1 hb.2 φ
  have heigen : T (x jet(z, m)) = mellinAt(z) • x jet(z, m) := by
    apply spectralStripGeometricKernel_eq_of_coords x f hb.1
    intro j
    let w : zeros(F, χ, a, α) :=
      ⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩
    let n : Fin (jetCount(w)) := ⟨j.val.2.2.2, j.property⟩
    change f jet(w, n) (T (x jet(z, m))) = f jet(w, n) (mellinAt(z) • x jet(z, m))
    rw [map_smul, smul_eq_mul]
    by_cases hw : w = z
    · subst z
      have hnm : n = m := Fin.ext (by have := n.isLt; have := m.isLt; omega)
      rw [hnm, hb.1.1, mul_one]
      exact (hcoeff.2 w m).trans (spectralConvolution_mellin_integrable φ (χ w.val.1) _).2
    · have hne : (jet(z, m) : jets) ≠ jet(w, n) := by
        intro heq
        exact hw (Subtype.ext (congrArg (fun i : jets ↦ (i.val.1, i.val.2.1, i.val.2.2.1)) heq).symm)
      rw [hb.1.2.1 _ _ hne, mul_zero]
      exact hcoeff.1 w z hw n m
  have hsec (v : H(F, a, hα, hs)) : (Θ₀).mkQL (lift v) = v :=
    ((Θ₀).quotientEquivOrthogonal_symm_eq_mk _ ((Θ₀).quotientEquivOrthogonal v).property).symm.trans
      ((Θ₀).quotientEquivOrthogonal.symm_apply_apply v)
  have hp := DFunLike.congr_fun (spectralProjection_convolution_factor (F := F) a hα hs₀ φ)
    (lift (x jet(z, m)))
  change Pₐ (Aφ (lift (x jet(z, m)))) = lift (T ((Θ₀).mkQL (lift (x jet(z, m))))) at hp
  rw [hsec, heigen, map_smul] at hp
  exact eq_sub_of_add_eq ((congrArg (Gₐ (Aφ (lift (x jet(z, m)))) + ·) hp.symm).trans
    ((Θ₀).starProjection_add_starProjection_orthogonal _))

local notation "lineEnergy(" z ")" =>
  ((1 / 2 : ℝ) * ∫ t : ℝ, ‖deriv (fun u : ℝ ↦ ∫ g : IdeleClassGroup (𝓞 F) F,
    φ.val g * ideleClassNormTwist (χ (z).val.1) ((u : ℂ) * Complex.I) g
      ∂ideleClassTamagawaMeasure F) t‖ ^ 2 * Real.exp (-2 * |t - (z).val.2.2|))

/-- On the line at order two at most one jet survives. The half integral in the energy
majorant uses the actual scalar Mellin multiplier of the test and the translated exponential
envelope of a hyperbolic cardinal function. -/
theorem spectralStripGeometricKernel_blocks_bddAbove_of_lineEnergy
    (hline : α = 0) (htwo : s = 2)
    (henergy : ∀ (z : zeros(F, χ, a, α)) (m : Fin (jetCount(z))),
      (‖(f jet(z, m)).comp (Θ₀).mkQL‖ *
        ‖Aφ (Sₐ(x jet(z, m))) - mellinAt(z) • Sₐ(x jet(z, m))‖) ^ 2 ≤ lineEnergy(z))
    (hscalar : Summable (fun z : zeros(F, χ, a, α) ↦ Real.sqrt lineEnergy(z))) :
    BddAbove (range fun K : Finset zeros(F, χ, a, α) ↦ traceNorm (∑ z ∈ K, geometricBlock(z))) := by
  apply spectralStripGeometricKernel_blocks_bddAbove_of_summable_rows a hα hs φ ha χ eχ e x f hχ he horder hb
  apply hscalar.of_nonneg_of_le (fun z ↦ Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro z
  have hz : z.val.2.1 = -α := by linarith only [z.property.1.1, z.property.1.2, hline]
  have hcount : jetCount(z) ≤ 1 := by
    rw [spectralStripMultiplicity_boundary hα (Or.inl hz), spectralBoundaryMultiplicity]
    exact (Nat.min_le_right _ _).trans (Nat.ceil_le.mpr (by norm_num [htwo]))
  calc
    _ ≤ ∑ _m : Fin (jetCount(z)), Real.sqrt lineEnergy(z) :=
      Finset.sum_le_sum fun m _ ↦ by
        rw [spectralStripGeometricKernel_output_eq_sub_of_one_jet a hα hs φ ha χ eχ e x f hχ he horder hb z m hcount]
        exact Real.le_sqrt_of_sq_le (henergy z m)
    _ ≤ Real.sqrt lineEnergy(z) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (by exact_mod_cast hcount)

/-- Paper: Theorem 10.4.3.5(2), p. 472. For each zero `z` of the strip, let `R_z` be the
finite-rank operator `v ↦ ∑ₘ f_{z,m}(q v) • P^geom_a(A(φ)(S_a x_{z,m}))` on the Sobolev space,
summed over the jets kept at `z`; here `q` is the quotient map and `S_a` its isometric section.
The finite sums of the `R_z`, over arbitrary finite sets of zeros, are bounded in trace norm.
Reconstruction: The paper gives no estimate for the geometric component (p. 472). This is the
geometric analogue of the bound that `spectralStripConvolution_traceCauchy` obtains for the
quotient sums; with `traceClass_blockSums_tails_of_bddAbove` it implies
`spectralStripGeometricKernel_cauchy`. It asks for more than that statement: summability of
the blocks in every order, where the theorem needs convergence along its rectangles only. It
is equivalent to the summability, for every compact
operator `U`, of `z ↦ ∑ₘ f_{z,m}(q(U(P^geom_a(A(φ)(S_a x_{z,m})))))`, by uniform boundedness.
Gap: No bound is known for the geometric output of convolution on the biorthogonal vectors,
that is, for the part of `A(φ)(S_a x_{z,m})` outside the spectral subspace; the bound
(10.4.2.34) on p. 464 does not give one. The statement implies that `P^geom_a ∘ A(φ) ∘ P^spec_a`
is nuclear on the Sobolev space, which is not known either. Nothing in the Lean uses this statement, and it is not
known how it connects with the rest of the proof in Lean; in the paper it is used on pp. 471–474. -/
theorem spectralStripGeometricKernel_blocks_bddAbove :
    BddAbove (range fun K : Finset zeros(F, χ, a, α) ↦ traceNorm (∑ z ∈ K, geometricBlock(z))) := by
  sorry

/-- Paper: Theorem 10.4.3.5(2), p. 472. At positive twist and Sobolev order above one, the
geometric projections of the corrected ambient rectangles are Cauchy in the completed
projective tensor product.
Deviation: For the operator in (10.4.3.45), convolution acts on the orthogonal output lift.
The rectangles use injections of the actual strip zeros and the strict §10.2 boundary cutoff.
Reconstruction: This is the geometric component of the convergence claimed on pp. 472–473,
with the operator order repaired in §10.4.3. The paper gives no separate geometric estimate.
Proved here (#7427) from the open statement `spectralStripGeometricKernel_blocks_bddAbove`
and `traceClass_blockSums_tails_of_bddAbove`, which is proved (#7459). The quotient estimates
control the spectral component only, and the bound (10.4.2.34) on p. 464 gives no bound
tending to zero for these projective tails. Nothing in the Lean outside this file uses this
statement, and it is not known how it connects with the rest of the proof in Lean; in the
paper it is used on pp. 471–474. -/
theorem spectralStripGeometricKernel_cauchy : Cauchy (Filter.map geometricRectangles atTop) :=
  spectralStripGeometricKernel_cauchy_of_blocks
    (modulatedIntervalSobolev_dual (continuousIdeleClassNorm F : IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ)
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ (ideleClassTamagawaMeasure F)
      (-α) α s hI hs₀).exists.choose.toContinuousLinearEquiv.toContinuousLinearMap
    (Θ₀).mkQL e _ _ _ f _ (fun _ ↦ rfl)
    (spectralStripGeometricKernel_blocks_bddAbove a hα hs φ ha χ eχ e x f hχ he horder hb)

/-- Paper: Theorem 10.4.3.5(2)–(3), p. 472. The corrected ambient net converges to a kernel
representing convolution after projection (p. 473) exactly when its geometric rectangles are Cauchy.
Deviation: Both conclusions concern the same ambient rectangles, with convolution on the output
and the repaired indexing of §10.4.3.
Reconstruction: The equivalence identifies exactly what the geometric estimate on pp. 471–473 must supply. -/
theorem spectralStripAmbientKernel_exists_iff_geometric_cauchy :
    (∃ K, Tendsto ambientRectangles atTop (𝓝 K) ∧
      sobolevProjectiveKernelOperator (F := F) hα hs₀ K = (Aφ).comp Pₐ) ↔
      Cauchy (Filter.map geometricRectangles atTop) := by
  constructor
  · rintro ⟨K, hK, _⟩
    exact cauchy_rectangles_map_output e _ _ _ (fun j ↦ Aφ (Sₐ(x j))) Gₐ hK
  · intro hgeom
    exact (spectralStripAmbientKernel_tendsto (F := F) a hα hs φ ha χ eχ e x f hχ he horder hb hgeom).imp
      fun K hK ↦ ⟨hK, spectralStripAmbientKernel_operator (F := F) a hα hs φ ha χ eχ e x f hχ he horder hb K hK⟩

/-- Paper: Theorem 10.4.3.5(2)–(3), p. 472. The isolated geometric Cauchy estimate supplies
the limit and the operator identity (10.4.3.45) on p. 473.
Deviation: The ambient tensors use the repaired output action and strip indexing of §10.4.3. -/
theorem spectralStripAmbientKernel_exists :
    ∃ K, Tendsto ambientRectangles atTop (𝓝 K) ∧
      sobolevProjectiveKernelOperator (F := F) hα hs₀ K = (Aφ).comp Pₐ :=
  (spectralStripAmbientKernel_exists_iff_geometric_cauchy a hα hs φ ha χ eχ e x f hχ he horder hb).mpr
    (spectralStripGeometricKernel_cauchy a hα hs φ ha χ eχ e x f hχ he horder hb)

end RiemannMasullo.Isolated
