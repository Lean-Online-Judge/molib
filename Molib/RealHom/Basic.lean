module

public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section

open Real Set Function Finset Rat
open Bornology (IsBounded)

variable {α β : Type*}

def IsAdditive [Add α] [Add β] (f : α → β) : Prop :=
  ∀ x y, f (x + y) = f x + f y

namespace IsAdditive

theorem ofHom [AddZero α] [AddZero β] (f : α →+ β) :
    IsAdditive f := AddMonoidHom.map_add f

abbrev toHom [AddZeroClass α] [AddGroup β] {f : α → β} (hf : IsAdditive f) : α →+ β :=
    .mk' f hf

theorem add [AddZeroClass α] [AddCommGroup β] {f g : α → β} (hf : IsAdditive f)
  (hg : IsAdditive g) : IsAdditive (f + g) := ofHom (hf.toHom + hg.toHom)

theorem neg [AddZeroClass α] [AddCommGroup β] {f : α → β} (hf : IsAdditive f) :
  IsAdditive (-f) := ofHom (-hf.toHom)

@[simp]
theorem of_const_zero [Add α] [AddZeroClass β] : IsAdditive (0 : α → β) := by
  simp [IsAdditive]

@[simp]
theorem of_const_mul [Mul α] [Add α] [LeftDistribClass α] {r : α} : IsAdditive (fun x ↦ r * x) :=
  left_distrib r

@[simp]
theorem of_mul_const [Mul α] [Add α] [RightDistribClass α] {r : α} : IsAdditive (fun x ↦ x * r) :=
  fun _ _ ↦ right_distrib _ _ r

@[simp]
theorem id [Add α] : IsAdditive (@id α) := fun _ _ ↦ rfl

@[simp]
theorem of_neg [SubtractionCommMonoid α] : IsAdditive (fun x ↦ -x) := neg_add

variable {f : α → β}

@[simp]
theorem map_zero [AddZeroClass α] [AddGroup β] (hf : IsAdditive f) : f 0 = 0 :=
  _root_.map_zero hf.toHom

theorem map_sum_finset [AddCommMonoid α] [AddCommGroup β] (hf : IsAdditive f) {ι : Type*}
    (r : ι → α) (s : Finset ι) : ∑ x ∈ s, f (r x) = f (∑ x ∈ s, r x) := (map_sum hf.toHom r s).symm

theorem map_nat_mul [NonAssocSemiring α] [NonAssocRing β] (hf : IsAdditive f) (n : ℕ) (x : α) :
    f (n * x) = n * f x := by
  simp only [← nsmul_eq_mul]
  exact map_nsmul hf.toHom n x

theorem map_mul_nat [NonAssocSemiring α] [NonAssocRing β] (hf : IsAdditive f) (n : ℕ) (x : α) :
    f (x * n) = f x * n := by
  simp only [← nsmul_eq_mul']
  exact map_nsmul hf.toHom n x

theorem map_neg [AddGroup α] [AddGroup β] (hf : IsAdditive f) (x : α) : f (-x) = -f x :=
  _root_.map_neg hf.toHom x

theorem map_int_mul [NonAssocRing α] [NonAssocRing β] (hf : IsAdditive f) (n : ℤ) (x : α) :
    f (n * x) = n * f x := by
  simp only [← zsmul_eq_mul]
  exact map_zsmul hf.toHom n x

theorem map_mul_int [NonAssocRing α] [NonAssocRing β] (hf : IsAdditive f) (n : ℤ) (x : α) :
    f (x * n) = f x * n := by
  simp only [← zsmul_eq_mul']
  exact map_zsmul hf.toHom n x

theorem map_rat_mul [DivisionRing α] [DivisionRing β] [CharZero α] [CharZero β]
    (hf : IsAdditive f) (r : ℚ) (x : α) : f (r * x) = r * f x := by
  simp only [← Rat.smul_def]
  exact map_rat_smul hf.toHom r x

theorem ofNat [AddCommMonoid α] [AddCommGroup β] (hf : IsAdditive f) : IsLinearMap ℕ f :=
  hf.toHom.toNatLinearMap.isLinear

theorem ofInt [AddCommGroup α] [AddCommGroup β] (hf : IsAdditive f) : IsLinearMap ℤ f :=
  hf.toHom.toIntLinearMap.isLinear

theorem ofRat [DivisionRing α] [DivisionRing β] [CharZero α] [CharZero β] (hf : IsAdditive f) :
  IsLinearMap ℚ f := hf.toHom.toRatLinearMap.isLinear

end IsAdditive

--to mathlib?
theorem monotone_iff_neg_antitone {α β : Type*} [Preorder α] [AddGroup β] [Preorder β]
    [AddLeftMono β] [AddRightMono β] {f : α → β} : Monotone f ↔ Antitone (-f) :=
  ⟨fun h ↦ h.neg, fun h ↦ by convert h.neg; simp⟩

--to mathlib?
theorem antitone_iff_neg_monotone {α β : Type*} [Preorder α] [AddGroup β] [Preorder β]
    [AddLeftMono β] [AddRightMono β] {f : α → β} : Antitone f ↔ Monotone (-f) :=
  ⟨fun h ↦ h.neg, fun h ↦ by convert h.neg; simp⟩

lemma real_span_subset_closure_rat_span {V : Type u} [AddCommGroup V] [TopologicalSpace V]
    [Module ℚ V] [Module ℝ V] [ContinuousAdd V] [ContinuousSMul ℚ V] [ContinuousSMul ℝ V]
    (s : Set V) : (Submodule.span ℝ s : Set V) ⊆ (Submodule.span ℚ s).topologicalClosure := by
  intro x xsp
  simp only [SetLike.mem_coe] at xsp ⊢
  induction xsp using Submodule.span_induction with
  | mem y ys => exact Submodule.le_topologicalClosure _ <| Submodule.mem_span_of_mem ys
  | zero => exact zero_mem _
  | add _ _ _ _ hy hz => exact add_mem hy hz
  | smul μ y h₁ h₂ =>
    let f := ContinuousLinearMap.toSpanSingleton ℝ y
    have : MapsTo f (range Rat.cast) (Submodule.span ℚ s).topologicalClosure := by
      rintro _ ⟨q, rfl⟩
      simp only [f, ContinuousLinearMap.toSpanSingleton_apply]
      convert Submodule.smul_mem _ q h₂ using 1
      exact cast_smul_eq_qsmul ℝ q y
    have := f.continuous.continuousWithinAt.mem_closure (denseRange_cast μ) this
    simpa using this

namespace IsAdditive.Real

variable {f : ℝ → ℝ} (hf : IsAdditive f)

include hf

theorem linear_of_not_dense (h : ¬Dense (graph f)) : IsLinearMap ℝ f := by
  suffices l₁ : ∀ x, f x = x * f 1 by
    refine ⟨hf, fun x y ↦ ?_⟩
    simp only [smul_eq_mul, l₁ y, l₁ (x * y)]
    exact mul_assoc x y (f 1)
  intro x
  contrapose h
  simp only [dense_iff_closure_eq, ← univ_subset_iff]
  let ℚ₁ : Submodule ℚ (ℝ × ℝ) := ℚ ∙ (1, f 1)
  let ℝ₁ : Submodule ℝ (ℝ × ℝ) := ℝ ∙ (1, f 1)
  let ℚ₂ : Submodule ℚ (ℝ × ℝ) := ℚ ∙ (x, f x)
  let ℝ₂ : Submodule ℝ (ℝ × ℝ) := ℝ ∙ (x, f x)
  have ℚℝ₁ : (ℝ₁ : Set (ℝ × ℝ)) ⊆ ℚ₁.topologicalClosure := real_span_subset_closure_rat_span _
  have ℚℝ₂ : (ℝ₂ : Set (ℝ × ℝ)) ⊆ ℚ₂.topologicalClosure := real_span_subset_closure_rat_span _
  calc
    _ ⊆ ((ℝ₁ ⊔ ℝ₂ : Submodule ℝ (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      simp only [univ_subset_iff, Submodule.coe_eq_univ, ℝ₁, ℝ₂, ← Submodule.span_union,
        singleton_union]
      have : LinearIndepOn ℝ _root_.id {(1, f 1), (x, f x)} := by
        refine linearIndepOn_id_pair ?_ ?_
        · simp
        · intro y
          contrapose h
          simp only [Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk.injEq] at h
          exact (h.1 ▸ h.2).symm
      convert this.span_eq_top_of_card_eq_finrank' ?_
      · ext
        simp
      · simp only [Fintype.card_ofFinset, toFinset_singleton, Module.finrank_prod,
          Module.finrank_self, Nat.reduceAdd]
        refine card_pair ?_
        contrapose h
        simp at h
        simp [← h.1]
    _ ⊆ ((ℚ₁.topologicalClosure ⊔ ℚ₂.topologicalClosure : Submodule ℚ (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      intro v hv
      simp only [SetLike.mem_coe, Submodule.mem_sup] at hv ⊢
      rcases hv with ⟨v₁, hv₁, v₂, hv₂, rfl⟩
      exact ⟨v₁, ℚℝ₁ hv₁, v₂, ℚℝ₂ hv₂, rfl⟩
    _ ⊆ hf.toHom.toRatLinearMap.graph.topologicalClosure := by
      refine (sup_le (closure_mono ?_) (closure_mono ?_)
        : ℚ₁.topologicalClosure ⊔ ℚ₂.topologicalClosure ≤
          hf.toHom.toRatLinearMap.graph.topologicalClosure) <;> (
        change ℚ ∙ _ ≤ hf.toHom.toRatLinearMap.graph
        simp
      )
    _ = _ := by
      refine congrArg closure ?_
      ext
      simp [graph, Eq.comm]

theorem linear_of_locally_not_dense {U : Set ℝ} (iU : (interior U).Nonempty) (h : ¬Dense (f '' U)) :
    IsLinearMap ℝ f := by
  refine linear_of_not_dense hf ?_
  contrapose h
  grw [← image_mono (f := f) (interior_subset (s := U))]
  have op := isOpen_interior (s := U)
  generalize interior U = U at iU op
  let g := U.restrict f
  have hg : Dense (graph g) := by
    have op' : IsOpen (U ×ˢ (@Set.univ ℝ)) := op.prod isOpen_univ
    let φ : C(U × ℝ, ℝ × ℝ) := .prodMap (.restrict U (.id ℝ)) (.id ℝ)
    have φi : Topology.IsInducing φ := .prodMap .subtypeVal .id
    have opφ : IsOpen (Set.range φ) := by
      convert op'
      ext ⟨x, y⟩
      simp [φ]
    exact h.preimage (φi.isOpenMap opφ)
  let ψ := @ContinuousMap.snd U ℝ _ _
  have : Nonempty U := nonempty_subtype.2 iU
  have ψsurj : Surjective ψ := Prod.snd_surjective
  convert ψsurj.denseRange.dense_image ψ.continuous hg
  ext
  simp [g, ψ]

theorem linear_of_locally_bounded {U : Set ℝ} (iU : (interior U).Nonempty)
    (fb : IsBounded (f '' U)) : IsLinearMap ℝ f :=
  linear_of_locally_not_dense hf iU fun d ↦ NormedSpace.unbounded_univ ℝ ℝ
    (d.closure_eq ▸ fb.closure)

theorem linear_of_locally_monotone {U : Set ℝ} (iU : (interior U).Nonempty)
    (fm : MonotoneOn f U) : IsLinearMap ℝ f := by
  rcases iU with ⟨x, xU⟩
  rw [mem_interior_iff_mem_nhds] at xU
  rcases exists_Icc_mem_subset_of_mem_nhds xU with ⟨l, r, -, lrx, lrU⟩
  rw [← mem_interior_iff_mem_nhds] at lrx
  refine linear_of_locally_bounded hf ⟨x, lrx⟩
    ((Metric.isBounded_Icc _ _).subset (fm.mono lrU).image_Icc_subset)

theorem linear_of_locally_antitone {U : Set ℝ} (iU : (interior U).Nonempty)
    (fm : AntitoneOn f U) : IsLinearMap ℝ f := by
  rcases iU with ⟨x, xU⟩
  rw [mem_interior_iff_mem_nhds] at xU
  rcases exists_Icc_mem_subset_of_mem_nhds xU with ⟨l, r, -, lrx, lrU⟩
  rw [← mem_interior_iff_mem_nhds] at lrx
  refine linear_of_locally_bounded hf ⟨x, lrx⟩
    ((Metric.isBounded_Icc _ _).subset (fm.mono lrU).image_Icc_subset)

theorem ofMonotone (fm : Monotone f) : IsLinearMap ℝ f := by
  refine linear_of_locally_monotone hf ?_ (fm.monotoneOn univ)
  simp only [interior_univ, Set.univ_nonempty]

theorem ofAntitone (fm : Antitone f) : IsLinearMap ℝ f := by
  refine linear_of_locally_antitone hf ?_ (fm.antitoneOn univ)
  simp only [interior_univ, Set.univ_nonempty]

end IsAdditive.Real
