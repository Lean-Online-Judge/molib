module

public import Mathlib.Data.Finset.Preimage
public import Mathlib.Tactic.IntervalCases

@[expose] public section

open scoped Finset

variable {α : Type u} [DecidableEq α] (family : Finset (Finset α))

/-- A r-sunflower is a collection of r sets where all pairwise intersections are equal (the core).
    This is also called a Δ-system. -/
def IsSunflower (r : ℕ) : Prop :=
  #family = r ∧ ∃ core : Finset α, ∀ S T : Finset α, S ∈ family → T ∈ family → S ≠ T → S ∩ T = core

/-- A family is r-sunflower-free if it contains no r-sunflower as a subfamily. -/
def IsSunflowerFree (r : ℕ) : Prop :=
  ∀ subfamily : Finset (Finset α), subfamily ⊆ family → ¬IsSunflower subfamily r

@[simp]
theorem IsSunflower_zero : IsSunflower family 0 ↔ #family = 0 := by
  simp only [IsSunflower, and_iff_left_iff_imp, Finset.card_eq_zero]
  rintro rfl
  simp

@[simp]
theorem IsSunflower_one : IsSunflower family 1 ↔ #family = 1 := by
  simp only [IsSunflower, and_iff_left_iff_imp]
  intro h
  rw [Finset.card_eq_one] at h
  rcases h with ⟨a, rfl⟩
  refine ⟨a, ?_⟩
  simp

@[simp]
theorem IsSunflower_two : IsSunflower family 2 ↔ #family = 2 := by
  simp only [IsSunflower, and_iff_left_iff_imp]
  intro h
  rw [Finset.card_eq_two] at h
  rcases h with ⟨a, b, ab, rfl⟩
  refine ⟨a ∩ b, ?_⟩
  aesop

@[simp]
theorem IsSunflower_le_two {r : ℕ} (r₂ : r ≤ 2) : IsSunflower family r ↔ #family = r := by
  interval_cases r
  · exact IsSunflower_zero family
  · exact IsSunflower_one family
  · exact IsSunflower_two family

@[simp]
theorem IsSunflowerFree_le_two {r : ℕ} (r₂ : r ≤ 2) : IsSunflowerFree family r ↔ #family < r := by
  simp only [IsSunflowerFree, IsSunflower_le_two, r₂]
  refine ⟨fun h ↦ ?_, fun h s s₁ ↦ Nat.ne_of_lt (Nat.lt_of_le_of_lt (Finset.card_le_card s₁) h)⟩
  contrapose! h
  exact Finset.le_card_iff_exists_subset_card.1 h

theorem IsSunflowerFree.mono_left {r : ℕ} {f₁ f₂ : Finset (Finset α)} (f₁₂ : f₁ ⊆ f₂)
  (h₂ : IsSunflowerFree f₂ r) : IsSunflowerFree f₁ r := fun sub h ↦ h₂ sub (h.trans f₁₂)

theorem IsSunflowerFree.mono_right {r₁ r₂ : ℕ} {f : Finset (Finset α)} (r₁₂ : r₁ ≤ r₂)
  (h₁ : IsSunflowerFree f r₁) : IsSunflowerFree f r₂ := by
  intro sub h sf
  rcases Finset.exists_subset_card_eq (r₁₂.trans_eq sf.1.symm) with ⟨sub', s, c⟩
  rcases sf.2 with ⟨core, corespec⟩
  exact h₁ sub' (s.trans h) ⟨c, core, fun S T S₁ T₁ ↦ corespec S T (s S₁) (s T₁)⟩

@[simp]
theorem IsSunflower_empty_iff {r : ℕ} : @IsSunflower α _ ∅ r ↔ r = 0 := by
  simpa [IsSunflower] using Eq.comm

@[simp]
theorem IsSunflowerFree_empty_iff {r : ℕ} : @IsSunflowerFree α _ ∅ r ↔ r ≠ 0 := by
  simp [IsSunflowerFree]

@[simp]
theorem IsSunflower_map_iff {β : Type v} [DecidableEq β] (φ : α ↪ β) {r : ℕ} {family} :
  IsSunflower (family.map (Finset.mapEmbedding φ).toEmbedding) r ↔ IsSunflower family r := by
  unfold IsSunflower
  simp only [Finset.le_eq_subset, Finset.card_map, Finset.mem_map, RelEmbedding.coe_toEmbedding,
    ne_eq, forall_exists_index, and_imp, and_congr_right_iff]
  refine fun sf ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with ⟨core₀, core₀spec⟩
    let core := core₀.preimage φ φ.injective.injOn
    refine ⟨core, fun S T Ss Ts ST ↦ ?_⟩
    have := core₀spec (S.map φ) (T.map φ) S Ss rfl T Ts rfl (by simpa)
    ext
    simp [core, ← this]
  · rcases h with ⟨core, corespec⟩
    refine ⟨core.map φ, fun S₀ T₀ S Ss S₀s T Ts T₀s ST ↦ ?_⟩
    cases S₀s
    cases T₀s
    simp only [EmbeddingLike.apply_eq_iff_eq] at ST
    have := corespec S T Ss Ts ST
    change S.map φ ∩ T.map φ = core.map φ
    simp [← this, Finset.map_inter]

@[simp]
theorem IsSunflowerFree_map_iff {β : Type v} [DecidableEq β] (φ : α ↪ β) {r : ℕ} {family} :
  IsSunflowerFree (family.map (Finset.mapEmbedding φ).toEmbedding) r ↔
    IsSunflowerFree family r := by
  refine ⟨fun h f hf ↦ ?_, fun h f₀ hf₀ ↦ ?_⟩
  · simpa using h (f.map (Finset.mapEmbedding φ).toEmbedding) (by simpa)
  · simp only [Finset.le_eq_subset, Finset.subset_map_iff] at hf₀
    rcases hf₀ with ⟨f, hf, rfl⟩
    simpa using h f hf

end
