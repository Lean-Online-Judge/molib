module

public import Mathlib.Algebra.Order.Interval.Set.SuccPred
public import Mathlib.Data.Set.PowersetCard
public import Molib.Sunflower.Basic

@[expose] public section

open scoped Finset Nat

/-- The maximum number of size-k sets of a r-sunflower-free family. -/
noncomputable def maxSunflowerFreeCard (k r : ℕ) : ℕ := sSup (Finset.card ''
  { family : Finset (Finset ℕ) | (∀ S ∈ family, #S = k) ∧ IsSunflowerFree family r })

private lemma sunflower_upperbounds (k r : ℕ) : k ! * (r - 1)^k ∈ upperBounds (Finset.card ''
  { family : Finset (Finset ℕ) | (∀ S ∈ family, #S = k) ∧ IsSunflowerFree family r }) := by
  intro n h
  simp only [Set.mem_image, Set.mem_setOf_eq] at h
  rcases h with ⟨family, ⟨hₖ, h⟩, cf⟩
  refine (SunflowerLemma.main family (k := k) ?_ h).trans_eq' cf
  peel hₖ
  exact Nat.le_of_eq this

theorem sunflower_le (k r : ℕ) : maxSunflowerFreeCard k r ≤ k ! * (r - 1)^k :=
  csSup_le' (sunflower_upperbounds k r)

theorem sunflower_ge (k r : ℕ) [NeZero k] [NeZero r] : (r - 1)^k ≤ maxSunflowerFreeCard k r :=
  le_csSup ⟨_, sunflower_upperbounds k r⟩ <| (SunflowerLemma.lower k r).imp fun _ ↦ and_assoc.2

theorem sunflower_k_eq_zero (r : ℕ) : maxSunflowerFreeCard 0 r = if r <= 1 then 0 else 1 := by
  split_ifs with r₁
  · rw [← Nat.le_zero]
    refine csSup_le' fun n h ↦ ?_
    have r₂ : r ≤ 2 := Nat.le_succ_of_le r₁
    simp [IsSunflowerFree_le_two _ r₂] at h
    grind
  · refine Nat.le_antisymm (csSup_le' fun n h ↦ ?_)
      (le_csSup ⟨_, sunflower_upperbounds 0 r⟩ ?_)
    · simp only [Finset.card_eq_zero, Set.mem_image, Set.mem_setOf_eq] at h
      rcases h with ⟨family, ⟨F₀, -⟩, rfl⟩
      rw [Finset.card_le_one]
      grind
    · simp only [Finset.card_eq_zero, Set.mem_image, Set.mem_setOf_eq]
      refine ⟨{∅}, ⟨?_, fun sub se ↦ ?_⟩, rfl⟩
      · simp
      · contrapose r₁
        rw [← r₁.1]
        simp only [Finset.subset_singleton_iff'] at se
        rw [Finset.card_le_one]
        grind

theorem sunflower_trivial (k r : ℕ) [NeZero k] (triv : r ≤ 2 ∨ k ≤ 1) :
    maxSunflowerFreeCard k r = r - 1 := by
  calc
    _ = sSup (Finset.card ''
        { family : Finset (Finset ℕ) | (∀ S ∈ family, #S = k) ∧ #family < r }) := by
      unfold maxSunflowerFreeCard
      congr with family
      simp only [and_congr_right_iff]
      intro hₖ
      rcases triv with (r₂ | k₁)
      · exact IsSunflowerFree_le_two family r₂
      · refine SunflowerLemma.k_le_1 family ?_ r
        peel hₖ
        exact k₁.trans_eq' this.symm
    _ = sSup (Set.Iio r) := by
      congr
      ext
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Iio]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · rcases h with ⟨family, ⟨-, cf'⟩, cf⟩
        exact cf'.trans_eq' cf
      · rcases Infinite.exists_subset_card_eq (Set.powersetCard ℕ k) _ with ⟨family, fn⟩
        refine ⟨family.map (Function.Embedding.subtype _), ?_, ?_⟩
        · simp [fn]
          tauto
        · simpa
    _ = _ := by
      cases r with
      | zero => simp
      | succ n => simp [Set.Iio_add_one_eq_Iic]

theorem sunflower_exists_nat (k r : ℕ) [NeZero r] : ∃ family : Finset (Finset ℕ),
    (∀ S ∈ family, #S = k) ∧ IsSunflowerFree family r ∧ #family = maxSunflowerFreeCard k r := by
  have : maxSunflowerFreeCard k r ∈ _ := Nat.sSup_mem ⟨0, ?_⟩ ⟨_, sunflower_upperbounds k r⟩
  · exact this.imp fun _ ↦ and_assoc.1
  · simpa using NeZero.ne r

private lemma sunflower_bounds_nat' {k r : ℕ} (family : Finset (Finset ℕ))
    (hₖ : ∀ S ∈ family, #S = k) (h : IsSunflowerFree family r) :
    #family ≤ maxSunflowerFreeCard k r :=
  le_csSup ⟨_, sunflower_upperbounds k r⟩ ⟨family, ⟨hₖ, h⟩, rfl⟩

theorem sunflower_bounds_nat {k r : ℕ} (family : Finset (Finset ℕ)) (hₖ : ∀ S ∈ family, #S ≤ k)
    (h : IsSunflowerFree family r) : #family ≤ maxSunflowerFreeCard k r := by
  let univ := family.sup id
  let compl := (univ : Set ℕ)ᶜ
  have compl_inf : compl.Infinite := Set.Finite.infinite_compl univ.finite_toSet
  let family₀ := family.attach
  have hc (s : family) : ∃ t : Finset ℕ, #t = k ∧ t ∩ univ = s.val := by
    rcases compl_inf.exists_subset_card_eq (k - #s.val) with ⟨sc, scc, csc⟩
    have h₁ : Disjoint sc univ := by
      rw [← Finset.disjoint_coe]
      exact disjoint_compl_left.mono_left scc
    have h₂ : s.val ⊆ univ := by
      simp only [univ]
      exact Finset.le_sup (f := id) s.property
    refine ⟨s ∪ sc, ?_, ?_⟩
    · rw [Finset.card_union_eq_card_add_card.2 (h₁.symm.mono_left h₂), csc]
      exact Nat.add_sub_cancel' (hₖ s.val s.property)
    · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 h₂]
      convert s.val.union_empty
      rwa [← Finset.disjoint_iff_inter_eq_empty]
  rcases Classical.axiomOfChoice hc with ⟨φ', φspec⟩
  let φ : family ↪ Finset ℕ := {
    toFun := φ'
    inj' x y h := Subtype.ext (by rw [← (φspec x).2, ← (φspec y).2, h])
  }
  have := @sunflower_bounds_nat' k r (family.attach.map φ) ?_ (fun sub₀ ss₀ sf₀ ↦ ?_)
  · simpa using this
  · simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, forall_exists_index]
    rintro - S Sf rfl
    exact (φspec ⟨S, Sf⟩).1
  · simp only [Finset.subset_map_iff] at ss₀
    rcases ss₀ with ⟨sub, ss, rfl⟩
    refine h (sub.map (Function.Embedding.subtype _)) ?_ ?_
    · intro
      simp
      tauto
    · rcases sf₀ with ⟨card₀, core₀, core₀spec⟩
      simp only [Finset.card_map] at card₀
      refine ⟨?_, core₀ ∩ univ, fun S T Sf Tf ST ↦ ?_⟩
      · simpa
      · simp only [Finset.mem_map, Function.Embedding.subtype_apply, Subtype.exists,
          exists_and_right, exists_eq_right] at Sf Tf
        rcases Sf with ⟨Sf, Sft⟩
        rcases Tf with ⟨Tf, Tft⟩
        change ⟨S, Sf⟩ ∈ sub at Sft
        change ⟨T, Tf⟩ ∈ sub at Tft
        have := core₀spec (φ ⟨S, Sf⟩) (φ ⟨T, Tf⟩) (by simpa) (by simpa) (by simpa)
        have it := congr($this ∩ univ)
        have gS : φ ⟨S, Sf⟩ ∩ univ = S := (φspec ⟨S, Sf⟩).2
        have gT : φ ⟨T, Tf⟩ ∩ univ = T := (φspec ⟨T, Tf⟩).2
        rwa [Finset.inter_inter_distrib_right, gS, gT] at it

variable {α : Type u} [DecidableEq α]

theorem sunflower_exists [Infinite α] (k r : ℕ) [NeZero r] : ∃ family : Finset (Finset α),
    (∀ S ∈ family, #S = k) ∧ IsSunflowerFree family r ∧ #family = maxSunflowerFreeCard k r := by
  have φ := Infinite.natEmbedding α
  rcases sunflower_exists_nat k r with ⟨family, hₖ, h, cf⟩
  refine ⟨family.map (Finset.mapEmbedding φ).toEmbedding, ?_, ?_, ?_⟩
  · simp only [Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    change ∀ S ∈ family, #(S.map φ) = k
    simpa
  · simpa
  · simpa

private lemma sunflower_bounds_countable [Countable α] {k r : ℕ} (family : Finset (Finset α))
    (hₖ : ∀ S ∈ family, #S ≤ k) (h : IsSunflowerFree family r) :
    #family ≤ maxSunflowerFreeCard k r := by
  rcases Countable.exists_injective_nat α with ⟨φ', φ_inj⟩
  have φ : α ↪ ℕ := ⟨φ', φ_inj⟩
  have := @sunflower_bounds_nat k r
    (family.map (Finset.mapEmbedding φ).toEmbedding)
    (by
      simp only [Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      change ∀ S ∈ family, #(S.map φ) ≤ k
      simpa)
    (by simpa)
  simpa using this

theorem sunflower_bounds {k r : ℕ} (family : Finset (Finset α)) (hₖ : ∀ S ∈ family, #S ≤ k)
    (h : IsSunflowerFree family r) : #family ≤ maxSunflowerFreeCard k r := by
  let univ := family.sup id
  have univ_fin := univ.finite_toSet
  let β := ↥univ
  have β_fin : Finite β := univ_fin
  let φ : β ↪ α := Function.Embedding.subtype _
  let Φ : Finset β ↪ Finset α := (Finset.mapEmbedding φ).toEmbedding
  let family' := family.preimage Φ Φ.injective.injOn
  have rt : family = family'.map Φ := by
    simp only [family']
    rw [Finset.map_eq_image, Finset.image_preimage_of_bij]
    refine ⟨fun _ ↦ id, Φ.injective.injOn,
      fun s sf ↦ ⟨s.preimage φ φ.injective.injOn, ?_⟩⟩
    suffices h : Φ (s.preimage φ φ.injective.injOn) = s by simpa [h]
    simp only [Φ, Finset.le_eq_subset, RelEmbedding.coe_toEmbedding]
    rw [Finset.mapEmbedding_apply, Finset.map_eq_image, Finset.image_preimage_of_bij]
    refine ⟨fun _ ↦ id, φ.injective.injOn,
      fun x xs ↦ ?_⟩
    have xu : x ∈ univ := by
      simp only [univ, Finset.mem_sup]
      exact ⟨s, sf, xs⟩
    exact ⟨⟨x, xu⟩, xs, rfl⟩
  simp only [rt, Φ, Finset.le_eq_subset, IsSunflowerFree_map_iff, Finset.mem_map,
    RelEmbedding.coe_toEmbedding, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Finset.card_map, ge_iff_le, Φ] at h hₖ ⊢
  refine sunflower_bounds_countable (k := k) family' (fun S Sf ↦ ?_) h
  have : #(S.map φ) ≤ k := hₖ S Sf
  simpa using this
