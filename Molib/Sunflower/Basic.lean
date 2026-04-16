module

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.NAry
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Tactic.Peel
public import Molib.Sunflower.Defs

@[expose] public section

open scoped Finset Nat

variable {α : Type u} [DecidableEq α] (family : Finset (Finset α))

namespace SunflowerLemma

lemma k_le_1 (h₁ : ∀ S ∈ family, #S ≤ 1) (r : ℕ) : IsSunflowerFree family r ↔ #family < r := by
  refine ⟨fun h ↦ ?_, fun h s s₁ sf ↦ Nat.ne_of_lt
    (Nat.lt_of_le_of_lt (Finset.card_le_card s₁) h) sf.1⟩
  by_contra! h
  rw [Finset.le_card_iff_exists_subset_card] at h
  rcases h with ⟨s, s₁, sc⟩
  refine h s s₁ ⟨sc, ∅, fun S T Ss Ts ST ↦ Finset.eq_empty_of_forall_notMem fun x xst ↦ ST ?_⟩
  have S₁ := h₁ S (s₁ Ss)
  have T₁ := h₁ T (s₁ Ts)
  simp only [Finset.mem_inter] at xst
  rw [Finset.card_le_one_iff_subsingleton] at S₁ T₁
  have Sd := S₁.eq_singleton_of_mem xst.1
  have Td := T₁.eq_singleton_of_mem xst.2
  simp at Sd Td
  exact Sd.trans Td.symm

theorem main {k : ℕ} (hₖ : ∀ S ∈ family, #S ≤ k) {r : ℕ} (h : IsSunflowerFree family r) :
    #family ≤ k ! * (r - 1) ^ k := by
  induction k generalizing family with
  | zero =>
    simp only [Nat.factorial_zero, pow_zero, mul_one, Finset.card_le_one]
    intro S Ss T Ts
    simp at hₖ
    simp [hₖ S Ss, hₖ T Ts]
  | succ k i =>
    by_cases! r₁ : r ≤ 1
    · rw [IsSunflowerFree_le_two] at h <;> omega
    let 𝒟j (subfamily : Finset (Finset α)) := Set.PairwiseDisjoint (subfamily : Set (Finset α)) id
    let : DecidablePred 𝒟j := fun subfamily ↦ Finset.decidableDforallFinset
    let 𝒟jf := { subfamily ∈ family.powerset | 𝒟j subfamily }
    have h₁ : 𝒟jf.Nonempty := ⟨∅, by simp [𝒟jf, 𝒟j]⟩
    rcases 𝒟jf.exists_maximal h₁ with ⟨W, h₂, h₃⟩
    simp only [𝒟jf, Finset.mem_filter, Finset.mem_powerset] at h₂
    rcases h₂ with ⟨Wsub, 𝒟jW⟩
    replace h₃ (subfamily : Finset (Finset α)) (d : 𝒟j subfamily)
      (U : subfamily ⊆ family) (Ws : W ⊆ subfamily) : subfamily = W := by
      refine le_antisymm (h₃ ?_ Ws) Ws
      simp [𝒟jf, d, U]
    have cW : #W < r := by
      by_contra! rW
      rw [Finset.le_card_iff_exists_subset_card] at rW
      rcases rW with ⟨W₀, W₀W, cW₀⟩
      exact h W₀ (W₀W.trans Wsub) ⟨cW₀, ∅, fun S T SW₀ TW₀ ST ↦
        disjoint_iff.1 (𝒟jW (W₀W SW₀) (W₀W TW₀) ST)⟩
    let ℱ a := { W₁ ∈ family | a ∈ W₁ }
    let 𝒲 a := (ℱ a).image (Finset.erase · a)
    let ℱ𝒲 a : PartialEquiv (Finset α) (Finset α) := {
      toFun s := s.erase a
      invFun := insert a
      source := ℱ a
      target := 𝒲 a
      map_source' s h := by
        simp only [𝒲, Finset.coe_image, Set.mem_image, SetLike.mem_coe]
        exists s
      map_target' s h := by
        simp only [𝒲, Finset.coe_image, Set.mem_image, SetLike.mem_coe] at h
        rcases h with ⟨s, sℱa, rfl⟩
        convert sℱa
        refine Finset.insert_erase ?_
        simp only [ℱ, Finset.mem_filter] at sℱa
        exact sℱa.2
      left_inv' s h := by
        refine Finset.insert_erase ?_
        simp only [ℱ, Finset.coe_filter, Set.mem_setOf_eq] at h
        exact h.2
      right_inv' s h := by
        refine Finset.erase_insert ?_
        simp only [𝒲, Finset.coe_image, Set.mem_image, SetLike.mem_coe] at h
        rcases h with ⟨s, sℱa, rfl⟩
        exact s.notMem_erase a
    }
    have hₖ' a S (Ss : S ∈ 𝒲 a) : #S ≤ k := by
      simp only [𝒲, ℱ, Finset.mem_image, Finset.mem_filter] at Ss
      rcases Ss with ⟨S, ⟨SW, aS⟩, rfl⟩
      rw [Finset.card_erase_of_mem aS]
      exact Nat.pred_le_of_le_succ (hₖ S SW)
    have h' a : IsSunflowerFree (𝒲 a) r := by
      intro s s₁ sf
      let t := s.image (insert a)
      refine h t ?_ ⟨?_, ?_⟩
      · intro ω ωt
        simp only [t, Finset.mem_image] at ωt
        rcases ωt with ⟨ω, ωs, rfl⟩
        have c : insert a ω ∈ ℱ a := (ℱ𝒲 a).map_target' (s₁ ωs)
        simpa [ℱ] using c
      · rw [← sf.1, Finset.card_image_iff]
        exact (ℱ𝒲 a).symm.injOn.mono s₁
      · rcases sf.2 with ⟨core, core_spec⟩
        refine ⟨insert a core, fun S T St Tt ST ↦ ?_⟩
        simp only [t, Finset.mem_image] at St Tt
        rcases St with ⟨S, Ss, rfl⟩
        rcases Tt with ⟨T, Ts, rfl⟩
        have := core_spec S T Ss Ts (fun h ↦ ST (h ▸ rfl))
        rw [Finset.insert_eq, Finset.insert_eq, ← Finset.union_inter_distrib_left,
          ← Finset.insert_eq, this]
    have c𝒲 a := i (𝒲 a) (hₖ' a) (h' a)
    have cℱ a : #(ℱ a) ≤ k ! * (r - 1)^k := by
      convert c𝒲 a using 1
      exact (ℱ𝒲 a).bijOn.finsetCard_eq
    let W₀ := W.erase ∅
    let A := W₀.sup id
    have cA : #A ≤ #W₀ * (k + 1) := by
      calc
        _ ≤ ∑ s ∈ W₀, #s := W₀.apply_sup_le_sum (f := Finset.card)
          Finset.card_empty (@Finset.card_union_le α _) (s := id)
        _ ≤ _ := W₀.sum_le_card_nsmul Finset.card (k + 1)
          fun s sW ↦ hₖ s (Wsub (W.mem_of_mem_erase sW))
    have tot : family.erase ∅ ⊆ A.sup ℱ := by
      intro s h
      simp only [Finset.mem_erase] at h
      rcases h with ⟨s₀, sf⟩
      simp only [A, Finset.mem_sup]
      by_cases 𝒟ji : 𝒟j (insert s W)
      · have sW := h₃ (insert s W) 𝒟ji (W.insert_subset sf Wsub) (W.subset_insert s)
        simp only [Finset.insert_eq_self] at sW
        rcases s.nonempty_of_ne_empty s₀ with ⟨a, as⟩
        refine ⟨a, ⟨s, ?_, as⟩, ?_⟩
        · simp only [W₀, Finset.mem_erase]
          exact ⟨s₀, sW⟩
        · simp only [ℱ, Finset.mem_filter]
          exact ⟨sf, as⟩
      · unfold 𝒟j at 𝒟ji 𝒟jW
        rw [Finset.coe_insert, Set.pairwiseDisjoint_insert] at 𝒟ji
        simp only [𝒟jW, SetLike.mem_coe, true_and, not_forall] at 𝒟ji
        rcases 𝒟ji with ⟨t, tW, st, dst⟩
        rcases Finset.not_disjoint_iff.1 dst with ⟨a, as, at'⟩
        refine ⟨a, ⟨t, ?_, at'⟩, ?_⟩
        · simp only [W₀, Finset.mem_erase]
          refine ⟨fun t₀ ↦ ?_, tW⟩
          simp [t₀] at at'
        · simp only [ℱ, Finset.mem_filter]
          exact ⟨sf, as⟩
    have tot' : #(family.erase ∅) ≤ (k + 1)! * #W₀ * (r - 1)^k := by
      calc
        _ ≤ #(A.sup ℱ) := Finset.card_le_card tot
        _ ≤ ∑ a ∈ A, #(ℱ a) := A.apply_sup_le_sum (f := Finset.card) Finset.card_empty
          (@Finset.card_union_le (Finset α) _) (s := ℱ)
        _ ≤ #A * (k ! * (r - 1)^k) := A.sum_le_card_nsmul _ _ fun a _ ↦ cℱ a
        _ ≤ _ := by
          grw [cA, k.factorial_succ]
          ac_nf
    by_cases f₀ : ∅ ∈ family
    · rw [Finset.card_erase_of_mem f₀] at tot'
      replace tot' : #family ≤ _ + 1 := Nat.le_succ_of_pred_le tot'
      grw [tot']
      rw [Nat.pow_succ', ← Nat.mul_assoc]
      nth_grw 2 [← show #W ≤ r - 1 from Nat.le_pred_of_lt cW]
      have W₀' : ∅ ∈ W := by
        have := h₃ (insert ∅ W) ?_ (W.insert_subset f₀ Wsub) (W.subset_insert ∅)
        · simpa only [Finset.insert_eq_self] using this
        unfold 𝒟j
        rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
        refine ⟨𝒟jW, ?_⟩
        simp
      have W₀'' : #W₀ + 1 = #W := W.card_erase_add_one W₀'
      rw [← W₀'']
      rw [Nat.mul_succ, Nat.add_mul]
      gcongr
      refine Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos ?_)
      omega
    · rw [Finset.erase_eq_of_notMem f₀] at tot'
      grw [tot']
      rw [Nat.pow_succ', ← Nat.mul_assoc]
      gcongr
      grw [W.card_erase_le]
      exact Nat.le_pred_of_lt cW

theorem lower (k r : ℕ) [NeZero k] [NeZero r] : ∃ family : Finset (Finset ℕ),
    (∀ S ∈ family, #S = k) ∧ IsSunflowerFree family r ∧ #family = (r - 1)^k := by
  have k₁ : 1 ≤ k := Nat.pos_of_neZero k
  induction k, k₁ using Nat.le_induction with
  | base =>
    let φ : ℕ ↪ Finset ℕ := {
      toFun := Singleton.singleton
      inj' := Finset.singleton_injective
    }
    let family := (Finset.range (r - 1)).map φ
    have fc S (h : S ∈ family) : #S = 1 := by
      simp only [family, Finset.mem_map, Finset.mem_range] at h
      rcases h with ⟨a, -, rfl⟩
      simp [φ]
    have cf : #family = r - 1 := by simp [family]
    refine ⟨family, fc, ?_, ?_⟩
    · rw [k_le_1, cf]
      · exact Nat.pred_lt (NeZero.ne r)
      peel fc
      simp [this]
    · simp [cf]
  | succ k k₁ h =>
    rcases h with ⟨family, fk, fsf, cf⟩
    let univ := family.sup id
    let compl := (univ : Set ℕ)ᶜ
    have compl_inf : compl.Infinite := Set.Finite.infinite_compl univ.finite_toSet
    rcases compl_inf.exists_subset_card_eq (r - 1) with ⟨𝒜, 𝒜compl, c𝒜⟩
    have D𝒜 S (sf : S ∈ family) : Disjoint S 𝒜 := by
      grw [← Finset.disjoint_coe, 𝒜compl, Set.disjoint_compl_right_iff_subset]
      intro x xS
      simp only [univ, SetLike.mem_coe, Finset.mem_sup]
      exact ⟨S, sf, xS⟩
    have bij : Set.BijOn (fun (x : ℕ × Finset ℕ) ↦ insert x.1 x.2)
      (𝒜 ×ˢ family : Finset (ℕ × Finset ℕ))
      (𝒜.image₂ insert family) := by
      simp only [Finset.coe_product, Finset.coe_image₂]
      and_intros
      · exact fun ⟨a, b⟩ ⟨a𝒜, bf⟩ ↦ ⟨a, a𝒜, b, bf, rfl⟩
      · intro ⟨a₁, b₁⟩ ⟨a₁𝒜, b₁f⟩ ⟨a₂, b₂⟩ ⟨a₂𝒜, b₂f⟩ h
        simp only [Prod.mk.injEq] at *
        have ca a b (a𝒜 : a ∈ 𝒜) (bf : b ∈ family) : insert a b ∩ univ = b := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_insert]
          refine ⟨fun h ↦ h.1.resolve_left ?_, fun h ↦ ⟨Or.inr h, ?_⟩⟩
          · rintro rfl
            exact 𝒜compl a𝒜 h.2
          · simp only [univ, Finset.mem_sup]
            exact ⟨b, bf, h⟩
        have b₁₂ : b₁ = b₂ := by
          have h₁ := congr($h ∩ univ)
          rwa [ca a₁ b₁ a₁𝒜 b₁f, ca a₂ b₂ a₂𝒜 b₂f] at h₁
        cases b₁₂
        specialize D𝒜 b₁ b₁f
        refine ⟨Finset.insert_inj_on b₁ ?_ ?_ h, rfl⟩
        · exact D𝒜.notMem_of_mem_right_finset a₁𝒜
        · exact D𝒜.notMem_of_mem_right_finset a₂𝒜
      · rintro _ ⟨a, a𝒜, b, bf, rfl⟩
        exact ⟨⟨a, b⟩, ⟨a𝒜, bf⟩, rfl⟩
    refine ⟨𝒜.image₂ insert family, fun S Sf ↦ ?_, fun sub₀ sub₀s sf₀ ↦ ?_, ?_⟩
    · simp only [Finset.mem_image₂] at Sf
      rcases Sf with ⟨a, a𝒜, b, bf, rfl⟩
      rw [Finset.card_insert_of_notMem, fk b bf]
      exact (D𝒜 b bf).notMem_of_mem_right_finset a𝒜
    · rcases sf₀ with ⟨csub₀, core₀, core₀spec⟩
      let φ := Function.invFunOn (fun (x : ℕ × Finset ℕ) ↦ insert x.1 x.2)
        (𝒜 ×ˢ family : Finset (ℕ × Finset ℕ))
      have φspec₁ : Set.InvOn φ _ _ _ := bij.invOn_invFunOn
      have φspec₂ := φspec₁.left.mapsTo bij.surjOn
      have φspec₃ := φspec₁.symm.bijOn φspec₂ bij.mapsTo
      let msub₀ := sub₀.image φ
      have msub₀sub : msub₀ ⊆ 𝒜 ×ˢ family := by
        rw [Finset.image_subset_iff]
        intro x xs
        simpa using φspec₂ (sub₀s xs)
      have φspec₁' : Set.InvOn φ (fun (x : ℕ × Finset ℕ) ↦ insert x.1 x.2) msub₀ sub₀ :=
        φspec₁.mono msub₀sub sub₀s
      have φspec₂' : Set.BijOn φ sub₀ msub₀ := by
        convert φspec₃.subset_left sub₀s
        simp only [Finset.coe_image, msub₀]
      have φspec₃' : Set.BijOn (fun (x : ℕ × Finset ℕ) ↦ insert x.1 x.2) msub₀ sub₀ :=
        φspec₂'.symm φspec₁'
      have cmsub₀ : #msub₀ = r := by rwa [Finset.card_image_iff.2 φspec₂'.injOn]
      have msubproj x (hx : x ∈ msub₀) : x.1 ∈ 𝒜 ∧ x.2 ∈ family := by
        have := msub₀sub hx
        simpa only [Finset.mem_product] using this
      have pigeonhole := msub₀.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (n := 1) (fun x hx ↦ (msubproj x hx).1)
        (by simp [c𝒜, cmsub₀, r.pos_of_neZero])
      rcases pigeonhole with ⟨a, a𝒜, fiber_lt⟩
      rw [Finset.one_lt_card] at fiber_lt
      rcases fiber_lt with ⟨⟨a₁, b₁⟩, bf₁, ⟨a₂, b₂⟩, bf₂, b₁₂⟩
      simp only [Finset.mem_filter] at bf₁ bf₂ b₁₂
      cases bf₁.2
      cases bf₂.2
      simp only [and_true] at bf₁ bf₂ b₁₂
      have acore₀ : a ∈ core₀ := by
        rw [← core₀spec (insert a b₁) (insert a b₂) (φspec₃'.mapsTo bf₁) (φspec₃'.mapsTo bf₂)]
        · simp
        · contrapose b₁₂
          have := φspec₃'.injOn bf₁ bf₂ b₁₂
          simpa only [Prod.mk.injEq, true_and] using this
      have alla x (hx : x ∈ msub₀) : x.1 = a := by
        by_contra h
        rw [← core₀spec (insert a b₁) (insert x.1 x.2)
          (φspec₃'.mapsTo bf₁) (φspec₃'.mapsTo hx)] at acore₀
        · simp at acore₀
          refine acore₀.elim (h ∘ Eq.symm) fun ax₂ ↦ 𝒜compl a𝒜 ?_
          simp only [univ, SetLike.mem_coe, Finset.mem_sup]
          exact ⟨x.2, (msubproj x hx).2, ax₂⟩
        · contrapose h
          have := φspec₃'.injOn bf₁ hx h
          rw [Prod.mk.injEq] at this
          exact this.1.symm
      refine fsf (msub₀.image Prod.snd) ?_ ⟨?_, core₀.erase a, fun S T Si Ti ST ↦ ?_⟩
      · simp only [Finset.image_subset_iff]
        exact fun x hx ↦ (msubproj x hx).2
      · rwa [Finset.card_image_iff.2]
        intro x hx y hy xy
        rw [Prod.mk.injEq]
        simp [xy, alla x hx, alla y hy]
      · simp only [Finset.mem_image, Prod.exists, exists_eq_right] at Si Ti
        rcases Si with ⟨a₁, Si⟩
        rcases Ti with ⟨a₂, Ti⟩
        have a₁spec : a₁ = a := alla _ Si
        have a₂spec : a₂ = a := alla _ Ti
        cases a₁spec
        cases a₂spec
        rw [← core₀spec (insert a S) (insert a T) (φspec₃'.mapsTo Si) (φspec₃'.mapsTo Ti)]
        · rw [Finset.insert_eq, Finset.insert_eq,
            ← Finset.union_inter_distrib_left, ← Finset.insert_eq, Finset.erase_insert]
          simp only [Finset.mem_inter, not_and]
          refine fun aS aT ↦ 𝒜compl a𝒜 ?_
          simp only [univ, SetLike.mem_coe, Finset.mem_sup]
          exact ⟨S, (msubproj _ Si).2, aS⟩
        · contrapose ST
          have := φspec₃'.injOn Si Ti ST
          simpa only [Prod.mk.injEq, true_and] using this
    · rw [Finset.card_image₂_iff.2, c𝒜, cf, Nat.pow_succ']
      convert bij.injOn
      simp only [Finset.coe_product]

end SunflowerLemma
