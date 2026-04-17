module

public import Mathlib

@[expose] public section

open Real Set Function Finset Rat

def IsAdditive {α β : Type*} [Add α] [Add β] (f : α → β) : Prop :=
  ∀ x y, f (x + y) = f x + f y

namespace IsAdditive

theorem ofHom {α β : Type*} [AddZero α] [AddZero β] (f : α →+ β) :
    IsAdditive f := AddMonoidHom.map_add f

abbrev toHom {α β : Type*} [AddMonoid α] [AddGroup β] {f : α → β} (h : IsAdditive f) : α →+ β where
  toFun := f
  map_add' := h
  map_zero' := by
    have := h 0 0
    simp only [add_zero, left_eq_add] at this
    exact this

theorem add_additive {f g : ℝ → ℝ} (hf : IsAdditive f) (hg : IsAdditive g) :
    IsAdditive (f + g) := by
  intro _ _
  dsimp
  rw [hf, hg]
  ring

theorem neg_additive {f : ℝ → ℝ} (hf : IsAdditive f) : IsAdditive (- f) := by
  intro x y
  dsimp
  rw [hf x y, neg_add]

@[simp]
theorem of_const_zero : IsAdditive (0 : ℝ → ℝ) := by
  simp [IsAdditive]

@[simp]
theorem of_const_mul {r : ℝ} : IsAdditive (fun x ↦ r * x) := by
  intro _ _
  ring

@[simp]
theorem of_mul_const {r : ℝ} : IsAdditive (fun x ↦ x * r) := by
  intro _ _
  ring

@[simp]
theorem id : IsAdditive (id : ℝ → ℝ) := by
  intro _ _
  rfl

@[simp]
theorem of_neg : IsAdditive (fun x ↦ -x) := by
  intro _ _
  ring

variable {f : ℝ → ℝ}

@[simp]
theorem zero (hf : IsAdditive f) : f 0 = 0 := by
  have := hf 0 0
  simp_all

theorem sum_finset (hf : IsAdditive f) {ι : Type*} (r : ι → ℝ) (s : Finset ι) :
    ∑ x ∈ s, f (r x) = f (∑ x ∈ s, r x) := by
  classical
  induction s using Finset.induction with
  | empty => simp [zero hf]
  | insert i s is hs => rw [sum_insert is, sum_insert is, hs, hf (r i)]

theorem nat_mul (hf : IsAdditive f) (n : ℕ) (x : ℝ) : f (n * x) = n * f x := by
  calc
    f (n * x) = f (∑ i ∈ range n, x) := by simp
      _ = ∑ i ∈ range n, f x := by rw [sum_finset hf]
      _ = n * f x := by simp

theorem mul_nat (hf : IsAdditive f) (n : ℕ) (x : ℝ) : f (x * n) = f x * n := by
  rw [mul_comm, nat_mul hf, mul_comm (f x)]

theorem neg (hf : IsAdditive f) (x : ℝ) : f (- x) = - f x := by
  have := hf x (-x)
  simp only [add_neg_cancel, zero hf] at this
  rw [← add_zero (- f x), this]
  ring

theorem int_mul (hf : IsAdditive f) (n : ℤ) (x : ℝ) : f (n * x) = n * f x := by
  by_cases! hn : 0 ≤ n
  · have : (↑n : ℝ) = n.toNat := by
      rw [← Int.toNat_of_nonneg hn]
      rfl
    rw [this, nat_mul hf]
  have : (↑n : ℝ) = -((-(↑n : ℤ)).toNat : ℝ) := by
      apply Eq.trans (b := -↑((-n).toNat : ℤ))
      · rw [Int.toNat_of_nonneg (by simp [hn.le])]
        simp
      · simp [-Int.ofNat_toNat]
  rw [this, neg_mul, neg_mul, ← nat_mul hf, neg hf]

theorem mul_int (hf : IsAdditive f) (n : ℤ) (x : ℝ) : f (x * n) = f x * n := by
  rw [mul_comm, int_mul hf, mul_comm]

theorem inv_nat_mul (hf : IsAdditive f) {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    f ((↑n : ℝ)⁻¹ * x) = (↑n : ℝ)⁻¹ * f x := by
  have : (↑n : ℝ) ≠ 0 := by simpa
  apply (mul_right_inj' this).mp
  rw [← nat_mul hf, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ this, one_mul, one_mul]

theorem rat_mul (hf : IsAdditive f) (r : ℚ) (x : ℝ) : f (r * x) = r * f x := by
  by_cases hr : r = 0
  · simp [hr, zero hf]
  have : (↑r.den : ℝ) ≠ 0 := by simp
  apply (mul_right_inj' this).mp
  have (a b : ℚ) : (↑(a * b) : ℝ) = (↑a : ℝ) * b := by
    exact cast_mul a b
  have (m : ℕ) : (↑m : ℝ) = (↑(↑m : ℚ) : ℝ) := ext_cauchy rfl
  rw [← nat_mul hf, ← mul_assoc, ← mul_assoc, this, ← cast_mul,
    den_mul_eq_num, cast_intCast, int_mul hf]

theorem ofNat (hf : IsAdditive f) (n : ℕ) : f n = n * f 1 := by
  rw [← mul_one n, Nat.cast_mul, nat_mul hf, Nat.cast_one, mul_one]

theorem ofInt (hf : IsAdditive f) (n : ℤ) : f n = n * f 1 := by
  rw [← mul_one n, Int.cast_mul, int_mul hf, Int.cast_one, mul_one]

theorem ofRat (hf : IsAdditive f) (r : ℚ) : f r = r * f 1 := by
  rw [← mul_one r, cast_mul, rat_mul hf, cast_one, mul_one]

-- Major TODO : If the graph of an additive function is not dense, it is linear. -/
/-
theorem linear_of_not_dense (hf : IsAdditive f) (h : ¬ Dense (graph f)) (x : ℝ) :
    f x = x * f 1 := by
  sorry
-/

--to mathlib?
theorem _root_.monotone_iff_neg_antitone {α β : Type*} [Preorder α] [AddGroup β] [Preorder β]
    [AddLeftMono β] [AddRightMono β] {f : α → β} : Monotone f ↔ Antitone (-f) :=
  ⟨fun h _ _ ab ↦ neg_le_neg_iff.mpr <| h ab, fun h _ _ ab ↦ neg_le_neg_iff.mp <| h ab⟩

--to mathlib?
theorem _root_.antitone_iff_neg_monotone {α β : Type*} [Preorder α] [AddGroup β] [Preorder β]
    [AddLeftMono β] [AddRightMono β] {f : α → β} : Antitone f ↔ Monotone (-f) :=
  ⟨fun h _ _ ab ↦ neg_le_neg_iff.mpr <| h ab, fun h _ _ ab ↦ neg_le_neg_iff.mp <| h ab⟩

private lemma ofMonotone_spec (hf : IsAdditive f) (fm : Monotone f) (x : ℝ) (op : 0 ≤ f 1) :
    f x = x * f 1 := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add (fun e epos ↦ ?_)
    suffices ∃ q : ℚ, x ≤ q ∧ f q ≤ x * f 1 + e by
      obtain ⟨p, hp⟩ := this
      apply le_trans <| fm hp.1
      exact hp.2
    by_cases ot : f 1 = 0
    · rw [ot]
      obtain ⟨q, hq⟩ := exists_rat_gt x
      refine ⟨q, hq.le, ?_⟩
      rw [ofRat hf, ot]
      simp [epos.le]
    have : x < x + e / f 1 := by
      simp only [lt_add_iff_pos_right]
      exact div_pos epos (by order)
    obtain ⟨q, hq, hq'⟩ := exists_rat_btwn this
    refine ⟨q, hq.le, ?_⟩
    rw [ofRat hf]
    calc
      _ ≤ (x + e / f 1) * f 1 := by gcongr
      _ = x * f 1 + e := by
        rw [add_mul]
        simp only [add_right_inj]
        exact div_mul_cancel₀ e ot
  apply le_of_forall_pos_le_add (fun e epos ↦ ?_)
  suffices ∃ q : ℚ, q ≤ x ∧ x * f 1 ≤ f q + e by
    obtain ⟨p, hp⟩ := this
    exact le_trans hp.2 <| add_le_add_left (fm hp.1) e
  rcases eq_or_ne (f 1) 0 with ot|ot
  · rw [ot]
    obtain ⟨q, hq⟩ := exists_rat_lt x
    refine ⟨q, hq.le, ?_⟩
    rw [ofRat hf, ot]
    simp [epos.le]
  have : x - e / f 1 < x := by
    simp only [sub_lt_self_iff]
    exact div_pos epos (by order)
  obtain ⟨q, hq, hq'⟩ := exists_rat_btwn this
  refine ⟨q, hq'.le, ?_⟩
  rw [ofRat hf]
  replace hq : x < q + e / f 1 := lt_add_of_tsub_lt_right hq
  calc
    _ ≤ (q + e / f 1) * f 1 := by gcongr
    _ = q * f 1 + e := by
      rw [add_mul]
      simp only [add_right_inj]
      exact div_mul_cancel₀ e ot

theorem ofMonotone (hf : IsAdditive f) (fm : Monotone f) (x : ℝ) :
    f x = x * f 1 := by
  rcases le_or_gt 0 (f 1) with h|h
  · exact ofMonotone_spec hf fm x h
  let g : ℝ → ℝ := f + (fun x ↦ x * - f 1)
  have hg : Monotone g := by
    intro x y xy
    unfold g
    dsimp
    gcongr
    · exact fm xy
    · simp [h.le]
  replace hg := ofMonotone_spec (add_additive hf of_mul_const) hg x
  simp at hg
  linarith

theorem ofAntitone (hf : IsAdditive f) (fm : Antitone f) (x : ℝ) :
    f x = x * f 1 := by
  have := ofMonotone (neg_additive hf) (antitone_iff_neg_monotone.mp fm) x
  simp only [Pi.neg_apply, mul_neg, neg_inj] at this
  exact this

--TODO: Above can be generalised to monotone (antitone) on some interval

end IsAdditive
