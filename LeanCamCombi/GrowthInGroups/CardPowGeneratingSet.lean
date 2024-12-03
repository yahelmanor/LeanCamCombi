/-
Copyright (c) 2024 Yaël Dillies, Patrick Luo, Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Eric Rodriguez
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.Nat.SuccPred
import LeanCamCombi.Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Linear lower bound on the growth of a generating set

This file proves that the growth of a set generating an infinite group is at least linear.
-/

open Subgroup
open scoped Pointwise

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {X : Finset G} {n : ℕ}

@[to_additive]
lemma card_pow_lt_card_pow_succ_of_pow_ne_closure (hX₁ : (1 : G) ∈ X) (hX : X.Nontrivial)
    (hXclosure : (X ^ n : Set G) ≠ closure (X : Set G)) : #(X ^ n) < #(X ^ (n + 1)) := by
  obtain rfl | hn := eq_or_ne n 0
  · simpa [one_lt_card_iff_nontrivial]
  contrapose! hXclosure with hXn
  rw [← closure_pow (mod_cast hX₁) hn]
  have heq : X ^ n = X ^ (n + 1) := eq_of_subset_of_card_le (pow_subset_pow_right hX₁ n.le_succ) hXn
  wlog hn₁ : n = 1
  · simp +contextual only [pow_one] at this
    replace heq d : X ^ (n + d) = X ^ n := by
      induction' d with d hd
      . rw [add_zero]
      . rw [pow_add, pow_one] at heq
        rw [← add_assoc, pow_add, pow_one, hd, ← heq]
    exact mod_cast this (one_mem_pow hX₁) (hX.pow hn) one_ne_zero
      (by simp [heq, ← pow_mul, mul_two]) (by simp [heq, ← pow_mul, mul_two]) rfl
  subst hn₁
  simp only [ne_eq, one_ne_zero, not_false_eq_true, Nat.reduceAdd, pow_one] at *
  let Xgp : Subgroup G :=
  { carrier := X
    mul_mem' := fun {x y} hx hy ↦ by
      norm_cast at *
      simpa [← heq, ← sq] using mul_mem_mul hx hy
    one_mem' := hX₁
    inv_mem' := fun {x} hx ↦ by
      dsimp at *
      norm_cast at *
      have : x • X ⊆ X := by
        simpa [← heq, add_assoc, ← sq] using smul_finset_subset_mul (t := X) hx
      have : x • X = X := eq_of_subset_of_card_le this (card_smul_finset ..).ge
      rw [← eq_inv_smul_iff] at this
      rw [this]
      simpa [mem_inv_smul_finset_iff] }
  exact subset_closure.antisymm <| (closure_le Xgp).2 subset_rfl

@[to_additive]
lemma card_pow_strictMonoOn (hX₁ : 1 ∈ X) (hX : X.Nontrivial) :
    StrictMonoOn (fun n ↦ #(X ^ n)) {n | (X ^ (n - 1) : Set G) ≠ closure (X : Set G)} := by
  refine strictMonoOn_of_lt_add_one ⟨?_⟩ fun n _ _ hn ↦
    card_pow_lt_card_pow_succ_of_pow_ne_closure hX₁ hX hn
  rintro - - n hn m ⟨-, hmn⟩ hm
  apply hn
  obtain rfl | hm₀ := m.eq_zero_or_pos
  · simp at hm
    rw [← hm]
    rw [eq_comm, coe_set_eq_one, closure_eq_bot_iff] at hm
    cases hX.not_subset_singleton hm
  calc (X : Set G) ^ (n - 1) = X ^ (n - m) * X ^ (m - 1) := by rw [← pow_add]; congr 1; omega
  _ = closure (X : Set G) := by rw [hm, Set.pow_mul_subgroupClosure hX.nonempty.to_set]

@[to_additive]
lemma card_pow_strictMono (hX₁ : 1 ∈ X) (hXclosure : (closure (X : Set G) : Set G).Infinite) :
    StrictMono fun n ↦ #(X ^ n) := by
  obtain rfl | hX := eq_singleton_or_nontrivial hX₁
  · simp [closure_singleton_one] at hXclosure
  have h n : (X ^ (n - 1) : Set G) ≠ closure (X : Set G) :=
    fun h ↦ by simp [← h, ← coe_pow] at hXclosure
  simpa [h] using card_pow_strictMonoOn hX₁ hX

/-- The growth of a set generating an infinite group is at least linear. -/
@[to_additive "The growth of a set generating an infinite group is at least linear."]
lemma add_one_le_card_pow (hX₁ : 1 ∈ X) (hXclosure : (closure (X : Set G) : Set G).Infinite) :
    ∀ n, n + 1 ≤ #(X ^ n)
  | 0 => by simp
  | n + 1 => (add_one_le_card_pow hX₁ hXclosure _).trans_lt <|
      card_pow_strictMono hX₁ (by simp [hXclosure, Set.infinite_univ]) n.lt_succ_self

end Finset
