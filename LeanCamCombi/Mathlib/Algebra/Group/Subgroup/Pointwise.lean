import Mathlib.Algebra.Group.Subgroup.Pointwise

open Subgroup
open scoped Pointwise

namespace Set
variable {G : Type*} [Group G] {s : Set G}

@[to_additive (attr := simp)]
lemma mul_subgroupClosure (hs : s.Nonempty) : s * closure s = closure s := by
  rw [← smul_eq_mul, ← Set.iUnion_smul_set]
  have h a (ha : a ∈ s) : a • (closure s : Set G) = closure s :=
    smul_coe_set <| subset_closure ha
  simp (config := {contextual := true}) [h, hs]

@[to_additive (attr := simp)]
lemma mul_subgroupClosure_pow (hs : s.Nonempty) : ∀ n, s ^ n * closure s = closure s
  | 0 => by simp
  | n + 1 => by rw [pow_add, pow_one, mul_assoc, mul_subgroupClosure hs, mul_subgroupClosure_pow hs]

end Set

variable {G S : Type*} [Group G] [SetLike S G] [SubgroupClass S G] {s : Set G} {n : ℕ}

set_option linter.unusedVariables false in
@[to_additive (attr := simp)]
lemma coe_set_pow : ∀ {n} (hn : n ≠ 0) (H : S), (H ^ n : Set G) = H
  | 1, _, H => by simp
  | n + 2, _, H => by rw [pow_succ, coe_set_pow n.succ_ne_zero, coe_mul_coe]
