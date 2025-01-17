import Mathlib.Algebra.Order.SuccPred.WithBot
import Mathlib.Algebra.Polynomial.CoeffMem
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.RingTheory.Spectrum.Prime.Polynomial
import LeanCamCombi.Mathlib.Algebra.MvPolynomial.Basic
import LeanCamCombi.Mathlib.Algebra.MvPolynomial.Degrees
import LeanCamCombi.Mathlib.Algebra.MvPolynomial.Equiv
import LeanCamCombi.Mathlib.Data.Prod.Lex
import LeanCamCombi.Mathlib.Data.Set.Image
import LeanCamCombi.Mathlib.RingTheory.Spectrum.Prime.Topology
import LeanCamCombi.GrowthInGroups.ConstructibleSetData

variable {R S M A : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] [CommRing A]
  [Algebra R A]

open Function Localization Polynomial TensorProduct PrimeSpectrum
open scoped Pointwise

variable (R) in
@[ext]
structure InductionObj (n : ℕ) where val : Fin n → R[X]

variable {n : ℕ}

instance : CoeFun (InductionObj R n) (fun _ ↦ Fin n → R[X]) := ⟨InductionObj.val⟩

namespace InductionObj

attribute [-instance] AddCommGroup.toIntModule in
attribute [-instance] Ring.toIntAlgebra in
def coeffSubmodule [Algebra ℤ R] (e : InductionObj R n) : Submodule ℤ R :=
  .span ℤ ({1} ∪ ⋃ i, Set.range (e.val i).coeff)

lemma coeffSubmodule_mapRingHom_comp (e : InductionObj R n) (f : R →+* S) :
    ({ val := mapRingHom f ∘ e.val } : InductionObj S n).coeffSubmodule
      = e.coeffSubmodule.map f.toIntAlgHom.toLinearMap := by
  simp [coeffSubmodule, Submodule.map_span, Set.image_insert_eq, Set.image_iUnion, ← Set.range_comp,
    coeff_map_eq_comp]

variable {e T : InductionObj R n}

lemma coeff_mem_coeffSubmodule {i : Fin n} {d : ℕ} : (e.val i).coeff d ∈ e.coeffSubmodule :=
  Submodule.subset_span <| .inr <| Set.mem_iUnion.2 ⟨i, Set.mem_range_self _⟩

lemma one_mem_coeffSubmodule : 1 ∈ e.coeffSubmodule := Submodule.subset_span (.inl rfl)

lemma one_le_coeffSubmodule : 1 ≤ e.coeffSubmodule := by
  rw [Submodule.one_eq_span, Submodule.span_le, Set.singleton_subset_iff]
  exact one_mem_coeffSubmodule

variable (n) in
abbrev DegreeType := (Fin n → WithBot ℕ) ×ₗ Prop

variable (e) in
def degree : DegreeType n :=
  toLex (Polynomial.degree ∘ e.val, ¬ ∃ i, (e.val i).Monic ∧
    ∀ j, e.val j ≠ 0 → (e.val i).degree ≤ (e.val j).degree)

@[simp] lemma ofLex_degree_fst (i) : (ofLex e.degree).fst i = (e.val i).degree := rfl
lemma ofLex_degree_snd : (ofLex e.degree).snd = ¬ ∃ i, (e.val i).Monic ∧
    ∀ j, e.val j ≠ 0 → (e.val i).degree ≤ (e.val j).degree := rfl

variable (e) in
def degBound : ℕ := ∑ i, (e.val i).degree.succ

variable (e) in
def powBound : ℕ := e.degBound ^ e.degBound

lemma powBound_ne_zero : e.powBound ≠ 0 := by
  unfold powBound
  match h : e.degBound with
  | 0 => decide
  | n + 1 => exact (Nat.pow_pos n.succ_pos).ne'

attribute [-instance] Ring.toIntAlgebra in
variable (R n e) in
def InductionStatement [Algebra ℤ R] : Prop :=
  ∀ f, ∃ T : Finset (Σ n, R × (Fin n → R)),
    comap C '' (zeroLocus (Set.range e.val) \ zeroLocus {f}) =
      ⋃ C ∈ T, (zeroLocus (Set.range C.2.2) \ zeroLocus {C.2.1}) ∧
    ∀ C ∈ T, C.1 ≤ e.degBound ∧ ∀ i, C.2.2 i ∈ e.coeffSubmodule ^ e.powBound

local notation3 "coeff("p")" => Set.range (Polynomial.coeff p)

universe u

lemma foo_induction (n : ℕ)
    (P : ∀ (R : Type u) [CommRing R], (InductionObj R n) → Prop)
    (hP₀ : ∀ (R) [CommRing R] (e : InductionObj R n) (i : Fin n),
      (e.1 i).Monic → (∀ j ≠ i, e.1 j = 0) → P R e)
    (hP₁ : ∀ (R) [CommRing R], P R ⟨0⟩)
    (hP₃ : ∀ (R) [CommRing R] (e : InductionObj R n) (i j : Fin n),
      (e.1 i).Monic → (e.1 i).degree ≤ (e.1 j).degree → i ≠ j →
      P R ⟨Function.update e.1 j (e.1 j %ₘ e.1 i)⟩ → P R e)
    (hP : ∀ (R) [CommRing R] (c : R) (i : Fin n) (e : InductionObj R n), c = (e.1 i).leadingCoeff →
      c ≠ 0 →
      P (Away c) ⟨C (IsLocalization.Away.invSelf (S := Away c) c) •
        mapRingHom (algebraMap _ _) ∘ e.val⟩ →
      P (R ⧸ Ideal.span {c}) ⟨mapRingHom (algebraMap _ _) ∘ e.val⟩ → P R e)
    {R} [CommRing R] (e : InductionObj R n) : P R e := by
  classical
  set v := e.degree with hv
  clear_value v
  induction v using WellFoundedLT.induction generalizing R with
  | ind v H_IH =>
    by_cases he0 : e = ⟨0⟩
    · exact he0 ▸ hP₁ R
    cases subsingleton_or_nontrivial R
    · convert hP₁ R; ext; exact Subsingleton.elim _ _
    simp only [InductionObj.ext_iff, funext_iff, Pi.zero_apply, not_forall] at he0
    -- Case I : The `e i ≠ 0` with minimal degree has invertible leading coefficient
    by_cases H : (∃ i, (e.1 i).Monic ∧ ∀ j, e.1 j ≠ 0 → (e.1 i).degree ≤ (e.1 j).degree)
    · obtain ⟨i, hi, i_min⟩ := H
      -- Case I.ii : `e j = 0` for all `j ≠ i`.
      by_cases H' : ∀ j ≠ i, e.1 j = 0
      -- then `I = Ideal.span {e i}`
      · exact hP₀ R e i hi H'
      -- Case I.i : There is another `e j ≠ 0`
      · simp only [ne_eq, not_forall, Classical.not_imp] at H'
        obtain ⟨j, hj, hj'⟩ := H'
        replace i_min := i_min j hj'
        -- then we can replace `e j` with `e j %ₘ (C h.unit⁻¹ * e i) `
        -- with `h : IsUnit (e i).leadingCoeff`.
        apply hP₃ R e i j hi i_min (.symm hj) (H_IH _ ?_ _ rfl)
        refine .left _ _ (lt_of_le_of_ne (b := (ofLex v).1) ?_ ?_)
        · intro k
          simp only [Function.comp_apply, Function.update_apply, hv, ne_eq, not_exists, not_and,
            not_forall, Classical.not_imp, not_le, ofLex_toLex]
          split_ifs with hjk
          · rw [hjk]
            exact (degree_modByMonic_le _ hi).trans i_min
          · exact le_rfl
        · simp only [hv, ne_eq, not_exists, not_and, not_forall, not_le, funext_iff,
            Function.comp_apply, exists_prop, ofLex_toLex]
          use j
          simp only [Function.update_self]
          refine ((degree_modByMonic_lt _ hi).trans_le i_min).ne
    -- Case II : The `e i ≠ 0` with minimal degree has non-invertible leading coefficient
    obtain ⟨i, hi, i_min⟩ : ∃ i, e.1 i ≠ 0 ∧ ∀ j, e.1 j ≠ 0 → (e.1 i).degree ≤ (e.1 j).degree := by
      have : ∃ n : ℕ, ∃ i, (e.1 i).degree = n ∧ (e.1 i) ≠ 0 := by
        obtain ⟨i, hi⟩ := he0; exact ⟨(e.1 i).natDegree, i, degree_eq_natDegree hi, hi⟩
      let m := Nat.find this
      obtain ⟨i, hi, hi'⟩ : ∃ i, (e.1 i).degree = m ∧ (e.1 i) ≠ 0 := Nat.find_spec this
      refine ⟨i, hi', fun j hj ↦ ?_⟩
      refine hi.le.trans ?_
      rw [degree_eq_natDegree hj, Nat.cast_le]
      exact Nat.find_min' _ ⟨j, degree_eq_natDegree hj, hj⟩
    have : ¬ (e.1 i).Monic := fun HH ↦ H ⟨i, HH, i_min⟩
    -- We replace `R` by `R ⧸ Ideal.span {(e i).leadingCoeff}` where `(e i).degree` is lowered
    -- and `Away (e i).leadingCoeff` where `(e i).leadingCoeff` becomes invertible.
    apply hP _ _ i e rfl (by simpa using hi) (H_IH _ ?_ _ rfl) (H_IH _ ?_ _ rfl)
    · rw [hv, Prod.Lex.lt_iff'']
      constructor
      · intro j
        simp only [coe_mapRingHom, InductionObj.ofLex_degree_fst, Pi.smul_apply,
          Function.comp_apply, smul_eq_mul]
        refine ((degree_mul_le _ _).trans (add_le_add degree_C_le degree_map_le)).trans ?_
        simp
      rw [lt_iff_le_not_le]
      simp only [coe_mapRingHom, funext_iff, InductionObj.ofLex_degree_fst, Pi.smul_apply,
        Function.comp_apply, smul_eq_mul, show (ofLex e.degree).2 from H,
        le_Prop_eq, implies_true, true_implies, true_and]
      simp only [InductionObj.ofLex_degree_snd, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
        ne_eq, not_exists, not_and, not_forall, Classical.not_imp, not_le, not_lt]
      intro h_eq
      refine ⟨i, ?_, ?_⟩
      · rw [Monic.def, ← coeff_natDegree (p := _ * _), natDegree_eq_of_degree_eq (h_eq i),
          coeff_C_mul, coeff_map, coeff_natDegree, mul_comm, IsLocalization.Away.mul_invSelf]
      · intro j hj; rw [h_eq, h_eq]; exact i_min j fun H ↦ (by simp [H] at hj)
    · rw [hv]
      refine .left _ _ (lt_of_le_of_ne ?_ ?_)
      · intro j; simpa using degree_map_le
      simp only [coe_mapRingHom, Function.comp_apply, ne_eq, hv, ofLex_toLex,
        not_exists, not_and, not_forall, Classical.not_imp, not_le, H, not_false_eq_true]
      intro h_eq
      replace h_eq := congr_fun h_eq i
      simp only [Ideal.Quotient.algebraMap_eq, Function.comp_apply, degree_map_eq_iff,
        Ideal.Quotient.mk_singleton_self, ne_eq, not_true_eq_false, false_or] at h_eq
      exact hi h_eq

attribute [-instance] AddCommGroup.toIntModule

set_option maxHeartbeats 300000 in
open IsLocalization in
open Submodule hiding comap in
lemma induction_aux (R) [CommRing R] (c : R) (i : Fin n) (e : InductionObj R n)
      (hi : c = (e.1 i).leadingCoeff) (hc : c ≠ 0) :
      InductionStatement (Away c) n
        ⟨C (IsLocalization.Away.invSelf (S := Away c) c) •
          mapRingHom (algebraMap _ _) ∘ e.val⟩ →
      InductionStatement (R ⧸ Ideal.span {c}) n ⟨mapRingHom (algebraMap _ _) ∘ e.val⟩ →
        InductionStatement R n e := by
  set q₁ := IsScalarTower.toAlgHom ℤ R (Away c)
  set q₂ := Ideal.Quotient.mk (.span {c})
  have q₂_surjective : Surjective q₂ := Ideal.Quotient.mk_surjective
  set e₁ : InductionObj (Away c) n :=
    ⟨C (IsLocalization.Away.invSelf (S := Away c) c) • mapRingHom q₁ ∘ e.val⟩
  set e₂ : InductionObj (R ⧸ Ideal.span {c}) n := ⟨mapRingHom q₂ ∘ e.val⟩
  have degBound_e₁_le : e₁.degBound ≤ e.degBound := by
    unfold degBound
    gcongr with j
    exact (degree_mul_le _ _).trans <| (add_le_of_nonpos_left degree_C_le).trans degree_map_le
  have degBound_e₂_lt : e₂.degBound < e.degBound := by
    unfold degBound
    refine Fintype.sum_strictMono <| Pi.lt_def.2 ⟨fun j ↦ ?_, i, ?_⟩
    · dsimp
      gcongr
      exact degree_map_le
    · gcongr
      exact degree_map_lt (by simp [q₂, ← hi]) (by simpa [hi] using hc)
  intro (H₁ : InductionStatement _ _ e₁) (H₂ : InductionStatement _ _ e₂) f
  obtain ⟨T₁, hT₁⟩ := H₁ (mapRingHom q₁ f)
  obtain ⟨T₂, hT₂⟩ := H₂ (mapRingHom q₂ f)
  simp only [forall_and] at hT₁ hT₂
  obtain ⟨hT₁, hT₁deg, hT₁span⟩ := hT₁
  obtain ⟨hT₂, hT₂deg, hT₂span⟩ := hT₂
  -- Lift the tuples of `T₁` from `Away c` to `R`
  let _ : Invertible (q₁ c) :=
    -- TODO(Andrew): add API for `IsLocalization.Away.invSelf`
    ⟨IsLocalization.Away.invSelf c, by simp [q₁, IsLocalization.Away.invSelf], by
      simp [q₁, IsLocalization.Away.invSelf]⟩
  have he₁span :
      e₁.coeffSubmodule ^ e₁.powBound = ⅟(q₁ c ^ e₁.powBound) •
        (span ℤ ({c} ∪ ⋃ i, coeff(e.val i)) ^ e₁.powBound).map q₁.toLinearMap := by
    unfold coeffSubmodule
    rw [Submodule.map_pow, map_span, invOf_pow, ← smul_pow, ← span_smul]
    simp [Set.image_insert_eq, Set.smul_set_insert, Set.image_iUnion, Set.smul_set_iUnion, q₁, e₁]
    congr! with i
    change _ = IsLocalization.Away.invSelf c • _
    simp [← Set.range_comp, Set.smul_set_range, funext fun _ ↦ coeff_C_mul _]
    ext
    simp [q₁]
  replace hT₁span x hx i :=
    smul_mem_pointwise_smul _ (q₁ c ^ e₁.powBound) _ (hT₁span x hx i)
  simp only [he₁span, smul_invOf_smul, smul_eq_mul] at hT₁span
  choose! g₁ hg₁ hq₁g₁ using hT₁span
  -- Lift the constants of `T₁` from `Away c` to `R`
  choose! n₁ f₁ hf₁ using Away.surj (S := Away c) c
  change (∀ _, _ * q₁ _ ^ _ = q₁ _) at hf₁
  -- Lift the tuples of `T₂` from `R ⧸ Ideal.span {c}` to `R`
  let _ : Algebra ℤ R := Ring.toIntAlgebra _
  rw [coeffSubmodule_mapRingHom_comp, ← Submodule.map_pow] at hT₂span
  choose! g₂ hg₂ hq₂g₂ using hT₂span
  -- Lift the constants of `T₂` from `R ⧸ Ideal.span {c}` to `R`
  choose! f₂ hf₂ using Ideal.Quotient.mk_surjective (I := .span {c})
  change (∀ _, q₂ _ = _) at hf₂
  -- Lift everything together
  classical
  let S₁ : Finset (Σ n, R × (Fin n → R)) := T₁.image fun x ↦ ⟨_, (c * f₁ x.2.1, g₁ x)⟩
  let S₂ : Finset (Σ n, R × (Fin n → R)) := T₂.image fun x ↦ ⟨_, (f₂ x.2.1, Fin.cons c (g₂ x))⟩
  refine ⟨S₁ ∪ S₂, ?_, ?_⟩
  · calc
      comap C '' (zeroLocus (.range e.val) \ zeroLocus {f})
        = comap q₁ '' (comap C ''
            (comap (mapRingHom q₁.toRingHom) ⁻¹' (zeroLocus (.range e.val) \ zeroLocus {f}))) ∪
          comap q₂ '' (comap C ''
            (comap (mapRingHom q₂) ⁻¹' (zeroLocus (.range e.val) \ zeroLocus {f}))) :=
        Set.image_of_range_union_range_eq_univ (by ext; simp) (by ext; simp)
          (by rw [← range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk,
            RingHom.algebraMap_toAlgebra]; exact Set.union_compl_self _) _
      _ = (⋃ C ∈ S₁, zeroLocus (Set.range C.snd.2) \ zeroLocus {C.snd.1}) ∪
          ⋃ C ∈ S₂, zeroLocus (Set.range C.snd.2) \ zeroLocus {C.snd.1} := ?_
      _ = ⋃ C ∈ S₁ ∪ S₂, zeroLocus (Set.range C.snd.2) \ zeroLocus {C.snd.1} := by
        simpa using (Set.biUnion_union S₁.toSet S₂ _).symm
    congr 1
    · convert congr(comap q₁.toRingHom '' $hT₁)
      · dsimp only [e₁]
        rw [Set.preimage_diff, preimage_comap_zeroLocus, preimage_comap_zeroLocus,
          Set.image_singleton, Pi.smul_def, ← Set.smul_set_range, Set.range_comp]
        congr 1
        refine (PrimeSpectrum.zeroLocus_smul_of_isUnit (.map _ ?_) _).symm
        exact isUnit_iff_exists_inv'.mpr ⟨_, IsLocalization.Away.mul_invSelf c⟩
      · rw [Set.image_iUnion₂]
        simp_rw [← Finset.mem_coe, S₁, Finset.coe_image, Set.biUnion_image]
        congr! with x hxT₁
        apply Set.injOn_preimage subset_rfl (f := comap q₁.toRingHom)
        · erw [localization_away_comap_range (S := Localization.Away c) (r := c)]
          rw [sdiff_eq, ← basicOpen_eq_zeroLocus_compl, basicOpen_mul]
          exact Set.inter_subset_right.trans Set.inter_subset_left
        · exact Set.image_subset_range ..
        · rw [Set.preimage_diff, preimage_comap_zeroLocus, preimage_comap_zeroLocus,
            Set.preimage_image_eq]
          swap; · exact localization_specComap_injective _ (.powers c)
          simp only [AlgHom.toLinearMap_apply] at hq₁g₁
          simp only [← Set.range_comp, Function.comp_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            hq₁g₁ _ hxT₁, Set.image_singleton, map_mul, ← hf₁, mul_comm x.2.1, ← mul_assoc,
            ← pow_succ']
          simp only [← smul_eq_mul, ← Set.smul_set_range, ← Set.smul_set_singleton,
            zeroLocus_smul_of_isUnit ((isUnit_of_invertible (q₁ c)).pow _)]
    · convert congr(comap q₂ '' $hT₂)
      · rw [Set.preimage_diff, preimage_comap_zeroLocus, preimage_comap_zeroLocus,
          Set.image_singleton, Set.range_comp]
      · rw [Set.image_iUnion₂]
        simp_rw [← Finset.mem_coe, S₂, Finset.coe_image, Set.biUnion_image]
        congr! 3 with x hxT₂
        apply Set.injOn_preimage subset_rfl (f := comap q₂)
        · rw [range_comap_of_surjective _ _ q₂_surjective]
          simp only [Ideal.mk_ker, zeroLocus_span, q₂]
          exact Set.diff_subset.trans (zeroLocus_anti_mono (by simp))
        · exact Set.image_subset_range _ _
        · simp only [AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe] at hq₂g₂
          have : q₂ c = 0 := by simp [q₂]
          simp only [Set.preimage_diff, preimage_comap_zeroLocus, preimage_comap_zeroLocus,
            Set.preimage_image_eq _ (comap_injective_of_surjective _ q₂_surjective)]
          simp only [Fin.range_cons, Set.image_singleton, hf₂, Set.image_insert_eq,
            ← Set.range_comp, Function.comp_def, hq₂g₂ _ hxT₂]
          rw [← Set.union_singleton, zeroLocus_union, this,
            zeroLocus_singleton_zero, Set.inter_univ]
  · simp only [Finset.mem_union, forall_and, or_imp, Finset.forall_mem_image, S₁, S₂]
    refine ⟨⟨fun x hx ↦ (hT₁deg _ hx).trans degBound_e₁_le,
      fun x hx ↦ (hT₂deg _ hx).trans_lt degBound_e₂_lt⟩,
      fun x hx k ↦ SetLike.mem_of_subset ?_ (hg₁ _ hx _),
      fun x hx ↦ Fin.cons ?_ fun k ↦ SetLike.mem_of_subset ?_ (hg₂ _ hx _)⟩
    · norm_cast
      calc
        span ℤ ({c} ∪ ⋃ i, coeff(e.val i)) ^ e₁.powBound
        _ ≤ span ℤ (⋃ i, coeff(e.val i)) ^ e₁.powBound := by
          gcongr; simpa [Set.insert_subset_iff] using ⟨_, _, hi.symm⟩
        _ ≤ e.coeffSubmodule ^ e.powBound := by
          unfold coeffSubmodule powBound
          gcongr
          · exact one_le_coeffSubmodule
          · exact Set.subset_union_right
          · omega
    · exact le_self_pow one_le_coeffSubmodule powBound_ne_zero <| subset_span <| .inr <| by
        simpa using ⟨_, _, hi.symm⟩
    · unfold powBound
      gcongr
      · exact one_le_coeffSubmodule
      · omega

lemma isConstructible_comap_C_zeroLocus_sdiff_zeroLocus :
    ∀ S : InductionObj R n, InductionStatement R n S := by
  classical
  apply foo_induction
  · intros R _ g i hi hi_min f
    let M := R[X] ⧸ Ideal.span {g.1 i}
    have : Module.Free R M := .of_basis (AdjoinRoot.powerBasis' hi).basis
    have : Module.Finite R M := .of_basis (AdjoinRoot.powerBasis' hi).basis
    refine ⟨(Finset.range (Module.finrank R M)).image
      fun j ↦ ⟨0, (Algebra.lmul R M (Ideal.Quotient.mk _ f)).charpoly.coeff j, 0⟩, ?_, ?_⟩
    · ext x
      have : zeroLocus (Set.range g.val) = zeroLocus {g.1 i} := by
        rw [Set.range_eq_iUnion, zeroLocus_iUnion]
        refine (Set.iInter_subset _ _).antisymm (Set.subset_iInter fun j ↦ ?_)
        by_cases hij : i = j
        · subst hij; rfl
        · rw [hi_min j (.symm hij), zeroLocus_singleton_zero]; exact Set.subset_univ _
      rw [this, ← Polynomial.algebraMap_eq, mem_image_comap_zeroLocus_sdiff,
        IsScalarTower.algebraMap_apply R[X] M, isNilpotent_tensor_residueField_iff]
      simp [Set.subset_def, M]
    · simp
  · intro R _ f
    refine ⟨(Finset.range (f.natDegree + 2)).image fun j ↦ ⟨0, f.coeff j, 0⟩, ?_, ?_⟩
    · convert image_comap_C_basicOpen f
      · simp only [basicOpen_eq_zeroLocus_compl, Set.compl_eq_univ_diff]
        congr 1
        rw [← Set.univ_subset_iff]
        rintro x _ _ ⟨_, rfl⟩
        exact zero_mem x.asIdeal
      · suffices Set.range f.coeff = ⋃ i < f.natDegree + 2, {f.coeff i} by
          simp [← Set.compl_eq_univ_diff, eq_compl_comm (y := zeroLocus _),
            ← zeroLocus_iUnion₂, this]
        trans f.coeff '' (Set.Iio (f.natDegree + 2))
        · refine ((Set.image_subset_range _ _).antisymm ?_).symm
          rintro _ ⟨i, rfl⟩
          by_cases hi : i ≤ f.natDegree
          · exact ⟨i, hi.trans_lt (by simp), rfl⟩
          · exact ⟨f.natDegree + 1, by simp,
              by simp [f.coeff_eq_zero_of_natDegree_lt (lt_of_not_le hi)]⟩
        · ext; simp [eq_comm]
    · simp
  · intro R _ c i j hi hle hne H f
    cases subsingleton_or_nontrivial R
    · use ∅
      simp [Subsingleton.elim f 0]
    obtain ⟨S, hS, hS'⟩ := H f
    refine ⟨S, Eq.trans ?_ hS, ?_⟩
    · rw [← zeroLocus_span (Set.range _), ← zeroLocus_span (Set.range _),
        idealSpan_range_update_divByMonic hne _ hi]
    · intro C hC
      let c' : InductionObj _ _ := ⟨Function.update c.val j (c.val j %ₘ c.val i)⟩
      have deg_bound₁ : c'.degBound ≤ c.degBound := by
        dsimp [InductionObj.degBound, c']
        gcongr with k
        · rw [Function.update_apply]
          split_ifs with hkj
          · subst hkj; exact (degree_modByMonic_le _ hi).trans hle
          · rfl
      refine ⟨(hS' C hC).1.trans deg_bound₁, fun k ↦ SetLike.le_def.mp ?_ ((hS' C hC).2 k)⟩
      show c'.coeffSubmodule ^ c'.powBound ≤ _
      delta powBound
      suffices hij : c'.coeffSubmodule ≤ c.coeffSubmodule ^ (c.val j).degree.succ by
        by_cases hi' : c.val i = 1
        · gcongr
          · exact c.one_le_coeffSubmodule
          · refine Submodule.span_le.mpr (Set.union_subset ?_ ?_)
            · exact Set.subset_union_left.trans Submodule.subset_span
            · refine Set.iUnion_subset fun k ↦ ?_
              simp only [Function.update_apply, hi', modByMonic_one, c']
              split_ifs
              · rintro _ ⟨_, rfl⟩
                exact zero_mem _
              · exact (Set.subset_iUnion (fun i ↦ coeff(c.val i)) k).trans
                  (Set.subset_union_right.trans Submodule.subset_span)
          rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, InductionObj.degBound]
          refine Fintype.sum_pos (Pi.lt_def.mpr ⟨by positivity, i, by simp [hi']⟩)
        refine (pow_le_pow_left' hij _).trans ?_
        rw [← pow_mul]
        apply pow_le_pow_right' c.one_le_coeffSubmodule
        have deg_bound₂ : c'.degBound < c.degBound := by
          dsimp [InductionObj.degBound, c']
          apply Finset.sum_lt_sum ?_ ⟨j, Finset.mem_univ _, ?_⟩
          · intro k _
            rw [Function.update_apply]
            split_ifs with hkj
            · subst hkj; gcongr; exact (degree_modByMonic_le _ hi).trans hle
            · rfl
          · gcongr; simpa using (degree_modByMonic_lt _ hi).trans_le hle
        calc  (c.val j).degree.succ * c'.degBound ^ c'.degBound
          _ ≤ c.degBound * c.degBound ^ c'.degBound := by
            gcongr
            delta InductionObj.degBound
            exact Finset.single_le_sum (f := fun i ↦ (c.val i).degree.succ)
              (by intros; positivity) (Finset.mem_univ _)
          _ = c.degBound ^ (c'.degBound + 1) := by rw [pow_succ']
          _ ≤ c.degBound ^ c.degBound := by gcongr <;> omega
      rw [coeffSubmodule]
      simp only [Submodule.span_le, Set.union_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        Set.iUnion_subset_iff, Set.range_subset_iff, c']
      constructor
      · apply one_le_pow_of_one_le' c.one_le_coeffSubmodule
        rw [Submodule.one_eq_span]
        exact Submodule.subset_span rfl
      · intro l m
        rw [Function.update_apply]
        split_ifs with hlj
        · convert coeff_modByMonic_mem_pow_natDegree_mul _ _ _ (fun _ ↦ coeff_mem_coeffSubmodule)
            one_mem_coeffSubmodule _ (fun _ ↦ coeff_mem_coeffSubmodule) one_mem_coeffSubmodule _
          rw [← pow_succ, Polynomial.degree_eq_natDegree, WithBot.succ_natCast, Nat.cast_id]
          intro e
          simp [show c.val i = 0 by simpa [e] using hle] at hi
        · have : (c.val j).degree.succ ≠ 0 := by
            rw [← Nat.pos_iff_ne_zero]
            apply WithBot.succ_lt_succ (x := ⊥)
            refine lt_of_lt_of_le ?_ hle
            rw [bot_lt_iff_ne_bot, ne_eq, degree_eq_bot]
            intro e
            simp [e] at hi
          refine le_self_pow c.one_le_coeffSubmodule this ?_
          exact Submodule.subset_span (.inr (Set.mem_iUnion_of_mem l ⟨m, rfl⟩))
  · convert induction_aux (n := n) -- Andrew: this is absolutely fine if you ignore it
    ext
    exact (OreLocalization.zsmul_eq_zsmul _ _).symm

lemma exists_constructibleSetData_comap_C_toSet_eq_toSet {R} [CommRing R]
    (M : Submodule ℤ R) (hM : 1 ∈ M)
    (S : ConstructibleSetData R[X]) (hS : ∀ x ∈ S, ∀ j k, (x.2.2 j).coeff k ∈ M) :
    ∃ T : ConstructibleSetData R,
      comap C '' S.toSet = T.toSet ∧ ∀ C ∈ T, C.1 ≤ S.degBound ∧
      ∀ i, C.2.2 i ∈ M ^ S.degBound ^ S.degBound := by
  classical
  choose f hf₁ hf₂ hf₃ using fun x : Σ n, R[X] × (Fin n → R[X]) ↦
    isConstructible_comap_C_zeroLocus_sdiff_zeroLocus ⟨x.2.2⟩ x.2.1
  refine ⟨S.biUnion f, ?_, ?_⟩
  · simp only [ConstructibleSetData.toSet, Set.image_iUnion, Finset.set_biUnion_biUnion, hf₁]
  · simp only [Finset.mem_biUnion, Prod.exists, forall_exists_index, and_imp]
    intros x y hy hx
    have H : degBound ⟨y.snd.2⟩ ≤ S.degBound :=
      Finset.le_sup (f := fun e ↦ ∑ i, (e.2.2 i).degree.succ) hy
    refine ⟨(hf₂ y x hx).trans H, fun i ↦ SetLike.le_def.mp ?_ (hf₃ y x hx i)⟩
    gcongr
    · simpa [Submodule.one_eq_span]
    · refine Submodule.span_le.mpr ?_
      simp [Set.subset_def, hM, forall_comm (α := R), hS y hy]
    · delta powBound
      by_cases h : S.degBound = 0
      · have : degBound ⟨y.snd.2⟩ = 0 := by nlinarith
        rw [h, this]
      gcongr
      rwa [Nat.one_le_iff_ne_zero]

section

mutual

def δ (k : ℕ) (D : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => ν k D (n + 1) ^ ν k D (n + 1) * δ k D n

def ν (k : ℕ) (D : ℕ → ℕ) : ℕ → ℕ
  | 0 => k
  | n + 1 => ν k D n * δ k D n * D n

end

@[simp]
lemma δ_zero (k : ℕ) (D : ℕ → ℕ) : δ k D 0 = 1 := by delta δ; rfl

@[simp]
lemma δ_succ (k : ℕ) (D : ℕ → ℕ) (n) :
    δ k D (n + 1) = ν k D (n + 1) ^ ν k D (n + 1) * δ k D n := by
  delta δ ν; rfl

@[simp]
lemma ν_zero (k : ℕ) (D : ℕ → ℕ) : ν k D 0 = k := by delta ν; rfl

@[simp]
lemma ν_succ (k : ℕ) (D : ℕ → ℕ) (n) :
    ν k D (n + 1) = ν k D n * δ k D n * D n := by
  delta δ ν; rfl

section

mutual

lemma δ_casesOn_succ (k₀ k : ℕ) (D : ℕ → ℕ) :
    ∀ n, δ k₀ (fun t ↦ Nat.casesOn t k D) (n + 1) =
      (k₀ * k) ^ (k₀ * k) * δ (k₀ * k) ((k₀ * k) ^ (k₀ * k) • D) n
  | 0 => by simp
  | (n + 1) => by
    rw [δ_succ, ν_casesOn_succ, δ_casesOn_succ, ν_succ, δ_succ, ν_succ]
    ring

lemma ν_casesOn_succ (k₀ k : ℕ) (D : ℕ → ℕ) :
    ∀ n, ν k₀ (fun t ↦ Nat.casesOn t k D) (n + 1) = ν (k₀ * k) ((k₀ * k) ^ (k₀ * k) • D) n
  | 0 => by simp [mul_comm k]
  | (n + 1) => by
    rw [ν_succ (n := n + 1), ν_casesOn_succ k₀ k D n, ν_succ, δ_casesOn_succ]
    dsimp
    ring

end

section

variable {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) {D₁ D₂ : ℕ → ℕ}

mutual

lemma δ_le_δ (hk : k₁ ≤ k₂) : ∀ (n) (_ : ∀ i < n, D₁ i ≤ D₂ i), δ k₁ D₁ n ≤ δ k₂ D₂ n
  | 0, hD => by simp
  | n + 1, hD => by
    rw [δ_succ, δ_succ]
    refine Nat.mul_le_mul (Nat.pow_self_mono (ν_le_ν hk _ hD)) (δ_le_δ hk _
      fun i hi ↦ hD _ (hi.trans n.lt_succ_self))


lemma ν_le_ν (hk : k₁ ≤ k₂) : ∀ (n) (_ : ∀ i < n, D₁ i ≤ D₂ i), ν k₁ D₁ n ≤ ν k₂ D₂ n
  | 0, hD => by simpa using hk
  | n + 1, hD => by
    rw [ν_succ, ν_succ]
    gcongr
    · exact ν_le_ν hk _ fun i hi ↦ hD _ (hi.trans n.lt_succ_self)
    · exact δ_le_δ hk _ fun i hi ↦ hD _ (hi.trans n.lt_succ_self)
    · exact hD _ n.lt_succ_self

end

lemma δ_pos (k : ℕ) (D : ℕ → ℕ) : ∀ n, 0 < δ k D n
  | 0 => by simp
  | n + 1 => by simp [δ_succ, Nat.pow_self_pos, δ_pos]

lemma exists_constructibleSetData_comap_C_toSet_eq_toSet'
    {M : Submodule ℤ R} (hM : 1 ∈ M) (k : ℕ) (d : Multiset (Fin n))
    (S : ConstructibleSetData (MvPolynomial (Fin n) R))
    (hSn : ∀ x ∈ S, x.1 ≤ k)
    (hS : ∀ x ∈ S, ∀ j, x.2.2 j ∈ M.mvPolynomial _ ⊓
      (MvPolynomial.degreesLE _ _ d).restrictScalars _) :
    ∃ T : ConstructibleSetData R,
      comap MvPolynomial.C '' S.toSet = T.toSet ∧ ∀ C ∈ T,
        C.1 ≤ ν k (fun i ↦ 1 + (d.map Fin.val).count i) n ∧
      ∀ i, C.2.2 i ∈ M ^ (δ k (fun i ↦ 1 + (d.map Fin.val).count i) n) := by
  classical
  induction' n with n IH generalizing k M
  · refine ⟨(S.map (MvPolynomial.isEmptyRingEquiv _ _).toRingHom), ?_, ?_⟩
    · rw [ConstructibleSetData.toSet_map]
      show _ = (comapEquiv (MvPolynomial.isEmptyRingEquiv _ _)).symm ⁻¹' _
      rw [← Equiv.image_eq_preimage]
      rfl
    · simp only [Sigma.map, ne_eq, RingEquiv.toRingHom_eq_coe, Finset.mem_image,
        Prod.exists, forall_exists_index, and_imp, ConstructibleSetData.map, id_eq,
        RingHom.coe_coe, δ_zero, ν_zero, one_mul, pow_one,
        MvPolynomial.isEmptyRingEquiv_eq_coeff_zero,
        forall_apply_eq_imp_iff₂, comp_apply]
      exact fun a haS ↦ ⟨hSn a haS, fun i ↦ (hS a haS i).1 0⟩
  let e : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] (MvPolynomial (Fin n) R)[X] :=
    MvPolynomial.finSuccEquiv R n
  let S' := S.map e.toRingHom
  let hS' : S'.degBound ≤ k * (1 + d.count 0) := by
    apply Finset.sup_le fun x hxS ↦ ?_
    simp only [ConstructibleSetData.map, id_eq, AlgEquiv.toRingEquiv_eq_coe,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe,
      Finset.mem_image, Sigma.map, Sigma.exists, Prod.exists, S'] at hxS
    obtain ⟨i, f, g, hxS, rfl⟩ := hxS
    trans ∑ i : Fin i, (1 + d.count 0)
    · gcongr with j hj
      simp only [e, Function.comp_apply]
      by_cases hgj : g j = 0
      · rw [hgj, map_zero]
        simp
      rw [MvPolynomial.degree_finSuccEquiv hgj, WithBot.succ_natCast, add_comm]
      simp only [Nat.cast_id, add_le_add_iff_left, MvPolynomial.degreeOf_def]
      exact Multiset.count_le_of_le _ (hS _ hxS _).2
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      gcongr
      exact hSn _ hxS
  let B : Multiset (Fin n) :=
    (d.toFinsupp.comapDomain Fin.succ (Fin.succ_injective _).injOn).toMultiset
  obtain ⟨T, hT₁, hT₂⟩ := exists_constructibleSetData_comap_C_toSet_eq_toSet
      (R := MvPolynomial (Fin n) R)
      (M.mvPolynomial _ ⊓ (MvPolynomial.degreesLE _ _ B).restrictScalars ℤ)
      (by simpa [MvPolynomial.coeff_one, apply_ite] using hM)
      S' (fun x hxS j k ↦ by
        simp only [ConstructibleSetData.map, id_eq, AlgEquiv.toRingEquiv_eq_coe,
          RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe,
          Finset.mem_image, Sigma.map, Sigma.exists, Prod.exists, S'] at hxS
        obtain ⟨i, f, g, hxS, rfl⟩ := hxS
        simp only [comp_apply, Submodule.mem_inf, Submodule.mem_mvPolynomial,
          Submodule.restrictScalars_mem, MvPolynomial.mem_degreesLE]
        constructor
        · intro d
          simp only [MvPolynomial.finSuccEquiv_coeff_coeff, e]
          exact (hS _ hxS _).1 _
        · simp only [MvPolynomial.totalDegree, Finset.sup_le_iff,
            MvPolynomial.mem_support_iff, B,
            MvPolynomial.finSuccEquiv_coeff_coeff, ne_eq, e]
          replace hS := (hS _ hxS j).2
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe, MvPolynomial.mem_degreesLE,
            Multiset.le_iff_count, Finsupp.count_toMultiset, Finsupp.comapDomain_apply,
            Multiset.toFinsupp_apply, ← MvPolynomial.degreeOf_def] at hS ⊢
          intro a
          exact (MvPolynomial.degreeOf_coeff_finSuccEquiv (g j) a k).trans (hS _))
  have (C hCT k) := SetLike.le_def.mp pow_inf_le ((hT₂ C hCT).2 k)
  replace this (C hCT k) := SetLike.le_def.mp (inf_le_inf_right _ Submodule.mvPolynomial_pow_le)
    (this C hCT k)
  let N := (k * (1 + d.count 0)) ^ (k * (1 + d.count 0))
  have (C) (hCT : C ∈ T) (a) : C.snd.2 a ∈ (M ^ N).mvPolynomial (Fin n) ⊓
        (MvPolynomial.degreesLE R (Fin n) (N • B)).restrictScalars ℤ := by
    refine SetLike.le_def.mp ?_ ((hT₂ C hCT).2 a)
    refine pow_inf_le.trans (inf_le_inf ?_ ?_)
    · refine (pow_le_pow_right' ?_ (Nat.pow_self_mono hS')).trans Submodule.mvPolynomial_pow_le
      simpa [MvPolynomial.coeff_one, apply_ite] using hM
    · rw [← MvPolynomial.degreesLE_pow, Submodule.restrictScalars_pow Nat.pow_self_pos.ne']
      refine pow_le_pow_right' ?_ (Nat.pow_self_mono hS')
      simp
  have h1M : 1 ≤ M := Submodule.one_le.mpr hM
  obtain ⟨U, hU₁, hU₂⟩ := IH (M := M ^ N)
    (SetLike.le_def.mp (le_self_pow h1M Nat.pow_self_pos.ne') hM) _ _ T
    (fun C hCT ↦ (hT₂ C hCT).1)
    (fun C hCT k ↦ this C hCT k)
  simp only [Multiset.map_nsmul, smul_comm _ (_ ^ _), Multiset.count_nsmul, ← pow_mul, N] at hU₂
  have : ∀ i < n + 1, i.casesOn (1 + d.count 0) (1 + (B.map Fin.val).count ·) ≤
      1 + (d.map Fin.val).count i := by
    intro t ht
    show _ ≤ 1 + (d.map Fin.val).count (Fin.mk t ht).val
    rw [Multiset.count_map_eq_count' _ _ Fin.val_injective]
    cases' t with t
    · exact le_rfl
    · simp only [add_lt_add_iff_right] at ht
      show 1 + (B.map Fin.val).count (Fin.mk t ht).val ≤ _
      rw [Multiset.count_map_eq_count' _ _ Fin.val_injective]
      simp [B]
  refine ⟨U, ?_, fun C hCU ↦ ⟨(hU₂ C hCU).1.trans ?_,
    fun i ↦ pow_le_pow_right' h1M ?_ <| (hU₂ C hCU).2 i⟩⟩
  · unfold S' at hT₁
    rw [← hU₁, ← hT₁, ← Set.image_comp, ← ContinuousMap.coe_comp, ← comap_comp,
      ConstructibleSetData.toSet_map]
    show _ = _ '' ((comapEquiv e.toRingEquiv).symm ⁻¹' _)
    rw [← Equiv.image_eq_preimage, Set.image_image]
    simp only [comapEquiv_apply, ← comap_apply, ← comap_comp_apply]
    congr!
    exact e.symm.toAlgHom.comp_algebraMap.symm
  · refine (ν_le_ν hS' _ fun _ _ ↦ ?_).trans
      ((ν_casesOn_succ k _ _ _).symm.trans_le (ν_le_ν le_rfl _ this))
    simp +contextual [mul_add, Nat.one_le_iff_ne_zero]
  · refine (Nat.mul_le_mul le_rfl (δ_le_δ hS' _ fun _ _ ↦ ?_)).trans
      ((δ_casesOn_succ k _ _ _).symm.trans_le (δ_le_δ le_rfl _ this))
    simp +contextual [mul_add, Nat.one_le_iff_ne_zero]

lemma chevalley_mvPolynomial_mvPolynomial
    {n m : ℕ} (f : MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin n) R)
    (k : ℕ) (d : Multiset (Fin n))
    (S : ConstructibleSetData (MvPolynomial (Fin n) R))
    (hSn : ∀ x ∈ S, x.1 ≤ k)
    (hS : ∀ x ∈ S, ∀ j, (x.2.2 j).degrees ≤ d)
    (hf : ∀ i, (f (.X i)).degrees ≤ d) :
    ∃ T : ConstructibleSetData (MvPolynomial (Fin m) R),
      comap f '' S.toSet = T.toSet ∧
      ∀ C ∈ T, C.1 ≤ ν (k + m) (fun i ↦ 1 + Multiset.count i (Multiset.map Fin.val d)) n ∧
        ∀ i j, MvPolynomial.degreeOf j (C.2.2 i) ≤
          δ (k + m) (fun i ↦ 1 + (d.map Fin.val).count i) n := by
  classical
  let g : MvPolynomial (Fin n) (MvPolynomial (Fin m) R) →+* MvPolynomial (Fin n) R :=
    MvPolynomial.eval₂Hom f.toRingHom MvPolynomial.X
  have hg : g.comp (algebraMap (MvPolynomial (Fin m) R) _) = f := by
    ext x : 2 <;> simp [g]
  let σ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) (MvPolynomial (Fin m) R) :=
    MvPolynomial.map (algebraMap _ _)
  have hσ : g.comp σ = .id _ := by ext : 2 <;> simp [g, σ]
  have hσ' (x) : g (σ x) = x := DFunLike.congr_fun hσ x
  have hg' : Function.Surjective g := LeftInverse.surjective hσ'
  let S' : ConstructibleSetData (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)) := S.image
    fun ⟨k, fk, gk⟩ ↦ ⟨k + m, σ fk, fun s ↦ (finSumFinEquiv.symm s).elim (σ ∘ gk)
      fun i ↦ .C (.X i) - σ (f (.X i))⟩
  let s₀ : Set (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)) :=
    Set.range fun i ↦ .C (.X i) - σ (f (.X i))
  have hs : zeroLocus s₀ = Set.range (comap g) := by
    rw [range_comap_of_surjective _ _ hg', ← zeroLocus_span]
    congr! 2
    have H : Ideal.span s₀ ≤ RingHom.ker g := by
      simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub,
        hσ', s₀]
      simp [g]
    refine H.antisymm fun p hp ↦ ?_
    obtain ⟨q₁, q₂, hq₁, rfl⟩ : ∃ q₁ q₂, q₁ ∈ Ideal.span s₀ ∧ p = q₁ + σ q₂ := by
      clear hp
      obtain ⟨p, rfl⟩ := (MvPolynomial.commAlgEquiv _ _ _).surjective p
      simp_rw [← (MvPolynomial.commAlgEquiv R (Fin m) (Fin n)).symm.injective.eq_iff,
        AlgEquiv.symm_apply_apply]
      induction p using MvPolynomial.induction_on with
      | h_C q =>
        exact ⟨0, q, by simp, (MvPolynomial.commAlgEquiv _ _ _).injective <|
          by simp [MvPolynomial.commAlgEquiv_C, σ]⟩
      | h_add p q hp hq =>
        obtain ⟨q₁, q₂, hq₁, rfl⟩ := hp
        obtain ⟨q₃, q₄, hq₃, rfl⟩ := hq
        refine ⟨q₁ + q₃, q₂ + q₄, add_mem hq₁ hq₃, by simp only [map_add, add_add_add_comm]⟩
      | h_X p i hp =>
        obtain ⟨q₁, q₂, hq₁, rfl⟩ := hp
        simp only [← (MvPolynomial.commAlgEquiv R (Fin m) (Fin n)).injective.eq_iff,
          map_mul, AlgEquiv.apply_symm_apply, MvPolynomial.commAlgEquiv_X]
        refine ⟨q₁ * .C (.X i) + σ q₂ * (.C (.X i) - σ (f (.X i))), q₂ * f (.X i), ?_, ?_⟩
        · exact add_mem (Ideal.mul_mem_right _ _ hq₁)
            (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self _)))
        · simp; ring
    obtain rfl : q₂ = 0 := by simpa [hσ', show g q₁ = 0 from H hq₁] using hp
    simpa using hq₁
  have hg'' (t) : comap g '' t = comap σ ⁻¹' t ∩ zeroLocus s₀ := by
    refine Set.injOn_preimage (f := comap g) subset_rfl ?_ ?_ ?_
    · simp
    · simp [hs]
    · rw [Set.preimage_image_eq _ (comap_injective_of_surjective g hg'),
        Set.preimage_inter, hs, Set.preimage_range, Set.inter_univ,
        ← Set.preimage_comp, ← ContinuousMap.coe_comp, ← comap_comp, hσ]
      simp only [comap_id, ContinuousMap.coe_id, Set.preimage_id_eq, id_eq]
  have hS' : comap g '' S.toSet = S'.toSet := by
    simp only [S', ConstructibleSetData.toSet, Set.image_iUnion₂, Finset.set_biUnion_finset_image,
      ← Function.comp_def (g := finSumFinEquiv.symm), Set.range_comp,
      Equiv.range_eq_univ, Set.image_univ, Set.Sum.elim_range,
      Set.image_diff (hf := comap_injective_of_surjective g hg'), zeroLocus_union]
    simp [hg'', ← Set.inter_diff_distrib_right, Set.sdiff_inter_right_comm, s₀]
  obtain ⟨T, hT, hT'⟩ :=
    exists_constructibleSetData_comap_C_toSet_eq_toSet'
    (M := (MvPolynomial.degreesLE R (Fin m) Finset.univ.1).restrictScalars ℤ) (by simp) (k + m) d S'
    (Finset.forall_mem_image.mpr fun x hx ↦ (by simpa using hSn _ hx))
    (Finset.forall_mem_image.mpr fun x hx ↦ by
      intro j
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
      simp only [Equiv.symm_apply_apply, Submodule.mem_inf, Submodule.mem_mvPolynomial,
        implies_true, Submodule.restrictScalars_mem, MvPolynomial.mem_degreesLE,
        true_and]
      constructor
      · intro i
        cases' j with j j
        · simp [σ, MvPolynomial.coeff_map, MvPolynomial.degrees_C]
        · simp only [MvPolynomial.algebraMap_eq, Sum.elim_inr, MvPolynomial.coeff_sub,
            MvPolynomial.coeff_C, MvPolynomial.coeff_map, σ]
          refine (MvPolynomial.degrees_sub _ _).trans ?_
          simp only [MvPolynomial.degrees_C, apply_ite, MvPolynomial.degrees_zero]
          simp only [zero_le, sup_of_le_left]
          split_ifs with h
          · refine (MvPolynomial.degrees_X' _).trans ?_
            simp
          · simp
      · cases' j with j j
        · simp only [MvPolynomial.algebraMap_eq, Sum.elim_inl, comp_apply, σ]
          exact (MvPolynomial.degrees_map_le _ _).trans (hS _ hx j)
        · refine (MvPolynomial.degrees_sub _ _).trans ?_
          simp only [MvPolynomial.degrees_C, zero_le, sup_of_le_right]
          exact (MvPolynomial.degrees_map_le _ _).trans (hf _))
  refine ⟨T, ?_, fun C hCT ↦ ⟨(hT' C hCT).1, fun i j ↦ ?_⟩⟩
  · rwa [← hg, comap_comp, ContinuousMap.coe_comp, Set.image_comp, hS']
  · have := (hT' C hCT).2 i
    rw [← Submodule.restrictScalars_pow (δ_pos ..).ne', MvPolynomial.degreesLE_pow,
      Submodule.restrictScalars_mem, MvPolynomial.mem_degreesLE,
        Multiset.le_iff_count] at this
    simpa only [Multiset.count_nsmul, Multiset.count_univ, mul_one, ← MvPolynomial.degreeOf_def]
      using this j
