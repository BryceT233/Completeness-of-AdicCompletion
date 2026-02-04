/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.FreeProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Completeness of the Adic Completion for Finitely Generated Ideals

This file establishes that `AdicCompletion I M` is itself `I`-adically complete
when the ideal `I` is finitely generated.

## Main definitions

* `Submodule.powSmulQuotInclusion`: The canonical inclusion from
  `(I ^ m • M) / I ^ (n - m) • (I ^ m • M)` to `M / I ^ n • M`.

* `AdicCompletion.powSmulTopInclusion`: The canonical inclusion between the adic completions
  induced by the inclusion from `I ^ n • M` to `M`.

* `AdicCompletion.liftOfValZero`: Given `x` in `AdicCompletion I M` projecting to zero
  in `M / I ^ n • M`, `liftOfValZero` constructs the corresponding element in
  the adic completion of `I ^ m • M`.

## Main results

* `AdicCompletion.powSmulTopInclusion_range_eq_eval_ker`: The image of the adic completion
  of `I ^ m • M` inside `AdicCompletion I M` is exactly the kernel of the evaluation map
  `eval I M n`.

* `AdicCompletion.pow_smul_top_eq_eval_ker`: `I ^ n • AdicCompletion I M` is exact the kernel
  of the evaluation map `eval I M n` when `I` is finitely generated.

* `AdicCompletion.instIsAdicComplete`: The main instance showing that if `I` is finitely
  generated, then `AdicCompletion I M` is `I`-adically complete.

-/

public section

noncomputable section

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]

namespace Submodule

variable (M) in
/-- The canonical inclusion from `I ^ m • M ⧸ I ^ (n - m) • (I ^ m • M)` to `M ⧸ I ^ n • M`. -/
def powSmulQuotInclusion {m n : ℕ} (h : m ≤ n) := liftQ (I ^ (n - m) •
  ⊤ : Submodule R ↥(I ^ m • (⊤ : Submodule R M))) ((mkQ (I ^ n • ⊤)).comp <| topEquiv.comp <|
    inclusion (le_top (a := I ^ m • (⊤ : Submodule R M)))) (by
      suffices ∀ r ∈ I ^ (n - m), ∀ t ∈ I ^ m • ⊤, r • t ∈ I ^ n • ⊤ by
        simpa [smul_le, ← Quotient.mk_smul]
      intro r r_in t t_in
      rw [show n = n - m + m by lia, pow_add, ← smul_smul]
      exact smul_mem_smul r_in t_in)

theorem powSmulQuotInclusion_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective (powSmulQuotInclusion I M h) := by
  rw [powSmulQuotInclusion, ← LinearMap.ker_eq_bot, ker_liftQ, eq_bot_iff, SetLike.le_def]
  simp only [mem_map, LinearMap.mem_ker, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, topEquiv_apply, coe_inclusion, mkQ_apply, Quotient.mk_eq_zero,
    Subtype.exists, exists_and_left, mem_bot, forall_exists_index, and_imp]
  intro _ _ _ _ h'
  rwa [← h', Quotient.mk_eq_zero, mem_smul_top_iff, smul_smul, ← pow_add, Nat.sub_add_cancel h]

theorem factorPow_powSmulQuotInclusion_comm {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    (factorPow I M hnp) ∘ₗ (powSmulQuotInclusion I M (hmn.trans hnp)) =
      (powSmulQuotInclusion I M hmn) ∘ₗ (factorPow I ↥(I ^ m • ⊤ : Submodule R M)
        (Nat.sub_le_sub_right hnp m)) := by
  ext; rfl

theorem factorPow_powSmulQuotInclusion_comm_apply {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) {x} :
    (factorPow I M hnp) ((powSmulQuotInclusion I M (hmn.trans hnp)) x) =
      (powSmulQuotInclusion I M hmn) ((factorPow I ↥(I ^ m • ⊤ : Submodule R M)
        (Nat.sub_le_sub_right hnp m) x)) := by
  simpa using LinearMap.ext_iff.mp (factorPow_powSmulQuotInclusion_comm ..) x

theorem factorPow_comp_powSmulQuotInclusion_eq_zero {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    (factorPow I M (hmn.trans hnp)) ∘ₗ (powSmulQuotInclusion I M hnp) = 0 := by
  ext ⟨t, _⟩; revert t
  simpa [powSmulQuotInclusion, ← SetLike.le_def] using pow_smul_top_le _ _ (by lia)

theorem powSmulQuotInclusion_range {m n : ℕ} (h : m ≤ n) :
    (powSmulQuotInclusion I M h).range = I ^ m • ⊤ := by
  have : Function.Surjective ((I ^ n • ⊤ : Submodule R M).mkQ ∘ₗ
    topEquiv (R := R) (M := M) : ↥(⊤ : Submodule R M) →ₗ[R] M ⧸ I ^ n • ⊤) := by
    simpa using mkQ_surjective (I ^ n • ⊤)
  rw [powSmulQuotInclusion, range_liftQ, LinearMap.range_comp, LinearMap.range_comp,
    range_inclusion, ← map_comp, ← map_comap_eq_of_surjective this (I ^ m • ⊤)]
  congr 1; ext ⟨t, _⟩
  simp only [mem_comap, subtype_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    topEquiv_apply]
  rw [← mem_comap, ← sup_eq_right.mpr (pow_smul_top_le I M h), ← comap_map_mkQ, map_smul'',
    map_top, range_mkQ]

theorem factor_quotEquivOfEq_comm {p p' q q' : Submodule R M} (heq : p = p') (heq' : q = q')
    (hle : p ≤ q) : (quotEquivOfEq q q' heq') ∘ₗ (factor hle) =
      (factor (show p' ≤ q' by rwa [← heq, ← heq'])) ∘ₗ (quotEquivOfEq p p' heq) := by
  ext; rfl

lemma factor_quotEquivOfEq_comm_apply {p p' q q' : Submodule R M} (heq : p = p') (heq' : q = q')
    (hle : p ≤ q) {x} : (quotEquivOfEq q q' heq') ((factor hle) x) =
      factor (show p' ≤ q' by rwa [← heq, ← heq']) ((quotEquivOfEq p p' heq) x) := by
  simpa using LinearMap.ext_iff.mp (factor_quotEquivOfEq_comm ..) x

open Pointwise Classical in
theorem image_smul_top_eq_range_directSum {σ : Type*} (s : Set σ) (f : σ → R) :
    (f '' s • ⊤ : Submodule R M) =
      (DirectSum.toModule R s M (fun r ↦ LinearMap.lsmul R M (f r.val))).range := by
  refine Submodule.ext (fun m ↦ ⟨fun h ↦ LinearMap.mem_range.mpr ?_, fun ⟨c, h⟩ ↦ ?_⟩)
  · refine set_smul_inductionOn m h ?_ ?_ ?_ ⟨0, by simp⟩
    · rintro _ m ⟨i, i_in, rfl⟩ _
      use DirectSum.lof R s (fun (i : s) ↦ M) ⟨i, i_in⟩ m
      simp
    · intro r m m_in ⟨a, ha⟩
      use r • a; simp [ha]
    · intro m1 m2 _ _ ⟨a, ha⟩ ⟨b, hb⟩
      use a + b; simp [ha, hb]
  · rw [← h]; apply DirectSum.induction_lon (R := R) c
    · simp
    · intro ⟨r, r_in⟩ x
      simpa using mem_set_smul_of_mem_mem (show f r ∈ f '' s by use r) mem_top
    · intro _ _ h h'
      simpa using add_mem h h'

open Pointwise Classical in
theorem smul_top_eq_range_directSum (s : Set R) : (s • ⊤ : Submodule R M) =
    (DirectSum.toModule R s M (fun r ↦ LinearMap.lsmul R M r.val)).range := by
  simpa using image_smul_top_eq_range_directSum (M := M) s id

end Submodule

namespace AdicCompletion

open Submodule

@[simp]
lemma eval_zero : eval I M 0 = 0 := by
  have := Submodule.Quotient.subsingleton_iff.mpr (show I ^ 0 • (⊤ : Submodule R M) = ⊤ by simp)
  exact Subsingleton.allEq ..

theorem pow_smul_top_le_eval_ker (n : ℕ) : I ^ n • ⊤ ≤ (eval I M n).ker := by
  simp only [smul_le, mem_top, LinearMap.mem_ker, map_smul, coe_eval, forall_const]
  intro r r_in x
  rw [← Submodule.Quotient.mk_out (x.val n), ← Quotient.mk_smul, Quotient.mk_eq_zero]
  exact smul_mem_smul r_in mem_top

@[simp]
lemma algebraMap_apply {r : R} : algebraMap R (AdicCompletion I R) r = of I R r := by rfl

lemma smul_eq_of_smul {r : R} {x : AdicCompletion I M} : r • x = (of I R r) • x := by rfl

lemma val_apply_mem_smul_top_iff {m n : ℕ} {x : AdicCompletion I M}
    (m_ge : n ≤ m) : x.val m ∈ I ^ n • (⊤ : Submodule R (M ⧸ I ^ m • ⊤)) ↔ x.val n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa [mapQ, h, ← LinearMap.mem_ker, ker_liftQ] using x.prop m_ge⟩
  rw [← x.prop m_ge, transitionMap, factorPow, factor, mapQ, ← LinearMap.mem_ker]
  simpa [ker_liftQ]

open scoped Pointwise in
theorem set_smul_top_eq_restrictScalars_image_smul_top {s : Set R} :
    (s • ⊤ : Submodule R (AdicCompletion I M)) = ((of I R) '' s • ⊤ :
      Submodule (AdicCompletion I R) (AdicCompletion I M)).restrictScalars R := by
  refine le_antisymm (set_smul_le _ _ _ fun r x r_in _ ↦ ?_) ?_
  · rw [restrictScalars_mem, smul_eq_of_smul]
    exact mem_set_smul_of_mem_mem (Set.mem_image_of_mem _ r_in) mem_top
  intro x x_in
  rw [restrictScalars_mem] at x_in
  refine set_smul_inductionOn x x_in ?_ ?_ ?_ (zero_mem _)
  · rintro _ x ⟨r, r_in, rfl⟩ _
    rw [← smul_eq_of_smul]
    exact mem_set_smul_of_mem_mem r_in mem_top
  · intro r x h h'
    obtain ⟨c, c_supp, hc⟩ := (mem_set_smul ..).mp <| smul_mem _ r h
    simp only [hc, Finsupp.sum, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    refine sum_mem fun u u_in ↦ ?_
    obtain ⟨u, u_in', rfl⟩ := c_supp (Finset.mem_coe.mpr u_in)
    rw [← smul_eq_of_smul]
    exact mem_set_smul_of_mem_mem u_in' mem_top
  · intro _ _ _ _ h h'
    exact add_mem h h'

variable (M) in
/-- The canonical inclusion from the `I`-adic completion of `I ^ n • M` to
the `I`-adic completion of `M`. -/
def powSmulTopInclusion (n : ℕ) := (AdicCompletion.map I (topEquiv.toLinearMap ∘ₗ
    ((I ^ n • (⊤ : Submodule R M)).inclusion le_top)))

theorem powSmulTopInclusion_val_apply_eq_zero {n i : ℕ} (h : i ≤ n)
    {x : AdicCompletion I ↥(I ^ n • ⊤ : Submodule R M)} :
      (powSmulTopInclusion I M n x).val i = 0 := by
  rw [powSmulTopInclusion, map_val_apply]
  refine Quotient.induction_on _ (x.val i) fun z ↦ ?_
  simpa using pow_smul_top_le _ _ h z.prop

theorem powSmulTopInclusion_val_apply_eq_powSmulQuotInclusion {n i : ℕ} (h : n ≤ i)
    {x : AdicCompletion I ↥(I ^ n • ⊤ : Submodule R M)} : (powSmulTopInclusion I M n x).val i =
      powSmulQuotInclusion I M h (x.val (i - n)) := by
  rw [← x.prop (Nat.sub_le i n), powSmulTopInclusion, map_val_apply]
  refine Quotient.induction_on _ (x.val i) fun z ↦ ?_
  simp [powSmulQuotInclusion]

theorem powSmulTopInclusion_injective (n : ℕ) :
    Function.Injective (powSmulTopInclusion I M n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx; ext i
  simp only [AdicCompletion.ext_iff, val_zero, Pi.zero_apply] at hx
  specialize hx (i + n)
  rw [powSmulTopInclusion_val_apply_eq_powSmulQuotInclusion _ (by lia),
    LinearMap.map_eq_zero_iff _ (powSmulQuotInclusion_injective ..)] at hx
  rw [← x.prop (show i ≤ i + n - n by simp), hx, _root_.map_zero, val_zero, Pi.zero_apply]

private lemma liftOfValZeroAux_exists {m n : ℕ} {x : AdicCompletion I M} (h : x.val n = 0)
    (m_ge : n ≤ m) : ∃ t, powSmulQuotInclusion I M m_ge t = x.val m := by
  simpa [← LinearMap.mem_range, powSmulQuotInclusion_range] using
    (val_apply_mem_smul_top_iff I m_ge).mpr h

/-- An auxillary lift function used in the definition of `liftOfValZero`.
Use `liftOfValZero` instead. -/
def liftOfValZeroAux {m n : ℕ} {x : AdicCompletion I M} (h : x.val n = 0) (m_ge : n ≤ m) :
    ↥(I ^ n • ⊤ : Submodule R M) ⧸ I ^ (m - n) • (⊤ : Submodule R ↥(I ^ n • ⊤ : Submodule R M)) :=
  Exists.choose (liftOfValZeroAux_exists I h m_ge)

private lemma liftOfValZeroAux_prop_1 {m n : ℕ} {x : AdicCompletion I M} (h : x.val n = 0)
    (m_ge : n ≤ m) : (powSmulQuotInclusion I M m_ge) (liftOfValZeroAux I h m_ge) = x.val m :=
  Exists.choose_spec (liftOfValZeroAux_exists I h m_ge)

private lemma liftOfValZeroAux_prop_2 {i j n : ℕ} {x : AdicCompletion I M} (h : x.val n = 0)
    (h' : i ≤ j) : factorPow I _ (show i + n - n ≤ j + n - n by simpa)
      (liftOfValZeroAux I h (Nat.le_add_left n j)) =
        liftOfValZeroAux I h (Nat.le_add_left n i) := by
    rw [← (powSmulQuotInclusion_injective I (by lia)).eq_iff, liftOfValZeroAux_prop_1,
      ← factorPow_powSmulQuotInclusion_comm_apply I _ (by lia), liftOfValZeroAux_prop_1,
      ← transitionMap, x.prop (by lia)]

private lemma liftOfValZeroAux_prop_3 {n : ℕ} {x : AdicCompletion I M} (h : x.val n = 0) (m m' : ℕ)
    (hle : n ≤ m) (hle' : n ≤ m') (heq : m = m') : quotEquivOfEq _ _ (by rw [heq])
      (liftOfValZeroAux I h hle) = (liftOfValZeroAux I h hle') := by
  subst heq
  induction liftOfValZeroAux I h hle using Quotient.induction_on
  rfl

/-- Given an element `x` in the adic completion of `M` whose projection to `M / I ^ n • M` is zero,
`liftOfValZero` constructs the corresponding element in the adic completion of `I ^ n • M`. -/
@[no_expose]
def liftOfValZero {n : ℕ} {x : AdicCompletion I M} (hx : x.val n = 0) :
    AdicCompletion I ↥(I ^ n • (⊤ : Submodule R M)) where
  val i := quotEquivOfEq _ _ (by rw [Nat.add_sub_cancel]) <|
    liftOfValZeroAux I hx (Nat.le_add_left n i)
  property {i j} h := by
    simp only
    rw [← factor_quotEquivOfEq_comm_apply (show (I ^ (j + n - n) • ⊤ : Submodule R ↥(I ^ n • ⊤ :
      Submodule R M)) = I ^ j • ⊤ by simp) (show I ^ (i + n - n) • ⊤ = I ^ i • ⊤ by simp) (by
        simpa using pow_smul_top_le I _ h), ← factorPow]
    · rwa [liftOfValZeroAux_prop_2 I]
    simpa

@[simp]
theorem powSmulTopInclusion_liftOfValZero_apply {n : ℕ} {x : AdicCompletion I M}
    (hx : x.val n = 0) : powSmulTopInclusion I M n (liftOfValZero I hx) = x := by
  ext i; by_cases h : n ≤ i
  · rw [powSmulTopInclusion_val_apply_eq_powSmulQuotInclusion _ h]
    simp only [← liftOfValZeroAux_prop_1 I hx h, liftOfValZero,
      liftOfValZeroAux_prop_3 I hx (i - n + n) i (by lia) (by lia) (by lia)]
  replace h : i ≤ n := by lia
  rw [powSmulTopInclusion_val_apply_eq_zero _ h, ← x.prop h, hx, _root_.map_zero]

theorem powSmulQuotInclusion_liftOfValZero_val_apply {n i : ℕ} {x : AdicCompletion I M}
    (hx : x.val n = 0) (hle : n ≤ i) :
      powSmulQuotInclusion I M hle ((liftOfValZero I hx).val (i - n)) = x.val i := by
  rw [← powSmulTopInclusion_val_apply_eq_powSmulQuotInclusion,
    powSmulTopInclusion_liftOfValZero_apply]

theorem powSmulTopInclusion_range_eq_eval_ker {n : ℕ} :
    (powSmulTopInclusion I M n).range.restrictScalars R = (eval I M n).ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rcases hx with ⟨y, rfl⟩
    rw [LinearMap.mem_ker, eval_apply, powSmulTopInclusion_val_apply_eq_zero _ (by rfl)]
  simp only [LinearMap.mem_ker, coe_eval] at hx
  use liftOfValZero I hx; simp

theorem map_toModule_sum_eq_toModule_map {ι N : Type*} (P : ι → Type*) [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (P i)] [AddCommGroup N] [Module R N] (φ : ∀ i, P i →ₗ[R] N)
      [DecidableEq ι] : (map I (DirectSum.toModule R ι N φ)) ∘ₗ (sum I P) =
        DirectSum.toModule (AdicCompletion I R) ι (AdicCompletion I N) (fun i ↦ map I (φ i)) := by
  ext; simp

theorem map_lsmul_eq_lsmul_of (r : R) : map I (LinearMap.lsmul R M r) =
    LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) (of I R r) := by rfl

variable {I} in
theorem pow_smul_top_eq_eval_ker {n : ℕ} (h : I.FG) : I ^ n • ⊤ = (eval I M n).ker := by
  classical
  refine le_antisymm (pow_smul_top_le_eval_ker ..) ?_
  replace h := Ideal.FG.pow (n := n) h
  rcases h with ⟨s, hs⟩
  simp only [← hs, span_smul_eq]
  rw [set_smul_top_eq_restrictScalars_image_smul_top, ← powSmulTopInclusion_range_eq_eval_ker,
    restrictScalars_le, image_smul_top_eq_range_directSum]
  simp only [SetLike.coe_sort_coe, ← map_lsmul_eq_lsmul_of, ← map_toModule_sum_eq_toModule_map]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _ <|
    Function.RightInverse.surjective (g := sumInv I fun i ↦ M) (fun _ ↦ by
      rw [← LinearMap.comp_apply, sum_comp_sumInv, LinearMap.id_apply]))]
  rintro _ ⟨x, rfl⟩
  have : Function.Surjective ((DirectSum.toModule R s M fun r ↦ LinearMap.lsmul R M r).codRestrict
    (I ^ n • ⊤) (fun _ ↦ by simp [← hs, span_smul_eq, smul_top_eq_range_directSum])) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, ← hs, span_smul_eq,
      smul_top_eq_range_directSum]
    simp
  rcases map_surjective I this x with ⟨u, rfl⟩
  exact ⟨u, by rw [powSmulTopInclusion, ← LinearMap.comp_apply, map_comp]; rfl⟩

variable {I} in
/-- `AdicCompletion I M` is complete when `I` is finitely generated. -/
instance (h : I.FG) : IsAdicComplete I (AdicCompletion I M) where
  prec' x hx := by
    let L : AdicCompletion I M := {
      val i := (x i).val i
      property {m n} h' := by
        simp only [transitionMap_comp_eval_apply]
        specialize hx h'
        rwa [SModEq.sub_mem, pow_smul_top_eq_eval_ker h, LinearMap.mem_ker, _root_.map_sub,
          sub_eq_zero, eval_apply, eval_apply, eq_comm] at hx
    }
    use L; intro i
    rw [SModEq.sub_mem, pow_smul_top_eq_eval_ker h]
    simp [L]
