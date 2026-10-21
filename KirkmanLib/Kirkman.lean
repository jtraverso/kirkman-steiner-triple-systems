/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import KirkmanLib.Instances

/-!
# Kirkman's theorem

* `Kirkman.kirkman`: **Kirkman (1847).** A Steiner triple system on `v ≥ 1` points exists if and
  only if `v ≡ 1` or `3 (mod 6)`.

A Steiner triple system on `Fin v` is a family of 3-element subsets such that every pair of
distinct points lies in exactly one of them (`Kirkman.IsSTS`). Necessity is a double count;
sufficiency uses Bose's construction for `v ≡ 3 (mod 6)` and Skolem's for `v ≡ 1 (mod 6)`.
-/

@[expose] public section

open Finset

namespace Kirkman

/-- `𝒯` is a Steiner triple system on `Fin v`: its members have three elements and every pair
of distinct points lies in exactly one member. -/
def IsSTS {v : ℕ} (𝒯 : Finset (Finset (Fin v))) : Prop :=
  (∀ T ∈ 𝒯, #T = 3) ∧ ∀ x y : Fin v, x ≠ y → ∃! T, T ∈ 𝒯 ∧ x ∈ T ∧ y ∈ T

lemma isSTS_of_equiv {P : Type*} [Fintype P] {v : ℕ} (S : SteinerOp P)
    (hP : Fintype.card P = v) : ∃ 𝒯 : Finset (Finset (Fin v)), IsSTS 𝒯 := by
  classical
  exact ⟨_, S.isSTSOn_triples.map (Fintype.equivFinOfCardEq hP)⟩

/-- Every point lies in `(v - 1) / 2` triples. -/
lemma two_mul_card_through {v : ℕ} {𝒯 : Finset (Finset (Fin v))} (h : IsSTS 𝒯) (x : Fin v) :
    2 * #(𝒯.filter (fun T => x ∈ T)) = v - 1 := by
  have hU : (univ : Finset (Fin v)).erase x = (𝒯.filter (fun T => x ∈ T)).biUnion
      (fun T => T.erase x) := by
    ext y
    simp only [mem_erase, mem_univ, and_true, mem_biUnion, mem_filter]
    constructor
    · intro hyx
      obtain ⟨T, ⟨hT, hxT, hyT⟩, -⟩ := h.2 x y (Ne.symm hyx)
      exact ⟨T, ⟨hT, hxT⟩, hyx, hyT⟩
    · rintro ⟨T, -, hyx, -⟩; exact hyx
  have hdisj : (↑(𝒯.filter (fun T => x ∈ T)) : Set (Finset (Fin v))).PairwiseDisjoint
      (fun T => T.erase x) := by
    intro T hT T' hT' hne
    simp only [coe_filter, Set.mem_ofPred_eq] at hT hT'
    rw [Function.onFun, disjoint_left]
    intro y hy hy'
    rw [mem_erase] at hy hy'
    obtain ⟨S, -, hS⟩ := h.2 x y (Ne.symm hy.1)
    exact hne ((hS T ⟨hT.1, hT.2, hy.2⟩).trans (hS T' ⟨hT'.1, hT'.2, hy'.2⟩).symm)
  have := congrArg Finset.card hU
  rw [card_biUnion hdisj, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at this
  rw [this, sum_congr rfl (g := fun _ => 2), sum_const, smul_eq_mul, mul_comm]
  intro T hT
  rw [mem_filter] at hT
  rw [card_erase_of_mem hT.2, h.1 T hT.1]

/-- The double count `∑ₓ #{T ∋ x} = 3 #𝒯`. -/
lemma sum_card_through {v : ℕ} {𝒯 : Finset (Finset (Fin v))} (h : IsSTS 𝒯) :
    ∑ x : Fin v, #(𝒯.filter (fun T => x ∈ T)) = 3 * #𝒯 := by
  simp only [card_filter]
  rw [sum_comm]
  rw [card_eq_sum_ones, mul_sum, mul_one]
  refine sum_congr rfl fun T hT => ?_
  rw [← card_filter]
  have e : (univ : Finset (Fin v)).filter (fun i => i ∈ T) = T := by ext; simp
  rw [e, h.1 T hT]

/-- **Kirkman (1847).** -/
theorem kirkman (v : ℕ) (hv : 0 < v) :
    (∃ 𝒯 : Finset (Finset (Fin v)), IsSTS 𝒯) ↔ v % 6 = 1 ∨ v % 6 = 3 := by
  constructor
  · rintro ⟨𝒯, h𝒯⟩
    set d := #(𝒯.filter (fun T => (⟨0, hv⟩ : Fin v) ∈ T))
    have hd : 2 * d = v - 1 := two_mul_card_through h𝒯 _
    have hsum := sum_card_through h𝒯
    have hall : ∀ x : Fin v, #(𝒯.filter (fun T => x ∈ T)) = d := by
      intro x
      have := two_mul_card_through h𝒯 x
      omega
    rw [sum_congr rfl (fun x _ => hall x), sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul] at hsum
    have h3 : 3 ∣ v * d := ⟨#𝒯, hsum⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with ⟨a, ha⟩ | ⟨c, hc⟩ <;> omega
  · rintro (h | h)
    · by_cases hv1 : v = 1
      · subst hv1
        refine ⟨∅, fun T hT => absurd hT (notMem_empty _), fun x y hxy => ?_⟩
        exact absurd (Subsingleton.elim x y) hxy
      · obtain ⟨t, rfl⟩ : ∃ t, v = 6 * t + 7 := ⟨(v - 7) / 6, by omega⟩
        exact isSTS_of_equiv (skolemSteiner (skolemQ t)) (by simp; ring)
    · obtain ⟨n, rfl⟩ : ∃ n, v = 3 * n := ⟨v / 3, by omega⟩
      have hn : n % 2 = 1 := by omega
      have : NeZero n := ⟨by omega⟩
      exact isSTS_of_equiv (boseSteiner (boseQ hn) (boseQ_idem hn)) (by simp; ring)

end Kirkman
