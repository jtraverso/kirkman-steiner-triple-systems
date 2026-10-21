/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Steiner triple systems from Steiner quasigroups

A *Steiner operation* on `P` is a commutative idempotent operation with `x ∘ (x ∘ y) = y`. The sets
`{x, y, x ∘ y}` with `x ≠ y` form a Steiner triple system on `P`.
-/

@[expose] public section

open Finset

namespace Kirkman

variable {P : Type*}

/-- `𝒯` is a Steiner triple system on `P`: its members have three elements and every pair of
distinct points lies in exactly one member. -/
def IsSTSOn [DecidableEq P] (𝒯 : Finset (Finset P)) : Prop :=
  (∀ T ∈ 𝒯, #T = 3) ∧ ∀ x y : P, x ≠ y → ∃! T, T ∈ 𝒯 ∧ x ∈ T ∧ y ∈ T

/-- A Steiner operation. -/
structure SteinerOp (P : Type*) where
  /-- The operation. -/
  op : P → P → P
  comm : ∀ x y, op x y = op y x
  idem : ∀ x, op x x = x
  cancel : ∀ x y, op x (op x y) = y

namespace SteinerOp

variable (S : SteinerOp P)

lemma ne_left {x y : P} (h : x ≠ y) : S.op x y ≠ x := by
  intro e
  apply h
  have := S.cancel x y
  rwa [e, S.idem] at this

lemma ne_right {x y : P} (h : x ≠ y) : S.op x y ≠ y := by
  rw [S.comm]; exact S.ne_left (Ne.symm h)

variable [DecidableEq P]

/-- The triple through `x` and `y`. -/
def tri (x y : P) : Finset P := {x, y, S.op x y}

lemma card_tri {x y : P} (h : x ≠ y) : #(S.tri x y) = 3 := by
  unfold tri
  rw [card_insert_of_notMem, card_pair (S.ne_right h).symm]
  simp only [mem_insert, mem_singleton, not_or]
  exact ⟨h, (S.ne_left h).symm⟩

omit [DecidableEq P] in
lemma op_op_left (x y : P) : S.op (S.op x y) x = y := by rw [S.comm, S.cancel]

omit [DecidableEq P] in
lemma op_op_right (x y : P) : S.op y (S.op x y) = x := by rw [S.comm x y, S.cancel]

omit [DecidableEq P] in
lemma op_op_right' (x y : P) : S.op (S.op x y) y = x := by rw [S.comm, S.op_op_right]

/-- The operation maps two points of a triple into the triple. -/
lemma op_mem_tri {a b u w : P} (hu : u ∈ S.tri a b) (hw : w ∈ S.tri a b) :
    S.op u w ∈ S.tri a b := by
  unfold tri at *
  simp only [mem_insert, mem_singleton] at hu hw ⊢
  rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
    first
    | simp [S.idem, S.op_op_left, S.op_op_right, S.op_op_right']
    | simp [S.op_op_right, S.comm]

lemma tri_eq {a b x y : P} (hab : a ≠ b) (hxy : x ≠ y) (hx : x ∈ S.tri a b)
    (hy : y ∈ S.tri a b) : S.tri a b = S.tri x y := by
  symm
  refine eq_of_subset_of_card_le ?_ (by rw [S.card_tri hab, S.card_tri hxy])
  intro w hw
  unfold tri at hw
  simp only [mem_insert, mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact hx
  · exact hy
  · exact S.op_mem_tri hx hy

lemma mem_tri_left (x y : P) : x ∈ S.tri x y := by unfold tri; simp

lemma mem_tri_right (x y : P) : y ∈ S.tri x y := by unfold tri; simp

variable [Fintype P]

/-- The triples of a Steiner operation. -/
def triples : Finset (Finset P) :=
  (univ.filter (fun p : P × P => p.1 ≠ p.2)).image (fun p => S.tri p.1 p.2)

theorem isSTSOn_triples : IsSTSOn S.triples := by
  refine ⟨fun T hT => ?_, fun x y hxy => ?_⟩
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 hT
    exact S.card_tri (mem_filter.1 hab).2
  · refine ⟨S.tri x y, ⟨mem_image.2 ⟨(x, y), mem_filter.2 ⟨mem_univ _, hxy⟩, rfl⟩,
      S.mem_tri_left x y, S.mem_tri_right x y⟩, ?_⟩
    rintro T ⟨hT, hxT, hyT⟩
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 hT
    exact S.tri_eq (mem_filter.1 hab).2 hxy hxT hyT

end SteinerOp

/-- A Steiner triple system transports along a bijection. -/
theorem IsSTSOn.map [DecidableEq P] {Q : Type*} [DecidableEq Q] {𝒯 : Finset (Finset P)} (h :
    IsSTSOn 𝒯)
    (e : P ≃ Q) : IsSTSOn (𝒯.map ⟨fun T => T.map e.toEmbedding, map_injective _⟩) := by
  refine ⟨fun T hT => ?_, fun x y hxy => ?_⟩
  · obtain ⟨T₁, hT₁, rfl⟩ := mem_map.1 hT
    simp only [Function.Embedding.coeFn_mk, card_map]
    exact h.1 T₁ hT₁
  · have hxy' : e.symm x ≠ e.symm y := fun h' => hxy (e.symm.injective h')
    obtain ⟨T, ⟨hT, hxT, hyT⟩, huniq⟩ := h.2 _ _ hxy'
    refine ⟨T.map e.toEmbedding, ⟨mem_map_of_mem _ hT, ?_, ?_⟩, ?_⟩
    · exact mem_map.2 ⟨_, hxT, by simp⟩
    · exact mem_map.2 ⟨_, hyT, by simp⟩
    · rintro T' ⟨hT', hxT', hyT'⟩
      obtain ⟨T₀, hT₀, rfl⟩ := mem_map.1 hT'
      simp only [Function.Embedding.coeFn_mk] at hxT' hyT' ⊢
      have hx0 : e.symm x ∈ T₀ := by
        obtain ⟨u, hu, hux⟩ := mem_map.1 hxT'
        simp only [Equiv.coe_toEmbedding] at hux
        rw [← hux, Equiv.symm_apply_apply]; exact hu
      have hy0 : e.symm y ∈ T₀ := by
        obtain ⟨u, hu, hux⟩ := mem_map.1 hyT'
        simp only [Equiv.coe_toEmbedding] at hux
        rw [← hux, Equiv.symm_apply_apply]; exact hu
      rw [huniq T₀ ⟨hT₀, hx0, hy0⟩]

end Kirkman
