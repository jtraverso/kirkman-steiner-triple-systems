/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import KirkmanLib.Constructions

/-!
# The quasigroups for Bose and Skolem

* For odd `n`, `x ∘ y = (x + y) / 2` on `ZMod n` is a commutative idempotent quasigroup.
* For `s ≥ 1`, on `Fin (2s)` let `g` send an even residue `2a` to `a` and an odd residue
  `2a + 1` to `a + s`; then `x ∘ y = g (x + y)` is a half-idempotent commutative quasigroup with
  `τ x = x + s` and first half `{x | x < s}`.
-/

@[expose] public section

namespace Kirkman

/-! ### Bose: `(x + y) / 2` on `ZMod n`, `n` odd -/

section BoseQ

variable {n : ℕ} (hn : n % 2 = 1)

/-- One half in `ZMod n` for odd `n`. -/
def half (n : ℕ) : ZMod n := (((n + 1) / 2 : ℕ) : ZMod n)

include hn in
lemma two_mul_half : 2 * half n = 1 := by
  unfold half
  have : 2 * ((n + 1) / 2) = n + 1 := by omega
  have h2 : ((2 * ((n + 1) / 2) : ℕ) : ZMod n) = 2 * (((n + 1) / 2 : ℕ) : ZMod n) := by
    push_cast; ring
  rw [← h2, this]
  push_cast
  rw [ZMod.natCast_self, zero_add]

/-- The quasigroup `(x + y) / 2`. -/
def boseQ : CQ (ZMod n) where
  L x y := (x + y) * half n
  D x y := 2 * y - x
  comm x y := by ring
  LD x y := by linear_combination y * two_mul_half hn
  DL x y := by linear_combination (x + y) * two_mul_half hn

lemma boseQ_idem (x : ZMod n) : (boseQ hn).L x x = x := by
  change (x + x) * half n = x
  linear_combination x * two_mul_half hn

end BoseQ

/-! ### Skolem: a half-idempotent quasigroup on `Fin (2t + 2)` -/

section SkolemQ

lemma addv {t : ℕ} (a b : Fin (2 * t + 2)) :
    (a + b).val = if a.val + b.val < 2 * t + 2 then a.val + b.val
      else a.val + b.val - (2 * t + 2) := by
  rw [Fin.val_add]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by have := a.isLt; have := b.isLt; omega)]

/-- The element `t + 1` of `Fin (2t + 2)`. -/
def sElt (t : ℕ) : Fin (2 * t + 2) := ⟨t + 1, by omega⟩

/-- `g`: even residues `2a ↦ a`, odd residues `2a + 1 ↦ a + (t + 1)`. -/
def gfun {t : ℕ} (r : Fin (2 * t + 2)) : Fin (2 * t + 2) :=
  if r.val % 2 = 0 then ⟨r.val / 2, by have := r.isLt; omega⟩
  else ⟨r.val / 2 + (t + 1), by have := r.isLt; omega⟩

/-- The inverse of `g`. -/
def ginv {t : ℕ} (c : Fin (2 * t + 2)) : Fin (2 * t + 2) :=
  if h : c.val < t + 1 then ⟨2 * c.val, by omega⟩
  else ⟨2 * (c.val - (t + 1)) + 1, by have := c.isLt; omega⟩

lemma g_ginv {t : ℕ} (c : Fin (2 * t + 2)) : gfun (ginv c) = c := by
  unfold gfun ginv
  by_cases h : c.val < t + 1
  · rw [dite_eq_left h]
    apply Fin.ext
    rw [ite_eq_left (by simp only; omega)]
    simp only; omega
  · rw [dite_eq_right h]
    apply Fin.ext
    rw [ite_eq_right (by simp only; omega)]
    simp only; omega

lemma ginv_g {t : ℕ} (r : Fin (2 * t + 2)) : ginv (gfun r) = r := by
  unfold gfun ginv
  have := r.isLt
  by_cases h : r.val % 2 = 0
  · rw [ite_eq_left h, dite_eq_left (by simp only; omega)]
    apply Fin.ext; simp only; omega
  · rw [ite_eq_right h, dite_eq_right (by simp only; omega)]
    apply Fin.ext; simp only; omega

/-- The quasigroup `g (x + y)`. -/
def skolemCQ (t : ℕ) : CQ (Fin (2 * t + 2)) where
  L x y := gfun (x + y)
  D x y := ginv y - x
  comm x y := by rw [add_comm x y]
  LD x y := by rw [add_sub_cancel, g_ginv]
  DL x y := by rw [ginv_g]; abel

lemma s_add_s {t : ℕ} : sElt t + sElt t = 0 := by
  apply Fin.ext
  rw [addv, Fin.val_zero]
  have h : (sElt t).val = t + 1 := rfl
  split <;> omega

/-- The half-idempotent quasigroup for Skolem's construction. -/
def skolemQ (t : ℕ) : HalfIdem (Fin (2 * t + 2)) where
  toCQ := skolemCQ t
  τ x := x + sElt t
  H x := x.val < t + 1
  ττ x := by rw [add_assoc, s_add_s, add_zero]
  Hτ x := by
    rw [addv]
    have := x.isLt
    split_ifs <;> simp only [sElt] at * <;> omega
  Lτ x := by
    change gfun (x + sElt t + (x + sElt t)) = gfun (x + x)
    congr 1
    have : x + sElt t + (x + sElt t) = x + x + (sElt t + sElt t) := by abel
    rw [this, s_add_s, add_zero]
  LH x hx := by
    change gfun (x + x) = x
    have hx' : x.val < t + 1 := hx
    have hxx : (x + x).val = 2 * x.val := by
      rw [addv]; split_ifs <;> omega
    unfold gfun
    apply Fin.ext
    rw [ite_eq_left (by rw [hxx]; omega)]
    simp only [hxx]; omega

end SkolemQ

end Kirkman
