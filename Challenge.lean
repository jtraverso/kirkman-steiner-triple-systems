/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Kirkman's theorem

* `KirkmanTheorem.kirkman`: **Kirkman (1847).** A Steiner triple system on `v ≥ 1` points exists
  if and only if `v ≡ 1` or `3 (mod 6)`.

A Steiner triple system on `Fin v` is a family of 3-element subsets such that every pair of
distinct points lies in exactly one of them (`KirkmanTheorem.IsSTS`). Necessity is a double count;
sufficiency uses Bose's construction for `v ≡ 3 (mod 6)` and Skolem's for `v ≡ 1 (mod 6)`.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open Finset

namespace KirkmanTheorem

/-- `𝒯` is a Steiner triple system on `Fin v`: its members have three elements and every pair
of distinct points lies in exactly one member. -/
def IsSTS {v : ℕ} (𝒯 : Finset (Finset (Fin v))) : Prop :=
  (∀ T ∈ 𝒯, #T = 3) ∧ ∀ x y : Fin v, x ≠ y → ∃! T, T ∈ 𝒯 ∧ x ∈ T ∧ y ∈ T

/-- **Kirkman (1847).** -/
theorem kirkman (v : ℕ) (hv : 0 < v) :
    (∃ 𝒯 : Finset (Finset (Fin v)), IsSTS 𝒯) ↔ v % 6 = 1 ∨ v % 6 = 3 := by
  sorry

end KirkmanTheorem
