/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import KirkmanLib.Kirkman

/-!
# Proofs of the statements in `Challenge.lean`

The theorem is proved in `KirkmanLib/` (namespace `Kirkman`), with the definition stated
identically there. `SteinerOp.lean` shows that a Steiner operation (commutative, idempotent, with
`x ∘ (x ∘ y) = y`) yields a Steiner triple system of triples `{x, y, x ∘ y}`. `Constructions.lean`
gives Bose's operation on `Q × ℤ/3` from a commutative idempotent quasigroup and Skolem's on
`Option (Q × ℤ/3)` from a half-idempotent one; `Instances.lean` provides `(x + y)/2` on `ZMod n`
(`n` odd) and a half-idempotent quasigroup on `Fin (2t + 2)`. Necessity is a double count.
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
    (∃ 𝒯 : Finset (Finset (Fin v)), IsSTS 𝒯) ↔ v % 6 = 1 ∨ v % 6 = 3 :=
  Kirkman.kirkman v hv

end KirkmanTheorem
