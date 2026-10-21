# Kirkman's theorem on Steiner triple systems in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A *Steiner triple system* on `Fin v` is a family of 3-element subsets such that every pair of
distinct points lies in exactly one member (`KirkmanTheorem.IsSTS`).

`KirkmanTheorem.kirkman`, **Kirkman's theorem (1847).** For `v ≥ 1`, a Steiner triple system on
`v` points exists if and only if `v ≡ 1` or `3 (mod 6)`.

The definition is stated in `Challenge.lean`; `comparator.json` selects only the theorem, and the
definition enters the check only as part of the theorem statement. Mathlib does not contain
Steiner triple systems.

## Files

- [`Challenge.lean`](Challenge.lean): the definition and the audited statement. It imports only
  Mathlib.
- [`Solution.lean`](Solution.lean) and [`KirkmanLib/`](KirkmanLib): the proof.
- [`comparator.json`](comparator.json): the theorem that is compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proof goes

* **Necessity** (`Kirkman.lean`). The triples through a point split the other `v − 1` points into
  pairs, so `v` is odd; counting incidences gives `v (v − 1) / 2 = 3 · (number of triples)`, so `3`
  divides `v` or `(v − 1)/2`, that is, `v ≡ 3` or `1 (mod 6)`.
* **Steiner quasigroups** (`SteinerOp.lean`). A commutative idempotent operation with
  `x ∘ (x ∘ y) = y` gives the Steiner triple system of the triples `{x, y, x ∘ y}`.
* **Bose's construction** (`Constructions.lean`, `Instances.lean`), `v = 3n` with `n` odd: on
  `ZMod n × ℤ/3`, from the commutative idempotent quasigroup `(x + y)/2` on `ZMod n`.
* **Skolem's construction**, `v = 6t + 7`: on `(Fin (2t + 2) × ℤ/3) ∪ {∞}`, from the
  half-idempotent commutative quasigroup sending `x, y` to `g (x + y)`, where `g` maps an even
  residue `2a` to `a` and an odd residue `2a + 1` to `a + t + 1`. The case `v = 1` is the empty
  system.

## Sources

* T. P. Kirkman, *On a problem in combinations*, Cambridge and Dublin Math. J. 2 (1847) 191–204.
* R. C. Bose, *On the construction of balanced incomplete block designs*, Ann. Eugenics 9 (1939)
  353–399, doi:10.1111/j.1469-1809.1939.tb02219.x.
* Th. Skolem, *Some remarks on the triple systems of Steiner*, Math. Scand. 6 (1958) 273–280,
  doi:10.7146/math.scand.a-10551.

## Authorship and use of AI

The author chose the result. The statement and the Lean proof were written with Claude in Claude
Code and checked locally. Lean checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
