# Equitable quotients of outerplanar graphs are outerplanar (Lean 4)

Lean 4 + Mathlib formalization of a proof of the conjecture stated after Corollary 4.6 of

> L. Coste, M. Csikós, L. Viennot, *Color Refinement Distinguishes Connected Rooted Outerplanar Graphs*, [arXiv:2611.18391](https://arxiv.org/abs/2611.18391) (2026):
> "We conjecture that this still holds for any equitable coloring of a connected outerplanar graph (not necessarily with a singleton color class)."

**Author:** Parker Lipscomb (independent student researcher). AI tools were used under the author's direction to search for the proof, write the formalization and draft the note; see the note's acknowledgments.

## Theorem

Let `G` be a finite outerplanar graph (no `K4` or `K2,3` minor), not necessarily connected, and let `c` be a surjective equitable coloring of `G`. Then the underlying simple graph of the color graph of `(G, c)` is outerplanar.

Human-readable proof: [`outerplanar-equitable-quotients-lipscomb.pdf`](./outerplanar-equitable-quotients-lipscomb.pdf) (Theorem 1.1).

## Lean statements

Definitions are in `LeanForge/CosteOuterplanarStatement.lean`; proofs in `LeanForge/CosteOuterplanarProof.lean`.

```lean
def CosteCsikosViennotConjecture.{u} : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (k : ℕ) (c : V → Fin k),
    G.Connected → IsOuterplanar G → Function.Surjective c →
    IsEquitableColoring G c → IsOuterplanar (colorQuotientSimple G c)

theorem coste_csikos_viennot_conjecture.{u} : CosteCsikosViennotConjecture.{u}

-- stronger: no connectivity assumption, any color type
theorem outerplanar_equitable_quotient_isOuterplanar.{u, v} :
    OuterplanarEquitableQuotientStatement.{u, v}
```

`IsOuterplanar G := ¬ HasMinor G K4 ∧ ¬ HasMinor G K23`, where `HasMinor` is given by a minor model (pairwise disjoint connected branch sets).

## Verify

Requires [elan](https://github.com/leanprover/elan). Toolchain `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0`.

```sh
lake exe cache get
lake build
lake env leanchecker LeanForge.CosteOuterplanarProof
lake env leanchecker-paranoid LeanForge.CosteOuterplanarProof
```

`#print axioms` on both headline theorems reports only `propext`, `Classical.choice`, `Quot.sound`. The project contains no `sorry`, `admit` or `native_decide`.

## Citation

See [`CITATION.cff`](./CITATION.cff). License: MIT.
