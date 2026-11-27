/-
Copyright (c) 2026 Parker Lipscomb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Parker Lipscomb
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Set.Card

/-!
# Statement Formalization: Coste–Csikós–Viennot Outerplanar Equitable Quotient Conjecture

This file formalizes the definitions and conjecture from:

* Louann Coste, Mónika Csikós, and Laurent Viennot, *Color Refinement Distinguishes Connected
  Rooted Outerplanar Graphs*, `arXiv:2611.18391v1` (submitted 2026-11-13).

(Prior art note: for the special case of graph covers / locally bijective homomorphisms,
Dickson Y. B. Annor's PhD thesis, *Graph Covers: Topological and Combinatorial Perspectives*
(La Trobe University; abstract in *Bull. Aust. Math. Soc.* 2026,
`doi:10.1017/s0004972726102111`), proves the outerplanar cover case; Coste–Csikós–Viennot's
conjecture concerns arbitrary equitable colorings, allowing intra-class edges, unequal class sizes,
and neighbor counts $K_{ij} > 1$.)

## Verbatim Primary-Source Definitions and Conjecture

* **Equitable coloring (`2_preliminaries.tex`, lines 30–32):**
  > we say that $c$ is *equitable* if for every $i, j \in [|c|]$, all vertices of color $i$ have
  > the same number of neighbors of color $j$.

* **Color graph and underlying simple graph (`2_preliminaries.tex`, lines 46–59):**
  > Let $c$ be an equitable coloring of $G$. The *color graph* $K = \mathrm{CG}(G, c)$ of $(G, c)$
  > is the vertex- and arc-weighted directed graph on $[|c|]$ in which the color $i$ carries the
  > vertex weight $w_i = |c^{-1}(i)|$ and there is an arc $(i, j)$ of weight
  > $K_{ij} = |\{u \in N_G(v) : c(u) = j\}|$ for any vertex $v$ with $c(v) = i$ whenever this
  > number is positive. ... We write $\widetilde{K}$ for the *underlying simple graph* of $K$,
  > obtained by forgetting weights, directions and loops.

* **Outerplanar graphs (`2_preliminaries.tex`, lines 80–82):**
  > A graph is *outerplanar* if it admits a planar embedding in which every vertex lies on the
  > boundary of the outer face; equivalently, if it has neither $K_4$ nor $K_{2,3}$ as a minor.

* **Corollary `cor:K-outerplanar` and Conjecture (`5_details.tex`, lines 43–47):**
  > **Corollary.** Given a connected rooted outerplanar graph $(G, r)$, the underlying graph
  > $\widetilde{K}$ of its color graph is outerplanar.
  >
  > We conjecture that this still holds for any equitable coloring of a connected outerplanar
  > graph (not necessarily with a singleton color class).

## Contents

1. `HasMinor`, `K4`, `K23`, and `IsOuterplanar` (the forbidden-minor characterization of
   outerplanar graphs).
2. `colorNeighborCount`, `IsEquitableColoring`, and `colorQuotientSimple` ($\widetilde{K}$).
3. Definition-fidelity sanity lemmas (`hasMinor_refl`, `not_isOuterplanar_K4`,
   `not_isOuterplanar_K23`, `colorNeighborCount_eq_filter_card`,
   `colorQuotientSimple_adj_iff_pos_count`).
4. Headline statement propositions `CosteCsikosViennotConjecture` (exact verbatim conjecture) and
   `OuterplanarEquitableQuotientStatement` (stronger version dropping connectedness for arbitrary
   color types). No conjecture proofs appear in this statement-only module.
-/

@[expose] public section

namespace LeanForge.CosteOuterplanar

/-! ### 1. Graph Minors and Outerplanarity (`2_preliminaries.tex`, lines 80–82) -/

/-- A simple graph `H` is a *minor* of a simple graph `G` if there exists a minor model
`B : W → Set V` consisting of pairwise disjoint vertex subsets whose induced subgraphs
`G.induce (B w)` are connected (hence nonempty), such that every edge `H.Adj u v` is witnessed
by at least one edge of `G` between `B u` and `B v`. -/
def HasMinor {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ B : W → Set V,
    (∀ w : W, (G.induce (B w)).Connected) ∧
    Pairwise (Function.onFun Disjoint B) ∧
    (∀ u v : W, H.Adj u v → ∃ x ∈ B u, ∃ y ∈ B v, G.Adj x y)

/-- The complete graph `K_4` on `Fin 4`. -/
abbrev K4 : SimpleGraph (Fin 4) := ⊤

/-- The complete bipartite graph `K_{2,3}` on `Fin 2 ⊕ Fin 3`. -/
abbrev K23 : SimpleGraph (Fin 2 ⊕ Fin 3) := completeBipartiteGraph (Fin 2) (Fin 3)

/-- A simple graph is *outerplanar* iff it has neither `K_4` nor `K_{2,3}` as a minor
(Chartrand–Harary forbidden-minor characterization, matching `2_preliminaries.tex` lines 81–82). -/
def IsOuterplanar {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ HasMinor G K4 ∧ ¬ HasMinor G K23

/-- Every graph is a minor of itself via singleton branch sets. -/
theorem hasMinor_refl {V : Type*} (G : SimpleGraph V) : HasMinor G G := by
  refine ⟨fun v => {v}, ?_, ?_, ?_⟩
  · intro v
    have : Nonempty ({v} : Set V) := ⟨⟨v, Set.mem_singleton v⟩⟩
    refine ⟨fun x y => ?_⟩
    have hx : x.1 = v := Set.mem_singleton_iff.mp x.2
    have hy : y.1 = v := Set.mem_singleton_iff.mp y.2
    have hxy : x = y := Subtype.ext (hx.trans hy.symm)
    subst hxy
    exact SimpleGraph.Reachable.refl x
  · intro u v huv
    exact Set.disjoint_singleton.mpr huv
  · intro u v huv
    exact ⟨u, Set.mem_singleton u, v, Set.mem_singleton v, huv⟩

/-- `K_4` is not outerplanar. -/
theorem not_isOuterplanar_K4 : ¬ IsOuterplanar K4 :=
  fun h => h.1 (hasMinor_refl K4)

/-- `K_{2,3}` is not outerplanar. -/
theorem not_isOuterplanar_K23 : ¬ IsOuterplanar K23 :=
  fun h => h.2 (hasMinor_refl K23)

/-! ### 2. Equitable Colorings and Simple Color Quotient (`2_preliminaries.tex`, lines 30–59) -/

/-- Number of neighbors of vertex `v` in `G` having color `j` under coloring `c`:
`K_{c(v), j} = |{w ∈ N_G(v) : c(w) = j}|`.
Intended for finite vertex types `V` (matching the `[Finite V]` / `[Fintype V]` hypotheses on all
downstream lemmas and conjectures), where `Set.ncard` agrees with `Finset.card`. -/
noncomputable def colorNeighborCount {V C : Type*}
    (G : SimpleGraph V) (c : V → C) (v : V) (j : C) : ℕ :=
  Set.ncard {w : V | G.Adj v w ∧ c w = j}

/-- On a finite graph with decidable adjacency and color equality, `colorNeighborCount G c v j`
equals the cardinality of the filtered `Finset` of `j`-colored neighbors of `v`. -/
theorem colorNeighborCount_eq_filter_card {V C : Type*} [Fintype V] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → C) (v : V) (j : C) :
    colorNeighborCount G c v j =
      (Finset.univ.filter fun w : V => G.Adj v w ∧ c w = j).card := by
  unfold colorNeighborCount
  have hcoe : ((Finset.univ.filter fun w : V => G.Adj v w ∧ c w = j : Finset V) : Set V) =
      {w : V | G.Adj v w ∧ c w = j} := by
    ext w
    simp
  rw [← hcoe, Set.ncard_coe_finset]

/-- A coloring `c : V → C` of `G` is *equitable* if vertices of the same color have the same
number of neighbors of every color `j : C` (`2_preliminaries.tex`, lines 30–32). -/
def IsEquitableColoring {V C : Type*} (G : SimpleGraph V) (c : V → C) : Prop :=
  ∀ u v : V, c u = c v → ∀ j : C,
    colorNeighborCount G c u j = colorNeighborCount G c v j

/-- The underlying simple graph `\widetilde{K}` of the color graph `CG(G, c)`
(`2_preliminaries.tex`, lines 46–59): distinct colors `i ≠ j` are adjacent iff there exists
an edge of `G` between a vertex of color `i` and a vertex of color `j`. -/
def colorQuotientSimple {V C : Type*} (G : SimpleGraph V) (c : V → C) : SimpleGraph C where
  Adj i j := i ≠ j ∧ ∃ u v : V, c u = i ∧ c v = j ∧ G.Adj u v
  symm := ⟨fun _ _ ⟨hne, u, v, hu, hv, hadj⟩ => ⟨hne.symm, v, u, hv, hu, hadj.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- Fidelity check matching `2_preliminaries.tex` lines 48–59: for a finite graph `G` with a
surjective equitable coloring `c`, two colors `i, j` are adjacent in `colorQuotientSimple G c`
iff `i ≠ j` and every vertex `u` of color `i` has `K_{ij} = colorNeighborCount G c u j > 0`. -/
theorem colorQuotientSimple_adj_iff_pos_count {V C : Type*} [Finite V]
    {G : SimpleGraph V} {c : V → C}
    (heq : IsEquitableColoring G c) (hsurj : Function.Surjective c) (i j : C) :
    (colorQuotientSimple G c).Adj i j ↔
      i ≠ j ∧ ∀ u : V, c u = i → 0 < colorNeighborCount G c u j := by
  constructor
  · rintro ⟨hne, u₀, v₀, hu₀, hv₀, hadj⟩
    refine ⟨hne, fun u hu => ?_⟩
    rw [heq u u₀ (hu.trans hu₀.symm) j]
    unfold colorNeighborCount
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨v₀, hadj, hv₀⟩
  · rintro ⟨hne, hpos⟩
    obtain ⟨u, hu⟩ := hsurj i
    have hgt : 0 < Set.ncard {w : V | G.Adj u w ∧ c w = j} := hpos u hu
    obtain ⟨v, hadj, hv⟩ := Set.nonempty_of_ncard_ne_zero (Nat.pos_iff_ne_zero.mp hgt)
    exact ⟨hne, u, v, hu, hv, hadj⟩

/-! ### 3. Conjecture Statements (`5_details.tex`, line 47) -/

/-- **Coste–Csikós–Viennot Conjecture** (`arXiv:2611.18391v1`, `5_details.tex` line 47):
For any finite connected outerplanar graph `G` and any surjective equitable coloring
`c : V → Fin k` (not necessarily with a singleton color class), the underlying simple quotient
graph `\widetilde{K}` (`colorQuotientSimple G c`) is outerplanar. -/
def CosteCsikosViennotConjecture.{u} : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (k : ℕ) (c : V → Fin k),
    G.Connected →
    IsOuterplanar G →
    Function.Surjective c →
    IsEquitableColoring G c →
    IsOuterplanar (colorQuotientSimple G c)

/-- **Stronger Unrestricted Statement:** Dropping connectedness and allowing any color type `C`,
for every finite outerplanar graph `G` and every surjective equitable coloring `c : V → C`,
the underlying simple quotient graph `colorQuotientSimple G c` is outerplanar. -/
def OuterplanarEquitableQuotientStatement.{u, v} : Prop :=
  ∀ (V : Type u) (C : Type v) [Finite V] (G : SimpleGraph V) (c : V → C),
    IsOuterplanar G →
    Function.Surjective c →
    IsEquitableColoring G c →
    IsOuterplanar (colorQuotientSimple G c)

end LeanForge.CosteOuterplanar
