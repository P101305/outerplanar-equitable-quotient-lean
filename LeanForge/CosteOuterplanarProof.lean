/-
Copyright (c) 2026 Parker Lipscomb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Parker Lipscomb
-/
module

public import LeanForge.CosteConnectivity
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum

/-!
# Proof of the Coste–Csikós–Viennot Outerplanar Equitable Quotient Conjecture

This file implements the main minimal-counterexample proof, establishing:

* **Theorem 1 (`subdivGraph_mixedQuotient_isOuterplanar`):** For every finite tagged mixed
  multigraph `M` whose subdivision graph `subdivGraph M` is outerplanar and every surjective
  equitable coloring `c` of `M`, the subdivision graph of the tagged mixed quotient
  `mixedQuotient M c` is outerplanar.
* **`outerplanar_equitable_quotient_isOuterplanar`:** Stronger unrestricted theorem (arbitrary
  finite vertex type `V : Type u` and color type `C : Type v`, no connectedness needed).
* **`coste_csikos_viennot_conjecture`:** Verbatim conjecture from `arXiv:2611.18391v1`
  (`5_details.tex`, line 47).
-/

@[expose] public section

namespace LeanForge.CosteOuterplanar

/-! ### 1. Tagged Mixed Multigraphs, Subdivision Graph, and Mixed Quotients -/

/-- A tagged mixed multigraph `M = (V, E_S, E_D, τ)` with loopless simple solid edges `solid`
and loopless tagged dashed edges indexed by `E` with tags in `T`. -/
structure TaggedMixedMultigraph (V E T : Type) where
  solid : SimpleGraph V
  e₁ : E → V
  e₂ : E → V
  loopless_dashed : ∀ e : E, e₁ e ≠ e₂ e
  tag : E → T

namespace TaggedMixedMultigraph

/-- Dashed edge `e` has unordered endpoints `{u, v}`. -/
def connects {V E T : Type} (M : TaggedMixedMultigraph V E T) (e : E) (u v : V) : Prop :=
  (M.e₁ e = u ∧ M.e₂ e = v) ∨ (M.e₁ e = v ∧ M.e₂ e = u)

lemma connects_symm {V E T : Type} (M : TaggedMixedMultigraph V E T) {e : E} {u v : V} :
    M.connects e u v → M.connects e v u := by
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩

lemma connects_comm {V E T : Type} (M : TaggedMixedMultigraph V E T) (e : E) (u v : V) :
    M.connects e u v ↔ M.connects e v u :=
  ⟨M.connects_symm, M.connects_symm⟩

lemma ne_of_connects {V E T : Type} (M : TaggedMixedMultigraph V E T) {e : E} {u v : V}
    (h : M.connects e u v) : u ≠ v := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact fun huv => M.loopless_dashed e (h1.trans (huv.trans h2.symm))
  · exact fun huv => M.loopless_dashed e (h1.trans (huv.symm.trans h2.symm))

lemma connects_unique_right {V E T : Type} (M : TaggedMixedMultigraph V E T)
    {e : E} {u v₁ v₂ : V} (h1 : M.connects e u v₁) (h2 : M.connects e u v₂) : v₁ = v₂ := by
  rcases h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases h2 with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · exact hb.symm.trans hd
  · exact absurd (ha.trans hd.symm) (M.loopless_dashed e)
  · exact absurd (hc.trans hb.symm) (M.loopless_dashed e)
  · exact ha.symm.trans hc

end TaggedMixedMultigraph

/-- The subdivision graph `G(M)` on `V ⊕ E` placing one degree-2 subdivision vertex on every
dashed edge. -/
def subdivGraph {V E T : Type} (M : TaggedMixedMultigraph V E T) : SimpleGraph (V ⊕ E) where
  Adj x y :=
    match x, y with
    | Sum.inl u, Sum.inl v => M.solid.Adj u v
    | Sum.inl u, Sum.inr e => M.e₁ e = u ∨ M.e₂ e = u
    | Sum.inr e, Sum.inl u => M.e₁ e = u ∨ M.e₂ e = u
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨fun x y h => by
    cases x <;> cases y
    · exact h.symm
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨fun x h => by
    cases x
    · exact M.solid.loopless.irrefl _ h
    · exact h⟩

/-- The underlying simple graph `M_simp` on `V` having edge `u ~ v` iff `M` has at least one solid
or dashed edge between `u` and `v`. -/
def underlyingSimple {V E T : Type} (M : TaggedMixedMultigraph V E T) : SimpleGraph V where
  Adj u v := M.solid.Adj u v ∨ ∃ e : E, M.connects e u v
  symm := ⟨fun _ _ h => by
    rcases h with h | ⟨e, he⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨e, M.connects_symm he⟩⟩
  loopless := ⟨fun u h => by
    rcases h with h | ⟨e, he⟩
    · exact M.solid.loopless.irrefl u h
    · exact M.ne_of_connects he rfl⟩

/-- `underlyingSimple M` is a minor of `subdivGraph M` by contracting each dashed vertex `e` into
its endpoint `M.e₁ e`. -/
theorem hasMinor_subdivGraph_underlyingSimple {V E T : Type} (M : TaggedMixedMultigraph V E T) :
    HasMinor (subdivGraph M) (underlyingSimple M) := by
  let φ : V ⊕ E → Option V := fun x =>
    match x with
    | Sum.inl u => some u
    | Sum.inr e => some (M.e₁ e)
  refine hasMinor_of_partialMap φ ?_ ?_
  · intro u
    have hu_mem : Sum.inl u ∈ ({x : V ⊕ E | φ x = some u} : Set (V ⊕ E)) := rfl
    have : Nonempty ({x : V ⊕ E | φ x = some u} : Set (V ⊕ E)) := ⟨⟨Sum.inl u, hu_mem⟩⟩
    refine ⟨fun x y => ?_⟩
    have hto : ∀ z : ({x : V ⊕ E | φ x = some u} : Set (V ⊕ E)),
        ((subdivGraph M).induce {x : V ⊕ E | φ x = some u}).Reachable ⟨Sum.inl u, hu_mem⟩ z := by
      intro z
      rcases hz : z.1 with v | e
      · have hv : v = u := Option.some.inj (by simpa [φ, hz] using z.2)
        have hEq : (⟨Sum.inl u, hu_mem⟩ : ({x : V ⊕ E | φ x = some u} : Set (V ⊕ E))) = z :=
          Subtype.ext (by rw [hz, hv])
        rw [hEq]
      · have he : M.e₁ e = u := Option.some.inj (by simpa [φ, hz] using z.2)
        have hadj : ((subdivGraph M).induce {x : V ⊕ E | φ x = some u}).Adj
            ⟨Sum.inl u, hu_mem⟩ z := by
          change (subdivGraph M).Adj (Sum.inl u) z.1
          rw [hz]
          exact Or.inl he
        exact hadj.reachable
    exact (hto x).symm.trans (hto y)
  · intro u v huv
    rcases huv with hsol | ⟨e, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨Sum.inl u, Sum.inl v, rfl, rfl, hsol⟩
    · exact ⟨Sum.inr e, Sum.inl v, by simp [φ, h1], rfl, Or.inr h2⟩
    · exact ⟨Sum.inl u, Sum.inr e, rfl, by simp [φ, h1], Or.inr h2⟩

/-- Number of solid edges incident to `u` with other endpoint of color `b`. -/
noncomputable def solidCountAt {V E T C : Type} (M : TaggedMixedMultigraph V E T)
    (c : V → C) (u : V) (b : C) : ℕ :=
  Set.ncard {w : V | M.solid.Adj u w ∧ c w = b}

/-- Number of tag-`t` dashed edges incident to `u` with other endpoint of color `b`. -/
noncomputable def dashedCountAt {V E T C : Type} (M : TaggedMixedMultigraph V E T)
    (c : V → C) (u : V) (b : C) (t : T) : ℕ :=
  Set.ncard {e : E | M.tag e = t ∧ ∃ w : V, M.connects e u w ∧ c w = b}

/-- A coloring `c : V → C` is *equitable* on a tagged mixed multigraph `M` if same-colored
vertices have equal solid counts and equal per-tag dashed counts to every color class. -/
def IsMixedEquitable {V E T C : Type} (M : TaggedMixedMultigraph V E T) (c : V → C) : Prop :=
  (∀ u v : V, c u = c v → ∀ b : C, solidCountAt M c u b = solidCountAt M c v b) ∧
  (∀ u v : V, c u = c v → ∀ b : C, ∀ t : T, dashedCountAt M c u b t = dashedCountAt M c v b t)

/-- Dashed edges of the tagged mixed quotient `\widehat{K}(M, c)`: unordered pairs `({a, b}, t)`
with `a ≠ b` that occur as the endpoint-colors and tag of at least one dashed edge of `M`. -/
abbrev QuotDashedEdge {V E T C : Type} (M : TaggedMixedMultigraph V E T) (c : V → C) : Type :=
  {p : Sym2 C × T // ¬ p.1.IsDiag ∧ ∃ e : E, M.tag e = p.2 ∧ s(c (M.e₁ e), c (M.e₂ e)) = p.1}

/-- Noncomputable ordered representatives of a non-diagonal unordered pair `p : Sym2 C`. -/
noncomputable def sym2Endpoints {C : Type} (p : Sym2 C) (hnd : ¬ p.IsDiag) :
    {ab : C × C // ab.1 ≠ ab.2 ∧ s(ab.1, ab.2) = p} := by
  have hex : ∃ ab : C × C, ab.1 ≠ ab.2 ∧ s(ab.1, ab.2) = p := by
    induction p using Sym2.ind with
    | _ a b =>
      refine ⟨(a, b), ?_, rfl⟩
      intro hab
      exact hnd (Sym2.mk_isDiag_iff.mpr hab)
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

/-- The tagged mixed quotient `\widehat{K}(M, c)` on color set `C`. -/
noncomputable def mixedQuotient {V E T C : Type} (M : TaggedMixedMultigraph V E T) (c : V → C) :
    TaggedMixedMultigraph C (QuotDashedEdge M c) T where
  solid := colorQuotientSimple M.solid c
  e₁ q := (sym2Endpoints q.1.1 q.2.1).1.1
  e₂ q := (sym2Endpoints q.1.1 q.2.1).1.2
  loopless_dashed q := (sym2Endpoints q.1.1 q.2.1).2.1
  tag q := q.1.2

lemma subdivGraph_mixedQuotient_adj_inl_inr {V E T C : Type}
    (M : TaggedMixedMultigraph V E T) (c : V → C) (a : C) (q : QuotDashedEdge M c) :
    (subdivGraph (mixedQuotient M c)).Adj (Sum.inl a) (Sum.inr q) ↔ a ∈ q.1.1 := by
  set ab := (sym2Endpoints q.1.1 q.2.1).1
  have hs : s(ab.1, ab.2) = q.1.1 := (sym2Endpoints q.1.1 q.2.1).2.2
  change ab.1 = a ∨ ab.2 = a ↔ a ∈ q.1.1
  rw [← hs, Sym2.mem_iff]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

lemma subdivGraph_mixedQuotient_adj_inr_inl {V E T C : Type}
    (M : TaggedMixedMultigraph V E T) (c : V → C) (q : QuotDashedEdge M c) (a : C) :
    (subdivGraph (mixedQuotient M c)).Adj (Sum.inr q) (Sum.inl a) ↔ a ∈ q.1.1 := by
  rw [SimpleGraph.adj_comm]
  exact subdivGraph_mixedQuotient_adj_inl_inr M c a q

/-- Vertices of `G(\widehat{K} - i)` inside `G(\widehat{K})`: all colors `a ≠ i` and all quotient
dashed edges not incident to `i`. -/
def delColorSet {V E T C : Type} (M : TaggedMixedMultigraph V E T) (c : V → C) (i : C) :
    Set (C ⊕ QuotDashedEdge M c) :=
  {x | match x with | Sum.inl a => a ≠ i | Sum.inr q => i ∉ q.1.1}

/-- Secondary induction measure: count of ordered solid adjacencies plus number of dashed edges. -/
noncomputable def mixedSize {V E T : Type} [Fintype E]
    (M : TaggedMixedMultigraph V E T) : ℕ :=
  Set.ncard {p : V × V | M.solid.Adj p.1 p.2} + Fintype.card E

/-- A helper showing `Set.ncard` equality from a bijection between finite sets. -/
private lemma ncard_eq_of_bij {α β : Type*} [Finite α] [Finite β]
    {S : Set α} {T : Set β} (f : α → β)
    (hf_mem : ∀ a ∈ S, f a ∈ T)
    (hf_inj : ∀ a₁ ∈ S, ∀ a₂ ∈ S, f a₁ = f a₂ → a₁ = a₂)
    (hf_surj : ∀ b ∈ T, ∃ a ∈ S, f a = b) :
    Set.ncard S = Set.ncard T :=
  Set.ncard_congr (fun a _ => f a) hf_mem
    (fun a₁ a₂ h1 h2 h => hf_inj a₁ h1 a₂ h2 h)
    (fun b hb => let ⟨a, ha, hfa⟩ := hf_surj b hb; ⟨a, ha, hfa⟩)

/-- Helper converting positive `solidCountAt` / `dashedCountAt` into an actual edge witness. -/
private lemma exists_solid_of_quot_adj {V E T C : Type} [Finite V]
    {M : TaggedMixedMultigraph V E T} {c : V → C} (heq : IsMixedEquitable M c)
    {a b : C} (hadj : (mixedQuotient M c).solid.Adj a b) {u : V} (hu : c u = a) :
    ∃ w : V, M.solid.Adj u w ∧ c w = b := by
  obtain ⟨-, u₀, v₀, hu₀, hv₀, huv₀⟩ := hadj
  have hpos : 0 < solidCountAt M c u b := by
    rw [heq.1 u u₀ (hu.trans hu₀.symm) b]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨v₀, huv₀, hv₀⟩
  exact Set.nonempty_of_ncard_ne_zero (Nat.pos_iff_ne_zero.mp hpos)

private lemma exists_dashed_of_quot_edge {V E T C : Type} [Finite E]
    {M : TaggedMixedMultigraph V E T} {c : V → C} (heq : IsMixedEquitable M c)
    {q : QuotDashedEdge M c} {a b : C} (hpair : q.1.1 = s(a, b))
    {u : V} (hu : c u = a) :
    ∃ (e : E) (w : V), M.tag e = q.1.2 ∧ M.connects e u w ∧ c w = b := by
  obtain ⟨-, e₀, htag₀, hs₀⟩ := q.2
  have hpair₀ : s(c (M.e₁ e₀), c (M.e₂ e₀)) = s(a, b) := hs₀.trans hpair
  have hcases := Sym2.eq_iff.mp hpair₀
  have hex₀ : ∃ u₀ : V, c u₀ = a ∧ ∃ w₀ : V, M.connects e₀ u₀ w₀ ∧ c w₀ = b := by
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨M.e₁ e₀, h1, M.e₂ e₀, Or.inl ⟨rfl, rfl⟩, h2⟩
    · exact ⟨M.e₂ e₀, h2, M.e₁ e₀, Or.inr ⟨rfl, rfl⟩, h1⟩
  obtain ⟨u₀, hu₀, w₀, hconn₀, hw₀⟩ := hex₀
  have hpos : 0 < dashedCountAt M c u b q.1.2 := by
    rw [heq.2 u u₀ (hu.trans hu₀.symm) b q.1.2]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨e₀, htag₀, w₀, hconn₀, hw₀⟩
  obtain ⟨e, htag, w, hconn, hw⟩ := Set.nonempty_of_ncard_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  exact ⟨e, w, htag, hconn, hw⟩

/-! ### 2. Forbidden `K_{2,3}` Configurations, 1-Sum Helper, and Degree-2 Path Contractions -/

/-- An outerplanar mixed multigraph has at most 2 parallel dashed edges between any two vertices
(3 parallel dashed edges yield a `K_{2,3}` subgraph in `subdivGraph M`). -/
private lemma card_parallel_dashed_le_two {V E T : Type} [Finite E]
    (M : TaggedMixedMultigraph V E T) (hOut : IsOuterplanar (subdivGraph M))
    {u v : V} (huv : u ≠ v) :
    Set.ncard {e : E | M.connects e u v} ≤ 2 := by
  classical
  have := Fintype.ofFinite E
  set S : Finset E := Finset.univ.filter fun e : E => M.connects e u v
  have hSeq : (S : Set E) = {e : E | M.connects e u v} := by ext e; simp [S]
  rw [← hSeq, Set.ncard_coe_finset]
  by_contra hgt
  have h3 : 3 ≤ S.card := by omega
  obtain ⟨e₁, he₁S⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hS1 : 0 < (S.erase e₁).card := by rw [Finset.card_erase_of_mem he₁S]; omega
  obtain ⟨e₂, he₂⟩ := Finset.card_pos.mp hS1
  have he₂₁ : e₂ ≠ e₁ := (Finset.mem_erase.mp he₂).1
  have he₂S : e₂ ∈ S := Finset.mem_of_mem_erase he₂
  have hS2 : 0 < ((S.erase e₁).erase e₂).card := by
    rw [Finset.card_erase_of_mem he₂, Finset.card_erase_of_mem he₁S]; omega
  obtain ⟨e₃, he₃⟩ := Finset.card_pos.mp hS2
  have he₃₂ : e₃ ≠ e₂ := (Finset.mem_erase.mp he₃).1
  have he₃₁ : e₃ ≠ e₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase he₃)).1
  have he₃S : e₃ ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he₃)
  have hc₁ : M.connects e₁ u v := (Finset.mem_filter.mp he₁S).2
  have hc₂ : M.connects e₂ u v := (Finset.mem_filter.mp he₂S).2
  have hc₃ : M.connects e₃ u v := (Finset.mem_filter.mp he₃S).2
  let f : Fin 2 ⊕ Fin 3 → V ⊕ E := fun x =>
    match x with
    | Sum.inl ⟨0, _⟩ => Sum.inl u
    | Sum.inl ⟨1, _⟩ => Sum.inl v
    | Sum.inr ⟨0, _⟩ => Sum.inr e₁
    | Sum.inr ⟨1, _⟩ => Sum.inr e₂
    | Sum.inr ⟨2, _⟩ => Sum.inr e₃
  have hK23 : HasMinor (subdivGraph M) K23 := by
    refine ⟨fun x => {f x}, ?_, ?_, ?_⟩
    · intro x
      have : Nonempty ({f x} : Set (V ⊕ E)) := ⟨⟨f x, Set.mem_singleton _⟩⟩
      refine ⟨fun a b => ?_⟩
      have hEq : a = b := Subtype.ext
        ((Set.mem_singleton_iff.mp a.2).trans (Set.mem_singleton_iff.mp b.2).symm)
      rw [hEq]
    · intro x y hxy
      dsimp only [Function.onFun]
      rw [Set.disjoint_singleton]
      intro hEq
      rcases x with i | j <;> rcases y with i' | j'
      · fin_cases i <;> fin_cases i'
        · exact hxy rfl
        · exact huv (Sum.inl.inj hEq)
        · exact huv.symm (Sum.inl.inj hEq)
        · exact hxy rfl
      · fin_cases i <;> fin_cases j' <;> simp [f] at hEq
      · fin_cases j <;> fin_cases i' <;> simp [f] at hEq
      · fin_cases j <;> fin_cases j'
        · exact hxy rfl
        · exact he₂₁.symm (Sum.inr.inj hEq)
        · exact he₃₁.symm (Sum.inr.inj hEq)
        · exact he₂₁ (Sum.inr.inj hEq)
        · exact hxy rfl
        · exact he₃₂.symm (Sum.inr.inj hEq)
        · exact he₃₁ (Sum.inr.inj hEq)
        · exact he₃₂ (Sum.inr.inj hEq)
        · exact hxy rfl
    · intro x y hxy
      refine ⟨f x, Set.mem_singleton _, f y, Set.mem_singleton _, ?_⟩
      rcases x with i | j <;> rcases y with i' | j'
      · simp [K23] at hxy
      · fin_cases i <;> fin_cases j'
        · exact hc₁.imp And.left And.right
        · exact hc₂.imp And.left And.right
        · exact hc₃.imp And.left And.right
        · exact (M.connects_symm hc₁).imp And.left And.right
        · exact (M.connects_symm hc₂).imp And.left And.right
        · exact (M.connects_symm hc₃).imp And.left And.right
      · fin_cases j <;> fin_cases i'
        · exact hc₁.imp And.left And.right
        · exact (M.connects_symm hc₁).imp And.left And.right
        · exact hc₂.imp And.left And.right
        · exact (M.connects_symm hc₂).imp And.left And.right
        · exact hc₃.imp And.left And.right
        · exact (M.connects_symm hc₃).imp And.left And.right
      · simp [K23] at hxy
  exact hOut.2 hK23

/-- Lifting a walk in `underlyingSimple M` avoiding `{v, a}` into a connected vertex subset of
`subdivGraph M` containing both endpoints and avoiding `Sum.inl v`, `Sum.inl a`, and any dashed
edge incident to `v`. -/
private lemma lift_walk_subdiv {V E T : Type} (M : TaggedMixedMultigraph V E T) {v a : V}
    {x y : V} (P : (underlyingSimple M).Walk x y)
    (hP : ∀ w ∈ P.support, w ≠ v ∧ w ≠ a) :
    ∃ S : Set (V ⊕ E),
      Sum.inl x ∈ S ∧ Sum.inl y ∈ S ∧
      ((subdivGraph M).induce S).Connected ∧
      (∀ w : V, Sum.inl w ∈ S → w ≠ v ∧ w ≠ a) ∧
      (∀ e : E, Sum.inr e ∈ S → M.e₁ e ≠ v ∧ M.e₂ e ≠ v) := by
  induction P with
  | @nil x =>
    refine ⟨{Sum.inl x}, Set.mem_singleton _, Set.mem_singleton _, ?_, ?_, ?_⟩
    · have : Nonempty ({Sum.inl x} : Set (V ⊕ E)) := ⟨⟨Sum.inl x, Set.mem_singleton _⟩⟩
      refine ⟨fun p q => ?_⟩
      have hEq : p = q := Subtype.ext
        ((Set.mem_singleton_iff.mp p.2).trans (Set.mem_singleton_iff.mp q.2).symm)
      rw [hEq]
    · intro w hw
      have hwx : w = x := Sum.inl.inj (Set.mem_singleton_iff.mp hw)
      exact hwx ▸ hP x (by simp)
    · intro e he
      simp at he
  | @cons x y z hxy Q ih =>
    have hx_va : x ≠ v ∧ x ≠ a := hP x (by simp)
    have hy_va : y ≠ v ∧ y ≠ a := hP y (by simp)
    have hQ : ∀ w ∈ Q.support, w ≠ v ∧ w ≠ a := fun w hw => hP w (by simp [hw])
    obtain ⟨S, hyS, hzS, hSconn, hSinl, hSinr⟩ := ih hQ
    rcases hxy with hsol | ⟨e, he⟩
    · refine ⟨insert (Sum.inl x) S, Set.mem_insert _ _, Set.mem_insert_of_mem _ hzS,
        induce_connected_insert hSconn ⟨Sum.inl y, hyS, hsol⟩, ?_, ?_⟩
      · intro w hw
        rcases Set.mem_insert_iff.mp hw with hEq | hwS
        · exact Sum.inl.inj hEq ▸ hx_va
        · exact hSinl w hwS
      · intro e heS
        rcases Set.mem_insert_iff.mp heS with hEq | heS'
        · exact False.elim (by simp at hEq)
        · exact hSinr e heS'
    · have hxe : (subdivGraph M).Adj (Sum.inl x) (Sum.inr e) := by
        rcases he with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact Or.inl h1
        · exact Or.inr h2
      have hye : (subdivGraph M).Adj (Sum.inr e) (Sum.inl y) := by
        rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Or.inr h2
        · exact Or.inl h1
      have he_nv : M.e₁ e ≠ v ∧ M.e₂ e ≠ v := by
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1.symm ▸ hx_va.1, h2.symm ▸ hy_va.1⟩
        · exact ⟨h1.symm ▸ hy_va.1, h2.symm ▸ hx_va.1⟩
      have hS1 : ((subdivGraph M).induce (insert (Sum.inr e) S)).Connected :=
        induce_connected_insert hSconn ⟨Sum.inl y, hyS, hye⟩
      have hS2 : ((subdivGraph M).induce (insert (Sum.inl x) (insert (Sum.inr e) S))).Connected :=
        induce_connected_insert hS1 ⟨Sum.inr e, Set.mem_insert _ _, hxe⟩
      refine ⟨insert (Sum.inl x) (insert (Sum.inr e) S), Set.mem_insert _ _,
        Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hzS), hS2, ?_, ?_⟩
      · intro w hw
        rcases Set.mem_insert_iff.mp hw with hEq | hw1
        · exact Sum.inl.inj hEq ▸ hx_va
        · rcases Set.mem_insert_iff.mp hw1 with hEq | hwS
          · exact False.elim (by simp at hEq)
          · exact hSinl w hwS
      · intro e' he'
        rcases Set.mem_insert_iff.mp he' with hEq | he1
        · exact False.elim (by simp at hEq)
        · rcases Set.mem_insert_iff.mp he1 with hEq | heS'
          · exact Sum.inr.inj hEq ▸ he_nv
          · exact hSinr e' heS'

/-- If `v` has neighbor `b ≠ a` in `underlyingSimple M` and there is a `b`-`a` walk in
`underlyingSimple M` avoiding `v`, then `M` has at most 1 dashed edge connecting `v` and `a`
(otherwise `subdivGraph M` has a `K_{2,3}` minor). -/
private lemma dashed_unique_of_alt_walk {V E T : Type} (M : TaggedMixedMultigraph V E T)
    (hOut : IsOuterplanar (subdivGraph M)) {v a b : V}
    (hva : v ≠ a) (_hvb : v ≠ b) (hba : b ≠ a)
    (hvb_adj : (underlyingSimple M).Adj v b)
    (P : (underlyingSimple M).Walk b a) (hP : ∀ w ∈ P.support, w ≠ v)
    {e₁ e₂ : E} (he₁ : M.connects e₁ v a) (he₂ : M.connects e₂ v a) : e₁ = e₂ := by
  by_contra hne
  -- Take prefix of `P` up to first arrival at `a`.
  obtain ⟨a', a'', P₁, _, ha'ne, ha''eq, ha'a'', hP₁ne, hP₁sub, -, -⟩ :=
    walk_first_exit (A := {w : V | w ≠ a}) P hba (fun h => h rfl)
  have ha''_is_a : a'' = a := by
    by_contra h
    exact ha''eq h
  have ha'a : (underlyingSimple M).Adj a' a := ha''_is_a ▸ ha'a''
  have hP₁_va : ∀ w ∈ P₁.support, w ≠ v ∧ w ≠ a :=
    fun w hw => ⟨hP w (hP₁sub w hw), hP₁ne w hw⟩
  obtain ⟨S₀, hbS₀, ha'S₀, hS₀conn, hS₀inl, hS₀inr⟩ := lift_walk_subdiv M P₁ hP₁_va
  -- Extend `S₀` if needed so it is adjacent to `Sum.inl a`.
  have hstep_a : ∃ S₁ : Set (V ⊕ E),
      S₀ ⊆ S₁ ∧ ((subdivGraph M).induce S₁).Connected ∧
      (∃ x ∈ S₁, (subdivGraph M).Adj x (Sum.inl a)) ∧
      Sum.inl v ∉ S₁ ∧ Sum.inl a ∉ S₁ ∧ Sum.inr e₁ ∉ S₁ ∧ Sum.inr e₂ ∉ S₁ := by
    have hS₀_nv : Sum.inl v ∉ S₀ := fun h => (hS₀inl v h).1 rfl
    have hS₀_na : Sum.inl a ∉ S₀ := fun h => (hS₀inl a h).2 rfl
    have hS₀_ne1 : Sum.inr e₁ ∉ S₀ := fun h => by
      have ⟨h1, h2⟩ := hS₀inr e₁ h
      rcases he₁ with ⟨ha1, _⟩ | ⟨_, ha2⟩
      · exact h1 ha1
      · exact h2 ha2
    have hS₀_ne2 : Sum.inr e₂ ∉ S₀ := fun h => by
      have ⟨h1, h2⟩ := hS₀inr e₂ h
      rcases he₂ with ⟨ha1, _⟩ | ⟨_, ha2⟩
      · exact h1 ha1
      · exact h2 ha2
    rcases ha'a with hsol | ⟨e', he'⟩
    · exact ⟨S₀, Set.Subset.rfl, hS₀conn, ⟨Sum.inl a', ha'S₀, hsol⟩,
        hS₀_nv, hS₀_na, hS₀_ne1, hS₀_ne2⟩
    · have ha'_nv : a' ≠ v := (hS₀inl a' ha'S₀).1
      have he'_ne1 : e' ≠ e₁ := fun hEq => by
        subst hEq
        rcases he' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases he₁ with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · exact ha'_nv (h1.symm.trans k1)
        · exact hva.symm (h2.symm.trans k2)
        · exact hva.symm (h1.symm.trans k1)
        · exact ha'_nv (h2.symm.trans k2)
      have he'_ne2 : e' ≠ e₂ := fun hEq => by
        subst hEq
        rcases he' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases he₂ with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · exact ha'_nv (h1.symm.trans k1)
        · exact hva.symm (h2.symm.trans k2)
        · exact hva.symm (h1.symm.trans k1)
        · exact ha'_nv (h2.symm.trans k2)
      have he'_a' : (subdivGraph M).Adj (Sum.inr e') (Sum.inl a') :=
        he'.imp And.left And.right
      have he'_a : (subdivGraph M).Adj (Sum.inr e') (Sum.inl a) :=
        (M.connects_symm he').imp And.left And.right
      refine ⟨insert (Sum.inr e') S₀, Set.subset_insert _ _,
        induce_connected_insert hS₀conn ⟨Sum.inl a', ha'S₀, he'_a'⟩,
        ⟨Sum.inr e', Set.mem_insert _ _, he'_a⟩, ?_, ?_, ?_, ?_⟩
      · intro h; rcases Set.mem_insert_iff.mp h with hEq | h0
        · simp at hEq
        · exact hS₀_nv h0
      · intro h; rcases Set.mem_insert_iff.mp h with hEq | h0
        · simp at hEq
        · exact hS₀_na h0
      · intro h; rcases Set.mem_insert_iff.mp h with hEq | h0
        · exact he'_ne1 (Sum.inr.inj hEq).symm
        · exact hS₀_ne1 h0
      · intro h; rcases Set.mem_insert_iff.mp h with hEq | h0
        · exact he'_ne2 (Sum.inr.inj hEq).symm
        · exact hS₀_ne2 h0
  obtain ⟨S₁, hS₀₁, hS₁conn, ⟨xa, hxaS₁, hxa_adj⟩, hS₁_nv, hS₁_na, hS₁_ne1, hS₁_ne2⟩ := hstep_a
  -- Extend `S₁` if needed so it is also adjacent to `Sum.inl v`.
  have hstep_v : ∃ S₂ : Set (V ⊕ E),
      ((subdivGraph M).induce S₂).Connected ∧
      (∃ x ∈ S₂, (subdivGraph M).Adj x (Sum.inl v)) ∧
      (∃ x ∈ S₂, (subdivGraph M).Adj x (Sum.inl a)) ∧
      Sum.inl v ∉ S₂ ∧ Sum.inl a ∉ S₂ ∧ Sum.inr e₁ ∉ S₂ ∧ Sum.inr e₂ ∉ S₂ := by
    have hbS₁ : Sum.inl b ∈ S₁ := hS₀₁ hbS₀
    rcases hvb_adj with hsol | ⟨e'', he''⟩
    · exact ⟨S₁, hS₁conn, ⟨Sum.inl b, hbS₁, hsol.symm⟩, ⟨xa, hxaS₁, hxa_adj⟩,
        hS₁_nv, hS₁_na, hS₁_ne1, hS₁_ne2⟩
    · have he''_ne1 : e'' ≠ e₁ := fun hEq => by
        subst hEq
        exact hba (M.connects_unique_right he'' he₁)
      have he''_ne2 : e'' ≠ e₂ := fun hEq => by
        subst hEq
        exact hba (M.connects_unique_right he'' he₂)
      have he''_b : (subdivGraph M).Adj (Sum.inr e'') (Sum.inl b) :=
        (M.connects_symm he'').imp And.left And.right
      have he''_v : (subdivGraph M).Adj (Sum.inr e'') (Sum.inl v) :=
        he''.imp And.left And.right
      refine ⟨insert (Sum.inr e'') S₁,
        induce_connected_insert hS₁conn ⟨Sum.inl b, hbS₁, he''_b⟩,
        ⟨Sum.inr e'', Set.mem_insert _ _, he''_v⟩,
        ⟨xa, Set.mem_insert_of_mem _ hxaS₁, hxa_adj⟩, ?_, ?_, ?_, ?_⟩
      · intro h; rcases Set.mem_insert_iff.mp h with hEq | h1
        · simp at hEq
        · exact hS₁_nv h1
      · intro h; rcases Set.mem_insert_iff.mp h with hEq | h1
        · simp at hEq
        · exact hS₁_na h1
      · intro h; rcases Set.mem_insert_iff.mp h with hEq | h1
        · exact he''_ne1 (Sum.inr.inj hEq).symm
        · exact hS₁_ne1 h1
      · intro h; rcases Set.mem_insert_iff.mp h with hEq | h1
        · exact he''_ne2 (Sum.inr.inj hEq).symm
        · exact hS₁_ne2 h1
  obtain ⟨S₂, hS₂conn, ⟨xv, hxvS₂, hxv_adj⟩, ⟨xa', hxa'S₂, hxa'_adj⟩,
    hS₂_nv, hS₂_na, hS₂_ne1, hS₂_ne2⟩ := hstep_v
  -- Build a `K_{2,3}` minor model in `subdivGraph M`.
  let B : Fin 2 ⊕ Fin 3 → Set (V ⊕ E) := fun x =>
    match x with
    | Sum.inl ⟨0, _⟩ => {Sum.inl v}
    | Sum.inl ⟨1, _⟩ => {Sum.inl a}
    | Sum.inr ⟨0, _⟩ => {Sum.inr e₁}
    | Sum.inr ⟨1, _⟩ => {Sum.inr e₂}
    | Sum.inr ⟨2, _⟩ => S₂
  have hsing_conn : ∀ z : V ⊕ E, ((subdivGraph M).induce ({z} : Set (V ⊕ E))).Connected := by
    intro z
    have : Nonempty ({z} : Set (V ⊕ E)) := ⟨⟨z, Set.mem_singleton z⟩⟩
    refine ⟨fun p q => ?_⟩
    have hEq : p = q := Subtype.ext
      ((Set.mem_singleton_iff.mp p.2).trans (Set.mem_singleton_iff.mp q.2).symm)
    rw [hEq]
  have hK23 : HasMinor (subdivGraph M) K23 := by
    refine ⟨B, ?_, ?_, ?_⟩
    · intro x
      rcases x with i | j
      · fin_cases i <;> exact hsing_conn _
      · fin_cases j
        · exact hsing_conn _
        · exact hsing_conn _
        · exact hS₂conn
    · intro x y hxy
      dsimp only [Function.onFun]
      rcases x with i | j <;> rcases y with i' | j'
      · fin_cases i <;> fin_cases i'
        · exact absurd rfl hxy
        · exact Set.disjoint_singleton.mpr (fun h => hva (Sum.inl.inj h))
        · exact Set.disjoint_singleton.mpr (fun h => hva.symm (Sum.inl.inj h))
        · exact absurd rfl hxy
      · fin_cases i <;> fin_cases j'
        · exact Set.disjoint_singleton.mpr (by simp)
        · exact Set.disjoint_singleton.mpr (by simp)
        · exact Set.disjoint_singleton_left.mpr hS₂_nv
        · exact Set.disjoint_singleton.mpr (by simp)
        · exact Set.disjoint_singleton.mpr (by simp)
        · exact Set.disjoint_singleton_left.mpr hS₂_na
      · fin_cases j <;> fin_cases i'
        · exact Set.disjoint_singleton.mpr (by simp)
        · exact Set.disjoint_singleton.mpr (by simp)
        · exact Set.disjoint_singleton.mpr (by simp)
        · exact Set.disjoint_singleton.mpr (by simp)
        · exact Set.disjoint_singleton_right.mpr hS₂_nv
        · exact Set.disjoint_singleton_right.mpr hS₂_na
      · fin_cases j <;> fin_cases j'
        · exact absurd rfl hxy
        · exact Set.disjoint_singleton.mpr (fun h => hne (Sum.inr.inj h))
        · exact Set.disjoint_singleton_left.mpr hS₂_ne1
        · exact Set.disjoint_singleton.mpr (fun h => hne (Sum.inr.inj h).symm)
        · exact absurd rfl hxy
        · exact Set.disjoint_singleton_left.mpr hS₂_ne2
        · exact Set.disjoint_singleton_right.mpr hS₂_ne1
        · exact Set.disjoint_singleton_right.mpr hS₂_ne2
        · exact absurd rfl hxy
    · intro x y hxy
      rcases x with i | j <;> rcases y with i' | j'
      · simp [K23] at hxy
      · fin_cases i <;> fin_cases j'
        · exact ⟨Sum.inl v, Set.mem_singleton _, Sum.inr e₁, Set.mem_singleton _,
            he₁.imp And.left And.right⟩
        · exact ⟨Sum.inl v, Set.mem_singleton _, Sum.inr e₂, Set.mem_singleton _,
            he₂.imp And.left And.right⟩
        · exact ⟨Sum.inl v, Set.mem_singleton _, xv, hxvS₂, hxv_adj.symm⟩
        · exact ⟨Sum.inl a, Set.mem_singleton _, Sum.inr e₁, Set.mem_singleton _,
            (M.connects_symm he₁).imp And.left And.right⟩
        · exact ⟨Sum.inl a, Set.mem_singleton _, Sum.inr e₂, Set.mem_singleton _,
            (M.connects_symm he₂).imp And.left And.right⟩
        · exact ⟨Sum.inl a, Set.mem_singleton _, xa', hxa'S₂, hxa'_adj.symm⟩
      · fin_cases j <;> fin_cases i'
        · exact ⟨Sum.inr e₁, Set.mem_singleton _, Sum.inl v, Set.mem_singleton _,
            he₁.imp And.left And.right⟩
        · exact ⟨Sum.inr e₁, Set.mem_singleton _, Sum.inl a, Set.mem_singleton _,
            (M.connects_symm he₁).imp And.left And.right⟩
        · exact ⟨Sum.inr e₂, Set.mem_singleton _, Sum.inl v, Set.mem_singleton _,
            he₂.imp And.left And.right⟩
        · exact ⟨Sum.inr e₂, Set.mem_singleton _, Sum.inl a, Set.mem_singleton _,
            (M.connects_symm he₂).imp And.left And.right⟩
        · exact ⟨xv, hxvS₂, Sum.inl v, Set.mem_singleton _, hxv_adj⟩
        · exact ⟨xa', hxa'S₂, Sum.inl a, Set.mem_singleton _, hxa'_adj⟩
      · simp [K23] at hxy
  exact hOut.2 hK23

/-- Shared 1-sum outerplanarity lemma for Case 3A and Subcase 3B(i): if color `i` only connects
to color `j ≠ i` in `mixedQuotient M c`, has at most 2 quotient dashed edges to `j`, and
`G(\widehat{K} - i)` is outerplanar, then `G(\widehat{K})` is outerplanar. -/
private lemma one_sum_two_color_isOuterplanar {V E T C : Type}
    [Finite C] [Finite T]
    (M : TaggedMixedMultigraph V E T) (c : V → C) {i j : C} (hij : i ≠ j)
    (hsol_only : ∀ b : C, (mixedQuotient M c).solid.Adj i b → b = j)
    (hdash_only : ∀ q : QuotDashedEdge M c, i ∈ q.1.1 → q.1.1 = s(i, j))
    (hcard_le : Set.ncard {q : QuotDashedEdge M c | q.1.1 = s(i, j)} ≤ 2)
    (hdel : IsOuterplanar ((subdivGraph (mixedQuotient M c)).induce (delColorSet M c i))) :
    IsOuterplanar (subdivGraph (mixedQuotient M c)) := by
  classical
  have := Fintype.ofFinite C
  have := Fintype.ofFinite T
  have : Fintype (QuotDashedEdge M c) := Fintype.ofFinite _
  let GK := subdivGraph (mixedQuotient M c)
  let Qij : Finset (QuotDashedEdge M c) := Finset.univ.filter fun q => q.1.1 = s(i, j)
  have hQij_le : Qij.card ≤ 2 := by
    have hQeq : (Qij : Set (QuotDashedEdge M c)) = {q | q.1.1 = s(i, j)} := by ext q; simp [Qij]
    rwa [← hQeq, Set.ncard_coe_finset] at hcard_le
  let V₁fin : Finset (C ⊕ QuotDashedEdge M c) :=
    insert (Sum.inl i) (insert (Sum.inl j) (Qij.image Sum.inr))
  let V₁ : Set (C ⊕ QuotDashedEdge M c) := (V₁fin : Set (C ⊕ QuotDashedEdge M c))
  let V₂ : Set (C ⊕ QuotDashedEdge M c) := delColorSet M c i
  have hmemV₁ : ∀ x : C ⊕ QuotDashedEdge M c,
      x ∈ V₁ ↔ x = Sum.inl i ∨ x = Sum.inl j ∨ ∃ q : QuotDashedEdge M c, q.1.1 = s(i, j) ∧
        x = Sum.inr q := by
    intro x
    simp only [V₁, V₁fin, Qij, Finset.mem_coe, Finset.mem_insert, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h | ⟨q, hq, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)
    · rintro (h | h | ⟨q, hq, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)
  have hunion : V₁ ∪ V₂ = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    rcases x with a | q
    · by_cases hai : a = i
      · left; exact (hmemV₁ _).mpr (Or.inl (congrArg Sum.inl hai))
      · right; exact hai
    · by_cases hiq : i ∈ q.1.1
      · left; exact (hmemV₁ _).mpr (Or.inr (Or.inr ⟨q, hdash_only q hiq, rfl⟩))
      · right; exact hiq
  have hinter : V₁ ∩ V₂ = {Sum.inl j} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx1, hx2⟩
      rcases (hmemV₁ x).mp hx1 with rfl | rfl | ⟨q, hq, rfl⟩
      · exact absurd rfl hx2
      · rfl
      · exact absurd (hq ▸ Sym2.mem_mk_left i j) hx2
    · rintro rfl
      exact ⟨(hmemV₁ _).mpr (Or.inr (Or.inl rfl)), hij.symm⟩
  have hno : ∀ x ∈ V₁, ∀ y ∈ V₂, x ≠ Sum.inl j → y ≠ Sum.inl j → ¬ GK.Adj x y := by
    intro x hx1 y hy2 hxj hyj hxy
    rcases (hmemV₁ x).mp hx1 with rfl | rfl | ⟨q, hq, rfl⟩
    · rcases y with b | q'
      · have hbj : b = j := hsol_only b hxy
        exact hyj (congrArg Sum.inl hbj)
      · have hiq' : i ∈ q'.1.1 := (subdivGraph_mixedQuotient_adj_inl_inr M c i q').mp hxy
        exact hy2 hiq'
    · exact hxj rfl
    · rcases y with b | q'
      · have hbq : b ∈ q.1.1 := (subdivGraph_mixedQuotient_adj_inr_inl M c q b).mp hxy
        rw [hq, Sym2.mem_iff] at hbq
        rcases hbq with rfl | rfl
        · exact hy2 rfl
        · exact hyj rfl
      · exact hxy
  have hV₁_out : IsOuterplanar (GK.induce V₁) := by
    have hcard_V₁ : Fintype.card V₁ = 2 + Qij.card := by
      have hi_not : Sum.inl i ∉ insert (Sum.inl j) (Qij.image Sum.inr) := by
        simp only [Finset.mem_insert, Finset.mem_image, not_or]
        exact ⟨fun h => hij (Sum.inl.inj h), fun ⟨_, _, h⟩ => by simp at h⟩
      have hj_not : Sum.inl j ∉ Qij.image Sum.inr := by
        simp only [Finset.mem_image]
        rintro ⟨_, _, h⟩; simp at h
      have hcard_fin : V₁fin.card = 2 + Qij.card := by
        rw [Finset.card_insert_of_notMem hi_not, Finset.card_insert_of_notMem hj_not,
          Finset.card_image_of_injective _ Sum.inr_injective]
        omega
      simpa [V₁, Fintype.card_coe] using hcard_fin
    by_cases hQ2 : Qij.card = 2
    · obtain ⟨q₁, q₂, hq₁₂, hQeq⟩ := Finset.card_eq_two.mp hQ2
      have hq₁_mem : Sum.inr q₁ ∈ V₁ := by
        refine (hmemV₁ _).mpr (Or.inr (Or.inr ⟨q₁, ?_, rfl⟩))
        have h1 : q₁ ∈ Qij := by rw [hQeq]; exact Finset.mem_insert_self q₁ {q₂}
        exact (Finset.mem_filter.mp h1).2
      have hq₂_mem : Sum.inr q₂ ∈ V₁ := by
        refine (hmemV₁ _).mpr (Or.inr (Or.inr ⟨q₂, ?_, rfl⟩))
        have h2 : q₂ ∈ Qij := by rw [hQeq]; simp
        exact (Finset.mem_filter.mp h2).2
      exact isOuterplanar_of_card_eq_four_of_not_adj (GK.induce V₁) (by omega)
        (x := ⟨Sum.inr q₁, hq₁_mem⟩) (y := ⟨Sum.inr q₂, hq₂_mem⟩)
        (fun h => hq₁₂ (Sum.inr.inj (congrArg Subtype.val h))) (fun hadj => hadj)
    · exact isOuterplanar_of_card_le_three (GK.induce V₁) (by omega)
  exact isOuterplanar_of_one_sum hunion hinter hno hV₁_out hdel

/-- Helper for Subcase 3B(ii) ($L = 4$): contracting a 3-vertex internal degree-2 chain
`u — a — b — c — w` (`u ≠ w`) down to a single degree-2 vertex `a` adjacent to `u, w` preserves
outerplanarity backward (two applications of Lemma 4). -/
private lemma isOuterplanar_of_deg2_chain4 {V W : Type*} {X : SimpleGraph V} {Y : SimpleGraph W}
    {a b c u w : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (huw : u ≠ w) (hua : u ≠ a) (hub : u ≠ b) (huc : u ≠ c)
    (hwa : w ≠ a) (hwb : w ≠ b) (_hwc : w ≠ c)
    (ha_adj : ∀ z : V, X.Adj a z ↔ z = u ∨ z = b)
    (hb_adj : ∀ z : V, X.Adj b z ↔ z = a ∨ z = c)
    (hc_adj : ∀ z : V, X.Adj c z ↔ z = b ∨ z = w)
    (e : contractEdgeGraph (contractEdgeGraph X a b c hac) ⟨a, hab⟩ ⟨c, hbc.symm⟩
      ⟨w, hwb⟩ (fun h => hwa.symm (congrArg Subtype.val h)) ≃g Y)
    (hY : IsOuterplanar Y) : IsOuterplanar X := by
  let X₁ := contractEdgeGraph X a b c hac
  let a₁ : {v : V // v ≠ b} := ⟨a, hab⟩
  let c₁ : {v : V // v ≠ b} := ⟨c, hbc.symm⟩
  let u₁ : {v : V // v ≠ b} := ⟨u, hub⟩
  let w₁ : {v : V // v ≠ b} := ⟨w, hwb⟩
  have hX₂_out : IsOuterplanar (contractEdgeGraph X₁ a₁ c₁ w₁
      (fun h => hwa.symm (congrArg Subtype.val h))) :=
    (isOuterplanar_iff_of_iso e).mpr hY
  have huw₁ : u₁ ≠ w₁ := fun h => huw (congrArg Subtype.val h)
  have huc₁ : u₁ ≠ c₁ := fun h => huc (congrArg Subtype.val h)
  have hwa₁ : w₁ ≠ a₁ := fun h => hwa (congrArg Subtype.val h)
  have ha₁_adj : ∀ z : {v : V // v ≠ b}, X₁.Adj a₁ z ↔ z = u₁ ∨ z = c₁ := by
    intro z
    constructor
    · rintro (hX | ⟨_, hzc⟩ | ⟨hac', _⟩)
      · rcases (ha_adj z.1).mp hX with rfl | hzb
        · exact Or.inl (Subtype.ext rfl)
        · exact absurd hzb z.2
      · exact Or.inr (Subtype.ext hzc)
      · exact absurd hac' hac
    · rintro (rfl | rfl)
      · exact Or.inl ((ha_adj u).mpr (Or.inl rfl))
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  have hc₁_adj : ∀ z : {v : V // v ≠ b}, X₁.Adj c₁ z ↔ z = a₁ ∨ z = w₁ := by
    intro z
    constructor
    · rintro (hX | ⟨hca, _⟩ | ⟨_, hza⟩)
      · rcases (hc_adj z.1).mp hX with hzb | hzw
        · exact absurd hzb z.2
        · exact Or.inr (Subtype.ext hzw)
      · exact absurd hca hac.symm
      · exact Or.inl (Subtype.ext hza)
    · rintro (rfl | rfl)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inl ((hc_adj w).mpr (Or.inr rfl))
  have hX₁_out : IsOuterplanar X₁ :=
    isOuterplanar_of_contract_adj_deg2 huw₁ huc₁ hwa₁ ha₁_adj hc₁_adj hX₂_out
  exact isOuterplanar_of_contract_adj_deg2 huc hub hac.symm ha_adj hb_adj hX₁_out

/-! ### 3. Reduction Lemmas for Theorem 1 (M1–M3 and Subcase 3B(ii)) -/

/-- Deleting all monochromatic solid edges strictly reduces `mixedSize` (when any exists),
preserves outerplanarity of `subdivGraph` and equitability, and leaves the quotient unchanged. -/
private lemma delMonoSolid_step {V E T C : Type} [Finite V] [Fintype E]
    (M : TaggedMixedMultigraph V E T) (c : V → C)
    (hOut : IsOuterplanar (subdivGraph M)) (heq : IsMixedEquitable M c)
    (hmono : ∃ u v : V, M.solid.Adj u v ∧ c u = c v) :
    ∃ M' : TaggedMixedMultigraph V E T,
      mixedSize M' < mixedSize M ∧
      IsOuterplanar (subdivGraph M') ∧
      IsMixedEquitable M' c ∧
      Nonempty (subdivGraph (mixedQuotient M' c) ≃g subdivGraph (mixedQuotient M c)) := by
  classical
  let M' : TaggedMixedMultigraph V E T :=
    { solid :=
        { Adj u v := M.solid.Adj u v ∧ c u ≠ c v
          symm := ⟨fun _ _ ⟨h, hne⟩ => ⟨h.symm, hne.symm⟩⟩
          loopless := ⟨fun u ⟨h, _⟩ => M.solid.loopless.irrefl u h⟩ }
      e₁ := M.e₁
      e₂ := M.e₂
      loopless_dashed := M.loopless_dashed
      tag := M.tag }
  have hle : subdivGraph M' ≤ subdivGraph M := by
    intro x y hxy
    cases x <;> cases y
    · exact hxy.1
    · exact hxy
    · exact hxy
    · exact hxy
  have hlt : mixedSize M' < mixedSize M := by
    unfold mixedSize
    obtain ⟨u₀, v₀, huv₀, hcu₀⟩ := hmono
    have hssub : {p : V × V | M'.solid.Adj p.1 p.2} ⊂ {p : V × V | M.solid.Adj p.1 p.2} := by
      refine Set.ssubset_iff_subset_ne.mpr ⟨fun _ hp => hp.1, fun hEq => ?_⟩
      have hmem : (u₀, v₀) ∈ {p : V × V | M'.solid.Adj p.1 p.2} := by rw [hEq]; exact huv₀
      exact hmem.2 hcu₀
    have hcard := Set.ncard_lt_ncard hssub (Set.toFinite _)
    omega
  have heq' : IsMixedEquitable M' c := by
    refine ⟨fun u v huv b => ?_, heq.2⟩
    by_cases hcb : c u = b
    · have h1 : {w : V | M'.solid.Adj u w ∧ c w = b} = ∅ := by
        ext w; simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hne⟩, hwb⟩; exact hne (hcb.trans hwb.symm)
      have h2 : {w : V | M'.solid.Adj v w ∧ c w = b} = ∅ := by
        ext w; simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hne⟩, hwb⟩; exact hne (huv.symm.trans (hcb.trans hwb.symm))
      simp [solidCountAt, h1, h2]
    · have h1 : {w : V | M'.solid.Adj u w ∧ c w = b} = {w : V | M.solid.Adj u w ∧ c w = b} := by
        ext w; exact ⟨fun ⟨⟨h, _⟩, hw⟩ => ⟨h, hw⟩,
          fun ⟨h, hw⟩ => ⟨⟨h, fun hEq => hcb (hEq.trans hw)⟩, hw⟩⟩
      have h2 : {w : V | M'.solid.Adj v w ∧ c w = b} = {w : V | M.solid.Adj v w ∧ c w = b} := by
        ext w; exact ⟨fun ⟨⟨h, _⟩, hw⟩ => ⟨h, hw⟩,
          fun ⟨h, hw⟩ => ⟨⟨h, fun hEq => hcb (huv.trans (hEq.trans hw))⟩, hw⟩⟩
      simpa [solidCountAt, h1, h2] using heq.1 u v huv b
  have hiso : subdivGraph (mixedQuotient M' c) ≃g subdivGraph (mixedQuotient M c) :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := by
        intro x y
        rcases x with a | q <;> rcases y with b | q'
        · constructor
          · rintro ⟨hab, u, v, hu, hv, huv⟩; exact ⟨hab, u, v, hu, hv, huv, by rwa [hu, hv]⟩
          · rintro ⟨hab, u, v, hu, hv, huv, _⟩; exact ⟨hab, u, v, hu, hv, huv⟩
        · exact Iff.rfl
        · exact Iff.rfl
        · exact Iff.rfl }
  exact ⟨M', hlt, isOuterplanar_of_le hOut hle, heq', ⟨hiso⟩⟩

/-- Deleting all monochromatic dashed edges strictly reduces `mixedSize` (when any exists),
preserves outerplanarity of `subdivGraph` and equitability, and leaves the quotient isomorphic. -/
private lemma delMonoDashed_step {V E T C : Type} [Finite V] [Fintype E]
    (M : TaggedMixedMultigraph V E T) (c : V → C)
    (hOut : IsOuterplanar (subdivGraph M)) (heq : IsMixedEquitable M c)
    (hmono : ∃ e : E, c (M.e₁ e) = c (M.e₂ e)) :
    ∃ (E' : Type) (_ : Fintype E') (M' : TaggedMixedMultigraph V E' T),
      mixedSize M' < mixedSize M ∧
      IsOuterplanar (subdivGraph M') ∧
      IsMixedEquitable M' c ∧
      Nonempty (subdivGraph (mixedQuotient M' c) ≃g subdivGraph (mixedQuotient M c)) := by
  classical
  let E' : Type := {e : E // c (M.e₁ e) ≠ c (M.e₂ e)}
  let M' : TaggedMixedMultigraph V E' T :=
    { solid := M.solid
      e₁ e := M.e₁ e.1
      e₂ e := M.e₂ e.1
      loopless_dashed e := M.loopless_dashed e.1
      tag e := M.tag e.1 }
  have hlt : mixedSize M' < mixedSize M := by
    unfold mixedSize
    dsimp only [M']
    obtain ⟨e₀, he₀⟩ := hmono
    have hcardE : Fintype.card E' < Fintype.card E := by
      have hssub : (Finset.univ.filter fun e : E => c (M.e₁ e) ≠ c (M.e₂ e)) ⊂ Finset.univ := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun hEq => ?_⟩
        have hmem : e₀ ∈ Finset.univ.filter fun e : E => c (M.e₁ e) ≠ c (M.e₂ e) := by
          rw [hEq]; exact Finset.mem_univ e₀
        exact (Finset.mem_filter.mp hmem).2 he₀
      have h1 := Finset.card_lt_card hssub
      simpa [E', Fintype.card_subtype] using h1
    omega
  have hemb : subdivGraph M' ↪g subdivGraph M :=
    { toFun := Sum.map id Subtype.val
      inj' := by
        intro x y h
        rcases x with u | e <;> rcases y with v | e'
        · exact congrArg Sum.inl (Sum.inl.inj h)
        · simp at h
        · simp at h
        · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))
      map_rel_iff' := by
        intro x y
        rcases x with u | e <;> rcases y with v | e' <;> exact Iff.rfl }
  have heq' : IsMixedEquitable M' c := by
    refine ⟨heq.1, fun u v huv b t => ?_⟩
    by_cases hcb : c u = b
    · have h1 : {e : E' | M'.tag e = t ∧ ∃ w, M'.connects e u w ∧ c w = b} = ∅ := by
        ext e; simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, w, (⟨h1, h2⟩ | ⟨h1, h2⟩), hwb⟩
        · exact e.2 (by rw [h1, h2, hcb, hwb])
        · exact e.2 (by rw [h1, h2, hwb, hcb])
      have h2 : {e : E' | M'.tag e = t ∧ ∃ w, M'.connects e v w ∧ c w = b} = ∅ := by
        ext e; simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, w, (⟨h1, h2⟩ | ⟨h1, h2⟩), hwb⟩
        · exact e.2 (by rw [h1, h2, huv.symm, hcb, hwb])
        · exact e.2 (by rw [h1, h2, hwb, huv.symm, hcb])
      simp [dashedCountAt, h1, h2]
    · have hbij : ∀ x : V, c x ≠ b → dashedCountAt M' c x b t = dashedCountAt M c x b t := by
        intro x hxb
        apply ncard_eq_of_bij (fun e : E' => e.1)
        · rintro e ⟨ht, w, hconn, hwb⟩; exact ⟨ht, w, hconn, hwb⟩
        · intro e₁ _ e₂ _ h; exact Subtype.ext h
        · rintro e ⟨ht, w, hconn, hwb⟩
          have hne : c (M.e₁ e) ≠ c (M.e₂ e) := by
            rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2, hwb]; exact hxb
            · rw [h1, h2, hwb]; exact hxb.symm
          exact ⟨⟨e, hne⟩, ⟨ht, w, hconn, hwb⟩, rfl⟩
      rw [hbij u hcb, hbij v (huv.symm ▸ hcb)]
      exact heq.2 u v huv b t
  let qEquiv : QuotDashedEdge M' c ≃ QuotDashedEdge M c :=
    { toFun := fun q => ⟨q.1, q.2.1, let ⟨e, ht, hs⟩ := q.2.2; ⟨e.1, ht, hs⟩⟩
      invFun := fun q => ⟨q.1, q.2.1, by
        obtain ⟨e, ht, hs⟩ := q.2.2
        have hne : c (M.e₁ e) ≠ c (M.e₂ e) := fun hEq =>
          q.2.1 (hs ▸ Sym2.mk_isDiag_iff.mpr hEq)
        exact ⟨⟨e, hne⟩, ht, hs⟩⟩
      left_inv := fun q => Subtype.ext rfl
      right_inv := fun q => Subtype.ext rfl }
  have hiso : subdivGraph (mixedQuotient M' c) ≃g subdivGraph (mixedQuotient M c) :=
    { toEquiv := Equiv.sumCongr (Equiv.refl C) qEquiv
      map_rel_iff' := by
        intro x y
        rcases x with a | q <;> rcases y with b | q'
        · exact Iff.rfl
        · simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply,
            subdivGraph_mixedQuotient_adj_inl_inr]
          exact Iff.rfl
        · simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply,
            subdivGraph_mixedQuotient_adj_inr_inl]
          exact Iff.rfl
        · exact Iff.rfl }
  exact ⟨E', inferInstance, M', hlt, isOuterplanar_of_hasMinor hOut (hasMinor_of_emb hemb),
    heq', ⟨hiso⟩⟩

/-- Deleting color class `C_i` reduces `Fintype.card V`, preserves outerplanarity, surjectivity,
and equitability, and yields a quotient subdivision graph isomorphic to `G(\widehat{K} - i)`. -/
private lemma delColorClass_step {V E T C : Type} [Fintype V] [Finite E] [Finite C]
    (M : TaggedMixedMultigraph V E T) (c : V → C)
    (hOut : IsOuterplanar (subdivGraph M)) (hSurj : Function.Surjective c)
    (heq : IsMixedEquitable M c) (i : C) :
    ∃ (V' E' C' : Type) (_ : Fintype V') (_ : Fintype E') (_ : Fintype C')
      (M' : TaggedMixedMultigraph V' E' T) (c' : V' → C'),
      Fintype.card V' < Fintype.card V ∧
      IsOuterplanar (subdivGraph M') ∧
      Function.Surjective c' ∧
      IsMixedEquitable M' c' ∧
      Nonempty (subdivGraph (mixedQuotient M' c') ≃g
        (subdivGraph (mixedQuotient M c)).induce (delColorSet M c i)) := by
  classical
  have := Fintype.ofFinite E
  have := Fintype.ofFinite C
  let V' : Type := {v : V // c v ≠ i}
  let E' : Type := {e : E // c (M.e₁ e) ≠ i ∧ c (M.e₂ e) ≠ i}
  let C' : Type := {a : C // a ≠ i}
  let M' : TaggedMixedMultigraph V' E' T :=
    { solid := M.solid.induce {v : V | c v ≠ i}
      e₁ e := ⟨M.e₁ e.1, e.2.1⟩
      e₂ e := ⟨M.e₂ e.1, e.2.2⟩
      loopless_dashed e := fun h => M.loopless_dashed e.1 (congrArg Subtype.val h)
      tag e := M.tag e.1 }
  let c' : V' → C' := fun v => ⟨c v.1, v.2⟩
  have hltV : Fintype.card V' < Fintype.card V := by
    obtain ⟨v₀, hv₀⟩ := hSurj i
    have hssub : (Finset.univ.filter fun v : V => c v ≠ i) ⊂ Finset.univ := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun hEq => ?_⟩
      have hmem : v₀ ∈ Finset.univ.filter fun v : V => c v ≠ i := by
        rw [hEq]; exact Finset.mem_univ v₀
      exact (Finset.mem_filter.mp hmem).2 hv₀
    simpa [V', Fintype.card_subtype] using Finset.card_lt_card hssub
  have hemb : subdivGraph M' ↪g subdivGraph M :=
    { toFun := Sum.map Subtype.val Subtype.val
      inj' := by
        intro x y h
        rcases x with u | e <;> rcases y with v | e'
        · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
        · simp at h
        · simp at h
        · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))
      map_rel_iff' := by
        intro x y
        rcases x with u | e <;> rcases y with v | e'
        · exact Iff.rfl
        · change (M.e₁ e'.1 = u.1 ∨ M.e₂ e'.1 = u.1) ↔
            (⟨M.e₁ e'.1, e'.2.1⟩ : V') = u ∨ (⟨M.e₂ e'.1, e'.2.2⟩ : V') = u
          simp [Subtype.ext_iff]
        · change (M.e₁ e.1 = v.1 ∨ M.e₂ e.1 = v.1) ↔
            (⟨M.e₁ e.1, e.2.1⟩ : V') = v ∨ (⟨M.e₂ e.1, e.2.2⟩ : V') = v
          simp [Subtype.ext_iff]
        · exact Iff.rfl }
  have hSurj' : Function.Surjective c' := by
    intro a
    obtain ⟨v, hv⟩ := hSurj a.1
    exact ⟨⟨v, hv.symm ▸ a.2⟩, Subtype.ext hv⟩
  have heq' : IsMixedEquitable M' c' := by
    refine ⟨fun u v huv b => ?_, fun u v huv b t => ?_⟩
    · have hbij : ∀ x : V', solidCountAt M' c' x b = solidCountAt M c x.1 b.1 := by
        intro x
        apply ncard_eq_of_bij (fun w : V' => w.1)
        · rintro w ⟨hadj, hw⟩; exact ⟨hadj, congrArg Subtype.val hw⟩
        · intro w₁ _ w₂ _ h; exact Subtype.ext h
        · rintro w ⟨hadj, hw⟩
          exact ⟨⟨w, hw.symm ▸ b.2⟩, ⟨hadj, Subtype.ext hw⟩, rfl⟩
      rw [hbij u, hbij v]
      exact heq.1 u.1 v.1 (congrArg Subtype.val huv) b.1
    · have hbij : ∀ x : V', dashedCountAt M' c' x b t = dashedCountAt M c x.1 b.1 t := by
        intro x
        apply ncard_eq_of_bij (fun e : E' => e.1)
        · rintro e ⟨ht, w, (⟨h1, h2⟩ | ⟨h1, h2⟩), hwb⟩
          · exact ⟨ht, w.1, Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩,
              congrArg Subtype.val hwb⟩
          · exact ⟨ht, w.1, Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩,
              congrArg Subtype.val hwb⟩
        · intro e₁ _ e₂ _ h; exact Subtype.ext h
        · rintro e ⟨ht, w, hconn, hwb⟩
          have he' : c (M.e₁ e) ≠ i ∧ c (M.e₂ e) ≠ i := by
            rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨h1.symm ▸ x.2, h2.symm ▸ (hwb.symm ▸ b.2)⟩
            · exact ⟨h1.symm ▸ (hwb.symm ▸ b.2), h2.symm ▸ x.2⟩
          refine ⟨⟨e, he'⟩, ⟨ht, ⟨w, hwb.symm ▸ b.2⟩, ?_, Subtype.ext hwb⟩, rfl⟩
          rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
          · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
      rw [hbij u, hbij v]
      exact heq.2 u.1 v.1 (congrArg Subtype.val huv) b.1 t
  -- Build graph iso `subdivGraph (mixedQuotient M' c') ≃g G(\widehat{K} - i)`.
  let mapQ : QuotDashedEdge M' c' → {q : QuotDashedEdge M c // i ∉ q.1.1} := fun q =>
    ⟨⟨(Sym2.map Subtype.val q.1.1, q.1.2), by
      refine ⟨?_, ?_⟩
      · intro hdiag
        apply q.2.1
        induction h : q.1.1 using Sym2.ind with
        | _ a b =>
          rw [h] at hdiag
          simp only [Sym2.map_mk, Sym2.mk_isDiag_iff] at hdiag
          exact Sym2.mk_isDiag_iff.mpr (Subtype.ext hdiag)
      · obtain ⟨e, ht, hs⟩ := q.2.2
        refine ⟨e.1, ht, ?_⟩
        rw [← hs]
        simp [M', c']⟩,
      by
        intro hi
        obtain ⟨a, _, ha⟩ := Sym2.mem_map.mp hi
        exact a.2 ha⟩
  let invQ : {q : QuotDashedEdge M c // i ∉ q.1.1} → QuotDashedEdge M' c' := fun q =>
    let ab := sym2Endpoints q.1.1.1 q.1.2.1
    have ha : ab.1.1 ≠ i := fun hEq => q.2 (by rw [← ab.2.2, Sym2.mem_iff]; exact Or.inl hEq.symm)
    have hb : ab.1.2 ≠ i := fun hEq => q.2 (by rw [← ab.2.2, Sym2.mem_iff]; exact Or.inr hEq.symm)
    ⟨(s(⟨ab.1.1, ha⟩, ⟨ab.1.2, hb⟩), q.1.1.2), by
      refine ⟨?_, ?_⟩
      · intro hdiag
        exact ab.2.1 (congrArg Subtype.val (Sym2.mk_isDiag_iff.mp hdiag))
      · obtain ⟨e, ht, hs⟩ := q.1.2.2
        have h1 : c (M.e₁ e) ∈ q.1.1.1 := hs ▸ Sym2.mem_mk_left _ _
        have h2 : c (M.e₂ e) ∈ q.1.1.1 := hs ▸ Sym2.mem_mk_right _ _
        have he1 : c (M.e₁ e) ≠ i := fun hEq => q.2 (hEq ▸ h1)
        have he2 : c (M.e₂ e) ≠ i := fun hEq => q.2 (hEq ▸ h2)
        refine ⟨⟨e, he1, he2⟩, ht, ?_⟩
        have hpair : s(c (M.e₁ e), c (M.e₂ e)) = s(ab.1.1, ab.1.2) := hs.trans ab.2.2.symm
        rcases Sym2.eq_iff.mp hpair with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext k1, Subtype.ext k2⟩)
        · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext k1, Subtype.ext k2⟩)⟩
  have hmapQ_pair : ∀ q : QuotDashedEdge M' c', (mapQ q).1.1.1 = Sym2.map Subtype.val q.1.1 :=
    fun _ => rfl
  have hinvQ_pair : ∀ q : {q : QuotDashedEdge M c // i ∉ q.1.1},
      Sym2.map Subtype.val (invQ q).1.1 = q.1.1.1 := by
    intro q
    change Sym2.map Subtype.val s(_, _) = q.1.1.1
    rw [Sym2.map_mk]
    exact (sym2Endpoints q.1.1.1 q.1.2.1).2.2
  have hsym2_map_inj : ∀ p₁ p₂ : Sym2 C',
      Sym2.map Subtype.val p₁ = Sym2.map Subtype.val p₂ → p₁ = p₂ := by
    intro p₁ p₂ h
    induction p₁ using Sym2.ind with
    | _ a₁ b₁ =>
      induction p₂ using Sym2.ind with
      | _ a₂ b₂ =>
        simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
        · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
  let toF : C' ⊕ QuotDashedEdge M' c' → ↥(delColorSet M c i) :=
    fun x => match x with
    | Sum.inl a => ⟨Sum.inl a.1, a.2⟩
    | Sum.inr q => ⟨Sum.inr (mapQ q).1, (mapQ q).2⟩
  let invF : ↥(delColorSet M c i) → C' ⊕ QuotDashedEdge M' c' :=
    fun ⟨y, hy⟩ => match y, hy with
    | Sum.inl a, ha => Sum.inl ⟨a, ha⟩
    | Sum.inr q, hq => Sum.inr (invQ ⟨q, hq⟩)
  have hiso : subdivGraph (mixedQuotient M' c') ≃g
      (subdivGraph (mixedQuotient M c)).induce (delColorSet M c i) :=
    { toFun := toF
      invFun := invF
      left_inv := fun x => by
        rcases x with a | q
        · rfl
        · simp only [toF, invF]
          congr 1
          apply Subtype.ext
          apply Prod.ext
          · apply hsym2_map_inj
            exact hinvQ_pair (mapQ q)
          · rfl
      right_inv := fun ⟨y, hy⟩ => by
        rcases y with a | q
        · rfl
        · apply Subtype.ext
          simp only [toF, invF]
          congr 1
          apply Subtype.ext
          apply Prod.ext
          · exact hinvQ_pair ⟨q, hy⟩
          · rfl
      map_rel_iff' := by
        intro x y
        rcases x with a | q <;> rcases y with b | q'
        · change (mixedQuotient M c).solid.Adj a.1 b.1 ↔ (mixedQuotient M' c').solid.Adj a b
          constructor
          · rintro ⟨hab, u, v, hu, hv, huv⟩
            refine ⟨fun h => hab (congrArg Subtype.val h),
              ⟨u, hu.symm ▸ a.2⟩, ⟨v, hv.symm ▸ b.2⟩, Subtype.ext hu, Subtype.ext hv, huv⟩
          · rintro ⟨hab, u, v, hu, hv, huv⟩
            exact ⟨fun h => hab (Subtype.ext h), u.1, v.1, congrArg Subtype.val hu,
              congrArg Subtype.val hv, huv⟩
        · change (subdivGraph (mixedQuotient M c)).Adj (Sum.inl a.1) (Sum.inr (mapQ q').1) ↔
            (subdivGraph (mixedQuotient M' c')).Adj (Sum.inl a) (Sum.inr q')
          rw [subdivGraph_mixedQuotient_adj_inl_inr, subdivGraph_mixedQuotient_adj_inl_inr]
          change a.1 ∈ Sym2.map Subtype.val q'.1.1 ↔ a ∈ q'.1.1
          constructor
          · intro hmem
            obtain ⟨a', ha'q', hval⟩ := Sym2.mem_map.mp hmem
            exact Subtype.ext hval ▸ ha'q'
          · intro haq'
            exact Sym2.mem_map.mpr ⟨a, haq', rfl⟩
        · change (subdivGraph (mixedQuotient M c)).Adj (Sum.inr (mapQ q).1) (Sum.inl b.1) ↔
            (subdivGraph (mixedQuotient M' c')).Adj (Sum.inr q) (Sum.inl b)
          rw [subdivGraph_mixedQuotient_adj_inr_inl, subdivGraph_mixedQuotient_adj_inr_inl]
          change b.1 ∈ Sym2.map Subtype.val q.1.1 ↔ b ∈ q.1.1
          constructor
          · intro hmem
            obtain ⟨b', hb'q, hval⟩ := Sym2.mem_map.mp hmem
            exact Subtype.ext hval ▸ hb'q
          · intro hbq
            exact Sym2.mem_map.mpr ⟨b, hbq, rfl⟩
        · exact Iff.rfl }
  exact ⟨V', E', C', inferInstance, inferInstance, inferInstance, M', c',
    hltV, isOuterplanar_of_hasMinor hOut (hasMinor_of_emb hemb), hSurj', heq', ⟨hiso⟩⟩

/-- Deleting all solid edges between two distinct color classes `C_a, C_b` that share a solid edge
strictly reduces `mixedSize`, preserves outerplanarity & equitability, and deletes the single edge
`Sum.inl a ~ Sum.inl b` from `subdivGraph (mixedQuotient M c)`. -/
private lemma delQuotSolidEdge_step {V E T C : Type} [Finite V] [Fintype E]
    (M : TaggedMixedMultigraph V E T) (c : V → C)
    (hOut : IsOuterplanar (subdivGraph M)) (heq : IsMixedEquitable M c)
    {a b : C} (hab : (mixedQuotient M c).solid.Adj a b) :
    ∃ (M' : TaggedMixedMultigraph V E T) (H' : SimpleGraph (C ⊕ QuotDashedEdge M c)),
      mixedSize M' < mixedSize M ∧
      IsOuterplanar (subdivGraph M') ∧
      IsMixedEquitable M' c ∧
      (∀ x y : C ⊕ QuotDashedEdge M c,
        H'.Adj x y ↔ (subdivGraph (mixedQuotient M c)).Adj x y ∧
          ¬ ((x = Sum.inl a ∧ y = Sum.inl b) ∨ (x = Sum.inl b ∧ y = Sum.inl a))) ∧
      Nonempty (subdivGraph (mixedQuotient M' c) ≃g H') := by
  classical
  let M' : TaggedMixedMultigraph V E T :=
    { solid :=
        { Adj u v := M.solid.Adj u v ∧ ¬ ((c u = a ∧ c v = b) ∨ (c u = b ∧ c v = a))
          symm := ⟨fun _ _ ⟨h, hnot⟩ => ⟨h.symm, fun h1 => hnot (by tauto)⟩⟩
          loopless := ⟨fun u ⟨h, _⟩ => M.solid.loopless.irrefl u h⟩ }
      e₁ := M.e₁
      e₂ := M.e₂
      loopless_dashed := M.loopless_dashed
      tag := M.tag }
  have hle : subdivGraph M' ≤ subdivGraph M := by
    intro x y hxy
    cases x <;> cases y
    · exact hxy.1
    · exact hxy
    · exact hxy
    · exact hxy
  have hlt : mixedSize M' < mixedSize M := by
    unfold mixedSize
    obtain ⟨-, u₀, v₀, hu₀, hv₀, huv₀⟩ := hab
    have hssub : {p : V × V | M'.solid.Adj p.1 p.2} ⊂ {p : V × V | M.solid.Adj p.1 p.2} := by
      refine Set.ssubset_iff_subset_ne.mpr ⟨fun _ hp => hp.1, fun hEq => ?_⟩
      have hmem : (u₀, v₀) ∈ {p : V × V | M'.solid.Adj p.1 p.2} := by rw [hEq]; exact huv₀
      exact hmem.2 (Or.inl ⟨hu₀, hv₀⟩)
    have hcard := Set.ncard_lt_ncard hssub (Set.toFinite _)
    omega
  have heq' : IsMixedEquitable M' c := by
    refine ⟨fun u v huv d => ?_, heq.2⟩
    by_cases hpair : (c u = a ∧ d = b) ∨ (c u = b ∧ d = a)
    · have h1 : {w : V | M'.solid.Adj u w ∧ c w = d} = ∅ := by
        ext w; simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hnot⟩, hwd⟩
        exact hnot (by rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, hwd])
      have h2 : {w : V | M'.solid.Adj v w ∧ c w = d} = ∅ := by
        ext w; simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hnot⟩, hwd⟩
        exact hnot (by rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [← huv, h1, h2, hwd])
      simp [solidCountAt, h1, h2]
    · have h1 : {w : V | M'.solid.Adj u w ∧ c w = d} = {w : V | M.solid.Adj u w ∧ c w = d} := by
        ext w; exact ⟨fun ⟨⟨h, _⟩, hw⟩ => ⟨h, hw⟩,
          fun ⟨h, hw⟩ => ⟨⟨h, fun hbad => hpair (by
            rcases hbad with ⟨k1, k2⟩ | ⟨k1, k2⟩ <;> simp [k1, k2, ← hw])⟩, hw⟩⟩
      have h2 : {w : V | M'.solid.Adj v w ∧ c w = d} = {w : V | M.solid.Adj v w ∧ c w = d} := by
        ext w; exact ⟨fun ⟨⟨h, _⟩, hw⟩ => ⟨h, hw⟩,
          fun ⟨h, hw⟩ => ⟨⟨h, fun hbad => hpair (by
            rcases hbad with ⟨k1, k2⟩ | ⟨k1, k2⟩ <;> simp [huv, k1, k2, ← hw])⟩, hw⟩⟩
      simpa [solidCountAt, h1, h2] using heq.1 u v huv d
  let H' : SimpleGraph (C ⊕ QuotDashedEdge M c) :=
    { Adj x y := (subdivGraph (mixedQuotient M c)).Adj x y ∧
        ¬ ((x = Sum.inl a ∧ y = Sum.inl b) ∨ (x = Sum.inl b ∧ y = Sum.inl a))
      symm := ⟨fun _ _ ⟨h, hnot⟩ => ⟨h.symm, fun h1 => hnot (by tauto)⟩⟩
      loopless := ⟨fun x ⟨h, _⟩ => (subdivGraph (mixedQuotient M c)).loopless.irrefl x h⟩ }
  have hiso : subdivGraph (mixedQuotient M' c) ≃g H' :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := by
        intro x y
        rcases x with a' | q <;> rcases y with b' | q'
        · constructor
          · rintro ⟨⟨hne, u, v, hu, hv, huv⟩, hnot⟩
            refine ⟨hne, u, v, hu, hv, huv, fun hbad => hnot ?_⟩
            rcases hbad with ⟨k1, k2⟩ | ⟨k1, k2⟩
            · exact Or.inl
                ⟨congrArg Sum.inl (hu.symm.trans k1), congrArg Sum.inl (hv.symm.trans k2)⟩
            · exact Or.inr
                ⟨congrArg Sum.inl (hu.symm.trans k1), congrArg Sum.inl (hv.symm.trans k2)⟩
          · rintro ⟨hne, u, v, hu, hv, huv, hnot⟩
            refine ⟨⟨hne, u, v, hu, hv, huv⟩, fun hbad => hnot ?_⟩
            rcases hbad with ⟨k1, k2⟩ | ⟨k1, k2⟩
            · exact Or.inl ⟨hu.trans (Sum.inl.inj k1), hv.trans (Sum.inl.inj k2)⟩
            · exact Or.inr ⟨hu.trans (Sum.inl.inj k1), hv.trans (Sum.inl.inj k2)⟩
        · constructor
          · rintro ⟨h, _⟩; exact h
          · intro h; refine ⟨h, by simp⟩
        · constructor
          · rintro ⟨h, _⟩; exact h
          · intro h; refine ⟨h, by simp⟩
        · simp [H', subdivGraph] }
  exact ⟨M', H', hlt, isOuterplanar_of_le hOut hle, heq', fun _ _ => Iff.rfl, ⟨hiso⟩⟩

/-- Unique-edge link summary from every vertex of color `i` to color `b ≠ i` in Subcase 3B(ii). -/
private structure ColorLink {V E T C : Type} (M : TaggedMixedMultigraph V E T) (c : V → C)
    (i b : C) where
  nbr : {x : V // c x = i} → V
  nbr_color : ∀ x, c (nbr x) = b
  tagOpt : Option T
  solid_iff : ∀ (x : {x : V // c x = i}) (w : V), c w = b →
    (M.solid.Adj x.1 w ↔ tagOpt = none ∧ w = nbr x)
  dashed_only : ∀ (x : {x : V // c x = i}) (e : E) (w : V), c w = b →
    M.connects e x.1 w → tagOpt = some (M.tag e) ∧ w = nbr x
  dashed_unique : ∀ (t₀ : T), tagOpt = some t₀ →
    ∀ (x : {x : V // c x = i}), ∃! e : E, M.tag e = t₀ ∧ M.connects e x.1 (nbr x)

/-- Build a `ColorLink M c i b` when a witness vertex `v ∈ C_i` has a unique neighbor `u_b` of
color `b` in `underlyingSimple M`, at most 1 dashed edge between `v` and `u_b`, and no
solid+dashed collision on `s(i, b)`. -/
private noncomputable def buildColorLink {V E T C : Type} [Finite V] [Finite E]
    (M : TaggedMixedMultigraph V E T) (c : V → C) (heq : IsMixedEquitable M c)
    {i b : C} (hib : i ≠ b) {v u_b : V} (hv : c v = i) (hub : c u_b = b)
    (hv_adj : (underlyingSimple M).Adj v u_b)
    (hv_uniq_nbr : ∀ w : V, (underlyingSimple M).Adj v w → c w = b → w = u_b)
    (hv_uniq_dash : ∀ e₁ e₂ : E, M.connects e₁ v u_b → M.connects e₂ v u_b → e₁ = e₂)
    (hno_both : (mixedQuotient M c).solid.Adj i b →
      ∀ q : QuotDashedEdge M c, q.1.1 ≠ s(i, b)) :
    ColorLink M c i b := by
  classical
  by_cases hsol : M.solid.Adj v u_b
  · -- Solid case: `tagOpt = none`.
    have hq_sol : (mixedQuotient M c).solid.Adj i b := ⟨hib, v, u_b, hv, hub, hsol⟩
    have hsol_set_v : {w : V | M.solid.Adj v w ∧ c w = b} = {u_b} := by
      ext w
      simp only [Set.mem_singleton_iff]
      exact ⟨fun ⟨hadj, hwb⟩ => hv_uniq_nbr w (Or.inl hadj) hwb,
        fun hEq => hEq ▸ ⟨hsol, hub⟩⟩
    have hsol_card : ∀ x : {x : V // c x = i}, solidCountAt M c x.1 b = 1 := by
      intro x
      rw [heq.1 x.1 v (x.2.trans hv.symm) b]
      simp [solidCountAt, hsol_set_v]
    have hsol_ex : ∀ x : {x : V // c x = i}, ∃ w : V, {u : V | M.solid.Adj x.1 u ∧ c u = b} = {w} :=
      fun x => Set.ncard_eq_one.mp (hsol_card x)
    have hno_dash : ∀ (x : {x : V // c x = i}) (e : E) (w : V), c w = b → ¬ M.connects e x.1 w := by
      intro x e w hwb hconn
      have hpair : s(c (M.e₁ e), c (M.e₂ e)) = s(i, b) := by
        rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2, x.2, hwb]
        · rw [h1, h2, hwb, x.2, Sym2.eq_swap]
      have hnd : ¬ (s(i, b) : Sym2 C).IsDiag := fun hd => hib (Sym2.mk_isDiag_iff.mp hd)
      let q : QuotDashedEdge M c := ⟨(s(i, b), M.tag e), hnd, ⟨e, rfl, hpair⟩⟩
      exact hno_both hq_sol q rfl
    refine
      { nbr := fun x => Classical.choose (hsol_ex x)
        nbr_color := fun x =>
          ((Set.ext_iff.mp (Classical.choose_spec (hsol_ex x)) _).mpr rfl).2
        tagOpt := none
        solid_iff := fun x w hwb => by
          have hspec := Classical.choose_spec (hsol_ex x)
          constructor
          · intro hadj
            refine ⟨rfl, ?_⟩
            exact (Set.ext_iff.mp hspec w).mp ⟨hadj, hwb⟩
          · rintro ⟨_, rfl⟩
            exact ((Set.ext_iff.mp hspec _).mpr rfl).1
        dashed_only := fun x e w hwb hconn => False.elim (hno_dash x e w hwb hconn)
        dashed_unique := fun _ h => by simp at h }
  · -- Dashed case: `tagOpt = some (M.tag e₀)`.
    have hex_e0 : ∃ e₀ : E, M.connects e₀ v u_b := hv_adj.resolve_left hsol
    let e₀ : E := Classical.choose hex_e0
    have he₀ : M.connects e₀ v u_b := Classical.choose_spec hex_e0
    let t₀ : T := M.tag e₀
    have hno_sol : ∀ (x : {x : V // c x = i}) (w : V), c w = b → ¬ M.solid.Adj x.1 w := by
      intro x w hwb hadj
      have hpos : 0 < solidCountAt M c v b := by
        rw [heq.1 v x.1 (hv.trans x.2.symm) b]
        exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨w, hadj, hwb⟩
      obtain ⟨w', hw'adj, hw'b⟩ := Set.nonempty_of_ncard_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hEq := hv_uniq_nbr w' (Or.inl hw'adj) hw'b
      exact hsol (hEq ▸ hw'adj)
    have hdash_set_v : {e : E | M.tag e = t₀ ∧ ∃ w, M.connects e v w ∧ c w = b} = {e₀} := by
      ext e
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro ⟨_, w, hconn, hwb⟩
        have hEq := hv_uniq_nbr w (Or.inr ⟨e, hconn⟩) hwb
        exact hv_uniq_dash e e₀ (hEq ▸ hconn) he₀
      · rintro rfl
        exact ⟨rfl, u_b, he₀, hub⟩
    have hdash_card : ∀ x : {x : V // c x = i}, dashedCountAt M c x.1 b t₀ = 1 := by
      intro x
      rw [heq.2 x.1 v (x.2.trans hv.symm) b t₀]
      simp [dashedCountAt, hdash_set_v]
    have hdash_other : ∀ (x : {x : V // c x = i}) (t : T), t ≠ t₀ →
        dashedCountAt M c x.1 b t = 0 := by
      intro x t htt₀
      rw [heq.2 x.1 v (x.2.trans hv.symm) b t]
      have hemp : {e : E | M.tag e = t ∧ ∃ w, M.connects e v w ∧ c w = b} = ∅ := by
        ext e; simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨ht, w, hconn, hwb⟩
        have hEq := hv_uniq_nbr w (Or.inr ⟨e, hconn⟩) hwb
        have heEq := hv_uniq_dash e e₀ (hEq ▸ hconn) he₀
        exact htt₀ (ht.symm.trans (congrArg M.tag heEq))
      simp [dashedCountAt, hemp]
    have hdash_ex : ∀ x : {x : V // c x = i},
        ∃ e : E, {e' : E | M.tag e' = t₀ ∧ ∃ w, M.connects e' x.1 w ∧ c w = b} = {e} :=
      fun x => Set.ncard_eq_one.mp (hdash_card x)
    let edgeOf : {x : V // c x = i} → E := fun x => Classical.choose (hdash_ex x)
    have hedge_mem : ∀ x, M.tag (edgeOf x) = t₀ ∧ ∃ w, M.connects (edgeOf x) x.1 w ∧ c w = b := by
      intro x
      have hspec := Classical.choose_spec (hdash_ex x)
      have hmem : edgeOf x ∈ {e' : E | M.tag e' = t₀ ∧ ∃ w, M.connects e' x.1 w ∧ c w = b} := by
        rw [hspec]; exact Set.mem_singleton _
      exact hmem
    let nbrOf : {x : V // c x = i} → V := fun x => Classical.choose (hedge_mem x).2
    have hnbr_spec : ∀ x, M.connects (edgeOf x) x.1 (nbrOf x) ∧ c (nbrOf x) = b :=
      fun x => Classical.choose_spec (hedge_mem x).2
    refine
      { nbr := nbrOf
        nbr_color := fun x => (hnbr_spec x).2
        tagOpt := some t₀
        solid_iff := fun x w hwb => ⟨fun hadj => False.elim (hno_sol x w hwb hadj),
          fun ⟨h, _⟩ => by simp at h⟩
        dashed_only := fun x e w hwb hconn => by
          have htag : M.tag e = t₀ := by
            by_contra hne
            have h0 := hdash_other x (M.tag e) hne
            have hpos : 0 < dashedCountAt M c x.1 b (M.tag e) :=
              (Set.ncard_pos (Set.toFinite _)).mpr ⟨e, rfl, w, hconn, hwb⟩
            omega
          have hspec := Classical.choose_spec (hdash_ex x)
          have heEq : e = edgeOf x := by
            have hmem : e ∈ ({edgeOf x} : Set E) := by
              rw [← hspec]; exact ⟨htag, w, hconn, hwb⟩
            exact Set.mem_singleton_iff.mp hmem
          refine ⟨congrArg some htag.symm, ?_⟩
          exact M.connects_unique_right (heEq ▸ hconn) (hnbr_spec x).1
        dashed_unique := fun t ht x => by
          have htt₀ : t = t₀ := Option.some.inj ht.symm
          subst htt₀
          refine ⟨edgeOf x, ⟨(hedge_mem x).1, (hnbr_spec x).1⟩, fun e ⟨hte, hconn⟩ => ?_⟩
          have hspec := Classical.choose_spec (hdash_ex x)
          have hmem : e ∈ ({edgeOf x} : Set E) := by
            rw [← hspec]; exact ⟨hte, nbrOf x, hconn, (hnbr_spec x).2⟩
          exact Set.mem_singleton_iff.mp hmem }

/-- Helper for Subcase 3B(ii) equitability: counting `{x ∈ C_i | link.nbr x = w}` equals either
`solidCountAt M c w i` or `dashedCountAt M c w i t₀`, hence is independent of `w ∈ C_b`. -/
private lemma card_colorLink_preimage_eq {V E T C : Type} [Finite V] [Finite E]
    (M : TaggedMixedMultigraph V E T) (c : V → C) {i b : C} (_hib : i ≠ b)
    (link : ColorLink M c i b) (w : V) (hwb : c w = b) :
    match link.tagOpt with
    | none =>
      Set.ncard {x : {x : V // c x = i} | link.nbr x = w} = solidCountAt M c w i
    | some t₀ =>
      Set.ncard {x : {x : V // c x = i} | link.nbr x = w} = dashedCountAt M c w i t₀ := by
  cases htag : link.tagOpt with
  | none =>
    apply ncard_eq_of_bij (fun x : {x : V // c x = i} => x.1)
    · intro x hx
      have hsol : M.solid.Adj x.1 w := (link.solid_iff x w hwb).mpr ⟨htag, hx.symm⟩
      exact ⟨hsol.symm, x.2⟩
    · intro x₁ _ x₂ _ h; exact Subtype.ext h
    · rintro x ⟨hsol, hxi⟩
      have hEq : w = link.nbr ⟨x, hxi⟩ := ((link.solid_iff ⟨x, hxi⟩ w hwb).mp hsol.symm).2
      exact ⟨⟨x, hxi⟩, hEq.symm, rfl⟩
  | some t₀ =>
    have huniq := link.dashed_unique t₀ htag
    let edgeOf : {x : V // c x = i} → E := fun x => Classical.choose (huniq x)
    have hedge_spec : ∀ x, M.tag (edgeOf x) = t₀ ∧ M.connects (edgeOf x) x.1 (link.nbr x) :=
      fun x => (Classical.choose_spec (huniq x)).1
    have hedge_uniq : ∀ x e, M.tag e = t₀ ∧ M.connects e x.1 (link.nbr x) → e = edgeOf x :=
      fun x e h => (Classical.choose_spec (huniq x)).2 e h
    apply ncard_eq_of_bij edgeOf
    · intro x hx
      refine ⟨(hedge_spec x).1, x.1, M.connects_symm (hx ▸ (hedge_spec x).2), x.2⟩
    · intro x₁ hx₁ x₂ hx₂ hEq
      have h1 : M.connects (edgeOf x₁) w x₁.1 := M.connects_symm (hx₁ ▸ (hedge_spec x₁).2)
      have h2 : M.connects (edgeOf x₁) w x₂.1 := M.connects_symm (hEq ▸ hx₂ ▸ (hedge_spec x₂).2)
      exact Subtype.ext (M.connects_unique_right h1 h2)
    · rintro e ⟨hte, x, hconn, hxi⟩
      have hxw : M.connects e x w := M.connects_symm hconn
      have honly := link.dashed_only ⟨x, hxi⟩ e w hwb hxw
      have hwEq : w = link.nbr ⟨x, hxi⟩ := honly.2
      refine ⟨⟨x, hxi⟩, hwEq.symm, ?_⟩
      exact (hedge_uniq ⟨x, hxi⟩ e ⟨hte, hwEq ▸ hxw⟩).symm

/-- Subcase 3B(ii) complete reduction: given a degree-2 vertex `v ∈ C_i` whose two neighbors
`u₁ ∈ C_j`, `u₂ ∈ C_ℓ` have distinct colors `j ≠ ℓ` (with `i ≠ j`, `i ≠ ℓ`), build the strictly
smaller mixed multigraph `(M', c')` on `V \ C_i` with brand-new tag `none : Option T`, prove it is
outerplanar and equitable, and prove `IsOuterplanar G(\widehat{K}') → IsOuterplanar G(\widehat{K})`
using 0, 1, or 2 applications of Lemma 4. -/
private lemma subcase3Bii_step {V E T C : Type}
    [Fintype V] [Finite E] [Finite T] [Finite C]
    (M : TaggedMixedMultigraph V E T) (c : V → C)
    (hOut : IsOuterplanar (subdivGraph M)) (hSurj : Function.Surjective c)
    (heq : IsMixedEquitable M c)
    (_hM1_dash : ∀ e : E, c (M.e₁ e) ≠ c (M.e₂ e))
    (hM4 : ∀ a b : C, (mixedQuotient M c).solid.Adj a b →
      ∀ q : QuotDashedEdge M c, q.1.1 ≠ s(a, b))
    {v u₁ u₂ : V} {i j ℓ : C}
    (hv : c v = i) (hu₁ : c u₁ = j) (hu₂ : c u₂ = ℓ)
    (hij : i ≠ j) (hiℓ : i ≠ ℓ) (hjℓ : j ≠ ℓ)
    (hNv : ∀ w : V, (underlyingSimple M).Adj v w ↔ w = u₁ ∨ w = u₂)
    (hd1 : ∀ e₁ e₂ : E, M.connects e₁ v u₁ → M.connects e₂ v u₁ → e₁ = e₂)
    (hd2 : ∀ e₁ e₂ : E, M.connects e₁ v u₂ → M.connects e₂ v u₂ → e₁ = e₂) :
    ∃ (V' E' T' C' : Type) (_ : Fintype V') (_ : Fintype E') (_ : Fintype T') (_ : Fintype C')
      (M' : TaggedMixedMultigraph V' E' T') (c' : V' → C'),
      Fintype.card V' < Fintype.card V ∧
      IsOuterplanar (subdivGraph M') ∧
      Function.Surjective c' ∧
      IsMixedEquitable M' c' ∧
      (IsOuterplanar (subdivGraph (mixedQuotient M' c')) →
        IsOuterplanar (subdivGraph (mixedQuotient M c))) := by
  classical
  have := Fintype.ofFinite E
  have := Fintype.ofFinite T
  have := Fintype.ofFinite C
  -- Build the two `ColorLink`s from `C_i` to `C_j` and `C_ℓ`.
  have huniq_j : ∀ w : V, (underlyingSimple M).Adj v w → c w = j → w = u₁ := by
    intro w hadj hwj
    rcases (hNv w).mp hadj with rfl | rfl
    · rfl
    · exact absurd (hu₂.symm.trans hwj) hjℓ.symm
  have huniq_ℓ : ∀ w : V, (underlyingSimple M).Adj v w → c w = ℓ → w = u₂ := by
    intro w hadj hwℓ
    rcases (hNv w).mp hadj with rfl | rfl
    · exact absurd (hu₁.symm.trans hwℓ) hjℓ
    · rfl
  let link₁ : ColorLink M c i j := buildColorLink M c heq hij hv hu₁
    ((hNv u₁).mpr (Or.inl rfl)) huniq_j hd1 (hM4 i j)
  let link₂ : ColorLink M c i ℓ := buildColorLink M c heq hiℓ hv hu₂
    ((hNv u₂).mpr (Or.inr rfl)) huniq_ℓ hd2 (hM4 i ℓ)
  -- No edges from `C_i` to any color `b ∉ {j, ℓ}`.
  have hno_other_sol : ∀ b : C, b ≠ j → b ≠ ℓ → ¬ (mixedQuotient M c).solid.Adj i b := by
    intro b hbj hbℓ hadj
    obtain ⟨w, hvw, hwb⟩ := exists_solid_of_quot_adj heq hadj hv
    rcases (hNv w).mp (Or.inl hvw) with rfl | rfl
    · exact hbj (hwb.symm.trans hu₁)
    · exact hbℓ (hwb.symm.trans hu₂)
  have hno_other_dash : ∀ (q : QuotDashedEdge M c), i ∈ q.1.1 →
      q.1.1 = s(i, j) ∨ q.1.1 = s(i, ℓ) := by
    intro q hiq
    obtain ⟨b, hpair⟩ := Sym2.mem_iff_exists.mp hiq
    obtain ⟨e, w, -, hconn, hwb⟩ := exists_dashed_of_quot_edge heq hpair hv
    rcases (hNv w).mp (Or.inr ⟨e, hconn⟩) with rfl | rfl
    · left; rw [hpair, hwb.symm.trans hu₁]
    · right; rw [hpair, hwb.symm.trans hu₂]
  -- Define reduced mixed multigraph `M'` on `V' = V \ C_i` with brand-new tag `none : Option T`.
  let V' : Type := {u : V // c u ≠ i}
  let Eold : Type := {e : E // c (M.e₁ e) ≠ i ∧ c (M.e₂ e) ≠ i}
  let Ci : Type := {x : V // c x = i}
  let E' : Type := Eold ⊕ Ci
  let T' : Type := Option T
  let C' : Type := {a : C // a ≠ i}
  let yOf : Ci → V' := fun x => ⟨link₁.nbr x, (link₁.nbr_color x).symm ▸ hij.symm⟩
  let zOf : Ci → V' := fun x => ⟨link₂.nbr x, (link₂.nbr_color x).symm ▸ hiℓ.symm⟩
  let M' : TaggedMixedMultigraph V' E' T' :=
    { solid := M.solid.induce {u : V | c u ≠ i}
      e₁ e := match e with
        | Sum.inl eo => ⟨M.e₁ eo.1, eo.2.1⟩
        | Sum.inr x => yOf x
      e₂ e := match e with
        | Sum.inl eo => ⟨M.e₂ eo.1, eo.2.2⟩
        | Sum.inr x => zOf x
      loopless_dashed e := by
        cases e with
        | inl eo => exact fun h => M.loopless_dashed eo.1 (congrArg Subtype.val h)
        | inr x =>
          intro h
          have hEq : link₁.nbr x = link₂.nbr x := congrArg Subtype.val h
          exact hjℓ ((link₁.nbr_color x).symm.trans ((congrArg c hEq).trans (link₂.nbr_color x)))
      tag e := match e with
        | Sum.inl eo => some (M.tag eo.1)
        | Sum.inr _ => none }
  let c' : V' → C' := fun u => ⟨c u.1, u.2⟩
  -- 1. Strictly smaller vertex count.
  have hltV : Fintype.card V' < Fintype.card V := by
    have hssub : (Finset.univ.filter fun u : V => c u ≠ i) ⊂ Finset.univ := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun hEq => ?_⟩
      have hmem : v ∈ Finset.univ.filter fun u : V => c u ≠ i := by
        rw [hEq]; exact Finset.mem_univ v
      exact (Finset.mem_filter.mp hmem).2 hv
    simpa [V', Fintype.card_subtype] using Finset.card_lt_card hssub
  -- 2. `HasMinor (subdivGraph M) (subdivGraph M')` via star contraction on each `x ∈ C_i`.
  have hMinorM' : HasMinor (subdivGraph M) (subdivGraph M') := by
    let φ : V ⊕ E → Option (V' ⊕ E') := fun s =>
      match s with
      | Sum.inl u =>
        if hu : c u = i then some (Sum.inr (Sum.inr ⟨u, hu⟩))
        else some (Sum.inl ⟨u, hu⟩)
      | Sum.inr e =>
        if h1 : c (M.e₁ e) = i then some (Sum.inr (Sum.inr ⟨M.e₁ e, h1⟩))
        else if h2 : c (M.e₂ e) = i then some (Sum.inr (Sum.inr ⟨M.e₂ e, h2⟩))
        else some (Sum.inr (Sum.inl ⟨e, h1, h2⟩))
    refine hasMinor_of_partialMap φ ?_ ?_
    · intro w
      rcases w with u | (eo | x)
      · -- Singleton fiber `{Sum.inl u.1}`.
        have hfib : {s : V ⊕ E | φ s = some (Sum.inl u)} = {Sum.inl u.1} := by
          ext s
          simp only [Set.mem_singleton_iff]
          constructor
          · intro hs
            change φ s = some (Sum.inl u) at hs
            rcases s with a | e
            · by_cases ha : c a = i
              · simp [φ, ha] at hs
              · simp only [φ, ha, ↓reduceDIte, Option.some.injEq, Sum.inl.injEq] at hs
                exact congrArg Sum.inl (congrArg Subtype.val hs)
            · by_cases h1 : c (M.e₁ e) = i
              · simp [φ, h1] at hs
              · by_cases h2 : c (M.e₂ e) = i
                · simp [φ, h1, h2] at hs
                · simp [φ, h1, h2] at hs
          · rintro rfl
            change φ (Sum.inl u.1) = some (Sum.inl u)
            simp [φ, u.2]
        rw [hfib]
        have : Nonempty ({Sum.inl u.1} : Set (V ⊕ E)) := ⟨⟨Sum.inl u.1, Set.mem_singleton _⟩⟩
        refine ⟨fun p q => ?_⟩
        have hEq : p = q := Subtype.ext
          ((Set.mem_singleton_iff.mp p.2).trans (Set.mem_singleton_iff.mp q.2).symm)
        rw [hEq]
      · -- Singleton fiber `{Sum.inr eo.1}`.
        have hfib : {s : V ⊕ E | φ s = some (Sum.inr (Sum.inl eo))} = {Sum.inr eo.1} := by
          ext s
          simp only [Set.mem_singleton_iff]
          constructor
          · intro hs
            change φ s = some (Sum.inr (Sum.inl eo)) at hs
            rcases s with a | e
            · by_cases ha : c a = i
              · simp [φ, ha] at hs
              · simp [φ, ha] at hs
            · by_cases h1 : c (M.e₁ e) = i
              · simp [φ, h1] at hs
              · by_cases h2 : c (M.e₂ e) = i
                · simp [φ, h1, h2] at hs
                · simp only [φ, h1, h2, ↓reduceDIte] at hs
                  exact congrArg Sum.inr
                    (congrArg Subtype.val (Sum.inl.inj (Sum.inr.inj (Option.some.inj hs))))
          · rintro rfl
            change φ (Sum.inr eo.1) = some (Sum.inr (Sum.inl eo))
            simp [φ, eo.2.1, eo.2.2]
        rw [hfib]
        have : Nonempty ({Sum.inr eo.1} : Set (V ⊕ E)) := ⟨⟨Sum.inr eo.1, Set.mem_singleton _⟩⟩
        refine ⟨fun p q => ?_⟩
        have hEq : p = q := Subtype.ext
          ((Set.mem_singleton_iff.mp p.2).trans (Set.mem_singleton_iff.mp q.2).symm)
        rw [hEq]
      · -- Star fiber centered at `Sum.inl x.1`.
        set F := {s : V ⊕ E | φ s = some (Sum.inr (Sum.inr x))}
        have hxF : Sum.inl x.1 ∈ F := by
          change φ (Sum.inl x.1) = some (Sum.inr (Sum.inr x))
          simp [φ, x.2]
        have : Nonempty F := ⟨⟨Sum.inl x.1, hxF⟩⟩
        refine ⟨fun p q => ?_⟩
        have hto : ∀ r : F, ((subdivGraph M).induce F).Reachable ⟨Sum.inl x.1, hxF⟩ r := by
          intro r
          rcases hr : r.1 with a | e
          · have hφr : φ (Sum.inl a) = some (Sum.inr (Sum.inr x)) := hr ▸ r.2
            by_cases ha : c a = i
            · simp only [φ, ha, ↓reduceDIte] at hφr
              have hax : a = x.1 :=
                congrArg Subtype.val (Sum.inr.inj (Sum.inr.inj (Option.some.inj hφr)))
              have hEq : (⟨Sum.inl x.1, hxF⟩ : F) = r := Subtype.ext (by rw [hr, hax])
              rw [hEq]
            · simp [φ, ha] at hφr
          · have hφr : φ (Sum.inr e) = some (Sum.inr (Sum.inr x)) := hr ▸ r.2
            have hinc : M.e₁ e = x.1 ∨ M.e₂ e = x.1 := by
              by_cases h1 : c (M.e₁ e) = i
              · simp only [φ, h1, ↓reduceDIte] at hφr
                exact Or.inl
                  (congrArg Subtype.val (Sum.inr.inj (Sum.inr.inj (Option.some.inj hφr))))
              · by_cases h2 : c (M.e₂ e) = i
                · simp only [φ, h1, h2, ↓reduceDIte] at hφr
                  exact Or.inr
                    (congrArg Subtype.val (Sum.inr.inj (Sum.inr.inj (Option.some.inj hφr))))
                · simp [φ, h1, h2] at hφr
            have hadj : ((subdivGraph M).induce F).Adj ⟨Sum.inl x.1, hxF⟩ r := by
              change (subdivGraph M).Adj (Sum.inl x.1) r.1
              rw [hr]
              exact hinc
            exact hadj.reachable
        exact (hto p).symm.trans (hto q)
    · -- Lift edges of `subdivGraph M'`.
      have hlift_link : ∀ {b : C} (hib : i ≠ b) (link : ColorLink M c i b) (x : Ci),
          ∃ s₁ s₂ : V ⊕ E,
            φ s₁ = some (Sum.inr (Sum.inr x)) ∧
            φ s₂ = some (Sum.inl ⟨link.nbr x, (link.nbr_color x).symm ▸ hib.symm⟩) ∧
            (subdivGraph M).Adj s₁ s₂ := by
        intro b hib link x
        cases htag : link.tagOpt with
        | none =>
          have hsol : M.solid.Adj x.1 (link.nbr x) :=
            (link.solid_iff x (link.nbr x) (link.nbr_color x)).mpr ⟨htag, rfl⟩
          refine ⟨Sum.inl x.1, Sum.inl (link.nbr x), ?_, ?_, hsol⟩
          · simp [φ, x.2]
          · have hne : c (link.nbr x) ≠ i := (link.nbr_color x).symm ▸ hib.symm
            simp [φ, hne]
        | some t₀ =>
          obtain ⟨e, ⟨-, hconn⟩, -⟩ := link.dashed_unique t₀ htag x
          have hφe : φ (Sum.inr e) = some (Sum.inr (Sum.inr x)) := by
            rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have h1i : c (M.e₁ e) = i := h1.symm ▸ x.2
              simp only [φ, h1i, ↓reduceDIte]
              congr 3; exact Subtype.ext h1
            · have h1ni : c (M.e₁ e) ≠ i := h1.symm ▸ ((link.nbr_color x).symm ▸ hib.symm)
              have h2i : c (M.e₂ e) = i := h2.symm ▸ x.2
              simp only [φ, h1ni, h2i, ↓reduceDIte]
              congr 3; exact Subtype.ext h2
          have hadj : (subdivGraph M).Adj (Sum.inr e) (Sum.inl (link.nbr x)) := by
            rcases hconn with ⟨_, h2⟩ | ⟨h1, _⟩
            · exact Or.inr h2
            · exact Or.inl h1
          have hne : c (link.nbr x) ≠ i := (link.nbr_color x).symm ▸ hib.symm
          exact ⟨Sum.inr e, Sum.inl (link.nbr x), hφe, by simp [φ, hne], hadj⟩
      intro s₁ s₂ hs₁₂
      rcases s₁ with u | (eo | x) <;> rcases s₂ with w | (eo' | x')
      · exact ⟨Sum.inl u.1, Sum.inl w.1, by simp [φ, u.2], by simp [φ, w.2], hs₁₂⟩
      · refine ⟨Sum.inl u.1, Sum.inr eo'.1, by simp [φ, u.2], by simp [φ, eo'.2.1, eo'.2.2], ?_⟩
        rcases hs₁₂ with h1 | h2
        · exact Or.inl (congrArg Subtype.val h1)
        · exact Or.inr (congrArg Subtype.val h2)
      · rcases hs₁₂ with h1 | h2
        · obtain ⟨p, q, hp, hq, hpq⟩ := hlift_link hij link₁ x'
          have huEq : u = ⟨link₁.nbr x', (link₁.nbr_color x').symm ▸ hij.symm⟩ := h1.symm
          exact ⟨q, p, huEq ▸ hq, hp, hpq.symm⟩
        · obtain ⟨p, q, hp, hq, hpq⟩ := hlift_link hiℓ link₂ x'
          have huEq : u = ⟨link₂.nbr x', (link₂.nbr_color x').symm ▸ hiℓ.symm⟩ := h2.symm
          exact ⟨q, p, huEq ▸ hq, hp, hpq.symm⟩
      · refine ⟨Sum.inr eo.1, Sum.inl w.1, by simp [φ, eo.2.1, eo.2.2], by simp [φ, w.2], ?_⟩
        rcases hs₁₂ with h1 | h2
        · exact Or.inl (congrArg Subtype.val h1)
        · exact Or.inr (congrArg Subtype.val h2)
      · exact False.elim hs₁₂
      · exact False.elim hs₁₂
      · rcases hs₁₂ with h1 | h2
        · obtain ⟨p, q, hp, hq, hpq⟩ := hlift_link hij link₁ x
          have hwEq : w = ⟨link₁.nbr x, (link₁.nbr_color x).symm ▸ hij.symm⟩ := h1.symm
          exact ⟨p, q, hp, hwEq ▸ hq, hpq⟩
        · obtain ⟨p, q, hp, hq, hpq⟩ := hlift_link hiℓ link₂ x
          have hwEq : w = ⟨link₂.nbr x, (link₂.nbr_color x).symm ▸ hiℓ.symm⟩ := h2.symm
          exact ⟨p, q, hp, hwEq ▸ hq, hpq⟩
      · exact False.elim hs₁₂
      · exact False.elim hs₁₂
  -- 3. Surjectivity and equitability of `c'` on `M'`.
  have hSurj' : Function.Surjective c' := by
    intro a
    obtain ⟨u, hu⟩ := hSurj a.1
    exact ⟨⟨u, hu.symm ▸ a.2⟩, Subtype.ext hu⟩
  have heq' : IsMixedEquitable M' c' := by
    refine ⟨fun u w huw b => ?_, fun u w huw b t' => ?_⟩
    · have hbij : ∀ x : V', solidCountAt M' c' x b = solidCountAt M c x.1 b.1 := by
        intro x
        apply ncard_eq_of_bij (fun r : V' => r.1)
        · rintro r ⟨hadj, hr⟩; exact ⟨hadj, congrArg Subtype.val hr⟩
        · intro r₁ _ r₂ _ h; exact Subtype.ext h
        · rintro r ⟨hadj, hr⟩
          exact ⟨⟨r, hr.symm ▸ b.2⟩, ⟨hadj, Subtype.ext hr⟩, rfl⟩
      rw [hbij u, hbij w]
      exact heq.1 u.1 w.1 (congrArg Subtype.val huw) b.1
    · cases t' with
      | some t =>
        have hbij : ∀ x : V', dashedCountAt M' c' x b (some t) = dashedCountAt M c x.1 b.1 t := by
          intro x
          refine Set.ncard_congr
            (fun e (he : e ∈ {e : E' | M'.tag e = some t ∧ ∃ y, M'.connects e x y ∧ c' y = b}) =>
              match e, he with
              | Sum.inl eo, _ => eo.1
              | Sum.inr _, h => False.elim (by simp [M'] at h)) ?_ ?_ ?_
          · rintro (eo | r) ⟨ht, y, hconn, hyb⟩
            · have ht' : M.tag eo.1 = t := Option.some.inj ht
              rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact ⟨ht', y.1, Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩,
                  congrArg Subtype.val hyb⟩
              · exact ⟨ht', y.1, Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩,
                  congrArg Subtype.val hyb⟩
            · simp [M'] at ht
          · rintro (eo₁ | r₁) (eo₂ | r₂) ⟨ht₁, _⟩ ⟨ht₂, _⟩ hEq
            · exact congrArg Sum.inl (Subtype.ext hEq)
            · simp [M'] at ht₂
            · simp [M'] at ht₁
            · simp [M'] at ht₁
          · rintro e ⟨ht, y, hconn, hyb⟩
            have he' : c (M.e₁ e) ≠ i ∧ c (M.e₂ e) ≠ i := by
              rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact ⟨h1.symm ▸ x.2, h2.symm ▸ (hyb.symm ▸ b.2)⟩
              · exact ⟨h1.symm ▸ (hyb.symm ▸ b.2), h2.symm ▸ x.2⟩
            refine ⟨Sum.inl ⟨e, he'⟩, ⟨congrArg some ht, ⟨y, hyb.symm ▸ b.2⟩, ?_, Subtype.ext hyb⟩,
              rfl⟩
            rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
            · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
        rw [hbij u, hbij w]
        exact heq.2 u.1 w.1 (congrArg Subtype.val huw) b.1 t
      | none =>
        have hcu_eq : c u.1 = c w.1 := congrArg Subtype.val huw
        by_cases hcase1 : c u.1 = j ∧ b.1 = ℓ
        · have hbij : ∀ x : V', c x.1 = j →
              dashedCountAt M' c' x b none = Set.ncard {r : Ci | link₁.nbr r = x.1} := by
            intro x hxj
            apply ncard_eq_of_bij (fun e : E' =>
              match e with | Sum.inr r => r | Sum.inl _ => ⟨v, hv⟩)
            · rintro (eo | r) ⟨ht, y, hconn, hyb⟩
              · simp [M'] at ht
              · rcases hconn with ⟨h1, _⟩ | ⟨_, h2⟩
                · exact congrArg Subtype.val h1
                · have hxz : link₂.nbr r = x.1 := congrArg Subtype.val h2
                  exact absurd
                    ((link₂.nbr_color r).symm.trans ((congrArg c hxz).trans hxj)) hjℓ.symm
            · rintro (eo₁ | r₁) ⟨ht₁, _⟩ (eo₂ | r₂) ⟨ht₂, _⟩ hEq
              · simp [M'] at ht₁
              · simp [M'] at ht₁
              · simp [M'] at ht₂
              · exact congrArg Sum.inr hEq
            · intro r hr
              refine ⟨Sum.inr r, ⟨rfl, zOf r, Or.inl ⟨Subtype.ext hr, rfl⟩,
                Subtype.ext ((link₂.nbr_color r).trans hcase1.2.symm)⟩, rfl⟩
          rw [hbij u hcase1.1, hbij w (hcu_eq.symm.trans hcase1.1)]
          have hu_cnt := card_colorLink_preimage_eq M c hij link₁ u.1 hcase1.1
          have hw_cnt := card_colorLink_preimage_eq M c hij link₁ w.1 (hcu_eq.symm.trans hcase1.1)
          cases htag : link₁.tagOpt
          · rw [htag] at hu_cnt hw_cnt; rw [hu_cnt, hw_cnt]; exact heq.1 u.1 w.1 hcu_eq i
          · rw [htag] at hu_cnt hw_cnt; rw [hu_cnt, hw_cnt]; exact heq.2 u.1 w.1 hcu_eq i _
        · by_cases hcase2 : c u.1 = ℓ ∧ b.1 = j
          · have hbij : ∀ x : V', c x.1 = ℓ →
                dashedCountAt M' c' x b none = Set.ncard {r : Ci | link₂.nbr r = x.1} := by
              intro x hxℓ
              apply ncard_eq_of_bij (fun e : E' =>
                match e with | Sum.inr r => r | Sum.inl _ => ⟨v, hv⟩)
              · rintro (eo | r) ⟨ht, y, hconn, hyb⟩
                · simp [M'] at ht
                · rcases hconn with ⟨h1, _⟩ | ⟨_, h2⟩
                  · have hxy : link₁.nbr r = x.1 := congrArg Subtype.val h1
                    exact absurd ((link₁.nbr_color r).symm.trans ((congrArg c hxy).trans hxℓ)) hjℓ
                  · exact congrArg Subtype.val h2
              · rintro (eo₁ | r₁) ⟨ht₁, _⟩ (eo₂ | r₂) ⟨ht₂, _⟩ hEq
                · simp [M'] at ht₁
                · simp [M'] at ht₁
                · simp [M'] at ht₂
                · exact congrArg Sum.inr hEq
              · intro r hr
                refine ⟨Sum.inr r, ⟨rfl, yOf r, Or.inr ⟨rfl, Subtype.ext hr⟩,
                  Subtype.ext ((link₁.nbr_color r).trans hcase2.2.symm)⟩, rfl⟩
            rw [hbij u hcase2.1, hbij w (hcu_eq.symm.trans hcase2.1)]
            have hu_cnt := card_colorLink_preimage_eq M c hiℓ link₂ u.1 hcase2.1
            have hw_cnt := card_colorLink_preimage_eq M c hiℓ link₂ w.1 (hcu_eq.symm.trans hcase2.1)
            cases htag : link₂.tagOpt
            · rw [htag] at hu_cnt hw_cnt; rw [hu_cnt, hw_cnt]; exact heq.1 u.1 w.1 hcu_eq i
            · rw [htag] at hu_cnt hw_cnt; rw [hu_cnt, hw_cnt]; exact heq.2 u.1 w.1 hcu_eq i _
          · -- All other color pairs have 0 tag-`none` edges.
            have hzero : ∀ x : V', c x.1 = c u.1 → dashedCountAt M' c' x b none = 0 := by
              intro x hxu
              have hemp : {e : E' | M'.tag e = none ∧ ∃ y, M'.connects e x y ∧ c' y = b} = ∅ := by
                ext e; simp only [Set.mem_empty_iff_false, iff_false]
                rintro ⟨ht, y, hconn, hyb⟩
                rcases e with eo | r
                · simp [M'] at ht
                · rcases hconn with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · have hx_j : c x.1 = j := (congrArg (fun a : V' => c a.1) h1).symm.trans
                      (link₁.nbr_color r)
                    have hb_ℓ : b.1 = ℓ := (congrArg Subtype.val hyb).symm.trans
                      ((congrArg (fun a : V' => c a.1) h2).symm.trans (link₂.nbr_color r))
                    exact hcase1 ⟨hxu.symm.trans hx_j, hb_ℓ⟩
                  · have hx_ℓ : c x.1 = ℓ := (congrArg (fun a : V' => c a.1) h2).symm.trans
                      (link₂.nbr_color r)
                    have hb_j : b.1 = j := (congrArg Subtype.val hyb).symm.trans
                      ((congrArg (fun a : V' => c a.1) h1).symm.trans (link₁.nbr_color r))
                    exact hcase2 ⟨hxu.symm.trans hx_ℓ, hb_j⟩
              simp [dashedCountAt, hemp]
            rw [hzero u rfl, hzero w hcu_eq.symm]
  -- 4. Compare `G(\widehat{K}')` with `G(\widehat{K})` via 0, 1, or 2 applications of Lemma 4.
  have himp : IsOuterplanar (subdivGraph (mixedQuotient M' c')) →
      IsOuterplanar (subdivGraph (mixedQuotient M c)) := by
    intro hK'_out
    let GK := subdivGraph (mixedQuotient M c)
    let GK' := subdivGraph (mixedQuotient M' c')
    let j' : C' := ⟨j, hij.symm⟩
    let ℓ' : C' := ⟨ℓ, hiℓ.symm⟩
    have hjℓ' : j' ≠ ℓ' := fun h => hjℓ (congrArg Subtype.val h)
    -- The unique new quotient dashed edge `q_new` of tag `none` in `mixedQuotient M' c'`.
    let q_new : QuotDashedEdge M' c' :=
      ⟨(s(j', ℓ'), none),
        fun hd => hjℓ' (Sym2.mk_isDiag_iff.mp hd),
        ⟨Sum.inr ⟨v, hv⟩, rfl, by
          have h1 : c' (yOf ⟨v, hv⟩) = j' := Subtype.ext (link₁.nbr_color ⟨v, hv⟩)
          have h2 : c' (zOf ⟨v, hv⟩) = ℓ' := Subtype.ext (link₂.nbr_color ⟨v, hv⟩)
          change s(c' (yOf ⟨v, hv⟩), c' (zOf ⟨v, hv⟩)) = s(j', ℓ')
          rw [h1, h2]⟩⟩
    have hq_new_uniq : ∀ q : QuotDashedEdge M' c', q.1.2 = none → q = q_new := by
      intro q hqn
      obtain ⟨e, hte, hse⟩ := q.2.2
      rcases e with eo | r
      · rw [hqn] at hte; simp [M'] at hte
      · apply Subtype.ext
        apply Prod.ext
        · have h1 : c' (yOf r) = j' := Subtype.ext (link₁.nbr_color r)
          have h2 : c' (zOf r) = ℓ' := Subtype.ext (link₂.nbr_color r)
          rw [← hse]
          change s(c' (yOf r), c' (zOf r)) = s(j', ℓ')
          rw [h1, h2]
        · exact hqn
    -- Bijection between `delColorSet M c i` and `GK' \ {Sum.inr q_new}`.
    have hsym2_map_inj : ∀ p₁ p₂ : Sym2 C',
        Sym2.map Subtype.val p₁ = Sym2.map Subtype.val p₂ → p₁ = p₂ := by
      intro p₁ p₂ h
      induction p₁ using Sym2.ind with
      | _ a₁ b₁ =>
        induction p₂ using Sym2.ind with
        | _ a₂ b₂ =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
          · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    let toOldQ : {q : QuotDashedEdge M' c' // q ≠ q_new} → {q : QuotDashedEdge M c // i ∉ q.1.1} :=
      fun q =>
        have hsome : ∃ t : T, q.1.1.2 = some t := by
          cases h : q.1.1.2 with
          | none => exact absurd (hq_new_uniq q.1 h) q.2
          | some t => exact ⟨t, rfl⟩
        let t := Classical.choose hsome
        have ht : q.1.1.2 = some t := Classical.choose_spec hsome
        ⟨⟨(Sym2.map Subtype.val q.1.1.1, t), by
          refine ⟨?_, ?_⟩
          · intro hd
            apply q.1.2.1
            induction h : q.1.1.1 using Sym2.ind with
            | _ a b =>
              rw [h] at hd
              simp only [Sym2.map_mk, Sym2.mk_isDiag_iff] at hd
              exact Sym2.mk_isDiag_iff.mpr (Subtype.ext hd)
          · obtain ⟨e, hte, hse⟩ := q.1.2.2
            rcases e with eo | r
            · have htag : M.tag eo.1 = t := Option.some.inj (hte.trans ht)
              refine ⟨eo.1, htag, ?_⟩
              rw [← hse]
              simp [M', c']
            · simp [M', ht] at hte⟩,
          by
            intro hi
            obtain ⟨a, _, ha⟩ := Sym2.mem_map.mp hi
            exact a.2 ha⟩
    let fromOldQ :
        {q : QuotDashedEdge M c // i ∉ q.1.1} → {q : QuotDashedEdge M' c' // q ≠ q_new} :=
      fun q =>
        let ab := sym2Endpoints q.1.1.1 q.1.2.1
        have ha : ab.1.1 ≠ i := fun hEq =>
          q.2 (by rw [← ab.2.2, Sym2.mem_iff]; exact Or.inl hEq.symm)
        have hb : ab.1.2 ≠ i := fun hEq =>
          q.2 (by rw [← ab.2.2, Sym2.mem_iff]; exact Or.inr hEq.symm)
        ⟨⟨(s(⟨ab.1.1, ha⟩, ⟨ab.1.2, hb⟩), some q.1.1.2), by
          refine ⟨?_, ?_⟩
          · intro hd; exact ab.2.1 (congrArg Subtype.val (Sym2.mk_isDiag_iff.mp hd))
          · obtain ⟨e, hte, hse⟩ := q.1.2.2
            have he1 : c (M.e₁ e) ≠ i := fun hEq => q.2 (hEq ▸ hse ▸ Sym2.mem_mk_left _ _)
            have he2 : c (M.e₂ e) ≠ i := fun hEq => q.2 (hEq ▸ hse ▸ Sym2.mem_mk_right _ _)
            refine ⟨Sum.inl ⟨e, he1, he2⟩, congrArg some hte, ?_⟩
            have hpair : s(c (M.e₁ e), c (M.e₂ e)) = s(ab.1.1, ab.1.2) := hse.trans ab.2.2.symm
            rcases Sym2.eq_iff.mp hpair with ⟨k1, k2⟩ | ⟨k1, k2⟩
            · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext k1, Subtype.ext k2⟩)
            · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext k1, Subtype.ext k2⟩)⟩,
          fun hEq => by
            have := congrArg (fun r : QuotDashedEdge M' c' => r.1.2) hEq
            simp [q_new] at this⟩
    have htoOld_pair : ∀ q : {q : QuotDashedEdge M' c' // q ≠ q_new},
        (toOldQ q).1.1.1 = Sym2.map Subtype.val q.1.1.1 := fun _ => rfl
    have hfromOld_pair : ∀ q : {q : QuotDashedEdge M c // i ∉ q.1.1},
        Sym2.map Subtype.val (fromOldQ q).1.1.1 = q.1.1.1 := by
      intro q
      change Sym2.map Subtype.val s(_, _) = q.1.1.1
      rw [Sym2.map_mk]
      exact (sym2Endpoints q.1.1.1 q.1.2.1).2.2
    have hto_from : ∀ q : {q : QuotDashedEdge M c // i ∉ q.1.1}, toOldQ (fromOldQ q) = q := by
      intro q
      apply Subtype.ext; apply Subtype.ext; apply Prod.ext
      · exact hfromOld_pair q
      · have hsome : ∃ t : T, (fromOldQ q).1.1.2 = some t := ⟨q.1.1.2, rfl⟩
        have hspec := Classical.choose_spec (show ∃ t : T, (fromOldQ q).1.1.2 = some t from hsome)
        exact (Option.some.inj hspec).symm
    have hfrom_to : ∀ q : {q : QuotDashedEdge M' c' // q ≠ q_new}, fromOldQ (toOldQ q) = q := by
      intro q
      apply Subtype.ext; apply Subtype.ext; apply Prod.ext
      · apply hsym2_map_inj
        exact hfromOld_pair (toOldQ q)
      · have hsome : ∃ t : T, q.1.1.2 = some t := by
          cases h : q.1.1.2 with
          | none => exact absurd (hq_new_uniq q.1 h) q.2
          | some t => exact ⟨t, rfl⟩
        exact (Classical.choose_spec hsome).symm
    -- Universal builder: given any graph `H` on vertex type `U` with a distinguished vertex `s : U`
    -- whose neighbors are `{u_j, u_ℓ}` and an equiv `f : (delColorSet M c i) ≃ {u : U // u ≠ s}`
    -- preserving all edges inside `delColorSet M c i` and mapping `Sum.inl j ↦ u_j`,
    -- `Sum.inl ℓ ↦ u_ℓ`, we obtain `H ≃g GK'`, hence `IsOuterplanar H`!
    have hiso_from_del : ∀ {U : Type} (H : SimpleGraph U) (s : U)
        (toU : ↥(delColorSet M c i) → {u : U // u ≠ s})
        (fromU : {u : U // u ≠ s} → ↥(delColorSet M c i)),
        (∀ x, fromU (toU x) = x) →
        (∀ u, toU (fromU u) = u) →
        (∀ x y, H.Adj (toU x).1 (toU y).1 ↔ GK.Adj x.1 y.1) →
        (∀ u : U, H.Adj s u ↔
          u = (toU ⟨Sum.inl j, hij.symm⟩).1 ∨ u = (toU ⟨Sum.inl ℓ, hiℓ.symm⟩).1) →
        IsOuterplanar H := by
      intro U H s toU fromU hleft hright hadj_old hadj_s
      let d2k : ↥(delColorSet M c i) → C' ⊕ QuotDashedEdge M' c' :=
        fun ⟨x, hx⟩ => match x, hx with
        | Sum.inl a, ha => Sum.inl ⟨a, ha⟩
        | Sum.inr q, hq => Sum.inr (fromOldQ ⟨q, hq⟩).1
      let k2d : {y : C' ⊕ QuotDashedEdge M' c' // y ≠ Sum.inr q_new} →
          ↥(delColorSet M c i) :=
        fun ⟨y, hy⟩ => match y, hy with
        | Sum.inl a, _ => ⟨Sum.inl a.1, a.2⟩
        | Sum.inr q, hq =>
          have hq' : q ≠ q_new := fun h => hq (congrArg Sum.inr h)
          ⟨Sum.inr (toOldQ ⟨q, hq'⟩).1, (toOldQ ⟨q, hq'⟩).2⟩
      have hd2k_ne : ∀ x, d2k x ≠ Sum.inr q_new := by
        rintro ⟨a | q, hx⟩
        · simp [d2k]
        · simp only [d2k, ne_eq, Sum.inr.injEq]
          exact (fromOldQ ⟨q, hx⟩).2
      have hk2d_d2k : ∀ x, k2d ⟨d2k x, hd2k_ne x⟩ = x := by
        rintro ⟨a | q, hx⟩
        · rfl
        · apply Subtype.ext
          simp only [d2k, k2d]
          congr 1
          exact congrArg Subtype.val (hto_from ⟨q, hx⟩)
      have hd2k_k2d : ∀ y : {y : C' ⊕ QuotDashedEdge M' c' // y ≠ Sum.inr q_new},
          d2k (k2d y) = y.1 := by
        rintro ⟨a | q, hy⟩
        · rfl
        · have hq : q ≠ q_new := fun h => hy (congrArg Sum.inr h)
          simp only [k2d, d2k]
          congr 1
          exact congrArg Subtype.val (hfrom_to ⟨q, hq⟩)
      have hd2k_adj : ∀ x y : ↥(delColorSet M c i),
          GK'.Adj (d2k x) (d2k y) ↔ GK.Adj x.1 y.1 := by
        rintro ⟨a | q, hx⟩ ⟨b | q', hy⟩
        · change (mixedQuotient M' c').solid.Adj ⟨a, hx⟩ ⟨b, hy⟩ ↔
            (mixedQuotient M c).solid.Adj a b
          constructor
          · rintro ⟨hab, u, w, hu, hw, huw⟩
            exact ⟨fun h => hab (Subtype.ext h), u.1, w.1, congrArg Subtype.val hu,
              congrArg Subtype.val hw, huw⟩
          · rintro ⟨hab, u, w, hu, hw, huw⟩
            exact ⟨fun h => hab (congrArg Subtype.val h), ⟨u, hu.symm ▸ hx⟩, ⟨w, hw.symm ▸ hy⟩,
              Subtype.ext hu, Subtype.ext hw, huw⟩
        · change (GK'.Adj (Sum.inl ⟨a, hx⟩) (Sum.inr (fromOldQ ⟨q', hy⟩).1)) ↔
            GK.Adj (Sum.inl a) (Sum.inr q')
          simp only [GK', GK, subdivGraph_mixedQuotient_adj_inl_inr]
          have hpair := hfromOld_pair ⟨q', hy⟩
          rw [← hpair]
          constructor
          · intro hmem; exact Sym2.mem_map.mpr ⟨⟨a, hx⟩, hmem, rfl⟩
          · intro hmem
            obtain ⟨a', ha', hval⟩ := Sym2.mem_map.mp hmem
            have hsub : a' = ⟨a, hx⟩ := Subtype.ext hval
            exact hsub ▸ ha'
        · change (GK'.Adj (Sum.inr (fromOldQ ⟨q, hx⟩).1) (Sum.inl ⟨b, hy⟩)) ↔
            GK.Adj (Sum.inr q) (Sum.inl b)
          simp only [GK', GK, subdivGraph_mixedQuotient_adj_inr_inl]
          have hpair := hfromOld_pair ⟨q, hx⟩
          rw [← hpair]
          constructor
          · intro hmem; exact Sym2.mem_map.mpr ⟨⟨b, hy⟩, hmem, rfl⟩
          · intro hmem
            obtain ⟨b', hb', hval⟩ := Sym2.mem_map.mp hmem
            have hsub : b' = ⟨b, hy⟩ := Subtype.ext hval
            exact hsub ▸ hb'
        · exact Iff.rfl
      have hGK'_qnew_adj : ∀ y : C' ⊕ QuotDashedEdge M' c',
          GK'.Adj (Sum.inr q_new) y ↔ y = Sum.inl j' ∨ y = Sum.inl ℓ' := by
        intro y
        rcases y with a | q
        · rw [subdivGraph_mixedQuotient_adj_inr_inl]
          change a ∈ s(j', ℓ') ↔ Sum.inl a = Sum.inl j' ∨ Sum.inl a = Sum.inl ℓ'
          simp [Sym2.mem_iff]
        · simp [GK', subdivGraph]
      let eIso : H ≃g GK' :=
        { toFun := fun u =>
            if hu : u = s then Sum.inr q_new else d2k (fromU ⟨u, hu⟩)
          invFun := fun y =>
            if hy : y = Sum.inr q_new then s else (toU (k2d ⟨y, hy⟩)).1
          left_inv := fun u => by
            by_cases hu : u = s
            · simp [hu]
            · simp only [hu, ↓reduceDIte, hd2k_ne, hk2d_d2k, hright]
          right_inv := fun y => by
            by_cases hy : y = Sum.inr q_new
            · simp [hy]
            · have hne : (toU (k2d ⟨y, hy⟩)).1 ≠ s := (toU (k2d ⟨y, hy⟩)).2
              simp only [hy, ↓reduceDIte, hne, hleft, hd2k_k2d]
          map_rel_iff' := by
            intro u₁ u₂
            change GK'.Adj (if hu : u₁ = s then Sum.inr q_new else d2k (fromU ⟨u₁, hu⟩))
              (if hu : u₂ = s then Sum.inr q_new else d2k (fromU ⟨u₂, hu⟩)) ↔ H.Adj u₁ u₂
            by_cases h1 : u₁ = s <;> by_cases h2 : u₂ = s
            · subst u₁; subst u₂
              simp only [↓reduceDIte]
              exact ⟨fun h => absurd h (GK'.loopless.irrefl _),
                fun h => absurd h (H.loopless.irrefl _)⟩
            · subst u₁
              simp only [↓reduceDIte, h2, hGK'_qnew_adj, hadj_s]
              constructor
              · rintro (hjEq | hℓEq)
                · left
                  have : fromU ⟨u₂, h2⟩ = ⟨Sum.inl j, hij.symm⟩ := by
                    have hsub : (⟨d2k (fromU ⟨u₂, h2⟩), hd2k_ne _⟩ :
                        {y // y ≠ Sum.inr q_new}) = ⟨Sum.inl j', by simp⟩ := Subtype.ext hjEq
                    have := congrArg k2d hsub
                    simpa [hk2d_d2k, k2d] using this
                  have hto := congrArg (fun r => (toU r).1) this
                  simpa [hright] using hto
                · right
                  have : fromU ⟨u₂, h2⟩ = ⟨Sum.inl ℓ, hiℓ.symm⟩ := by
                    have hsub : (⟨d2k (fromU ⟨u₂, h2⟩), hd2k_ne _⟩ :
                        {y // y ≠ Sum.inr q_new}) = ⟨Sum.inl ℓ', by simp⟩ := Subtype.ext hℓEq
                    have := congrArg k2d hsub
                    simpa [hk2d_d2k, k2d] using this
                  have hto := congrArg (fun r => (toU r).1) this
                  simpa [hright] using hto
              · rintro (hjEq | hℓEq)
                · left
                  have hsub : (⟨u₂, h2⟩ : {u : U // u ≠ s}) = toU ⟨Sum.inl j, hij.symm⟩ :=
                    Subtype.ext hjEq
                  rw [hsub, hleft]
                · right
                  have hsub : (⟨u₂, h2⟩ : {u : U // u ≠ s}) = toU ⟨Sum.inl ℓ, hiℓ.symm⟩ :=
                    Subtype.ext hℓEq
                  rw [hsub, hleft]
            · subst u₂
              simp only [h1, ↓reduceDIte]
              rw [SimpleGraph.adj_comm, hGK'_qnew_adj, SimpleGraph.adj_comm (G := H), hadj_s]
              constructor
              · rintro (hjEq | hℓEq)
                · left
                  have : fromU ⟨u₁, h1⟩ = ⟨Sum.inl j, hij.symm⟩ := by
                    have hsub : (⟨d2k (fromU ⟨u₁, h1⟩), hd2k_ne _⟩ :
                        {y // y ≠ Sum.inr q_new}) = ⟨Sum.inl j', by simp⟩ := Subtype.ext hjEq
                    have := congrArg k2d hsub
                    simpa [hk2d_d2k, k2d] using this
                  have hto := congrArg (fun r => (toU r).1) this
                  simpa [hright] using hto
                · right
                  have : fromU ⟨u₁, h1⟩ = ⟨Sum.inl ℓ, hiℓ.symm⟩ := by
                    have hsub : (⟨d2k (fromU ⟨u₁, h1⟩), hd2k_ne _⟩ :
                        {y // y ≠ Sum.inr q_new}) = ⟨Sum.inl ℓ', by simp⟩ := Subtype.ext hℓEq
                    have := congrArg k2d hsub
                    simpa [hk2d_d2k, k2d] using this
                  have hto := congrArg (fun r => (toU r).1) this
                  simpa [hright] using hto
              · rintro (hjEq | hℓEq)
                · left
                  have hsub : (⟨u₁, h1⟩ : {u : U // u ≠ s}) = toU ⟨Sum.inl j, hij.symm⟩ :=
                    Subtype.ext hjEq
                  rw [hsub, hleft]
                · right
                  have hsub : (⟨u₁, h1⟩ : {u : U // u ≠ s}) = toU ⟨Sum.inl ℓ, hiℓ.symm⟩ :=
                    Subtype.ext hℓEq
                  rw [hsub, hleft]
            · simp only [h1, h2, ↓reduceDIte, hd2k_adj]
              have hEq1 : (toU (fromU ⟨u₁, h1⟩)).1 = u₁ := congrArg Subtype.val (hright _)
              have hEq2 : (toU (fromU ⟨u₂, h2⟩)).1 = u₂ := congrArg Subtype.val (hright _)
              simpa [hEq1, hEq2] using (hadj_old (fromU ⟨u₁, h1⟩) (fromU ⟨u₂, h2⟩)).symm }
      exact (isOuterplanar_iff_of_iso eIso).mpr hK'_out
    -- Characterize quotient edges between `i` and `b ∈ {j, ℓ}` from `ColorLink`.
    have hlink_quot : ∀ {b : C} (hib : i ≠ b) (link : ColorLink M c i b),
        match link.tagOpt with
        | none =>
          (mixedQuotient M c).solid.Adj i b ∧
          ∀ q : QuotDashedEdge M c, q.1.1 ≠ s(i, b)
        | some t₀ =>
          ¬ (mixedQuotient M c).solid.Adj i b ∧
          ∃ q₀ : QuotDashedEdge M c, q₀.1 = (s(i, b), t₀) ∧
            ∀ q : QuotDashedEdge M c, q.1.1 = s(i, b) → q = q₀ := by
      intro b hib link
      cases htag : link.tagOpt with
      | none =>
        refine ⟨?_, ?_⟩
        · have hsol := (link.solid_iff ⟨v, hv⟩ (link.nbr ⟨v, hv⟩) (link.nbr_color ⟨v, hv⟩)).mpr
            ⟨htag, rfl⟩
          exact ⟨hib, v, link.nbr ⟨v, hv⟩, hv, link.nbr_color ⟨v, hv⟩, hsol⟩
        · intro q hq
          obtain ⟨e, w, -, hconn, hwb⟩ := exists_dashed_of_quot_edge heq hq hv
          have h := (link.dashed_only ⟨v, hv⟩ e w hwb hconn).1
          rw [htag] at h; simp at h
      | some t₀ =>
        refine ⟨?_, ?_⟩
        · intro hadj
          obtain ⟨w, hsol, hwb⟩ := exists_solid_of_quot_adj heq hadj hv
          have h := ((link.solid_iff ⟨v, hv⟩ w hwb).mp hsol).1
          rw [htag] at h; simp at h
        · obtain ⟨e₀, ⟨ht₀, hconn₀⟩, -⟩ := link.dashed_unique t₀ htag ⟨v, hv⟩
          have hpair₀ : s(c (M.e₁ e₀), c (M.e₂ e₀)) = s(i, b) := by
            rcases hconn₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2, hv, link.nbr_color]
            · rw [h1, h2, link.nbr_color, hv, Sym2.eq_swap]
          let q₀ : QuotDashedEdge M c :=
            ⟨(s(i, b), t₀), fun hd => hib (Sym2.mk_isDiag_iff.mp hd), ⟨e₀, ht₀, hpair₀⟩⟩
          refine ⟨q₀, rfl, fun q hq => ?_⟩
          obtain ⟨e, w, hte, hconn, hwb⟩ := exists_dashed_of_quot_edge heq hq hv
          have htag_e := (link.dashed_only ⟨v, hv⟩ e w hwb hconn).1
          rw [htag] at htag_e
          have htEq : q.1.2 = t₀ := hte.symm.trans (Option.some.inj htag_e).symm
          exact Subtype.ext (Prod.ext hq htEq)
    have hq1 := hlink_quot hij link₁
    have hq2 := hlink_quot hiℓ link₂
    -- Case split on `(link₁.tagOpt, link₂.tagOpt)` (4 cases: L = 2, 3, 3, 4).
    cases htag₁ : link₁.tagOpt <;> cases htag₂ : link₂.tagOpt
    · -- Case L = 2: both solid.
      rw [htag₁] at hq1; rw [htag₂] at hq2
      have hno_qi : ∀ q : QuotDashedEdge M c, i ∉ q.1.1 := by
        intro q hiq
        rcases hno_other_dash q hiq with h1 | h2
        · exact hq1.2 q h1
        · exact hq2.2 q h2
      have hdel_eq : ∀ x : C ⊕ QuotDashedEdge M c, x ∈ delColorSet M c i ↔ x ≠ Sum.inl i := by
        intro x
        rcases x with a | q
        · simp [delColorSet]
        · simp [delColorSet, hno_qi q]
      refine hiso_from_del GK (Sum.inl i)
        (fun x => ⟨x.1, (hdel_eq x.1).mp x.2⟩)
        (fun u => ⟨u.1, (hdel_eq u.1).mpr u.2⟩)
        (fun _ => Subtype.ext rfl) (fun _ => Subtype.ext rfl)
        (fun _ _ => Iff.rfl) ?_
      intro u
      rcases u with b | q
      · constructor
        · intro hadj
          by_cases hbj : b = j
          · exact Or.inl (congrArg Sum.inl hbj)
          by_cases hbℓ : b = ℓ
          · exact Or.inr (congrArg Sum.inl hbℓ)
          exact absurd hadj (hno_other_sol b hbj hbℓ)
        · rintro (hEq | hEq)
          · rw [Sum.inl.inj hEq]; exact hq1.1
          · rw [Sum.inl.inj hEq]; exact hq2.1
      · simp only [GK, subdivGraph_mixedQuotient_adj_inl_inr, hno_qi q, false_iff, not_or]
        exact ⟨by simp, by simp⟩
    · -- Case L = 3 (j solid, ℓ dashed with q₂).
      rename_i t₂
      rw [htag₁] at hq1; rw [htag₂] at hq2
      obtain ⟨q₂, hq₂_val, hq₂_uniq⟩ := hq2.2
      have hq₂_pair : q₂.1.1 = s(i, ℓ) := congrArg Prod.fst hq₂_val
      have hqi_eq : ∀ q : QuotDashedEdge M c, i ∈ q.1.1 → q = q₂ := by
        intro q hiq
        rcases hno_other_dash q hiq with h1 | h2
        · exact absurd h1 (hq1.2 q)
        · exact hq₂_uniq q h2
      have hq₂_adj : ∀ z : C ⊕ QuotDashedEdge M c,
          GK.Adj (Sum.inr q₂) z ↔ z = Sum.inl ℓ ∨ z = Sum.inl i := by
        intro z
        rcases z with b | q
        · rw [subdivGraph_mixedQuotient_adj_inr_inl, hq₂_pair, Sym2.mem_iff]
          simp [or_comm]
        · simp [GK, subdivGraph]
      have hi_adj : ∀ z : C ⊕ QuotDashedEdge M c,
          GK.Adj (Sum.inl i) z ↔ z = Sum.inr q₂ ∨ z = Sum.inl j := by
        intro z
        rcases z with b | q
        · constructor
          · intro hadj
            by_cases hbj : b = j
            · exact Or.inr (congrArg Sum.inl hbj)
            by_cases hbℓ : b = ℓ
            · exact absurd (hbℓ ▸ hadj) hq2.1
            exact absurd hadj (hno_other_sol b hbj hbℓ)
          · rintro (h | h)
            · simp at h
            · rw [Sum.inl.inj h]; exact hq1.1
        · rw [subdivGraph_mixedQuotient_adj_inl_inr]
          constructor
          · intro hiq; exact Or.inl (congrArg Sum.inr (hqi_eq q hiq))
          · rintro (h | h)
            · rw [Sum.inr.inj h, hq₂_pair]; exact Sym2.mem_mk_left i ℓ
            · simp at h
      -- Contract `Sum.inr q₂ ~ Sum.inl i` via Lemma 4.
      have hXc_out : IsOuterplanar (contractEdgeGraph GK (Sum.inr q₂) (Sum.inl i) (Sum.inl j)
          (by simp)) := by
        let Xc := contractEdgeGraph GK (Sum.inr q₂) (Sum.inl i) (Sum.inl j) (by simp)
        let s_c : {x : C ⊕ QuotDashedEdge M c // x ≠ Sum.inl i} := ⟨Sum.inr q₂, by simp⟩
        have hdel_iff : ∀ u : {x : C ⊕ QuotDashedEdge M c // x ≠ Sum.inl i},
            u.1 ∈ delColorSet M c i ↔ u ≠ s_c := by
          intro u
          rcases hu : u.1 with b | q
          · have hbi : b ≠ i := fun h => u.2 (hu.trans (congrArg Sum.inl h))
            simp [delColorSet, s_c, Subtype.ext_iff, hu, hbi]
          · simp only [delColorSet, s_c, ne_eq, Subtype.ext_iff, hu, Sum.inr.injEq]
            exact ⟨fun hni hEq => hni (Subtype.ext hEq ▸ hq₂_pair ▸ Sym2.mem_mk_left i ℓ),
              fun hne hiq => hne (congrArg Subtype.val (hqi_eq q hiq))⟩
        refine hiso_from_del Xc s_c
          (fun x => ⟨⟨x.1, fun hEq => by
            have := x.2; rw [hEq] at this; exact this rfl⟩,
            (hdel_iff _).mp x.2⟩)
          (fun u => ⟨u.1.1, (hdel_iff u.1).mpr u.2⟩)
          (fun _ => Subtype.ext rfl) (fun _ => Subtype.ext (Subtype.ext rfl))
          ?_ ?_
        · intro x y
          have hxq₂ : x.1 ≠ Sum.inr q₂ := fun hEq =>
            (hdel_iff ⟨x.1, fun h => by have := x.2; rw [h] at this; exact this rfl⟩).mp x.2
              (Subtype.ext hEq)
          have hyq₂ : y.1 ≠ Sum.inr q₂ := fun hEq =>
            (hdel_iff ⟨y.1, fun h => by have := y.2; rw [h] at this; exact this rfl⟩).mp y.2
              (Subtype.ext hEq)
          constructor
          · rintro (h | ⟨h1, _⟩ | ⟨_, h2⟩)
            · exact h
            · exact absurd h1 hxq₂
            · exact absurd h2 hyq₂
          · intro h; exact Or.inl h
        · intro u
          constructor
          · rintro (h | ⟨_, h2⟩ | ⟨h1, _⟩)
            · rcases (hq₂_adj u.1).mp h with hℓ | hi'
              · exact Or.inr (Subtype.ext hℓ)
              · exact absurd hi' u.2
            · exact Or.inl (Subtype.ext h2)
            · simp at h1
          · rintro (rfl | rfl)
            · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
            · exact Or.inl ((hq₂_adj (Sum.inl ℓ)).mpr (Or.inl rfl))
      exact isOuterplanar_of_contract_adj_deg2
        (u := Sum.inl ℓ) (a := Sum.inr q₂) (b := Sum.inl i) (w := Sum.inl j)
        (fun h => hjℓ.symm (Sum.inl.inj h)) (fun h => hiℓ.symm (Sum.inl.inj h)) (by simp)
        hq₂_adj hi_adj hXc_out
    · -- Case L = 3 (j dashed with q₁, ℓ solid).
      rename_i t₁
      rw [htag₁] at hq1; rw [htag₂] at hq2
      obtain ⟨q₁, hq₁_val, hq₁_uniq⟩ := hq1.2
      have hq₁_pair : q₁.1.1 = s(i, j) := congrArg Prod.fst hq₁_val
      have hqi_eq : ∀ q : QuotDashedEdge M c, i ∈ q.1.1 → q = q₁ := by
        intro q hiq
        rcases hno_other_dash q hiq with h1 | h2
        · exact hq₁_uniq q h1
        · exact absurd h2 (hq2.2 q)
      have hq₁_adj : ∀ z : C ⊕ QuotDashedEdge M c,
          GK.Adj (Sum.inr q₁) z ↔ z = Sum.inl j ∨ z = Sum.inl i := by
        intro z
        rcases z with b | q
        · rw [subdivGraph_mixedQuotient_adj_inr_inl, hq₁_pair, Sym2.mem_iff]
          simp [or_comm]
        · simp [GK, subdivGraph]
      have hi_adj : ∀ z : C ⊕ QuotDashedEdge M c,
          GK.Adj (Sum.inl i) z ↔ z = Sum.inr q₁ ∨ z = Sum.inl ℓ := by
        intro z
        rcases z with b | q
        · constructor
          · intro hadj
            by_cases hbj : b = j
            · exact absurd (hbj ▸ hadj) hq1.1
            by_cases hbℓ : b = ℓ
            · exact Or.inr (congrArg Sum.inl hbℓ)
            exact absurd hadj (hno_other_sol b hbj hbℓ)
          · rintro (h | h)
            · simp at h
            · rw [Sum.inl.inj h]; exact hq2.1
        · rw [subdivGraph_mixedQuotient_adj_inl_inr]
          constructor
          · intro hiq; exact Or.inl (congrArg Sum.inr (hqi_eq q hiq))
          · rintro (h | h)
            · rw [Sum.inr.inj h, hq₁_pair]; exact Sym2.mem_mk_left i j
            · simp at h
      have hXc_out : IsOuterplanar (contractEdgeGraph GK (Sum.inr q₁) (Sum.inl i) (Sum.inl ℓ)
          (by simp)) := by
        let Xc := contractEdgeGraph GK (Sum.inr q₁) (Sum.inl i) (Sum.inl ℓ) (by simp)
        let s_c : {x : C ⊕ QuotDashedEdge M c // x ≠ Sum.inl i} := ⟨Sum.inr q₁, by simp⟩
        have hdel_iff : ∀ u : {x : C ⊕ QuotDashedEdge M c // x ≠ Sum.inl i},
            u.1 ∈ delColorSet M c i ↔ u ≠ s_c := by
          intro u
          rcases hu : u.1 with b | q
          · have hbi : b ≠ i := fun h => u.2 (hu.trans (congrArg Sum.inl h))
            simp [delColorSet, s_c, Subtype.ext_iff, hu, hbi]
          · simp only [delColorSet, s_c, ne_eq, Subtype.ext_iff, hu, Sum.inr.injEq]
            exact ⟨fun hni hEq => hni (Subtype.ext hEq ▸ hq₁_pair ▸ Sym2.mem_mk_left i j),
              fun hne hiq => hne (congrArg Subtype.val (hqi_eq q hiq))⟩
        refine hiso_from_del Xc s_c
          (fun x => ⟨⟨x.1, fun hEq => by
            have := x.2; rw [hEq] at this; exact this rfl⟩,
            (hdel_iff _).mp x.2⟩)
          (fun u => ⟨u.1.1, (hdel_iff u.1).mpr u.2⟩)
          (fun _ => Subtype.ext rfl) (fun _ => Subtype.ext (Subtype.ext rfl))
          ?_ ?_
        · intro x y
          have hxq₁ : x.1 ≠ Sum.inr q₁ := fun hEq =>
            (hdel_iff ⟨x.1, fun h => by have := x.2; rw [h] at this; exact this rfl⟩).mp x.2
              (Subtype.ext hEq)
          have hyq₁ : y.1 ≠ Sum.inr q₁ := fun hEq =>
            (hdel_iff ⟨y.1, fun h => by have := y.2; rw [h] at this; exact this rfl⟩).mp y.2
              (Subtype.ext hEq)
          constructor
          · rintro (h | ⟨h1, _⟩ | ⟨_, h2⟩)
            · exact h
            · exact absurd h1 hxq₁
            · exact absurd h2 hyq₁
          · intro h; exact Or.inl h
        · intro u
          constructor
          · rintro (h | ⟨_, h2⟩ | ⟨h1, _⟩)
            · rcases (hq₁_adj u.1).mp h with hj' | hi'
              · exact Or.inl (Subtype.ext hj')
              · exact absurd hi' u.2
            · exact Or.inr (Subtype.ext h2)
            · simp at h1
          · rintro (rfl | rfl)
            · exact Or.inl ((hq₁_adj (Sum.inl j)).mpr (Or.inl rfl))
            · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      exact isOuterplanar_of_contract_adj_deg2
        (u := Sum.inl j) (a := Sum.inr q₁) (b := Sum.inl i) (w := Sum.inl ℓ)
        (fun h => hjℓ (Sum.inl.inj h)) (fun h => hij.symm (Sum.inl.inj h)) (by simp)
        hq₁_adj hi_adj hXc_out
    · -- Case L = 4: both dashed (q₁ and q₂).
      rename_i t₁ t₂
      rw [htag₁] at hq1; rw [htag₂] at hq2
      obtain ⟨q₁, hq₁_val, hq₁_uniq⟩ := hq1.2
      obtain ⟨q₂, hq₂_val, hq₂_uniq⟩ := hq2.2
      have hq₁_pair : q₁.1.1 = s(i, j) := congrArg Prod.fst hq₁_val
      have hq₂_pair : q₂.1.1 = s(i, ℓ) := congrArg Prod.fst hq₂_val
      have hq₁₂ : q₁ ≠ q₂ := fun hEq => by
        have hp : s(i, j) = s(i, ℓ) :=
          hq₁_pair.symm.trans ((congrArg (fun r => r.1.1) hEq).trans hq₂_pair)
        rcases Sym2.eq_iff.mp hp with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hjℓ h2
        · exact hiℓ h1
      have hqi_eq : ∀ q : QuotDashedEdge M c, i ∈ q.1.1 → q = q₁ ∨ q = q₂ := by
        intro q hiq
        rcases hno_other_dash q hiq with h1 | h2
        · exact Or.inl (hq₁_uniq q h1)
        · exact Or.inr (hq₂_uniq q h2)
      have hq₁_adj : ∀ z : C ⊕ QuotDashedEdge M c,
          GK.Adj (Sum.inr q₁) z ↔ z = Sum.inl j ∨ z = Sum.inl i := by
        intro z
        rcases z with b | q
        · rw [subdivGraph_mixedQuotient_adj_inr_inl, hq₁_pair, Sym2.mem_iff]
          simp [or_comm]
        · simp [GK, subdivGraph]
      have hi_adj : ∀ z : C ⊕ QuotDashedEdge M c,
          GK.Adj (Sum.inl i) z ↔ z = Sum.inr q₁ ∨ z = Sum.inr q₂ := by
        intro z
        rcases z with b | q
        · constructor
          · intro hadj
            by_cases hbj : b = j
            · exact absurd (hbj ▸ hadj) hq1.1
            by_cases hbℓ : b = ℓ
            · exact absurd (hbℓ ▸ hadj) hq2.1
            exact absurd hadj (hno_other_sol b hbj hbℓ)
          · rintro (h | h) <;> simp at h
        · rw [subdivGraph_mixedQuotient_adj_inl_inr]
          constructor
          · intro hiq
            rcases hqi_eq q hiq with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
          · rintro (h | h)
            · rw [Sum.inr.inj h, hq₁_pair]; exact Sym2.mem_mk_left i j
            · rw [Sum.inr.inj h, hq₂_pair]; exact Sym2.mem_mk_left i ℓ
      have hq₂_adj : ∀ z : C ⊕ QuotDashedEdge M c,
          GK.Adj (Sum.inr q₂) z ↔ z = Sum.inl i ∨ z = Sum.inl ℓ := by
        intro z
        rcases z with b | q
        · rw [subdivGraph_mixedQuotient_adj_inr_inl, hq₂_pair, Sym2.mem_iff]
          simp
        · simp [GK, subdivGraph]
      let X₁ := contractEdgeGraph GK (Sum.inr q₁) (Sum.inl i) (Sum.inr q₂)
        (fun h => hq₁₂ (Sum.inr.inj h))
      let X₂ := contractEdgeGraph X₁ ⟨Sum.inr q₁, by simp⟩ ⟨Sum.inr q₂, by simp⟩
        ⟨Sum.inl ℓ, fun h => hiℓ.symm (Sum.inl.inj h)⟩ (by simp)
      have hX₂_out : IsOuterplanar X₂ := by
        let s₂ : {u : {x : C ⊕ QuotDashedEdge M c // x ≠ Sum.inl i} //
            u ≠ ⟨Sum.inr q₂, by simp⟩} :=
          ⟨⟨Sum.inr q₁, by simp⟩, fun h => hq₁₂ (Sum.inr.inj (congrArg Subtype.val h))⟩
        have hdel_iff : ∀ u : {u : {x : C ⊕ QuotDashedEdge M c // x ≠ Sum.inl i} //
            u ≠ ⟨Sum.inr q₂, by simp⟩}, u.1.1 ∈ delColorSet M c i ↔ u ≠ s₂ := by
          intro u
          rcases hu : u.1.1 with b | q
          · have hbi : b ≠ i := fun h => u.1.2 (hu.trans (congrArg Sum.inl h))
            simp [delColorSet, s₂, Subtype.ext_iff, hu, hbi]
          · have hqq₂ : q ≠ q₂ := fun h => u.2 (Subtype.ext (hu.trans (congrArg Sum.inr h)))
            simp only [delColorSet, s₂, ne_eq, Subtype.ext_iff, hu, Sum.inr.injEq]
            exact ⟨fun hni hEq => hni (hEq ▸ hq₁_pair ▸ Sym2.mem_mk_left i j),
              fun hne hiq => by
                rcases hqi_eq q hiq with rfl | rfl
                · exact hne rfl
                · exact hqq₂ rfl⟩
        refine hiso_from_del X₂ s₂
          (fun x => ⟨⟨⟨x.1, fun h => by have := x.2; rw [h] at this; exact this rfl⟩,
            fun h => by
              have hEq : x.1 = Sum.inr q₂ := congrArg Subtype.val h
              have := x.2; rw [hEq] at this
              exact this (hq₂_pair ▸ Sym2.mem_mk_left i ℓ)⟩,
            (hdel_iff _).mp x.2⟩)
          (fun u => ⟨u.1.1.1, (hdel_iff u.1).mpr u.2⟩)
          (fun _ => Subtype.ext rfl)
          (fun _ => Subtype.ext (Subtype.ext (Subtype.ext rfl)))
          ?_ ?_
        · intro x y
          have hxq₁ : x.1 ≠ Sum.inr q₁ := fun h => by
            have := x.2; rw [h] at this; exact this (hq₁_pair ▸ Sym2.mem_mk_left i j)
          have hyq₁ : y.1 ≠ Sum.inr q₁ := fun h => by
            have := y.2; rw [h] at this; exact this (hq₁_pair ▸ Sym2.mem_mk_left i j)
          constructor
          · rintro ((h | ⟨h1, _⟩ | ⟨_, h2⟩) | ⟨h1, _⟩ | ⟨_, h2⟩)
            · exact h
            · exact absurd h1 hxq₁
            · exact absurd h2 hyq₁
            · exact absurd (congrArg Subtype.val h1) hxq₁
            · exact absurd (congrArg Subtype.val h2) hyq₁
          · intro h; exact Or.inl (Or.inl h)
        · intro u
          constructor
          · rintro ((h | ⟨_, h2⟩ | ⟨h1, _⟩) | ⟨_, h2⟩ | ⟨h1, _⟩)
            · rcases (hq₁_adj u.1.1).mp h with hj' | hi'
              · exact Or.inl (Subtype.ext (Subtype.ext hj'))
              · exact absurd hi' u.1.2
            · exact absurd (Subtype.ext h2) u.2
            · exact absurd h1 (fun h => hq₁₂ (Sum.inr.inj h))
            · exact Or.inr (Subtype.ext h2)
            · simp [Subtype.ext_iff] at h1
          · rintro (rfl | rfl)
            · exact Or.inl (Or.inl ((hq₁_adj (Sum.inl j)).mpr (Or.inl rfl)))
            · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      exact isOuterplanar_of_deg2_chain4
        (a := Sum.inr q₁) (b := Sum.inl i) (c := Sum.inr q₂) (u := Sum.inl j) (w := Sum.inl ℓ)
        (by simp) (fun h => hq₁₂ (Sum.inr.inj h)) (by simp)
        (fun h => hjℓ (Sum.inl.inj h)) (by simp) (fun h => hij.symm (Sum.inl.inj h)) (by simp)
        (by simp) (fun h => hiℓ.symm (Sum.inl.inj h)) (by simp)
        hq₁_adj hi_adj hq₂_adj (SimpleGraph.Iso.refl) hX₂_out
  exact ⟨V', E', T', C', inferInstance, inferInstance, inferInstance, inferInstance,
    M', c', hltV, isOuterplanar_of_hasMinor hOut hMinorM', hSurj', heq', himp⟩

/-! ### 4. Proof of Theorem 1 (Minimal Counterexample Induction) -/

/-- **Theorem 1 (Tagged Outerplanar Mixed Multigraphs):**
If `M` is a finite tagged mixed multigraph whose subdivision graph `subdivGraph M` is outerplanar
and `c : V → C` is a surjective equitable coloring of `M`, then `subdivGraph (mixedQuotient M c)`
is outerplanar. -/
theorem subdivGraph_mixedQuotient_isOuterplanar :
    ∀ (n m : ℕ) (V E T C : Type) [Fintype V] [Fintype E] [Finite T] [Finite C]
      (M : TaggedMixedMultigraph V E T) (c : V → C),
      Fintype.card V = n →
      mixedSize M = m →
      IsOuterplanar (subdivGraph M) →
      Function.Surjective c →
      IsMixedEquitable M c →
      IsOuterplanar (subdivGraph (mixedQuotient M c)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih_n =>
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih_m =>
      intro V E T C _ _ _ _ M c hcardV hsize hOut hSurj heq
      classical
      have := Fintype.ofFinite T
      have := Fintype.ofFinite C
      -- (M1a) Eliminate monochromatic solid edges.
      by_cases hmonoS : ∃ u v : V, M.solid.Adj u v ∧ c u = c v
      · obtain ⟨M', hlt, hOut', heq', ⟨hiso⟩⟩ := delMonoSolid_step M c hOut heq hmonoS
        exact (isOuterplanar_iff_of_iso hiso).mp
          (ih_m (mixedSize M') (hsize ▸ hlt) V E T C M' c hcardV rfl hOut' hSurj heq')
      -- (M1b) Eliminate monochromatic dashed edges.
      by_cases hmonoD : ∃ e : E, c (M.e₁ e) = c (M.e₂ e)
      · obtain ⟨E', _, M', hlt, hOut', heq', ⟨hiso⟩⟩ := delMonoDashed_step M c hOut heq hmonoD
        exact (isOuterplanar_iff_of_iso hiso).mp
          (ih_m (mixedSize M') (hsize ▸ hlt) V E' T C M' c hcardV rfl hOut' hSurj heq')
      push Not at hmonoS hmonoD
      -- (M2) Deleting any color class yields an outerplanar quotient `G(\widehat{K} - i)`.
      have hM2 : ∀ i : C,
          IsOuterplanar ((subdivGraph (mixedQuotient M c)).induce (delColorSet M c i)) := by
        intro i
        obtain ⟨V', E', C', _, _, _, M', c', hltV, hOut', hSurj', heq', ⟨hiso⟩⟩ :=
          delColorClass_step M c hOut hSurj heq i
        exact (isOuterplanar_iff_of_iso hiso).mp
          (ih_n (Fintype.card V') (hcardV ▸ hltV) (mixedSize M') V' E' T C' M' c' rfl rfl
            hOut' hSurj' heq')
      -- (M4) No pair `{a, b}` has both a solid edge and a dashed edge in `mixedQuotient M c`.
      by_cases hM4_viol : ∃ (a b : C) (q : QuotDashedEdge M c),
          (mixedQuotient M c).solid.Adj a b ∧ q.1.1 = s(a, b)
      · obtain ⟨a, b, q, hab, hqpair⟩ := hM4_viol
        obtain ⟨M', H', hlt, hOut', heq', hH'_adj, ⟨hiso⟩⟩ :=
          delQuotSolidEdge_step M c hOut heq hab
        have hH'_out : IsOuterplanar H' :=
          (isOuterplanar_iff_of_iso hiso).mp
            (ih_m (mixedSize M') (hsize ▸ hlt) V E T C M' c hcardV rfl hOut' hSurj heq')
        have hq_adj : ∀ z : C ⊕ QuotDashedEdge M c,
            (subdivGraph (mixedQuotient M c)).Adj (Sum.inr q) z ↔
              z = Sum.inl a ∨ z = Sum.inl b := by
          intro z
          rcases z with d | q'
          · rw [subdivGraph_mixedQuotient_adj_inr_inl, hqpair, Sym2.mem_iff]
            simp
          · simp [subdivGraph]
        exact isOuterplanar_of_triangle_ear hq_adj hH'_adj hH'_out
      push Not at hM4_viol
      -- Step 2: Check `V` empty or isolated vertex in `underlyingSimple M`.
      by_cases hV_emp : IsEmpty V
      · have hC_emp : IsEmpty C := ⟨fun a => let ⟨v, _⟩ := hSurj a; hV_emp.false v⟩
        have hQ_emp : IsEmpty (QuotDashedEdge M c) :=
          ⟨fun q => let ⟨e, _, _⟩ := q.2.2; hV_emp.false (M.e₁ e)⟩
        have h0 : Fintype.card (C ⊕ QuotDashedEdge M c) = 0 := by simp
        exact isOuterplanar_of_card_le_three (subdivGraph (mixedQuotient M c)) (by omega)
      rw [not_isEmpty_iff] at hV_emp
      by_cases hiso_v : ∃ v : V, ∀ w : V, ¬ (underlyingSimple M).Adj v w
      · obtain ⟨v₀, hv₀_iso⟩ := hiso_v
        let i := c v₀
        have hi_iso : ∀ y : C ⊕ QuotDashedEdge M c,
            ¬ (subdivGraph (mixedQuotient M c)).Adj (Sum.inl i) y := by
          intro y hy
          rcases y with b | q
          · obtain ⟨w, hvw, _⟩ := exists_solid_of_quot_adj heq hy rfl
            exact hv₀_iso w (Or.inl hvw)
          · have hiq : i ∈ q.1.1 := (subdivGraph_mixedQuotient_adj_inl_inr M c i q).mp hy
            obtain ⟨b, hpair⟩ := Sym2.mem_iff_exists.mp hiq
            obtain ⟨e, w, -, hconn, -⟩ := exists_dashed_of_quot_edge heq hpair rfl
            exact hv₀_iso w (Or.inr ⟨e, hconn⟩)
        have hdel_eq : delColorSet M c i = {y : C ⊕ QuotDashedEdge M c | y ≠ Sum.inl i} := by
          ext y
          rcases y with b | q
          · simp [delColorSet]
          · constructor
            · intro _; simp
            · intro _ hiq
              exact hi_iso (Sum.inr q) ((subdivGraph_mixedQuotient_adj_inl_inr M c i q).mpr hiq)
        have hsub : IsOuterplanar ((subdivGraph (mixedQuotient M c)).induce
            {y : C ⊕ QuotDashedEdge M c | y ≠ Sum.inl i}) := hdel_eq ▸ hM2 i
        exact isOuterplanar_of_isolated_compl hi_iso hsub
      push Not at hiso_v
      -- `underlyingSimple M` has at least one edge and is outerplanar.
      have hEdge : ∃ u w : V, (underlyingSimple M).Adj u w := by
        obtain ⟨v₀⟩ := hV_emp
        obtain ⟨w₀, hw₀⟩ := hiso_v v₀
        exact ⟨v₀, w₀, hw₀⟩
      have hSimp_out : IsOuterplanar (underlyingSimple M) :=
        isOuterplanar_of_hasMinor hOut (hasMinor_subdivGraph_underlyingSimple M)
      -- Apply Lemma 6 to `underlyingSimple M` to obtain end-block `(B, z)`.
      obtain ⟨B, z, hzB, ⟨wB, hwBB, hwBz⟩, hBconn, hBtype, hBclosed⟩ :=
        exists_endBlock (underlyingSimple M) hEdge
      rcases hBtype with hB2 | hB2conn
      · -- Case 3A: `B ≅ K_2` with vertices `z` and `v := wB`.
        let v := wB
        have hBpair : B = {v, z} := by
          have hsub : ({v, z} : Finset V) ⊆ B := by
            intro a ha
            rcases Finset.mem_insert.mp ha with rfl | ha
            · exact hwBB
            · rw [Finset.mem_singleton.mp ha]; exact hzB
          have hcard2 : ({v, z} : Finset V).card = B.card := by
            rw [Finset.card_pair hwBz, hB2]
          exact (Finset.eq_of_subset_of_card_le hsub hcard2.ge).symm
        have hNv : ∀ w : V, (underlyingSimple M).Adj v w ↔ w = z := by
          intro w
          constructor
          · intro hvw
            have hwB : w ∈ B := hBclosed v hwBB hwBz w hvw
            rw [hBpair, Finset.mem_insert, Finset.mem_singleton] at hwB
            exact hwB.resolve_left hvw.ne.symm
          · rintro hwz
            rw [hwz]
            obtain ⟨w', hvw'⟩ := hiso_v v
            have hw'B : w' ∈ B := hBclosed v hwBB hwBz w' hvw'
            rw [hBpair, Finset.mem_insert, Finset.mem_singleton] at hw'B
            have hw'z : w' = z := hw'B.resolve_left hvw'.ne.symm
            exact hw'z ▸ hvw'
        let i := c v
        let j := c z
        have hij : i ≠ j := by
          rcases (hNv z).mpr rfl with hsol | ⟨e, he⟩
          · exact hmonoS v z hsol
          · rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have h := hmonoD e; rw [h1, h2] at h; exact h
            · have h := hmonoD e; rw [h1, h2] at h; exact h.symm
        have hsol_only : ∀ b : C, (mixedQuotient M c).solid.Adj i b → b = j := by
          intro b hadj
          obtain ⟨w, hvw, hwb⟩ := exists_solid_of_quot_adj heq hadj rfl
          have hwz : w = z := (hNv w).mp (Or.inl hvw)
          exact hwb.symm.trans (congrArg c hwz)
        have hdash_only : ∀ q : QuotDashedEdge M c, i ∈ q.1.1 → q.1.1 = s(i, j) := by
          intro q hiq
          obtain ⟨b, hpair⟩ := Sym2.mem_iff_exists.mp hiq
          obtain ⟨e, w, -, hconn, hwb⟩ := exists_dashed_of_quot_edge heq hpair rfl
          have hwz : w = z := (hNv w).mp (Or.inr ⟨e, hconn⟩)
          rw [hpair, hwb.symm.trans (congrArg c hwz)]
        have hcardQ : Set.ncard {q : QuotDashedEdge M c | q.1.1 = s(i, j)} ≤ 2 := by
          have : Fintype (QuotDashedEdge M c) := Fintype.ofFinite _
          let Qij := Finset.univ.filter fun q : QuotDashedEdge M c => q.1.1 = s(i, j)
          let Evz := Finset.univ.filter fun e : E => M.connects e v z
          have hQeq : (Qij : Set (QuotDashedEdge M c)) = {q | q.1.1 = s(i, j)} := by
            ext q; simp [Qij]
          have hEeq : (Evz : Set E) = {e | M.connects e v z} := by ext e; simp [Evz]
          rw [← hQeq, Set.ncard_coe_finset]
          have hex : ∀ q : QuotDashedEdge M c, q ∈ Qij → ∃ e ∈ Evz, M.tag e = q.1.2 := by
            intro q hq
            have hpair : q.1.1 = s(i, j) := (Finset.mem_filter.mp hq).2
            obtain ⟨e, w, hte, hconn, -⟩ := exists_dashed_of_quot_edge heq hpair rfl
            have hwz : w = z := (hNv w).mp (Or.inr ⟨e, hconn⟩)
            exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, hwz ▸ hconn⟩, hte⟩
          let pick : Qij → Evz := fun q =>
            ⟨Classical.choose (hex q.1 q.2), (Classical.choose_spec (hex q.1 q.2)).1⟩
          have hpick_inj : Function.Injective pick := by
            intro q₁ q₂ hEq
            have ht₁ : M.tag (pick q₁).1 = q₁.1.1.2 := (Classical.choose_spec (hex q₁.1 q₁.2)).2
            have ht₂ : M.tag (pick q₂).1 = q₂.1.1.2 := (Classical.choose_spec (hex q₂.1 q₂.2)).2
            have htag_eq : q₁.1.1.2 = q₂.1.1.2 :=
              ht₁.symm.trans ((congrArg (fun x : Evz => M.tag x.1) hEq).trans ht₂)
            have hp₁ : q₁.1.1.1 = s(i, j) := (Finset.mem_filter.mp q₁.2).2
            have hp₂ : q₂.1.1.1 = s(i, j) := (Finset.mem_filter.mp q₂.2).2
            exact Subtype.ext (Subtype.ext (Prod.ext (hp₁.trans hp₂.symm) htag_eq))
          have hle : Qij.card ≤ Evz.card := by
            have h := Fintype.card_le_of_injective pick hpick_inj
            rwa [Fintype.card_coe, Fintype.card_coe] at h
          have hEv2 : Evz.card ≤ 2 := by
            rw [← Set.ncard_coe_finset, hEeq]
            exact card_parallel_dashed_le_two M hOut hwBz
          exact hle.trans hEv2
        exact one_sum_two_color_isOuterplanar M c hij hsol_only hdash_only hcardQ (hM2 i)
      · -- Case 3B: `G_simp[B]` is 2-connected (`|B| ≥ 3`).
        -- Find a neighbor `y ∈ B` of `z` in `G_simp[B]`.
        have hy_ex :
            ∃ y : (B : Set V), ((underlyingSimple M).induce (B : Set V)).Adj ⟨z, hzB⟩ y := by
          obtain ⟨P⟩ := hBconn ⟨z, hzB⟩ ⟨wB, hwBB⟩
          cases P with
          | nil => exact absurd rfl hwBz.symm
          | @cons _ y _ hzy _ => exact ⟨y, hzy⟩
        obtain ⟨y, hzy⟩ := hy_ex
        have hBK4 : ¬ HasMinor ((underlyingSimple M).induce (B : Set V)) K4 :=
          (isOuterplanar_induce hSimp_out (B : Set V)).1
        obtain ⟨vB, hvBz, _, u₁B, u₂B, hu₁₂B, hNvB⟩ :=
          exists_deg_two_avoiding_edge ((underlyingSimple M).induce (B : Set V)) hB2conn hBK4 hzy
        let v := vB.1
        let u₁ := u₁B.1
        let u₂ := u₂B.1
        have hvz : v ≠ z := fun h => hvBz (Subtype.ext h)
        have hu₁₂ : u₁ ≠ u₂ := fun h => hu₁₂B (Subtype.ext h)
        have hNv : ∀ w : V, (underlyingSimple M).Adj v w ↔ w = u₁ ∨ w = u₂ := by
          intro w
          constructor
          · intro hvw
            have hwB : w ∈ B := hBclosed v vB.2 hvz w hvw
            rcases (hNvB ⟨w, hwB⟩).mp hvw with h1 | h2
            · exact Or.inl (congrArg Subtype.val h1)
            · exact Or.inr (congrArg Subtype.val h2)
          · rintro (rfl | rfl)
            · exact (hNvB u₁B).mpr (Or.inl rfl)
            · exact (hNvB u₂B).mpr (Or.inr rfl)
        have hvu₁ : v ≠ u₁ := ((hNv u₁).mpr (Or.inl rfl)).ne
        have hvu₂ : v ≠ u₂ := ((hNv u₂).mpr (Or.inr rfl)).ne
        -- By 2-connectivity of `B`, at most 1 dashed edge between `v` and `u₁` (and `v` and `u₂`).
        have hd1 : ∀ e₁ e₂ : E, M.connects e₁ v u₁ → M.connects e₂ v u₁ → e₁ = e₂ := by
          intro e₁ e₂ he₁ he₂
          obtain ⟨P, hP⟩ := exists_walk_of_induce_reachable (hB2conn.2 vB
            ⟨u₂B, fun h => hvu₂ (congrArg Subtype.val h).symm⟩
            ⟨u₁B, fun h => hvu₁ (congrArg Subtype.val h).symm⟩)
          let P' : (underlyingSimple M).Walk u₂ u₁ :=
            P.map (SimpleGraph.Embedding.induce (B : Set V)).toHom
          have hP' : ∀ w ∈ P'.support, w ≠ v := by
            intro w hw
            have hmem : w ∈ List.map
                (SimpleGraph.Embedding.induce (G := underlyingSimple M) (B : Set V)).toHom
                P.support := by
              rw [← SimpleGraph.Walk.support_map]; exact hw
            obtain ⟨w', hw'P, rfl⟩ := List.mem_map.mp hmem
            exact fun hEq => hP w' hw'P (Subtype.ext hEq)
          exact dashed_unique_of_alt_walk M hOut hvu₁ hvu₂ hu₁₂.symm
            ((hNv u₂).mpr (Or.inr rfl)) P' hP' he₁ he₂
        have hd2 : ∀ e₁ e₂ : E, M.connects e₁ v u₂ → M.connects e₂ v u₂ → e₁ = e₂ := by
          intro e₁ e₂ he₁ he₂
          obtain ⟨P, hP⟩ := exists_walk_of_induce_reachable (hB2conn.2 vB
            ⟨u₁B, fun h => hvu₁ (congrArg Subtype.val h).symm⟩
            ⟨u₂B, fun h => hvu₂ (congrArg Subtype.val h).symm⟩)
          let P' : (underlyingSimple M).Walk u₁ u₂ :=
            P.map (SimpleGraph.Embedding.induce (B : Set V)).toHom
          have hP' : ∀ w ∈ P'.support, w ≠ v := by
            intro w hw
            have hmem : w ∈ List.map
                (SimpleGraph.Embedding.induce (G := underlyingSimple M) (B : Set V)).toHom
                P.support := by
              rw [← SimpleGraph.Walk.support_map]; exact hw
            obtain ⟨w', hw'P, rfl⟩ := List.mem_map.mp hmem
            exact fun hEq => hP w' hw'P (Subtype.ext hEq)
          exact dashed_unique_of_alt_walk M hOut hvu₂ hvu₁ hu₁₂
            ((hNv u₁).mpr (Or.inl rfl)) P' hP' he₁ he₂
        let i := c v
        let j := c u₁
        let ℓ := c u₂
        have hij : i ≠ j := by
          rcases (hNv u₁).mpr (Or.inl rfl) with hsol | ⟨e, he⟩
          · exact hmonoS v u₁ hsol
          · rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have h := hmonoD e; rw [h1, h2] at h; exact h
            · have h := hmonoD e; rw [h1, h2] at h; exact h.symm
        have hiℓ : i ≠ ℓ := by
          rcases (hNv u₂).mpr (Or.inr rfl) with hsol | ⟨e, he⟩
          · exact hmonoS v u₂ hsol
          · rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have h := hmonoD e; rw [h1, h2] at h; exact h
            · have h := hmonoD e; rw [h1, h2] at h; exact h.symm
        by_cases hjℓ : j = ℓ
        · -- Subcase 3B(i): `c u₁ = c u₂`.
          have hsol_only : ∀ b : C, (mixedQuotient M c).solid.Adj i b → b = j := by
            intro b hadj
            obtain ⟨w, hvw, hwb⟩ := exists_solid_of_quot_adj heq hadj rfl
            rcases (hNv w).mp (Or.inl hvw) with rfl | rfl
            · exact hwb.symm
            · exact hwb.symm.trans hjℓ.symm
          have hdash_only : ∀ q : QuotDashedEdge M c, i ∈ q.1.1 → q.1.1 = s(i, j) := by
            intro q hiq
            obtain ⟨b, hpair⟩ := Sym2.mem_iff_exists.mp hiq
            obtain ⟨e, w, -, hconn, hwb⟩ := exists_dashed_of_quot_edge heq hpair rfl
            rcases (hNv w).mp (Or.inr ⟨e, hconn⟩) with rfl | rfl
            · rw [hpair, hwb.symm]
            · rw [hpair, hwb.symm, hjℓ]
          have hcardQ : Set.ncard {q : QuotDashedEdge M c | q.1.1 = s(i, j)} ≤ 2 := by
            have : Fintype (QuotDashedEdge M c) := Fintype.ofFinite _
            let Qij := Finset.univ.filter fun q : QuotDashedEdge M c => q.1.1 = s(i, j)
            have hQeq : (Qij : Set (QuotDashedEdge M c)) = {q | q.1.1 = s(i, j)} := by
              ext q; simp [Qij]
            rw [← hQeq, Set.ncard_coe_finset]
            let Ev1 := Finset.univ.filter fun e : E => M.connects e v u₁
            let Ev2 := Finset.univ.filter fun e : E => M.connects e v u₂
            have hEv1_le : Ev1.card ≤ 1 := Finset.card_le_one.mpr fun e₁ h1 e₂ h2 =>
              hd1 e₁ e₂ (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
            have hEv2_le : Ev2.card ≤ 1 := Finset.card_le_one.mpr fun e₁ h1 e₂ h2 =>
              hd2 e₁ e₂ (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
            have hEv_le : (Ev1 ∪ Ev2).card ≤ 2 :=
              (Finset.card_union_le Ev1 Ev2).trans (by omega)
            have hex : ∀ q : QuotDashedEdge M c, q ∈ Qij →
                ∃ e ∈ Ev1 ∪ Ev2, M.tag e = q.1.2 := by
              intro q hq
              have hpair : q.1.1 = s(i, j) := (Finset.mem_filter.mp hq).2
              obtain ⟨e, w, hte, hconn, -⟩ := exists_dashed_of_quot_edge heq hpair rfl
              rcases (hNv w).mp (Or.inr ⟨e, hconn⟩) with rfl | rfl
              · exact ⟨e, Finset.mem_union_left _ (Finset.mem_filter.mpr
                  ⟨Finset.mem_univ e, hconn⟩), hte⟩
              · exact ⟨e, Finset.mem_union_right _ (Finset.mem_filter.mpr
                  ⟨Finset.mem_univ e, hconn⟩), hte⟩
            let pick : Qij → (Ev1 ∪ Ev2 : Finset E) := fun q =>
              ⟨Classical.choose (hex q.1 q.2), (Classical.choose_spec (hex q.1 q.2)).1⟩
            have hpick_inj : Function.Injective pick := by
              intro q₁ q₂ hEq
              have ht₁ : M.tag (pick q₁).1 = q₁.1.1.2 := (Classical.choose_spec (hex q₁.1 q₁.2)).2
              have ht₂ : M.tag (pick q₂).1 = q₂.1.1.2 := (Classical.choose_spec (hex q₂.1 q₂.2)).2
              have htag_eq : q₁.1.1.2 = q₂.1.1.2 :=
                ht₁.symm.trans ((congrArg (fun x => M.tag x.1) hEq).trans ht₂)
              have hp₁ : q₁.1.1.1 = s(i, j) := (Finset.mem_filter.mp q₁.2).2
              have hp₂ : q₂.1.1.1 = s(i, j) := (Finset.mem_filter.mp q₂.2).2
              exact Subtype.ext (Subtype.ext (Prod.ext (hp₁.trans hp₂.symm) htag_eq))
            have hle : Qij.card ≤ (Ev1 ∪ Ev2).card := by
              have h := Fintype.card_le_of_injective pick hpick_inj
              rwa [Fintype.card_coe, Fintype.card_coe] at h
            exact hle.trans hEv_le
          exact one_sum_two_color_isOuterplanar M c hij hsol_only hdash_only hcardQ (hM2 i)
        · -- Subcase 3B(ii): `c u₁ ≠ c u₂`.
          obtain ⟨V', E', T', C', _, _, _, _, M', c', hltV, hOut', hSurj', heq', himp⟩ :=
            subcase3Bii_step M c hOut hSurj heq hmonoD
              (fun a b hab q hq => hM4_viol a b q hab hq)
              rfl rfl rfl hij hiℓ hjℓ hNv hd1 hd2
          exact himp (ih_n (Fintype.card V') (hcardV ▸ hltV) (mixedSize M') V' E' T' C' M' c'
            rfl rfl hOut' hSurj' heq')

/-! ### 5. Headline Theorems (Universe-Polymorphic Transport) -/

/-- **Stronger Unrestricted Theorem (`OuterplanarEquitableQuotientStatement`):**
For every finite outerplanar simple graph `G` (connected or not) on `V : Type u` and every
surjective equitable coloring `c : V → C` (for any color type `C : Type v`), the underlying
simple quotient graph `colorQuotientSimple G c` is outerplanar. -/
theorem outerplanar_equitable_quotient_isOuterplanar.{u, v} :
    OuterplanarEquitableQuotientStatement.{u, v} := by
  intro V C hFinV G c hOut hSurj heq
  have hFinC : Finite C := Finite.of_surjective c hSurj
  have hFTV := Fintype.ofFinite V
  have hFTC := Fintype.ofFinite C
  let eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let eC : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let G₀ : SimpleGraph (Fin (Fintype.card V)) := G.comap eV.symm
  let c₀ : Fin (Fintype.card V) → Fin (Fintype.card C) := fun x => eC (c (eV.symm x))
  let isoG : G ≃g G₀ :=
    { toEquiv := eV
      map_rel_iff' := by
        intro x y
        change G.Adj (eV.symm (eV x)) (eV.symm (eV y)) ↔ G.Adj x y
        simp }
  have hOut₀ : IsOuterplanar G₀ := (isOuterplanar_iff_of_iso isoG).mp hOut
  have hSurj₀ : Function.Surjective c₀ :=
    eC.surjective.comp (hSurj.comp eV.symm.surjective)
  let M₀ : TaggedMixedMultigraph (Fin (Fintype.card V)) Empty Empty :=
    { solid := G₀
      e₁ := Empty.elim
      e₂ := Empty.elim
      loopless_dashed := fun e => e.elim
      tag := Empty.elim }
  let isoSub : subdivGraph M₀ ≃g G₀ :=
    { toEquiv := Equiv.sumEmpty (Fin (Fintype.card V)) Empty
      map_rel_iff' := by
        intro x y
        rcases x with u | e
        · rcases y with w | e'
          · exact Iff.rfl
          · exact e'.elim
        · exact e.elim }
  have hOutM₀ : IsOuterplanar (subdivGraph M₀) := (isOuterplanar_iff_of_iso isoSub).mpr hOut₀
  have heqM₀ : IsMixedEquitable M₀ c₀ := by
    refine ⟨fun x y hxy b => ?_, fun _ _ _ _ t => t.elim⟩
    have hc_eq : c (eV.symm x) = c (eV.symm y) := eC.injective hxy
    have hcnt : ∀ z : Fin (Fintype.card V),
        solidCountAt M₀ c₀ z b = colorNeighborCount G c (eV.symm z) (eC.symm b) := by
      intro z
      apply ncard_eq_of_bij eV.symm
      · rintro w ⟨hadj, hwb⟩
        exact ⟨hadj, (eC.eq_symm_apply).mpr hwb⟩
      · intro w₁ _ w₂ _ h; exact eV.symm.injective h
      · rintro w ⟨hadj, hwb⟩
        refine ⟨eV w, ⟨?_, ?_⟩, eV.symm_apply_apply w⟩
        · change G.Adj (eV.symm z) (eV.symm (eV w))
          simpa using hadj
        · change eC (c (eV.symm (eV w))) = b
          simp [hwb]
    rw [hcnt x, hcnt y]
    exact heq (eV.symm x) (eV.symm y) hc_eq (eC.symm b)
  have hQuotOut : IsOuterplanar (subdivGraph (mixedQuotient M₀ c₀)) :=
    subdivGraph_mixedQuotient_isOuterplanar (Fintype.card (Fin (Fintype.card V)))
      (mixedSize M₀) (Fin (Fintype.card V)) Empty Empty (Fin (Fintype.card C))
      M₀ c₀ rfl rfl hOutM₀ hSurj₀ heqM₀
  have hQ_emp : IsEmpty (QuotDashedEdge M₀ c₀) := ⟨fun q => let ⟨e, _, _⟩ := q.2.2; e.elim⟩
  let isoQuot : subdivGraph (mixedQuotient M₀ c₀) ≃g colorQuotientSimple G c :=
    { toFun := fun x =>
        match x with
        | Sum.inl a => eC.symm a
        | Sum.inr q => (hQ_emp.false q).elim
      invFun := fun a => Sum.inl (eC a)
      left_inv := fun x => by
        rcases x with a | q
        · simp
        · exact (hQ_emp.false q).elim
      right_inv := fun a => by simp
      map_rel_iff' := by
        intro x y
        rcases x with a | q
        · rcases y with b | q'
          · change (colorQuotientSimple G c).Adj (eC.symm a) (eC.symm b) ↔
              (colorQuotientSimple G₀ c₀).Adj a b
            constructor
            · rintro ⟨hne, u, w, hu, hw, huw⟩
              refine ⟨fun h => hne (congrArg eC.symm h), eV u, eV w, ?_, ?_, ?_⟩
              · change eC (c (eV.symm (eV u))) = a; simp [hu]
              · change eC (c (eV.symm (eV w))) = b; simp [hw]
              · change G.Adj (eV.symm (eV u)) (eV.symm (eV w)); simpa using huw
            · rintro ⟨hne, u, w, hu, hw, huw⟩
              exact ⟨fun h => hne (eC.symm.injective h), eV.symm u, eV.symm w,
                (eC.eq_symm_apply).mpr hu, (eC.eq_symm_apply).mpr hw, huw⟩
          · exact (hQ_emp.false q').elim
        · exact (hQ_emp.false q).elim }
  exact (isOuterplanar_iff_of_iso isoQuot).mp hQuotOut

/-- **Coste–Csikós–Viennot Conjecture (`arXiv:2611.18391v1`, `5_details.tex` line 47):**
For every finite connected outerplanar graph `G` and every surjective equitable coloring
`c : V → Fin k` (not necessarily with a singleton color class), the underlying simple quotient
graph `colorQuotientSimple G c` is outerplanar. -/
theorem coste_csikos_viennot_conjecture.{u} : CosteCsikosViennotConjecture.{u} :=
  fun V _ G k c _ hOut hSurj heq =>
    outerplanar_equitable_quotient_isOuterplanar V (Fin k) G c hOut hSurj heq

end LeanForge.CosteOuterplanar
