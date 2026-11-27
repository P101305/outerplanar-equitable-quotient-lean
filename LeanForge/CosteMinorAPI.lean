/-
Copyright (c) 2026 Parker Lipscomb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Parker Lipscomb
-/
module

public import LeanForge.CosteOuterplanarStatement
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.FinCases

/-!
# Minor Infrastructure and Structural Outerplanarity Lemmas (Stage 1)

This module builds the minor-theoretic machinery and proves Lemmas 3, 4, and 5
purely combinatorially:

1. Induced-subgraph connectivity helpers (`induce_reachable_of_walk`, `induce_connected_insert`,
   `induce_connected_erase_leaf`, `induce_connected_replace_edge_by_path`,
   `induce_connected_inter_side`).
2. Core graph-minor closure properties (`hasMinor_trans`, `hasMinor_of_le`, `hasMinor_of_iso`,
   `hasMinor_of_emb`, `hasMinor_of_partialMap`, `isOuterplanar_of_hasMinor`,
   `isOuterplanar_iff_of_iso`, `isOuterplanar_of_le`, `isOuterplanar_induce`).
3. Small-graph outerplanarity (`isOuterplanar_of_card_le_three`,
   `isOuterplanar_of_card_eq_four_of_not_adj`, `isOuterplanar_of_isolated_compl`).
4. Unified `IsForbiddenOuterplanarMinor` interface shared by `K4` and `K23`, discharging:
   * **Lemma 3 (`isOuterplanar_of_triangle_ear`)**: triangle-ear edge deletion.
   * **Lemma 4 (`isOuterplanar_of_contract_adj_deg2`)**: adjacent degree-2 edge contraction.
   * **Lemma 5 (`isOuterplanar_of_one_sum`)**: 1-sum preserves outerplanarity.
-/

@[expose] public section

namespace LeanForge.CosteOuterplanar

/-! ### 1. Induced-Subgraph Connectivity Helpers -/

/-- A walk in `G` whose entire support lies in `S` yields reachability in `G.induce S`. -/
lemma induce_reachable_of_walk {V : Type*} {G : SimpleGraph V} {S : Set V} {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ S) :
    (G.induce S).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab q ih =>
    have hb : b ∈ S := hp b (by simp)
    have hstep : (G.induce S).Adj ⟨a, hu⟩ ⟨b, hb⟩ := hab
    have hq : ∀ x ∈ q.support, x ∈ S := fun x hx => hp x (by simp [hx])
    exact hstep.reachable.trans (ih hb hv hq)

/-- Reachability in `G.induce S` lifts to a walk in `G` supported inside `S`. -/
lemma exists_walk_of_induce_reachable {V : Type*} {G : SimpleGraph V} {S : Set V} {u v : S}
    (h : (G.induce S).Reachable u v) :
    ∃ p : G.Walk u.1 v.1, ∀ x ∈ p.support, x ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | @nil a =>
    refine ⟨SimpleGraph.Walk.nil, fun x hx => ?_⟩
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ a.2
  | @cons a b c hab q ih =>
    obtain ⟨q', hq'⟩ := ih
    refine ⟨SimpleGraph.Walk.cons hab q', fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact a.2
    · exact hq' x hx

/-- Monotonicity of induced connectivity under graph inclusion `G ≤ G'`. -/
lemma induce_connected_mono {V : Type*} {G G' : SimpleGraph V} (hle : G ≤ G') {S : Set V}
    (h : (G.induce S).Connected) : (G'.induce S).Connected :=
  h.mono fun _ _ hab => hle hab

/-- Reachability in `G.induce S` embeds into `G.induce T` whenever `S ⊆ T`. -/
lemma induce_reachable_of_subset {V : Type*} {G : SimpleGraph V} {S T : Set V} (hST : S ⊆ T)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (h : (G.induce S).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    (G.induce T).Reachable ⟨u, hST hu⟩ ⟨v, hST hv⟩ := by
  obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable h
  exact induce_reachable_of_walk (hST hu) (hST hv) p fun x hx => hST (hp x hx)

/-- Attaching a vertex `s` with a neighbor in a connected set `S` keeps `insert s S` connected. -/
lemma induce_connected_insert {V : Type*} {G : SimpleGraph V} {S : Set V} {s : V}
    (hS : (G.induce S).Connected) (hs : ∃ a ∈ S, G.Adj s a) :
    (G.induce (insert s S)).Connected := by
  obtain ⟨a, haS, hsa⟩ := hs
  have hsub : S ⊆ insert s S := Set.subset_insert s S
  have : Nonempty (insert s S : Set V) := ⟨⟨s, Set.mem_insert s S⟩⟩
  refine ⟨fun x y => ?_⟩
  have hto_a : ∀ z : (insert s S : Set V),
      (G.induce (insert s S)).Reachable z ⟨a, hsub haS⟩ := by
    intro z
    rcases z.2 with hzs | hzS
    · have hEq : z = ⟨s, Set.mem_insert s S⟩ := Subtype.ext hzs
      rw [hEq]
      exact SimpleGraph.Adj.reachable hsa
    · exact induce_reachable_of_subset hsub hzS haS (hS ⟨z.1, hzS⟩ ⟨a, haS⟩)
  exact (hto_a x).trans (hto_a y).symm

/-- Every internal vertex of a simple path has two distinct neighbors in the path. -/
lemma exists_two_adj_of_mem_support_of_isPath {V : Type*} {G : SimpleGraph V} {u v a : V}
    {p : G.Walk u v} (hp : p.IsPath) (ha : a ∈ p.support) (hau : a ≠ u) (hav : a ≠ v) :
    ∃ z₁ z₂ : V, z₁ ≠ z₂ ∧ z₁ ∈ p.support ∧ z₂ ∈ p.support ∧ G.Adj a z₁ ∧ G.Adj a z₂ := by
  induction p with
  | nil =>
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at ha
    exact absurd ha hau
  | @cons x y w hxy q ih =>
    have hnodup : (x :: q.support).Nodup := by
      simpa [SimpleGraph.Walk.support_cons] using hp.support_nodup
    have hx_not_q : x ∉ q.support := (List.nodup_cons.mp hnodup).1
    have hq_path : q.IsPath := hp.of_cons
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
    rcases ha with rfl | haq
    · exact absurd rfl hau
    · by_cases hay : a = y
      · subst hay
        cases q with
        | nil => exact absurd rfl hav
        | @cons y' z w' hyz r =>
          have hxz : x ≠ z := fun hEq => hx_not_q (by simp [hEq])
          refine ⟨x, z, hxz, by simp, by simp, hxy.symm, hyz⟩
      · obtain ⟨z₁, z₂, hne, hz₁, hz₂, h1, h2⟩ := ih hq_path haq hay hav
        exact ⟨z₁, z₂, hne, by simp [hz₁], by simp [hz₂], h1, h2⟩

/-- Deleting a leaf `a` (having at most one neighbor `u` inside `S`) from a connected set `S`
keeps `S \ {a}` connected. -/
lemma induce_connected_erase_leaf {V : Type*} {G : SimpleGraph V} {S : Set V} {a u : V}
    (hS : (G.induce S).Connected) (hu : u ∈ S) (hua : u ≠ a)
    (hleaf : ∀ z ∈ S, G.Adj a z → z = u) :
    (G.induce (S \ {a})).Connected := by
  have : Nonempty (S \ {a} : Set V) := ⟨⟨u, hu, hua⟩⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨p, hp⟩ := hS.exists_isPath ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩
  have hnotmem : ∀ z ∈ p.support, z.1 ≠ a := by
    intro z hz hza
    have hzx : z ≠ ⟨x.1, x.2.1⟩ := fun hEq => x.2.2 (hza ▸ congrArg Subtype.val hEq.symm)
    have hzy : z ≠ ⟨y.1, y.2.1⟩ := fun hEq => y.2.2 (hza ▸ congrArg Subtype.val hEq.symm)
    obtain ⟨w₁, w₂, hne, -, -, hw₁, hw₂⟩ :=
      exists_two_adj_of_mem_support_of_isPath hp hz hzx hzy
    have h1 : w₁.1 = u := hleaf w₁.1 w₁.2 (hza ▸ hw₁)
    have h2 : w₂.1 = u := hleaf w₂.1 w₂.2 (hza ▸ hw₂)
    exact hne (Subtype.ext (h1.trans h2.symm))
  have hlift : ∀ {b c : (S : Set V)} (q : (G.induce S).Walk b c)
      (hq : ∀ z ∈ q.support, z.1 ≠ a),
      (G.induce (S \ {a})).Reachable ⟨b.1, b.2, hq b (by simp)⟩
        ⟨c.1, c.2, hq c (by simp)⟩ := by
    intro b c q hq
    induction q with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons d e f hde r ih =>
      have hd : d.1 ≠ a := hq d (by simp)
      have he : e.1 ≠ a := hq e (by simp)
      have hr : ∀ z ∈ r.support, z.1 ≠ a := fun z hz => hq z (by simp [hz])
      have hstep : (G.induce (S \ {a})).Adj ⟨d.1, d.2, hd⟩ ⟨e.1, e.2, he⟩ := hde
      exact hstep.reachable.trans (ih hr)
  exact hlift p hnotmem

/-- If `G'` agrees with `G` on all pairs except possibly `{a, b}`, and `a, b, s ∈ S` with
`G'.Adj a s` and `G'.Adj s b`, then connectivity of `G.induce S` implies connectivity of
`G'.induce S`. -/
lemma induce_connected_replace_edge_by_path {V : Type*} {G G' : SimpleGraph V} {S : Set V}
    {a b s : V} (hS : (G.induce S).Connected)
    (hs : s ∈ S) (has : G'.Adj a s) (hsb : G'.Adj s b)
    (hagree : ∀ x y : V, G.Adj x y → (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨ G'.Adj x y) :
    (G'.induce S).Connected := by
  have : Nonempty S := hS.nonempty
  refine ⟨fun x y => ?_⟩
  obtain ⟨p⟩ := hS x y
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w huv q ih =>
    rcases hagree u.1 v.1 huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ | huv'
    · have h1 : (G'.induce S).Adj u ⟨s, hs⟩ := by
        change G'.Adj u.1 s; rw [hu]; exact has
      have h2 : (G'.induce S).Adj ⟨s, hs⟩ v := by
        change G'.Adj s v.1; rw [hv]; exact hsb
      exact (h1.reachable.trans h2.reachable).trans ih
    · have h1 : (G'.induce S).Adj u ⟨s, hs⟩ := by
        change G'.Adj u.1 s; rw [hu]; exact hsb.symm
      have h2 : (G'.induce S).Adj ⟨s, hs⟩ v := by
        change G'.Adj s v.1; rw [hv]; exact has.symm
      exact (h1.reachable.trans h2.reachable).trans ih
    · exact (SimpleGraph.Adj.reachable (show (G'.induce S).Adj u v from huv')).trans ih

/-- In a 1-sum split `V₁ ∪ V₂ = univ`, `V₁ ∩ V₂ = {j}` with no edges between `V₁ \ {j}` and
`V₂ \ {j}`, any connected set `B` avoiding `j` that meets `V₁` is completely contained in `V₁`. -/
lemma subset_side_of_induce_connected {V : Type*} {X : SimpleGraph V} {V₁ V₂ B : Set V} {j : V}
    (hunion : V₁ ∪ V₂ = Set.univ)
    (hno : ∀ x ∈ V₁, ∀ y ∈ V₂, x ≠ j → y ≠ j → ¬ X.Adj x y)
    (hB : (X.induce B).Connected) (hjB : j ∉ B)
    {x₀ : V} (hx₀B : x₀ ∈ B) (hx₀1 : x₀ ∈ V₁) : B ⊆ V₁ := by
  intro y hyB
  obtain ⟨p⟩ := hB ⟨x₀, hx₀B⟩ ⟨y, hyB⟩
  have hstep : ∀ {a b : B} (q : (X.induce B).Walk a b), a.1 ∈ V₁ → b.1 ∈ V₁ := by
    intro a b q ha1
    induction q with
    | nil => exact ha1
    | @cons u v w huv r ih =>
      apply ih
      have hu_ne : u.1 ≠ j := fun hEq => hjB (hEq ▸ u.2)
      have hv_ne : v.1 ≠ j := fun hEq => hjB (hEq ▸ v.2)
      have hv_all : v.1 ∈ V₁ ∪ V₂ := by rw [hunion]; trivial
      rcases hv_all with hv1 | hv2
      · exact hv1
      · exact absurd huv (hno u.1 ha1 v.1 hv2 hu_ne hv_ne)
  exact hstep p hx₀1

/-- In a 1-sum split along cut-vertex `j`, intersecting a connected set `B` containing `j` with
`V₁` preserves connectivity. -/
lemma induce_connected_inter_side {V : Type*} {X : SimpleGraph V} {V₁ V₂ B : Set V} {j : V}
    (hunion : V₁ ∪ V₂ = Set.univ)
    (hno : ∀ x ∈ V₁, ∀ y ∈ V₂, x ≠ j → y ≠ j → ¬ X.Adj x y)
    (hB : (X.induce B).Connected) (hjB : j ∈ B) (hj1 : j ∈ V₁) :
    (X.induce (B ∩ V₁)).Connected := by
  have : Nonempty (B ∩ V₁ : Set V) := ⟨⟨j, hjB, hj1⟩⟩
  refine ⟨fun x y => ?_⟩
  have hreach_j : ∀ z : (B ∩ V₁ : Set V),
      (X.induce (B ∩ V₁)).Reachable z ⟨j, hjB, hj1⟩ := by
    intro z
    obtain ⟨p⟩ := hB ⟨z.1, z.2.1⟩ ⟨j, hjB⟩
    have haux : ∀ {a b : B} (q : (X.induce B).Walk a b),
        b = ⟨j, hjB⟩ → ∀ (ha1 : a.1 ∈ V₁),
        (X.induce (B ∩ V₁)).Reachable ⟨a.1, a.2, ha1⟩ ⟨j, hjB, hj1⟩ := by
      intro a b q
      induction q with
      | @nil a =>
        intro hb ha1
        have hEq : (⟨a.1, a.2, ha1⟩ : (B ∩ V₁ : Set V)) = ⟨j, hjB, hj1⟩ :=
          Subtype.ext (congrArg (Subtype.val : B → V) hb)
        exact hEq ▸ SimpleGraph.Reachable.refl _
      | @cons u v w huv r ih =>
        intro hw hu1
        by_cases huj : u.1 = j
        · have hEq : (⟨u.1, u.2, hu1⟩ : (B ∩ V₁ : Set V)) = ⟨j, hjB, hj1⟩ := Subtype.ext huj
          exact hEq ▸ SimpleGraph.Reachable.refl _
        · have hv1 : v.1 ∈ V₁ := by
            by_cases hvj : v.1 = j
            · exact hvj ▸ hj1
            · have hv_all : v.1 ∈ V₁ ∪ V₂ := by rw [hunion]; trivial
              rcases hv_all with h1 | h2
              · exact h1
              · exact absurd huv (hno u.1 hu1 v.1 h2 huj hvj)
          have hstep : (X.induce (B ∩ V₁)).Adj ⟨u.1, u.2, hu1⟩ ⟨v.1, v.2, hv1⟩ := huv
          exact hstep.reachable.trans (ih hw hv1)
    exact haux p rfl z.2.2
  exact (hreach_j x).trans (hreach_j y).symm

/-! ### 2. Core Graph-Minor Closure Properties -/

/-- Transitivity of `HasMinor`: if `H` is a minor of `G` and `F` is a minor of `H`, then
`F` is a minor of `G`. -/
theorem hasMinor_trans {U V W : Type*} {G : SimpleGraph U} {H : SimpleGraph V}
    {F : SimpleGraph W} (hGH : HasMinor G H) (hHF : HasMinor H F) : HasMinor G F := by
  obtain ⟨B, hBconn, hBdisj, hBadj⟩ := hGH
  obtain ⟨C, hCconn, hCdisj, hCadj⟩ := hHF
  refine ⟨fun w => ⋃ v ∈ C w, B v, ?_, ?_, ?_⟩
  · intro w
    have hneCw : (C w).Nonempty := by
      obtain ⟨⟨v₀, hv₀⟩⟩ := (hCconn w).nonempty
      exact ⟨v₀, hv₀⟩
    obtain ⟨v₀, hv₀⟩ := hneCw
    obtain ⟨⟨x₀, hx₀⟩⟩ := (hBconn v₀).nonempty
    have : Nonempty (⋃ v ∈ C w, B v : Set U) := ⟨⟨x₀, Set.mem_biUnion hv₀ hx₀⟩⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨va, hva, hxa⟩ := Set.mem_iUnion₂.mp a.2
    obtain ⟨vb, hvb, hxb⟩ := Set.mem_iUnion₂.mp b.2
    have hBsub : ∀ v ∈ C w, B v ⊆ ⋃ u ∈ C w, B u := fun v hv => Set.subset_biUnion_of_mem hv
    have hstep_walk : ∀ {v₁ v₂ : C w} (q : (H.induce (C w)).Walk v₁ v₂)
        {y₁ : U} (hy₁ : y₁ ∈ B v₁.1) {y₂ : U} (hy₂ : y₂ ∈ B v₂.1),
        (G.induce (⋃ v ∈ C w, B v)).Reachable
          ⟨y₁, hBsub v₁.1 v₁.2 hy₁⟩ ⟨y₂, hBsub v₂.1 v₂.2 hy₂⟩ := by
      intro v₁ v₂ q
      induction q with
      | @nil v₁ =>
        intro y₁ hy₁ y₂ hy₂
        exact induce_reachable_of_subset (hBsub v₁.1 v₁.2) hy₁ hy₂
          (hBconn v₁.1 ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩)
      | @cons u₁ u₂ u₃ hu₁₂ r ih =>
        intro y₁ hy₁ y₃ hy₃
        obtain ⟨z₁, hz₁, z₂, hz₂, hzz⟩ := hBadj u₁.1 u₂.1 hu₁₂
        have hr1 := induce_reachable_of_subset (hBsub u₁.1 u₁.2) hy₁ hz₁
          (hBconn u₁.1 ⟨y₁, hy₁⟩ ⟨z₁, hz₁⟩)
        have hbridge : (G.induce (⋃ v ∈ C w, B v)).Adj
            ⟨z₁, hBsub u₁.1 u₁.2 hz₁⟩ ⟨z₂, hBsub u₂.1 u₂.2 hz₂⟩ := hzz
        exact (hr1.trans hbridge.reachable).trans (ih hz₂ hy₃)
    obtain ⟨q⟩ := hCconn w ⟨va, hva⟩ ⟨vb, hvb⟩
    exact hstep_walk q hxa hxb
  · intro w₁ w₂ hw
    dsimp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨v₁, hv₁, hxv₁⟩ := Set.mem_iUnion₂.mp hx₁
    obtain ⟨v₂, hv₂, hxv₂⟩ := Set.mem_iUnion₂.mp hx₂
    have hvne : v₁ ≠ v₂ := fun hEq =>
      Set.disjoint_left.mp (hCdisj hw) hv₁ (hEq ▸ hv₂)
    exact Set.disjoint_left.mp (hBdisj hvne) hxv₁ hxv₂
  · intro w₁ w₂ hw
    obtain ⟨v₁, hv₁, v₂, hv₂, hv12⟩ := hCadj w₁ w₂ hw
    obtain ⟨x, hx, y, hy, hxy⟩ := hBadj v₁ v₂ hv12
    exact ⟨x, Set.mem_biUnion hv₁ hx, y, Set.mem_biUnion hv₂ hy, hxy⟩

/-- A spanning subgraph `G ≤ G'` is a minor of `G'`. -/
theorem hasMinor_of_le {V : Type*} {G G' : SimpleGraph V} (hle : G ≤ G') : HasMinor G' G := by
  obtain ⟨B, hconn, hdisj, hadj⟩ := hasMinor_refl G
  exact ⟨B, fun w => induce_connected_mono hle (hconn w), hdisj,
    fun u v huv => let ⟨x, hx, y, hy, hxy⟩ := hadj u v huv; ⟨x, hx, y, hy, hle hxy⟩⟩

/-- Any graph embedding `H ↪g G` (e.g. an induced subgraph or isomorphism) yields `HasMinor G H`. -/
theorem hasMinor_of_emb {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H ↪g G) : HasMinor G H := by
  refine ⟨fun w => {f w}, ?_, ?_, ?_⟩
  · intro w
    have : Nonempty ({f w} : Set V) := ⟨⟨f w, Set.mem_singleton _⟩⟩
    refine ⟨fun x y => ?_⟩
    have hx : x.1 = f w := Set.mem_singleton_iff.mp x.2
    have hy : y.1 = f w := Set.mem_singleton_iff.mp y.2
    have hxy : x = y := Subtype.ext (hx.trans hy.symm)
    subst hxy
    exact SimpleGraph.Reachable.refl x
  · intro u v huv
    exact Set.disjoint_singleton.mpr fun hEq => huv (f.injective hEq)
  · intro u v huv
    exact ⟨f u, Set.mem_singleton _, f v, Set.mem_singleton _, f.map_rel_iff.mpr huv⟩

/-- Isomorphic graphs are minors of each other. -/
theorem hasMinor_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : HasMinor G H :=
  hasMinor_of_emb e.symm.toEmbedding

/-- Fiber contraction via a partial map `f : V → Option W`: if every fiber `{v | f v = some w}`
is connected in `G` and every edge of `H` lifts to an edge of `G` between the corresponding fibers,
then `HasMinor G H`. -/
theorem hasMinor_of_partialMap {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → Option W)
    (hconn : ∀ w : W, (G.induce {v : V | f v = some w}).Connected)
    (hadj : ∀ u v : W, H.Adj u v → ∃ x y : V, f x = some u ∧ f y = some v ∧ G.Adj x y) :
    HasMinor G H := by
  refine ⟨fun w => {v : V | f v = some w}, hconn, ?_, ?_⟩
  · intro u v huv
    dsimp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hxu hxv
    exact huv (Option.some.inj (hxu.symm.trans hxv))
  · intro u v huv
    obtain ⟨x, y, hx, hy, hxy⟩ := hadj u v huv
    exact ⟨x, hx, y, hy, hxy⟩

/-- Minor-heredity of outerplanarity: every minor of an outerplanar graph is outerplanar. -/
theorem isOuterplanar_of_hasMinor {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : IsOuterplanar G) (hGH : HasMinor G H) : IsOuterplanar H :=
  ⟨fun hK4 => hG.1 (hasMinor_trans hGH hK4), fun hK23 => hG.2 (hasMinor_trans hGH hK23)⟩

/-- Isomorphism invariance of outerplanarity. -/
theorem isOuterplanar_iff_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : IsOuterplanar G ↔ IsOuterplanar H :=
  ⟨fun hG => isOuterplanar_of_hasMinor hG (hasMinor_of_iso e),
   fun hH => isOuterplanar_of_hasMinor hH (hasMinor_of_iso e.symm)⟩

/-- Subgraphs of outerplanar graphs are outerplanar. -/
theorem isOuterplanar_of_le {V : Type*} {G G' : SimpleGraph V}
    (hG' : IsOuterplanar G') (hle : G ≤ G') : IsOuterplanar G :=
  isOuterplanar_of_hasMinor hG' (hasMinor_of_le hle)

/-- Induced subgraphs of outerplanar graphs are outerplanar. -/
theorem isOuterplanar_induce {V : Type*} {G : SimpleGraph V}
    (hG : IsOuterplanar G) (S : Set V) : IsOuterplanar (G.induce S) :=
  isOuterplanar_of_hasMinor hG (hasMinor_of_emb (SimpleGraph.Embedding.induce S))

/-! ### 3. Cardinality Bounds and Small-Graph Outerplanarity -/

/-- A minor model `H` in `G` yields an injection `W → V`, so `|W| ≤ |V|`. -/
lemma card_le_of_hasMinor {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (h : HasMinor G H) :
    Fintype.card W ≤ Fintype.card V := by
  obtain ⟨B, hconn, hdisj, -⟩ := h
  have hne : ∀ w : W, ∃ v : V, v ∈ B w := fun w =>
    let ⟨⟨v, hv⟩⟩ := (hconn w).nonempty; ⟨v, hv⟩
  choose g hg using hne
  have hinj : Function.Injective g := by
    intro u v huv
    by_contra hne_uv
    exact Set.disjoint_left.mp (hdisj hne_uv) (hg u) (huv ▸ hg v)
  exact Fintype.card_le_of_injective g hinj

/-- Any graph on at most 3 vertices is outerplanar (covers empty, `K_1`, `K_2`, `P_3`, `K_3`). -/
theorem isOuterplanar_of_card_le_three {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V ≤ 3) : IsOuterplanar G := by
  refine ⟨fun hK4 => ?_, fun hK23 => ?_⟩
  · have h4 := card_le_of_hasMinor hK4
    simp only [Fintype.card_fin] at h4
    omega
  · have h5 := card_le_of_hasMinor hK23
    simp only [Fintype.card_sum, Fintype.card_fin] at h5
    omega

/-- Any graph on 4 vertices with at least one non-adjacent distinct pair (e.g., `C_4`, `P_4`,
`K_{1,3}`, `K_4 - e`) is outerplanar. -/
theorem isOuterplanar_of_card_eq_four_of_not_adj {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V = 4) {x y : V} (hxy : x ≠ y) (hnadj : ¬ G.Adj x y) :
    IsOuterplanar G := by
  refine ⟨fun hK4 => ?_, fun hK23 => ?_⟩
  · obtain ⟨B, hconn, hdisj, hadj⟩ := hK4
    have hne : ∀ w : Fin 4, ∃ v : V, v ∈ B w := fun w =>
      let ⟨⟨v, hv⟩⟩ := (hconn w).nonempty; ⟨v, hv⟩
    choose g hg using hne
    have hinj : Function.Injective g := by
      intro u v huv
      by_contra hne_uv
      exact Set.disjoint_left.mp (hdisj hne_uv) (hg u) (huv ▸ hg v)
    have hsurj : Function.Surjective g :=
      ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hinj, by simp [hcard]⟩).2
    have hsingle : ∀ w : Fin 4, ∀ z ∈ B w, z = g w := by
      intro w z hz
      obtain ⟨w', hw'⟩ := hsurj z
      by_cases hww' : w = w'
      · exact (hww' ▸ hw').symm
      · exact absurd (hw' ▸ hg w') (Set.disjoint_left.mp (hdisj hww') hz)
    obtain ⟨wx, hwx⟩ := hsurj x
    obtain ⟨wy, hwy⟩ := hsurj y
    have hwxy : wx ≠ wy := fun hEq => hxy (hwx.symm.trans (hEq ▸ hwy))
    obtain ⟨x', hx', y', hy', hx'y'⟩ := hadj wx wy hwxy
    have h1 : x' = x := (hsingle wx x' hx').trans hwx
    have h2 : y' = y := (hsingle wy y' hy').trans hwy
    exact hnadj (h1 ▸ h2 ▸ hx'y')
  · have h5 := card_le_of_hasMinor hK23
    simp only [Fintype.card_sum, Fintype.card_fin] at h5
    omega

/-! ### 4. Unified Forbidden-Minor Interface for `K_4` and `K_{2,3}` -/

/-- Structural properties shared by both forbidden outerplanar minors `K_4` and `K_{2,3}`.
Proving Lemmas 3, 4, and 5 once for any graph satisfying `IsForbiddenOuterplanarMinor` avoids
duplicating minor-model arguments for `K_4` and `K_{2,3}`. -/
structure IsForbiddenOuterplanarMinor {W : Type*} (F : SimpleGraph W) : Prop where
  /-- Every vertex has at least two distinct neighbors (`δ(F) ≥ 2`). -/
  exists_two_adj : ∀ w : W, ∃ u v : W, u ≠ v ∧ F.Adj w u ∧ F.Adj w v
  /-- No vertex of degree ≤ 2 has two adjacent neighbors. -/
  no_deg_le_two_in_triangle :
    ∀ w u v : W, u ≠ v → F.Adj u v → (∀ z : W, F.Adj w z → z = u ∨ z = v) → False
  /-- No edge joins two vertices each of degree ≤ 2. -/
  no_edge_deg_le_two :
    ∀ x y : W, F.Adj x y →
      (∃ u : W, ∀ z : W, F.Adj x z → z = y ∨ z = u) →
      (∃ w : W, ∀ z : W, F.Adj y z → z = x ∨ z = w) → False
  /-- Deleting any single vertex leaves a connected graph (`F` is 2-connected). -/
  connected_delete_vertex : ∀ w₀ : W, (F.induce {w : W | w ≠ w₀}).Connected

/-- Any graph satisfying `IsForbiddenOuterplanarMinor` is itself connected. -/
lemma IsForbiddenOuterplanarMinor.connected {W : Type*} {F : SimpleGraph W}
    (hF : IsForbiddenOuterplanarMinor F) (hne : Nonempty W) : F.Connected := by
  obtain ⟨w₀⟩ := hne
  have : Nonempty W := ⟨w₀⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨u₀, -, -, hwu₀, -⟩ := hF.exists_two_adj w₀
  have hu₀_ne : u₀ ≠ w₀ := fun hEq => F.loopless.irrefl w₀ (hEq ▸ hwu₀)
  have hreach_u₀ : ∀ z : W, F.Reachable z u₀ := by
    intro z
    by_cases hzw : z = w₀
    · exact hzw ▸ hwu₀.reachable
    · obtain ⟨p, -⟩ := exists_walk_of_induce_reachable
        (hF.connected_delete_vertex w₀ ⟨z, hzw⟩ ⟨u₀, hu₀_ne⟩)
      exact ⟨p⟩
  exact (hreach_u₀ x).trans (hreach_u₀ y).symm

/-- `K_4` satisfies `IsForbiddenOuterplanarMinor`. -/
theorem isForbiddenOuterplanarMinor_K4 : IsForbiddenOuterplanarMinor K4 where
  exists_two_adj := by
    intro w
    fin_cases w
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  no_deg_le_two_in_triangle := by
    intro w u v _ _ hdeg
    fin_cases w <;> fin_cases u <;> fin_cases v <;>
      first
      | exact absurd (hdeg 0 (by decide)) (by decide)
      | exact absurd (hdeg 1 (by decide)) (by decide)
      | exact absurd (hdeg 2 (by decide)) (by decide)
      | exact absurd (hdeg 3 (by decide)) (by decide)
  no_edge_deg_le_two := by
    intro x y _ ⟨u, hx⟩ _
    fin_cases x <;> fin_cases y <;> fin_cases u <;>
      first
      | exact absurd (hx 0 (by decide)) (by decide)
      | exact absurd (hx 1 (by decide)) (by decide)
      | exact absurd (hx 2 (by decide)) (by decide)
      | exact absurd (hx 3 (by decide)) (by decide)
  connected_delete_vertex := by
    intro w₀
    have hne : ∃ a : Fin 4, a ≠ w₀ := by
      fin_cases w₀
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    obtain ⟨a, ha⟩ := hne
    have : Nonempty ({w : Fin 4 | w ≠ w₀} : Set (Fin 4)) := ⟨⟨a, ha⟩⟩
    refine ⟨fun x y => ?_⟩
    by_cases hxy : x = y
    · exact hxy ▸ SimpleGraph.Reachable.refl x
    · have hadj : (K4.induce {w : Fin 4 | w ≠ w₀}).Adj x y := fun hEq => hxy (Subtype.ext hEq)
      exact hadj.reachable

/-- `K_{2,3}` satisfies `IsForbiddenOuterplanarMinor`. -/
theorem isForbiddenOuterplanarMinor_K23 : IsForbiddenOuterplanarMinor K23 where
  exists_two_adj := by
    intro w
    rcases w with i | j
    · exact ⟨Sum.inr 0, Sum.inr 1, by decide, by simp [K23], by simp [K23]⟩
    · exact ⟨Sum.inl 0, Sum.inl 1, by decide, by simp [K23], by simp [K23]⟩
  no_deg_le_two_in_triangle := by
    intro w u v _ huv hdeg
    rcases w with i | j
    · have h0 := hdeg (Sum.inr 0) (by simp [K23])
      have h1 := hdeg (Sum.inr 1) (by simp [K23])
      have h2 := hdeg (Sum.inr 2) (by simp [K23])
      rcases h0 with h0' | h0' <;> rcases h1 with h1' | h1' <;> rcases h2 with h2' | h2'
      · exact absurd (h0'.trans h1'.symm) (by decide)
      · exact absurd (h0'.trans h1'.symm) (by decide)
      · exact absurd (h0'.trans h2'.symm) (by decide)
      · exact absurd (h1'.trans h2'.symm) (by decide)
      · exact absurd (h1'.trans h2'.symm) (by decide)
      · exact absurd (h0'.trans h2'.symm) (by decide)
      · exact absurd (h0'.trans h1'.symm) (by decide)
      · exact absurd (h0'.trans h1'.symm) (by decide)
    · have h0 := hdeg (Sum.inl 0) (by simp [K23])
      have h1 := hdeg (Sum.inl 1) (by simp [K23])
      rcases h0 with h0' | h0' <;> rcases h1 with h1' | h1'
      · exact absurd (h0'.trans h1'.symm) (by decide)
      · rw [← h0', ← h1'] at huv; simp [K23] at huv
      · rw [← h1', ← h0'] at huv; simp [K23] at huv
      · exact absurd (h0'.trans h1'.symm) (by decide)
  no_edge_deg_le_two := by
    intro x y hxy ⟨u, hx⟩ ⟨w, hy⟩
    rcases x with i | j <;> rcases y with i' | j'
    · simp [K23] at hxy
    · have h0 := hx (Sum.inr 0) (by simp [K23])
      have h1 := hx (Sum.inr 1) (by simp [K23])
      have h2 := hx (Sum.inr 2) (by simp [K23])
      fin_cases j'
      · rcases h1 with h1' | h1'
        · exact absurd h1' (by decide)
        · rcases h2 with h2' | h2'
          · exact absurd h2' (by decide)
          · exact absurd (h1'.trans h2'.symm) (by decide)
      · rcases h0 with h0' | h0'
        · exact absurd h0' (by decide)
        · rcases h2 with h2' | h2'
          · exact absurd h2' (by decide)
          · exact absurd (h0'.trans h2'.symm) (by decide)
      · rcases h0 with h0' | h0'
        · exact absurd h0' (by decide)
        · rcases h1 with h1' | h1'
          · exact absurd h1' (by decide)
          · exact absurd (h0'.trans h1'.symm) (by decide)
    · have h0 := hy (Sum.inr 0) (by simp [K23])
      have h1 := hy (Sum.inr 1) (by simp [K23])
      have h2 := hy (Sum.inr 2) (by simp [K23])
      fin_cases j
      · rcases h1 with h1' | h1'
        · exact absurd h1' (by decide)
        · rcases h2 with h2' | h2'
          · exact absurd h2' (by decide)
          · exact absurd (h1'.trans h2'.symm) (by decide)
      · rcases h0 with h0' | h0'
        · exact absurd h0' (by decide)
        · rcases h2 with h2' | h2'
          · exact absurd h2' (by decide)
          · exact absurd (h0'.trans h2'.symm) (by decide)
      · rcases h0 with h0' | h0'
        · exact absurd h0' (by decide)
        · rcases h1 with h1' | h1'
          · exact absurd h1' (by decide)
          · exact absurd (h0'.trans h1'.symm) (by decide)
    · simp [K23] at hxy
  connected_delete_vertex := by
    intro w₀
    rcases w₀ with i₀ | j₀
    · let i₁ : Fin 2 := if i₀ = 0 then 1 else 0
      have hi₁ : Sum.inl i₁ ≠ (Sum.inl i₀ : Fin 2 ⊕ Fin 3) := by
        fin_cases i₀ <;> simp [i₁]
      have : Nonempty ({w : Fin 2 ⊕ Fin 3 | w ≠ Sum.inl i₀} : Set (Fin 2 ⊕ Fin 3)) :=
        ⟨⟨Sum.inl i₁, hi₁⟩⟩
      refine ⟨fun x y => ?_⟩
      have hto : ∀ z : ({w : Fin 2 ⊕ Fin 3 | w ≠ Sum.inl i₀} : Set (Fin 2 ⊕ Fin 3)),
          (K23.induce {w | w ≠ Sum.inl i₀}).Reachable z ⟨Sum.inl i₁, hi₁⟩ := by
        intro z
        rcases hz : z.1 with i | j
        · have hi_eq : i = i₁ := by
            have hne : i ≠ i₀ := fun hEq => z.2 (hz.trans (congrArg Sum.inl hEq))
            fin_cases i₀ <;> fin_cases i <;> simp [i₁] at hne ⊢
          have hEq : z = ⟨Sum.inl i₁, hi₁⟩ := Subtype.ext (hz.trans (congrArg Sum.inl hi_eq))
          exact hEq ▸ SimpleGraph.Reachable.refl _
        · have hadj : (K23.induce {w | w ≠ Sum.inl i₀}).Adj z ⟨Sum.inl i₁, hi₁⟩ := by
            change K23.Adj z.1 (Sum.inl i₁)
            rw [hz]
            simp [K23]
          exact hadj.reachable
      exact (hto x).trans (hto y).symm
    · have h0ne : (Sum.inl 0 : Fin 2 ⊕ Fin 3) ≠ Sum.inr j₀ := by simp
      let j₁ : Fin 3 := if j₀ = 0 then 1 else 0
      have hj₁ : (Sum.inr j₁ : Fin 2 ⊕ Fin 3) ≠ Sum.inr j₀ := by
        fin_cases j₀ <;> simp [j₁]
      have : Nonempty ({w : Fin 2 ⊕ Fin 3 | w ≠ Sum.inr j₀} : Set (Fin 2 ⊕ Fin 3)) :=
        ⟨⟨Sum.inl 0, h0ne⟩⟩
      refine ⟨fun x y => ?_⟩
      have hto : ∀ z : ({w : Fin 2 ⊕ Fin 3 | w ≠ Sum.inr j₀} : Set (Fin 2 ⊕ Fin 3)),
          (K23.induce {w | w ≠ Sum.inr j₀}).Reachable z ⟨Sum.inl 0, h0ne⟩ := by
        intro z
        rcases hz : z.1 with i | j
        · have h1 : (K23.induce {w | w ≠ Sum.inr j₀}).Adj z ⟨Sum.inr j₁, hj₁⟩ := by
            change K23.Adj z.1 (Sum.inr j₁); rw [hz]; simp [K23]
          have h2 : (K23.induce {w | w ≠ Sum.inr j₀}).Adj ⟨Sum.inr j₁, hj₁⟩ ⟨Sum.inl 0, h0ne⟩ := by
            change K23.Adj (Sum.inr j₁) (Sum.inl 0); simp [K23]
          exact h1.reachable.trans h2.reachable
        · have h1 : (K23.induce {w | w ≠ Sum.inr j₀}).Adj z ⟨Sum.inl 0, h0ne⟩ := by
            change K23.Adj z.1 (Sum.inl 0); rw [hz]; simp [K23]
          exact h1.reachable
      exact (hto x).trans (hto y).symm

/-- Deleting an isolated vertex preserves `¬ HasMinor _ F` for any
`IsForbiddenOuterplanarMinor F`. -/
lemma hasMinor_of_isolated_compl {V W : Type*} {G : SimpleGraph V} {F : SimpleGraph W}
    (hF : IsForbiddenOuterplanarMinor F) {v₀ : V} (hiso : ∀ y : V, ¬ G.Adj v₀ y)
    (hGF : HasMinor G F) : HasMinor (G.induce {v : V | v ≠ v₀}) F := by
  obtain ⟨B, hconn, hdisj, hadj⟩ := hGF
  have hnotmem : ∀ w : W, v₀ ∉ B w := by
    intro w hv₀
    have hsingle : B w = {v₀} := by
      ext x
      constructor
      · intro hx
        obtain ⟨p, -⟩ := exists_walk_of_induce_reachable (hconn w ⟨v₀, hv₀⟩ ⟨x, hx⟩)
        cases p with
        | nil => exact Set.mem_singleton _
        | cons hadj' _ => exact absurd hadj' (hiso _)
      · intro hx
        exact (Set.mem_singleton_iff.mp hx) ▸ hv₀
    obtain ⟨u, -, -, hwu, -⟩ := hF.exists_two_adj w
    obtain ⟨x, hx, y, -, hxy⟩ := hadj w u hwu
    rw [hsingle, Set.mem_singleton_iff] at hx
    exact hiso y (hx ▸ hxy)
  refine ⟨fun w => {x : {v : V | v ≠ v₀} | x.1 ∈ B w}, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨⟨x₀, hx₀⟩⟩ := (hconn w).nonempty
    have hx₀ne : x₀ ≠ v₀ := fun hEq => hnotmem w (hEq ▸ hx₀)
    have : Nonempty ({x : {v : V | v ≠ v₀} | x.1 ∈ B w} : Set {v : V | v ≠ v₀}) :=
      ⟨⟨⟨x₀, hx₀ne⟩, hx₀⟩⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable (hconn w ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)
    have hlift : ∀ {x y : V} (q : G.Walk x y) (hq : ∀ z ∈ q.support, z ∈ B w),
        ((G.induce {v : V | v ≠ v₀}).induce {z | z.1 ∈ B w}).Reachable
          ⟨⟨x, fun hEq => hnotmem w (hEq ▸ hq x (by simp))⟩, hq x (by simp)⟩
          ⟨⟨y, fun hEq => hnotmem w (hEq ▸ hq y (by simp))⟩, hq y (by simp)⟩ := by
      intro x y q hq
      induction q with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons c d e hcd r ih =>
        have hc : c ∈ B w := hq c (by simp)
        have hd : d ∈ B w := hq d (by simp)
        have hr : ∀ z ∈ r.support, z ∈ B w := fun z hz => hq z (by simp [hz])
        have hstep :
            ((G.induce {v : V | v ≠ v₀}).induce {z | z.1 ∈ B w}).Adj
              ⟨⟨c, fun hEq => hnotmem w (hEq ▸ hc)⟩, hc⟩
              ⟨⟨d, fun hEq => hnotmem w (hEq ▸ hd)⟩, hd⟩ := hcd
        exact hstep.reachable.trans (ih hr)
    exact hlift p hp
  · intro u v huv
    dsimp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hxu hxv
    exact Set.disjoint_left.mp (hdisj huv) hxu hxv
  · intro u v huv
    obtain ⟨x, hx, y, hy, hxy⟩ := hadj u v huv
    exact ⟨⟨x, fun hEq => hnotmem u (hEq ▸ hx)⟩, hx,
      ⟨y, fun hEq => hnotmem v (hEq ▸ hy)⟩, hy, hxy⟩

/-- Deleting an isolated vertex preserves outerplanarity. -/
theorem isOuterplanar_of_isolated_compl {V : Type*} {G : SimpleGraph V} {v₀ : V}
    (hiso : ∀ y : V, ¬ G.Adj v₀ y)
    (hsub : IsOuterplanar (G.induce {v : V | v ≠ v₀})) : IsOuterplanar G :=
  ⟨fun hK4 => hsub.1 (hasMinor_of_isolated_compl isForbiddenOuterplanarMinor_K4 hiso hK4),
   fun hK23 => hsub.2 (hasMinor_of_isolated_compl isForbiddenOuterplanarMinor_K23 hiso hK23)⟩

/-! ### 5. Lemma 3: Triangle-Ear Edge Deletion -/

/-- **Lemma 3 (general forbidden-minor form):** If `H` has a degree-2 vertex `s` whose two
neighbors `a, b` are adjacent, and `H'` is obtained from `H` by deleting the edge `ab`, then any
minor of `H` satisfying `IsForbiddenOuterplanarMinor` is already a minor of `H'`. -/
lemma hasMinor_of_triangle_ear {V W : Type*} {H H' : SimpleGraph V} {F : SimpleGraph W}
    (hF : IsForbiddenOuterplanarMinor F) {a b s : V}
    (hs_adj : ∀ z : V, H.Adj s z ↔ z = a ∨ z = b)
    (hH'_adj : ∀ x y : V, H'.Adj x y ↔ H.Adj x y ∧ ¬((x = a ∧ y = b) ∨ (x = b ∧ y = a)))
    (hHF : HasMinor H F) : HasMinor H' F := by
  classical
  obtain ⟨B, hconn, hdisj, hadj⟩ := hHF
  have hsa_ne : s ≠ a := fun hEq => H.loopless.irrefl s (hEq ▸ (hs_adj a).mpr (Or.inl rfl))
  have hsb_ne : s ≠ b := fun hEq => H.loopless.irrefl s (hEq ▸ (hs_adj b).mpr (Or.inr rfl))
  have has' : H'.Adj a s := (hH'_adj a s).mpr
    ⟨((hs_adj a).mpr (Or.inl rfl)).symm, fun h => h.elim (fun h' => hsb_ne h'.2)
      (fun h' => hsa_ne h'.2)⟩
  have hsb' : H'.Adj s b := (hH'_adj s b).mpr
    ⟨(hs_adj b).mpr (Or.inr rfl), fun h => h.elim (fun h' => hsa_ne h'.1)
      (fun h' => hsb_ne h'.1)⟩
  have hagree : ∀ x y : V, H.Adj x y → (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨ H'.Adj x y := by
    intro x y hxy
    by_cases h1 : x = a ∧ y = b
    · exact Or.inl h1
    · by_cases h2 : x = b ∧ y = a
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ((hH'_adj x y).mpr ⟨hxy, not_or.mpr ⟨h1, h2⟩⟩))
  have hconn_if_miss : ∀ w : W, (a ∉ B w ∨ b ∉ B w) → (H'.induce (B w)).Connected := by
    intro w hmiss
    have : Nonempty (B w) := (hconn w).nonempty
    refine ⟨fun x y => ?_⟩
    obtain ⟨p⟩ := hconn w x y
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u v z huv q ih =>
      rcases hagree u.1 v.1 huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ | huv'
      · exfalso
        have ha_in : a ∈ B w := hu ▸ u.2
        have hb_in : b ∈ B w := hv ▸ v.2
        rcases hmiss with ha | hb
        · exact ha ha_in
        · exact hb hb_in
      · exfalso
        have ha_in : a ∈ B w := hv ▸ v.2
        have hb_in : b ∈ B w := hu ▸ u.2
        rcases hmiss with ha | hb
        · exact ha ha_in
        · exact hb hb_in
      · exact (SimpleGraph.Adj.reachable (show (H'.induce (B w)).Adj u v from huv')).trans ih
  have hsingle_s : ∀ w : W, s ∈ B w → a ∉ B w → b ∉ B w → B w = {s} := by
    intro w hs ha hb
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable (hconn w ⟨s, hs⟩ ⟨x, hx⟩)
      cases p with
      | nil => exact Set.mem_singleton _
      | @cons _ y _ hsy _ =>
        rcases (hs_adj y).mp hsy with hy | hy
        · exact absurd (hy ▸ hp y (by simp)) ha
        · exact absurd (hy ▸ hp y (by simp)) hb
    · intro hx
      exact (Set.mem_singleton_iff.mp hx) ▸ hs
  by_cases ha_in : ∃ u : W, a ∈ B u
  · obtain ⟨u, hau⟩ := ha_in
    by_cases hb_in : ∃ v : W, b ∈ B v
    · obtain ⟨v, hbv⟩ := hb_in
      by_cases huv : u = v
      · -- Case A: `a, b ∈ B u`
        subst huv
        by_cases hs_in : ∃ w : W, s ∈ B w
        · obtain ⟨w, hsw⟩ := hs_in
          by_cases hwu : w = u
          · subst hwu
            refine ⟨B, fun z => ?_, hdisj, fun x y hxy => ?_⟩
            · by_cases hzw : z = w
              · exact hzw ▸ induce_connected_replace_edge_by_path (hconn w) hsw has' hsb' hagree
              · exact hconn_if_miss z (Or.inl fun ha => Set.disjoint_left.mp (hdisj hzw) ha hau)
            · obtain ⟨p, hp, q, hq, hpq⟩ := hadj x y hxy
              rcases hagree p q hpq with ⟨hpa, hqb⟩ | ⟨hpb, hqa⟩ | hpq'
              · have hx : x = w := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpa ▸ hp) hau
                have hy : y = w := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqb ▸ hq) hbv
                exact absurd (hx.trans hy.symm) (F.ne_of_adj hxy)
              · have hx : x = w := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpb ▸ hp) hbv
                have hy : y = w := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqa ▸ hq) hau
                exact absurd (hx.trans hy.symm) (F.ne_of_adj hxy)
              · exact ⟨p, hp, q, hq, hpq'⟩
          · exfalso
            have haw : a ∉ B w := fun ha => Set.disjoint_left.mp (hdisj hwu) ha hau
            have hbw : b ∉ B w := fun hb => Set.disjoint_left.mp (hdisj hwu) hb hbv
            have hBw : B w = {s} := hsingle_s w hsw haw hbw
            obtain ⟨z₁, z₂, hzne, hz₁, hz₂⟩ := hF.exists_two_adj w
            have h_eq_u : ∀ z : W, F.Adj w z → z = u := by
              intro z hwz
              obtain ⟨x, hx, y, hy, hxy⟩ := hadj w z hwz
              rw [hBw, Set.mem_singleton_iff] at hx
              subst hx
              rcases (hs_adj y).mp hxy with hya | hyb
              · by_contra hzu; exact Set.disjoint_left.mp (hdisj hzu) (hya ▸ hy) hau
              · by_contra hzu; exact Set.disjoint_left.mp (hdisj hzu) (hyb ▸ hy) hbv
            exact hzne ((h_eq_u z₁ hz₁).trans (h_eq_u z₂ hz₂).symm)
        · push Not at hs_in
          let B' : W → Set V := fun z => if z = u then insert s (B u) else B z
          refine ⟨B', fun z => ?_, ?_, ?_⟩
          · by_cases hzu : z = u
            · subst hzu
              have hEq : B' z = insert s (B z) := by simp [B']
              rw [hEq]
              have hconn_ins : (H.induce (insert s (B z))).Connected :=
                induce_connected_insert (hconn z) ⟨a, hau, (hs_adj a).mpr (Or.inl rfl)⟩
              exact induce_connected_replace_edge_by_path hconn_ins (Set.mem_insert s _)
                has' hsb' hagree
            · have hEq : B' z = B z := by simp [B', hzu]
              rw [hEq]
              exact hconn_if_miss z (Or.inl fun ha => Set.disjoint_left.mp (hdisj hzu) ha hau)
          · intro x y hxy
            dsimp only [Function.onFun]
            rw [Set.disjoint_left]
            intro p hp hq
            by_cases hxu : x = u
            · subst hxu
              have hyu : y ≠ x := hxy.symm
              simp only [B', ↓reduceIte, hyu] at hp hq
              rcases hp with rfl | hpB
              · exact hs_in y hq
              · exact Set.disjoint_left.mp (hdisj hxy) hpB hq
            · by_cases hyu : y = u
              · subst hyu
                simp only [B', hxu, ↓reduceIte] at hp hq
                rcases hq with rfl | hqB
                · exact hs_in x hp
                · exact Set.disjoint_left.mp (hdisj hxy) hp hqB
              · simp only [B', hxu, hyu, ↓reduceIte] at hp hq
                exact Set.disjoint_left.mp (hdisj hxy) hp hq
          · intro x y hxy
            obtain ⟨p, hp, q, hq, hpq⟩ := hadj x y hxy
            rcases hagree p q hpq with ⟨hpa, hqb⟩ | ⟨hpb, hqa⟩ | hpq'
            · have hx : x = u := by
                by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpa ▸ hp) hau
              have hy : y = u := by
                by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqb ▸ hq) hbv
              exact absurd (hx.trans hy.symm) (F.ne_of_adj hxy)
            · have hx : x = u := by
                by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpb ▸ hp) hbv
              have hy : y = u := by
                by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqa ▸ hq) hau
              exact absurd (hx.trans hy.symm) (F.ne_of_adj hxy)
            · refine ⟨p, ?_, q, ?_, hpq'⟩
              · by_cases hxu : x = u
                · subst hxu; simp only [B', ↓reduceIte]; exact Set.mem_insert_of_mem _ hp
                · simp only [B', hxu, ↓reduceIte]; exact hp
              · by_cases hyu : y = u
                · subst hyu; simp only [B', ↓reduceIte]; exact Set.mem_insert_of_mem _ hq
                · simp only [B', hyu, ↓reduceIte]; exact hq
      · -- Case B: `a ∈ B u`, `b ∈ B v` with `u ≠ v`
        have hconn_all : ∀ z : W, (H'.induce (B z)).Connected := by
          intro z
          by_cases hzu : z = u
          · subst hzu
            exact hconn_if_miss z (Or.inr fun hb => Set.disjoint_left.mp (hdisj huv) hb hbv)
          · exact hconn_if_miss z (Or.inl fun ha => Set.disjoint_left.mp (hdisj hzu) ha hau)
        by_cases hFuv : F.Adj u v
        · by_cases hs_in : ∃ w : W, s ∈ B w
          · obtain ⟨w, hsw⟩ := hs_in
            by_cases hwu : w = u
            · subst hwu
              refine ⟨B, hconn_all, hdisj, fun x y hxy => ?_⟩
              obtain ⟨p, hp, q, hq, hpq⟩ := hadj x y hxy
              rcases hagree p q hpq with ⟨hpa, hqb⟩ | ⟨hpb, hqa⟩ | hpq'
              · have hx : x = w := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpa ▸ hp) hau
                have hy : y = v := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqb ▸ hq) hbv
                exact ⟨s, hx ▸ hsw, b, hy ▸ hbv, hsb'⟩
              · have hx : x = v := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpb ▸ hp) hbv
                have hy : y = w := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqa ▸ hq) hau
                exact ⟨b, hx ▸ hbv, s, hy ▸ hsw, hsb'.symm⟩
              · exact ⟨p, hp, q, hq, hpq'⟩
            · by_cases hwv : w = v
              · subst hwv
                refine ⟨B, hconn_all, hdisj, fun x y hxy => ?_⟩
                obtain ⟨p, hp, q, hq, hpq⟩ := hadj x y hxy
                rcases hagree p q hpq with ⟨hpa, hqb⟩ | ⟨hpb, hqa⟩ | hpq'
                · have hx : x = u := by
                    by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpa ▸ hp) hau
                  have hy : y = w := by
                    by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqb ▸ hq) hbv
                  exact ⟨a, hx ▸ hau, s, hy ▸ hsw, has'⟩
                · have hx : x = w := by
                    by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpb ▸ hp) hbv
                  have hy : y = u := by
                    by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqa ▸ hq) hau
                  exact ⟨s, hx ▸ hsw, a, hy ▸ hau, has'.symm⟩
                · exact ⟨p, hp, q, hq, hpq'⟩
              · exfalso
                have haw : a ∉ B w := fun ha => Set.disjoint_left.mp (hdisj hwu) ha hau
                have hbw : b ∉ B w := fun hb => Set.disjoint_left.mp (hdisj hwv) hb hbv
                have hBw : B w = {s} := hsingle_s w hsw haw hbw
                refine hF.no_deg_le_two_in_triangle w u v huv hFuv fun z hwz => ?_
                obtain ⟨x, hx, y, hy, hxy⟩ := hadj w z hwz
                rw [hBw, Set.mem_singleton_iff] at hx
                subst hx
                rcases (hs_adj y).mp hxy with hya | hyb
                · left; by_contra hzu; exact Set.disjoint_left.mp (hdisj hzu) (hya ▸ hy) hau
                · right; by_contra hzv; exact Set.disjoint_left.mp (hdisj hzv) (hyb ▸ hy) hbv
          · push Not at hs_in
            let B' : W → Set V := fun z => if z = u then insert s (B u) else B z
            refine ⟨B', fun z => ?_, ?_, ?_⟩
            · by_cases hzu : z = u
              · subst hzu
                have hEq : B' z = insert s (B z) := by simp [B']
                rw [hEq]
                exact induce_connected_insert (hconn_all z) ⟨a, hau, has'.symm⟩
              · have hEq : B' z = B z := by simp [B', hzu]
                rw [hEq]
                exact hconn_all z
            · intro x y hxy
              dsimp only [Function.onFun]
              rw [Set.disjoint_left]
              intro p hp hq
              by_cases hxu : x = u
              · subst hxu
                have hyu : y ≠ x := hxy.symm
                simp only [B', ↓reduceIte, hyu] at hp hq
                rcases hp with rfl | hpB
                · exact hs_in y hq
                · exact Set.disjoint_left.mp (hdisj hxy) hpB hq
              · by_cases hyu : y = u
                · subst hyu
                  simp only [B', hxu, ↓reduceIte] at hp hq
                  rcases hq with rfl | hqB
                  · exact hs_in x hp
                  · exact Set.disjoint_left.mp (hdisj hxy) hp hqB
                · simp only [B', hxu, hyu, ↓reduceIte] at hp hq
                  exact Set.disjoint_left.mp (hdisj hxy) hp hq
            · intro x y hxy
              obtain ⟨p, hp, q, hq, hpq⟩ := hadj x y hxy
              rcases hagree p q hpq with ⟨hpa, hqb⟩ | ⟨hpb, hqa⟩ | hpq'
              · have hx : x = u := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpa ▸ hp) hau
                have hy : y = v := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqb ▸ hq) hbv
                refine ⟨s, ?_, b, ?_, hsb'⟩
                · subst hx; simp only [B', ↓reduceIte]; exact Set.mem_insert s _
                · subst hy; simp only [B', Ne.symm huv, ↓reduceIte]; exact hbv
              · have hx : x = v := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpb ▸ hp) hbv
                have hy : y = u := by
                  by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqa ▸ hq) hau
                refine ⟨b, ?_, s, ?_, hsb'.symm⟩
                · subst hx; simp only [B', Ne.symm huv, ↓reduceIte]; exact hbv
                · subst hy; simp only [B', ↓reduceIte]; exact Set.mem_insert s _
              · refine ⟨p, ?_, q, ?_, hpq'⟩
                · by_cases hxu : x = u
                  · subst hxu; simp only [B', ↓reduceIte]; exact Set.mem_insert_of_mem _ hp
                  · simp only [B', hxu, ↓reduceIte]; exact hp
                · by_cases hyu : y = u
                  · subst hyu; simp only [B', ↓reduceIte]; exact Set.mem_insert_of_mem _ hq
                  · simp only [B', hyu, ↓reduceIte]; exact hq
        · refine ⟨B, hconn_all, hdisj, fun x y hxy => ?_⟩
          obtain ⟨p, hp, q, hq, hpq⟩ := hadj x y hxy
          rcases hagree p q hpq with ⟨hpa, hqb⟩ | ⟨hpb, hqa⟩ | hpq'
          · have hx : x = u := by
              by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpa ▸ hp) hau
            have hy : y = v := by
              by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqb ▸ hq) hbv
            exact absurd (hx ▸ hy ▸ hxy) hFuv
          · have hx : x = v := by
              by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpb ▸ hp) hbv
            have hy : y = u := by
              by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqa ▸ hq) hau
            exact absurd (hx ▸ hy ▸ hxy.symm) hFuv
          · exact ⟨p, hp, q, hq, hpq'⟩
    · push Not at hb_in
      refine ⟨B, fun z => hconn_if_miss z (Or.inr (hb_in z)), hdisj, fun x y hxy => ?_⟩
      obtain ⟨p, hp, q, hq, hpq⟩ := hadj x y hxy
      rcases hagree p q hpq with ⟨_, hqb⟩ | ⟨hpb, _⟩ | hpq'
      · exact absurd (hqb ▸ hq) (hb_in y)
      · exact absurd (hpb ▸ hp) (hb_in x)
      · exact ⟨p, hp, q, hq, hpq'⟩
  · push Not at ha_in
    refine ⟨B, fun z => hconn_if_miss z (Or.inl (ha_in z)), hdisj, fun x y hxy => ?_⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := hadj x y hxy
    rcases hagree p q hpq with ⟨hpa, _⟩ | ⟨_, hqa⟩ | hpq'
    · exact absurd (hpa ▸ hp) (ha_in x)
    · exact absurd (hqa ▸ hq) (ha_in y)
    · exact ⟨p, hp, q, hq, hpq'⟩

/-- **Lemma 3 (Triangle-Ear Edge Deletion):** If `H` has a degree-2 vertex `s` with adjacent
neighbors `a, b`, and deleting edge `ab` produces an outerplanar graph `H'`, then `H` is
outerplanar. -/
theorem isOuterplanar_of_triangle_ear {V : Type*} {H H' : SimpleGraph V} {a b s : V}
    (hs_adj : ∀ z : V, H.Adj s z ↔ z = a ∨ z = b)
    (hH'_adj : ∀ x y : V, H'.Adj x y ↔ H.Adj x y ∧ ¬((x = a ∧ y = b) ∨ (x = b ∧ y = a)))
    (hH' : IsOuterplanar H') : IsOuterplanar H :=
  ⟨fun hK4 => hH'.1 (hasMinor_of_triangle_ear isForbiddenOuterplanarMinor_K4 hs_adj hH'_adj hK4),
   fun hK23 => hH'.2 (hasMinor_of_triangle_ear isForbiddenOuterplanarMinor_K23 hs_adj hH'_adj hK23)⟩

/-! ### 6. Lemma 4: Adjacent Degree-2 Edge Contraction -/

/-- The simple graph `X / ab` on `{v : V // v ≠ b}` obtained by contracting edge `ab` into `a`
(where `b` had neighborhood `{a, w}` with `w ≠ a`), adding edge `a ~ w`. -/
def contractEdgeGraph {V : Type*} (X : SimpleGraph V) (a b w : V) (haw : a ≠ w) :
    SimpleGraph {v : V // v ≠ b} where
  Adj x y := X.Adj x.1 y.1 ∨ (x.1 = a ∧ y.1 = w) ∨ (x.1 = w ∧ y.1 = a)
  symm := ⟨fun _ _ h => by
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · exact Or.inr (Or.inl ⟨h2, h1⟩)⟩
  loopless := ⟨fun x h => by
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact X.loopless.irrefl x.1 h
    · exact haw (h1.symm.trans h2)
    · exact haw (h2.symm.trans h1)⟩

/-- **Lemma 4 (general forbidden-minor form):** If `X` has adjacent degree-2 vertices `a, b`
with `N(a) = {u, b}` and `N(b) = {a, w}` where `u ≠ w`, `u ≠ b`, `w ≠ a`, then any minor `F` of
`X` satisfying `IsForbiddenOuterplanarMinor` is also a minor of `contractEdgeGraph X a b w`. -/
lemma hasMinor_of_contract_adj_deg2 {V W : Type*} {X : SimpleGraph V} {F : SimpleGraph W}
    (hF : IsForbiddenOuterplanarMinor F) {a b u w : V}
    (_huw : u ≠ w) (hub : u ≠ b) (hwa : w ≠ a)
    (ha_adj : ∀ z : V, X.Adj a z ↔ z = u ∨ z = b)
    (hb_adj : ∀ z : V, X.Adj b z ↔ z = a ∨ z = w)
    (hXF : HasMinor X F) :
    HasMinor (contractEdgeGraph X a b w hwa.symm) F := by
  classical
  obtain ⟨B, hconn, hdisj, hadj⟩ := hXF
  have hab : a ≠ b := fun hEq => X.loopless.irrefl a (hEq ▸ (ha_adj b).mpr (Or.inr rfl))
  have hua : u ≠ a := fun hEq => X.loopless.irrefl a (hEq ▸ (ha_adj u).mpr (Or.inl rfl))
  have hwb : w ≠ b := fun hEq => X.loopless.irrefl b (hEq ▸ (hb_adj w).mpr (Or.inr rfl))
  let Xc := contractEdgeGraph X a b w hwa.symm
  let s : {v : V // v ≠ b} := ⟨a, hab⟩
  let φ : V → {v : V // v ≠ b} := fun v => if hv : v = b then s else ⟨v, hv⟩
  have hφ_b : φ b = s := by simp [φ]
  have hφ_a : φ a = s := by simp [φ, hab, s]
  have hφ_u : (φ u).1 = u := by simp [φ, hub]
  have hφ_w : (φ w).1 = w := by simp [φ, hwb]
  have hφ_adj : ∀ x y : V, X.Adj x y → φ x = φ y ∨ Xc.Adj (φ x) (φ y) := by
    intro x y hxy
    by_cases hxb : x = b
    · rcases (hb_adj y).mp (hxb ▸ hxy) with hya | hyw
      · exact Or.inl (by rw [hxb, hya, hφ_b, hφ_a])
      · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
        · rw [hxb, hφ_b]
        · rw [hyw, hφ_w]
    · by_cases hyb : y = b
      · rcases (hb_adj x).mp (hyb ▸ hxy.symm) with hxa | hxw
        · exact Or.inl (by rw [hxa, hyb, hφ_a, hφ_b])
        · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
          · rw [hxw, hφ_w]
          · rw [hyb, hφ_b]
      · exact Or.inr (Or.inl (by simpa [φ, hxb, hyb] using hxy))
  have hconn_image : ∀ S : Set V, (X.induce S).Connected → (Xc.induce (φ '' S)).Connected := by
    intro S hS
    obtain ⟨⟨x₀, hx₀⟩⟩ := hS.nonempty
    have : Nonempty (φ '' S : Set {v : V // v ≠ b}) := ⟨⟨φ x₀, x₀, hx₀, rfl⟩⟩
    refine ⟨fun x y => ?_⟩
    obtain ⟨x', hx', hfx⟩ := x.2
    obtain ⟨y', hy', hfy⟩ := y.2
    obtain ⟨p⟩ := hS ⟨x', hx'⟩ ⟨y', hy'⟩
    have hwalk : ∀ {p₁ p₂ : S} (q : (X.induce S).Walk p₁ p₂),
        (Xc.induce (φ '' S)).Reachable ⟨φ p₁.1, p₁.1, p₁.2, rfl⟩ ⟨φ p₂.1, p₂.1, p₂.2, rfl⟩ := by
      intro p₁ p₂ q
      induction q with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons c d e hcd r ih =>
        rcases hφ_adj c.1 d.1 hcd with hEq | hAdj
        · have hsub : (⟨φ c.1, c.1, c.2, rfl⟩ : (φ '' S : Set _)) =
              ⟨φ d.1, d.1, d.2, rfl⟩ := Subtype.ext hEq
          exact hsub ▸ ih
        · have hAdj' :
              (Xc.induce (φ '' S)).Adj ⟨φ c.1, c.1, c.2, rfl⟩ ⟨φ d.1, d.1, d.2, rfl⟩ := hAdj
          exact hAdj'.reachable.trans ih
    have h1 : x = ⟨φ x', x', hx', rfl⟩ := Subtype.ext hfx.symm
    have h2 : y = ⟨φ y', y', hy', rfl⟩ := Subtype.ext hfy.symm
    rw [h1, h2]
    exact hwalk p
  by_cases hsplit : ∃ x y : W, x ≠ y ∧ a ∈ B x ∧ b ∈ B y
  · obtain ⟨x, y, hxy, hax, hby⟩ := hsplit
    have ha_deg2 : B x = {a} → ∃ u₀ : W, ∀ z : W, F.Adj x z → z = y ∨ z = u₀ := by
      intro hBx
      by_cases hu_in : ∃ u₀ : W, u ∈ B u₀
      · obtain ⟨u₀, hu₀⟩ := hu_in
        refine ⟨u₀, fun z hxz => ?_⟩
        obtain ⟨p, hp, q, hq, hpq⟩ := hadj x z hxz
        rw [hBx, Set.mem_singleton_iff] at hp
        rcases (ha_adj q).mp (hp ▸ hpq) with hqu | hqb
        · right; by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqu ▸ hq) hu₀
        · left; by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqb ▸ hq) hby
      · push Not at hu_in
        refine ⟨y, fun z hxz => ?_⟩
        obtain ⟨p, hp, q, hq, hpq⟩ := hadj x z hxz
        rw [hBx, Set.mem_singleton_iff] at hp
        rcases (ha_adj q).mp (hp ▸ hpq) with hqu | hqb
        · exact absurd (hqu ▸ hq) (hu_in z)
        · left; by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqb ▸ hq) hby
    have hb_deg2 : B y = {b} → ∃ w₀ : W, ∀ z : W, F.Adj y z → z = x ∨ z = w₀ := by
      intro hBy
      by_cases hw_in : ∃ w₀ : W, w ∈ B w₀
      · obtain ⟨w₀, hw₀⟩ := hw_in
        refine ⟨w₀, fun z hyz => ?_⟩
        obtain ⟨p, hp, q, hq, hpq⟩ := hadj y z hyz
        rw [hBy, Set.mem_singleton_iff] at hp
        rcases (hb_adj q).mp (hp ▸ hpq) with hqa | hqw
        · left; by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqa ▸ hq) hax
        · right; by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqw ▸ hq) hw₀
      · push Not at hw_in
        refine ⟨x, fun z hyz => ?_⟩
        obtain ⟨p, hp, q, hq, hpq⟩ := hadj y z hyz
        rw [hBy, Set.mem_singleton_iff] at hp
        rcases (hb_adj q).mp (hp ▸ hpq) with hqa | hqw
        · left; by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqa ▸ hq) hax
        · exact absurd (hqw ▸ hq) (hw_in z)
    have hnot_both : ¬ (B x = {a} ∧ B y = {b}) := by
      rintro ⟨hBx, hBy⟩
      by_cases hFxy : F.Adj x y
      · exact hF.no_edge_deg_le_two x y hFxy (ha_deg2 hBx) (hb_deg2 hBy)
      · obtain ⟨z₁, z₂, hzne, hz₁, hz₂⟩ := hF.exists_two_adj x
        obtain ⟨u₀, hu₀⟩ := ha_deg2 hBx
        have h1 : z₁ = u₀ := (hu₀ z₁ hz₁).resolve_left fun hEq => hFxy (hEq ▸ hz₁)
        have h2 : z₂ = u₀ := (hu₀ z₂ hz₂).resolve_left fun hEq => hFxy (hEq ▸ hz₂)
        exact hzne (h1.trans h2.symm)
    have hor : (∃ p ∈ B x, p ≠ a) ∨ (∃ q ∈ B y, q ≠ b) := by
      by_contra hnone
      push Not at hnone
      apply hnot_both
      constructor
      · ext p; exact ⟨fun hp => Set.mem_singleton_iff.mpr (hnone.1 p hp),
          fun hp => (Set.mem_singleton_iff.mp hp) ▸ hax⟩
      · ext q; exact ⟨fun hq => Set.mem_singleton_iff.mpr (hnone.2 q hq),
          fun hq => (Set.mem_singleton_iff.mp hq) ▸ hby⟩
    rcases hor with ⟨p₀, hp₀, hp₀a⟩ | ⟨q₀, hq₀, hq₀b⟩
    · -- Subcase 4a: `|B x| ≥ 2`, erase leaf `a` from `B x`
      have hux : u ∈ B x := by
        obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable (hconn x ⟨a, hax⟩ ⟨p₀, hp₀⟩)
        cases p with
        | nil => exact absurd rfl hp₀a
        | @cons _ z _ haz _ =>
          rcases (ha_adj z).mp haz with hzu | hzb
          · exact hzu ▸ hp z (by simp)
          · exact absurd (hzb ▸ hp z (by simp))
              (fun hbx => Set.disjoint_left.mp (hdisj hxy) hbx hby)
      have hleaf_a : ∀ z ∈ B x, X.Adj a z → z = u := by
        intro z hz haz
        rcases (ha_adj z).mp haz with hzu | hzb
        · exact hzu
        · exact absurd (hzb ▸ hz) (fun hbx => Set.disjoint_left.mp (hdisj hxy) hbx hby)
      have hBx'_conn : (X.induce (B x \ {a})).Connected :=
        induce_connected_erase_leaf (hconn x) hux hua hleaf_a
      let B' : W → Set {v : V // v ≠ b} := fun z =>
        if z = x then φ '' (B x \ {a}) else φ '' (B z)
      have hφ_inj_on : Pairwise (Function.onFun Disjoint B') := by
        intro z₁ z₂ hne
        dsimp only [Function.onFun]
        rw [Set.disjoint_left]
        intro r hr₁ hr₂
        have hmem_src : ∀ z : W, r ∈ B' z → ∃ v ∈ B z, (z = x → v ≠ a) ∧ φ v = r := by
          intro z hz
          by_cases hzx : z = x
          · subst hzx
            simp only [B', ↓reduceIte] at hz
            obtain ⟨v, ⟨hvB, hva⟩, hfv⟩ := hz
            exact ⟨v, hvB, fun _ => hva, hfv⟩
          · simp only [B', hzx, ↓reduceIte] at hz
            obtain ⟨v, hvB, hfv⟩ := hz
            exact ⟨v, hvB, fun h => absurd h hzx, hfv⟩
        obtain ⟨v₁, hv₁B, hv₁a, hfv₁⟩ := hmem_src z₁ hr₁
        obtain ⟨v₂, hv₂B, hv₂a, hfv₂⟩ := hmem_src z₂ hr₂
        have hvne : v₁ ≠ v₂ := fun hEq => Set.disjoint_left.mp (hdisj hne) hv₁B (hEq ▸ hv₂B)
        have hEqφ : (φ v₁).1 = (φ v₂).1 := congrArg Subtype.val (hfv₁.trans hfv₂.symm)
        by_cases h1b : v₁ = b
        · have h2b : v₂ ≠ b := fun hEq => hvne (h1b.trans hEq.symm)
          have h2a : v₂ = a := by
            rw [h1b, hφ_b] at hEqφ
            simp only [φ, h2b, ↓reduceDIte, s] at hEqφ
            exact hEqφ.symm
          have hz₂x : z₂ = x := by
            by_contra hz₂; exact Set.disjoint_left.mp (hdisj hz₂) (h2a ▸ hv₂B) hax
          exact hv₂a hz₂x h2a
        · by_cases h2b : v₂ = b
          · have h1a : v₁ = a := by
              rw [h2b, hφ_b] at hEqφ
              simp only [φ, h1b, ↓reduceDIte, s] at hEqφ
              exact hEqφ
            have hz₁x : z₁ = x := by
              by_contra hz₁; exact Set.disjoint_left.mp (hdisj hz₁) (h1a ▸ hv₁B) hax
            exact hv₁a hz₁x h1a
          · simp only [φ, h1b, h2b, ↓reduceDIte] at hEqφ
            exact hvne hEqφ
      refine ⟨B', fun z => ?_, hφ_inj_on, fun z₁ z₂ hz12 => ?_⟩
      · by_cases hzx : z = x
        · subst hzx
          have hEq : B' z = φ '' (B z \ {a}) := by simp [B']
          rw [hEq]
          exact hconn_image _ hBx'_conn
        · have hEq : B' z = φ '' (B z) := by simp [B', hzx]
          rw [hEq]
          exact hconn_image _ (hconn z)
      · obtain ⟨p, hp, q, hq, hpq⟩ := hadj z₁ z₂ hz12
        by_cases hpa : p = a
        · have hz₁x : z₁ = x := by
            by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpa ▸ hp) hax
          rcases (ha_adj q).mp (hpa ▸ hpq) with hqu | hqb
          · exact absurd (hqu ▸ hq)
              (fun hqu' => Set.disjoint_left.mp (hdisj (F.ne_of_adj hz12)) (hz₁x ▸ hux) hqu')
          · have hz₂y : z₂ = y := by
              by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqb ▸ hq) hby
            refine ⟨φ u, ?_, φ b, ?_, ?_⟩
            · rw [hz₁x]; simp only [B', ↓reduceIte]; exact ⟨u, ⟨hux, hua⟩, rfl⟩
            · rw [hz₂y]; simp only [B', hxy.symm, ↓reduceIte]; exact ⟨b, hby, rfl⟩
            · change Xc.Adj (φ u) (φ b)
              left
              rw [hφ_u, hφ_b]
              exact ((ha_adj u).mpr (Or.inl rfl)).symm
        · by_cases hqa : q = a
          · have hz₂x : z₂ = x := by
              by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqa ▸ hq) hax
            rcases (ha_adj p).mp (hqa ▸ hpq.symm) with hpu | hpb
            · exact absurd (hpu ▸ hp)
                (fun hpu' => Set.disjoint_left.mp (hdisj (F.ne_of_adj hz12)) hpu' (hz₂x ▸ hux))
            · have hz₁y : z₁ = y := by
                by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpb ▸ hp) hby
              refine ⟨φ b, ?_, φ u, ?_, ?_⟩
              · rw [hz₁y]; simp only [B', hxy.symm, ↓reduceIte]; exact ⟨b, hby, rfl⟩
              · rw [hz₂x]; simp only [B', ↓reduceIte]; exact ⟨u, ⟨hux, hua⟩, rfl⟩
              · change Xc.Adj (φ b) (φ u)
                left
                rw [hφ_b, hφ_u]
                exact (ha_adj u).mpr (Or.inl rfl)
          · have h1 : φ p ∈ B' z₁ := by
              by_cases hz₁ : z₁ = x
              · subst hz₁; simp only [B', ↓reduceIte]; exact ⟨p, ⟨hp, hpa⟩, rfl⟩
              · simp only [B', hz₁, ↓reduceIte]; exact ⟨p, hp, rfl⟩
            have h2 : φ q ∈ B' z₂ := by
              by_cases hz₂ : z₂ = x
              · subst hz₂; simp only [B', ↓reduceIte]; exact ⟨q, ⟨hq, hqa⟩, rfl⟩
              · simp only [B', hz₂, ↓reduceIte]; exact ⟨q, hq, rfl⟩
            rcases hφ_adj p q hpq with hEq | hAdj
            · exact absurd h2
                (Set.disjoint_left.mp (hφ_inj_on (F.ne_of_adj hz12)) (hEq ▸ h1))
            · exact ⟨φ p, h1, φ q, h2, hAdj⟩
    · -- Subcase 4b: `|B y| ≥ 2`, erase leaf `b` from `B y`
      have hwy : w ∈ B y := by
        obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable (hconn y ⟨b, hby⟩ ⟨q₀, hq₀⟩)
        cases p with
        | nil => exact absurd rfl hq₀b
        | @cons _ z _ hbz _ =>
          rcases (hb_adj z).mp hbz with hza | hzw
          · exact absurd (hza ▸ hp z (by simp))
              (fun hay => Set.disjoint_left.mp (hdisj hxy) hax hay)
          · exact hzw ▸ hp z (by simp)
      have hleaf_b : ∀ z ∈ B y, X.Adj b z → z = w := by
        intro z hz hbz
        rcases (hb_adj z).mp hbz with hza | hzw
        · exact absurd (hza ▸ hz) (fun hay => Set.disjoint_left.mp (hdisj hxy) hax hay)
        · exact hzw
      have hBy'_conn : (X.induce (B y \ {b})).Connected :=
        induce_connected_erase_leaf (hconn y) hwy hwb hleaf_b
      let B' : W → Set {v : V // v ≠ b} := fun z =>
        if z = y then φ '' (B y \ {b}) else φ '' (B z)
      have hφ_inj_on : Pairwise (Function.onFun Disjoint B') := by
        intro z₁ z₂ hne
        dsimp only [Function.onFun]
        rw [Set.disjoint_left]
        intro r hr₁ hr₂
        have hmem_src : ∀ z : W, r ∈ B' z → ∃ v ∈ B z, v ≠ b ∧ φ v = r := by
          intro z hz
          by_cases hzy : z = y
          · subst hzy
            simp only [B', ↓reduceIte] at hz
            obtain ⟨v, ⟨hvB, hvb⟩, hfv⟩ := hz
            exact ⟨v, hvB, hvb, hfv⟩
          · simp only [B', hzy, ↓reduceIte] at hz
            obtain ⟨v, hvB, hfv⟩ := hz
            have hvb : v ≠ b := fun hEq =>
              Set.disjoint_left.mp (hdisj hzy) (hEq ▸ hvB) hby
            exact ⟨v, hvB, hvb, hfv⟩
        obtain ⟨v₁, hv₁B, hv₁b, hfv₁⟩ := hmem_src z₁ hr₁
        obtain ⟨v₂, hv₂B, hv₂b, hfv₂⟩ := hmem_src z₂ hr₂
        have hvEq : v₁ = v₂ := by
          have := congrArg Subtype.val (hfv₁.trans hfv₂.symm)
          simp only [φ, hv₁b, hv₂b, ↓reduceDIte] at this
          exact this
        exact Set.disjoint_left.mp (hdisj hne) hv₁B (hvEq ▸ hv₂B)
      refine ⟨B', fun z => ?_, hφ_inj_on, fun z₁ z₂ hz12 => ?_⟩
      · by_cases hzy : z = y
        · subst hzy
          have hEq : B' z = φ '' (B z \ {b}) := by simp [B']
          rw [hEq]
          exact hconn_image _ hBy'_conn
        · have hEq : B' z = φ '' (B z) := by simp [B', hzy]
          rw [hEq]
          exact hconn_image _ (hconn z)
      · obtain ⟨p, hp, q, hq, hpq⟩ := hadj z₁ z₂ hz12
        by_cases hpb : p = b
        · have hz₁y : z₁ = y := by
            by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpb ▸ hp) hby
          rcases (hb_adj q).mp (hpb ▸ hpq) with hqa | hqw
          · have hz₂x : z₂ = x := by
              by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqa ▸ hq) hax
            refine ⟨φ w, ?_, φ a, ?_, ?_⟩
            · rw [hz₁y]; simp only [B', ↓reduceIte]; exact ⟨w, ⟨hwy, hwb⟩, rfl⟩
            · rw [hz₂x]; simp only [B', hxy, ↓reduceIte]; exact ⟨a, hax, rfl⟩
            · change Xc.Adj (φ w) (φ a)
              exact Or.inr (Or.inr ⟨hφ_w, by rw [hφ_a]⟩)
          · exact absurd (hqw ▸ hq)
              (fun hqw' => Set.disjoint_left.mp (hdisj (F.ne_of_adj hz12)) (hz₁y ▸ hwy) hqw')
        · by_cases hqb : q = b
          · have hz₂y : z₂ = y := by
              by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hqb ▸ hq) hby
            rcases (hb_adj p).mp (hqb ▸ hpq.symm) with hpa | hpw
            · have hz₁x : z₁ = x := by
                by_contra hne; exact Set.disjoint_left.mp (hdisj hne) (hpa ▸ hp) hax
              refine ⟨φ a, ?_, φ w, ?_, ?_⟩
              · rw [hz₁x]; simp only [B', hxy, ↓reduceIte]; exact ⟨a, hax, rfl⟩
              · rw [hz₂y]; simp only [B', ↓reduceIte]; exact ⟨w, ⟨hwy, hwb⟩, rfl⟩
              · change Xc.Adj (φ a) (φ w)
                exact Or.inr (Or.inl ⟨by rw [hφ_a], hφ_w⟩)
            · exact absurd (hpw ▸ hp)
                (fun hpw' => Set.disjoint_left.mp (hdisj (F.ne_of_adj hz12)) hpw' (hz₂y ▸ hwy))
          · have h1 : φ p ∈ B' z₁ := by
              by_cases hz₁ : z₁ = y
              · subst hz₁; simp only [B', ↓reduceIte]; exact ⟨p, ⟨hp, hpb⟩, rfl⟩
              · simp only [B', hz₁, ↓reduceIte]; exact ⟨p, hp, rfl⟩
            have h2 : φ q ∈ B' z₂ := by
              by_cases hz₂ : z₂ = y
              · subst hz₂; simp only [B', ↓reduceIte]; exact ⟨q, ⟨hq, hqb⟩, rfl⟩
              · simp only [B', hz₂, ↓reduceIte]; exact ⟨q, hq, rfl⟩
            rcases hφ_adj p q hpq with hEq | hAdj
            · exact absurd h2
                (Set.disjoint_left.mp (hφ_inj_on (F.ne_of_adj hz12)) (hEq ▸ h1))
            · exact ⟨φ p, h1, φ q, h2, hAdj⟩
  · -- Cases 1, 2, 3: `a` and `b` are NOT in distinct branch sets
    push Not at hsplit
    have hdisj' : Pairwise (Function.onFun Disjoint (fun z => φ '' B z)) := by
      intro z₁ z₂ hne
      dsimp only [Function.onFun]
      rw [Set.disjoint_left]
      rintro r ⟨v₁, hv₁, rfl⟩ ⟨v₂, hv₂, hfv⟩
      by_cases h1b : v₁ = b
      · by_cases h2b : v₂ = b
        · exact Set.disjoint_left.mp (hdisj hne) (h1b ▸ hv₁) (h2b ▸ hv₂)
        · have h2a : v₂ = a := by
            have := congrArg Subtype.val hfv
            rw [h1b, hφ_b] at this
            simp only [φ, h2b, ↓reduceDIte, s] at this
            exact this
          exact hsplit z₂ z₁ hne.symm (h2a ▸ hv₂) (h1b ▸ hv₁)
      · by_cases h2b : v₂ = b
        · have h1a : v₁ = a := by
            have := congrArg Subtype.val hfv
            rw [h2b, hφ_b] at this
            simp only [φ, h1b, ↓reduceDIte, s] at this
            exact this.symm
          exact hsplit z₁ z₂ hne (h1a ▸ hv₁) (h2b ▸ hv₂)
        · have hvEq : v₁ = v₂ := by
            have := congrArg Subtype.val hfv
            simp only [φ, h1b, h2b, ↓reduceDIte] at this
            exact this.symm
          exact Set.disjoint_left.mp (hdisj hne) hv₁ (hvEq ▸ hv₂)
    refine ⟨fun z => φ '' B z, fun z => hconn_image _ (hconn z), hdisj', fun z₁ z₂ hz12 => ?_⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := hadj z₁ z₂ hz12
    rcases hφ_adj p q hpq with hEq | hAdj
    · exact absurd ⟨q, hq, hEq.symm⟩
        (Set.disjoint_left.mp (hdisj' (F.ne_of_adj hz12)) ⟨p, hp, rfl⟩)
    · exact ⟨φ p, ⟨p, hp, rfl⟩, φ q, ⟨q, hq, rfl⟩, hAdj⟩

/-- **Lemma 4 (Adjacent Degree-2 Edge Contraction):** If `X` contains adjacent degree-2 vertices
`a, b` with `N(a) = {u, b}` and `N(b) = {a, w}` where `u ≠ w`, `u ≠ b`, `w ≠ a`, and the
contracted graph `contractEdgeGraph X a b w` is outerplanar, then `X` is outerplanar. -/
theorem isOuterplanar_of_contract_adj_deg2 {V : Type*} {X : SimpleGraph V} {a b u w : V}
    (huw : u ≠ w) (hub : u ≠ b) (hwa : w ≠ a)
    (ha_adj : ∀ z : V, X.Adj a z ↔ z = u ∨ z = b)
    (hb_adj : ∀ z : V, X.Adj b z ↔ z = a ∨ z = w)
    (hXc : IsOuterplanar (contractEdgeGraph X a b w hwa.symm)) : IsOuterplanar X :=
  ⟨fun hK4 => hXc.1 (hasMinor_of_contract_adj_deg2 isForbiddenOuterplanarMinor_K4
      huw hub hwa ha_adj hb_adj hK4),
   fun hK23 => hXc.2 (hasMinor_of_contract_adj_deg2 isForbiddenOuterplanarMinor_K23
      huw hub hwa ha_adj hb_adj hK23)⟩

/-! ### 7. Lemma 5: 1-Sum Preserves Outerplanarity -/

/-- **Lemma 5 (general forbidden-minor form):** In a 1-sum `V₁ ∪ V₂ = univ`, `V₁ ∩ V₂ = {j}`
with no edges between `V₁ \ {j}` and `V₂ \ {j}`, any minor `F` of `X` satisfying
`IsForbiddenOuterplanarMinor` (with `Nonempty W`) is already a minor of `X.induce V₁` or
`X.induce V₂`. -/
lemma hasMinor_one_sum {V W : Type*} [Nonempty W] {X : SimpleGraph V} {F : SimpleGraph W}
    (hF : IsForbiddenOuterplanarMinor F) {V₁ V₂ : Set V} {j : V}
    (hunion : V₁ ∪ V₂ = Set.univ) (hinter : V₁ ∩ V₂ = {j})
    (hno : ∀ x ∈ V₁, ∀ y ∈ V₂, x ≠ j → y ≠ j → ¬ X.Adj x y)
    (hXF : HasMinor X F) :
    HasMinor (X.induce V₁) F ∨ HasMinor (X.induce V₂) F := by
  obtain ⟨B, hconn, hdisj, hadj⟩ := hXF
  have hj1 : j ∈ V₁ := (Set.mem_inter_iff _ _ _ |>.mp (hinter.symm ▸ Set.mem_singleton j)).1
  have hj2 : j ∈ V₂ := (Set.mem_inter_iff _ _ _ |>.mp (hinter.symm ▸ Set.mem_singleton j)).2
  have hunion2 : V₂ ∪ V₁ = Set.univ := by rw [Set.union_comm]; exact hunion
  have hno2 : ∀ x ∈ V₂, ∀ y ∈ V₁, x ≠ j → y ≠ j → ¬ X.Adj x y :=
    fun x hx y hy hxj hyj hxy => hno y hy x hx hyj hxj hxy.symm
  have hside : ∀ w : W, j ∉ B w → B w ⊆ V₁ ∨ B w ⊆ V₂ := by
    intro w hjw
    obtain ⟨⟨x₀, hx₀⟩⟩ := (hconn w).nonempty
    have hx₀all : x₀ ∈ V₁ ∪ V₂ := by rw [hunion]; trivial
    rcases hx₀all with hx₁ | hx₂
    · exact Or.inl (subset_side_of_induce_connected hunion hno (hconn w) hjw hx₀ hx₁)
    · exact Or.inr (subset_side_of_induce_connected hunion2 hno2 (hconn w) hjw hx₀ hx₂)
  have hsame_side : ∀ u v : W, F.Adj u v → j ∉ B u → j ∉ B v → B u ⊆ V₁ → B v ⊆ V₁ := by
    intro u v huv hju hjv hu1
    rcases hside v hjv with hv1 | hv2
    · exact hv1
    · obtain ⟨x, hx, y, hy, hxy⟩ := hadj u v huv
      exact absurd hxy (hno x (hu1 hx) y (hv2 hy)
        (fun hEq => hju (hEq ▸ hx)) (fun hEq => hjv (hEq ▸ hy)))
  have hlift_side : ∀ (S T : Set V) (hU : S ∪ T = Set.univ)
      (hN : ∀ x ∈ S, ∀ y ∈ T, x ≠ j → y ≠ j → ¬ X.Adj x y)
      (_ : j ∈ S),
      (∀ w : W, j ∉ B w → B w ⊆ S) → HasMinor (X.induce S) F := by
    intro S T hU hN hjS hallS
    refine ⟨fun w => {x : S | x.1 ∈ B w}, ?_, ?_, ?_⟩
    · intro w
      by_cases hjw : j ∈ B w
      · have hBS : (X.induce (B w ∩ S)).Connected :=
          induce_connected_inter_side hU hN (hconn w) hjw hjS
        have : Nonempty ({x : S | x.1 ∈ B w} : Set S) := ⟨⟨⟨j, hjS⟩, hjw⟩⟩
        refine ⟨fun a b => ?_⟩
        obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable
          (hBS ⟨a.1.1, a.2, a.1.2⟩ ⟨b.1.1, b.2, b.1.2⟩)
        have hlift_p : ∀ {c d : V} (q : X.Walk c d) (hq : ∀ z ∈ q.support, z ∈ B w ∩ S),
            ((X.induce S).induce {x : S | x.1 ∈ B w}).Reachable
              ⟨⟨c, (hq c (by simp)).2⟩, (hq c (by simp)).1⟩
              ⟨⟨d, (hq d (by simp)).2⟩, (hq d (by simp)).1⟩ := by
          intro c d q hq
          induction q with
          | nil => exact SimpleGraph.Reachable.refl _
          | @cons e f g hef r ih =>
            have he := hq e (by simp)
            have hf := hq f (by simp)
            have hr : ∀ z ∈ r.support, z ∈ B w ∩ S := fun z hz => hq z (by simp [hz])
            have hstep : ((X.induce S).induce {x : S | x.1 ∈ B w}).Adj
                ⟨⟨e, he.2⟩, he.1⟩ ⟨⟨f, hf.2⟩, hf.1⟩ := hef
            exact hstep.reachable.trans (ih hr)
        exact hlift_p p hp
      · have hsub : B w ⊆ S := hallS w hjw
        obtain ⟨⟨x₀, hx₀⟩⟩ := (hconn w).nonempty
        have : Nonempty ({x : S | x.1 ∈ B w} : Set S) := ⟨⟨⟨x₀, hsub hx₀⟩, hx₀⟩⟩
        refine ⟨fun a b => ?_⟩
        obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable (hconn w ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)
        have hlift_p : ∀ {c d : V} (q : X.Walk c d) (hq : ∀ z ∈ q.support, z ∈ B w),
            ((X.induce S).induce {x : S | x.1 ∈ B w}).Reachable
              ⟨⟨c, hsub (hq c (by simp))⟩, hq c (by simp)⟩
              ⟨⟨d, hsub (hq d (by simp))⟩, hq d (by simp)⟩ := by
          intro c d q hq
          induction q with
          | nil => exact SimpleGraph.Reachable.refl _
          | @cons e f g hef r ih =>
            have he := hq e (by simp)
            have hf := hq f (by simp)
            have hr : ∀ z ∈ r.support, z ∈ B w := fun z hz => hq z (by simp [hz])
            have hstep : ((X.induce S).induce {x : S | x.1 ∈ B w}).Adj
                ⟨⟨e, hsub he⟩, he⟩ ⟨⟨f, hsub hf⟩, hf⟩ := hef
            exact hstep.reachable.trans (ih hr)
        exact hlift_p p hp
    · intro u v huv
      dsimp only [Function.onFun]
      rw [Set.disjoint_left]
      intro x hxu hxv
      exact Set.disjoint_left.mp (hdisj huv) hxu hxv
    · intro u v huv
      obtain ⟨x, hx, y, hy, hxy⟩ := hadj u v huv
      have hxs : x ∈ S := by
        by_cases hju : j ∈ B u
        · by_cases hxj : x = j
          · exact hxj ▸ hjS
          · have hyv : y ∈ S :=
              hallS v (fun hjv => Set.disjoint_left.mp (hdisj (F.ne_of_adj huv)) hju hjv) hy
            have hyj : y ≠ j := fun hEq =>
              Set.disjoint_left.mp (hdisj (F.ne_of_adj huv)) hju (hEq ▸ hy)
            have hxall : x ∈ S ∪ T := by rw [hU]; trivial
            rcases hxall with h1 | h2
            · exact h1
            · exact absurd hxy.symm (hN y hyv x h2 hyj hxj)
        · exact hallS u hju hx
      have hys : y ∈ S := by
        by_cases hjv : j ∈ B v
        · by_cases hyj : y = j
          · exact hyj ▸ hjS
          · have hxu : x ∈ S :=
              hallS u (fun hju => Set.disjoint_left.mp (hdisj (F.ne_of_adj huv)) hju hjv) hx
            have hxj : x ≠ j := fun hEq =>
              Set.disjoint_left.mp (hdisj (F.ne_of_adj huv)) (hEq ▸ hx) hjv
            have hyall : y ∈ S ∪ T := by rw [hU]; trivial
            rcases hyall with h1 | h2
            · exact h1
            · exact absurd hxy (hN x hxu y h2 hxj hyj)
        · exact hallS v hjv hy
      exact ⟨⟨x, hxs⟩, hx, ⟨y, hys⟩, hy, hxy⟩
  by_cases hj_in : ∃ w₀ : W, j ∈ B w₀
  · obtain ⟨w₀, hjw₀⟩ := hj_in
    have hnotj : ∀ w : W, w ≠ w₀ → j ∉ B w :=
      fun w hne hjw => Set.disjoint_left.mp (hdisj hne) hjw hjw₀
    obtain ⟨⟨w₁, hw₁⟩⟩ := (hF.connected_delete_vertex w₀).nonempty
    have hprop : ∀ {a b : {w : W | w ≠ w₀}} (q : (F.induce {w | w ≠ w₀}).Walk a b),
        (B a.1 ⊆ V₁ → B b.1 ⊆ V₁) ∧ (B a.1 ⊆ V₂ → B b.1 ⊆ V₂) := by
      intro a b q
      induction q with
      | nil => exact ⟨id, id⟩
      | @cons c d e hcd r ih =>
        refine ⟨fun hc => ih.1 (hsame_side c.1 d.1 hcd (hnotj c.1 c.2) (hnotj d.1 d.2) hc),
          fun hc => ih.2 ?_⟩
        rcases hside d.1 (hnotj d.1 d.2) with hd1 | hd2
        · obtain ⟨x, hx, y, hy, hxy⟩ := hadj c.1 d.1 hcd
          exact absurd hxy (hno2 x (hc hx) y (hd1 hy)
            (fun hEq => hnotj c.1 c.2 (hEq ▸ hx)) (fun hEq => hnotj d.1 d.2 (hEq ▸ hy)))
        · exact hd2
    rcases hside w₁ (hnotj w₁ hw₁) with hw₁1 | hw₁2
    · left
      apply hlift_side V₁ V₂ hunion hno hj1
      intro w hjw
      have hwne : w ≠ w₀ := fun hEq => hjw (hEq ▸ hjw₀)
      obtain ⟨q⟩ := hF.connected_delete_vertex w₀ ⟨w₁, hw₁⟩ ⟨w, hwne⟩
      exact (hprop q).1 hw₁1
    · right
      apply hlift_side V₂ V₁ hunion2 hno2 hj2
      intro w hjw
      have hwne : w ≠ w₀ := fun hEq => hjw (hEq ▸ hjw₀)
      obtain ⟨q⟩ := hF.connected_delete_vertex w₀ ⟨w₁, hw₁⟩ ⟨w, hwne⟩
      exact (hprop q).2 hw₁2
  · push Not at hj_in
    obtain ⟨w₁⟩ := ‹Nonempty W›
    have hFconn : F.Connected := hF.connected ⟨w₁⟩
    have hprop : ∀ {a b : W} (q : F.Walk a b),
        (B a ⊆ V₁ → B b ⊆ V₁) ∧ (B a ⊆ V₂ → B b ⊆ V₂) := by
      intro a b q
      induction q with
      | nil => exact ⟨id, id⟩
      | @cons c d e hcd r ih =>
        refine ⟨fun hc => ih.1 (hsame_side c d hcd (hj_in c) (hj_in d) hc),
          fun hc => ih.2 ?_⟩
        rcases hside d (hj_in d) with hd1 | hd2
        · obtain ⟨x, hx, y, hy, hxy⟩ := hadj c d hcd
          exact absurd hxy (hno2 x (hc hx) y (hd1 hy)
            (fun hEq => hj_in c (hEq ▸ hx)) (fun hEq => hj_in d (hEq ▸ hy)))
        · exact hd2
    rcases hside w₁ (hj_in w₁) with hw₁1 | hw₁2
    · left
      apply hlift_side V₁ V₂ hunion hno hj1
      intro w _
      obtain ⟨q⟩ := hFconn w₁ w
      exact (hprop q).1 hw₁1
    · right
      apply hlift_side V₂ V₁ hunion2 hno2 hj2
      intro w _
      obtain ⟨q⟩ := hFconn w₁ w
      exact (hprop q).2 hw₁2

/-- **Lemma 5 (1-Sum Preserves Outerplanarity):** If `V₁ ∪ V₂ = univ`, `V₁ ∩ V₂ = {j}`, no edge
joins `V₁ \ {j}` to `V₂ \ {j}`, and both `X.induce V₁` and `X.induce V₂` are outerplanar, then
`X` is outerplanar. -/
theorem isOuterplanar_of_one_sum {V : Type*} {X : SimpleGraph V} {V₁ V₂ : Set V} {j : V}
    (hunion : V₁ ∪ V₂ = Set.univ) (hinter : V₁ ∩ V₂ = {j})
    (hno : ∀ x ∈ V₁, ∀ y ∈ V₂, x ≠ j → y ≠ j → ¬ X.Adj x y)
    (h1 : IsOuterplanar (X.induce V₁)) (h2 : IsOuterplanar (X.induce V₂)) :
    IsOuterplanar X := by
  refine ⟨fun hK4 => ?_, fun hK23 => ?_⟩
  · rcases hasMinor_one_sum isForbiddenOuterplanarMinor_K4 hunion hinter hno hK4 with h | h
    · exact h1.1 h
    · exact h2.1 h
  · rcases hasMinor_one_sum isForbiddenOuterplanarMinor_K23 hunion hinter hno hK23 with h | h
    · exact h1.2 h
    · exact h2.2 h

end LeanForge.CosteOuterplanar
