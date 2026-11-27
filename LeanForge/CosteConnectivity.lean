/-
Copyright (c) 2026 Parker Lipscomb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Parker Lipscomb
-/
module

public import LeanForge.CosteMinorAPI
public import Mathlib.Data.Finset.Max

/-!
# Connectivity and Minor Lemmas for the Coste–Csikós–Viennot Proof (Lemmas 6, 1, 2)

This file implements the connectivity and Dirac–Duffin infrastructure:

1. Finite-graph connectivity predicates `IsTwoConnected` and `IsThreeConnected`, together with
   walk-exit and component helpers.
2. **Lemma 6 (`exists_endBlock`):** Every finite simple graph with at least one edge contains a
   connected induced subgraph `B` (`|B| ≥ 2`) and an attachment vertex `z ∈ B` such that `B` is
   either `K_2` (`|B| = 2`) or 2-connected, and every `v ∈ B \ {z}` has all its `G`-neighbors
   inside `B`.
3. **Lemma 1 (`hasMinor_K4_of_isThreeConnected`):** Every finite simple 3-connected graph has a
   `K_4` minor.
4. **Lemma 2 (`exists_deg_two_avoiding_edge`, Dirac–Duffin):** Every finite simple 2-connected
   `K_4`-minor-free graph `B` and edge `xy ∈ E(B)` admits a vertex `v ∉ {x, y}` of degree 2 in `B`.
-/

@[expose] public section

namespace LeanForge.CosteOuterplanar

/-! ### 1. Connectivity Predicates and Elementary Helpers -/

/-- A finite simple graph `G` is *2-connected* if `|V(G)| ≥ 3` and deleting any single vertex
leaves a connected graph. -/
def IsTwoConnected {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ ∀ v : V, (G.induce {x : V | x ≠ v}).Connected

/-- A finite simple graph `G` is *3-connected* if `|V(G)| ≥ 4` and deleting any subset of at most
2 vertices leaves a connected graph. -/
def IsThreeConnected {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 2 → (G.induce {x : V | x ∉ S}).Connected

/-- Any walk starting in `A` and ending outside `A` has a first step exiting `A`, whose prefix
before that step stays inside `A`. -/
lemma walk_first_exit {V : Type*} {G : SimpleGraph V} {A : Set V} {u v : V}
    (p : G.Walk u v) (hu : u ∈ A) (hv : v ∉ A) :
    ∃ (a b : V) (p₁ : G.Walk u a) (p₂ : G.Walk b v),
      a ∈ A ∧ b ∉ A ∧ G.Adj a b ∧
      (∀ x ∈ p₁.support, x ∈ A) ∧
      (∀ x ∈ p₁.support, x ∈ p.support) ∧
      (∀ x ∈ p₂.support, x ∈ p.support) ∧
      p₂.length < p.length := by
  induction p with
  | nil => exact absurd hu hv
  | @cons x y z hxy q ih =>
    by_cases hy : y ∈ A
    · obtain ⟨a, b, p₁, p₂, ha, hb, hab, hp₁A, hp₁, hp₂, hlen⟩ := ih hy hv
      refine ⟨a, b, SimpleGraph.Walk.cons hxy p₁, p₂, ha, hb, hab, ?_, ?_, ?_, ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hu
        · exact hp₁A w hw
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · simp
        · exact List.mem_cons_of_mem x (hp₁ w hw)
      · intro w hw
        exact List.mem_cons_of_mem x (hp₂ w hw)
      · simp only [SimpleGraph.Walk.length_cons]
        omega
    · refine ⟨x, y, SimpleGraph.Walk.nil, q, hu, hy, hxy, ?_, ?_, ?_, ?_⟩
      · intro w hw
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
        exact hw ▸ hu
      · intro w hw
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
        exact hw ▸ List.mem_cons_self
      · intro w hw
        exact List.mem_cons_of_mem x hw
      · simp

/-- Reachability in `G.induce S` from a fixed `u₀ ∈ S` defines a connected component of `G[S]`. -/
lemma induce_component_connected {V : Type*} {G : SimpleGraph V} {S : Set V}
    {u₀ : V} (hu₀ : u₀ ∈ S) :
    (G.induce {v : V | ∃ hv : v ∈ S, (G.induce S).Reachable ⟨u₀, hu₀⟩ ⟨v, hv⟩}).Connected := by
  set K : Set V := {v : V | ∃ hv : v ∈ S, (G.induce S).Reachable ⟨u₀, hu₀⟩ ⟨v, hv⟩}
  have hu₀K : u₀ ∈ K := ⟨hu₀, SimpleGraph.Reachable.refl _⟩
  have : Nonempty K := ⟨⟨u₀, hu₀K⟩⟩
  refine ⟨fun x y => ?_⟩
  have hto : ∀ z : K, (G.induce K).Reachable ⟨u₀, hu₀K⟩ z := by
    intro z
    obtain ⟨hzS, hreach⟩ := z.2
    obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable hreach
    have hK : ∀ w ∈ p.support, w ∈ K := by
      intro w hw
      classical
      have hwS : w ∈ S := hp w hw
      refine ⟨hwS, induce_reachable_of_walk hu₀ hwS (p.takeUntil w hw) fun t ht => ?_⟩
      exact hp t (SimpleGraph.Walk.support_takeUntil_subset_support p hw ht)
    exact induce_reachable_of_walk hu₀K z.2 p hK
  exact (hto x).symm.trans (hto y)

/-- A 2-connected graph is connected. -/
lemma IsTwoConnected.connected {V : Type*} [Fintype V] {G : SimpleGraph V}
    (h2 : IsTwoConnected G) : G.Connected := by
  classical
  have h3card : 3 ≤ Fintype.card V := h2.1
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  refine ⟨fun x y => ?_⟩
  have hcard : ({x, y} : Finset V).card ≤ 2 := Finset.card_le_two
  have hsub : (Finset.univ \ ({x, y} : Finset V)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hle : Fintype.card V ≤ ({x, y} : Finset V).card := by
      have : Finset.univ ⊆ ({x, y} : Finset V) := Finset.sdiff_eq_empty_iff_subset.mp hemp
      simpa using Finset.card_le_card this
    omega
  obtain ⟨v, hv⟩ := hsub
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hv
  obtain ⟨p, -⟩ := exists_walk_of_induce_reachable
    (h2.2 v ⟨x, Ne.symm hv.1⟩ ⟨y, Ne.symm hv.2⟩)
  exact ⟨p⟩

/-- Every 3-connected graph is 2-connected. -/
lemma IsThreeConnected.isTwoConnected {V : Type*} [Fintype V] {G : SimpleGraph V}
    (h3 : IsThreeConnected G) : IsTwoConnected G := by
  classical
  have h4card : 4 ≤ Fintype.card V := h3.1
  refine ⟨by omega, fun v => ?_⟩
  have hS := h3.2 {v} (by simp)
  have hEq : ({x : V | x ∉ ({v} : Finset V)} : Set V) = {x : V | x ≠ v} := by
    ext x
    simp
  rwa [hEq] at hS

/-- Deleting a vertex `z ∈ S` from `G.induce S` is connected iff `G.induce (S.erase z)` is
connected. -/
lemma connected_induce_subtype_ne_iff {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} {z : V} (hz : z ∈ S) :
    ((G.induce (S : Set V)).induce {x : (S : Set V) | x ≠ ⟨z, hz⟩}).Connected ↔
      (G.induce ((S.erase z : Finset V) : Set V)).Connected := by
  let e : ((G.induce (S : Set V)).induce {x : (S : Set V) | x ≠ ⟨z, hz⟩}) ≃g
      G.induce ((S.erase z : Finset V) : Set V) :=
    { toFun := fun x => ⟨x.1.1, by
        simp only [Finset.mem_coe, Finset.mem_erase]
        exact ⟨fun hEq => x.2 (Subtype.ext hEq), x.1.2⟩⟩
      invFun := fun y =>
        ⟨⟨y.1, Finset.mem_of_mem_erase y.2⟩, fun hEq =>
          (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val hEq)⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl
      map_rel_iff' := Iff.rfl }
  exact ⟨fun h => h.map e.toHom e.surjective,
    fun h => h.map e.symm.toHom e.symm.surjective⟩

/-- Sorting three pairwise distinct elements of a linear order. -/
private lemma exists_sorted_triple {α : Type*} [LinearOrder α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {P : α → Prop}
    (ha : P a) (hb : P b) (hc : P c) :
    ∃ x y z : α, x < y ∧ y < z ∧ P x ∧ P y ∧ P z := by
  rcases lt_or_gt_of_ne hab with h1 | h1 <;>
    rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  · exact ⟨a, b, c, h1, h3, ha, hb, hc⟩
  · exact ⟨a, c, b, h2, h3, ha, hc, hb⟩
  · exact absurd (h1.trans h3) (not_lt.mpr h2.le)
  · exact ⟨c, a, b, h2, h1, hc, ha, hb⟩
  · exact ⟨b, a, c, h1, h2, hb, ha, hc⟩
  · exact absurd (h3.trans h1) (not_lt.mpr h2.le)
  · exact ⟨b, c, a, h3, h2, hb, hc, ha⟩
  · exact ⟨c, b, a, h3, h1, hc, hb, ha⟩

/-! ### 2. Lemma 6: Minimal Cut-Component / End-Block -/

/-- **Lemma 6 (Minimal Cut-Component / End-Block):**
Every finite simple graph `G` with at least one edge contains a vertex subset `B : Finset V`
and an attachment vertex `z ∈ B` such that:
1. `|B| ≥ 2` and `G[B]` is connected;
2. either `|B| = 2` (so `G[B] ≅ K_2`) or `G[B]` is 2-connected; and
3. every `v ∈ B \ {z}` has all its `G`-neighbors inside `B`. -/
theorem exists_endBlock {V : Type*} [Finite V] (G : SimpleGraph V)
    (hEdge : ∃ u v : V, G.Adj u v) :
    ∃ (B : Finset V) (z : V),
      z ∈ B ∧
      (∃ w ∈ B, w ≠ z) ∧
      (G.induce (B : Set V)).Connected ∧
      (B.card = 2 ∨ IsTwoConnected (G.induce (B : Set V))) ∧
      (∀ v ∈ B, v ≠ z → ∀ w : V, G.Adj v w → w ∈ B) := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨u₀, v₀, huv₀⟩ := hEdge
  let H : Finset V := Finset.univ.filter fun x => G.Reachable u₀ x
  have hu₀H : u₀ ∈ H := by simp [H]
  have hv₀H : v₀ ∈ H := by simp [H, huv₀.reachable]
  have hH_closed : ∀ a ∈ H, ∀ b : V, G.Adj a b → b ∈ H := by
    intro a ha b hab
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.trans hab.reachable
  have hH_conn : (G.induce (H : Set V)).Connected := by
    have : Nonempty (H : Set V) := ⟨⟨u₀, hu₀H⟩⟩
    refine ⟨fun x y => ?_⟩
    have hto : ∀ z : (H : Set V), (G.induce (H : Set V)).Reachable ⟨u₀, hu₀H⟩ z := by
      intro z
      have hr : G.Reachable u₀ z.1 := (Finset.mem_filter.mp z.2).2
      obtain ⟨p⟩ := hr
      refine induce_reachable_of_walk hu₀H z.2 p fun w hw => ?_
      simp only [H, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p.takeUntil w hw⟩
    exact (hto x).symm.trans (hto y)
  have hH_card : 2 ≤ H.card := by
    have hsub : ({u₀, v₀} : Finset V) ⊆ H := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hu₀H
      · rw [Finset.mem_singleton.mp hw]; exact hv₀H
    have h2 : ({u₀, v₀} : Finset V).card = 2 := Finset.card_pair huv₀.ne
    exact h2 ▸ Finset.card_le_card hsub
  by_cases hH2 : H.card = 2
  · exact ⟨H, u₀, hu₀H, ⟨v₀, hv₀H, huv₀.ne.symm⟩, hH_conn, Or.inl hH2,
      fun v hv _ w hvw => hH_closed v hv w hvw⟩
  have hH3 : 3 ≤ H.card := by omega
  by_cases hno_cut : ∀ z ∈ H, (G.induce ((H.erase z : Finset V) : Set V)).Connected
  · refine ⟨H, u₀, hu₀H, ⟨v₀, hv₀H, huv₀.ne.symm⟩, hH_conn, Or.inr ⟨?_, ?_⟩,
      fun v hv _ w hvw => hH_closed v hv w hvw⟩
    · simpa [Fintype.card_coe] using hH3
    · intro z
      exact (connected_induce_subtype_ne_iff z.2).mpr (hno_cut z.1 z.2)
  push Not at hno_cut
  let comp : V → V → Finset V := fun z x =>
    (H.erase z).filter fun y =>
      ∃ (hx : x ∈ H.erase z) (hy : y ∈ H.erase z),
        (G.induce ((H.erase z : Finset V) : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  let P : Finset (V × V) :=
    (H ×ˢ H).filter fun p => p.2 ≠ p.1 ∧ (comp p.1 p.2).card < (H.erase p.1).card
  have hP_ne : P.Nonempty := by
    obtain ⟨z₀, hz₀H, hdisc⟩ := hno_cut
    have hne_er : (H.erase z₀).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hz₀H]; omega)
    have : Nonempty ((H.erase z₀ : Finset V) : Set V) :=
      let ⟨x, hx⟩ := hne_er; ⟨⟨x, hx⟩⟩
    have hnot_all : ¬ ∀ x y : ((H.erase z₀ : Finset V) : Set V),
        (G.induce ((H.erase z₀ : Finset V) : Set V)).Reachable x y := by
      intro hall
      exact hdisc ⟨hall⟩
    push Not at hnot_all
    obtain ⟨x, y, hxy⟩ := hnot_all
    have hxH : x.1 ∈ H := Finset.mem_of_mem_erase x.2
    have hxz : x.1 ≠ z₀ := (Finset.mem_erase.mp x.2).1
    have hy_not : y.1 ∉ comp z₀ x.1 := by
      intro hyc
      simp only [comp, Finset.mem_filter] at hyc
      obtain ⟨-, _, _, hr⟩ := hyc
      exact hxy hr
    have hssub : comp z₀ x.1 ⊂ H.erase z₀ := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun hEq => ?_⟩
      have hy_in : y.1 ∈ comp z₀ x.1 := by rw [hEq]; exact y.2
      exact hy_not hy_in
    refine ⟨(z₀, x.1), ?_⟩
    simp only [P, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hz₀H, hxH⟩, hxz, Finset.card_lt_card hssub⟩
  obtain ⟨⟨z, x⟩, hzxP, hmin⟩ :=
    Finset.exists_min_image P (fun p => (comp p.1 p.2).card) hP_ne
  simp only [P, Finset.mem_filter, Finset.mem_product] at hzxP
  obtain ⟨⟨hzH, hxH⟩, hxz, _⟩ := hzxP
  have hx_er : x ∈ H.erase z := Finset.mem_erase.mpr ⟨hxz, hxH⟩
  set D : Finset V := comp z x
  have hD_sub : D ⊆ H.erase z := Finset.filter_subset _ _
  have hz_not_D : z ∉ D := fun hzD => (Finset.mem_erase.mp (hD_sub hzD)).1 rfl
  have hxD : x ∈ D := by
    simp only [D, comp, Finset.mem_filter]
    exact ⟨hx_er, hx_er, hx_er, SimpleGraph.Reachable.refl _⟩
  have hD_closed : ∀ v ∈ D, ∀ w : V, G.Adj v w → w = z ∨ w ∈ D := by
    intro v hvD w hvw
    by_cases hwz : w = z
    · exact Or.inl hwz
    · right
      have hvH : v ∈ H := Finset.mem_of_mem_erase (hD_sub hvD)
      have hwH : w ∈ H := hH_closed v hvH w hvw
      have hw_er : w ∈ H.erase z := Finset.mem_erase.mpr ⟨hwz, hwH⟩
      simp only [D, comp, Finset.mem_filter] at hvD ⊢
      obtain ⟨hv_er, hx', _, hrxv⟩ := hvD
      have hvw_ind : (G.induce ((H.erase z : Finset V) : Set V)).Adj ⟨v, hv_er⟩ ⟨w, hw_er⟩ := hvw
      exact ⟨hw_er, hx', hw_er, hrxv.trans hvw_ind.reachable⟩
  have hD_conn : (G.induce (D : Set V)).Connected := by
    have hEq : (D : Set V) = {v : V | ∃ hv : v ∈ ((H.erase z : Finset V) : Set V),
        (G.induce ((H.erase z : Finset V) : Set V)).Reachable ⟨x, hx_er⟩ ⟨v, hv⟩} := by
      ext v
      simp only [D, comp, Finset.mem_coe, Finset.mem_filter]
      constructor
      · rintro ⟨hv, _, _, hr⟩; exact ⟨hv, hr⟩
      · rintro ⟨hv, hr⟩; exact ⟨hv, hx_er, hv, hr⟩
    rw [hEq]
    exact induce_component_connected hx_er
  have hz_adj_D : ∃ a ∈ D, G.Adj z a := by
    obtain ⟨p, -⟩ := exists_walk_of_induce_reachable (hH_conn ⟨x, hxH⟩ ⟨z, hzH⟩)
    obtain ⟨a, b, _, _, haD, hbD, hab, -, -, -, -⟩ := walk_first_exit p hxD hz_not_D
    rcases hD_closed a haD b hab with rfl | hbD'
    · exact ⟨a, haD, hab.symm⟩
    · exact absurd hbD' hbD
  set B : Finset V := insert z D
  have hB_coe : (B : Set V) = insert z (D : Set V) := Finset.coe_insert z D
  have hB_conn : (G.induce (B : Set V)).Connected := by
    rw [hB_coe]
    exact induce_connected_insert hD_conn hz_adj_D
  have hB_closed : ∀ v ∈ B, v ≠ z → ∀ w : V, G.Adj v w → w ∈ B := by
    intro v hvB hvz w hvw
    have hvD : v ∈ D := (Finset.mem_insert.mp hvB).resolve_left hvz
    rcases hD_closed v hvD w hvw with hwz | hwD
    · rw [hwz]; exact Finset.mem_insert_self z D
    · exact Finset.mem_insert_of_mem hwD
  refine ⟨B, z, Finset.mem_insert_self z D, ⟨x, Finset.mem_insert_of_mem hxD, hxz⟩,
    hB_conn, ?_, hB_closed⟩
  by_cases hD1 : D.card = 1
  · left
    rw [Finset.card_insert_of_notMem hz_not_D, hD1]
  · right
    have hD2 : 2 ≤ D.card := by
      have hpos : 0 < D.card := Finset.card_pos.mpr ⟨x, hxD⟩
      omega
    have hB3 : 3 ≤ B.card := by
      rw [Finset.card_insert_of_notMem hz_not_D]
      omega
    refine ⟨by simpa [Fintype.card_coe] using hB3, fun w => ?_⟩
    rw [connected_induce_subtype_ne_iff w.2]
    by_cases hwz : w.1 = z
    · have hEq : B.erase w.1 = D := by
        rw [hwz]
        exact Finset.erase_insert hz_not_D
      rw [hEq]
      exact hD_conn
    · have hwD : w.1 ∈ D := (Finset.mem_insert.mp w.2).resolve_left hwz
      have hwH : w.1 ∈ H := Finset.mem_of_mem_erase (hD_sub hwD)
      by_contra hdisc
      have hz_Ber : z ∈ B.erase w.1 :=
        Finset.mem_erase.mpr ⟨Ne.symm hwz, Finset.mem_insert_self z D⟩
      have hnot_all : ¬ ∀ u : ((B.erase w.1 : Finset V) : Set V),
          (G.induce ((B.erase w.1 : Finset V) : Set V)).Reachable ⟨z, hz_Ber⟩ u := by
        intro hall
        have : Nonempty ((B.erase w.1 : Finset V) : Set V) := ⟨⟨z, hz_Ber⟩⟩
        exact hdisc ⟨fun a b => (hall a).symm.trans (hall b)⟩
      push Not at hnot_all
      obtain ⟨u, hzu_unreach⟩ := hnot_all
      have huw : u.1 ≠ w.1 := (Finset.mem_erase.mp u.2).1
      have huz : u.1 ≠ z := fun hEq => by
        have hsub : u = ⟨z, hz_Ber⟩ := Subtype.ext hEq
        rw [hsub] at hzu_unreach
        exact hzu_unreach (SimpleGraph.Reachable.refl _)
      have huD : u.1 ∈ D :=
        (Finset.mem_insert.mp (Finset.mem_of_mem_erase u.2)).resolve_left huz
      have huH : u.1 ∈ H := Finset.mem_of_mem_erase (hD_sub huD)
      have hD'_sub : comp w.1 u.1 ⊆ D.erase w.1 := by
        intro y hy
        simp only [comp, Finset.mem_filter] at hy
        obtain ⟨_, _, _, hr⟩ := hy
        obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable hr
        by_contra hy_not
        have hu_Dw : u.1 ∈ ((D.erase w.1 : Finset V) : Set V) :=
          Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨huw, huD⟩)
        have hy_not_coe : y ∉ ((D.erase w.1 : Finset V) : Set V) :=
          fun hmem => hy_not (Finset.mem_coe.mp hmem)
        obtain ⟨a, b, p₁, p₂, ha, hb, hab, hp₁Dw, -, hp₂, -⟩ :=
          walk_first_exit p hu_Dw hy_not_coe
        have haDw : a ∈ D.erase w.1 := Finset.mem_coe.mp ha
        have haD : a ∈ D := Finset.mem_of_mem_erase haDw
        have hb_supp : b ∈ p.support := hp₂ b (SimpleGraph.Walk.start_mem_support p₂)
        have hbw : b ≠ w.1 := (Finset.mem_erase.mp (hp b hb_supp)).1
        rcases hD_closed a haD b hab with hbz | hbD
        · have haBer : a ∈ ((B.erase w.1 : Finset V) : Set V) :=
            Finset.mem_coe.mpr (Finset.mem_erase.mpr
              ⟨(Finset.mem_erase.mp haDw).1, Finset.mem_insert_of_mem haD⟩)
          have hu_to_a : (G.induce ((B.erase w.1 : Finset V) : Set V)).Reachable u ⟨a, haBer⟩ :=
            induce_reachable_of_walk u.2 haBer p₁ fun t ht => by
              have htDw : t ∈ D.erase w.1 := Finset.mem_coe.mp (hp₁Dw t ht)
              exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
                ⟨(Finset.mem_erase.mp htDw).1,
                 Finset.mem_insert_of_mem (Finset.mem_of_mem_erase htDw)⟩)
          have ha_to_z : (G.induce ((B.erase w.1 : Finset V) : Set V)).Adj
              ⟨a, haBer⟩ ⟨z, hz_Ber⟩ := hbz ▸ hab
          exact hzu_unreach (hu_to_a.trans ha_to_z.reachable).symm
        · exact hb (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hbw, hbD⟩))
      have hwuP : (w.1, u.1) ∈ P := by
        have hz_not_D' : z ∉ comp w.1 u.1 := fun hz' =>
          hz_not_D (Finset.mem_of_mem_erase (hD'_sub hz'))
        have hz_Her : z ∈ H.erase w.1 := Finset.mem_erase.mpr ⟨Ne.symm hwz, hzH⟩
        have hssub : comp w.1 u.1 ⊂ H.erase w.1 := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun hEq => ?_⟩
          exact hz_not_D' (hEq ▸ hz_Her)
        simp only [P, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hwH, huH⟩, huw, Finset.card_lt_card hssub⟩
      have hle_min : D.card ≤ (comp w.1 u.1).card := hmin (w.1, u.1) hwuP
      have hlt_D : (comp w.1 u.1).card < D.card := by
        calc (comp w.1 u.1).card
            ≤ (D.erase w.1).card := Finset.card_le_card hD'_sub
          _ < D.card := Finset.card_erase_lt_of_mem hwD
      omega

/-! ### 3. Lemma 1: Every 3-Connected Graph Has a `K_4` Minor -/

/-- In a 3-connected graph, every vertex has a neighbor outside any subset of size at most 2. -/
private lemma exists_adj_not_mem_of_card_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (h3 : IsThreeConnected G) (v : V) (S : Finset V) (hS : S.card ≤ 2) :
    ∃ w : V, G.Adj v w ∧ w ∉ S := by
  classical
  let S' : Finset V := S.erase v
  have hS'_card : S'.card ≤ 2 := (Finset.card_erase_le).trans hS
  have hvS' : v ∉ S' := Finset.notMem_erase v S
  have hcard_ins : (insert v S').card ≤ 3 := by
    rw [Finset.card_insert_of_notMem hvS']
    omega
  have hne : (Finset.univ \ insert v S').Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hle : Fintype.card V ≤ (insert v S').card := by
      have : Finset.univ ⊆ insert v S' := Finset.sdiff_eq_empty_iff_subset.mp hemp
      simpa using Finset.card_le_card this
    have h4 := h3.1
    omega
  obtain ⟨u, hu⟩ := hne
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, true_and, not_or] at hu
  obtain ⟨huv, huS'⟩ := hu
  have hconn := h3.2 S' hS'_card
  obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable (hconn ⟨v, hvS'⟩ ⟨u, huS'⟩)
  cases p with
  | nil => exact absurd rfl huv
  | @cons _ w _ hvw _ =>
    have hwS' : w ∉ S' := hp w (by simp)
    have hwS : w ∉ S := fun hw => hwS' (Finset.mem_erase.mpr ⟨hvw.ne.symm, hw⟩)
    exact ⟨w, hvw, hwS⟩

/-- Every 3-connected graph contains a simple cycle of length `m ≥ 3`. -/
private lemma exists_simple_cycle_of_isThreeConnected {V : Type*} [Fintype V] {G : SimpleGraph V}
    (h3 : IsThreeConnected G) :
    ∃ (m : ℕ) (hm : 3 ≤ m) (f : Fin m → V),
      Function.Injective f ∧
      ∀ i : Fin m, G.Adj (f i) (f ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ L : List V, L.length = k ∧ L.Nodup ∧
      ∀ i (hi : i + 1 < L.length), G.Adj L[i] L[i + 1]
  have hV_pos : 0 < Fintype.card V := by have := h3.1; omega
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hV_pos
  have hP1 : P 1 := by
    refine ⟨[v₀], rfl, List.nodup_singleton v₀, fun i hi => ?_⟩
    simp at hi
  let KS : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter P
  have h1KS : 1 ∈ KS := by
    simp only [KS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := h3.1; omega, hP1⟩
  let k : ℕ := KS.max' ⟨1, h1KS⟩
  have hkKS : k ∈ KS := Finset.max'_mem KS ⟨1, h1KS⟩
  have hk_ge1 : 1 ≤ k := Finset.le_max' KS 1 h1KS
  have hPk : P k := (Finset.mem_filter.mp hkKS).2
  have hk_max : ∀ k', P k' → k' ≤ k := by
    intro k' ⟨L, hlen, hnodup, hadj⟩
    have hleV : k' ≤ Fintype.card V := by
      calc k' = L.length := hlen.symm
        _ = L.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
        _ ≤ Fintype.card V := Finset.card_le_univ _
    exact Finset.le_max' KS k' (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), L, hlen, hnodup, hadj⟩)
  obtain ⟨L, hLlen, hLnodup, hLadj⟩ := hPk
  let u : V := L[k - 1]'(by omega)
  let S : Finset V := if h2 : 2 ≤ k then {L[k - 2]'(by omega)} else ∅
  have hS_card : S.card ≤ 2 := by
    by_cases h2 : 2 ≤ k
    · simp [S, h2]
    · simp [S, h2]
  obtain ⟨w, huw, hwS⟩ := exists_adj_not_mem_of_card_le_two h3 u S hS_card
  have hwL : w ∈ L := by
    by_contra hw_not
    have hPk1 : P (k + 1) := by
      refine ⟨L ++ [w], by simp [hLlen], ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hLnodup, List.nodup_singleton w, fun a ha b hb hEq => ?_⟩
        rw [List.mem_singleton.mp hb] at hEq
        exact hw_not (hEq ▸ ha)
      · intro i hi
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hik : i + 1 < L.length
        · rw [List.getElem_append_left (by omega), List.getElem_append_left hik]
          exact hLadj i hik
        · have hiEq : i = k - 1 := by omega
          have hi1Eq : i + 1 = L.length := by omega
          rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
          have h1 : L[i]'(by omega) = u := by
            simp only [u, hiEq]
          have h2 : ([w][i + 1 - L.length]'(by simp; omega)) = w := by
            simp [hi1Eq]
          rw [h1, h2]
          exact huw
    have := hk_max (k + 1) hPk1
    omega
  obtain ⟨idx, hidx_lt, hLidx⟩ := List.mem_iff_getElem.mp hwL
  have hidx_ne1 : idx ≠ k - 1 := by
    intro hEq
    have hwu : w = u := by
      rw [← hLidx]
      simp only [u, hEq]
    exact huw.ne hwu.symm
  have hidx_lt2 : idx + 2 < k := by
    by_cases h2 : 2 ≤ k
    · have hidx_ne2 : idx ≠ k - 2 := by
        intro hEq
        have hw_mem : w ∈ S := by
          simp only [S, h2, ↓reduceDIte, Finset.mem_singleton]
          rw [← hLidx]
          congr 1
        exact hwS hw_mem
      omega
    · omega
  let m : ℕ := k - idx
  have hm : 3 ≤ m := by omega
  let f : Fin m → V := fun i => L[idx + i.val]'(by omega)
  refine ⟨m, hm, f, ?_, ?_⟩
  · intro i j hij
    have hidx_eq : idx + i.val = idx + j.val := (hLnodup.getElem_inj_iff).mp hij
    exact Fin.ext (by omega)
  · intro i
    by_cases hlast : i.val + 1 < m
    · have hmod : (i.val + 1) % m = i.val + 1 := Nat.mod_eq_of_lt hlast
      have hidx1 : idx + i.val + 1 < L.length := by omega
      have hstep := hLadj (idx + i.val) hidx1
      simpa only [f, hmod, Nat.add_assoc] using hstep
    · have hi_end : i.val = m - 1 := by omega
      have hmod : (i.val + 1) % m = 0 := by
        have : i.val + 1 = m := by omega
        rw [this, Nat.mod_self]
      have hfi : f i = u := by
        simp only [f, u]
        congr 1
        omega
      have hf0 : f ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ = w := by
        simp only [f, hmod, Nat.add_zero]
        exact hLidx
      rw [hfi, hf0]
      exact huw

/-- Rotating a simple cycle by `s` steps preserves injectivity, cycle adjacency, and range. -/
private lemma cycle_rotate {V : Type*} {G : SimpleGraph V} {m : ℕ} (hm : 3 ≤ m)
    (f : Fin m → V) (hf : Function.Injective f)
    (hcyc : ∀ i : Fin m, G.Adj (f i) (f ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩))
    (s : ℕ) :
    let g : Fin m → V := fun i => f ⟨(i.val + s) % m, Nat.mod_lt _ (by omega)⟩
    Function.Injective g ∧
    (∀ i : Fin m, G.Adj (g i) (g ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩)) ∧
    Set.range g = Set.range f := by
  intro g
  have hmod_cancel : ∀ a b : ℕ, a < m → b < m → (a + s) % m = (b + s) % m → a = b := by
    intro a b ha hb hEq
    set r := s % m
    have hr : r < m := Nat.mod_lt s (by omega)
    have hEq' : (a + r) % m = (b + r) % m := by
      simpa [r, Nat.add_mod_mod] using hEq
    by_cases har : a + r < m <;> by_cases hbr : b + r < m
    · rw [Nat.mod_eq_of_lt har, Nat.mod_eq_of_lt hbr] at hEq'; omega
    · have h1 : (b + r) % m = b + r - m := by
        have hlt : b + r - m < m := by omega
        calc (b + r) % m = (b + r - m + m) % m := by congr 1; omega
          _ = (b + r - m) % m := Nat.add_mod_right _ _
          _ = b + r - m := Nat.mod_eq_of_lt hlt
      rw [Nat.mod_eq_of_lt har, h1] at hEq'; omega
    · have h1 : (a + r) % m = a + r - m := by
        have hlt : a + r - m < m := by omega
        calc (a + r) % m = (a + r - m + m) % m := by congr 1; omega
          _ = (a + r - m) % m := Nat.add_mod_right _ _
          _ = a + r - m := Nat.mod_eq_of_lt hlt
      rw [h1, Nat.mod_eq_of_lt hbr] at hEq'; omega
    · have h1 : (a + r) % m = a + r - m := by
        have hlt : a + r - m < m := by omega
        calc (a + r) % m = (a + r - m + m) % m := by congr 1; omega
          _ = (a + r - m) % m := Nat.add_mod_right _ _
          _ = a + r - m := Nat.mod_eq_of_lt hlt
      have h2 : (b + r) % m = b + r - m := by
        have hlt : b + r - m < m := by omega
        calc (b + r) % m = (b + r - m + m) % m := by congr 1; omega
          _ = (b + r - m) % m := Nat.add_mod_right _ _
          _ = b + r - m := Nat.mod_eq_of_lt hlt
      rw [h1, h2] at hEq'; omega
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have hval := congrArg Fin.val (hf hij)
    exact Fin.ext (hmod_cancel i.val j.val i.isLt j.isLt hval)
  · intro i
    have hstep := hcyc ⟨(i.val + s) % m, Nat.mod_lt _ (by omega)⟩
    have hidx : ((i.val + 1) % m + s) % m = ((i.val + s) % m + 1) % m := by
      rw [Nat.mod_add_mod, Nat.mod_add_mod]
      congr 1
      omega
    simpa only [g, hidx] using hstep
  · ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨(i.val + s) % m, Nat.mod_lt _ (by omega)⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      set r := s % m
      have hr : r < m := Nat.mod_lt s (by omega)
      refine ⟨⟨(j.val + m - r) % m, Nat.mod_lt _ (by omega)⟩, ?_⟩
      simp only [g]
      congr 1
      apply Fin.ext
      dsimp only
      have h1 : ((j.val + m - r) % m + s) % m = ((j.val + m - r) + r) % m := by
        rw [Nat.mod_add_mod, ← Nat.add_mod_mod]
      rw [h1]
      have h2 : j.val + m - r + r = j.val + m := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

/-- A nonempty contiguous half-open arc `[a, b)` of a simple cycle is connected in `G`. -/
private lemma cycle_arc_connected {V : Type*} {G : SimpleGraph V} {m : ℕ} (hm : 3 ≤ m)
    (f : Fin m → V)
    (hcyc : ∀ i : Fin m, G.Adj (f i) (f ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩))
    {a b : ℕ} (hab : a < b) (hbm : b ≤ m) :
    (G.induce {v : V | ∃ i : Fin m, a ≤ i.val ∧ i.val < b ∧ f i = v}).Connected := by
  set A : Set V := {v : V | ∃ i : Fin m, a ≤ i.val ∧ i.val < b ∧ f i = v}
  have haA : f ⟨a, by omega⟩ ∈ A := ⟨⟨a, by omega⟩, le_rfl, hab, rfl⟩
  have : Nonempty A := ⟨⟨f ⟨a, by omega⟩, haA⟩⟩
  have hreach_off : ∀ d : ℕ, (hd : a + d < b) →
      (G.induce A).Reachable ⟨f ⟨a, by omega⟩, haA⟩
        ⟨f ⟨a + d, by omega⟩, ⟨⟨a + d, by omega⟩, by dsimp only; omega, hd, rfl⟩⟩ := by
    intro d
    induction d with
    | zero =>
      intro _
      exact SimpleGraph.Reachable.refl _
    | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      have hmod : (a + d + 1) % m = a + (d + 1) := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hstep_G : G.Adj (f ⟨a + d, by omega⟩) (f ⟨a + (d + 1), by omega⟩) := by
        have h := hcyc ⟨a + d, by omega⟩
        simpa only [hmod] using h
      have hstep : (G.induce A).Adj
          ⟨f ⟨a + d, by omega⟩,
            ⟨⟨a + d, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩⟩
          ⟨f ⟨a + (d + 1), by omega⟩,
            ⟨⟨a + (d + 1), by omega⟩, by dsimp only; omega, hd, rfl⟩⟩ := hstep_G
      exact hprev.trans hstep.reachable
  refine ⟨fun x y => ?_⟩
  have hto : ∀ z : A, (G.induce A).Reachable ⟨f ⟨a, by omega⟩, haA⟩ z := by
    intro z
    obtain ⟨i, hai, hib, hfi⟩ := z.2
    have hEq : a + (i.val - a) = i.val := by omega
    have hzEq : z = ⟨f ⟨a + (i.val - a), by omega⟩,
        ⟨⟨a + (i.val - a), by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩⟩ := by
      apply Subtype.ext
      rw [← hfi]
      congr 1
      exact Fin.ext hEq.symm
    rw [hzEq]
    exact hreach_off (i.val - a) (by omega)
  exact (hto x).symm.trans (hto y)

/-- **Lemma 1 (3-Connected Graphs Have a `K_4` Minor):**
Every finite simple 3-connected graph `G` has `K_4` as a minor. -/
theorem hasMinor_K4_of_isThreeConnected {V : Type*} [Fintype V] {G : SimpleGraph V}
    (h3 : IsThreeConnected G) : HasMinor G K4 := by
  classical
  obtain ⟨m, hm, f, hf, hcyc⟩ := exists_simple_cycle_of_isThreeConnected h3
  by_cases hham : Set.range f = Set.univ
  · -- Case 1: Hamiltonian cycle `V(C) = V(G)`.
    have hm4 : 4 ≤ m := by
      have hcard : Fintype.card V ≤ m := by
        have hsurj : Function.Surjective f := Set.range_eq_univ.mp hham
        simpa using Fintype.card_le_of_surjective f hsurj
      have h4 := h3.1
      omega
    let S_nbr : Finset V := {f ⟨1, by omega⟩, f ⟨m - 1, by omega⟩}
    obtain ⟨w, hfw, hwS⟩ :=
      exists_adj_not_mem_of_card_le_two h3 (f ⟨0, by omega⟩) S_nbr Finset.card_le_two
    have hw_range : w ∈ Set.range f := hham.symm ▸ Set.mem_univ w
    obtain ⟨k, hfk⟩ := hw_range
    have hk_ne0 : k.val ≠ 0 := by
      intro h0
      have hEq : w = f ⟨0, by omega⟩ := by rw [← hfk]; congr 1; exact Fin.ext h0
      exact hfw.ne hEq.symm
    have hk_ne1 : k.val ≠ 1 := by
      intro h1
      have hEq : w = f ⟨1, by omega⟩ := by rw [← hfk]; congr 1; exact Fin.ext h1
      exact hwS (by simp [S_nbr, hEq])
    have hk_nem1 : k.val ≠ m - 1 := by
      intro hm1
      have hEq : w = f ⟨m - 1, by omega⟩ := by rw [← hfk]; congr 1; exact Fin.ext hm1
      exact hwS (by simp [S_nbr, hEq])
    have hk_lo : 2 ≤ k.val := by omega
    have hk_hi : k.val + 1 < m := by omega
    let Sep : Finset V := {f ⟨0, by omega⟩, f k}
    have hconn_sep := h3.2 Sep Finset.card_le_two
    have hf1_not : f ⟨1, by omega⟩ ∉ Sep := by
      simp only [Sep, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => by have := congrArg Fin.val (hf h); dsimp only at this; omega,
             fun h => by have := congrArg Fin.val (hf h); dsimp only at this; omega⟩
    have hfm1_not : f ⟨m - 1, by omega⟩ ∉ Sep := by
      simp only [Sep, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => by have := congrArg Fin.val (hf h); dsimp only at this; omega,
             fun h => by have := congrArg Fin.val (hf h); dsimp only at this; omega⟩
    obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable
      (hconn_sep ⟨f ⟨1, by omega⟩, hf1_not⟩ ⟨f ⟨m - 1, by omega⟩, hfm1_not⟩)
    set A₁ : Set V := {v : V | ∃ i : Fin m, 0 < i.val ∧ i.val < k.val ∧ f i = v}
    have hf1A₁ : f ⟨1, by omega⟩ ∈ A₁ :=
      ⟨⟨1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩
    have hfm1A₁ : f ⟨m - 1, by omega⟩ ∉ A₁ := by
      rintro ⟨i, -, hik, hfi⟩
      have := congrArg Fin.val (hf hfi)
      dsimp only at this
      omega
    obtain ⟨a, b, _, p₂, haA₁, hbA₁, hab, -, -, hp₂, -⟩ := walk_first_exit p hf1A₁ hfm1A₁
    obtain ⟨i₁, hi₁_lo, hi₁_hi, hfi₁⟩ := haA₁
    have hb_range : b ∈ Set.range f := hham.symm ▸ Set.mem_univ b
    obtain ⟨i₂, hfi₂⟩ := hb_range
    have hb_notSep : b ∉ Sep := hp b (hp₂ b (SimpleGraph.Walk.start_mem_support p₂))
    have hi₂_ne0 : i₂.val ≠ 0 := fun h0 => hb_notSep (by
      simp only [Sep, Finset.mem_insert, Finset.mem_singleton]
      left; rw [← hfi₂]; congr 1; exact Fin.ext h0)
    have hi₂_nek : i₂.val ≠ k.val := fun hk' => hb_notSep (by
      simp only [Sep, Finset.mem_insert, Finset.mem_singleton]
      right; rw [← hfi₂]; congr 1; exact Fin.ext hk')
    have hi₂_gt : k.val < i₂.val := by
      by_contra hle
      exact hbA₁ ⟨i₂, by omega, by omega, hfi₂⟩
    have hcross : G.Adj (f i₁) (f i₂) := by rwa [hfi₁, hfi₂]
    have hchord : G.Adj (f ⟨0, by omega⟩) (f k) := by rwa [hfk]
    -- Four contiguous half-open arcs `[0, i₁), [i₁, k), [k, i₂), [i₂, m)`.
    let arc : ℕ → ℕ → Set V := fun lo hi =>
      {v : V | ∃ i : Fin m, lo ≤ i.val ∧ i.val < hi ∧ f i = v}
    let B : Fin 4 → Set V := fun idx =>
      match idx with
      | ⟨0, _⟩ => arc 0 i₁.val
      | ⟨1, _⟩ => arc i₁.val k.val
      | ⟨2, _⟩ => arc k.val i₂.val
      | ⟨3, _⟩ => arc i₂.val m
    refine ⟨B, ?_, ?_, ?_⟩
    · intro idx
      fin_cases idx
      · exact cycle_arc_connected hm f hcyc (by omega) (by omega)
      · exact cycle_arc_connected hm f hcyc (by omega) (by omega)
      · exact cycle_arc_connected hm f hcyc (by omega) (by omega)
      · exact cycle_arc_connected hm f hcyc (by omega) le_rfl
    · intro u v huv
      dsimp only [Function.onFun]
      rw [Set.disjoint_left]
      intro x hxu hxv
      fin_cases u <;> fin_cases v
      all_goals try exact huv rfl
      all_goals
        obtain ⟨iu, hiu1, hiu2, hiuEq⟩ := hxu
        obtain ⟨iv, hiv1, hiv2, hivEq⟩ := hxv
        have hEq := congrArg Fin.val (hf (hiuEq.trans hivEq.symm))
        omega
    · intro u v huv
      have hne : u ≠ v := huv
      fin_cases u <;> fin_cases v
      all_goals try exact absurd rfl hne
      · -- 0 ~ 1: f (i₁ - 1) ~ f i₁
        refine ⟨f ⟨i₁.val - 1, by omega⟩,
          ⟨⟨i₁.val - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩,
          f i₁, ⟨i₁, le_rfl, hi₁_hi, rfl⟩, ?_⟩
        have hstep := hcyc ⟨i₁.val - 1, by omega⟩
        have hmod : (i₁.val - 1 + 1) % m = i₁.val := by
          rw [show i₁.val - 1 + 1 = i₁.val by omega, Nat.mod_eq_of_lt i₁.isLt]
        simpa only [hmod] using hstep
      · -- 0 ~ 2: chord f 0 ~ f k
        exact ⟨f ⟨0, by omega⟩, ⟨⟨0, by omega⟩, le_rfl, hi₁_lo, rfl⟩,
          f k, ⟨k, le_rfl, hi₂_gt, rfl⟩, hchord⟩
      · -- 0 ~ 3: wrap cycle edge f (m - 1) ~ f 0
        refine ⟨f ⟨0, by omega⟩, ⟨⟨0, by omega⟩, le_rfl, hi₁_lo, rfl⟩,
          f ⟨m - 1, by omega⟩,
          ⟨⟨m - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩, ?_⟩
        have hstep := hcyc ⟨m - 1, by omega⟩
        have hmod : (m - 1 + 1) % m = 0 := by
          rw [show m - 1 + 1 = m by omega, Nat.mod_self]
        exact (by simpa only [hmod] using hstep :
          G.Adj (f ⟨m - 1, by omega⟩) (f ⟨0, by omega⟩)).symm
      · -- 1 ~ 0
        refine ⟨f i₁, ⟨i₁, le_rfl, hi₁_hi, rfl⟩,
          f ⟨i₁.val - 1, by omega⟩,
          ⟨⟨i₁.val - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩, ?_⟩
        have hstep := hcyc ⟨i₁.val - 1, by omega⟩
        have hmod : (i₁.val - 1 + 1) % m = i₁.val := by
          rw [show i₁.val - 1 + 1 = i₁.val by omega, Nat.mod_eq_of_lt i₁.isLt]
        exact (by simpa only [hmod] using hstep : G.Adj (f ⟨i₁.val - 1, by omega⟩) (f i₁)).symm
      · -- 1 ~ 2: f (k - 1) ~ f k
        refine ⟨f ⟨k.val - 1, by omega⟩,
          ⟨⟨k.val - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩,
          f k, ⟨k, le_rfl, hi₂_gt, rfl⟩, ?_⟩
        have hstep := hcyc ⟨k.val - 1, by omega⟩
        have hmod : (k.val - 1 + 1) % m = k.val := by
          rw [show k.val - 1 + 1 = k.val by omega, Nat.mod_eq_of_lt k.isLt]
        simpa only [hmod] using hstep
      · -- 1 ~ 3: crossing edge f i₁ ~ f i₂
        exact ⟨f i₁, ⟨i₁, le_rfl, hi₁_hi, rfl⟩, f i₂, ⟨i₂, le_rfl, i₂.isLt, rfl⟩, hcross⟩
      · -- 2 ~ 0: chord f k ~ f 0
        exact ⟨f k, ⟨k, le_rfl, hi₂_gt, rfl⟩,
          f ⟨0, by omega⟩, ⟨⟨0, by omega⟩, le_rfl, hi₁_lo, rfl⟩, hchord.symm⟩
      · -- 2 ~ 1
        refine ⟨f k, ⟨k, le_rfl, hi₂_gt, rfl⟩,
          f ⟨k.val - 1, by omega⟩,
          ⟨⟨k.val - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩, ?_⟩
        have hstep := hcyc ⟨k.val - 1, by omega⟩
        have hmod : (k.val - 1 + 1) % m = k.val := by
          rw [show k.val - 1 + 1 = k.val by omega, Nat.mod_eq_of_lt k.isLt]
        exact (by simpa only [hmod] using hstep : G.Adj (f ⟨k.val - 1, by omega⟩) (f k)).symm
      · -- 2 ~ 3: f (i₂ - 1) ~ f i₂
        refine ⟨f ⟨i₂.val - 1, by omega⟩,
          ⟨⟨i₂.val - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩,
          f i₂, ⟨i₂, le_rfl, i₂.isLt, rfl⟩, ?_⟩
        have hstep := hcyc ⟨i₂.val - 1, by omega⟩
        have hmod : (i₂.val - 1 + 1) % m = i₂.val := by
          rw [show i₂.val - 1 + 1 = i₂.val by omega, Nat.mod_eq_of_lt i₂.isLt]
        simpa only [hmod] using hstep
      · -- 3 ~ 0: f (m - 1) ~ f 0
        refine ⟨f ⟨m - 1, by omega⟩,
          ⟨⟨m - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩,
          f ⟨0, by omega⟩, ⟨⟨0, by omega⟩, le_rfl, hi₁_lo, rfl⟩, ?_⟩
        have hstep := hcyc ⟨m - 1, by omega⟩
        have hmod : (m - 1 + 1) % m = 0 := by
          rw [show m - 1 + 1 = m by omega, Nat.mod_self]
        simpa only [hmod] using hstep
      · -- 3 ~ 1: crossing edge f i₂ ~ f i₁
        exact ⟨f i₂, ⟨i₂, le_rfl, i₂.isLt, rfl⟩, f i₁, ⟨i₁, le_rfl, hi₁_hi, rfl⟩, hcross.symm⟩
      · -- 3 ~ 2
        refine ⟨f i₂, ⟨i₂, le_rfl, i₂.isLt, rfl⟩,
          f ⟨i₂.val - 1, by omega⟩,
          ⟨⟨i₂.val - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩, ?_⟩
        have hstep := hcyc ⟨i₂.val - 1, by omega⟩
        have hmod : (i₂.val - 1 + 1) % m = i₂.val := by
          rw [show i₂.val - 1 + 1 = i₂.val by omega, Nat.mod_eq_of_lt i₂.isLt]
        exact (by simpa only [hmod] using hstep : G.Adj (f ⟨i₂.val - 1, by omega⟩) (f i₂)).symm
  · -- Case 2: Non-Hamiltonian cycle `V(C) ⊂ V(G)`.
    have hex_out : ∃ h₀ : V, h₀ ∉ Set.range f := by
      by_contra hall
      push Not at hall
      exact hham (Set.eq_univ_of_forall hall)
    obtain ⟨h₀, hh₀⟩ := hex_out
    set Cset : Set V := Set.range f
    set H : Set V :=
      {v : V | ∃ hv : v ∉ Cset, (G.induce {x : V | x ∉ Cset}).Reachable ⟨h₀, hh₀⟩ ⟨v, hv⟩}
    have hh₀H : h₀ ∈ H := ⟨hh₀, SimpleGraph.Reachable.refl _⟩
    have hH_conn : (G.induce H).Connected :=
      induce_component_connected (S := {x : V | x ∉ Cset}) hh₀
    let N : Finset (Fin m) := Finset.univ.filter fun i => ∃ h ∈ H, G.Adj h (f i)
    have hN_card : 3 ≤ N.card := by
      by_contra hlt
      have hNle : N.card ≤ 2 := by omega
      let S : Finset V := N.image f
      have hSle : S.card ≤ 2 := Finset.card_image_le.trans hNle
      have hex_i : ∃ i₀ : Fin m, i₀ ∉ N := by
        by_contra hall
        push Not at hall
        have hEq : N = Finset.univ := Finset.eq_univ_of_forall hall
        have hcard : N.card = m := by rw [hEq]; simp
        omega
      obtain ⟨i₀, hi₀N⟩ := hex_i
      have hfi₀_notS : f i₀ ∉ S := by
        intro hmem
        obtain ⟨j, hjN, hfj⟩ := Finset.mem_image.mp hmem
        exact hi₀N (hf hfj ▸ hjN)
      have hh₀_notS : h₀ ∉ S := by
        intro hmem
        obtain ⟨j, -, hfj⟩ := Finset.mem_image.mp hmem
        exact hh₀ ⟨j, hfj⟩
      have hconnS := h3.2 S hSle
      obtain ⟨p, hp⟩ := exists_walk_of_induce_reachable
        (hconnS ⟨h₀, hh₀_notS⟩ ⟨f i₀, hfi₀_notS⟩)
      have hfi₀_notH : f i₀ ∉ H := fun hmem => hmem.1 ⟨i₀, rfl⟩
      obtain ⟨a, b, _, p₂, haH, hbH, hab, -, -, hp₂, -⟩ := walk_first_exit p hh₀H hfi₀_notH
      by_cases hbC : b ∈ Cset
      · obtain ⟨i, hfi⟩ := hbC
        have hiN : i ∈ N := by
          simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨a, haH, hfi ▸ hab⟩
        have hbS : b ∈ S := Finset.mem_image.mpr ⟨i, hiN, hfi⟩
        exact hp b (hp₂ b (SimpleGraph.Walk.start_mem_support p₂)) hbS
      · obtain ⟨haC, hra⟩ := haH
        have hab_ind : (G.induce {x : V | x ∉ Cset}).Adj ⟨a, haC⟩ ⟨b, hbC⟩ := hab
        exact hbH ⟨hbC, hra.trans hab_ind.reachable⟩
    -- Pick three distinct indices in `N`, sort them, and rotate the cycle so the first is `0`.
    obtain ⟨j₁, hj₁N⟩ := Finset.card_pos.mp (by omega : 0 < N.card)
    have hN1 : 0 < (N.erase j₁).card := by rw [Finset.card_erase_of_mem hj₁N]; omega
    obtain ⟨j₂, hj₂⟩ := Finset.card_pos.mp hN1
    have hj₂₁ : j₂ ≠ j₁ := (Finset.mem_erase.mp hj₂).1
    have hj₂N : j₂ ∈ N := Finset.mem_of_mem_erase hj₂
    have hN2 : 0 < ((N.erase j₁).erase j₂).card := by
      rw [Finset.card_erase_of_mem hj₂, Finset.card_erase_of_mem hj₁N]; omega
    obtain ⟨j₃, hj₃⟩ := Finset.card_pos.mp hN2
    have hj₃₂ : j₃ ≠ j₂ := (Finset.mem_erase.mp hj₃).1
    have hj₃₁ : j₃ ≠ j₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hj₃)).1
    have hj₃N : j₃ ∈ N := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj₃)
    obtain ⟨a, b, c, hab, hbc, haN, hbN, hcN⟩ :=
      exists_sorted_triple hj₂₁.symm hj₃₁.symm hj₃₂.symm (P := fun x => x ∈ N) hj₁N hj₂N hj₃N
    obtain ⟨hg_inj, hg_cyc, hg_range⟩ := cycle_rotate hm f hf hcyc a.val
    let g : Fin m → V := fun i => f ⟨(i.val + a.val) % m, Nat.mod_lt _ (by omega)⟩
    have ha_att : ∃ h ∈ H, G.Adj h (g ⟨0, by omega⟩) := by
      have h0 : g ⟨0, by omega⟩ = f a := by
        simp only [g, Nat.zero_add, Nat.mod_eq_of_lt a.isLt]
      rw [h0]
      exact (Finset.mem_filter.mp haN).2
    let i₁ : ℕ := b.val - a.val
    let i₂ : ℕ := c.val - a.val
    have hi₁_lo : 0 < i₁ := by have : a.val < b.val := hab; omega
    have hi₁₂ : i₁ < i₂ := by have : b.val < c.val := hbc; omega
    have hi₂_lt : i₂ < m := by omega
    have hb_att : ∃ h ∈ H, G.Adj h (g ⟨i₁, by omega⟩) := by
      have h1 : g ⟨i₁, by omega⟩ = f b := by
        simp only [g]
        congr 1
        apply Fin.ext
        dsimp only
        have : i₁ + a.val = b.val := by have : a.val < b.val := hab; omega
        rw [this, Nat.mod_eq_of_lt b.isLt]
      rw [h1]
      exact (Finset.mem_filter.mp hbN).2
    have hc_att : ∃ h ∈ H, G.Adj h (g ⟨i₂, by omega⟩) := by
      have h2 : g ⟨i₂, by omega⟩ = f c := by
        simp only [g]
        congr 1
        apply Fin.ext
        dsimp only
        have : i₂ + a.val = c.val := by
          have : a.val < b.val := hab; have : b.val < c.val := hbc; omega
        rw [this, Nat.mod_eq_of_lt c.isLt]
      rw [h2]
      exact (Finset.mem_filter.mp hcN).2
    let arc : ℕ → ℕ → Set V := fun lo hi =>
      {v : V | ∃ i : Fin m, lo ≤ i.val ∧ i.val < hi ∧ g i = v}
    let B : Fin 4 → Set V := fun idx =>
      match idx with
      | ⟨0, _⟩ => H
      | ⟨1, _⟩ => arc 0 i₁
      | ⟨2, _⟩ => arc i₁ i₂
      | ⟨3, _⟩ => arc i₂ m
    have hH_disj_arc : ∀ lo hi, Disjoint H (arc lo hi) := by
      intro lo hi
      rw [Set.disjoint_left]
      rintro v hvH ⟨i, -, -, hgi⟩
      have hvC : v ∈ Cset := by
        change v ∈ Set.range f
        rw [← hg_range]
        exact ⟨i, hgi⟩
      exact hvH.1 hvC
    refine ⟨B, ?_, ?_, ?_⟩
    · intro idx
      fin_cases idx
      · exact hH_conn
      · exact cycle_arc_connected hm g hg_cyc hi₁_lo (by omega)
      · exact cycle_arc_connected hm g hg_cyc hi₁₂ (by omega)
      · exact cycle_arc_connected hm g hg_cyc hi₂_lt le_rfl
    · intro u v huv
      dsimp only [Function.onFun]
      fin_cases u <;> fin_cases v
      all_goals try exact absurd rfl huv
      · exact hH_disj_arc 0 i₁
      · exact hH_disj_arc i₁ i₂
      · exact hH_disj_arc i₂ m
      · exact (hH_disj_arc 0 i₁).symm
      · rw [Set.disjoint_left]
        rintro x ⟨iu, _, hiu2, hiuEq⟩ ⟨iv, hiv1, _, hivEq⟩
        have := congrArg Fin.val (hg_inj (hiuEq.trans hivEq.symm)); omega
      · rw [Set.disjoint_left]
        rintro x ⟨iu, _, hiu2, hiuEq⟩ ⟨iv, hiv1, _, hivEq⟩
        have := congrArg Fin.val (hg_inj (hiuEq.trans hivEq.symm)); omega
      · exact (hH_disj_arc i₁ i₂).symm
      · rw [Set.disjoint_left]
        rintro x ⟨iu, hiu1, _, hiuEq⟩ ⟨iv, _, hiv2, hivEq⟩
        have := congrArg Fin.val (hg_inj (hiuEq.trans hivEq.symm)); omega
      · rw [Set.disjoint_left]
        rintro x ⟨iu, _, hiu2, hiuEq⟩ ⟨iv, hiv1, _, hivEq⟩
        have := congrArg Fin.val (hg_inj (hiuEq.trans hivEq.symm)); omega
      · exact (hH_disj_arc i₂ m).symm
      · rw [Set.disjoint_left]
        rintro x ⟨iu, hiu1, _, hiuEq⟩ ⟨iv, _, hiv2, hivEq⟩
        have := congrArg Fin.val (hg_inj (hiuEq.trans hivEq.symm)); omega
      · rw [Set.disjoint_left]
        rintro x ⟨iu, hiu1, _, hiuEq⟩ ⟨iv, _, hiv2, hivEq⟩
        have := congrArg Fin.val (hg_inj (hiuEq.trans hivEq.symm)); omega
    · intro u v huv
      have hne : u ≠ v := huv
      fin_cases u <;> fin_cases v
      all_goals try exact absurd rfl hne
      · obtain ⟨h, hhH, hhg⟩ := ha_att
        exact ⟨h, hhH, g ⟨0, by omega⟩, ⟨⟨0, by omega⟩, le_rfl, hi₁_lo, rfl⟩, hhg⟩
      · obtain ⟨h, hhH, hhg⟩ := hb_att
        exact ⟨h, hhH, g ⟨i₁, by omega⟩, ⟨⟨i₁, by omega⟩, le_rfl, hi₁₂, rfl⟩, hhg⟩
      · obtain ⟨h, hhH, hhg⟩ := hc_att
        exact ⟨h, hhH, g ⟨i₂, by omega⟩, ⟨⟨i₂, by omega⟩, le_rfl, hi₂_lt, rfl⟩, hhg⟩
      · obtain ⟨h, hhH, hhg⟩ := ha_att
        exact ⟨g ⟨0, by omega⟩, ⟨⟨0, by omega⟩, le_rfl, hi₁_lo, rfl⟩, h, hhH, hhg.symm⟩
      · refine ⟨g ⟨i₁ - 1, by omega⟩,
          ⟨⟨i₁ - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩,
          g ⟨i₁, by omega⟩, ⟨⟨i₁, by omega⟩, le_rfl, hi₁₂, rfl⟩, ?_⟩
        have hstep := hg_cyc ⟨i₁ - 1, by omega⟩
        have hmod : (i₁ - 1 + 1) % m = i₁ := by
          rw [show i₁ - 1 + 1 = i₁ by omega, Nat.mod_eq_of_lt (by omega)]
        simpa only [hmod] using hstep
      · refine ⟨g ⟨0, by omega⟩, ⟨⟨0, by omega⟩, le_rfl, hi₁_lo, rfl⟩,
          g ⟨m - 1, by omega⟩,
          ⟨⟨m - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩, ?_⟩
        have hstep := hg_cyc ⟨m - 1, by omega⟩
        have hmod : (m - 1 + 1) % m = 0 := by
          rw [show m - 1 + 1 = m by omega, Nat.mod_self]
        exact (by simpa only [hmod] using hstep :
          G.Adj (g ⟨m - 1, by omega⟩) (g ⟨0, by omega⟩)).symm
      · obtain ⟨h, hhH, hhg⟩ := hb_att
        exact ⟨g ⟨i₁, by omega⟩, ⟨⟨i₁, by omega⟩, le_rfl, hi₁₂, rfl⟩, h, hhH, hhg.symm⟩
      · refine ⟨g ⟨i₁, by omega⟩, ⟨⟨i₁, by omega⟩, le_rfl, hi₁₂, rfl⟩,
          g ⟨i₁ - 1, by omega⟩,
          ⟨⟨i₁ - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩, ?_⟩
        have hstep := hg_cyc ⟨i₁ - 1, by omega⟩
        have hmod : (i₁ - 1 + 1) % m = i₁ := by
          rw [show i₁ - 1 + 1 = i₁ by omega, Nat.mod_eq_of_lt (by omega)]
        exact (by simpa only [hmod] using hstep :
          G.Adj (g ⟨i₁ - 1, by omega⟩) (g ⟨i₁, by omega⟩)).symm
      · refine ⟨g ⟨i₂ - 1, by omega⟩,
          ⟨⟨i₂ - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩,
          g ⟨i₂, by omega⟩, ⟨⟨i₂, by omega⟩, le_rfl, hi₂_lt, rfl⟩, ?_⟩
        have hstep := hg_cyc ⟨i₂ - 1, by omega⟩
        have hmod : (i₂ - 1 + 1) % m = i₂ := by
          rw [show i₂ - 1 + 1 = i₂ by omega, Nat.mod_eq_of_lt (by omega)]
        simpa only [hmod] using hstep
      · obtain ⟨h, hhH, hhg⟩ := hc_att
        exact ⟨g ⟨i₂, by omega⟩, ⟨⟨i₂, by omega⟩, le_rfl, hi₂_lt, rfl⟩, h, hhH, hhg.symm⟩
      · refine ⟨g ⟨m - 1, by omega⟩,
          ⟨⟨m - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩,
          g ⟨0, by omega⟩, ⟨⟨0, by omega⟩, le_rfl, hi₁_lo, rfl⟩, ?_⟩
        have hstep := hg_cyc ⟨m - 1, by omega⟩
        have hmod : (m - 1 + 1) % m = 0 := by
          rw [show m - 1 + 1 = m by omega, Nat.mod_self]
        simpa only [hmod] using hstep
      · refine ⟨g ⟨i₂, by omega⟩, ⟨⟨i₂, by omega⟩, le_rfl, hi₂_lt, rfl⟩,
          g ⟨i₂ - 1, by omega⟩,
          ⟨⟨i₂ - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩, ?_⟩
        have hstep := hg_cyc ⟨i₂ - 1, by omega⟩
        have hmod : (i₂ - 1 + 1) % m = i₂ := by
          rw [show i₂ - 1 + 1 = i₂ by omega, Nat.mod_eq_of_lt (by omega)]
        exact (by simpa only [hmod] using hstep :
          G.Adj (g ⟨i₂ - 1, by omega⟩) (g ⟨i₂, by omega⟩)).symm

/-! ### 4. Lemma 2: Dirac–Duffin Degree-2 Lemma -/

/-- Auxiliary graph `B[A ∪ {p, q}] + pq` for a 2-separator split `(A, C)` across `{p, q}`. -/
private def splitSideGraph {V : Type*} [DecidableEq V] (B : SimpleGraph V)
    (A : Finset V) (p q : V) (hpq : p ≠ q) :
    SimpleGraph ((insert p (insert q A) : Finset V) : Set V) where
  Adj a b := B.Adj a.1 b.1 ∨ (a.1 = p ∧ b.1 = q) ∨ (a.1 = q ∧ b.1 = p)
  symm := ⟨fun _ _ h => by
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · exact Or.inr (Or.inl ⟨h2, h1⟩)⟩
  loopless := ⟨fun a h => by
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact B.loopless.irrefl a.1 h
    · exact hpq (h1.symm.trans h2)
    · exact hpq (h2.symm.trans h1)⟩

/-- Given a 2-connected graph `B` and a 2-separator `{p, q}` splitting `V \ {p, q}` into nonempty
sides `A, C` with no edge between `A` and `C`, the side graph `B[A ∪ {p, q}] + pq` is a minor of
`B` and is 2-connected. -/
private lemma splitSideGraph_minor_and_twoConnected {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (h2 : IsTwoConnected B)
    {p q : V} (hpq : p ≠ q) {A C : Finset V}
    (hpA : p ∉ A) (hqA : q ∉ A) (hpC : p ∉ C) (hqC : q ∉ C)
    (hdisj : Disjoint A C)
    (hcover : ∀ w : V, w = p ∨ w = q ∨ w ∈ A ∨ w ∈ C)
    (hAne : A.Nonempty) (hCne : C.Nonempty)
    (hnoEdge : ∀ a ∈ A, ∀ c ∈ C, ¬ B.Adj a c) :
    HasMinor B (splitSideGraph B A p q hpq) ∧
    IsTwoConnected (splitSideGraph B A p q hpq) := by
  classical
  set W : Finset V := insert p (insert q A)
  let B' := splitSideGraph B A p q hpq
  have hpW : p ∈ W := Finset.mem_insert_self p _
  have hqW : q ∈ W := Finset.mem_insert_of_mem (Finset.mem_insert_self q A)
  have hmemW_iff : ∀ v : V, v ∈ W ↔ v = p ∨ v = q ∨ v ∈ A := by
    intro v; simp [W]
  have hC_disj_W : ∀ v ∈ C, v ∉ W := by
    intro v hvC hvW
    rcases (hmemW_iff v).mp hvW with rfl | rfl | hvA
    · exact hpC hvC
    · exact hqC hvC
    · exact Finset.disjoint_left.mp hdisj hvA hvC
  -- Part 1: `HasMinor B B'`.
  have hMinor : HasMinor B B' := by
    obtain ⟨c₀, hc₀C⟩ := hCne
    obtain ⟨a₀, ha₀A⟩ := hAne
    set K : Set V := {v : V | ∃ hv : v ∈ (C : Set V),
      (B.induce (C : Set V)).Reachable ⟨c₀, hc₀C⟩ ⟨v, hv⟩}
    have hc₀K : c₀ ∈ K := ⟨hc₀C, SimpleGraph.Reachable.refl _⟩
    have hK_conn : (B.induce K).Connected := induce_component_connected hc₀C
    have hK_sub_C : ∀ v ∈ K, v ∈ C := fun v hv => hv.1
    have hK_closed : ∀ r ∈ K, ∀ s : V, B.Adj r s → s = p ∨ s = q ∨ s ∈ K := by
      intro r hrK s hrs
      have hrC : r ∈ C := hK_sub_C r hrK
      rcases hcover s with rfl | rfl | hsA | hsC
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd hrs.symm (hnoEdge s hsA r hrC)
      · right; right
        obtain ⟨hrC', hrc⟩ := hrK
        have hrs_ind : (B.induce (C : Set V)).Adj ⟨r, hrC'⟩ ⟨s, hsC⟩ := hrs
        exact ⟨hsC, hrc.trans hrs_ind.reachable⟩
    have hK_adj_p : ∃ r ∈ K, B.Adj r p := by
      have hc₀_nq : c₀ ≠ q := fun hEq => hqC (hEq ▸ hc₀C)
      have ha₀_nq : a₀ ≠ q := fun hEq => hqA (hEq ▸ ha₀A)
      obtain ⟨P, hP⟩ := exists_walk_of_induce_reachable (h2.2 q ⟨c₀, hc₀_nq⟩ ⟨a₀, ha₀_nq⟩)
      have ha₀_notK : a₀ ∉ K := fun haK =>
        Finset.disjoint_left.mp hdisj ha₀A (hK_sub_C a₀ haK)
      obtain ⟨r, s, _, P₂, hrK, hsK, hrs, -, -, hP₂, -⟩ := walk_first_exit P hc₀K ha₀_notK
      have hsq : s ≠ q := hP s (hP₂ s (SimpleGraph.Walk.start_mem_support P₂))
      rcases hK_closed r hrK s hrs with rfl | rfl | hsK'
      · exact ⟨r, hrK, hrs⟩
      · exact absurd rfl hsq
      · exact absurd hsK' hsK
    have hK_adj_q : ∃ r ∈ K, B.Adj r q := by
      have hc₀_np : c₀ ≠ p := fun hEq => hpC (hEq ▸ hc₀C)
      have ha₀_np : a₀ ≠ p := fun hEq => hpA (hEq ▸ ha₀A)
      obtain ⟨P, hP⟩ := exists_walk_of_induce_reachable (h2.2 p ⟨c₀, hc₀_np⟩ ⟨a₀, ha₀_np⟩)
      have ha₀_notK : a₀ ∉ K := fun haK =>
        Finset.disjoint_left.mp hdisj ha₀A (hK_sub_C a₀ haK)
      obtain ⟨r, s, _, P₂, hrK, hsK, hrs, -, -, hP₂, -⟩ := walk_first_exit P hc₀K ha₀_notK
      have hsp : s ≠ p := hP s (hP₂ s (SimpleGraph.Walk.start_mem_support P₂))
      rcases hK_closed r hrK s hrs with rfl | rfl | hsK'
      · exact absurd rfl hsp
      · exact ⟨r, hrK, hrs⟩
      · exact absurd hsK' hsK
    let φ : V → Option (W : Set V) := fun v =>
      if hv : v ∈ W then some ⟨v, hv⟩
      else if v ∈ K then some ⟨p, hpW⟩
      else none
    refine hasMinor_of_partialMap φ ?_ ?_
    · intro w
      by_cases hwp : w.1 = p
      · have hwEq : w = ⟨p, hpW⟩ := Subtype.ext hwp
        rw [hwEq]
        have hfib : {v : V | φ v = some ⟨p, hpW⟩} = insert p K := by
          ext v
          simp only [Set.mem_insert_iff]
          constructor
          · intro hv
            change φ v = some ⟨p, hpW⟩ at hv
            by_cases hvW : v ∈ W
            · simp only [φ, hvW, ↓reduceDIte, Option.some.injEq] at hv
              left; exact congrArg Subtype.val hv
            · by_cases hvK : v ∈ K
              · exact Or.inr hvK
              · simp [φ, hvW, hvK] at hv
          · rintro (hvp | hvK)
            · rw [hvp]
              change φ p = some ⟨p, hpW⟩
              simp [φ, hpW]
            · change φ v = some ⟨p, hpW⟩
              have hv_notW : v ∉ W := hC_disj_W v (hK_sub_C v hvK)
              simp [φ, hv_notW, hvK]
        rw [hfib]
        obtain ⟨r, hrK, hrp⟩ := hK_adj_p
        exact induce_connected_insert hK_conn ⟨r, hrK, hrp.symm⟩
      · have hfib : {v : V | φ v = some w} = {w.1} := by
          ext v
          simp only [Set.mem_singleton_iff]
          constructor
          · intro hv
            change φ v = some w at hv
            by_cases hvW : v ∈ W
            · simp only [φ, hvW, ↓reduceDIte, Option.some.injEq] at hv
              exact congrArg Subtype.val hv
            · by_cases hvK : v ∈ K
              · simp only [φ, hvW, ↓reduceDIte, hvK, ↓reduceIte, Option.some.injEq] at hv
                exact absurd (congrArg Subtype.val hv).symm hwp
              · simp [φ, hvW, hvK] at hv
          · rintro rfl
            change φ w.1 = some w
            simp [φ]
        rw [hfib]
        have : Nonempty ({w.1} : Set V) := ⟨⟨w.1, Set.mem_singleton _⟩⟩
        refine ⟨fun a b => ?_⟩
        have ha : a.1 = w.1 := Set.mem_singleton_iff.mp a.2
        have hb : b.1 = w.1 := Set.mem_singleton_iff.mp b.2
        have hEq : a = b := Subtype.ext (ha.trans hb.symm)
        rw [hEq]
    · intro u v huv
      rcases huv with huvB | ⟨hup, hvq⟩ | ⟨huq, hvp⟩
      · refine ⟨u.1, v.1, ?_, ?_, huvB⟩
        · simp [φ]
        · simp [φ]
      · obtain ⟨r, hrK, hrq⟩ := hK_adj_q
        have hr_notW : r ∉ W := hC_disj_W r (hK_sub_C r hrK)
        refine ⟨r, q, ?_, ?_, hrq⟩
        · simp only [φ, hr_notW, ↓reduceDIte, hrK, ↓reduceIte]
          congr 1; exact Subtype.ext hup.symm
        · simp only [φ, hqW, ↓reduceDIte]
          congr 1; exact Subtype.ext hvq.symm
      · obtain ⟨r, hrK, hrq⟩ := hK_adj_q
        have hr_notW : r ∉ W := hC_disj_W r (hK_sub_C r hrK)
        refine ⟨q, r, ?_, ?_, hrq.symm⟩
        · simp only [φ, hqW, ↓reduceDIte]
          congr 1; exact Subtype.ext huq.symm
        · simp only [φ, hr_notW, ↓reduceDIte, hrK, ↓reduceIte]
          congr 1; exact Subtype.ext hvp.symm
  -- Part 2: `IsTwoConnected B'`.
  have h2' : IsTwoConnected B' := by
    refine ⟨?_, ?_⟩
    · obtain ⟨a₀, ha₀A⟩ := hAne
      have h3sub : ({p, q, a₀} : Finset V) ⊆ W := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hpW
        · rcases Finset.mem_insert.mp hv with rfl | hv
          · exact hqW
          · rw [Finset.mem_singleton.mp hv]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha₀A)
      have h3card : ({p, q, a₀} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair]
        · exact fun h => hqA (h ▸ ha₀A)
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hpq, fun h => hpA (h ▸ ha₀A)⟩
      have hW3 : 3 ≤ W.card := h3card ▸ Finset.card_le_card h3sub
      simpa [Fintype.card_coe] using hW3
    · intro w
      -- Helper for deleting `p` or `q` (symmetric in `p, q`).
      have hdel_sep : ∀ (s t : V) (hsW : s ∈ W) (htW : t ∈ W),
          (s = p ∧ t = q) ∨ (s = q ∧ t = p) →
          (B'.induce {u : (W : Set V) | u ≠ ⟨s, hsW⟩}).Connected := by
        intro s t hsW htW hst
        have hts : t ≠ s := by
          rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hpq.symm
          · exact hpq
        have ht_mem : ⟨t, htW⟩ ∈ ({u : (W : Set V) | u ≠ ⟨s, hsW⟩} : Set (W : Set V)) :=
          fun hEq => hts (congrArg Subtype.val hEq)
        have : Nonempty ({u : (W : Set V) | u ≠ ⟨s, hsW⟩} : Set (W : Set V)) :=
          ⟨⟨⟨t, htW⟩, ht_mem⟩⟩
        refine ⟨fun x y => ?_⟩
        have hto : ∀ z : ({u : (W : Set V) | u ≠ ⟨s, hsW⟩} : Set (W : Set V)),
            (B'.induce {u : (W : Set V) | u ≠ ⟨s, hsW⟩}).Reachable z ⟨⟨t, htW⟩, ht_mem⟩ := by
          intro z
          by_cases hzt : z.1.1 = t
          · have hEq : z = ⟨⟨t, htW⟩, ht_mem⟩ := Subtype.ext (Subtype.ext hzt)
            rw [hEq]
          · have hz_ns : z.1.1 ≠ s := fun hEq => z.2 (Subtype.ext hEq)
            have hzA : z.1.1 ∈ A := by
              rcases (hmemW_iff z.1.1).mp z.1.2 with hp' | hq' | hA'
              · rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact absurd hp' hz_ns
                · exact absurd hp' hzt
              · rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact absurd hq' hzt
                · exact absurd hq' hz_ns
              · exact hA'
            obtain ⟨P, hP⟩ := exists_walk_of_induce_reachable (h2.2 s ⟨z.1.1, hz_ns⟩ ⟨t, hts⟩)
            have ht_notA : t ∉ (A : Set V) := by
              rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hqA
              · exact hpA
            obtain ⟨a, b, P₁, P₂, haA, hbA, hab, hP₁A, -, hP₂, -⟩ := walk_first_exit P hzA ht_notA
            have hb_ns : b ≠ s := hP b (hP₂ b (SimpleGraph.Walk.start_mem_support P₂))
            have hbt : b = t := by
              rcases hcover b with rfl | rfl | hbA' | hbC
              · rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact absurd rfl hb_ns
                · rfl
              · rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rfl
                · exact absurd rfl hb_ns
              · exact absurd hbA' hbA
              · exact absurd hab (hnoEdge a haA b hbC)
            have haW : a ∈ W := (hmemW_iff a).mpr (Or.inr (Or.inr haA))
            have ha_ns : (⟨a, haW⟩ : (W : Set V)) ≠ ⟨s, hsW⟩ := by
              intro hEq
              have has : a = s := congrArg Subtype.val hEq
              rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hpA (has ▸ haA)
              · exact hqA (has ▸ haA)
            -- Lift `P₁` inside `A` to `B' - s`.
            have hwalk_lift : ∀ {u₁ u₂ : V} (Q : B.Walk u₁ u₂)
                (hu₁ : u₁ ∈ A) (hu₂ : u₂ ∈ A) (hQ : ∀ r ∈ Q.support, r ∈ A),
                (B'.induce {u : (W : Set V) | u ≠ ⟨s, hsW⟩}).Reachable
                  ⟨⟨u₁, (hmemW_iff u₁).mpr (Or.inr (Or.inr hu₁))⟩,
                    fun hEq => by
                      have hu₁s : u₁ = s := congrArg Subtype.val hEq
                      rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · exact hpA (hu₁s ▸ hu₁)
                      · exact hqA (hu₁s ▸ hu₁)⟩
                  ⟨⟨u₂, (hmemW_iff u₂).mpr (Or.inr (Or.inr hu₂))⟩,
                    fun hEq => by
                      have hu₂s : u₂ = s := congrArg Subtype.val hEq
                      rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · exact hpA (hu₂s ▸ hu₂)
                      · exact hqA (hu₂s ▸ hu₂)⟩ := by
              intro u₁ u₂ Q
              induction Q with
              | nil =>
                intro _ _ _
                exact SimpleGraph.Reachable.refl _
              | @cons c d e hcd R ih =>
                intro hcA heA hQR
                have hdA : d ∈ A := hQR d (by simp)
                have hc_ns : (⟨c, (hmemW_iff c).mpr (Or.inr (Or.inr hcA))⟩ : (W : Set V)) ≠
                    ⟨s, hsW⟩ := fun hEq => by
                  have hcs : c = s := congrArg Subtype.val hEq
                  rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact hpA (hcs ▸ hcA)
                  · exact hqA (hcs ▸ hcA)
                have hd_ns : (⟨d, (hmemW_iff d).mpr (Or.inr (Or.inr hdA))⟩ : (W : Set V)) ≠
                    ⟨s, hsW⟩ := fun hEq => by
                  have hds : d = s := congrArg Subtype.val hEq
                  rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact hpA (hds ▸ hdA)
                  · exact hqA (hds ▸ hdA)
                have hstep : (B'.induce {u : (W : Set V) | u ≠ ⟨s, hsW⟩}).Adj
                    ⟨⟨c, (hmemW_iff c).mpr (Or.inr (Or.inr hcA))⟩, hc_ns⟩
                    ⟨⟨d, (hmemW_iff d).mpr (Or.inr (Or.inr hdA))⟩, hd_ns⟩ := Or.inl hcd
                exact hstep.reachable.trans (ih hdA heA fun r hr => hQR r (by simp [hr]))
            have hz_to_a := hwalk_lift P₁ hzA haA (fun r hr => hP₁A r hr)
            have ha_to_t : (B'.induce {u : (W : Set V) | u ≠ ⟨s, hsW⟩}).Adj
                ⟨⟨a, haW⟩, ha_ns⟩ ⟨⟨t, htW⟩, ht_mem⟩ := Or.inl (hbt ▸ hab)
            exact hz_to_a.trans ha_to_t.reachable
        exact (hto x).trans (hto y).symm
      by_cases hwp : w.1 = p
      · have hEq : w = ⟨p, hpW⟩ := Subtype.ext hwp
        rw [hEq]
        exact hdel_sep p q hpW hqW (Or.inl ⟨rfl, rfl⟩)
      by_cases hwq : w.1 = q
      · have hEq : w = ⟨q, hqW⟩ := Subtype.ext hwq
        rw [hEq]
        exact hdel_sep q p hqW hpW (Or.inr ⟨rfl, rfl⟩)
      -- Case `w.1 ∈ A`: shortcut excursions into `C` via `pq`.
      have hwA : w.1 ∈ A := by
        rcases (hmemW_iff w.1).mp w.2 with hp' | hq' | hA'
        · exact absurd hp' hwp
        · exact absurd hq' hwq
        · exact hA'
      have hp_nw : (⟨p, hpW⟩ : (W : Set V)) ≠ w := fun hEq => hwp (congrArg Subtype.val hEq).symm
      have hq_nw : (⟨q, hqW⟩ : (W : Set V)) ≠ w := fun hEq => hwq (congrArg Subtype.val hEq).symm
      have : Nonempty ({u : (W : Set V) | u ≠ w} : Set (W : Set V)) := ⟨⟨⟨p, hpW⟩, hp_nw⟩⟩
      -- Strong induction on walk length shortcutting `B - w` walks between vertices of `W \ {w}`.
      have hshortcut : ∀ (len : ℕ) (a b : (W : Set V)) (ha : a ≠ w) (hb : b ≠ w)
          (P : B.Walk a.1 b.1),
          P.length = len → (∀ r ∈ P.support, r ≠ w.1) →
          (B'.induce {u : (W : Set V) | u ≠ w}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
        intro len
        induction len using Nat.strong_induction_on with
        | _ len ih =>
          intro a b ha hb P hlen hPnw
          generalize ha1 : a.1 = a₁ at P hlen hPnw
          generalize hb1 : b.1 = b₁ at P hlen hPnw
          cases P with
          | nil =>
            have hEq : a = b := Subtype.ext (ha1.trans hb1.symm)
            subst hEq
            exact SimpleGraph.Reachable.refl _
          | @cons _ d _ had Q =>
            subst ha1
            subst hb1
            have hdw : d ≠ w.1 := hPnw d (by simp)
            have hQnw : ∀ r ∈ Q.support, r ≠ w.1 := fun r hr => hPnw r (by simp [hr])
            by_cases hdW : d ∈ W
            · have hd_nw : (⟨d, hdW⟩ : (W : Set V)) ≠ w := fun hEq => hdw (congrArg Subtype.val hEq)
              have hstep : (B'.induce {u : (W : Set V) | u ≠ w}).Adj ⟨a, ha⟩ ⟨⟨d, hdW⟩, hd_nw⟩ :=
                Or.inl had
              have hrest := ih Q.length (by simp [← hlen]) ⟨d, hdW⟩ b hd_nw hb Q rfl hQnw
              exact hstep.reachable.trans hrest
            · have hdC : d ∈ C := by
                rcases hcover d with rfl | rfl | hdA | hdC
                · exact absurd hpW hdW
                · exact absurd hqW hdW
                · exact absurd ((hmemW_iff d).mpr (Or.inr (Or.inr hdA))) hdW
                · exact hdC
              have ha_sep : a.1 = p ∨ a.1 = q := by
                rcases (hmemW_iff a.1).mp a.2 with hp' | hq' | haA
                · exact Or.inl hp'
                · exact Or.inr hq'
                · exact absurd had (hnoEdge a.1 haA d hdC)
              -- Walk `Q` starts at `d ∈ C` and ends at `b.1 ∈ W` (`b.1 ∉ C`).
              have hb_notC : b.1 ∉ (C : Set V) := fun hbC => hC_disj_W b.1 hbC b.2
              obtain ⟨r, e, _, Q₂, hrC, heC, hre, -, -, hQ₂, hQ₂len⟩ :=
                walk_first_exit Q hdC hb_notC
              have he_sep : e = p ∨ e = q := by
                rcases hcover e with rfl | rfl | heA | heC'
                · exact Or.inl rfl
                · exact Or.inr rfl
                · exact absurd hre.symm (hnoEdge e heA r hrC)
                · exact absurd heC' heC
              have heW : e ∈ W := by
                rcases he_sep with rfl | rfl
                · exact hpW
                · exact hqW
              have he_nw : (⟨e, heW⟩ : (W : Set V)) ≠ w := by
                rcases he_sep with rfl | rfl
                · exact hp_nw
                · exact hq_nw
              have ha_to_e : (B'.induce {u : (W : Set V) | u ≠ w}).Reachable
                  ⟨a, ha⟩ ⟨⟨e, heW⟩, he_nw⟩ := by
                by_cases hae : a.1 = e
                · have hEq : (⟨a, ha⟩ : ({u : (W : Set V) | u ≠ w} : Set (W : Set V))) =
                      ⟨⟨e, heW⟩, he_nw⟩ := Subtype.ext (Subtype.ext hae)
                  rw [hEq]
                · have hadj_ae : B'.Adj a ⟨e, heW⟩ := by
                    rcases ha_sep with ha' | ha' <;> rcases he_sep with he' | he'
                    · exact absurd (ha'.trans he'.symm) hae
                    · exact Or.inr (Or.inl ⟨ha', he'⟩)
                    · exact Or.inr (Or.inr ⟨ha', he'⟩)
                    · exact absurd (ha'.trans he'.symm) hae
                  exact (show (B'.induce {u : (W : Set V) | u ≠ w}).Adj ⟨a, ha⟩ ⟨⟨e, heW⟩, he_nw⟩
                    from hadj_ae).reachable
              have hQ₂_lt : Q₂.length < len := by
                have : Q.length < len := by simp [← hlen]
                omega
              have hQ₂_nw : ∀ t ∈ Q₂.support, t ≠ w.1 := fun t ht => hQnw t (hQ₂ t ht)
              have he_to_b := ih Q₂.length hQ₂_lt ⟨e, heW⟩ b he_nw hb Q₂ rfl hQ₂_nw
              exact ha_to_e.trans he_to_b
      refine ⟨fun x y => ?_⟩
      have hx_nw : x.1.1 ≠ w.1 := fun hEq => x.2 (Subtype.ext hEq)
      have hy_nw : y.1.1 ≠ w.1 := fun hEq => y.2 (Subtype.ext hEq)
      obtain ⟨P, hP⟩ := exists_walk_of_induce_reachable (h2.2 w.1 ⟨x.1.1, hx_nw⟩ ⟨y.1.1, hy_nw⟩)
      exact hshortcut P.length x.1 y.1 x.2 y.2 P rfl hP
  exact ⟨hMinor, h2'⟩

/-- Auxiliary universe-fixed strong induction for Lemma 2. -/
private lemma exists_deg_two_avoiding_edge_aux :
    ∀ (n : ℕ) {V : Type u} [Fintype V] (B : SimpleGraph V),
      Fintype.card V = n →
      IsTwoConnected B → ¬ HasMinor B K4 →
      ∀ {x y : V}, B.Adj x y →
        ∃ v : V, v ≠ x ∧ v ≠ y ∧
          ∃ u₁ u₂ : V, u₁ ≠ u₂ ∧ ∀ w : V, B.Adj v w ↔ w = u₁ ∨ w = u₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ B hcard h2 hK4 x y hxy
    classical
    have hn3 : 3 ≤ n := hcard ▸ h2.1
    by_cases hn_eq3 : n = 3
    · -- Base case `|V| = 3`: `B ≅ K_3`.
      let R : Finset V := (Finset.univ.erase x).erase y
      have hy_er : y ∈ Finset.univ.erase x :=
        Finset.mem_erase.mpr ⟨hxy.ne.symm, Finset.mem_univ y⟩
      have hR_card : R.card = 1 := by
        rw [Finset.card_erase_of_mem hy_er, Finset.card_erase_of_mem (Finset.mem_univ x),
          Finset.card_univ, hcard, hn_eq3]
      obtain ⟨v, hvR⟩ := Finset.card_eq_one.mp hR_card
      have hv_mem : v ∈ R := by rw [hvR]; exact Finset.mem_singleton_self v
      have hvy : v ≠ y := (Finset.mem_erase.mp hv_mem).1
      have hvx : v ≠ x := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hv_mem)).1
      have htri : ∀ w : V, w = x ∨ w = y ∨ w = v := by
        intro w
        by_cases hwx : w = x
        · exact Or.inl hwx
        by_cases hwy : w = y
        · exact Or.inr (Or.inl hwy)
        right; right
        have hwR : w ∈ R :=
          Finset.mem_erase.mpr ⟨hwy, Finset.mem_erase.mpr ⟨hwx, Finset.mem_univ w⟩⟩
        rw [hvR] at hwR
        exact Finset.mem_singleton.mp hwR
      have hv_adj_x : B.Adj v x := by
        obtain ⟨P, hP⟩ := exists_walk_of_induce_reachable (h2.2 y ⟨v, hvy⟩ ⟨x, hxy.ne⟩)
        cases P with
        | nil => exact absurd rfl hvx
        | @cons _ w _ hvw _ =>
          have hwy : w ≠ y := hP w (by simp)
          have hwv : w ≠ v := hvw.ne.symm
          rcases htri w with rfl | rfl | rfl
          · exact hvw
          · exact absurd rfl hwy
          · exact absurd rfl hwv
      have hv_adj_y : B.Adj v y := by
        obtain ⟨P, hP⟩ := exists_walk_of_induce_reachable (h2.2 x ⟨v, hvx⟩ ⟨y, hxy.ne.symm⟩)
        cases P with
        | nil => exact absurd rfl hvy
        | @cons _ w _ hvw _ =>
          have hwx : w ≠ x := hP w (by simp)
          have hwv : w ≠ v := hvw.ne.symm
          rcases htri w with rfl | rfl | rfl
          · exact absurd rfl hwx
          · exact hvw
          · exact absurd rfl hwv
      refine ⟨v, hvx, hvy, x, y, hxy.ne, fun w => ⟨fun hvw => ?_, fun h => ?_⟩⟩
      · rcases htri w with rfl | rfl | hwv
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd (hwv ▸ hvw) (B.loopless.irrefl v)
      · rcases h with rfl | rfl
        · exact hv_adj_x
        · exact hv_adj_y
    · -- Inductive step `|V| ≥ 4`.
      have hn4 : 4 ≤ Fintype.card V := by omega
      have hnot3 : ¬ IsThreeConnected B := fun h3 => hK4 (hasMinor_K4_of_isThreeConnected h3)
      have hexS : ∃ S : Finset V, S.card ≤ 2 ∧ ¬ (B.induce {w : V | w ∉ S}).Connected := by
        by_contra hall
        push Not at hall
        exact hnot3 ⟨hn4, hall⟩
      obtain ⟨S, hS_le, hS_disc⟩ := hexS
      have hS_ne0 : S.card ≠ 0 := by
        intro h0
        have hSempty : S = ∅ := Finset.card_eq_zero.mp h0
        have hconnB := h2.connected
        have hEq : ({w : V | w ∉ S} : Set V) = Set.univ := by ext w; simp [hSempty]
        have : Nonempty ({w : V | w ∉ S} : Set V) := by
          rw [hEq]
          exact ⟨⟨x, Set.mem_univ x⟩⟩
        apply hS_disc
        refine ⟨fun a b => ?_⟩
        obtain ⟨P⟩ := hconnB a.1 b.1
        exact induce_reachable_of_walk a.2 b.2 P fun t _ => by simp [hSempty]
      have hS_ne1 : S.card ≠ 1 := by
        intro h1
        obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp h1
        have hEq : ({w : V | w ∉ ({z} : Finset V)} : Set V) = {w : V | w ≠ z} := by ext w; simp
        rw [hEq] at hS_disc
        exact hS_disc (h2.2 z)
      have hS_eq2 : S.card = 2 := by omega
      obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hS_eq2
      have hcompl_ne : (Finset.univ \ ({p, q} : Finset V)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hle : Fintype.card V ≤ ({p, q} : Finset V).card := by
          have : Finset.univ ⊆ ({p, q} : Finset V) := Finset.sdiff_eq_empty_iff_subset.mp hemp
          simpa using Finset.card_le_card this
        have h2p : ({p, q} : Finset V).card ≤ 2 := Finset.card_le_two
        omega
      obtain ⟨u₀, hu₀_mem⟩ := hcompl_ne
      have hu₀_not : u₀ ∉ ({p, q} : Finset V) := (Finset.mem_sdiff.mp hu₀_mem).2
      have hnonempty_rem : Nonempty ({w : V | w ∉ ({p, q} : Finset V)} : Set V) :=
        ⟨⟨u₀, hu₀_not⟩⟩
      have hex_unreach : ∃ u₁ : ({w : V | w ∉ ({p, q} : Finset V)} : Set V),
          ¬ (B.induce {w : V | w ∉ ({p, q} : Finset V)}).Reachable ⟨u₀, hu₀_not⟩ u₁ := by
        by_contra hall
        push Not at hall
        exact hS_disc ⟨fun a b => (hall a).symm.trans (hall b)⟩
      obtain ⟨u₁, hu₁_unreach⟩ := hex_unreach
      let U₁ : Finset V := (Finset.univ \ ({p, q} : Finset V)).filter fun w =>
        ∃ hw : w ∉ ({p, q} : Finset V),
          (B.induce {t : V | t ∉ ({p, q} : Finset V)}).Reachable ⟨u₀, hu₀_not⟩ ⟨w, hw⟩
      let U₂ : Finset V := (Finset.univ \ ({p, q} : Finset V)).filter fun w =>
        ∀ hw : w ∉ ({p, q} : Finset V),
          ¬ (B.induce {t : V | t ∉ ({p, q} : Finset V)}).Reachable ⟨u₀, hu₀_not⟩ ⟨w, hw⟩
      have hpU₁ : p ∉ U₁ := by simp [U₁]
      have hqU₁ : q ∉ U₁ := by simp [U₁]
      have hpU₂ : p ∉ U₂ := by simp [U₂]
      have hqU₂ : q ∉ U₂ := by simp [U₂]
      have hdisj12 : Disjoint U₁ U₂ := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        simp only [U₁, U₂, Finset.mem_filter] at hw1 hw2
        obtain ⟨hw, hr⟩ := hw1.2
        exact hw2.2 hw hr
      have hcover12 : ∀ w : V, w = p ∨ w = q ∨ w ∈ U₁ ∨ w ∈ U₂ := by
        intro w
        by_cases hwp : w = p
        · exact Or.inl hwp
        by_cases hwq : w = q
        · exact Or.inr (Or.inl hwq)
        have hw_not : w ∉ ({p, q} : Finset V) := by simp [hwp, hwq]
        by_cases hr : (B.induce {t : V | t ∉ ({p, q} : Finset V)}).Reachable ⟨u₀, hu₀_not⟩
            ⟨w, hw_not⟩
        · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw_not⟩, hw_not, hr⟩)))
        · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw_not⟩, fun _ => hr⟩)))
      have hU₁ne : U₁.Nonempty :=
        ⟨u₀, Finset.mem_filter.mpr ⟨hu₀_mem, hu₀_not, SimpleGraph.Reachable.refl _⟩⟩
      have hU₂ne : U₂.Nonempty :=
        ⟨u₁.1, Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ u₁.1, u₁.2⟩, fun _ => hu₁_unreach⟩⟩
      have hnoEdge12 : ∀ a ∈ U₁, ∀ c ∈ U₂, ¬ B.Adj a c := by
        intro a ha c hc hac
        simp only [U₁, U₂, Finset.mem_filter, Finset.mem_sdiff] at ha hc
        obtain ⟨ha_not, hra⟩ := ha.2
        have hc_not : c ∉ ({p, q} : Finset V) := hc.1.2
        have hstep : (B.induce {t : V | t ∉ ({p, q} : Finset V)}).Adj ⟨a, ha_not⟩ ⟨c, hc_not⟩ := hac
        exact hc.2 hc_not (hra.trans hstep.reachable)
      -- Helper applying IH to whichever side `A` avoids `{x, y}`.
      have hsolve : ∀ (A C : Finset V),
          p ∉ A → q ∉ A → p ∉ C → q ∉ C → Disjoint A C →
          (∀ w : V, w = p ∨ w = q ∨ w ∈ A ∨ w ∈ C) →
          A.Nonempty → C.Nonempty →
          (∀ a ∈ A, ∀ c ∈ C, ¬ B.Adj a c) →
          x ∉ A → y ∉ A →
          ∃ v : V, v ≠ x ∧ v ≠ y ∧
            ∃ u₁ u₂ : V, u₁ ≠ u₂ ∧ ∀ w : V, B.Adj v w ↔ w = u₁ ∨ w = u₂ := by
        intro A C hpA hqA hpC hqC hdisj hcover hAne hCne hnoE hxA hyA
        obtain ⟨hMinor, h2'⟩ :=
          splitSideGraph_minor_and_twoConnected B h2 hpq hpA hqA hpC hqC
            hdisj hcover hAne hCne hnoE
        have hK4' : ¬ HasMinor (splitSideGraph B A p q hpq) K4 :=
          fun h => hK4 (hasMinor_trans hMinor h)
        set W : Finset V := insert p (insert q A)
        have hpW : p ∈ W := Finset.mem_insert_self p _
        have hqW : q ∈ W := Finset.mem_insert_of_mem (Finset.mem_insert_self q A)
        have hW_lt : Fintype.card (W : Set V) < n := by
          obtain ⟨c₀, hc₀C⟩ := hCne
          have hc₀_notW : c₀ ∉ W := by
            intro hcW
            simp only [W, Finset.mem_insert] at hcW
            rcases hcW with rfl | rfl | hcA
            · exact hpC hc₀C
            · exact hqC hc₀C
            · exact Finset.disjoint_left.mp hdisj hcA hc₀C
          have hssub : W ⊂ Finset.univ :=
            Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ W, fun hEq =>
              hc₀_notW (hEq ▸ Finset.mem_univ c₀)⟩
          have hlt : W.card < Fintype.card V := by
            simpa [Finset.card_univ] using Finset.card_lt_card hssub
          simpa [Fintype.card_coe, hcard] using hlt
        have hpq_adj : (splitSideGraph B A p q hpq).Adj ⟨p, hpW⟩ ⟨q, hqW⟩ :=
          Or.inr (Or.inl ⟨rfl, rfl⟩)
        obtain ⟨v', hv'p, hv'q, u₁', u₂', hu₁₂', hNv'⟩ :=
          ih (Fintype.card (W : Set V)) hW_lt (splitSideGraph B A p q hpq) rfl h2' hK4' hpq_adj
        have hvp : v'.1 ≠ p := fun hEq => hv'p (Subtype.ext hEq)
        have hvq : v'.1 ≠ q := fun hEq => hv'q (Subtype.ext hEq)
        have hvA : v'.1 ∈ A := by
          have hvW : v'.1 ∈ W := Finset.mem_coe.mp v'.2
          simp only [W, Finset.mem_insert] at hvW
          rcases hvW with hp' | hq' | hA'
          · exact absurd hp' hvp
          · exact absurd hq' hvq
          · exact hA'
        have hvx : v'.1 ≠ x := fun hEq => hxA (hEq ▸ hvA)
        have hvy : v'.1 ≠ y := fun hEq => hyA (hEq ▸ hvA)
        have hu₁₂ : u₁'.1 ≠ u₂'.1 := fun hEq => hu₁₂' (Subtype.ext hEq)
        refine ⟨v'.1, hvx, hvy, u₁'.1, u₂'.1, hu₁₂, fun w => ?_⟩
        constructor
        · intro hvw
          have hwW : w ∈ W := by
            rcases hcover w with rfl | rfl | hwA | hwC
            · exact hpW
            · exact hqW
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwA)
            · exact absurd hvw (hnoE v'.1 hvA w hwC)
          have hvw' : (splitSideGraph B A p q hpq).Adj v' ⟨w, hwW⟩ := Or.inl hvw
          rcases (hNv' ⟨w, hwW⟩).mp hvw' with h1 | h2
          · exact Or.inl (congrArg Subtype.val h1)
          · exact Or.inr (congrArg Subtype.val h2)
        · rintro (rfl | rfl)
          · have h1 := (hNv' u₁').mpr (Or.inl rfl)
            rcases h1 with hB | ⟨hp', _⟩ | ⟨hq', _⟩
            · exact hB
            · exact absurd hp' hvp
            · exact absurd hq' hvq
          · have h2 := (hNv' u₂').mpr (Or.inr rfl)
            rcases h2 with hB | ⟨hp', _⟩ | ⟨hq', _⟩
            · exact hB
            · exact absurd hp' hvp
            · exact absurd hq' hvq
      by_cases hxU₂ : x ∈ U₂
      · have hy_notU₁ : y ∉ U₁ := fun hyU₁ => hnoEdge12 y hyU₁ x hxU₂ hxy.symm
        have hx_notU₁ : x ∉ U₁ := fun hxU₁ => Finset.disjoint_left.mp hdisj12 hxU₁ hxU₂
        exact hsolve U₁ U₂ hpU₁ hqU₁ hpU₂ hqU₂ hdisj12 hcover12 hU₁ne hU₂ne hnoEdge12
          hx_notU₁ hy_notU₁
      · by_cases hyU₂ : y ∈ U₂
        · have hx_notU₁ : x ∉ U₁ := fun hxU₁ => hnoEdge12 x hxU₁ y hyU₂ hxy
          have hy_notU₁ : y ∉ U₁ := fun hyU₁ => Finset.disjoint_left.mp hdisj12 hyU₁ hyU₂
          exact hsolve U₁ U₂ hpU₁ hqU₁ hpU₂ hqU₂ hdisj12 hcover12 hU₁ne hU₂ne hnoEdge12
            hx_notU₁ hy_notU₁
        · exact hsolve U₂ U₁ hpU₂ hqU₂ hpU₁ hqU₁ hdisj12.symm
            (fun w => by rcases hcover12 w with h | h | h | h <;> simp [h])
            hU₂ne hU₁ne (fun a ha c hc hac => hnoEdge12 c hc a ha hac.symm)
            hxU₂ hyU₂

/-- **Lemma 2 (Dirac–Duffin Degree-2 Lemma):**
Let `B` be a finite simple 2-connected `K_4`-minor-free graph (`|V(B)| ≥ 3`). Then for every
edge `xy ∈ E(B)`, there exists a vertex `v ∉ {x, y}` having exactly two distinct neighbors
`u₁, u₂` in `B`. -/
theorem exists_deg_two_avoiding_edge {V : Type*} [Fintype V] (B : SimpleGraph V)
    (h2 : IsTwoConnected B) (hK4 : ¬ HasMinor B K4) {x y : V} (hxy : B.Adj x y) :
    ∃ v : V, v ≠ x ∧ v ≠ y ∧
      ∃ u₁ u₂ : V, u₁ ≠ u₂ ∧ ∀ w : V, B.Adj v w ↔ w = u₁ ∨ w = u₂ :=
  exists_deg_two_avoiding_edge_aux (Fintype.card V) B rfl h2 hK4 hxy

end LeanForge.CosteOuterplanar
