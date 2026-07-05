/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Trees.Labelled

/-!
# Planar Pre-Lie Grafting

This file defines the planar rooted-tree grafting operation which underlies the
pre-Lie product on rooted trees. The operation returns the list of all planar
trees obtained by grafting the first tree at one vertex of the second tree.
-/

namespace BSeries

open HopfAlgebras

universe u v

namespace PTree

open HopfAlgebras.PTree

mutual

/-- All planar trees obtained by grafting `s` at one vertex of `t`. -/
def preLieGrafts (s : PTree) : PTree → List PTree
  | .node ts => .node (s :: ts) :: (preLieGraftsList s ts).map PTree.node

/-- Child-list replacements induced by grafting `s` at one vertex of a child. -/
def preLieGraftsList (s : PTree) : List PTree → List (List PTree)
  | [] => []
  | t :: ts =>
      ((preLieGrafts s t).map fun t' => t' :: ts) ++
        ((preLieGraftsList s ts).map fun us => t :: us)

end

@[simp]
theorem preLieGrafts_node (s : PTree) (ts : List PTree) :
    preLieGrafts s (.node ts) =
      .node (s :: ts) :: (preLieGraftsList s ts).map PTree.node :=
  rfl

@[simp]
theorem preLieGraftsList_nil (s : PTree) :
    preLieGraftsList s [] = [] :=
  rfl

@[simp]
theorem preLieGraftsList_cons (s t : PTree) (ts : List PTree) :
    preLieGraftsList s (t :: ts) =
      ((preLieGrafts s t).map fun t' => t' :: ts) ++
        ((preLieGraftsList s ts).map fun us => t :: us) :=
  rfl

@[simp]
theorem preLieGrafts_bullet (s : PTree) :
    preLieGrafts s bullet = [.node [s]] := by
  simp [bullet]

mutual

theorem length_preLieGrafts (s : PTree) :
    ∀ t : PTree, (preLieGrafts s t).length = order t
  | .node ts => by
      rw [preLieGrafts_node, List.length_cons, List.length_map,
        length_preLieGraftsList s ts, order_node]
      omega

theorem length_preLieGraftsList (s : PTree) :
    ∀ ts : List PTree, (preLieGraftsList s ts).length = orderList ts
  | [] => by
      simp
  | t :: ts => by
      rw [preLieGraftsList_cons, List.length_append, List.length_map, List.length_map,
        length_preLieGrafts s t, length_preLieGraftsList s ts, orderList_cons]

end

mutual

theorem order_of_mem_preLieGrafts (s : PTree) :
    ∀ {t u : PTree}, u ∈ preLieGrafts s t → order u = order s + order t
  | .node ts, u, hu => by
      simp only [preLieGrafts_node, List.mem_cons, List.mem_map] at hu
      rcases hu with hu | ⟨us, hus, hu⟩
      · cases hu
        simp [order_node]
        omega
      · cases hu
        rw [order_node, order_of_mem_preLieGraftsList s hus, order_node]
        omega

theorem order_of_mem_preLieGraftsList (s : PTree) :
    ∀ {ts us : List PTree},
      us ∈ preLieGraftsList s ts → orderList us = order s + orderList ts
  | [], us, hus => by
      simp at hus
  | t :: ts, us, hus => by
      simp only [preLieGraftsList_cons, List.mem_append, List.mem_map] at hus
      rcases hus with ⟨u, hu, hus⟩ | ⟨vs, hvs, hus⟩
      · cases hus
        rw [orderList_cons, order_of_mem_preLieGrafts s hu, orderList_cons]
        omega
      · cases hus
        rw [orderList_cons, order_of_mem_preLieGraftsList s hvs, orderList_cons]
        omega

end

mutual

theorem preLieGrafts_listRelPerm_left {s s' : PTree} (hs : Perm s s') :
    ∀ t : PTree, ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s' t)
  | .node ts => by
      rw [preLieGrafts_node, preLieGrafts_node]
      refine ListRelPerm.cons ?_ ?_
      · exact .node (List.Perm.refl _) (.cons hs (permForall2_refl ts))
      · exact ListRelPerm.map
          (fun h => Perm.node (List.Perm.refl _) h)
          (preLieGraftsList_listRelPerm_left hs ts)

theorem preLieGraftsList_listRelPerm_left {s s' : PTree} (hs : Perm s s') :
    ∀ ts : List PTree,
      ListRelPerm (List.Forall₂ Perm) (preLieGraftsList s ts) (preLieGraftsList s' ts)
  | [] => by
      simp
      exact ListRelPerm.of_forall₂ .nil
  | t :: ts => by
      rw [preLieGraftsList_cons, preLieGraftsList_cons]
      exact ListRelPerm.append
        (ListRelPerm.map
          (fun h => List.Forall₂.cons h (permForall2_refl ts))
          (preLieGrafts_listRelPerm_left hs t))
        (ListRelPerm.map
          (fun h => List.Forall₂.cons (Perm.refl t) h)
          (preLieGraftsList_listRelPerm_left hs ts))

end

theorem preLieGrafts_map_ofPTree_perm_left {s s' : PTree} (hs : Perm s s')
    (t : PTree) :
    ((preLieGrafts s t).map RootedTree.ofPTree).Perm
      ((preLieGrafts s' t).map RootedTree.ofPTree) :=
  ListRelPerm.map_eq_perm
    (fun h => RootedTree.ofPTree_eq_iff.2 h)
    (preLieGrafts_listRelPerm_left hs t)

theorem preLieGraftsList_map_ofPTree_perm_left {s s' : PTree} (hs : Perm s s')
    (ts : List PTree) :
    ((preLieGraftsList s ts).map fun us => us.map RootedTree.ofPTree).Perm
      ((preLieGraftsList s' ts).map fun us => us.map RootedTree.ofPTree) :=
  ListRelPerm.map_eq_perm
    (fun h => RootedTree.map_ofPTree_eq_of_forall₂_perm h)
    (preLieGraftsList_listRelPerm_left hs ts)

private theorem node_cons_perm_of_list_perm {x y : PTree} {ts us : List PTree}
    (hxy : Perm x y) (hp : ts.Perm us) :
    Perm (.node (x :: ts)) (.node (y :: us)) :=
  .node (List.Perm.cons _ hp) (.cons hxy (permForall2_refl us))

private theorem node_cons_perm_of_node_perm {t u : PTree} {vs ws : List PTree}
    (htu : Perm t u) (h : Perm (.node vs) (.node ws)) :
    Perm (.node (t :: vs)) (.node (u :: ws)) := by
  cases h with
  | node hp hf =>
      exact .node (List.Perm.cons _ hp) (.cons htu hf)

private theorem forall₂_perm_of_forall₂_perm_grafts
    {P : PTree → PTree → Prop} :
    ∀ {ts us : List PTree},
      List.Forall₂ (fun t u => Perm t u ∧ P t u) ts us →
        List.Forall₂ Perm ts us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h htail =>
      .cons h.1 (forall₂_perm_of_forall₂_perm_grafts htail)

theorem preLieGraftsList_listRelPerm_node_of_perm (s : PTree) :
    ∀ {ts us : List PTree}, ts.Perm us →
      ListRelPerm (fun vs ws => Perm (.node vs) (.node ws))
        (preLieGraftsList s ts) (preLieGraftsList s us)
  | _, _, .nil => by
      simp
      exact ListRelPerm.of_forall₂ .nil
  | _, _, .cons t hp => by
      have ih := preLieGraftsList_listRelPerm_node_of_perm s hp
      rw [preLieGraftsList_cons, preLieGraftsList_cons]
      exact ListRelPerm.append
        (ListRelPerm.map
          (fun h => node_cons_perm_of_list_perm h hp)
          (ListRelPerm.refl Perm.refl (preLieGrafts s t)))
        (ListRelPerm.map
          (fun h => node_cons_perm_of_node_perm (Perm.refl t) h) ih)
  | _, _, .swap t u ts => by
      rw [preLieGraftsList_cons, preLieGraftsList_cons,
        preLieGraftsList_cons, preLieGraftsList_cons]
      simp only [List.map_append, List.map_map, Function.comp_def]
      let A := (preLieGrafts s t).map fun t' => t' :: u :: ts
      let B := (preLieGrafts s u).map fun u' => t :: u' :: ts
      let C := (preLieGraftsList s ts).map fun vs => t :: u :: vs
      let D := (preLieGrafts s u).map fun u' => u' :: t :: ts
      let E := (preLieGrafts s t).map fun t' => u :: t' :: ts
      let F := (preLieGraftsList s ts).map fun vs => u :: t :: vs
      change ListRelPerm (fun vs ws => Perm (.node vs) (.node ws))
        (D ++ (E ++ F)) (A ++ (B ++ C))
      refine ListRelPerm.perm_left (xs' := E ++ (D ++ F)) ?_ ?_
      · simpa [D, E, F, List.append_assoc] using
          (List.Perm.append_right F (List.perm_append_comm : (D ++ E).Perm (E ++ D)))
      · exact ListRelPerm.append
          (ListRelPerm.map
            (fun h => Perm.node (List.Perm.swap _ _ _)
              (.cons h (.cons (Perm.refl u) (permForall2_refl ts))))
            (ListRelPerm.refl Perm.refl (preLieGrafts s t)))
          (ListRelPerm.append
            (ListRelPerm.map
              (fun h => Perm.node (List.Perm.swap _ _ _)
                (.cons (Perm.refl t) (.cons h (permForall2_refl ts))))
              (ListRelPerm.refl Perm.refl (preLieGrafts s u)))
            (ListRelPerm.map
              (fun h => Perm.node (List.Perm.swap _ _ _)
                (.cons (Perm.refl t) (.cons (Perm.refl u) h)))
              (ListRelPerm.refl (fun xs => permForall2_refl xs) (preLieGraftsList s ts))))
  | _, _, .trans h₁ h₂ => by
      have ih₁ := preLieGraftsList_listRelPerm_node_of_perm s h₁
      have ih₂ := preLieGraftsList_listRelPerm_node_of_perm s h₂
      exact ListRelPerm.trans
        (R := fun vs ws => Perm (.node vs) (.node ws))
        (fun {x y z} => Perm.trans) ih₁ ih₂

theorem preLieGraftsList_nodes_listRelPerm_of_perm (s : PTree)
    {ts us : List PTree} (h : ts.Perm us) :
    ListRelPerm Perm
      ((preLieGraftsList s ts).map PTree.node)
      ((preLieGraftsList s us).map PTree.node) :=
  ListRelPerm.map
    (fun {_ _} h => h)
    (preLieGraftsList_listRelPerm_node_of_perm s h)

theorem preLieGraftsList_listRelPerm_node_of_forall₂_perm_grafts (s : PTree) :
    ∀ {ts us : List PTree},
      List.Forall₂
          (fun t u =>
            Perm t u ∧ ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s u))
          ts us →
        ListRelPerm (fun vs ws => Perm (.node vs) (.node ws))
          (preLieGraftsList s ts) (preLieGraftsList s us)
  | [], [], .nil => by
      simp
      exact ListRelPerm.of_forall₂ .nil
  | _ :: _, _ :: _, .cons h htail => by
      rw [preLieGraftsList_cons, preLieGraftsList_cons]
      have htailPerm :
          List.Forall₂ Perm _ _ :=
        forall₂_perm_of_forall₂_perm_grafts htail
      exact ListRelPerm.append
        (ListRelPerm.map
          (fun hgraft => Perm.node (List.Perm.refl _)
            (.cons hgraft htailPerm))
          h.2)
        (ListRelPerm.map
          (fun hnode => node_cons_perm_of_node_perm h.1 hnode)
          (preLieGraftsList_listRelPerm_node_of_forall₂_perm_grafts s htail))

theorem preLieGraftsList_nodes_listRelPerm_of_forall₂_perm_grafts (s : PTree)
    {ts us : List PTree}
    (h :
      List.Forall₂
        (fun t u =>
          Perm t u ∧ ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s u))
        ts us) :
    ListRelPerm Perm
      ((preLieGraftsList s ts).map PTree.node)
      ((preLieGraftsList s us).map PTree.node) :=
  ListRelPerm.map
    (fun {_ _} h => h)
    (preLieGraftsList_listRelPerm_node_of_forall₂_perm_grafts s h)

theorem preLieGrafts_node_listRelPerm_of_list_perm
    (s : PTree) {ts us : List PTree} (hp : ts.Perm us) :
    ListRelPerm Perm (preLieGrafts s (.node ts)) (preLieGrafts s (.node us)) := by
  rw [preLieGrafts_node, preLieGrafts_node]
  refine ListRelPerm.cons ?_ ?_
  · exact .node (List.Perm.cons _ hp) (permForall2_refl (s :: us))
  · exact preLieGraftsList_nodes_listRelPerm_of_perm s hp

theorem preLieGrafts_node_listRelPerm_of_forall₂_perm_grafts
    (s : PTree) {ts us : List PTree}
    (h :
      List.Forall₂
        (fun t u =>
          Perm t u ∧ ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s u))
        ts us) :
    ListRelPerm Perm (preLieGrafts s (.node ts)) (preLieGrafts s (.node us)) := by
  rw [preLieGrafts_node, preLieGrafts_node]
  refine ListRelPerm.cons ?_ ?_
  · exact .node (List.Perm.refl _) (.cons (Perm.refl s)
      (forall₂_perm_of_forall₂_perm_grafts h))
  · exact preLieGraftsList_nodes_listRelPerm_of_forall₂_perm_grafts s h

mutual

theorem preLieGrafts_listRelPerm_right (s : PTree) :
    ∀ {t u : PTree}, Perm t u →
      ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s u)
  | .node ts, .node us, Perm.node (ts1' := ts') hp hf => by
      have hleft :
          ListRelPerm Perm (preLieGrafts s (.node ts)) (preLieGrafts s (.node ts')) :=
        preLieGrafts_node_listRelPerm_of_list_perm s hp
      have hright :
          ListRelPerm Perm (preLieGrafts s (.node ts')) (preLieGrafts s (.node us)) :=
        preLieGrafts_node_listRelPerm_of_forall₂_perm_grafts s
          (forall₂_perm_preLieGrafts_of_forall₂_perm s hf)
      exact ListRelPerm.trans (R := Perm) (fun {x y z} => Perm.trans) hleft hright

theorem forall₂_perm_preLieGrafts_of_forall₂_perm (s : PTree) :
    ∀ {ts us : List PTree}, List.Forall₂ Perm ts us →
      List.Forall₂
        (fun t u =>
          Perm t u ∧ ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s u))
        ts us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h htail =>
      .cons ⟨h, preLieGrafts_listRelPerm_right s h⟩
        (forall₂_perm_preLieGrafts_of_forall₂_perm s htail)

end

theorem preLieGrafts_map_ofPTree_perm_right (s : PTree) {t t' : PTree}
    (ht : Perm t t') :
    ((preLieGrafts s t).map RootedTree.ofPTree).Perm
      ((preLieGrafts s t').map RootedTree.ofPTree) :=
  ListRelPerm.map_eq_perm
    (fun h => RootedTree.ofPTree_eq_iff.2 h)
    (preLieGrafts_listRelPerm_right s ht)

theorem preLieGraftsList_map_node_ofPTree_perm_right
    (s : PTree) {ts us : List PTree} (h : ts.Perm us) :
    ((preLieGraftsList s ts).map fun vs => RootedTree.ofPTree (.node vs)).Perm
      ((preLieGraftsList s us).map fun vs => RootedTree.ofPTree (.node vs)) :=
  ListRelPerm.map_eq_perm
    (fun hnode => RootedTree.ofPTree_eq_iff.2 hnode)
    (preLieGraftsList_listRelPerm_node_of_perm s h)

end PTree

namespace PLTree

open HopfAlgebras.PLTree

variable {α : Type u} {β : Type v}

mutual

/-- All labelled planar trees obtained by grafting `s` at one vertex of `t`. -/
def preLieGrafts (s : PLTree α) : PLTree α → List (PLTree α)
  | .node a ts => .node a (s :: ts) :: (preLieGraftsList s ts).map (PLTree.node a)

/-- Child-list replacements induced by labelled pre-Lie grafting. -/
def preLieGraftsList (s : PLTree α) : List (PLTree α) → List (List (PLTree α))
  | [] => []
  | t :: ts =>
      ((preLieGrafts s t).map fun t' => t' :: ts) ++
        ((preLieGraftsList s ts).map fun us => t :: us)

end

@[simp]
theorem preLieGrafts_node (s : PLTree α) (a : α) (ts : List (PLTree α)) :
    preLieGrafts s (.node a ts) =
      .node a (s :: ts) :: (preLieGraftsList s ts).map (PLTree.node a) :=
  rfl

@[simp]
theorem preLieGraftsList_nil (s : PLTree α) :
    preLieGraftsList s [] = [] :=
  rfl

@[simp]
theorem preLieGraftsList_cons (s t : PLTree α) (ts : List (PLTree α)) :
    preLieGraftsList s (t :: ts) =
      ((preLieGrafts s t).map fun t' => t' :: ts) ++
        ((preLieGraftsList s ts).map fun us => t :: us) :=
  rfl

mutual

theorem length_preLieGrafts (s : PLTree α) :
    ∀ t : PLTree α, (preLieGrafts s t).length = order t
  | .node _ ts => by
      rw [preLieGrafts_node, List.length_cons, List.length_map,
        length_preLieGraftsList s ts, order_node]
      omega

theorem length_preLieGraftsList (s : PLTree α) :
    ∀ ts : List (PLTree α), (preLieGraftsList s ts).length = orderList ts
  | [] => by
      simp
  | t :: ts => by
      rw [preLieGraftsList_cons, List.length_append, List.length_map, List.length_map,
        length_preLieGrafts s t, length_preLieGraftsList s ts, orderList_cons]

end

mutual

theorem order_of_mem_preLieGrafts (s : PLTree α) :
    ∀ {t u : PLTree α}, u ∈ preLieGrafts s t → order u = order s + order t
  | .node _ ts, u, hu => by
      simp only [preLieGrafts_node, List.mem_cons, List.mem_map] at hu
      rcases hu with hu | ⟨us, hus, hu⟩
      · cases hu
        simp [order_node]
        omega
      · cases hu
        rw [order_node, order_of_mem_preLieGraftsList s hus, order_node]
        omega

theorem order_of_mem_preLieGraftsList (s : PLTree α) :
    ∀ {ts us : List (PLTree α)},
      us ∈ preLieGraftsList s ts → orderList us = order s + orderList ts
  | [], us, hus => by
      simp at hus
  | t :: ts, us, hus => by
      simp only [preLieGraftsList_cons, List.mem_append, List.mem_map] at hus
      rcases hus with ⟨u, hu, hus⟩ | ⟨vs, hvs, hus⟩
      · cases hus
        rw [orderList_cons, order_of_mem_preLieGrafts s hu, orderList_cons]
        omega
      · cases hus
        rw [orderList_cons, order_of_mem_preLieGraftsList s hvs, orderList_cons]
        omega

end

mutual

theorem preLieGrafts_listRelPerm_left {s s' : PLTree α} (hs : Perm s s') :
    ∀ t : PLTree α, PTree.ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s' t)
  | .node a ts => by
      rw [preLieGrafts_node, preLieGrafts_node]
      refine PTree.ListRelPerm.cons ?_ ?_
      · exact .node (List.Perm.refl _) (.cons hs (permForall₂_refl ts))
      · exact PTree.ListRelPerm.map
          (fun h => Perm.node (List.Perm.refl _) h)
          (preLieGraftsList_listRelPerm_left hs ts)

theorem preLieGraftsList_listRelPerm_left {s s' : PLTree α} (hs : Perm s s') :
    ∀ ts : List (PLTree α),
      PTree.ListRelPerm (List.Forall₂ Perm)
        (preLieGraftsList s ts) (preLieGraftsList s' ts)
  | [] => by
      simp
      exact PTree.ListRelPerm.of_forall₂ .nil
  | t :: ts => by
      rw [preLieGraftsList_cons, preLieGraftsList_cons]
      exact PTree.ListRelPerm.append
        (PTree.ListRelPerm.map
          (fun h => List.Forall₂.cons h (permForall₂_refl ts))
          (preLieGrafts_listRelPerm_left hs t))
        (PTree.ListRelPerm.map
          (fun h => List.Forall₂.cons (Perm.refl t) h)
          (preLieGraftsList_listRelPerm_left hs ts))

end

theorem preLieGrafts_map_ofPLTree_perm_left {s s' : PLTree α} (hs : Perm s s')
    (t : PLTree α) :
    ((preLieGrafts s t).map LRootedTree.ofPLTree).Perm
      ((preLieGrafts s' t).map LRootedTree.ofPLTree) :=
  PTree.ListRelPerm.map_eq_perm
    (fun h => LRootedTree.ofPLTree_eq_iff.2 h)
    (preLieGrafts_listRelPerm_left hs t)

theorem preLieGraftsList_map_ofPLTree_perm_left {s s' : PLTree α} (hs : Perm s s')
    (ts : List (PLTree α)) :
    ((preLieGraftsList s ts).map fun us => us.map LRootedTree.ofPLTree).Perm
      ((preLieGraftsList s' ts).map fun us => us.map LRootedTree.ofPLTree) :=
  PTree.ListRelPerm.map_eq_perm
    (fun h => LRootedTree.map_ofPLTree_eq_of_forall₂_perm h)
    (preLieGraftsList_listRelPerm_left hs ts)

private theorem node_cons_perm_of_list_perm {a : α} {x y : PLTree α}
    {ts us : List (PLTree α)} (hxy : Perm x y) (hp : ts.Perm us) :
    Perm (.node a (x :: ts)) (.node a (y :: us)) :=
  .node (List.Perm.cons _ hp) (.cons hxy (permForall₂_refl us))

private theorem node_cons_perm_of_node_perm {a : α} {t u : PLTree α}
    {vs ws : List (PLTree α)} (htu : Perm t u)
    (h : Perm (.node a vs) (.node a ws)) :
    Perm (.node a (t :: vs)) (.node a (u :: ws)) := by
  cases h with
  | node hp hf =>
      exact .node (List.Perm.cons _ hp) (.cons htu hf)

private theorem forall₂_perm_of_forall₂_perm_grafts
    {P : PLTree α → PLTree α → Prop} :
    ∀ {ts us : List (PLTree α)},
      List.Forall₂ (fun t u => Perm t u ∧ P t u) ts us →
        List.Forall₂ Perm ts us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h htail =>
      .cons h.1 (forall₂_perm_of_forall₂_perm_grafts htail)

theorem preLieGraftsList_listRelPerm_node_of_perm (s : PLTree α) (a : α) :
    ∀ {ts us : List (PLTree α)}, ts.Perm us →
      PTree.ListRelPerm (fun vs ws => Perm (.node a vs) (.node a ws))
        (preLieGraftsList s ts) (preLieGraftsList s us)
  | _, _, .nil => by
      simp
      exact PTree.ListRelPerm.of_forall₂ .nil
  | _, _, .cons t hp => by
      have ih := preLieGraftsList_listRelPerm_node_of_perm s a hp
      rw [preLieGraftsList_cons, preLieGraftsList_cons]
      exact PTree.ListRelPerm.append
        (PTree.ListRelPerm.map
          (fun h => node_cons_perm_of_list_perm h hp)
          (PTree.ListRelPerm.refl Perm.refl (preLieGrafts s t)))
        (PTree.ListRelPerm.map
          (fun h => node_cons_perm_of_node_perm (Perm.refl t) h) ih)
  | _, _, .swap t u ts => by
      rw [preLieGraftsList_cons, preLieGraftsList_cons,
        preLieGraftsList_cons, preLieGraftsList_cons]
      simp only [List.map_append, List.map_map, Function.comp_def]
      let A := (preLieGrafts s t).map fun t' => t' :: u :: ts
      let B := (preLieGrafts s u).map fun u' => t :: u' :: ts
      let C := (preLieGraftsList s ts).map fun vs => t :: u :: vs
      let D := (preLieGrafts s u).map fun u' => u' :: t :: ts
      let E := (preLieGrafts s t).map fun t' => u :: t' :: ts
      let F := (preLieGraftsList s ts).map fun vs => u :: t :: vs
      change PTree.ListRelPerm (fun vs ws => Perm (.node a vs) (.node a ws))
        (D ++ (E ++ F)) (A ++ (B ++ C))
      refine PTree.ListRelPerm.perm_left (xs' := E ++ (D ++ F)) ?_ ?_
      · simpa [D, E, F, List.append_assoc] using
          (List.Perm.append_right F (List.perm_append_comm : (D ++ E).Perm (E ++ D)))
      · exact PTree.ListRelPerm.append
          (PTree.ListRelPerm.map
            (fun h => Perm.node (List.Perm.swap _ _ _)
              (.cons h (.cons (Perm.refl u) (permForall₂_refl ts))))
            (PTree.ListRelPerm.refl Perm.refl (preLieGrafts s t)))
          (PTree.ListRelPerm.append
            (PTree.ListRelPerm.map
              (fun h => Perm.node (List.Perm.swap _ _ _)
                (.cons (Perm.refl t) (.cons h (permForall₂_refl ts))))
              (PTree.ListRelPerm.refl Perm.refl (preLieGrafts s u)))
            (PTree.ListRelPerm.map
              (fun h => Perm.node (List.Perm.swap _ _ _)
                (.cons (Perm.refl t) (.cons (Perm.refl u) h)))
              (PTree.ListRelPerm.refl (fun xs => permForall₂_refl xs) (preLieGraftsList s ts))))
  | _, _, .trans h₁ h₂ => by
      have ih₁ := preLieGraftsList_listRelPerm_node_of_perm s a h₁
      have ih₂ := preLieGraftsList_listRelPerm_node_of_perm s a h₂
      exact PTree.ListRelPerm.trans
        (R := fun vs ws => Perm (.node a vs) (.node a ws))
        (fun {x y z} => Perm.trans) ih₁ ih₂

theorem preLieGraftsList_nodes_listRelPerm_of_perm (s : PLTree α) (a : α)
    {ts us : List (PLTree α)} (h : ts.Perm us) :
    PTree.ListRelPerm Perm
      ((preLieGraftsList s ts).map (PLTree.node a))
      ((preLieGraftsList s us).map (PLTree.node a)) :=
  PTree.ListRelPerm.map
    (fun {_ _} h => h)
    (preLieGraftsList_listRelPerm_node_of_perm s a h)

theorem preLieGraftsList_listRelPerm_node_of_forall₂_perm_grafts
    (s : PLTree α) (a : α) :
    ∀ {ts us : List (PLTree α)},
      List.Forall₂
          (fun t u =>
            Perm t u ∧ PTree.ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s u))
          ts us →
        PTree.ListRelPerm (fun vs ws => Perm (.node a vs) (.node a ws))
          (preLieGraftsList s ts) (preLieGraftsList s us)
  | [], [], .nil => by
      simp
      exact PTree.ListRelPerm.of_forall₂ .nil
  | _ :: _, _ :: _, .cons h htail => by
      rw [preLieGraftsList_cons, preLieGraftsList_cons]
      have htailPerm :
          List.Forall₂ Perm _ _ :=
        forall₂_perm_of_forall₂_perm_grafts htail
      exact PTree.ListRelPerm.append
        (PTree.ListRelPerm.map
          (fun hgraft => Perm.node (List.Perm.refl _)
            (.cons hgraft htailPerm))
          h.2)
        (PTree.ListRelPerm.map
          (fun hnode => node_cons_perm_of_node_perm h.1 hnode)
          (preLieGraftsList_listRelPerm_node_of_forall₂_perm_grafts s a htail))

theorem preLieGraftsList_nodes_listRelPerm_of_forall₂_perm_grafts
    (s : PLTree α) (a : α) {ts us : List (PLTree α)}
    (h :
      List.Forall₂
        (fun t u =>
          Perm t u ∧ PTree.ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s u))
        ts us) :
    PTree.ListRelPerm Perm
      ((preLieGraftsList s ts).map (PLTree.node a))
      ((preLieGraftsList s us).map (PLTree.node a)) :=
  PTree.ListRelPerm.map
    (fun {_ _} h => h)
    (preLieGraftsList_listRelPerm_node_of_forall₂_perm_grafts s a h)

theorem preLieGrafts_node_listRelPerm_of_list_perm
    (s : PLTree α) (a : α) {ts us : List (PLTree α)} (hp : ts.Perm us) :
    PTree.ListRelPerm Perm (preLieGrafts s (.node a ts)) (preLieGrafts s (.node a us)) := by
  rw [preLieGrafts_node, preLieGrafts_node]
  refine PTree.ListRelPerm.cons ?_ ?_
  · exact .node (List.Perm.cons _ hp) (permForall₂_refl (s :: us))
  · exact preLieGraftsList_nodes_listRelPerm_of_perm s a hp

theorem preLieGrafts_node_listRelPerm_of_forall₂_perm_grafts
    (s : PLTree α) (a : α) {ts us : List (PLTree α)}
    (h :
      List.Forall₂
        (fun t u =>
          Perm t u ∧ PTree.ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s u))
        ts us) :
    PTree.ListRelPerm Perm (preLieGrafts s (.node a ts)) (preLieGrafts s (.node a us)) := by
  rw [preLieGrafts_node, preLieGrafts_node]
  refine PTree.ListRelPerm.cons ?_ ?_
  · exact .node (List.Perm.refl _) (.cons (Perm.refl s)
      (forall₂_perm_of_forall₂_perm_grafts h))
  · exact preLieGraftsList_nodes_listRelPerm_of_forall₂_perm_grafts s a h

mutual

theorem preLieGrafts_listRelPerm_right (s : PLTree α) :
    ∀ {t u : PLTree α}, Perm t u →
      PTree.ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s u)
  | .node a ts, .node _ us, Perm.node (ts' := ts') hp hf => by
      have hleft :
          PTree.ListRelPerm Perm
            (preLieGrafts s (.node a ts)) (preLieGrafts s (.node a ts')) :=
        preLieGrafts_node_listRelPerm_of_list_perm s a hp
      have hright :
          PTree.ListRelPerm Perm
            (preLieGrafts s (.node a ts')) (preLieGrafts s (.node a us)) :=
        preLieGrafts_node_listRelPerm_of_forall₂_perm_grafts s a
          (forall₂_perm_preLieGrafts_of_forall₂_perm s hf)
      exact PTree.ListRelPerm.trans (R := Perm) (fun {x y z} => Perm.trans) hleft hright

theorem forall₂_perm_preLieGrafts_of_forall₂_perm (s : PLTree α) :
    ∀ {ts us : List (PLTree α)}, List.Forall₂ Perm ts us →
      List.Forall₂
        (fun t u =>
          Perm t u ∧ PTree.ListRelPerm Perm (preLieGrafts s t) (preLieGrafts s u))
        ts us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h htail =>
      .cons ⟨h, preLieGrafts_listRelPerm_right s h⟩
        (forall₂_perm_preLieGrafts_of_forall₂_perm s htail)

end

theorem preLieGrafts_map_ofPLTree_perm_right (s : PLTree α) {t t' : PLTree α}
    (ht : Perm t t') :
    ((preLieGrafts s t).map LRootedTree.ofPLTree).Perm
      ((preLieGrafts s t').map LRootedTree.ofPLTree) :=
  PTree.ListRelPerm.map_eq_perm
    (fun h => LRootedTree.ofPLTree_eq_iff.2 h)
    (preLieGrafts_listRelPerm_right s ht)

theorem preLieGraftsList_map_node_ofPLTree_perm_right
    (s : PLTree α) (a : α) {ts us : List (PLTree α)} (h : ts.Perm us) :
    ((preLieGraftsList s ts).map fun vs => LRootedTree.ofPLTree (.node a vs)).Perm
      ((preLieGraftsList s us).map fun vs => LRootedTree.ofPLTree (.node a vs)) :=
  PTree.ListRelPerm.map_eq_perm
    (fun hnode => LRootedTree.ofPLTree_eq_iff.2 hnode)
    (preLieGraftsList_listRelPerm_node_of_perm s a h)

mutual

@[simp]
theorem erase_preLieGrafts (s : PLTree α) :
    ∀ t : PLTree α,
      (preLieGrafts s t).map erase = PTree.preLieGrafts (erase s) (erase t)
  | .node _ ts => by
      simp only [preLieGrafts_node, erase_node, List.map_cons]
      rw [PTree.preLieGrafts_node]
      have htail :=
        congrArg (List.map PTree.node) (erase_preLieGraftsList s ts)
      simpa [List.map_map, Function.comp_def, erase] using htail

@[simp]
theorem erase_preLieGraftsList (s : PLTree α) :
    ∀ ts : List (PLTree α),
      (preLieGraftsList s ts).map (fun us => us.map erase) =
        PTree.preLieGraftsList (erase s) (ts.map erase)
  | [] => by
      simp
  | t :: ts => by
      simp only [preLieGraftsList_cons, PTree.preLieGraftsList_cons, List.map_cons,
        List.map_append]
      have hleft :=
        congrArg (List.map fun t' => t' :: ts.map erase) (erase_preLieGrafts s t)
      have hright :=
        congrArg (List.map fun us => erase t :: us) (erase_preLieGraftsList s ts)
      simpa [List.map_map, Function.comp_def] using congrArg₂ List.append hleft hright

end

mutual

@[simp]
theorem map_preLieGrafts (f : α → β) (s : PLTree α) :
    ∀ t : PLTree α,
      (preLieGrafts s t).map (map f) = preLieGrafts (map f s) (map f t)
  | .node a ts => by
      rw [preLieGrafts_node, map_node, preLieGrafts_node]
      have htail :=
        congrArg (List.map (PLTree.node (f a)))
          (map_preLieGraftsList f s ts)
      simpa [List.map_map, Function.comp_def, map_node] using htail

@[simp]
theorem map_preLieGraftsList (f : α → β) (s : PLTree α) :
    ∀ ts : List (PLTree α),
      (preLieGraftsList s ts).map (fun us => us.map (map f)) =
        preLieGraftsList (map f s) (ts.map (map f))
  | [] => by
      simp
  | t :: ts => by
      simp only [preLieGraftsList_cons, List.map_cons, List.map_append]
      have hleft :=
        congrArg (List.map fun t' => t' :: ts.map (map f)) (map_preLieGrafts f s t)
      have hright :=
        congrArg (List.map fun us => map f t :: us) (map_preLieGraftsList f s ts)
      simpa [List.map_map, Function.comp_def] using congrArg₂ List.append hleft hright

end

mutual

@[simp]
theorem constLabel_preLieGrafts (a : α) (s : PTree) :
    ∀ t : PTree,
      (PTree.preLieGrafts s t).map (constLabel a) =
        preLieGrafts (constLabel a s) (constLabel a t)
  | .node ts => by
      rw [PTree.preLieGrafts_node, constLabel_node, preLieGrafts_node]
      have htail :=
        congrArg (List.map (PLTree.node a))
          (constLabel_preLieGraftsList a s ts)
      simpa [List.map_map, Function.comp_def, constLabel_node] using htail

@[simp]
theorem constLabel_preLieGraftsList (a : α) (s : PTree) :
    ∀ ts : List PTree,
      (PTree.preLieGraftsList s ts).map (fun us => us.map (constLabel a)) =
        preLieGraftsList (constLabel a s) (ts.map (constLabel a))
  | [] => by
      simp
  | t :: ts => by
      simp only [PTree.preLieGraftsList_cons, preLieGraftsList_cons, List.map_cons,
        List.map_append]
      have hleft :=
        congrArg (List.map fun t' => t' :: ts.map (constLabel a))
          (constLabel_preLieGrafts a s t)
      have hright :=
        congrArg (List.map fun us => constLabel a t :: us)
          (constLabel_preLieGraftsList a s ts)
      simpa [List.map_map, Function.comp_def] using congrArg₂ List.append hleft hright

end

end PLTree

end BSeries
