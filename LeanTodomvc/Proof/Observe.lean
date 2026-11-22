import LeanTodomvc.Proof.Handlers
import LeanTodomvc.Proof.JsonRT
import LeanTodomvc.Spec

/-!
# What the user observes in a represented state
-/

namespace TodoMVC.Proof
open JS DOM

/-- The subtree of a block is the block, in order. -/
theorem subtree_block {w : World} {b : Nat} {t : TodoR} {ed : Bool} {par : Option Nat}
    (h : Block w b t ed par) (G : Nat) :
    World.subtree.go w (G + 4) b = List.range' b (blockSize t ed) := by
  obtain ⟨v2, ve, hb⟩ := h.2
  have hs : 5 ≤ blockSize t ed := by simp only [blockSize, dOff]; split <;> split <;> omega
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  have h4 := hb 4 (by omega)
  simp only [Nat.add_zero] at h0
  by_cases ht : t.title = "" <;> cases ed
  · simp [World.subtree.go, h0, h1, h2, h3, h4, blockNode, dOff, ht, blockSize, List.range'_succ, Nat.add_assoc]
  · have h5 := hb 5 (by simp [blockSize, dOff, ht])
    simp [World.subtree.go, h0, h1, h2, h3, h4, h5, blockNode, dOff, ht, blockSize, List.range'_succ, Nat.add_assoc]
  · have h5 := hb 5 (by simp [blockSize, dOff, ht])
    simp [World.subtree.go, h0, h1, h2, h3, h4, h5, blockNode, dOff, ht, blockSize, List.range'_succ, Nat.add_assoc]
  · have h5 := hb 5 (by simp [blockSize, dOff, ht])
    have h6 := hb 6 (by simp [blockSize, dOff, ht])
    simp [World.subtree.go, h0, h1, h2, h3, h4, h5, h6, blockNode, dOff, ht, blockSize, List.range'_succ, Nat.add_assoc]

theorem documentNodes_eq {m : Model} {w : World} {v5 v7 : String} {lis : List Nat} {c n : Nat}
    (hsz : 25 ≤ w.dom.size) (hst : ∀ k < 25, w.node k = staticNode m v5 v7 lis [c, c + 2] k)
    (hc : Counter w c n) :
    w.documentNodes = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] ++ lis.flatMap (World.subtree.go w (w.dom.size - 8 + 4)) ++
      [11, 12, c, c + 1, c + 2, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] := by
  obtain ⟨_, hc0, hc1, hc2⟩ := hc
  have : w.dom.size = (w.dom.size - 8) + 8 := by omega
  rw [World.documentNodes, World.subtree, this]
  generalize w.dom.size - 8 = G
  simp [World.subtree.go, hst, staticNode, staticNodeD, Model.dyn, hc0, hc1, hc2]

theorem mem_blocks {w : World} {P : Node → Prop}
    (hP : ∀ b t ed par v2 ve i, i < blockSize t ed → P (blockNode b t ed par v2 ve i)) (G : Nat) (ed : TodoR → Bool) :
    ∀ {lis : List Nat} {ts : List TodoR}, List.Forall₂ (fun b t => Block w b t (ed t) (some nList)) lis ts →
      ∀ x ∈ lis.flatMap (World.subtree.go w (G + 4)), P (w.node x)
  | _, _, .nil => by simp
  | _, _, .cons (a := b) (b := t) hb hr => by
    intro x hx
    simp only [List.flatMap_cons, List.mem_append, subtree_block hb, List.mem_range'] at hx
    rcases hx with ⟨i, hi, rfl⟩ | hx
    · obtain ⟨v2, ve, hn⟩ := hb.2
      simp only [Nat.one_mul]; rw [hn i hi]; exact hP _ _ _ _ _ _ _ hi
    · exact mem_blocks hP G ed hr x hx

theorem blockNode_id (b : Nat) (t : TodoR) (ed : Bool) (par : Option Nat) (v2 ve : String) (i : Nat) :
    (blockNode b t ed par v2 ve i).id = "" := by
  unfold blockNode; split <;> (try split_ifs) <;> rfl

def blockClasses : List String := ["completed", "editing", "view", "toggle", "destroy", "edit"]

theorem blockNode_classes (b : Nat) (t : TodoR) (ed : Bool) (par : Option Nat) (v2 ve : String) (i : Nat) :
    ∀ c ∈ (blockNode b t ed par v2 ve i).classes, c ∈ blockClasses := by
  unfold blockNode; split
  · simp only [Node.classes, liClass]
    cases t.completed <;> cases ed <;> simp [splitSpaces, blockClasses]
  all_goals (try split_ifs) <;> simp [Node.classes, splitSpaces, blockClasses, show (default : Node).className = "" from rfl]

/-- `DomRep`, unpacked. -/
structure DocRep (m : Model) (w : World) (v5 v7 : String) (lis : List Nat) (c : Nat) : Prop where
  size : 25 ≤ w.dom.size
  static : ∀ k < 25, w.node k = staticNode m v5 v7 lis [c, c + 2] k
  blocks : List.Forall₂ (fun b t => Block w b t (m.editingId = t.id) (some nList)) lis m.shown
  counter : Counter w c m.activeCount

theorem DomRep.doc {m : Model} {w : World} (h : DomRep m w) : ∃ v5 v7 lis c, DocRep m w v5 v7 lis c := by
  obtain ⟨v5, v7, lis, c, hst, hb, hc⟩ := h.static
  exact ⟨v5, v7, lis, c, h.size, hst, hb, hc⟩

theorem find?_doc {p : Nat → Bool} (pre M suf : List Nat) (hM : ∀ x ∈ M, p x = false) :
    (pre ++ M ++ suf).find? p = (pre.find? p).or (suf.find? p) := by
  have hn : M.find? p = none := List.find?_eq_none.2 (fun x hx => by simp [hM x hx])
  simp [List.find?_append, hn]

theorem classes_selectedIf (b : Bool) :
    splitSpaces (selectedIf b).toList [] = if b then ["selected"] else [] := by
  cases b <;> simp [selectedIf, splitSpaces]

section
variable {m : Model} {w : World} {v5 v7 : String} {lis : List Nat} {c : Nat} (h : DocRep m w v5 v7 lis c)
include h

theorem DocRep.findClass (cls : String) (hcls : cls ∉ blockClasses) :
    w.documentNodes.find? (fun n => (w.node n).hasClass cls) =
      (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List Nat).find? (fun n => (w.node n).hasClass cls)).or
      (([11, 12, c, c + 1, c + 2, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat).find?
        (fun n => (w.node n).hasClass cls)) := by
  rw [documentNodes_eq h.size h.static h.counter, find?_doc]
  have := mem_blocks (P := fun nd => nd.hasClass cls = false)
    (fun b t ed par v2 ve i _ => by
      have := blockNode_classes b t ed par v2 ve i
      simp only [Node.hasClass, List.contains_eq_mem, decide_eq_false_iff_not]
      exact fun hm => hcls (this _ hm)) (w.dom.size - 8) _ h.blocks
  exact this

theorem DocRep.findId (id : String) :
    w.documentNodes.find? (fun n => (w.node n).id == id) =
      (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List Nat).find? (fun n => (w.node n).id == id)).or
      (([11, 12, c, c + 1, c + 2, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List Nat).find?
        (fun n => (w.node n).id == id)) := by
  by_cases hid : id = ""
  · subst hid
    have h0 := h.static 0 (by omega)
    rw [documentNodes_eq h.size h.static h.counter]
    simp [h0, staticNode, staticNodeD]
  rw [documentNodes_eq h.size h.static h.counter, find?_doc]
  have := mem_blocks (P := fun nd => (nd.id == id) = false)
    (fun b t ed par v2 ve i _ => by simp [blockNode_id, Ne.symm hid]) (w.dom.size - 8) _ h.blocks
  exact this

theorem DocRep.q_list : w.querySelector ".todo-list" = some nList := by
  have : w.querySelector ".todo-list" = w.documentNodes.find? (fun n => (w.node n).hasClass "todo-list") := by
    simp [World.querySelector]
  rw [this, h.findClass "todo-list" (by decide)]
  simp [h.static, staticNode, staticNodeD, Node.hasClass, Node.classes, splitSpaces, h.counter.2.1,
    h.counter.2.2.1, h.counter.2.2.2, classes_selectedIf, Model.dyn, apply_ite]

theorem DocRep.q_main : w.querySelector ".main" = some nMain := by
  have : w.querySelector ".main" = w.documentNodes.find? (fun n => (w.node n).hasClass "main") := by
    simp [World.querySelector]
  rw [this, h.findClass "main" (by decide)]
  simp [h.static, staticNode, staticNodeD, Node.hasClass, Node.classes, splitSpaces, h.counter.2.1,
    h.counter.2.2.1, h.counter.2.2.2, classes_selectedIf, Model.dyn, apply_ite]

theorem DocRep.q_footer : w.querySelector ".footer" = some nFooter := by
  have : w.querySelector ".footer" = w.documentNodes.find? (fun n => (w.node n).hasClass "footer") := by
    simp [World.querySelector]
  rw [this, h.findClass "footer" (by decide)]
  simp [h.static, staticNode, staticNodeD, Node.hasClass, Node.classes, splitSpaces, h.counter.2.1,
    h.counter.2.2.1, h.counter.2.2.2, classes_selectedIf, Model.dyn, apply_ite]

theorem DocRep.q_count : w.querySelector ".todo-count" = some nCount := by
  have : w.querySelector ".todo-count" = w.documentNodes.find? (fun n => (w.node n).hasClass "todo-count") := by
    simp [World.querySelector]
  rw [this, h.findClass "todo-count" (by decide)]
  simp [h.static, staticNode, staticNodeD, Node.hasClass, Node.classes, splitSpaces, h.counter.2.1,
    h.counter.2.2.1, h.counter.2.2.2, classes_selectedIf, Model.dyn, apply_ite]

theorem DocRep.q_clear : w.querySelector ".clear-completed" = some nClear := by
  have : w.querySelector ".clear-completed" = w.documentNodes.find? (fun n => (w.node n).hasClass "clear-completed") := by
    simp [World.querySelector]
  rw [this, h.findClass "clear-completed" (by decide)]
  simp [h.static, staticNode, staticNodeD, Node.hasClass, Node.classes, splitSpaces, h.counter.2.1,
    h.counter.2.2.1, h.counter.2.2.2, classes_selectedIf, Model.dyn, apply_ite]

theorem DocRep.q_toggleAll : w.querySelector ".toggle-all" = some nToggleAll := by
  have : w.querySelector ".toggle-all" = w.documentNodes.find? (fun n => (w.node n).hasClass "toggle-all") := by
    simp [World.querySelector]
  rw [this, h.findClass "toggle-all" (by decide)]
  simp [h.static, staticNode, staticNodeD, Node.hasClass, Node.classes, splitSpaces, h.counter.2.1,
    h.counter.2.2.1, h.counter.2.2.2, classes_selectedIf, Model.dyn, apply_ite]

theorem DocRep.q_newTodo : w.querySelector ".new-todo" = some nNewTodo := by
  have : w.querySelector ".new-todo" = w.documentNodes.find? (fun n => (w.node n).hasClass "new-todo") := by
    simp [World.querySelector]
  rw [this, h.findClass "new-todo" (by decide)]
  simp [h.static, staticNode, staticNodeD, Node.hasClass, Node.classes, splitSpaces, h.counter.2.1,
    h.counter.2.2.1, h.counter.2.2.2, classes_selectedIf, Model.dyn, apply_ite]

theorem DocRep.q_filterAll : w.querySelector "#filter-all" = some nFilterAll := by
  have : w.querySelector "#filter-all" = w.documentNodes.find? (fun n => (w.node n).id == "filter-all") := by
    simp [World.querySelector]
  rw [this, h.findId "filter-all"]
  simp [h.static, staticNode, staticNodeD, h.counter.2.1, h.counter.2.2.1, h.counter.2.2.2]

theorem DocRep.q_filterActive : w.querySelector "#filter-active" = some nFilterActive := by
  have : w.querySelector "#filter-active" = w.documentNodes.find? (fun n => (w.node n).id == "filter-active") := by
    simp [World.querySelector]
  rw [this, h.findId "filter-active"]
  simp [h.static, staticNode, staticNodeD, h.counter.2.1, h.counter.2.2.1, h.counter.2.2.2]

theorem DocRep.q_filterCompleted : w.querySelector "#filter-completed" = some nFilterCompleted := by
  have : w.querySelector "#filter-completed" = w.documentNodes.find? (fun n => (w.node n).id == "filter-completed") := by
    simp [World.querySelector]
  rw [this, h.findId "filter-completed"]
  simp [h.static, staticNode, staticNodeD, h.counter.2.1, h.counter.2.2.1, h.counter.2.2.2]


theorem DocRep.size8 : ∃ G, w.dom.size = G + 8 := ⟨w.dom.size - 8, by have := h.size; omega⟩

theorem DocRep.visible_main : w.visible nMain = !m.todos.isEmpty := by
  obtain ⟨G, hG⟩ := h.size8
  have h1 : 23 < G + 8 := by have := h.size; omega
  simp [h1, Nat.lt_of_le_of_lt (by decide : 11 ≤ 23) h1, Nat.lt_of_le_of_lt (by decide : 6 ≤ 23) h1, World.visible, World.attached, World.ancestors, hG, World.ancestors.go, h.static, staticNode, staticNodeD, nMain, nFooter, nClear,
    Model.dyn]

theorem DocRep.visible_footer : w.visible nFooter = !m.todos.isEmpty := by
  obtain ⟨G, hG⟩ := h.size8
  have h1 : 23 < G + 8 := by have := h.size; omega
  simp [h1, Nat.lt_of_le_of_lt (by decide : 11 ≤ 23) h1, Nat.lt_of_le_of_lt (by decide : 6 ≤ 23) h1, World.visible, World.attached, World.ancestors, hG, World.ancestors.go, h.static, staticNode, staticNodeD, nMain, nFooter, nClear,
    Model.dyn]

theorem DocRep.visible_clear : w.visible nClear = m.todos.any (·.completed) := by
  obtain ⟨G, hG⟩ := h.size8
  have h1 : 23 < G + 8 := by have := h.size; omega
  simp [h1, Nat.lt_of_le_of_lt (by decide : 11 ≤ 23) h1, Nat.lt_of_le_of_lt (by decide : 6 ≤ 23) h1, World.visible, World.attached, World.ancestors, hG, World.ancestors.go, h.static, staticNode, staticNodeD, nMain, nFooter, nClear,
    Model.dyn]
  cases m.todos <;> simp

theorem DocRep.text_count : w.textContent nCount = toString m.activeCount ++ countLabel m.activeCount := by
  obtain ⟨G, hG⟩ := h.size8
  obtain ⟨_, hc0, hc1, hc2⟩ := h.counter
  simp [nCount, World.textContent, World.subtree, hG, World.subtree.go, h.static, staticNode, staticNodeD, Model.dyn,
    hc0, hc1, hc2, String.join_cons]

theorem DocRep.checked_toggleAll : (w.node nToggleAll).checked = m.allDone := by
  simp [nToggleAll, h.static, staticNode, staticNodeD, Model.dyn]

theorem DocRep.items : (w.node nList).children = lis := by
  simp [nList, h.static, staticNode, staticNodeD, Model.dyn]

end

def TodoR.toTodo (t : TodoR) : Todo := ⟨t.title, t.completed⟩

theorem completed_mem_liClass (t : TodoR) (ed : Bool) :
    "completed" ∈ splitSpaces (liClass t ed).toList [] ↔ t.completed = true := by
  cases ht : t.completed <;> cases ed <;> simp [liClass, ht, splitSpaces]

theorem editing_mem_liClass (t : TodoR) (ed : Bool) :
    "editing" ∈ splitSpaces (liClass t ed).toList [] ↔ ed = true := by
  cases ht : t.completed <;> cases ed <;> simp [liClass, ht, splitSpaces]

theorem itemTodo_block {s : State} {b : Nat} {t : TodoR} {ed : Bool} {par : Option Nat} (G : Nat)
    (hG : s.world.dom.size = G + 8) (hb : Block s.world b t ed par) :
    itemTodo s b = t.toTodo := by
  have hsub : ∀ k, World.subtree.go s.world (G + 8) k = World.subtree.go s.world ((G + 4) + 4) k := fun _ => rfl
  obtain ⟨v2, ve, hn⟩ := hb.2
  have hs : 5 ≤ blockSize t ed := by simp only [blockSize, dOff]; split <;> split <;> omega
  have h0 := hn 0 (by omega)
  have h1 := hn 1 (by omega)
  have h2 := hn 2 (by omega)
  have h3 := hn 3 (by omega)
  have h4 := hn 4 (by omega)
  simp only [Nat.add_zero] at h0
  obtain ⟨k, hk⟩ : ∃ k, blockSize t ed = k + 5 := ⟨blockSize t ed - 5, by omega⟩
  simp only [itemTodo, find, World.subtree, hG, hsub, subtree_block hb, hk, List.range'_succ]
  by_cases ht : t.title = ""
  · simp [h0, h1, h2, h3, blockNode, ht, World.textContent, World.subtree, hG, World.subtree.go,
      Node.hasClass, Node.classes, completed_mem_liClass, TodoR.toTodo]
  · simp [h0, h1, h2, h3, h4, blockNode, ht, World.textContent, World.subtree, hG, World.subtree.go,
      Node.hasClass, Node.classes, completed_mem_liClass, TodoR.toTodo]

theorem parseTodo_val (t : TodoR) : parseTodo t.val = some t.toTodo := by
  simp [parseTodo, TodoR.val, assocGet, TodoR.toTodo]

theorem mapM_parseTodo (ts : List TodoR) : (ts.map TodoR.val).mapM parseTodo = some (ts.map TodoR.toTodo) := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [parseTodo_val, ih]

theorem stored_rep {m : Model} {s : State} (h : Rep m s) : stored s = some (m.todos.map TodoR.toTodo) := by
  rcases h.storage with ⟨hs, ht⟩ | hs
  · simp [stored, hs, ht, assocGet]
  · have hp : Json.parse (Json.stringify (Value.arr (m.todos.map TodoR.val))) =
        some (.arr (m.todos.map TodoR.val)) := parse_stringify_todos m.todos h.model.nonneg
    have hg : assocGet s.world.storage STORAGE_KEY = some (Json.stringify (todosVal m.todos)) := by
      simp [hs, assocGet]
    simp only [stored, hg]
    rw [parse_stringify_todos m.todos h.model.nonneg]
    simp only [todosVal]
    exact mapM_parseTodo m.todos

theorem displayed_blocks {s : State} (G : Nat) (hG : s.world.dom.size = G + 8) (ed : TodoR → Bool) :
    ∀ {lis : List Nat} {ts : List TodoR}, List.Forall₂ (fun b t => Block s.world b t (ed t) (some nList)) lis ts →
      lis.map (itemTodo s) = ts.map TodoR.toTodo
  | _, _, .nil => rfl
  | _, _, .cons hb hr => by simp [itemTodo_block G hG hb, displayed_blocks G hG ed hr]

theorem filter_shows {m : Model} {s : State} (hh : s.world.hash = m.hash) (t : TodoR) :
    (filter s).shows t.toTodo = shows (filterStr m.hash) t := by
  simp only [filter, hh, filterStr, shows, TodoR.toTodo]
  split_ifs <;> simp_all [Filter.shows]

theorem editing_blocks {w : World} (ed : TodoR → Bool) :
    ∀ {lis : List Nat} {ts : List TodoR}, List.Forall₂ (fun b t => Block w b t (ed t) (some nList)) lis ts →
      (lis.filter fun li => (w.node li).hasClass "editing").length = (ts.filter ed).length
  | _, _, .nil => rfl
  | _, _, .cons (a := b) (b := t) hb hr => by
    obtain ⟨v2, ve, hn⟩ := hb.2
    have h0 := hn 0 (by simp only [blockSize, dOff]; split <;> split <;> omega)
    simp only [Nat.add_zero] at h0
    have ih := editing_blocks ed hr
    have hc : (blockNode b t (ed t) (some nList) v2 ve 0).hasClass "editing" = ed t := by
      cases he : ed t <;> simp [blockNode, Node.hasClass, Node.classes, editing_mem_liClass, he]
    rw [List.filter_cons, List.filter_cons, h0, hc]
    cases ed t <;> simp [ih]

theorem length_filter_id_le_one (ts : List TodoR) (hnd : (ts.map (·.id)).Nodup) (id : Int) :
    (ts.filter fun t => decide (id = t.id)).length ≤ 1 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    by_cases h : id = t.id
    · subst h
      simp [List.filter_cons]
      intro a ha he; exact hnd.1 ⟨a, ha, he.symm⟩
    · simp [List.filter_cons, h, ih hnd.2]

theorem invariant_of_rep {m : Model} {s : State} (h : Rep m s) : invariant s = true := by
  obtain ⟨v5, v7, lis, c, hd⟩ := h.dom.doc
  obtain ⟨G, hG⟩ := hd.size8
  have hst := stored_rep h
  have hdisp : displayed s = m.shown.map TodoR.toTodo := by
    simp only [displayed, items, q, hd.q_list, hd.items]
    exact displayed_blocks G hG _ hd.blocks
  have hshown : m.shown.map TodoR.toTodo = (m.todos.map TodoR.toTodo).filter (filter s).shows := by
    simp [Model.shown, List.filter_map, Function.comp_def, filter_shows h.hash]
  have hed : ((items s).filter fun li => (s.world.node li).hasClass "editing").length ≤ 1 := by
    simp only [items, q, hd.q_list, hd.items]
    rw [editing_blocks _ hd.blocks]
    exact length_filter_id_le_one _ (h.model.nodup.sublist (List.Sublist.map _ (List.filter_sublist))) _
  have hcomp : ∀ (p : Todo → Bool), (p ∘ TodoR.toTodo) = fun t => p ⟨t.title, t.completed⟩ := fun _ => rfl
  have i1 : noErrors s = true := by simp [noErrors, h.errors]
  have i2 : listMatchesStorage s = true := by simp [listMatchesStorage, hst, hdisp, hshown]
  have i3 : hiddenWhenEmpty s = true := by
    simp [hiddenWhenEmpty, hst, isVisible, q, hd.q_main, hd.q_footer, hd.visible_main, hd.visible_footer]
  have i4 : counterCorrect s = true := by
    have : (List.filter (fun x => !x.completed) (List.map TodoR.toTodo m.todos)).length = m.activeCount := by
      simp [Model.activeCount, List.filter_map, Function.comp_def, TodoR.toTodo]
    simp only [counterCorrect, hst, text, q, hd.q_count, hd.text_count, this, countLabel]
    simp
  have i5 : clearButtonCorrect s = true := by
    simp [clearButtonCorrect, hst, isVisible, q, hd.q_clear, hd.visible_clear, TodoR.toTodo, Function.comp_def]
  have i6 : toggleAllCorrect s = true := by
    simp [toggleAllCorrect, hst, isChecked, q, hd.q_toggleAll, hd.checked_toggleAll, Model.allDone,
      TodoR.toTodo, Function.comp_def]
  have i7 : filterLinkCorrect s = true := by
    simp only [filterLinkCorrect, q, show "#" ++ "filter-all" = "#filter-all" from rfl,
      show "#" ++ "filter-active" = "#filter-active" from rfl,
      show "#" ++ "filter-completed" = "#filter-completed" from rfl,
      hd.q_filterAll, hd.q_filterActive, hd.q_filterCompleted]
    simp [nFilterAll, nFilterActive, nFilterCompleted, hd.static, staticNode, staticNodeD, Model.dyn,
      Node.hasClass, Node.classes, classes_selectedIf, filter, h.hash, filterStr]
    split_ifs <;> simp_all
  have i8 : atMostOneEditing s = true := by simp [atMostOneEditing, hed]
  simp [invariant, i1, i2, i3, i4, i5, i6, i7, i8]

end TodoMVC.Proof
