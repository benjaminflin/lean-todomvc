import LeanTodomvc.Proof.Dispatch

/-!
# Loading the page

Running the script on the markup, with any well-formed `localStorage`, yields a
represented state.
-/
namespace TodoMVC.Proof
open JS DOM

/-- The page before the script runs. -/
def H : World := World.ofHtml html

@[simp] theorem H_qs_newTodo : H.querySelector ".new-todo" = some 5 := rfl
@[simp] theorem H_qs_main : H.querySelector ".main" = some 6 := rfl
@[simp] theorem H_qs_toggleAll : H.querySelector ".toggle-all" = some 7 := rfl
@[simp] theorem H_qs_list : H.querySelector ".todo-list" = some 10 := rfl
@[simp] theorem H_qs_footer : H.querySelector ".footer" = some 11 := rfl
@[simp] theorem H_qs_count : H.querySelector ".todo-count" = some 12 := rfl
@[simp] theorem H_qs_clear : H.querySelector ".clear-completed" = some 23 := rfl
@[simp] theorem H_qs_filterAll : H.querySelector "#filter-all" = some 15 := rfl
@[simp] theorem H_qs_filterActive : H.querySelector "#filter-active" = some 18 := rfl
@[simp] theorem H_qs_filterCompleted : H.querySelector "#filter-completed" = some 21 := rfl
@[simp] theorem H_globals : H.globals = [] := rfl
@[simp] theorem H_funcs : H.funcs = [] := rfl

theorem subtree_go_congr {w w' : World} (h : w'.dom = w.dom) :
    ∀ f n, World.subtree.go w' f n = World.subtree.go w f n
  | 0, _ => rfl
  | f + 1, n => by
    simp only [World.subtree.go, World.node_eq, h]
    have : World.subtree.go w' f = World.subtree.go w f := funext fun x => subtree_go_congr h f x
    rw [this]

theorem querySelector_congr {w w' : World} (h : w'.dom = w.dom) (s : String) :
    w'.querySelector s = w.querySelector s := by
  have hn : ∀ k, w'.node k = w.node k := fun k => by simp [World.node_eq, h]
  have hd : w'.documentNodes = w.documentNodes := by
    simp only [World.documentNodes, World.subtree, h]; exact subtree_go_congr h _ _
  simp only [World.querySelector, hd, hn]

@[simp] theorem qs_setGlobals (w : World) (g : List (String × Value)) (s : String) :
    (w.setGlobals g).querySelector s = w.querySelector s := querySelector_congr (w := w) (w' := w.setGlobals g) rfl s
@[simp] theorem qs_setFuncs (w : World) (g : List (String × FunDef)) (s : String) :
    (w.setFuncs g).querySelector s = w.querySelector s := querySelector_congr (w := w) (w' := w.setFuncs g) rfl s
@[simp] theorem qs_setStorage (w : World) (g : List (String × String)) (s : String) :
    (w.setStorage g).querySelector s = w.querySelector s := querySelector_congr (w := w) (w' := w.setStorage g) rfl s
@[simp] theorem qs_setHash (w : World) (g : String) (s : String) :
    (w.setHash g).querySelector s = w.querySelector s := querySelector_congr (w := w) (w' := w.setHash g) rfl s

theorem R_builtin_querySelector (s : String) (args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.host .document) "querySelector" (.str s :: args)) l w =
      some (.ok ((some (((w.querySelector s).map .node).getD .null), l), w)) := rfl

theorem R_declVar_global (x : String) (v : Value) (w : World) :
    R (declVar x v) none w = some (.ok (((), none), w.setGlobals (assocSet w.globals x v))) := by
  simp [declVar]

/-- The model before `load()`. -/
def m₀ : Model := ⟨[], 0, -1, ""⟩

theorem spec_prelude (w : World) (hd : w.dom = H.dom) (hg : w.globals = []) :
    R (execB prelude) none w = some (.ok ((.normal, none), w.setGlobals (globalsOf m₀))) := by
  have hq : ∀ s, w.querySelector s = H.querySelector s := querySelector_congr hd
  js_simp [prelude, R_declVar_global, assocSet_nil, assocSet_cons, R_builtin_querySelector, hg, hq,
    qs_setGlobals, H_qs_newTodo, H_qs_main, H_qs_toggleAll, H_qs_list, H_qs_footer, H_qs_count, H_qs_clear,
    H_qs_filterAll, H_qs_filterActive, H_qs_filterCompleted]
  rfl

/-! ## `load()` -/

def loadBody : List Stmt :=
  [.ite (.binop .ge (.member (.var "t") "id") (.var "nextId"))
    [.assign "nextId" (.binop .add (.member (.var "t") "id") (.lit (.num 1)))] []]

theorem loadBody_eq : Fn.load.body.getD 2 default = .forOf "t" (.var "todos") loadBody := rfl

/-- One more than the largest id, if that is at least `n`. -/
def maxNext (ts : List TodoR) (n : Int) : Int := ts.foldl (fun n t => if n ≤ t.id then t.id + 1 else n) n

theorem spec_loadLoop (ts₀ : List TodoR) : ∀ (ts : List TodoR) (ls : List (String × Value)) (n : Int) (w : World),
    (∀ x, x ≠ "t" → x ≠ "stored" → assocGet ls x = none) →
    R (execFor "t" (ts.map TodoR.val) loadBody) (some ls) (w.setGlobals (globalsOf ⟨ts₀, n, -1, ""⟩)) =
      some (.ok ((.normal, some (ts.foldl (fun ls t => assocSet ls "t" t.val) ls)),
        w.setGlobals (globalsOf ⟨ts₀, maxNext ts n, -1, ""⟩))) := by
  intro ts
  induction ts with
  | nil => intro ls n w _; rw [List.map_nil, execFor]; rfl
  | cons t ts ih =>
    intro ls n w hls
    have hls' : ∀ x, x ≠ "t" → x ≠ "stored" → assocGet (assocSet ls "t" t.val) x = none := by
      intro x hx hx'; rw [assocGet_assocSet, if_neg (Ne.symm hx), hls x hx hx']
    have hn : assocGet ls "nextId" = none := hls _ (by decide) (by decide)
    rw [List.map_cons, List.foldl_cons, execFor]
    by_cases hc : n ≤ t.id
    · have := ih (assocSet ls "t" t.val) (t.id + 1) w hls'
      rw [show maxNext (t :: ts) n = maxNext ts (t.id + 1) by simp [maxNext, hc]]
      js_simp [loadBody, globalsOf, TodoR.val, hn, hc, assocGet_assocSet]
      simpa [loadBody, globalsOf, TodoR.val] using this
    · have := ih (assocSet ls "t" t.val) n w hls'
      rw [show maxNext (t :: ts) n = maxNext ts n by simp [maxNext, hc]]
      js_simp [loadBody, globalsOf, TodoR.val, hn, hc, assocGet_assocSet]
      simpa [loadBody, globalsOf, TodoR.val] using this

theorem strictEq_null_null : strictEq .null .null = true := rfl

theorem setGlobals_self (w : World) : w.setGlobals w.globals = w := by cases w; rfl

theorem spec_load {l : Locals} {w : World} (hf : w.funcs = funcs) (hg : w.globals = globalsOf m₀)
    (ts : List TodoR) (hst : (w.storage = [] ∧ ts = []) ∨ w.storage = [(STORAGE_KEY, Json.stringify (todosVal ts))])
    (hnn : ∀ t ∈ ts, 0 ≤ t.id) :
    R (callValue (.fn "load" []) []) l w =
      some (.ok ((.undef, l), w.setGlobals (globalsOf ⟨ts, maxNext ts 0, -1, ""⟩))) := by
  rw [callFn lk_load hf]
  rcases hst with ⟨hs, rfl⟩ | hs
  · have := spec_loadLoop [] [] [("stored", .null)] 0 w (by intro x h1 h2; simp [assocGet, Ne.symm h2])
    js_simp [Fn.load, hs, hg, globalsOf, m₀, todosVal, STORAGE_KEY, strictEq_null_null]
    cases w; simp only [World.setGlobals] at hg ⊢; subst hg; rfl
  · have hp := parse_stringify_todos ts hnn
    have := spec_loadLoop ts ts [("stored", .str (Json.stringify (todosVal ts)))] 0 w
      (by intro x h1 h2; simp [assocGet, Ne.symm h2])
    js_simp [Fn.load, hs, hg, globalsOf, m₀, STORAGE_KEY, R_builtin_parse, hp]
    simp only [globalsOf, m₀, loadBody, todosVal] at this ⊢
    js_simp [this]

/-! ## The whole script -/

theorem R_execB_append (a b : List Stmt) (l : Locals) (w : World) :
    R (execB (a ++ b)) l w = (R (execB a) l w).andThen fun o l w =>
      match o with
      | .normal => R (execB b) l w
      | r => some (.ok ((r, l), w)) := by
  induction a generalizing l w with
  | nil => simp [execB.eq_1, Res.andThen]
  | cons s ss ih =>
    rw [List.cons_append, execB.eq_2, execB.eq_2]
    simp only [R_bind]
    rcases h : R (execS s) l w with _ | (e | ⟨⟨o, l'⟩, w'⟩)
    · rfl
    · rfl
    · simp only [Res.andThen]
      cases o <;> simp [ih, Res.andThen]

theorem R_lookupVar_global (x : String) (w : World) :
    R (lookupVar x) none w =
      match assocGet w.globals x with
      | some v => some (.ok ((v, none), w))
      | none =>
        if (assocGet w.funcs x).isSome then some (.ok ((.fn x [], none), w))
        else some (.error ("ReferenceError: " ++ x ++ " is not defined")) := by
  unfold lookupVar
  simp only [R_bind, R_get, Res.andThen_ok, R_getThe]
  rcases hg : assocGet w.globals x with _ | v
  · by_cases hf : (assocGet w.funcs x).isSome <;> simp [hf]
  · rfl

/-- The world after the listeners are added. -/
def withListeners (w : World) : World :=
  (((w.modify nNewTodo fun nd => { nd with listeners := nd.listeners ++ [("keydown", .fn "onNewTodoKey" [])] }).modify
    nToggleAll fun nd => { nd with listeners := nd.listeners ++ [("click", .fn "onToggleAll" [])] }).modify
    nClear fun nd => { nd with listeners := nd.listeners ++ [("click", .fn "clearCompleted" [])] }).setWindowListeners
    (w.windowListeners ++ [("hashchange", .fn "route" [])])

def loadModel (ts : List TodoR) : Model := ⟨ts, maxNext ts 0, -1, ""⟩

theorem spec_main {w : World} (hf : w.funcs = funcs) (hg : w.globals = globalsOf m₀)
    (ts : List TodoR) (hst : (w.storage = [] ∧ ts = []) ∨ w.storage = [(STORAGE_KEY, Json.stringify (todosVal ts))])
    (hnn : ∀ t ∈ ts, 0 ≤ t.id)
    (hpre : Pre (loadModel ts) ((withListeners w).setGlobals (globalsOf (loadModel ts)))) :
    R (execB main) none w = some (.ok ((.normal, none),
      renderW ((loadModel ts).route w.hash)
        ((withListeners w).setGlobals (globalsOf ((loadModel ts).route w.hash))))) := by
  have hload := fun (w' : World) (hf' : w'.funcs = funcs) (hg' : w'.globals = globalsOf m₀)
    (hs' : w'.storage = w.storage) => spec_load (l := none) hf' hg' ts (by rw [hs']; exact hst) hnn
  have hroute := spec_route (l := none) hpre []
  simp only [World.setGlobals_setGlobals, World.setGlobals_hash] at hroute
  js_simp [main, hf, hg, globalsOf, m₀, TodoMVC.funcs, R_lookupVar_global]
  rw [hload _ (by simp [hf]) (by simp [hg]) (by simp)]
  have hr : ∀ m : Model, assocGet (globalsOf m) "route" = none := fun m => by simp [globalsOf, assocGet]
  simp only [loadModel, withListeners, World.setWindowListeners_hash, World.modify_hash] at hroute ⊢
  js_simp [hf, TodoMVC.funcs, R_lookupVar_global, hr, hroute]
  rfl

/-! ## The initial page -/

/-- The dynamic parts of the markup. -/
def d₀ : Dyn := ⟨"", "", false, false, false, false, "selected", "", "", [], []⟩

theorem H_size : H.dom.size = 25 := rfl

theorem H_node : ∀ k < 25, H.node k = { staticNodeD d₀ k with listeners := [] } := by
  intro k hk; interval_cases k <;> rfl

theorem H_node_ge {k : Nat} (hk : 25 ≤ k) : H.node k = default :=
  World.node_of_size_le H k (by rw [H_size]; exact hk)

theorem maxNext_ge (ts : List TodoR) (n : Int) : n ≤ maxNext ts n := by
  induction ts generalizing n with
  | nil => simp [maxNext]
  | cons t ts ih =>
    simp only [maxNext, List.foldl_cons] at ih ⊢
    split
    · have := ih (t.id + 1); omega
    · exact ih n

theorem maxNext_gt (ts : List TodoR) (n : Int) : ∀ t ∈ ts, t.id < maxNext ts n := by
  induction ts generalizing n with
  | nil => simp
  | cons t ts ih =>
    intro t' ht'
    simp only [maxNext, List.foldl_cons] at ih ⊢
    rcases List.mem_cons.1 ht' with rfl | ht'
    · split
      · have := maxNext_ge ts (t'.id + 1); simp only [maxNext] at this; omega
      · have := maxNext_ge ts n; simp only [maxNext] at this; omega
    · exact ih _ t' ht'

theorem withListeners_node {w : World} (hd : w.dom = H.dom) (k : Nat) :
    (withListeners w).node k = if k < 25 then staticNodeD d₀ k else default := by
  have hw : ∀ k, w.node k = H.node k := fun k => by simp [World.node_eq, hd]
  have hs : w.dom.size = 25 := by rw [hd]; rfl
  by_cases hk : k < 25
  · rw [if_pos hk]
    interval_cases k <;>
      simp [withListeners, World.node_modify, hs, hw, H_node, staticNodeD, nNewTodo, nToggleAll, nClear]
  · rw [if_neg hk]
    have h5 : nNewTodo ≠ k := by simp [nNewTodo]; omega
    have h7 : nToggleAll ≠ k := by simp [nToggleAll]; omega
    have h23 : nClear ≠ k := by simp [nClear]; omega
    simp only [withListeners, World.setWindowListeners_node, World.node_modify_ne _ _ _ _ h5,
      World.node_modify_ne _ _ _ _ h7, World.node_modify_ne _ _ _ _ h23, hw]
    exact H_node_ge (by omega)

theorem pre_init {w : World} (hd : w.dom = H.dom) (hf : w.funcs = funcs) (ts : List TodoR) :
    Pre (loadModel ts) ((withListeners w).setGlobals (globalsOf (loadModel ts))) := by
  have hn := withListeners_node hd
  have hs : (withListeners w).dom.size = 25 := by simp [withListeners, hd]; rfl
  refine ⟨⟨by simp [withListeners, hf], rfl, by simp [hs], ?_, ?_, ?_⟩, ?_, ⟨d₀, fun k hk => ?_⟩, ?_⟩
  · simp only [World.chain_setGlobals]
    exact .step (by simp [hn, staticNodeD, nList]) <| .step (by simp [hn, staticNodeD, nMain]) <|
      .step (by simp [hn, staticNodeD]) <| .root (by simp [hn, staticNodeD])
  · simp only [World.parentLt_setGlobals]
    refine ⟨fun k p hk => ?_⟩
    rw [hn] at hk
    split at hk
    · interval_cases k <;> simp [staticNodeD] at hk <;> omega
    · cases hk
  · simp [hn, staticNodeD, d₀, nList]
  · simp only [World.parentWF_setGlobals]
    refine ⟨fun k p hk => ?_⟩
    rw [hn] at hk
    split at hk
    · rw [hn]; interval_cases k <;> simp [staticNodeD] at hk <;> subst hk <;> simp [staticNodeD, d₀]
    · cases hk
  · simp [hn, hk]
  · simp [hn, staticNodeD, d₀, nCount]

theorem setStorage_self (w : World) : w.setStorage w.storage = w := by cases w; rfl

theorem H_wl : H.windowListeners = [] := rfl

theorem init_world (st : List (String × String)) (h : String) :
    ({ World.ofHtml html with storage := st, hash := h } : World) = (H.setStorage st).setHash h := by
  unfold H; generalize World.ofHtml html = W; rfl

theorem hoist_script : hoistFuncs script [] = funcs := rfl

theorem filter_script : script.filter (fun s => !s.isFunDecl) = prelude ++ main := rfl

theorem loadModel_route_WF (ts : List TodoR) (hnd : (ts.map (·.id)).Nodup) (hnn : ∀ t ∈ ts, 0 ≤ t.id) (h : String) :
    ((loadModel ts).route h).WF :=
  ⟨hnd, hnn, maxNext_gt ts 0, maxNext_ge ts 0⟩

/-- Loading the page with todos `ts` in storage. -/
theorem init_rep (ts : List TodoR) (hnd : (ts.map (·.id)).Nodup) (hnn : ∀ t ∈ ts, 0 ≤ t.id)
    (st : List (String × String))
    (hst : (st = [] ∧ ts = []) ∨ st = [(STORAGE_KEY, Json.stringify (todosVal ts))]) (h : String) :
    Rep ((loadModel ts).route h) (app.init st h) := by
  let W1 : World := (H.setStorage st).setHash h
  let W3 : World := (W1.setFuncs funcs).setGlobals (globalsOf m₀)
  have hpre := pre_init (w := W3) rfl rfl ts
  have hmain := spec_main (w := W3) rfl rfl ts (by simpa [W3, W1] using hst) hnn hpre
  have hprel := spec_prelude (W1.setFuncs funcs) rfl rfl
  have hrun : R (runScript script) none W1 = some (.ok (((), none),
      renderW ((loadModel ts).route h) ((withListeners W3).setGlobals (globalsOf ((loadModel ts).route h))))) := by
    unfold runScript
    simp only [R_bind, R_modifyThe, Res.andThen_ok]
    rw [show W1.funcs = [] from rfl, hoist_script, filter_script, R_execB_append, hprel]
    simp only [Res.andThen_ok]
    rw [hmain]
    rfl
  have hinit : app.init st h =
      { world := (renderW ((loadModel ts).route h)
        ((withListeners W3).setGlobals (globalsOf ((loadModel ts).route h)))) } := by
    simp only [App.init, app, init_world]
    simp only [State.run, M.run']
    simp only [R] at hrun
    rw [hrun]
  rw [hinit]
  let Wl := (withListeners W3).setGlobals (globalsOf (loadModel ts))
  have hW : (withListeners W3).setGlobals (globalsOf ((loadModel ts).route h)) =
      withState Wl (globalsOf ((loadModel ts).route h)) Wl.storage := by
    simp only [withState, Wl, World.setGlobals_setGlobals]
    exact (setStorage_self _).symm
  rw [hW]
  refine rep_renderW hpre (loadModel_route_WF ts hnd hnn h) _ ?_
    (by simp [Wl, withListeners, W3, W1, Model.route]) (by simp [Wl, withListeners, W3, W1, H_wl])
  simp only [Wl, withListeners, W3, W1, World.setGlobals_storage, World.setWindowListeners_storage,
    World.modify_storage, World.setFuncs_storage, World.setHash_storage, World.setStorage_storage]
  rcases hst with ⟨rfl, rfl⟩ | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr rfl

end TodoMVC.Proof
