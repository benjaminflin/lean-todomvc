import LeanTodomvc.JS.Interp
import LeanTodomvc.Proof.World

/-!
# Symbolic execution lemmas

`R m l w` runs an interpreter computation with locals `l` in world `w`. The
lemmas here let `simp` step through programs at this level, without
unfolding the `StateT`/`ExceptT` plumbing.
-/

namespace JS
open DOM

abbrev Res (α : Type) := Option (Except String ((α × Locals) × World))

def R {α} (m : M α) (l : Locals) (w : World) : Res α := ((m.run l).run w).run

/-- Continue with `f` after a result. -/
def Res.andThen {α β} (r : Res α) (f : α → Locals → World → Res β) : Res β :=
  match r with
  | some (.ok ((a, l), w)) => f a l w
  | some (.error e) => some (.error e)
  | none => none

@[simp] theorem Res.andThen_ok {α β} (a : α) (l : Locals) (w : World) (f : α → Locals → World → Res β) :
    Res.andThen (some (.ok ((a, l), w))) f = f a l w := rfl

@[simp] theorem Res.andThen_error {α β} (e : String) (f : α → Locals → World → Res β) :
    Res.andThen (some (.error e)) f = some (.error e) := rfl

@[simp] theorem R_pure {α} (a : α) (l : Locals) (w : World) :
    R (pure a : M α) l w = some (.ok ((a, l), w)) := rfl

@[simp] theorem R_bind {α β} (x : M α) (f : α → M β) (l : Locals) (w : World) :
    R (x >>= f) l w = (R x l w).andThen fun a l w => R (f a) l w := by
  simp only [R, StateT.run_bind, ExceptT.run_bind]
  rcases h : ((x.run l).run w).run with _ | (e | ⟨⟨a, l'⟩, w'⟩) <;>
    simp [Res.andThen, Option.bind, ExceptT.run] <;> rfl

@[simp] theorem R_map {α β} (f : α → β) (x : M α) (l : Locals) (w : World) :
    R (f <$> x) l w = (R x l w).andThen fun a l w => some (.ok ((f a, l), w)) := by
  rw [map_eq_pure_bind, R_bind]; rfl

@[simp] theorem R_seqRight {α β} (x : M α) (y : M β) (l : Locals) (w : World) :
    R (x *> y) l w = (R x l w).andThen fun _ l w => R y l w := by
  rw [seqRight_eq_bind, R_bind]

@[simp] theorem R_throw {α} (e : String) (l : Locals) (w : World) :
    R (throw e : M α) l w = some (.error e) := rfl

@[simp] theorem R_get (l : Locals) (w : World) : R (get : M Locals) l w = some (.ok ((l, l), w)) := rfl

@[simp] theorem R_set (l l' : Locals) (w : World) :
    R (set l' : M Unit) l w = some (.ok (((), l'), w)) := rfl

@[simp] theorem R_getThe (l : Locals) (w : World) :
    R (getThe World : M World) l w = some (.ok ((w, l), w)) := rfl

@[simp] theorem R_setWorld (l : Locals) (w w' : World) :
    R (set w' : M Unit) l w = some (.ok (((), l), w')) := rfl

@[simp] theorem R_modifyThe (l : Locals) (w : World) (f : World → World) :
    R (modifyThe World f : M Unit) l w = some (.ok (((), l), f w)) := rfl

@[simp] theorem assocGet_nil {α} (k : String) : assocGet ([] : List (String × α)) k = none := rfl

@[simp] theorem assocGet_cons {α} (k k' : String) (v : α) (l : List (String × α)) :
    assocGet ((k', v) :: l) k = if k' = k then some v else assocGet l k := by
  by_cases h : k' = k
  · simp [assocGet, List.find?, h]
  · have : (k' == k) = false := by simpa using h
    simp [assocGet, List.find?, this, h]

theorem assocSet_nil {α} (k : String) (v : α) : assocSet [] k v = [(k, v)] := rfl

theorem assocSet_cons {α} (k k' : String) (v v' : α) (l : List (String × α)) :
    assocSet ((k', v') :: l) k v =
      if k' = k then (k, v) :: l.map (fun p => if p.1 = k then (k, v) else p)
      else (k', v') :: assocSet l k v := by
  unfold assocSet
  by_cases h : k' = k
  · subst h; simp
  · have h' : (k' == k) = false := by simpa using h
    by_cases ha : l.any (·.1 == k)
    · simp [h, h', ha]
    · simp [h, h', ha]

theorem assocGet_map_replace {α} (l : List (String × α)) (k x : String) (v : α) :
    assocGet (l.map fun p => if p.1 = k then (k, v) else p) x =
      if k = x then (if l.any (·.1 == k) then some v else none) else assocGet l x := by
  induction l with
  | nil => simp [assocGet]
  | cons p l ih =>
    obtain ⟨k', v'⟩ := p
    simp only [List.map_cons, assocGet_cons, List.any_cons]
    by_cases h1 : k' = k
    · subst h1
      by_cases h2 : k' = x
      · simp [h2]
      · simp only [ite_true, assocGet_cons, h2, ite_false]; rw [ih, if_neg h2]
    · have hb : (k' == k) = false := by simpa using h1
      simp only [h1, ite_false]
      rw [assocGet_cons, ih]
      by_cases h2 : k' = x
      · subst h2; simp [Ne.symm h1, h1]
      · simp only [hb, Bool.false_or, h2, ite_false]

theorem assocGet_assocSet {α} (l : List (String × α)) (k x : String) (v : α) :
    assocGet (assocSet l k v) x = if k = x then some v else assocGet l x := by
  induction l with
  | nil => simp [assocSet, assocGet]
  | cons p l ih =>
    obtain ⟨k', v'⟩ := p
    rw [assocSet_cons]
    by_cases h1 : k' = k
    · subst h1
      simp only [ite_true, assocGet_cons, assocGet_map_replace]
      by_cases h2 : k' = x <;> simp [h2]
    · simp only [h1, ite_false, assocGet_cons, ih]
      by_cases h2 : k' = x
      · subst h2; simp [Ne.symm h1]
      · simp [h2]

@[simp] theorem strictEq_num (a b : Int) : strictEq (.num a) (.num b) = decide (a = b) := by
  simp [strictEq, BEq.beq, Value.beq]
@[simp] theorem strictEq_str (a b : String) : strictEq (.str a) (.str b) = decide (a = b) := by
  simp [strictEq, BEq.beq, Value.beq]
@[simp] theorem strictEq_bool (a b : Bool) : strictEq (.bool a) (.bool b) = decide (a = b) := by
  simp [strictEq, BEq.beq, Value.beq]
@[simp] theorem strictEq_null_str (b : String) : strictEq .null (.str b) = false := rfl
@[simp] theorem strictEq_str_null (b : String) : strictEq (.str b) .null = false := rfl

/-! ## Variables -/

theorem R_lookupVar (x : String) (ls : List (String × Value)) (w : World) :
    R (lookupVar x) (some ls) w =
      match assocGet ls x with
      | some v => some (.ok ((v, some ls), w))
      | none =>
        match assocGet w.globals x with
        | some v => some (.ok ((v, some ls), w))
        | none =>
          if (assocGet w.funcs x).isSome then some (.ok ((.fn x [], some ls), w))
          else some (.error ("ReferenceError: " ++ x ++ " is not defined")) := by
  unfold lookupVar
  simp only [R_bind, R_get, Res.andThen_ok]
  rcases h : assocGet ls x with _ | v
  · simp only [R_bind, R_getThe, Res.andThen_ok]
    rcases hg : assocGet w.globals x with _ | v
    · by_cases hf : (assocGet w.funcs x).isSome <;> simp [hf]
    · rfl
  · rfl

theorem R_declVar_local (x : String) (v : Value) (ls : List (String × Value)) (w : World) :
    R (declVar x v) (some ls) w = some (.ok (((), some (assocSet ls x v)), w)) := by
  simp [declVar]

theorem R_assignVar (x : String) (ls : List (String × Value)) (v : Value) (w : World) :
    R (assignVar x v) (some ls) w =
      if (assocGet ls x).isSome then some (.ok (((), some (assocSet ls x v)), w))
      else if (assocGet w.globals x).isSome then
        some (.ok (((), some ls), { w with globals := assocSet w.globals x v }))
      else some (.error ("ReferenceError: " ++ x ++ " is not defined")) := by
  unfold assignVar
  simp only [R_bind, R_get, Res.andThen_ok]
  by_cases h : (assocGet ls x).isSome
  · simp [h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, R_bind, R_getThe, Res.andThen_ok]
    by_cases hg : (assocGet w.globals x).isSome <;> simp [hg]

/-! ## Calls -/

theorem R_callValue_fn {name : String} {bound args : List Value} {l : Locals} {w : World} {fd : FunDef}
    (h : assocGet w.funcs name = some fd) :
    R (callValue (.fn name bound) args) l w =
      (R (execB fd.body) (some (fd.params.zipIdx.map fun (p, i) => (p, (bound ++ args).getD i .undef))) w).andThen
        fun o _ w => match o with
          | .ret v => some (.ok ((v, l), w))
          | .normal => some (.ok ((.undef, l), w)) := by
  rw [callValue]
  simp only [R_bind, R_getThe, Res.andThen_ok, h]
  simp only [R_bind, R_get, Res.andThen_ok, R_set]
  rcases R (execB fd.body) _ w with _ | (e | ⟨⟨o, l'⟩, w'⟩)
  · rfl
  · rfl
  · cases o <;> rfl

/-! ## Properties -/

@[simp] theorem R_getMember_obj (fs : List (String × Value)) (f : String) (l : Locals) (w : World) :
    R (getMember (.obj fs) f) l w = some (.ok (((assocGet fs f).getD .undef, l), w)) := rfl

@[simp] theorem R_getMember_arr_length (vs : List Value) (l : Locals) (w : World) :
    R (getMember (.arr vs) "length") l w = some (.ok ((.num vs.length, l), w)) := rfl

@[simp] theorem R_getMember_node_value (n : Nat) (l : Locals) (w : World) :
    R (getMember (.node n) "value") l w = some (.ok ((.str (w.node n).value, l), w)) := rfl

@[simp] theorem R_getMember_node_checked (n : Nat) (l : Locals) (w : World) :
    R (getMember (.node n) "checked") l w = some (.ok ((.bool (w.node n).checked, l), w)) := rfl

@[simp] theorem R_getMember_location_hash (l : Locals) (w : World) :
    R (getMember (.host .location) "hash") l w = some (.ok ((.str w.hash, l), w)) := rfl

@[simp] theorem R_setMember_value (n : Nat) (v : Value) (l : Locals) (w : World) :
    R (setMember (.node n) "value" v) l w =
      some (.ok (((), l), w.modify n fun nd => { nd with value := toStr v })) := rfl

@[simp] theorem R_setMember_checked (n : Nat) (v : Value) (l : Locals) (w : World) :
    R (setMember (.node n) "checked" v) l w =
      some (.ok (((), l), w.modify n fun nd => { nd with checked := truthy v })) := rfl

@[simp] theorem R_setMember_hidden (n : Nat) (v : Value) (l : Locals) (w : World) :
    R (setMember (.node n) "hidden" v) l w =
      some (.ok (((), l), w.modify n fun nd => { nd with hidden := truthy v })) := rfl

@[simp] theorem R_setMember_className (n : Nat) (v : Value) (l : Locals) (w : World) :
    R (setMember (.node n) "className" v) l w =
      some (.ok (((), l), w.modify n fun nd => { nd with className := toStr v })) := rfl

@[simp] theorem R_setMember_textContent (n : Nat) (v : Value) (l : Locals) (w : World) :
    R (setMember (.node n) "textContent" v) l w = some (.ok (((), l), w.setTextContent n (toStr v))) := rfl

@[simp] theorem R_setMember_type (n : Nat) (v : Value) (l : Locals) (w : World) :
    R (setMember (.node n) "type" v) l w =
      some (.ok (((), l), w.modify n fun nd => { nd with attrs := assocSet nd.attrs "type" (toStr v) })) := rfl

/-! ## Built-in methods -/

theorem R_callMethod_builtin {r : Value} {m : String} {args : List Value} {l : Locals} {w : World}
    (hr : ∀ vs, r ≠ .arr vs) :
    R (callMethod r m args) l w = (R (builtinMethod r m args) l w).andThen fun o l w =>
      match o with
      | some v => some (.ok ((v, l), w))
      | none => some (.error ("TypeError: " ++ (toStr r ++ "." ++ m ++ " is not a function"))) := by
  rw [callMethod]
  · simp only [R_bind]
    rcases R (builtinMethod r m args) l w with _ | (e | ⟨⟨o, l'⟩, w'⟩)
    · rfl
    · rfl
    · cases o <;> rfl
  all_goals (intro vs; first | exact fun h => hr _ h | (intros; exact hr _ ‹_›))

theorem R_callMethod_host (h : Host) (m : String) (args : List Value) (l : Locals) (w : World) :
    R (callMethod (.host h) m args) l w = (R (builtinMethod (.host h) m args) l w).andThen fun o l w =>
      match o with
      | some v => some (.ok ((v, l), w))
      | none => some (.error ("TypeError: " ++ (toStr (.host h) ++ "." ++ m ++ " is not a function"))) :=
  R_callMethod_builtin (by simp)

theorem R_callMethod_node (n : Nat) (m : String) (args : List Value) (l : Locals) (w : World) :
    R (callMethod (.node n) m args) l w = (R (builtinMethod (.node n) m args) l w).andThen fun o l w =>
      match o with
      | some v => some (.ok ((v, l), w))
      | none => some (.error ("TypeError: " ++ (toStr (.node n) ++ "." ++ m ++ " is not a function"))) :=
  R_callMethod_builtin (by simp)

theorem R_callMethod_fn (f : String) (bound : List Value) (m : String) (args : List Value) (l : Locals)
    (w : World) :
    R (callMethod (.fn f bound) m args) l w = (R (builtinMethod (.fn f bound) m args) l w).andThen
      fun o l w => match o with
      | some v => some (.ok ((v, l), w))
      | none => some (.error ("TypeError: " ++ (toStr (.fn f bound) ++ "." ++ m ++ " is not a function"))) :=
  R_callMethod_builtin (by simp)

theorem R_callMethod_str (s : String) (m : String) (args : List Value) (l : Locals) (w : World) :
    R (callMethod (.str s) m args) l w = (R (builtinMethod (.str s) m args) l w).andThen fun o l w =>
      match o with
      | some v => some (.ok ((v, l), w))
      | none => some (.error ("TypeError: " ++ (toStr (.str s) ++ "." ++ m ++ " is not a function"))) :=
  R_callMethod_builtin (by simp)

@[simp] theorem R_builtin_createElement (t : String) (args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.host .document) "createElement" (.str t :: args)) l w =
      some (.ok ((some (.node w.dom.size), l), (w.alloc { tag := t }).1)) := rfl

@[simp] theorem R_builtin_createTextNode (t : String) (args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.host .document) "createTextNode" (.str t :: args)) l w =
      some (.ok ((some (.node w.dom.size), l), (w.alloc { tag := "#text", text := t }).1)) := rfl

@[simp] theorem R_builtin_getItem (k : String) (args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.host .localStorage) "getItem" (.str k :: args)) l w =
      some (.ok ((some (((assocGet w.storage k).map .str).getD .null), l), w)) := rfl

@[simp] theorem R_builtin_setItem (k : String) (v : Value) (args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.host .localStorage) "setItem" (.str k :: v :: args)) l w =
      some (.ok ((some .undef, l), { w with storage := assocSet w.storage k (toStr v) })) := rfl

@[simp] theorem R_builtin_stringify (v : Value) (args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.host .json) "stringify" (v :: args)) l w =
      some (.ok ((some (.str (Json.stringify v)), l), w)) := rfl

theorem R_builtin_parse (s : String) (args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.host .json) "parse" (.str s :: args)) l w =
      match Json.parse s with
      | some v => some (.ok ((some v, l), w))
      | none => some (.error "SyntaxError: JSON.parse") := by
  unfold builtinMethod
  simp only [R_bind, R_getThe, Res.andThen_ok, strArg, List.getD_cons_zero, toStr]
  cases Json.parse s <;> rfl

@[simp] theorem R_builtin_assign (t : List (String × Value)) (srcs : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.host .object) "assign" (.obj t :: srcs)) l w =
      (R (mergeObj t srcs) l w).andThen fun v l w => some (.ok ((some v, l), w)) := by
  unfold builtinMethod
  simp only [R_bind, R_getThe, Res.andThen_ok, R_map]

@[simp] theorem R_builtin_window_addEventListener (t : String) (f : Value) (args : List Value)
    (l : Locals) (w : World) :
    R (builtinMethod (.host .window) "addEventListener" (.str t :: f :: args)) l w =
      some (.ok ((some .undef, l), { w with windowListeners := w.windowListeners ++ [(t, f)] })) := rfl

@[simp] theorem R_builtin_addEventListener (n : Nat) (t : String) (f : Value) (args : List Value)
    (l : Locals) (w : World) :
    R (builtinMethod (.node n) "addEventListener" (.str t :: f :: args)) l w =
      some (.ok ((some .undef, l),
        w.modify n fun nd => { nd with listeners := nd.listeners ++ [(t, f)] })) := rfl

theorem R_builtin_appendChild (p c : Nat) (args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.node p) "appendChild" (.node c :: args)) l w =
      if (w.ancestors p).contains c then some (.error "HierarchyRequestError")
      else some (.ok ((some (.node c), l), w.appendChild p c)) := by
  unfold builtinMethod
  simp only [R_bind, R_getThe, Res.andThen_ok]
  split <;> simp_all

@[simp] theorem R_builtin_replaceChildren (p : Nat) (l : Locals) (w : World) :
    R (builtinMethod (.node p) "replaceChildren" []) l w =
      some (.ok ((some .undef, l), w.replaceChildren p)) := rfl

@[simp] theorem R_builtin_focus (p : Nat) (args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.node p) "focus" args) l w = some (.ok ((some .undef, l), w)) := rfl

@[simp] theorem R_builtin_bind (f : String) (bound args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.fn f bound) "bind" args) l w =
      some (.ok ((some (.fn f (bound ++ args.drop 1)), l), w)) := rfl

@[simp] theorem R_builtin_trim (s : String) (args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.str s) "trim" args) l w = some (.ok ((some (.str (jsTrim s)), l), w)) := rfl

@[simp] theorem R_builtin_concat (vs : List Value) (args : List Value) (l : Locals) (w : World) :
    R (builtinMethod (.arr vs) "concat" args) l w =
      some (.ok ((some (.arr (vs ++ args.flatMap fun | .arr ws => ws | v => [v])), l), w)) := rfl

theorem R_callMethod_concat (vs : List Value) (args : List Value) (l : Locals) (w : World) :
    R (callMethod (.arr vs) "concat" args) l w =
      some (.ok ((.arr (vs ++ args.flatMap fun | .arr ws => ws | v => [v]), l), w)) := by
  rw [callMethod]
  · simp
  all_goals simp

theorem R_callMethod_map (vs : List Value) (args : List Value) (l : Locals) (w : World) :
    R (callMethod (.arr vs) "map" args) l w =
      (R (mapArr (args.getD 0 .undef) vs) l w).andThen fun r l w => some (.ok ((.arr r, l), w)) := by
  rw [callMethod]; simp only [R_bind]; rfl

theorem R_callMethod_filter (vs : List Value) (args : List Value) (l : Locals) (w : World) :
    R (callMethod (.arr vs) "filter" args) l w =
      (R (filterArr (args.getD 0 .undef) vs) l w).andThen fun r l w => some (.ok ((.arr r, l), w)) := by
  rw [callMethod]; simp only [R_bind]; rfl

@[simp] theorem R_callValue_String (args : List Value) (l : Locals) (w : World) :
    R (callValue (.host .string) args) l w = some (.ok ((.str (toStr (args.getD 0 (.str ""))), l), w)) := by
  rw [callValue]; rfl

/-! ## Arithmetic on node indices -/

theorem nat_eq_self_add (a b : Nat) : (a = a + b) ↔ b = 0 := by omega
theorem nat_self_add_eq (a b : Nat) : (a + b = a) ↔ b = 0 := by omega
theorem nat_lt_self_add (a b : Nat) : (a < a + b) ↔ 0 < b := by omega

theorem toString_natCast_eq_empty (n : Nat) : (toString (n : Int) = "") = False := by
  have : toString (n : Int) = toString n := rfl
  rw [this]
  simp only [eq_iff_iff, iff_false]
  exact Nat.repr_ne_empty

theorem R_ite_pure {α} (c : Prop) [Decidable c] (a b : α) (l : Locals) (w : World) :
    R (if c then (pure a : M α) else pure b) l w = some (.ok (((if c then a else b), l), w)) := by
  split <;> rfl

theorem ite_value_str (c : Prop) [Decidable c] (a b : String) :
    (if c then Value.str a else Value.str b) = Value.str (if c then a else b) := by
  split <;> rfl

theorem ite_value_bool (c : Prop) [Decidable c] (a b : Bool) :
    (if c then Value.bool a else Value.bool b) = Value.bool (if c then a else b) := by
  split <;> rfl

/-- Symbolic execution: step through interpreter code with the lemmas above. -/
syntax "js_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| js_simp $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| simp (config := { maxSteps := 10000000, maxDischargeDepth := 12 }) only [
      evalE, evalList, evalFields, execS, execB, execFor,
      R_pure, R_bind, R_map, R_ite_pure, ite_value_str, ite_value_bool, R_seqRight, R_throw, R_get, R_set, R_getThe, R_setWorld, R_modifyThe,
      Res.andThen_ok, Res.andThen_error,
      R_lookupVar,
      R_declVar_local, R_assignVar,
      R_callMethod_host, R_callMethod_node, R_callMethod_fn, R_callMethod_str, R_callMethod_concat, R_callMethod_map, R_callMethod_filter, R_callValue_String,
      R_getMember_obj, R_getMember_arr_length, R_getMember_node_value, R_getMember_node_checked,
      R_getMember_location_hash,
      R_setMember_value, R_setMember_checked, R_setMember_hidden, R_setMember_className,
      R_setMember_textContent, R_setMember_type,
      R_builtin_createElement, R_builtin_createTextNode, R_builtin_getItem, R_builtin_setItem,
      R_builtin_stringify, R_builtin_parse, R_builtin_assign, R_builtin_window_addEventListener,
      R_builtin_addEventListener, R_builtin_appendChild, R_builtin_replaceChildren, R_builtin_focus,
      R_builtin_bind, R_builtin_trim, R_builtin_concat,
      assocGet_cons, assocGet_nil, assocGet_assocSet, assocSet_nil, assocSet_cons, strictEq_num, strictEq_str, strictEq_bool,
      strictEq_null_str, strictEq_str_null,
      evalUnop, evalBinop, truthy, toStr, strArg, mergeObj,
      World.alloc_fst_globals, World.alloc_fst_funcs, World.alloc_fst_storage, World.alloc_fst_hash,
      World.alloc_fst_windowListeners, World.alloc_fst_dom, World.alloc_snd,
      World.modify_globals, World.modify_funcs, World.modify_storage, World.modify_hash,
      World.modify_windowListeners, World.size_modify, World.size_replaceChildren, World.size_appendChild,
      World.alloc_modify_new, World.alloc_modify_old, World.modify_modify_same,
      World.node_alloc_eq, World.node_alloc_old,
      World.detach_globals, World.detach_funcs, World.detach_storage, World.detach_hash, World.detach_windowListeners, World.appendChild_globals, World.appendChild_funcs, World.appendChild_storage, World.appendChild_hash, World.appendChild_windowListeners, World.replaceChildren_globals, World.replaceChildren_funcs, World.replaceChildren_storage, World.replaceChildren_hash, World.replaceChildren_windowListeners, World.setTextContent_globals, World.setTextContent_funcs, World.setTextContent_storage, World.setTextContent_hash, World.setTextContent_windowListeners, World.node_modify_self, World.node_modify_ne,
      World.parent_modify_of, World.children_modify_of,
      World.appendChild_of_parent_none, World.replaceChildren_of_children_nil, World.setTextContent_eq,
      World.ancestors_of_parent_none,
      Array.size_push, List.mem_cons, List.not_mem_nil, or_false, or_true, false_or, true_or, List.contains_cons, List.contains_nil, List.flatten_cons, List.flatten_nil,
      List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ, List.drop,
      List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      Option.map_some, Option.map_none, Option.getD_some, Option.getD_none, Option.isSome_some,
      Option.isSome_none, Function.comp_apply,
      ite_true, ite_false, decide_true, decide_false, Bool.not_true, Bool.not_false,
      beq_self_eq_true, ne_eq, not_false_eq_true, implies_true, false_implies, forall_const,
      forall_eq', Option.some.injEq, eq_self_iff_true, decide_eq_true_eq, not_true_eq_false, decide_not, List.foldl_cons, List.foldl_nil, reduceCtorEq, Nat.add_one_ne_zero,
      true_and, and_true, false_and, and_false, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.or_false, Bool.false_or, Bool.true_or, Bool.or_true,
      List.any_cons, List.any_nil, String.reduceBEq, String.reduceEq, String.reduceAppend, reduceIte, Nat.reduceEqDiff, Int.reduceEq, Int.reduceNeg, Int.reduceGT, Int.reduceLT, Int.reduceSub, Int.reduceAdd,
      toString_natCast_eq_empty, Int.natCast_zero, Int.natCast_eq_zero, Int.natCast_pos, gt_iff_lt, Int.lt_irrefl,
      Nat.add_assoc, Nat.reduceAdd, Nat.add_lt_add_iff_left, Nat.reduceLT, Nat.lt_add_one,
      Nat.add_left_cancel_iff, nat_eq_self_add, nat_self_add_eq, nat_lt_self_add, Nat.one_ne_zero,
      Nat.succ_ne_zero, Nat.lt_irrefl, Nat.zero_lt_succ, Nat.zero_lt_one, beq_iff_eq,
      $extra,*])

end JS
