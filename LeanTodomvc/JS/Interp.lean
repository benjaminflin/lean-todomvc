import LeanTodomvc.DOM

/-!
# An interpreter for our JavaScript fragment

The interpreter is a big mutual definition by `partial_fixpoint`: it is defined
as the least fixed point in the flat order on `Option`, so `none` means the
computation diverges, while JS exceptions are the `Except String` layer. This
gives us real equations (`evalE.eq_1` etc.) to reason with, without fuel.

Why not fuel (or a fuel-based twin for kernel evaluation)? Proofs about
symbolic states are much cleaner without fuel bookkeeping. And kernel
evaluation would not pay off anyway: the kernel already gets stuck on core
`String` functions (e.g. `String.splitOn`, used by `querySelector`). So
concrete runs are checked with `native_decide`, which trusts the compiler,
and every other proof is kernel-checked.

The monad has two layers of state: the local variables of the current function
frame (`none` at the top level of the script, where declarations create
globals) and the `World`.
-/

namespace JS
open DOM

abbrev Locals := Option (List (String × Value))

abbrev M := StateT Locals (StateT World (ExceptT String Option))

inductive Outcome where
  | normal
  | ret (v : Value)

def assocSet {α} (l : List (String × α)) (k : String) (v : α) : List (String × α) :=
  if l.any (·.1 == k) then l.map fun p => if p.1 == k then (k, v) else p else l ++ [(k, v)]

def assocGet {α} (l : List (String × α)) (k : String) : Option α := (l.find? (·.1 == k)).map (·.2)

def truthy : Value → Bool
  | .undef | .null => false
  | .bool b => b
  | .num n => n != 0
  | .str s => s != ""
  | _ => true

mutual
def toStr : Value → String
  | .undef => "undefined"
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => toString n
  | .str s => s
  | .arr vs => ",".intercalate (toStrList vs)
  | .obj _ => "[object Object]"
  | .node _ => "[object HTMLElement]"
  | .fn _ _ => "function"
  | .host h => "[object " ++ h.name ++ "]"
def toStrList : List Value → List String
  | [] => []
  | v :: vs => toStr v :: toStrList vs
end

/-- `===`. Arrays/objects are compared structurally, which differs from JS's
reference equality; the app never compares them. -/
def isJsWhitespace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- `String.prototype.trim` -/
def jsTrim (s : String) : String :=
  String.ofList ((s.toList.dropWhile isJsWhitespace).reverse.dropWhile isJsWhitespace).reverse

def strictEq (a b : Value) : Bool := a == b

def throwT {α} (msg : String) : M α := throw ("TypeError: " ++ msg)

def lookupVar (x : String) : M Value := do
  if let some ls := (← get) then
    if let some v := assocGet ls x then return v
  let w ← getThe World
  if let some v := assocGet w.globals x then return v
  if (assocGet w.funcs x).isSome then return .fn x []
  throw ("ReferenceError: " ++ x ++ " is not defined")

def declVar (x : String) (v : Value) : M Unit := do
  match (← get) with
  | some ls => set (some (assocSet ls x v) : Locals)
  | none => modifyThe World fun w => { w with globals := assocSet w.globals x v }

def assignVar (x : String) (v : Value) : M Unit := do
  if let some ls := (← get) then
    if (assocGet ls x).isSome then
      set (some (assocSet ls x v) : Locals); return
  let w ← getThe World
  if (assocGet w.globals x).isSome then
    set { w with globals := assocSet w.globals x v }
  else throw ("ReferenceError: " ++ x ++ " is not defined")

def getMember (v : Value) (f : String) : M Value := do
  let w ← getThe World
  match v, f with
  | .undef, _ | .null, _ => throwT ("cannot read property " ++ f ++ " of " ++ toStr v)
  | .arr vs, "length" => return .num vs.length
  | .str s, "length" => return .num s.length
  | .obj fs, f => return (assocGet fs f).getD .undef
  | .node n, f =>
    let nd := w.node n
    match f with
    | "value" => return .str nd.value
    | "checked" => return .bool nd.checked
    | "hidden" => return .bool nd.hidden
    | "className" => return .str nd.className
    | "id" => return .str nd.id
    | "tagName" => return .str nd.tag
    | "textContent" => return .str (w.textContent n)
    | f => return ((nd.attr f).map Value.str).getD .undef
  | .host .location, "hash" => return .str w.hash
  | _, _ => return .undef

def setMember (o : Value) (f : String) (v : Value) : M Unit := do
  match o with
  | .node n =>
    let w ← getThe World
    match f with
    | "value" => set (w.modify n fun nd => { nd with value := toStr v })
    | "checked" => set (w.modify n fun nd => { nd with checked := truthy v })
    | "hidden" => set (w.modify n fun nd => { nd with hidden := truthy v })
    | "className" => set (w.modify n fun nd => { nd with className := toStr v })
    | "id" => set (w.modify n fun nd => { nd with id := toStr v })
    | "textContent" => set (w.setTextContent n (toStr v))
    | f => set (w.modify n fun nd => { nd with attrs := assocSet nd.attrs f (toStr v) })
  | _ => throwT ("unsupported assignment to property " ++ f)

def evalUnop : UnOp → Value → M Value
  | .not, v => return .bool (!truthy v)
  | .neg, .num n => return .num (-n)
  | .neg, _ => throwT "unary minus on non-number"

/-- Non-short-circuiting binary operators. -/
def evalBinop : BinOp → Value → Value → M Value
  | .add, .num a, .num b => return .num (a + b)
  | .add, .str a, b => return .str (a ++ toStr b)
  | .add, a, .str b => return .str (toStr a ++ b)
  | .sub, .num a, .num b => return .num (a - b)
  | .mul, .num a, .num b => return .num (a * b)
  | .seq, a, b => return .bool (strictEq a b)
  | .sne, a, b => return .bool (!strictEq a b)
  | .lt, .num a, .num b => return .bool (decide (a < b))
  | .le, .num a, .num b => return .bool (decide (a ≤ b))
  | .gt, .num a, .num b => return .bool (decide (a > b))
  | .ge, .num a, .num b => return .bool (decide (a ≥ b))
  | _, _, _ => throwT "unsupported operands"

def mergeObj (target : List (String × Value)) : List Value → M Value
  | [] => return .obj target
  | .obj fs :: rest => mergeObj (fs.foldl (fun t (k, v) => assocSet t k v) target) rest
  | .undef :: rest | .null :: rest => mergeObj target rest
  | _ :: _ => throwT "Object.assign on non-object"

def strArg (args : List Value) (i : Nat) : String := toStr (args.getD i .undef)

/-- Built-in methods which do not call back into JS. `none` = no such method. -/
def builtinMethod (recv : Value) (m : String) (args : List Value) : M (Option Value) := do
  let w ← getThe World
  match recv, m with
  | .fn f bound, "bind" => return some (.fn f (bound ++ args.drop 1))
  | .host .document, "getElementById" =>
    return some (((w.documentNodes.find? fun n => (w.node n).id == strArg args 0).map .node).getD .null)
  | .host .document, "querySelector" =>
    return some (((w.querySelector (strArg args 0)).map .node).getD .null)
  | .host .document, "createElement" =>
    let (w, n) := w.alloc { tag := strArg args 0 }
    set w; return some (.node n)
  | .host .document, "createTextNode" =>
    let (w, n) := w.alloc { tag := "#text", text := strArg args 0 }
    set w; return some (.node n)
  | .host .localStorage, "getItem" =>
    return some (((assocGet w.storage (strArg args 0)).map .str).getD .null)
  | .host .localStorage, "setItem" =>
    set { w with storage := assocSet w.storage (strArg args 0) (strArg args 1) }
    return some .undef
  | .host .localStorage, "removeItem" =>
    set { w with storage := w.storage.filter (·.1 != strArg args 0) }
    return some .undef
  | .host .json, "stringify" => return some (.str (Json.stringify (args.getD 0 .undef)))
  | .host .json, "parse" =>
    match Json.parse (strArg args 0) with
    | some v => return some v
    | none => throw "SyntaxError: JSON.parse"
  | .host .object, "assign" =>
    match args with
    | .obj t :: srcs => some <$> mergeObj t srcs
    | _ => throwT "Object.assign on non-object"
  | .host .window, "addEventListener" =>
    set { w with windowListeners := w.windowListeners ++ [(strArg args 0, args.getD 1 .undef)] }
    return some .undef
  | .node n, "addEventListener" =>
    set (w.modify n fun nd => { nd with listeners := nd.listeners ++ [(strArg args 0, args.getD 1 .undef)] })
    return some .undef
  | .node n, "appendChild" =>
    match args with
    | .node c :: _ =>
      if (w.ancestors n).contains c then throw "HierarchyRequestError"
      set (w.appendChild n c); return some (.node c)
    | _ => throwT "appendChild argument is not a Node"
  | .node n, "replaceChildren" =>
    if args.isEmpty then set (w.replaceChildren n); return some .undef
    else throwT "replaceChildren with arguments is not supported"
  | .node _, "focus" => return some .undef
  | .arr vs, "concat" =>
    return some (.arr (vs ++ args.flatMap fun | .arr ws => ws | v => [v]))
  | .str s, "trim" => return some (.str (jsTrim s))
  | _, _ => return none

mutual
def evalE : Expr → M Value
  | .lit v => return v
  | .var x => lookupVar x
  | .member e fld => do getMember (← evalE e) fld
  | .index e i => do
    let v ← evalE e
    let i ← evalE i
    match v, i with
    | .arr vs, .num n => return if n < 0 then .undef else vs.getD n.toNat .undef
    | v, i => getMember v (toStr i)
  | .call (.member recv m) args => do
    let r ← evalE recv
    let as ← evalList args
    callMethod r m as
  | .call fe args => do
    let fv ← evalE fe
    let as ← evalList args
    callValue fv as
  | .unop op e => do evalUnop op (← evalE e)
  | .binop .and a b => do
    let v ← evalE a
    if truthy v then evalE b else return v
  | .binop .or a b => do
    let v ← evalE a
    if truthy v then return v else evalE b
  | .binop op a b => do
    let x ← evalE a
    let y ← evalE b
    evalBinop op x y
  | .cond c t e => do
    if truthy (← evalE c) then evalE t else evalE e
  | .arrLit es => do return .arr (← evalList es)
  | .objLit fs => do return .obj (← evalFields fs)
partial_fixpoint

def evalList : List Expr → M (List Value)
  | [] => return []
  | e :: es => do
    let v ← evalE e
    let vs ← evalList es
    return v :: vs
partial_fixpoint

def evalFields : List (String × Expr) → M (List (String × Value))
  | [] => return []
  | (k, e) :: es => do
    let v ← evalE e
    let vs ← evalFields es
    return (k, v) :: vs
partial_fixpoint

/-- Call a function value. Missing arguments are `undefined`, extra ones ignored. -/
def callValue : Value → List Value → M Value
  | .host .string, args => return .str (toStr (args.getD 0 (.str "")))
  | .fn name bound, args => do
    let some fd := assocGet (← getThe World).funcs name
      | throw ("ReferenceError: " ++ name ++ " is not defined")
    let all := bound ++ args
    let frame := fd.params.zipIdx.map fun (p, i) => (p, all.getD i .undef)
    let saved ← get
    set (some frame : Locals)
    let r ← execB fd.body
    set saved
    match r with
    | .ret v => return v
    | .normal => return .undef
  | v, _ => throwT (toStr v ++ " is not a function")
partial_fixpoint

def callMethod : Value → String → List Value → M Value
  | .arr vs, "map", args => do return .arr (← mapArr (args.getD 0 .undef) vs)
  | .arr vs, "filter", args => do return .arr (← filterArr (args.getD 0 .undef) vs)
  | r, m, args => do
    match ← builtinMethod r m args with
    | some v => return v
    | none => throwT (toStr r ++ "." ++ m ++ " is not a function")
partial_fixpoint

/-- `Array.prototype.map`; the callback only receives the element. -/
def mapArr : Value → List Value → M (List Value)
  | _, [] => return []
  | g, v :: vs => do
    let w ← callValue g [v]
    let ws ← mapArr g vs
    return w :: ws
partial_fixpoint

/-- `Array.prototype.filter`; the callback only receives the element. -/
def filterArr : Value → List Value → M (List Value)
  | _, [] => return []
  | g, v :: vs => do
    let keep ← callValue g [v]
    let ws ← filterArr g vs
    return if truthy keep then v :: ws else ws
partial_fixpoint

def execS : Stmt → M Outcome
  | .expr e => do let _ ← evalE e; return .normal
  | .decl x e => do declVar x (← evalE e); return .normal
  | .assign x e => do assignVar x (← evalE e); return .normal
  | .setMember o fld e => do
    let ov ← evalE o
    let v ← evalE e
    setMember ov fld v; return .normal
  | .ite c t e => do
    if truthy (← evalE c) then execB t else execB e
  | .forOf x e body => do
    match ← evalE e with
    | .arr vs => execFor x vs body
    | v => throwT (toStr v ++ " is not iterable")
  | .ret e => do return .ret (← evalE e)
  | .funDecl name ps body => do
    modifyThe World fun w => { w with funcs := assocSet w.funcs name ⟨ps, body⟩ }
    return .normal
partial_fixpoint

def execB : List Stmt → M Outcome
  | [] => return .normal
  | s :: ss => do
    match ← execS s with
    | .normal => execB ss
    | r => return r
partial_fixpoint

def execFor : String → List Value → List Stmt → M Outcome
  | _, [], _ => return .normal
  | x, v :: vs, body => do
    declVar x v
    match ← execB body with
    | .normal => execFor x vs body
    | r => return r
partial_fixpoint
end

/-- Run an `M` computation against a world at the top level. -/
def M.run' {α} (m : M α) (w : World) : Option (Except String (α × World)) :=
  match ((m.run none).run w).run with
  | some (.ok ((a, _), w)) => some (.ok (a, w))
  | some (.error e) => some (.error e)
  | none => none

/-- Hoist the top-level function declarations, then run the script. -/
def runScript (prog : List Stmt) : M Unit := do
  for s in prog do
    if let .funDecl name ps body := s then
      modifyThe World fun w => { w with funcs := assocSet w.funcs name ⟨ps, body⟩ }
  let _ ← execB (prog.filter fun | .funDecl .. => false | _ => true)

/-- Call each listener in turn with the event object. -/
def fireListeners (ls : List Value) (ev : Value) : M Unit := do
  for l in ls do
    let _ ← callValue l [ev]

end JS
