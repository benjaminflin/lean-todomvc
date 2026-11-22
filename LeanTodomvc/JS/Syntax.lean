/-!
# A small fragment of JavaScript

This is the abstract syntax of the subset of JavaScript used by our TodoMVC
implementation. It is deliberately small:

* JS arrays and objects are modelled with *value* semantics (they are never
  mutated in place by the app, which only uses `concat`/`map`/`filter`/
  `Object.assign({}, …)`), so there is no JS heap.
* DOM nodes are references into the DOM arena (`Value.node`).
* Instead of closures we support named function declarations together with
  `Function.prototype.bind`, so a function value is a name plus bound arguments.
* Numbers are integers.
-/

namespace JS

/-- Runtime values. -/
inductive Value where
  | undef
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (vs : List Value)
  | obj (fields : List (String × Value))
  /-- A reference to a DOM node, by index in the DOM arena. -/
  | node (n : Nat)
  /-- A (possibly partially applied, via `bind`) named function. -/
  | fn (name : String) (bound : List Value)
  /-- Host objects / functions: `document`, `window`, `location`, `localStorage`,
  `JSON`, `Object`, `String`. -/
  | host (name : String)
  deriving Repr, Inhabited

mutual
/-- Structural equality on values. -/
def Value.beq : Value → Value → Bool
  | .undef, .undef => true
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr as, .arr bs => Value.beqList as bs
  | .obj as, .obj bs => Value.beqFields as bs
  | .node a, .node b => a == b
  | .fn a as, .fn b bs => a == b && Value.beqList as bs
  | .host a, .host b => a == b
  | _, _ => false
def Value.beqList : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => Value.beq a b && Value.beqList as bs
  | _, _ => false
def Value.beqFields : List (String × Value) → List (String × Value) → Bool
  | [], [] => true
  | (k, a) :: as, (l, b) :: bs => k == l && Value.beq a b && Value.beqFields as bs
  | _, _ => false
end

instance : BEq Value := ⟨Value.beq⟩

inductive UnOp where
  | not | neg
  deriving Repr, DecidableEq

inductive BinOp where
  | add | sub | mul
  | seq | sne          -- `===`, `!==`
  | lt | le | gt | ge
  | and | or           -- short-circuiting `&&`, `||`
  deriving Repr, DecidableEq

inductive Expr where
  | lit (v : Value)
  | var (x : String)
  | member (e : Expr) (field : String)
  | index (e i : Expr)
  | call (f : Expr) (args : List Expr)
  | unop (op : UnOp) (e : Expr)
  | binop (op : BinOp) (a b : Expr)
  | cond (c t e : Expr)
  | arrLit (es : List Expr)
  | objLit (fields : List (String × Expr))
  deriving Repr, Inhabited

inductive Stmt where
  | expr (e : Expr)
  /-- `let x = e;` / `const x = e;` -/
  | decl (x : String) (e : Expr)
  /-- `x = e;` -/
  | assign (x : String) (e : Expr)
  /-- `o.f = e;` (only supported when `o` is a DOM node) -/
  | setMember (o : Expr) (field : String) (e : Expr)
  | ite (c : Expr) (t e : List Stmt)
  /-- `for (const x of e) { body }` -/
  | forOf (x : String) (e : Expr) (body : List Stmt)
  | ret (e : Expr)
  /-- `function f(params) { body }` (hoisted at top level) -/
  | funDecl (name : String) (params : List String) (body : List Stmt)
  deriving Repr, Inhabited

/-- A user function definition. -/
structure FunDef where
  params : List String
  body : List Stmt
  deriving Repr, Inhabited

end JS
