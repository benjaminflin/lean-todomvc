import LeanTodomvc.JS.Syntax

/-!
# Concrete syntax for the JavaScript fragment

`[js| … ]` parses a sequence of JS statements into a `List JS.Stmt`, and
`[jsE| … ]` parses a single expression. Dotted names such as `e.target.value`
are lexed by Lean as a single identifier, so the macro splits them back into
member accesses.

Blocks `{ … }` are flattened into the surrounding statement list, which is
sound because the fragment has function scope only (no block scoping).
-/

namespace JS.Notation
open Lean

declare_syntax_cat jsexpr
declare_syntax_cat jsfield
declare_syntax_cat jsstmt

syntax:max ident : jsexpr
syntax:max num : jsexpr
syntax:max str : jsexpr
syntax:max "(" jsexpr ")" : jsexpr
syntax:max "[" jsexpr,* "]" : jsexpr
syntax ident ":" jsexpr : jsfield
syntax:max "{" jsfield,* "}" : jsexpr
syntax:max jsexpr:max "." ident : jsexpr
syntax:max jsexpr:max "(" jsexpr,* ")" : jsexpr
syntax:max jsexpr:max "[" jsexpr "]" : jsexpr
syntax:75 "!" jsexpr:75 : jsexpr
syntax:75 "-" jsexpr:75 : jsexpr
syntax:70 jsexpr:70 " * " jsexpr:71 : jsexpr
syntax:65 jsexpr:65 " + " jsexpr:66 : jsexpr
syntax:65 jsexpr:65 " - " jsexpr:66 : jsexpr
syntax:55 jsexpr:56 " < " jsexpr:56 : jsexpr
syntax:55 jsexpr:56 " <= " jsexpr:56 : jsexpr
syntax:55 jsexpr:56 " > " jsexpr:56 : jsexpr
syntax:55 jsexpr:56 " >= " jsexpr:56 : jsexpr
syntax:50 jsexpr:50 " === " jsexpr:51 : jsexpr
syntax:50 jsexpr:50 " !== " jsexpr:51 : jsexpr
syntax:35 jsexpr:35 " && " jsexpr:36 : jsexpr
syntax:30 jsexpr:30 " || " jsexpr:31 : jsexpr
syntax:20 jsexpr:21 " ? " jsexpr " : " jsexpr:20 : jsexpr

syntax "let " ident " = " jsexpr ";" : jsstmt
syntax "const " ident " = " jsexpr ";" : jsstmt
syntax jsexpr " = " jsexpr ";" : jsstmt
syntax jsexpr ";" : jsstmt
syntax "{" jsstmt* "}" : jsstmt
syntax "if " "(" jsexpr ")" jsstmt (" else " jsstmt)? : jsstmt
syntax "for " "(" "const " ident " of " jsexpr ")" jsstmt : jsstmt
syntax "return " jsexpr ";" : jsstmt
syntax "function " ident "(" ident,* ")" "{" jsstmt* "}" : jsstmt

syntax "[jsE|" jsexpr "]" : term
syntax "[jsS|" jsstmt "]" : term
syntax "[js|" jsstmt* "]" : term

def nameStrs : Name → List String
  | .str p s => nameStrs p ++ [s]
  | .num p n => nameStrs p ++ [toString n]
  | .anonymous => []

def nameParts (x : Ident) : List String :=
  nameStrs x.getId.eraseMacroScopes

def memberChain (base : Term) (fs : List String) : MacroM Term :=
  fs.foldlM (fun (acc : Term) f => `(JS.Expr.member $acc $(quote f))) base

/-- `a.b.c` as a chain of member accesses. -/
def identExpr (x : Ident) : MacroM Term := do
  match nameParts x with
  | [] => Macro.throwError "empty identifier"
  | p :: ps =>
    let base ← match p with
      | "true" => `(JS.Expr.lit (.bool true))
      | "false" => `(JS.Expr.lit (.bool false))
      | "null" => `(JS.Expr.lit .null)
      | "undefined" => `(JS.Expr.lit .undef)
      | p => `(JS.Expr.var $(quote p))
    ps.foldlM (fun (acc : Term) f => `(JS.Expr.member $acc $(quote f))) base

macro_rules
  | `([jsE| $x:ident ]) => identExpr x
  | `([jsE| $n:num ]) => `(JS.Expr.lit (.num $n))
  | `([jsE| $s:str ]) => `(JS.Expr.lit (.str $s))
  | `([jsE| ( $e ) ]) => `([jsE| $e ])
  | `([jsE| [ $es,* ] ]) => do
    let ts ← es.getElems.mapM fun e => `([jsE| $e ])
    `(JS.Expr.arrLit [$ts,*])
  | `([jsE| { $fs,* } ]) => do
    let ts ← fs.getElems.mapM fun
      | `(jsfield| $k:ident : $e) => `(($(quote k.getId.toString), [jsE| $e ]))
      | _ => Macro.throwUnsupported
    `(JS.Expr.objLit [$ts,*])
  | `([jsE| $e . $f:ident ]) => do
    memberChain (← `([jsE| $e ])) (nameParts f)
  | `([jsE| $f ( $as,* ) ]) => do
    let ts ← as.getElems.mapM fun e => `([jsE| $e ])
    `(JS.Expr.call [jsE| $f ] [$ts,*])
  | `([jsE| $e [ $i ] ]) => `(JS.Expr.index [jsE| $e ] [jsE| $i ])
  | `([jsE| ! $e ]) => `(JS.Expr.unop .not [jsE| $e ])
  | `([jsE| - $e ]) => `(JS.Expr.unop .neg [jsE| $e ])
  | `([jsE| $a * $b ]) => `(JS.Expr.binop .mul [jsE| $a ] [jsE| $b ])
  | `([jsE| $a + $b ]) => `(JS.Expr.binop .add [jsE| $a ] [jsE| $b ])
  | `([jsE| $a - $b ]) => `(JS.Expr.binop .sub [jsE| $a ] [jsE| $b ])
  | `([jsE| $a < $b ]) => `(JS.Expr.binop .lt [jsE| $a ] [jsE| $b ])
  | `([jsE| $a <= $b ]) => `(JS.Expr.binop .le [jsE| $a ] [jsE| $b ])
  | `([jsE| $a > $b ]) => `(JS.Expr.binop .gt [jsE| $a ] [jsE| $b ])
  | `([jsE| $a >= $b ]) => `(JS.Expr.binop .ge [jsE| $a ] [jsE| $b ])
  | `([jsE| $a === $b ]) => `(JS.Expr.binop .seq [jsE| $a ] [jsE| $b ])
  | `([jsE| $a !== $b ]) => `(JS.Expr.binop .sne [jsE| $a ] [jsE| $b ])
  | `([jsE| $a && $b ]) => `(JS.Expr.binop .and [jsE| $a ] [jsE| $b ])
  | `([jsE| $a || $b ]) => `(JS.Expr.binop .or [jsE| $a ] [jsE| $b ])
  | `([jsE| $c ? $t : $e ]) => `(JS.Expr.cond [jsE| $c ] [jsE| $t ] [jsE| $e ])

/-- Turn an assignment target into a statement. -/
def assignTarget (lhs : TSyntax `jsexpr) (rhs : Term) : MacroM Term := do
  match lhs with
  | `(jsexpr| $x:ident) =>
    match (nameParts x).reverse with
    | [v] => `([JS.Stmt.assign $(quote v) $rhs])
    | f :: rest =>
      let objId := mkIdent (rest.reverse.foldl (fun n s => Name.str n s) Name.anonymous)
      `([JS.Stmt.setMember [jsE| $objId:ident ] $(quote f) $rhs])
    | [] => Macro.throwError "bad assignment target"
  | `(jsexpr| $o . $f:ident) => `([JS.Stmt.setMember [jsE| $o ] $(quote f.getId.toString) $rhs])
  | _ => Macro.throwError "unsupported assignment target"

macro_rules
  | `([jsS| let $x:ident = $e ; ]) => `([JS.Stmt.decl $(quote x.getId.toString) [jsE| $e ]])
  | `([jsS| const $x:ident = $e ; ]) => `([JS.Stmt.decl $(quote x.getId.toString) [jsE| $e ]])
  | `([jsS| $l:jsexpr = $e ; ]) => do assignTarget l (← `([jsE| $e ]))
  | `([jsS| $e:jsexpr ; ]) => `([JS.Stmt.expr [jsE| $e ]])
  | `([jsS| { $ss* } ]) => `([js| $ss* ])
  | `([jsS| if ( $c ) $t ]) => `([JS.Stmt.ite [jsE| $c ] [jsS| $t ] []])
  | `([jsS| if ( $c ) $t else $e ]) => `([JS.Stmt.ite [jsE| $c ] [jsS| $t ] [jsS| $e ]])
  | `([jsS| for ( const $x:ident of $e ) $b ]) =>
    `([JS.Stmt.forOf $(quote x.getId.toString) [jsE| $e ] [jsS| $b ]])
  | `([jsS| return $e ; ]) => `([JS.Stmt.ret [jsE| $e ]])
  | `([jsS| function $f:ident ( $ps,* ) { $ss* } ]) => do
    let ps := ps.getElems.map fun p => quote (k := `term) p.getId.toString
    `([JS.Stmt.funDecl $(quote f.getId.toString) [$ps,*] [js| $ss* ]])
  | `([js| $ss* ]) => do
    let ts ← ss.mapM fun s => `([jsS| $s ])
    `(List.flatten [$ts,*])

end JS.Notation
