import LeanTodomvc.App

/-!
# Emitting the app as a web page

Prints the markup and the script that the transition system is built from as
real HTML and JavaScript, so the verified app can be run in a browser. The
script is printed from the same AST that the interpreter runs, statement for
statement; only the concrete syntax is added here.
-/

namespace JS.Emit

/-- A JS string literal. -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun
    | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
    | '<' => "\\u003c"  -- so `</script>` cannot end the script early
    | c => c.toString) ++ "\""

def binop : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*"
  | .seq => "===" | .sne => "!=="
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||"

mutual
def value : Value → String
  | .undef => "undefined"
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => if n < 0 then "(" ++ toString n ++ ")" else toString n
  | .str s => quote s
  | .arr vs => "[" ++ ", ".intercalate (values vs) ++ "]"
  | .obj fs => "{" ++ ", ".intercalate (fields fs) ++ "}"
  | .node n => s!"/* node {n} */ null"
  | .fn f [] => f
  | .fn f bound => f ++ ".bind(" ++ ", ".intercalate ("null" :: values bound) ++ ")"
  | .host h => h.name
def values : List Value → List String
  | [] => []
  | v :: vs => value v :: values vs
def fields : List (String × Value) → List String
  | [] => []
  | (k, v) :: fs => (quote k ++ ": " ++ value v) :: fields fs
end

-- Expressions are fully parenthesised, so precedence never matters.
mutual
def expr : Expr → String
  | .lit v => value v
  | .var x => x
  | .member e f => expr e ++ "." ++ f
  | .index e i => expr e ++ "[" ++ expr i ++ "]"
  | .call f as => expr f ++ "(" ++ ", ".intercalate (exprs as) ++ ")"
  | .unop .not e => "!" ++ expr e
  | .unop .neg e => "-" ++ expr e
  | .binop op a b => "(" ++ expr a ++ " " ++ binop op ++ " " ++ expr b ++ ")"
  | .cond c t e => "(" ++ expr c ++ " ? " ++ expr t ++ " : " ++ expr e ++ ")"
  | .arrLit es => "[" ++ ", ".intercalate (exprs es) ++ "]"
  | .objLit fs => "{" ++ ", ".intercalate (objFields fs) ++ "}"
def exprs : List Expr → List String
  | [] => []
  | e :: es => expr e :: exprs es
def objFields : List (String × Expr) → List String
  | [] => []
  | (k, e) :: fs => (quote k ++ ": " ++ expr e) :: objFields fs
end

def indent (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

mutual
def stmt (d : Nat) : Stmt → String
  | .expr e => indent d ++ expr e ++ ";\n"
  | .decl x e => indent d ++ "let " ++ x ++ " = " ++ expr e ++ ";\n"
  | .assign x e => indent d ++ x ++ " = " ++ expr e ++ ";\n"
  | .setMember o f e => indent d ++ expr o ++ "." ++ f ++ " = " ++ expr e ++ ";\n"
  | .ite c t [] => indent d ++ "if (" ++ expr c ++ ") {\n" ++ block (d + 1) t ++ indent d ++ "}\n"
  | .ite c t e => indent d ++ "if (" ++ expr c ++ ") {\n" ++ block (d + 1) t ++ indent d ++ "} else {\n" ++
      block (d + 1) e ++ indent d ++ "}\n"
  | .forOf x e b => indent d ++ "for (const " ++ x ++ " of " ++ expr e ++ ") {\n" ++ block (d + 1) b ++
      indent d ++ "}\n"
  | .ret e => indent d ++ "return " ++ expr e ++ ";\n"
  | .funDecl f ps b => indent d ++ "function " ++ f ++ "(" ++ ", ".intercalate ps ++ ") {\n" ++
      block (d + 1) b ++ indent d ++ "}\n"
def block (d : Nat) : List Stmt → String
  | [] => ""
  | s :: ss => stmt d s ++ block d ss
end

def script (prog : List Stmt) : String := String.join (prog.map fun s => stmt 0 s ++ "\n")

end JS.Emit

namespace DOM.Emit

def escape (s : String) : String :=
  String.join (s.toList.map fun
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '"' => "&quot;" | c => c.toString)

/-- Elements which have no closing tag. -/
def voidTags : List String := ["input", "br", "img", "hr", "meta", "link"]

-- No whitespace is printed between tags, so the browser builds exactly the DOM that
-- `World.ofHtml` loads (no extra whitespace text nodes).
mutual
def html : Html → String
  | .text s => escape s
  | .el tag attrs cs =>
    let open_ := "<" ++ tag ++ String.join (attrs.map fun (k, v) =>
      if v.isEmpty then " " ++ k else " " ++ k ++ "=\"" ++ escape v ++ "\"") ++ ">"
    if voidTags.contains tag then open_ else open_ ++ htmls cs ++ "</" ++ tag ++ ">"
def htmls : List Html → String
  | [] => ""
  | h :: hs => html h ++ htmls hs
end

end DOM.Emit

namespace TodoMVC

/-- The app as a self-contained HTML page. -/
def page : String :=
  "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" ++
  "<title>Lean • TodoMVC</title>\n" ++
  "<link rel=\"stylesheet\" href=\"https://unpkg.com/todomvc-app-css@2.4.3/index.css\">\n" ++
  "</head>\n<body>" ++ DOM.Emit.htmls app.html ++
  "\n<script>\n" ++ JS.Emit.script app.script ++ "</script>\n</body>\n</html>\n"

end TodoMVC
