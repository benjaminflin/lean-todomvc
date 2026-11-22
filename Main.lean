import LeanTodomvc.Emit

/-- Print the app as an HTML page, or write it to the file given as the first argument. -/
def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.print TodoMVC.page
  | path :: _ =>
    IO.FS.writeFile path TodoMVC.page
    IO.println s!"wrote {path}"
