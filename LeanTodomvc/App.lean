import LeanTodomvc.System
import LeanTodomvc.JS.Notation

/-!
# TodoMVC

The markup follows the TodoMVC template. Ids are added to the filter links so
the script can find them. The script is a vanilla-JS implementation in our
fragment, which re-renders the whole list after each change.
-/

namespace TodoMVC
open DOM JS

def html : List Html := [
  .el "section" [("class", "todoapp")] [
    .el "header" [("class", "header")] [
      .el "h1" [] [.text "todos"],
      .el "input" [("class", "new-todo"), ("placeholder", "What needs to be done?"),
        ("autofocus", "")] []],
    .el "section" [("class", "main")] [
      .el "input" [("id", "toggle-all"), ("class", "toggle-all"), ("type", "checkbox")] [],
      .el "label" [("for", "toggle-all")] [.text "Mark all as complete"],
      .el "ul" [("class", "todo-list")] []],
    .el "footer" [("class", "footer")] [
      .el "span" [("class", "todo-count")] [],
      .el "ul" [("class", "filters")] [
        .el "li" [] [.el "a" [("id", "filter-all"), ("class", "selected"), ("href", "#/")] [.text "All"]],
        .el "li" [] [.el "a" [("id", "filter-active"), ("href", "#/active")] [.text "Active"]],
        .el "li" [] [.el "a" [("id", "filter-completed"), ("href", "#/completed")] [.text "Completed"]]],
      .el "button" [("class", "clear-completed")] [.text "Clear completed"]]]]

def STORAGE_KEY : String := "todos-lean"

/-! ## The script

Each function is a separate definition, which makes it easier to reason
about functions one at a time. `script` declares all of them at the top
level, then runs the main code. -/

namespace Fn

js_function load() {
  const stored = localStorage.getItem("todos-lean");
  if (stored !== null) { todos = JSON.parse(stored); }
  for (const t of todos) {
    if (t.id >= nextId) { nextId = t.id + 1; }
  }
}

js_function save() {
  localStorage.setItem("todos-lean", JSON.stringify(todos));
}

js_function isActive(t) { return !t.completed; }

js_function isShown(t) {
  if (filter === "active") { return !t.completed; }
  if (filter === "completed") { return t.completed; }
  return true;
}

js_function flipIfId(id, t) {
  if (t.id === id) { return Object.assign({}, t, {completed: !t.completed}); }
  return t;
}

js_function setCompletedTo(c, t) { return Object.assign({}, t, {completed: c}); }

js_function setTitleIfId(id, title, t) {
  if (t.id === id) { return Object.assign({}, t, {title: title}); }
  return t;
}

js_function hasOtherId(id, t) { return t.id !== id; }

js_function onNewTodoKey(e) {
  if (e.key === "Enter") {
    const title = newTodo.value.trim();
    if (title !== "") {
      todos = todos.concat([{id: nextId, title: title, completed: false}]);
      nextId = nextId + 1;
      newTodo.value = "";
      save();
      render();
    }
  }
}

js_function toggleTodo(id) {
  todos = todos.map(flipIfId.bind(null, id));
  save();
  render();
}

js_function destroyTodo(id) {
  todos = todos.filter(hasOtherId.bind(null, id));
  save();
  render();
}

js_function onToggleAll() {
  todos = todos.map(setCompletedTo.bind(null, toggleAll.checked));
  save();
  render();
}

js_function clearCompleted() {
  todos = todos.filter(isActive);
  save();
  render();
}

js_function startEditing(id) {
  editingId = id;
  render();
}

js_function finishEditing(id, e) {
  if (editingId === id) {
    const title = e.target.value.trim();
    editingId = -1;
    if (title === "") {
      todos = todos.filter(hasOtherId.bind(null, id));
    } else {
      todos = todos.map(setTitleIfId.bind(null, id, title));
    }
    save();
    render();
  }
}

js_function onEditKey(id, e) {
  if (e.key === "Enter") { finishEditing(id, e); }
  else if (e.key === "Escape") {
    editingId = -1;
    render();
  }
}

js_function onEditBlur(id, e) { finishEditing(id, e); }

js_function route() {
  const h = location.hash;
  if (h === "#/active") { filter = "active"; }
  else if (h === "#/completed") { filter = "completed"; }
  else { filter = "all"; }
  render();
}

js_function renderTodo(t) {
  const li = document.createElement("li");
  const editing = editingId === t.id;
  li.className = (t.completed ? "completed" : "") + (editing ? " editing" : "");
  const view = document.createElement("div");
  view.className = "view";
  view.hidden = editing;
  const checkbox = document.createElement("input");
  checkbox.className = "toggle";
  checkbox.type = "checkbox";
  checkbox.checked = t.completed;
  checkbox.addEventListener("click", toggleTodo.bind(null, t.id));
  const label = document.createElement("label");
  label.textContent = t.title;
  label.addEventListener("dblclick", startEditing.bind(null, t.id));
  const destroy = document.createElement("button");
  destroy.className = "destroy";
  destroy.addEventListener("click", destroyTodo.bind(null, t.id));
  view.appendChild(checkbox);
  view.appendChild(label);
  view.appendChild(destroy);
  li.appendChild(view);
  if (editing) {
    const edit = document.createElement("input");
    edit.className = "edit";
    edit.value = t.title;
    edit.addEventListener("keydown", onEditKey.bind(null, t.id));
    edit.addEventListener("blur", onEditBlur.bind(null, t.id));
    li.appendChild(edit);
    edit.focus();
  }
  return li;
}

js_function render() {
  list.replaceChildren();
  for (const t of todos) {
    if (isShown(t)) { list.appendChild(renderTodo(t)); }
  }
  const activeCount = todos.filter(isActive).length;
  const completedCount = todos.length - activeCount;
  main.hidden = todos.length === 0;
  footer.hidden = todos.length === 0;
  toggleAll.checked = todos.length > 0 && activeCount === 0;
  count.replaceChildren();
  const strong = document.createElement("strong");
  strong.textContent = String(activeCount);
  count.appendChild(strong);
  count.appendChild(document.createTextNode(activeCount === 1 ? " item left" : " items left"));
  clearButton.hidden = completedCount === 0;
  filterAll.className = filter === "all" ? "selected" : "";
  filterActive.className = filter === "active" ? "selected" : "";
  filterCompleted.className = filter === "completed" ? "selected" : "";
}

end Fn

/-- The functions declared by the script. -/
def funcs : List (String × FunDef) := [
  ("load", Fn.load),
  ("save", Fn.save),
  ("isActive", Fn.isActive),
  ("isShown", Fn.isShown),
  ("flipIfId", Fn.flipIfId),
  ("setCompletedTo", Fn.setCompletedTo),
  ("setTitleIfId", Fn.setTitleIfId),
  ("hasOtherId", Fn.hasOtherId),
  ("onNewTodoKey", Fn.onNewTodoKey),
  ("toggleTodo", Fn.toggleTodo),
  ("destroyTodo", Fn.destroyTodo),
  ("onToggleAll", Fn.onToggleAll),
  ("clearCompleted", Fn.clearCompleted),
  ("startEditing", Fn.startEditing),
  ("finishEditing", Fn.finishEditing),
  ("onEditKey", Fn.onEditKey),
  ("onEditBlur", Fn.onEditBlur),
  ("route", Fn.route),
  ("renderTodo", Fn.renderTodo),
  ("render", Fn.render)]

/-- Global variable declarations at the start of the script. -/
def prelude : List Stmt := [js|
  let todos = [];
  let nextId = 0;
  let editingId = -1;
  let filter = "all";

  const newTodo = document.querySelector(".new-todo");
  const main = document.querySelector(".main");
  const toggleAll = document.querySelector(".toggle-all");
  const list = document.querySelector(".todo-list");
  const footer = document.querySelector(".footer");
  const count = document.querySelector(".todo-count");
  const clearButton = document.querySelector(".clear-completed");
  const filterAll = document.querySelector("#filter-all");
  const filterActive = document.querySelector("#filter-active");
  const filterCompleted = document.querySelector("#filter-completed");
]

/-- The main code, run after the declarations. -/
def main : List Stmt := [js|
  newTodo.addEventListener("keydown", onNewTodoKey);
  toggleAll.addEventListener("click", onToggleAll);
  clearButton.addEventListener("click", clearCompleted);
  window.addEventListener("hashchange", route);
  load();
  route();
]

def script : List Stmt :=
  prelude ++ funcs.map (fun (n, f) => .funDecl n f.params f.body) ++ main

def app : App := { html, script }

end TodoMVC
