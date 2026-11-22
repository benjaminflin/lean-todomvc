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

def script : List Stmt := [js|
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

  function load() {
    const stored = localStorage.getItem("todos-lean");
    if (stored !== null) { todos = JSON.parse(stored); }
    for (const t of todos) {
      if (t.id >= nextId) { nextId = t.id + 1; }
    }
  }

  function save() {
    localStorage.setItem("todos-lean", JSON.stringify(todos));
  }

  function isActive(t) { return !t.completed; }

  function isShown(t) {
    if (filter === "active") { return !t.completed; }
    if (filter === "completed") { return t.completed; }
    return true;
  }

  function flipIfId(id, t) {
    if (t.id === id) { return Object.assign({}, t, {completed: !t.completed}); }
    return t;
  }

  function setCompletedTo(c, t) { return Object.assign({}, t, {completed: c}); }

  function setTitleIfId(id, title, t) {
    if (t.id === id) { return Object.assign({}, t, {title: title}); }
    return t;
  }

  function hasOtherId(id, t) { return t.id !== id; }

  function onNewTodoKey(e) {
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

  function toggleTodo(id) {
    todos = todos.map(flipIfId.bind(null, id));
    save();
    render();
  }

  function destroyTodo(id) {
    todos = todos.filter(hasOtherId.bind(null, id));
    save();
    render();
  }

  function onToggleAll() {
    todos = todos.map(setCompletedTo.bind(null, toggleAll.checked));
    save();
    render();
  }

  function clearCompleted() {
    todos = todos.filter(isActive);
    save();
    render();
  }

  function startEditing(id) {
    editingId = id;
    render();
  }

  function finishEditing(id, e) {
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

  function onEditKey(id, e) {
    if (e.key === "Enter") { finishEditing(id, e); }
    else if (e.key === "Escape") {
      editingId = -1;
      render();
    }
  }

  function onEditBlur(id, e) { finishEditing(id, e); }

  function route() {
    const h = location.hash;
    if (h === "#/active") { filter = "active"; }
    else if (h === "#/completed") { filter = "completed"; }
    else { filter = "all"; }
    render();
  }

  function renderTodo(t) {
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

  function render() {
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

  newTodo.addEventListener("keydown", onNewTodoKey);
  toggleAll.addEventListener("click", onToggleAll);
  clearButton.addEventListener("click", clearCompleted);
  window.addEventListener("hashchange", route);
  load();
  route();
]

def app : App := { html, script }

end TodoMVC
