// Theme toggle, hover popovers with types, highlighting of related names, index filter.
(() => {
  const root = document.documentElement;
  const btn = document.querySelector("button.theme");
  const dark = () => root.dataset.theme === "dark" ||
    (!root.dataset.theme && matchMedia("(prefers-color-scheme: dark)").matches);
  btn?.addEventListener("click", () => {
    root.dataset.theme = dark() ? "light" : "dark";
    localStorage.setItem("theme", root.dataset.theme);
  });

  // the sidebar is collapsed on small screens
  if (matchMedia("(max-width: 900px)").matches) document.querySelector(".sidebar details")?.removeAttribute("open");

  const pop = document.createElement("div");
  pop.className = "popover";
  pop.setAttribute("role", "tooltip");
  pop.hidden = true;
  document.body.appendChild(pop);
  let current = null;
  const show = (el) => {
    current = el;
    pop.textContent = el.dataset.h;
    pop.hidden = false;
    const r = el.getBoundingClientRect();
    const w = pop.offsetWidth, h = pop.offsetHeight;
    let x = Math.min(r.left, innerWidth - w - 8);
    let y = r.bottom + 6;
    if (y + h > innerHeight - 8) y = r.top - h - 6;
    pop.style.left = Math.max(8, x) + "px";
    pop.style.top = y + "px";
    const ref = el.dataset.r;
    if (ref) document.querySelectorAll(`[data-r="${CSS.escape(ref)}"]`).forEach(e => e.classList.add("rel"));
  };
  const hide = () => {
    pop.hidden = true;
    current = null;
    document.querySelectorAll(".rel").forEach(e => e.classList.remove("rel"));
  };
  document.addEventListener("mouseover", (e) => {
    const el = e.target.closest?.("[data-h]");
    if (el === current) return;
    hide();
    if (el) show(el);
  });
  document.addEventListener("focusin", (e) => {
    const el = e.target.querySelector?.("[data-h]") || e.target.closest?.("[data-h]");
    hide();
    if (el) show(el);
  });
  addEventListener("scroll", hide, { passive: true });
  document.addEventListener("keydown", (e) => { if (e.key === "Escape") hide(); });

  const filter = document.querySelector("input.filter");
  filter?.addEventListener("input", () => {
    const q = filter.value.toLowerCase();
    document.querySelectorAll("table.index tbody tr").forEach(tr => {
      tr.hidden = q && !tr.textContent.toLowerCase().includes(q);
    });
  });
})();
