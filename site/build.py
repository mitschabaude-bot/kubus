#!/usr/bin/env python3
"""Builds the Kubus website into site/_site (Python standard library only).

Every ```kubus block is elaborated by `kubus --doc`: the blocks of a chapter form one module
(after the chapter's hidden imports), and are rendered with semantic highlighting, hovers with
types, links to definitions, `#eval`/`#check` output and the kernel's verdict. The library
(lib/*.ktt) is rendered as hyperlinked source with an index of definitions.

Block attributes: ```kubus fails (must raise an error, which is shown), ```kubus hole (shows the
goals of its `?` holes). The build fails if any other block raises an error, has a hole, or
contains a declaration the kernel does not certify.

Usage: site/build.py [--out DIR]
"""
import html, json, os, re, shutil, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SITE = os.path.join(ROOT, "site")
LIB = os.path.join(ROOT, "lib")
CHAPTERS = os.path.join(ROOT, "docs", "tutorial")
KUBUS = os.environ.get("KUBUS", os.path.join(ROOT, ".lake", "build", "bin", "kubus"))
REPO = "https://github.com/mitschabaude-bot/kubus"
errors = []


def fail(msg):
    errors.append(msg)
    print("ERROR:", msg, file=sys.stderr)


def doc(path):
    env = dict(os.environ, KUBUS_PATH=LIB)
    p = subprocess.run([KUBUS, "--doc", path], capture_output=True, text=True, env=env, timeout=600)
    if p.returncode != 0:
        fail(f"kubus --doc {path}: {p.stderr.strip()}")
        return None
    return json.loads(p.stdout)


# ---------------------------------------------------------------- markdown

def inline(s, rel):
    """Inline markdown: code, links, bold, italics."""
    out, pos = [], 0
    for m in re.finditer(r"`([^`]+)`", s):
        out.append(inline_text(s[pos:m.start()], rel))
        out.append(f"<code>{html.escape(m.group(1))}</code>")
        pos = m.end()
    out.append(inline_text(s[pos:], rel))
    return "".join(out)


def inline_text(s, rel):
    s = html.escape(s, quote=False)
    def link(m):
        href = m.group(2)
        if not re.match(r"[a-z]+:|#|/", href):
            href = rel + href
        return f'<a href="{html.escape(href)}">{m.group(1)}</a>'
    s = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", link, s)
    s = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", s)
    s = re.sub(r"(?<![\w*])\*([^*\s][^*]*)\*(?!\w)", r"<em>\1</em>", s)
    return s


def slugify(s):
    return re.sub(r"[^a-z0-9]+", "-", s.lower()).strip("-")


def markdown(text, rel, code_hook):
    """A small markdown renderer. `code_hook(lang, attrs, body)` renders fenced blocks."""
    lines = text.split("\n")
    out, i, toc = [], 0, []
    while i < len(lines):
        line = lines[i]
        if line.startswith("```"):
            info = line[3:].strip().split()
            lang, attrs = (info[0] if info else ""), info[1:]
            j = i + 1
            while j < len(lines) and not lines[j].startswith("```"):
                j += 1
            out.append(code_hook(lang, attrs, "\n".join(lines[i + 1:j])))
            i = j + 1
        elif line.startswith("<!--"):
            while i < len(lines) and "-->" not in lines[i]:
                i += 1
            i += 1
        elif m := re.match(r"(#{1,4}) (.*)", line):
            n, title = len(m.group(1)), m.group(2)
            sid = slugify(title)
            if n == 2:
                toc.append((sid, title))
            out.append(f'<h{n} id="{sid}">{inline(title, rel)}<a class="anchor" href="#{sid}" aria-hidden="true">#</a></h{n}>')
            i += 1
        elif line.startswith("<"):
            j = i
            while j < len(lines) and lines[j].strip():
                j += 1
            out.append("\n".join(lines[i:j]))
            i = j
        elif re.match(r"\s*([-*]|\d+\.) ", line):
            ordered = bool(re.match(r"\s*\d+\.", line))
            items = []
            while i < len(lines) and lines[i].strip() and (re.match(r"\s*([-*]|\d+\.) ", lines[i]) or lines[i].startswith("  ")):
                if re.match(r"\s*([-*]|\d+\.) ", lines[i]):
                    items.append(re.sub(r"\s*([-*]|\d+\.) ", "", lines[i], count=1))
                else:
                    items[-1] += " " + lines[i].strip()
                i += 1
            tag = "ol" if ordered else "ul"
            out.append(f"<{tag}>" + "".join(f"<li>{inline(it, rel)}</li>" for it in items) + f"</{tag}>")
        elif line.startswith("|"):
            rows = []
            while i < len(lines) and lines[i].startswith("|"):
                cells = re.split(r"(?<!\\)\|", lines[i].strip()[1:-1])
                rows.append([c.strip().replace("\\|", "|") for c in cells])
                i += 1
            head, body = rows[0], [r for r in rows[2:]]
            t = "<table><thead><tr>" + "".join(f"<th>{inline(c, rel)}</th>" for c in head) + "</tr></thead><tbody>"
            t += "".join("<tr>" + "".join(f"<td>{inline(c, rel)}</td>" for c in r) + "</tr>" for r in body)
            out.append('<div class="table">' + t + "</tbody></table></div>")
        elif line.startswith("> "):
            buf = []
            while i < len(lines) and lines[i].startswith(">"):
                buf.append(lines[i][1:].strip())
                i += 1
            out.append(f"<blockquote><p>{inline(' '.join(buf), rel)}</p></blockquote>")
        elif not line.strip():
            i += 1
        else:
            buf = []
            while i < len(lines) and lines[i].strip() and not re.match(r"(```|#|<|\||> |\s*([-*]|\d+\.) )", lines[i]):
                buf.append(lines[i])
                i += 1
            out.append(f"<p>{inline(' '.join(buf), rel)}</p>")
    return "\n".join(out), toc


# ---------------------------------------------------------------- code rendering

def tok_link(t, s, rel, local_module, module_pages):
    """The link from a use of a global to its definition (anchored by name)."""
    d = t.get("d")
    if not d:
        return None
    f = d["f"]
    if t["k"] == "module":
        return f"{rel}{module_pages[f]}" if f in module_pages else None
    if f == local_module:
        return "#" + s
    if f in module_pages:
        return f"{rel}{module_pages[f]}#{s}"
    return None


def render_lines(src_lines, tokens, first, last, rel, module, module_pages, decls, opts):
    """Render source lines first..last (1-based, inclusive) with their tokens."""
    by_line = {}
    for t in tokens:
        by_line.setdefault(t["l"], []).append(t)
    starts = {d["line"]: d for d in decls}
    # error ranges, per line: (col, ecol)
    err_ranges = {}
    for d in decls:
        e = d.get("error")
        if e and opts.get("show_errors"):
            p = e["pos"]
            el, ec = (p["eline"], p["ecol"]) if p["eline"] else (p["line"], None)
            for l in range(p["line"], el + 1):
                c0 = p["col"] if l == p["line"] else 1
                c1 = ec if (l == el and ec) else None
                err_ranges.setdefault(l, []).append((c0, c1))
    out = []
    cur = None
    for l in range(first, last + 1):
        if l in starts:
            cur = starts[l]
        text = src_lines[l - 1] if l - 1 < len(src_lines) else ""
        toks = sorted(by_line.get(l, []), key=lambda t: t["c"])
        parts, col = [], 1
        line_errs = err_ranges.get(l, [])

        def seg(s, c0, cls=None, attrs=""):
            if not s:
                return ""
            inner = html.escape(s)
            errc = any(c0 >= a and (b is None or c0 < b) for a, b in line_errs)
            classes = " ".join(x for x in [cls, "err" if errc else None] if x)
            if classes or attrs:
                return f'<span class="{classes}"{attrs}>{inner}</span>' if classes else f"<span{attrs}>{inner}</span>"
            return inner

        for t in toks:
            if t["c"] < col:
                continue
            parts.append(seg(text[col - 1:t["c"] - 1], col))
            s = text[t["c"] - 1:t["c"] - 1 + t["n"]]
            attrs = ""
            if "h" in t:
                attrs += f' data-h="{html.escape(t["h"])}"'
            k = t["k"]
            if k in ("variable", "interval-var") and cur is not None:
                attrs += f' data-r="v{cur["line"]}:{html.escape(s)}"'
            elif k in ("global", "constructor", "data", "definition"):
                attrs += f' data-r="g:{html.escape(s)}"'
            if "a" in t:
                attrs += f' id="{html.escape(t["a"])}"' if opts.get("anchors") else ""
            href = tok_link(t, s, rel, module, module_pages)
            cls = "k-" + k
            if href and k != "definition":
                inner = seg(s, t["c"], cls, attrs)
                parts.append(f'<a href="{html.escape(href)}">{inner}</a>')
            else:
                parts.append(seg(s, t["c"], cls, attrs))
            col = t["c"] + t["n"]
        parts.append(seg(text[col - 1:], col))
        gut = '<span class="gut"></span>'
        d = starts.get(l)
        if d and d.get("name"):
            k = d.get("kernel")
            name = html.escape(d["name"])
            if k == "certified":
                gut = f'<span class="gut ok" data-h="{name}: certified by the kernel" aria-label="certified by the kernel">✓</span>'
            elif k:
                gut = f'<span class="gut bad" data-h="{html.escape(d.get("kernelMsg") or k)}" aria-label="{html.escape(k)}">✗</span>'
        anchor = f' id="L{l}"' if opts.get("line_ids") else ""
        num = f'<a class="ln" href="#L{l}">{l}</a>' if opts.get("line_ids") else ""
        out.append(f'<div class="line"{anchor}>{num}{gut}<span class="src">{"".join(parts) or " "}</span></div>')
        for dd in decls:
            if dd["line"] >= first and min(dd["endLine"], last) == l:
                out.extend(after_decl(dd, opts))
    return "\n".join(out)


def after_decl(d, opts):
    out = []
    if d.get("out"):
        out.append(f'<div class="output"><pre>{html.escape(d["out"])}</pre></div>')
    for g in d.get("goals", []):
        out.append(f'<div class="goal"><pre>{html.escape(g["msg"])}</pre></div>')
    if d.get("error") and opts.get("show_errors"):
        out.append(f'<div class="error"><pre>{html.escape(d["error"]["msg"])}</pre></div>')
    return out


def trim_decl_ends(decls, src_lines):
    """Declarations end at their last non-blank line."""
    for d in decls:
        e = d["endLine"]
        while e > d["line"] and (e - 1 >= len(src_lines) or not src_lines[e - 1].strip() or src_lines[e - 1].lstrip().startswith("--")):
            e -= 1
        d["endLine"] = e


# ---------------------------------------------------------------- pages

NAV = [("Tutorial", "tutorial/index.html"), ("Library", "lib/index.html")]


def page(title, body, rel, active="", sidebar="", description="Kubus: a proof assistant for cubical type theory with a verified kernel"):
    nav = "".join(f'<a href="{rel}{href}"{" class=\"active\"" if active == name else ""}>{name}</a>' for name, href in NAV)
    side = f'<nav class="sidebar" aria-label="Contents"><details open><summary>Contents</summary>{sidebar}</details></nav>' if sidebar else ""
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<meta name="description" content="{html.escape(description)}">
<link rel="icon" href="{rel}static/favicon.svg" type="image/svg+xml">
<link rel="stylesheet" href="{rel}static/style.css">
<script>document.documentElement.dataset.theme = localStorage.getItem("theme") || "";</script>
</head>
<body class="{'with-sidebar' if sidebar else ''}">
<header class="top">
  <a class="brand" href="{rel}index.html"><img src="{rel}static/favicon.svg" alt="" width="22" height="22"> Kubus</a>
  <nav class="main" aria-label="Main">{nav}<a href="{REPO}">GitHub</a></nav>
  <button class="theme" type="button" aria-label="Toggle dark mode" title="Toggle dark mode">◐</button>
</header>
<div class="layout">
{side}
<main id="content">
{body}
</main>
</div>
<footer><p>Kubus is open source (MIT) · <a href="{REPO}">source on GitHub</a> · every code block on this site is checked by Kubus and certified by its kernel when the site is built.</p></footer>
<script src="{rel}static/kubus.js" defer></script>
</body>
</html>
"""


def write(out_dir, rel_path, content):
    p = os.path.join(out_dir, rel_path)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w") as f:
        f.write(content)


# ---------------------------------------------------------------- library

LIB_ORDER = ["basic", "equiv", "univalence", "int", "bool", "circle", "loopspace", "hits"]
LIB_DESC = {
    "basic": "Paths: reflexivity, symmetry, concatenation, transport, J, function extensionality.",
    "equiv": "Contractible types, fibers, equivalences, univalence as a map ua, isomorphisms are equivalences.",
    "univalence": "The univalence axiom: the type of types equivalent to A is contractible.",
    "int": "Natural numbers and integers; the successor equivalence of the integers.",
    "bool": "Booleans and negation as a path Bool = Bool.",
    "circle": "The circle, its universal cover, and winding numbers.",
    "loopspace": "The loop space of the circle is the integers.",
    "hits": "Propositional truncation and suspensions.",
}


def build_library(out_dir, module_pages):
    mods = [m for m in LIB_ORDER if os.path.exists(os.path.join(LIB, m + ".ktt"))]
    mods += sorted(f[:-4] for f in os.listdir(LIB) if f.endswith(".ktt") and f[:-4] not in mods)
    docs = {}
    for m in mods:
        module_pages[m] = f"lib/{m}.html"
    for m in mods:
        d = doc(os.path.join(LIB, m + ".ktt"))
        if d is None:
            continue
        docs[m] = d
        for dec in d["decls"]:
            if dec.get("name") and dec.get("kernel") != "certified":
                fail(f"lib/{m}.ktt: {dec['name']} is not certified by the kernel ({dec.get('kernelMsg')})")
            if dec.get("error"):
                fail(f"lib/{m}.ktt: {dec['error']['msg']}")
    index = []
    side = '<p class="side-title"><a href="index.html">Library</a></p><ul>' + "".join(
        f'<li><a href="{m}.html">{m}</a></li>' for m in mods) + "</ul>"
    for m, d in docs.items():
        src = open(os.path.join(LIB, m + ".ktt")).read().split("\n")
        trim_decl_ends(d["decls"], src)
        while src and not src[-1].strip():
            src.pop()
        code = render_lines(src, d["tokens"], 1, len(src), "../", m, module_pages, d["decls"],
                            {"anchors": True, "line_ids": True})
        ncert = sum(1 for x in d["decls"] if x.get("kernel") == "certified")
        body = (f'<h1>{m}<span class="sub">lib/{m}.ktt</span></h1><p class="lede">{html.escape(LIB_DESC.get(m, ""))}</p>'
                f'<p class="meta">{ncert} declarations, all certified by the kernel · <a href="{REPO}/blob/main/lib/{m}.ktt">source</a></p>'
                f'<div class="code file">{code}</div>')
        write(out_dir, f"lib/{m}.html", page(f"{m} · Kubus library", body, "../", "Library", side.replace(f'href="{m}.html"', f'href="{m}.html" aria-current="page"')))
        for t in d["tokens"]:
            if "a" in t:
                index.append((t["a"], m, t["l"], t.get("h", ""), t["k"]))
    index.sort(key=lambda x: x[0].lower())
    rows = "".join(
        f'<tr><td><a href="{m}.html#L{l}" class="k-{k}">{html.escape(n)}</a></td><td><code>{html.escape(h.split(" : ", 1)[1] if " : " in h else "")}</code></td><td><a href="{m}.html">{m}</a></td></tr>'
        for n, m, l, h, k in index)
    mods_html = "".join(f'<li><a href="{m}.html"><strong>{m}</strong></a> — {html.escape(LIB_DESC.get(m, ""))}</li>' for m in mods)
    body = (f"<h1>The library</h1><p class=\"lede\">The standard library, rendered from <code>lib/</code>: hover over a name to see its type, click it to go to its definition. Every declaration is certified by the kernel.</p>"
            f"<ul class=\"modules\">{mods_html}</ul><h2 id=\"index\">Index of definitions</h2>"
            f'<input class="filter" type="search" placeholder="Filter definitions…" aria-label="Filter definitions">'
            f'<div class="table"><table class="index"><thead><tr><th>name</th><th>type</th><th>module</th></tr></thead><tbody>{rows}</tbody></table></div>')
    write(out_dir, "lib/index.html", page("Library · Kubus", body, "../", "Library", side))
    return docs


# ---------------------------------------------------------------- chapters

def chapter_meta(text):
    m = re.match(r"<!--(.*?)-->", text, re.S)
    meta = {}
    if m:
        for line in m.group(1).strip().split("\n"):
            if ":" in line:
                k, v = line.split(":", 1)
                meta[k.strip()] = v.strip()
    return meta


def build_chapter(text, slug, module_pages, lib_docs, tmp):
    """Elaborate the chapter's kubus blocks as one module; return a code-block renderer."""
    meta = chapter_meta(text)
    imports = meta.get("imports", "").split()
    blocks = re.findall(r"^```kubus(?:[ \t]+([^\n]*))?\n(.*?)^```$", text, re.S | re.M)
    lines = [f"import {i}" for i in imports]
    spans = []
    for attrs, body in blocks:
        lines.append("")
        start = len(lines) + 1
        lines.extend(body.rstrip("\n").split("\n"))
        spans.append((start, len(lines), attrs.split()))
    module = "ch_" + slug.replace("-", "_")
    path = os.path.join(tmp, module + ".ktt")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    d = doc(path) if blocks else {"tokens": [], "decls": []}
    if d is None:
        d = {"tokens": [], "decls": []}
    src = lines
    trim_decl_ends(d["decls"], src)
    pages = dict(module_pages)
    pages[module] = ""
    # validation
    for (s, e, attrs) in spans:
        ds = [x for x in d["decls"] if s <= x["line"] <= e]
        has_err = any(x.get("error") for x in ds)
        if "fails" in attrs:
            if not has_err:
                fail(f"{slug}: a `fails` block did not fail:\n" + "\n".join(src[s - 1:e]))
            continue
        for x in ds:
            if x.get("error"):
                fail(f"{slug}: line {x['error']['pos']['line'] - s + 1} of a block: {x['error']['msg']}\n" + "\n".join(src[s - 1:e]))
            if x.get("goals") and "hole" not in attrs:
                fail(f"{slug}: unexpected hole:\n" + "\n".join(src[s - 1:e]))
            if x.get("name") and x.get("kernel") != "certified" and not x.get("error") and not x.get("goals"):
                fail(f"{slug}: {x['name']} is not certified by the kernel ({x.get('kernelMsg')})")
    it = iter(spans)

    def render(lang, attrs, body):
        if lang == "kubus":
            s, e, attrs = next(it)
            ds = [x for x in d["decls"] if s <= x["line"] <= e]
            code = render_lines(src, d["tokens"], s, e, "../", module, pages, ds,
                                {"show_errors": "fails" in attrs, "anchors": True})
            cls = "code" + (" fails" if "fails" in attrs else "")
            label = '<div class="label">expected to fail</div>' if "fails" in attrs else ""
            return f'<div class="{cls}">{label}{code}</div>'
        if lang == "kubus-lib":
            # attrs: module name [name ...]: show these declarations of the library
            mod, names = attrs[0], attrs[1:]
            ld = lib_docs.get(mod)
            if not ld:
                fail(f"{slug}: unknown library module {mod}")
                return ""
            lsrc = open(os.path.join(LIB, mod + ".ktt")).read().split("\n")
            parts = []
            for n in names:
                x = next((x for x in ld["decls"] if x.get("name") == n), None)
                if not x:
                    fail(f"{slug}: {n} is not declared in lib/{mod}.ktt")
                    continue
                parts.append(render_lines(lsrc, ld["tokens"], x["line"], x["endLine"], "../", mod, module_pages, [x], {}))
            return f'<div class="code lib"><div class="label"><a href="../lib/{mod}.html">lib/{mod}.ktt</a></div>' + "\n".join(parts) + "</div>"
        cls = f' class="lang-{html.escape(lang)}"' if lang else ""
        return f"<pre{cls}><code>{html.escape(body)}</code></pre>"

    return render


def build_tutorial(out_dir, module_pages, lib_docs):
    files = sorted(f for f in os.listdir(CHAPTERS) if f.endswith(".md"))
    chapters = []
    for f in files:
        text = open(os.path.join(CHAPTERS, f)).read()
        title = re.search(r"^# (.*)$", text, re.M).group(1)
        slug = f[:-3]
        chapters.append((slug, title, text))
    side = '<p class="side-title"><a href="index.html">Tutorial</a></p><ol>' + "".join(
        f'<li><a href="{s}.html">{html.escape(re.sub(r"^\d+\. ", "", t))}</a></li>' for s, t, _ in chapters) + "</ol>"
    tmp = tempfile.mkdtemp()
    try:
        for i, (slug, title, text) in enumerate(chapters):
            render = build_chapter(text, slug, module_pages, lib_docs, tmp)
            body, toc = markdown(text, "../", render)
            prev = f'<a class="prev" href="{chapters[i - 1][0]}.html">← {html.escape(chapters[i - 1][1])}</a>' if i > 0 else "<span></span>"
            nxt = f'<a class="next" href="{chapters[i + 1][0]}.html">{html.escape(chapters[i + 1][1])} →</a>' if i + 1 < len(chapters) else "<span></span>"
            toc_html = ""
            if toc:
                toc_html = '<p class="side-title">On this page</p><ul class="toc">' + "".join(f'<li><a href="#{a}">{inline(t, "../")}</a></li>' for a, t in toc) + "</ul>"
            s = side.replace(f'href="{slug}.html"', f'href="{slug}.html" aria-current="page"') + toc_html
            write(out_dir, f"tutorial/{slug}.html",
                  page(f"{re.sub(r'^\d+\. ', '', title)} · Kubus tutorial", f'<article>{body}</article><nav class="pager">{prev}{nxt}</nav>', "../", "Tutorial", s))
    finally:
        shutil.rmtree(tmp)
    items = "".join(f'<li><a href="{s}.html">{html.escape(re.sub(r"^\d+\. ", "", t))}</a></li>' for s, t, _ in chapters)
    body = ('<h1>Tutorial</h1><p class="lede">From functions and paths to univalence, the circle and the kernel. '
            'Every example is checked by Kubus when this site is built: hover over names to see their types, '
            'click to jump to definitions; a ✓ marks declarations certified by the kernel.</p>'
            f'<ol class="chapters">{items}</ol>')
    write(out_dir, "tutorial/index.html", page("Tutorial · Kubus", body, "../", "Tutorial", side))
    return chapters


def build_landing(out_dir, module_pages, lib_docs, chapters):
    text = open(os.path.join(SITE, "index.md")).read()
    tmp = tempfile.mkdtemp()
    try:
        render = build_chapter(text, "index", module_pages, lib_docs, tmp)
        body, _ = markdown(text, "", lambda lang, attrs, b: render(lang, attrs, b).replace('href="../', 'href="'))
    finally:
        shutil.rmtree(tmp)
    write(out_dir, "index.html", page("Kubus — cubical type theory with a verified kernel", f'<div class="landing">{body}</div>', ""))


def main():
    out_dir = os.path.join(SITE, "_site")
    if "--out" in sys.argv:
        out_dir = sys.argv[sys.argv.index("--out") + 1]
    if os.path.exists(out_dir):
        shutil.rmtree(out_dir)
    os.makedirs(out_dir)
    shutil.copytree(os.path.join(SITE, "static"), os.path.join(out_dir, "static"))
    module_pages = {}
    lib_docs = build_library(out_dir, module_pages)
    chapters = build_tutorial(out_dir, module_pages, lib_docs)
    build_landing(out_dir, module_pages, lib_docs, chapters)
    with open(os.path.join(out_dir, ".nojekyll"), "w") as f:
        f.write("")
    if errors:
        print(f"{len(errors)} errors", file=sys.stderr)
        sys.exit(1)
    print(f"site built in {out_dir}")


if __name__ == "__main__":
    main()
