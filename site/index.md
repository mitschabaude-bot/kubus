<section class="hero">
<h1>Cubical type theory, <em>verified</em>.</h1>
<p>Kubus is a proof assistant in which equality is a path, univalence and higher inductive types compute, and every definition is certified by a kernel that is proven sound for a theory proven consistent in Lean.</p>
<div class="cta"><a class="primary" href="tutorial/01-what-is-kubus.html">Read the tutorial</a><a href="lib/index.html">Browse the library</a><a href="https://github.com/mitschabaude-bot/kubus">Source on GitHub</a></div>
</section>

## Univalence computes

An equivalence of types gives a path between them, and transport along that path runs the equivalence. Negation is an equivalence of the booleans, so transporting `true` along `ua` of it gives `false`:

```kubus
import bool

def notEquiv : Equiv Bool Bool := isoToEquiv not not notnot notnot

#eval transport (ua notEquiv) true
```

## The circle, with winding numbers that run

The circle is a higher inductive type: a point `base` and a path `loop` from `base` to itself. Its universal cover sends the loop to the successor equivalence of the integers, so transport computes how often a loop winds around:

```kubus
import loopspace

#eval winding (trans loopP (trans loopP loopP))
#eval winding (trans loopP (sym loopP))
```

The library proves that the loops on the circle are exactly the integers. Hover over a name to see its type, click it to read its definition.

<div class="features">
<div><h3>A verified kernel</h3><p>Each definition is checked by a kernel whose functions return derivations in a formal specification of the theory. What it accepts is well formed by construction.</p></div>
<div><h3>A consistency proof</h3><p>A cubical-sets model in Lean validates every rule: no closed term of the empty type exists. It found seventeen bugs in earlier versions of the rules.</p></div>
<div><h3>A real language</h3><p>Implicit arguments and unification, nested pattern matching with coverage checking, higher inductive types, a REPL and a language server.</p></div>
<div><h3>Checked documentation</h3><p>Every snippet on this site is elaborated and kernel-certified when the site is built: the types you see on hover come from Kubus itself.</p></div>
</div>

## Learn more

- [The tutorial](tutorial/index.html) starts from functions and paths and ends with univalence, the circle and the consistency proof.
- [The library](lib/index.html) is rendered as hyperlinked source, with an index of definitions.
- [Trust](tutorial/11-trust.html) explains what is verified and what you need to read to believe it.
