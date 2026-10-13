# 2. Getting started

## Installing

Kubus is written in Lean 4. With [elan](https://github.com/leanprover/elan) installed:

```text
git clone https://github.com/mitschabaude-bot/kubus
cd kubus
lake build
export PATH="$PWD/.lake/build/bin:$PATH"
export KUBUS_PATH="$PWD/lib"
```

`KUBUS_PATH` tells Kubus where to find the library for `import`. Imports are also searched in the directory of the importing file.

## Checking a file

A Kubus file (`.ktt`) is a sequence of declarations: `def`, `data`, `import`, and the commands `#eval` and `#check`. Put this into `hello.ktt`:

```kubus
data Bool : U := false | true

def not : Bool -> Bool
  | false => true
  | true => false

def twice {A : U} (f : A -> A) (x : A) : A := f (f x)

#check twice
#eval twice not true
```

and run `kubus hello.ktt`. Kubus elaborates every declaration, prints the results of `#eval` (the normal form and its type) and `#check` (the term and its type), and certifies every definition with the kernel. It prints nothing else unless something goes wrong.

## The REPL

`kubus --interactive [FILES]` loads the files and reads declarations, commands and terms from standard input; a term on its own is evaluated. Definitions by pattern matching and data types end with an empty line.

```text
$ kubus --interactive lib/loopspace.ktt
kubus> winding (trans loopP loopP)
pos (suc (suc zero))
  : Int
kubus> #check sym
sym : {A : U} → {a b : A} → Path A a b → Path A b a
```

## Editor support

`editor/vscode` in the repository is a VS Code extension: syntax highlighting and a client for the language server `kubus --lsp`. The server checks the file as you type, shows errors at their precise location, `#eval` results and the goals of holes `?` inline, and types on hover.

```text
cd editor/vscode && npm install && npm run package
code --install-extension kubus-0.1.0.vsix
```

## Holes

A `?` in a term is a hole. Kubus reports the type it expects there (the *goal*) and the variables in scope, which makes it a good way to develop a proof step by step:

```kubus hole
def compose {A B C : U} (g : B -> C) (f : A -> B) : A -> C := \x -> ?
```

In the editor, a definition with holes is checked to the end; on the command line, the first hole is an error.
