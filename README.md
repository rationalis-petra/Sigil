# Sigil

Sigil is a small experimental dependently-typed language. 

From a theoretical perspective, Sigil aims to implement Higher Observational
Type Theory (HOTT). Future goals include extending the type system to include
higher inductive types, and allowing excluded middle to compute while
maintaining consistency.

## Usage

Sigil must be cloned and build with the haskell
[stack](https://docs.haskellstack.org/en/stable/) tool. From here, it can be
installed with `stack install` then run with `sigil <options>`, or, if you don't
want to install, run directly with `stack run -- <options>`. 

At the moment, only the 'interactive' mode is implemented, so for `<options>`
you'll need to substitute "interactive". This will drop you into a Terminal
Interface, from which you can evaluate expressions, run unification queries and
load modules.
+ To exit the program, make sure you are in normal mode `Esc` and hit `Space q q`
+ To learn more, look at the [tooling section](https://rationalis-petra.github.io/Sigil/tooling/index.html)  of the
  webpage. 
## Syntax

For an example of the syntax, see the
[github page](https://rationalis-petra.github.io/Sigil)
for this project, which has proper syntax highlighting. 

## Status
+ Can evaluate expressions, load files (modules) and run unification queries
  from the interactive interface.
+ Inductive datatypes are defined, but (propositional) equality is not
  impemented for them.
+ Univalent Propositional equality is partially implemented: reduction is
  implemented for the function-type, but the symmetry reduction rule/term is not.
+ Unification is partially implemented (not for propositional equality or
  recursion). The unification engine can be invoked directly via 'queries'.

## Known Issues
+ The universe system is a mess in general; level checks are often outright wrong and
  not (yet) based in the proper theory.
