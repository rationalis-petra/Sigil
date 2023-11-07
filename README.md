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
you'll need to substitute "interactive". This will drop you into a REPL, where
the following actions are available: 
+ Typing in a sigil expression will evaluate that expression, returning its'
  value and type (or an error)
+ `;q` will exit the REPL
+ `;load <filename>` will load the specified file, expecting it to be a module.
+ `;import <import-declaration>` will import symbols into the REPLs' namespace.

## Syntax

For an example of the syntax, see the
[github page](https://rationalis-petra.github.io/Sigil)
for this project, which has proper syntax highlighting. 

## Status
+ The runtime can evaluate and check both expressions in a REPL and files/modules.
+ Inductive datatypes are defined, but (propositional) equality is not
  impemented for them.
+ Propositional equality is partially implemented: reduction is implemented for
  the function-type, but the symmetry reduction rule/term is not (and, as above,
  not implemented for inductive datatypes).

## Known Issues
+ The universe system is a mess in general; level checks are often outright wrong and
  not (yet) based in the proper theory.
