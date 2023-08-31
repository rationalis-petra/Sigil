# Source Direcotry


## sigil
The sigil subdirectory contains most of the details of the implementation of the
sigil language. It mostly leaves out IO in favour of offering various components
(typechecker, compiler, interpreter etc.) that can be plugged together to
perform various different tasks (compilation, run a file, launch a REPL, provide
a language server etc.). These components are used in the `app` directory in the
project root.


## Prettyprinter
The `Prettyprinter/sigil` subdirectory contains expands upon the `Doc ann` type
from the prettyprinter library to provide a specific set of document stylings
(notably colour) that can be used in messages reported to the user.

## Backtrack
`Backtrack.hs` provides a very simple backtracking monad transformer, primarily
used by the unification algorithm.

