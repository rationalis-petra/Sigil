# Source Direcotry

This directory contains the bulk of the implementation of Glyph, Glaze and
Gdn. It is divided into 4 components:

+ **Glyph** provides tools for manipulating the Glyph programming language -
  typechecking, evaluation, compiltation etc.
+ **Glint** provides tools for manipulating the Glint document language,
  including a server for live glint documents.
+ **Glaze** provides the glaze build system, a build system specific to
  Glyph/Glint designed to provide reproducible builds.

Note that each Glyph mode (compilation/interactive/server) ties these components
together differently.

