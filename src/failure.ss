; Abstract over the representation of a failure stream, which is shared in common among many parts of the system including streams, states, and substitutions
(library (failure)
  (export failure failure?)
  (import (chezscheme))

  (define failure #f)
  (define failure? not))
