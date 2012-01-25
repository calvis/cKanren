;; -*- scheme -*-

;; This library provides compatibility with various scheme implementations.

(library (compat)
  (export pretty-print make-parameter printf)
  (import (only (chezscheme) pretty-print make-parameter printf)))
