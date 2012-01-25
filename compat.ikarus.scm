;; -*- scheme -*-

;; This library provides compatibility with various scheme implementations.

(library (compat)
  (export pretty-print)
  (import (only (ikarus) pretty-print)))
