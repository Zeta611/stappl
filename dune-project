(lang dune 3.4)

(using menhir 2.1)

(name stappl)

(generate_opam_files true)

(source
 (github shapespeare/stappl))

(authors
  "Dohyung Kim"
  "Jaeho Lee"
  "Hyeonseo Yang")

(maintainers
  "Dohyung Kim"
  "Jaeho Lee"
  "Hyeonseo Yang")

(package
 (name stappl)
 (synopsis "Statically typed probabilistic programming language")
 (description "STAPPL is a statically typed probabilistic programming language")
 (depends
  (core (>= 0.16.2))
  (ppx_jane (>= 0.16.0))
  (menhir (>= 20231231))))
;(map_workspace_root false)

(license MIT)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
