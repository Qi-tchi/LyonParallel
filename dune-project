(lang dune 3.16)

(name LyonParallel)

(generate_opam_files true)

(source
 (github Qi-tchi/LyonParallel))

(authors "")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://github.com/Qi-tchi/LyonParallel/wiki)

(package
 (name LyonParallel)
 (synopsis "A short synopsis")
 (description "LyonParallel is a lightweight prototype for termination analysis of DPO rewriting systems on directed, edge-labeled multigraphs.  
Implemented in OCaml under the MIT license, it integrates four methods:  
(1) Well-founded semiring-based termination (Endrullis et al., ICGT 2024),  
(2) Non-well-founded semiring extensions (QIU, HAL report hal-04954960),  
(3) A subgraph-counting criterion (QIU, accepted at ICGT 2025),  
(4) An extension of the subgraph-counting criterion accounting antipatterns (QIU, HAL report hal-04973012).  ")
 (depends ocaml)
 (tags
  ("Graph Rewriting" "Termination" "Interpretation Method" "Subgraph Counting" "Automated Reasoning")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
