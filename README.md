# Agda Graph Algorithms

A library of formally verified graph algorithms implemented in Agda with machine-checked correctness proofs.

## Features

- Finite graph representation with strong type safety
- Formally verified graph algorithms:
    - Depth-First Search (DFS) with proven termination
    - Topological Sort with correctness proofs
    - Graph traversal with path properties
- Extensive formal proofs:
    - Edge classification theorems
    - Path ordering properties
    - Reachability guarantees
    - Acyclicity verification

## Project Structure

```
src/
├── Algorithm/
│   ├── DFS.agda        - Depth-First Search with lexicographic path ordering
│   ├── TopoSort.agda   - Topological sorting with correctness proofs
│   └── Traversal.agda  - Graph traversal algorithms
└── Data/
    └── Core.agda       - Graph data structures and core operations
```

## Formal Verification

This project demonstrates how dependently-typed programming in Agda can be used to verify key properties of graph algorithms:

- Termination: All algorithms provably terminate on finite graphs
- Correctness: Algorithms satisfy their formal specifications
- Edge Classification: DFS edges are properly classified (tree/back/cross/forward)
- Ordering Properties: Proofs about lexicographical ordering of traversals

## Requirements

- Agda 2.6.2 or higher
- Agda standard library

## Building
Clone the repository and type-check the code with:

```bash
agda --safe src/Algorithm/TopoSort.agda
```

## References

[1] M. Erwig, "Inductive graphs and functional graph algorithms," Journal of Functional Programming, vol. 11, no. 5, pp. 467-492, 2001.