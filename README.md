# DafnyProvers

**DafnyProvers** is a small collection of self‑contained Dafny programs that showcase how formal verification can be used to prove the functional correctness of classic algorithms and data‑structure operations. Every file compiles and verifies with the Dafny verifier, so you can explore not only how the algorithm works but also how to specify contracts, invariants and termination metrics in Dafny.

## Table of Contents

* [Prerequisites](#prerequisites)
* [Project Layout](#project-layout)
* [Quick Start](#quick-start)
* [File‑by‑file overview](#file-by-file-overview)

## Prerequisites

* **Dafny ≥ 4.0**
  Download from the [official releases](https://github.com/dafny-lang/dafny/releases) or install with `dotnet tool install --global dafny`.

Optional:

* **Visual Studio Code** with the Dafny extension for an IDE experience.

## Project Layout

```text
.
├── has_cycle_exercise.dfy   # Detect cycles in a singly‑linked list
├── heapsort-starter.dfy     # A fully‑verified implementation of heapsort
├── power.dfy                # Fast exponentiation (a^n) with proofs of correctness
├── primebuffer.dfy          # A simple buffer that stores prime numbers
├── simplesort.dfy           # Straightforward sorting algorithm (selection sort) and proof
└── README.md
```

## Quick Start

Clone the repository and verify all programs:

```bash
git clone https://github.com/AlexiaBojian1/DafnyProvers.git
cd DafnyProvers

# Verify every file
for f in *.dfy; do
  echo "Verifying $f"; dafny verify $f; done
```

To run a single file interactively in VS Code, open it and hit **Ctrl + Shift + B**.

## File‑by‑file overview

| File                         | What it demonstrates                                       | Key verification points                                                                               |
| ---------------------------- | ---------------------------------------------------------- | ----------------------------------------------------------------------------------------------------- |
| **has\_cycle\_exercise.dfy** | Floyd’s tortoise‑and‑hare cycle‑detection on linked lists. | Ghost state for visited nodes, lemma on eventual repetition.                                          |
| **heapsort-starter.dfy**     | In‑place heapsort.                                         | Heap representation predicate, loop invariants guaranteeing partial heap property, permutation lemma. |
| **power.dfy**                | Exponentiation‑by‑squaring (`pow(base, exp)`).             | Decreases clause for termination, lemma `powMul` showing multiplicative property.                     |
| **primebuffer.dfy**          | Circular buffer that stores the first *n* primes.          | Functional specification of primality, ensures buffer contents are exactly the first *n* primes.      |
| **simplesort.dfy**           | Minimalistic comparison‑based sort (selection/insertion).  | Sortedness predicate, permutation proof via multiset equality.                                        |

Feel free to open any file – each is heavily commented so you can follow the proof structure step by step.

