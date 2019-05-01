# Code for the talk at DRADS'19

In this talk, I will introduce some basic concepts in Iris. Depending
on the how quickly it goes, I will try go through as many as possible
of the proofs of the examples below.


## Examples

- ```incr.v```:

  This example verifies a very simple program that allocates a
  reference with value 0, increments it and returns its value. We show
  that this program is safe and always returns the value 1 upon
  termination.


- ```linked_list.v```:

  This example verifies a standard linked-list reverse algorithm
  implemented with an accumulator.

- ```positive.v```:

  This example verifies a program in which consists of two
  threads. The program first allocates a reference with value 0. It
  then launches a thread that keeps incrementing this reference
  by 1. The main thread proceeds with an infinite loop and which
  checks that the value of stored in the global reference is always
  positive.

  This example uses a very simple invariant and no ghost theory to
  verify the safety of the aforementioned program.

- ```increasing.v```:

  This example verifies a program similar to the program in
  ```positive.v```.  The difference is that this program instead of
  checking positivity ensures checks that the global reference is
  increasing. It does this by checking reading keeping a local
  reference which starts with value 0.  In each iteration, the main
  thread checks that the global reference stores a value that is
  greater than the local value. If the value of the global reference
  turns out to be smaller, it will crash.  Otherwise, it stores the
  value read from the global reference into its local reference and
  repeats the checking process.

  This example uses an invariant together with a simple ghost theory to
  verify the safety of the aforementioned program.

- ```increasing_ghost.v```:

  Contains the ghost theory required for the verification of
  ```increasing.v```.

## Prerequisites

This code has been tested with the following versions:

- Coq 8.9 (https://github.com/coq/coq/releases/tag/V8.9.0)
- iris (https://gitlab.mpi-sws.org/iris/iris/) version: 0655aa19d67a1f8a364625bd8ecf5bb1ae0c2c75
- stdpp (https://gitlab.mpi-sws.org/iris/stdpp) version: 87b2fe62995413c6dea48c97c1ae4e8976f10d01
