### Verification of Dijkstra's Algorithm in Idris Language

This project provides the following: 
- **A detailed mathematical proof of Dijkstra's algorithm, which includes elaborating and proving lemmas and assumptions that are generally ignored/assumed**
- **An Idris implementation of Dijkstra's algorithm from scratch**, including: 
  - Idris implementation of **all definitions** used, such as graph, path, permutation, or even natural numbers. 
  - Implementaiton of **all data structures used**, such as priority queue
- **An Idris program that verifies the correctness of the Dijkstra's algorithm**, which includes 
  - Proof programs that **verifies the correctness of every data structures and concepts used**. 
      - Here are a few examples: 
        - [PriorityQueue.idr](https://github.com/EileenFeng/Verifying-Dijkstras-Algorithm-in-Idris/blob/master/code/PriorityQueue.idr) file provides an Idris implementation of the priority queue data structure, which is commonly used in implemeting Dijkstra's, along with code that proves the getMin function indeed returns the minimum value in the node. 
        - [CNat.idr](https://github.com/EileenFeng/Verifying-Dijkstras-Algorithm-in-Idris/blob/master/code/CNat.idr), [Perm.idr](https://github.com/EileenFeng/Verifying-Dijkstras-Algorithm-in-Idris/blob/master/code/Perm.idr) provides program that implements and proofs natural number and permutation properties.
  - **Programs that proves all lemmas and assumptions**
      - As an example, [this part of the Dijkstras.idr file](https://github.com/EileenFeng/Verifying-Dijkstras-Algorithm-in-Idris/blob/master/code/Dijkstras.idr#L539-L744) is a intricate, yet very interesting, implementation and proof of one of the most important lemmas in our Dijkstra's verification program.
  - **Finally, an Idris program that verifies DIjkstra's correctness**
      - [Idris verification of Dijkstra's](https://github.com/EileenFeng/Verifying-Dijkstras-Algorithm-in-Idris/blob/master/code/Dijkstras.idr#L764-L785) is a short, succint function, yet it is built on top of many other ugly, complicated proofs included in this repo :) 
- ***A [complete, 50 pages write-up](https://github.com/EileenFeng/Verifying-Dijkstras-Algorithm-in-Idris/blob/master/writing/final_draft.pdf)*** **that provides a detailed mathematical proofs that backs up the verification program, along with elaboration on the verification program details, discussions, and future works.**
