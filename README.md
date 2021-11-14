### Verification of Dijkstra's Algorithm in Idris Language

This project provides the following: 
- A detailed mathematical proof of Dijkstra's algorithm, which **includes elaborating and proving lemmas and assumptions that are generally ignored/assumed**
- **An Idris implementation of Dijkstra's algorithm from scratch**, including: 
  - Idris implementation of **all definitions** used, such as graph, path, permutation, or even natural numbers. 
  - Implementaiton of **all data structures used**, such as priority queue
- **An Idris program that verifies the correctness of the Dijkstra's algorithm**, which includes 
  - **Proof programs that verifies the correctness of every data structures used**. 
      - For instance, priority queue is one of the common data structures used in implementing Dijkstra's algorithm, and this [PriorityQueue.idr](https://github.com/EileenFeng/Verifying-Dijkstras-Algorithm-in-Idris/blob/master/code/PriorityQueue.idr) file provides an Idris implementation of the priority queue data structure, along with code that proves the getMin function indeed returns the minimum value in the node. 
  - **Programs that proves all lemmas
  - 
- A complete write-up that provides a detailed mathematical proofs that backs up the verification program, along with elaboration on the 
