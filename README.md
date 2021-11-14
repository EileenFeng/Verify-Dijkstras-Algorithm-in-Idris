### Verification of Dijkstra's Algorithm in Idris Language

This project provides the following: 
- An Idris implementation of Dijkstra's algorithm
- An Idris program that verifies the correctness of the Dijkstra's implementation, which includes 
  - Data structure implementations, along with proof programs that verifies the specifications and correctness of every data structures used. For instance, priority queue is one of the common data structures used in implementing Dijkstra's algorithm, and this [PriorityQueue.idr](https://github.com/EileenFeng/Verifying-Dijkstras-Algorithm-in-Idris/blob/master/code/PriorityQueue.idr) file provides an Idris implementation of the priority queue data structure, along with code that proves that the getMin function indeed returns the minimum value in the node. 
- A complete write-up that provides a detailed mathematical proofs that backs up the verification program, along with elaboration on the 
