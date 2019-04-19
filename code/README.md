# verified_functional_algorithms_idris
This file includes a summary of all the holes in the program, and a short analysis of the possible cause of restrictions in approaching each hole.

- Number of holes: 13
- Summary
  1. Due to unclear type error when match on the value of `inNodeset` using `with` rule:
    (1) Graph.idr:
        - `edgeEq` in function `edgeWEq`,
        - `adjSN` in function `adj_sameNode`
    (2) Dijkstras.idr
        - function `updateDistEqT`
        - function `updateDistEqF`
        - `l2` in function `l2_existPath`

  2. Due to the current definition of `mkdists` and `mkNodes` functions (hard to work with in proving)
    (1) Column.idr
        - `meq` in function `mkNodeEq`
    (2) Dijkstras.idr (most base cases)
        - `lemma2` and `base` in function `dijkstras_correctness`
        - `l5_unit` in function `l5_stm4` (base case for lemma 5 statement 4)
        - `l53Impossible` and `l53Base` in function `l5_stm3` (base cases for lemma 5 statement 3)
  3. Need to add additional construction on the input graph, but did not have enough time to design and modify the whole structure
    (1) Dijkstras.idr
        - `l51t` in function `l5_stm1`

- If granted additional 3-5 days, I might be able to resolve the following holes:
  (1) Dijkstras.idr
      - `l51t` in function `l5_stm1`
      - `lemma2` in function `dijkstras_correctness`
      - `l5_unit` in function `l5_stm4` (base case for lemma 5 statement 4)


- Other issues:
  - The `with` block in ` Dijkstras.l5_stm3` is still marked as incomplete for some unknown reasons, even though all possible cases are matched and implemented. I have tried to comment out each part and failed to figure out the reason why this is not total. Suspect this might be a potential error in Idris. 
