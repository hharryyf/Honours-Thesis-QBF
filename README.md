# Thesis
Year 4 thesis project, modified the QBF solver coded in TOR

1. 1/6/2021: refactor the code, seperate the solver and data structure into different packages

2. 3/6/2021: implement the backjumping trick on QDLL

3. 7/6/2021: detect bugs in preprocessing, fixed

4. 11/6/2021: The implementation of the backjumping trick is complete for both the QDLL solver and the PNS solver,
all shows some not insignficant improvement. 

5. 14/6/2021: Update the "R" function for the deepPNS, significant improvement shown for the DeepPNS solver.
This shows a very signicicant improvement in the simpler gttt4x4 instances, half of the instances were solved by this little modification.

6. 29/6/2021: Implement a baseline version of the BOMH heuristic, combine with disable the SAT solver, 3 block group instances can be solved.
It seems like it is necessary to decide how to compute a more accurate set of reasons for the case when the SAT solver is called.

7. 29/8/2021: Two modifications were done: 

1) Adapt inversion quantifier block into the backjumping, and combine the SAT solver with the backjumping algorithm. After this modification, 6 to 10 out of 13 block group instances can be solved depends on different branching heuristics.

2) Add trivial truth and trivial false into preprocessing, the impl group becomes meaningless.

8. 3/9/2021: QCDCL preprocessor, not sure if the idea is correct

9. 7/10/2021: 2-watched-literal data structure for QBF implemented

Current solver strength (30 minutes for QDLL or 4000000 node expansions for DeepPNS):

CHAIN 12/12 (QDLL + DLCS heuristic)

BLOCK 6-10/13 (QDLL + Backjumping + SAT4j + DLCS/BHOM/DLIS/RAND heuristic)

comp 6/8 (QDLL/DeepPNS + Backjumping + SAT4j) -> 8/8 (QCDCL preprocess + Backjumping + SAT4j)

c432 4/8 (DeepPNS + Backjumping + trivial truth preprocessing + SAT4j)

k_dum_n 3/21 (QDLL + Backjumping + SAT4j)

k_dum_p 6/21 (QDLL + Backjumping + SAT4j)

k_lin_n 3/21 (QDLL + Backjumping + SAT4j) -> 4/21 (QCDCL preprocess + Backjumping + SAT4j)

k_lin_p 5/21 (QDLL + Backjumping + SAT4j) -> 21/21 (QCDCL preprocess + Backjumping + SAT4j)

k_path_n 3/21 (QDLL + Backjumping + SAT4j) -> 4/21 (QCDCL preprocess + Backjumping + SAT4j)

k_path_p 5/21 (QDLL + Backjumping + SAT4j) -> 21/21 (QCDCL preprocess + Backjumping + SAT4j)

k_d4_n 2/21  (QDLL + Backjumping + SAT4j) -> 3/21 (QCDCL preprocess + Backjumping + SAT4j)

k_d4_p 6/21  (QDLL + Backjumping + SAT4j) -> 21/21 (QCDCL preprocess + Backjumping + SAT4j)

k_ph_n 5/21 (QDLL + Backjumping)

k_ph_p 5/21 (QDLL + Backjumping)

term1 5/8 (QDLL + SAT4j + trivial truth preprocessing) -> 6/8 (QCDCL preprocess + Backjumping + SAT4j)

TOILET 5/5 (DeepPNS + Backjumping)

TREE 12/14 (QDLL + SAT4j + trivial truth preprocessing) -> 14/14 (QCDCL preprocess + Backjumping + SAT4j)

longn 0/2 -> 2/2 (QCDCL preprocess + Backjumping + SAT4j)

gttt4x4 encoded 52/95 (DeepPNS + Backjumping + SAT4j)



