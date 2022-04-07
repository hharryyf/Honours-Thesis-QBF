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

The end of "informal" implementation

9. 7/10/2021: 2-watched-literal data structure for QBF implemented

10. 13/10/2021: 2-watched-literal + backjumping solver implemented, significant efficiency improvement

11. 18/10/2021: 2-watched-literal + cdcl + sbj solver implemented, the solver can equalize Quaffle and QUBE on some families

12. 15/2/2022: 2-watched-literal + qcdcl solver implemented, 2-watched-literal + backjumping + deeppns solver implemented, insignificant improvement

13. 17/2/2022: pure-literal-elimination for deeppns/dfs based backjumping solver added, significantly improved the deeppns + backjumping solver

14. 9/3/2022: deeppns + qcdcl solver implemented, it's correct, but not competitive with current state of art, might be competitive with 2004 solvers.

15. 15/3/2022: solution driven cube learning cannot be activated in deeppns solver, shutdown any cube learning

16. 22/3/2022: store the assertion clauses in tree nodes, could enable solution driven backjumping

There are two deeppns-based solvers with the following features respectively:

1) deeppns + backjumping + unit propagation (with 2-WL data structure) + pure literal elimination (with clause watching data structure)

2) deeppns + conflict-driven clause learning + solution-driven backjumping + unit propagation (with 2-WL data structure)

