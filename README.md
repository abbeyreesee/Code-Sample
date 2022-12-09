# Code Sample: SATSolver

 Solves an instance of the boolean satisfiability problem for boolean
 formulas in conjunctive normal form. 

    Boolean formulas in conjunctive normal form are represented as follows:
        1. a literal/boolean variable is of type: var = int
          e.g. x1 -> 1 ,  ¬x3 -> ~3
        2. a clause (an "OR" of literals) is represented as type: clause = var list
          e.g. (¬x1 ∨ x2) -> [~1, 2] 
        3. a cnf formula has type: formula = clause list
          e.g. (x1 ∨ ¬x3 ∨ ¬x5) ∧ (¬x1 ∨ x2) ∧ (¬x1 ∨ ¬x3 ∨ x4) ∧ (¬x1 ∨ ¬x2 ∨ x3)  ->
               [[1, ∼3, ∼5], [∼1, 2], [∼1, ∼3, 4], [∼1, ∼2, 3]]  
         
        4. an assignment to the variables is represented as type: assignment = var list
          e.g. assigning x1 = true, x2 = false, and x3 = true -> [1, ∼2, 3]
          
          
