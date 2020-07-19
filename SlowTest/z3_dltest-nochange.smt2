(simplifier :num-exprs 8 :num-asts 172 :time 0.00 :before-memory 2.95 :after-memory 2.95)
(simplifier :num-exprs 8 :num-asts 172 :time 0.00 :before-memory 2.95 :after-memory 2.95)
(propagate-values :num-exprs 8 :num-asts 172 :time 0.00 :before-memory 2.95 :after-memory 2.95)
(ctx-simplify :num-steps 20)
(ctx-simplify :num-exprs 8 :num-asts 172 :time 0.00 :before-memory 2.95 :after-memory 2.95)
(simplifier :num-exprs 8 :num-asts 172 :time 0.00 :before-memory 2.95 :after-memory 2.95)
(solve_eqs :num-exprs 8 :num-asts 172 :time 0.00 :before-memory 2.95 :after-memory 2.95)
(elim-uncnstr-vars :num-exprs 8 :num-asts 172 :time 0.00 :before-memory 2.95 :after-memory 2.95)
(simplifier :num-exprs 12 :num-asts 178 :time 0.00 :before-memory 2.95 :after-memory 2.95)
(ilp-model-finder-tactic start)
(propagate-ineqs :num-exprs 12 :num-asts 184 :time 0.00 :before-memory 2.95 :after-memory 2.95)
(no-cut-smt-tactic start)
(smt.tactic start)
(smt.propagate-values)
(smt.nnf-cnf)
(smt.reduce-asserted)
(smt.maximizing-bv-sharing)
(smt.reduce-asserted)
(smt.simplifier-done)
(smt.diff_logic: non-diff logic expression (+ x y))
(smt.searching)
(no-cut-smt-tactic done)
(:added-bounds 4)
(add-bounds :num-exprs 16 :num-asts 192 :time 0.00 :before-memory 2.90 :after-memory 2.90)
(lia2sat-tactic start)
(:bound-propagations 4)
(propagate-ineqs :num-exprs 16 :num-asts 198 :time 0.00 :before-memory 2.90 :after-memory 2.90)
(:normalized-bounds 2)
(normalize-bounds :num-exprs 15 :num-asts 224 :time 0.00 :before-memory 2.90 :after-memory 2.90)
(:converted-lia2pb 2)
(lia2pb :num-exprs 88 :num-asts 289 :time 0.00 :before-memory 2.90 :after-memory 2.90)
(pb2bv :num-exprs 72 :num-asts 310 :time 0.00 :before-memory 2.90 :after-memory 2.90)
(simplifier :num-exprs 71 :num-asts 315 :time 0.00 :before-memory 2.90 :after-memory 2.90)
(propagate-values :num-exprs 71 :num-asts 310 :time 0.00 :before-memory 2.90 :after-memory 2.90)
(solve_eqs :num-exprs 71 :num-asts 310 :time 0.00 :before-memory 2.90 :after-memory 2.90)
(max-bv-sharing :num-exprs 71 :num-asts 326 :time 0.00 :before-memory 2.90 :after-memory 2.90)
(bit-blaster :num-exprs 172 :num-asts 437 :time 0.00 :before-memory 2.90 :after-memory 2.90)
(aig :num-exprs 369 :num-asts 641 :time 0.00 :before-memory 2.90 :after-memory 3.00)
(ast-table :prev-capacity 1280 :capacity 640 :size 282)
(sat-status
  :inconsistent    false
  :vars            188
  :elim-vars       0
  :lits            1254
  :assigned        0
  :binary-clauses  360
  :ternary-clauses 178
  :clauses         0
  :del-clause      0
  :avg-clause-size 2.33
  :memory          3.09)
(sat.solver)
(lia2sat-tactic done)
(ilp-model-finder-tactic done)
sat
(model 
  (define-fun x () Int
    (- 14))
  (define-fun y () Int
    (- 9))
)
