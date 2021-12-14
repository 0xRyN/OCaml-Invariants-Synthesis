(declare-fun Invar (Int Int) Bool)
(assert (Invar 0 0))
(assert (forall (( x Int ) ( y Int )) (=> (and (Invar x y) (< x 3)) (Invar (+ x 1) (+ y 3)))))
(assert (forall (( x Int ) ( y Int )) (=> (and (Invar x y) (>= x 3)) (= y 9)))) 
(check-sat-using (then qe smt))
(get-model)
(exit)