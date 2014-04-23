let balayage = fun f1
  -> let f = elimination f1
     in let rec aux = fun l
	  -> match l with
	       [] -> false
	     | h::t -> let f2 = reductionFormule
				  (Et (attributionValeur f (fst h) True,
				       attributionValeur f (fst h) False))
		       in if f2 = Valeur True then true
			  else if reductionFormule
				    (Negation (f2)) = Valeur True
			  then true
			  else aux t
	in aux (listeVariables f);;
