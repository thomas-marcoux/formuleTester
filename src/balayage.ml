let f = Implique (Implique (Variable "p", Variable "q"), Variable "p");;
let rec eval = fun f1
  -> let f2 = reductionEquivalences f1
     in if f2 = f1 then f2 else eval f2;;
let balayage = fun f1
  -> let f = elimination f1
     in let rec aux = fun l
	  -> match l with
	       [] -> false
	     | h::t -> let f2 = eval (Et (attributionValeur f (fst h) True, attributionValeur f (fst h) False))
		       in if f2 = Valeur True then true
			  else if eval (Negation (f2)) = Valeur True
			  then true
			  else aux (suppVariable l h)
	in aux (listeVariables f);;
  balayage f;;
eval (elimination f);;
