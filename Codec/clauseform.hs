import Codec.TPTP
import Data.Functor.Identity

getFormula :: [TPTP_Input] -> [[Formula]]
getFormula [(AFormula _ _ a _)] = [[a]]


--whether a form is alpha formisalphaForm (F (Identity (BinOp op1 (:&:) op2))) = True
isAlphaForm :: Formula -> Bool
isAlphaForm (F (Identity (BinOp op1 op op2)))
  |op == (:&:) = True
  |op == (:~|:) = True
  |otherwise = False
isAlphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 op op2))))))
  |op == (:|:) = True
  |op ==  (:=>:) = True
  |op == (:<=:) = True
  |op == (:~&:) = True
  |otherwise = False
--isAlphaForm ((F (Identity ((:~:) op))))
--  |op == (F (Identity (BinOp (_) (:|:) (_) ))) = True
isAlphaForm (F (Identity (ac))) = False  
--whether a form is beta form
isBetaForm :: Formula -> Bool
isBetaForm (F (Identity (BinOp op1 op op2))) 
  |op == (:|:) = True
  |op == (:=>:) = True
  |op == (:<=:) = True
  |op == (:~&:) = True
  |otherwise = False
isBetaForm (F (Identity ((:~:) (F (Identity (BinOp op1 op op2))))))
  |op == (:&:) = False
  |op == (:~|:) = False
  |otherwise = True
isBetaForm (F (Identity (ac))) = False  
-- type of   "~~formula"
--isDoubleNag (F (Identity ((:~:) ( F (Identity ((:~:) formula)))))) = True
--isDoubleNag (F (Identity (BinOp op1 op op2))) = False
--isDoubleNag  ( F (Identity ((:~:) formula))) = False
--doubleNag [(F (Identity ((:~:) ( F (Identity ((:~:) formula))))))] = [formula]
--doubleNag [(F (Identity ((:~:) formula)))] = [( F (Identity ((:~:) formula)))]
--doubleNag [(F (Identity (BinOp op1 op op2)))] = [(F (Identity (BinOp op1 op op2)))]
--doubleNag [(F (Identity ((:~:) (F (Identity (BinOp op1 op op2)))))) ] = [(F (Identity ((:~:) (F (Identity (BinOp op1 op op2)))))) ]

isAtomicWord :: AtomicWord->Bool
isAtomicWord _ = True

--alpha form
alphaForm (F (Identity (BinOp op1 (:&:) op2))) = [op1, op2]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2)))))) = [F (Identity ((:~:) op1)),F (Identity ((:~:) op2))]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:) op2)))))) = [op1, F (Identity ((:~:) op2))]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:) op2)))))) = [F (Identity ((:~:) op1)), op2]
alphaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:~&:) op2)))))) = [op1, op2]
alphaForm (F (Identity (BinOp op1 (:~|:) op2))) = [F (Identity ((:~:) op1)),F (Identity ((:~:) op2))]

--beta form
betaForm (F (Identity (BinOp op1 (:|:) op2))) = [op1, op2]
betaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:&:) op2)))))) = [F (Identity ((:~:) op1)),F (Identity ((:~:) op2))]
betaForm (F (Identity (BinOp op1 (:=>:) op2))) = [F (Identity ((:~:) op1)), op2]
betaForm (F (Identity (BinOp op1 (:<=:) op2))) = [op1,F (Identity ((:~:) op2))]
betaForm (F (Identity ((:~:) (F (Identity (BinOp op1 (:~|:) op2)))))) = [op1, op2]
betaForm (F (Identity (BinOp op1 (:~&:) op2))) = [F (Identity ((:~:) op1)),F (Identity ((:~:) op2))]

--delete element form list
deleteFromList _ [] = []
deleteFromList x (y:ys) | x== y = deleteFromList x ys
	    | otherwise = y : deleteFromList x ys

--add element to list
addToList1 y x = y ++ [x]
addToList2 y x z = y ++ [x] ++ [z]

isLiter [] = True
isLiter (x:xs) | not(isAlphaForm x) && not(isBetaForm x) && isLiter xs = True
	       | otherwise = False
--tableauxForm :: Formula -> Formula
tableauxForm formula = F (Identity ((:~:) formula))


--transform a formula to clause form 
tran f | isLiter f = [f]
tran (x:xs) 
	    | isAlphaForm x = t1++t2 
	    | isBetaForm x = t3
	    | otherwise = t4
		where 
		      [bop1,bop2] = betaForm (x)
		      [aop1,aop2] = alphaForm (x)	
		      s = deleteFromList x (x:xs)
		      t1 =  tran (s ++ [aop1])
		      t2 =  tran (s ++ [aop2])
		      t3 = tran (s++[bop1]++[bop2])
		      t4 = tran (xs++[x])
-- transform a formula to dual clause form
tranD f | isLiter f = [f]
tranD (x:xs) 
	    | isBetaForm x = t1++t2 
	    | isAlphaForm x = t3
	    | otherwise = t4
		where 
		      [bop1,bop2] = betaForm (x)
		      [aop1,aop2] = alphaForm (x)	
		      s = deleteFromList x (x:xs)
		      t1 =  tranD (s ++ [bop1])
		      t2 =  tranD (s ++ [bop2])
		      t3 = tranD (s++[aop1]++[aop2])
		      t4 = tranD (xs++[x])
isClosed ::[Formula]->[Formula]->Bool
isClosed (x:xs) list | ((elem x list) && (elem ( F (Identity ((:~:) x)))) list) = True
--  || isClosed xs list
