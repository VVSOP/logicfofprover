module Codec.TPTP(
                  module Codec.TPTP.Base
                 ,module Codec.TPTP.Import
                 ,module Codec.TPTP.Pretty
                 ,module Codec.TPTP.Export
                 ,module Codec.TPTP.Diff
                 )
    where

import Codec.TPTP.Base
import Codec.TPTP.Pretty
import Codec.TPTP.Import
import Codec.TPTP.Export
import Codec.TPTP.Diff

import Data.Functor.Identity

t_a = parse "fof(test,axiom,~(a&b))."
t_b = parse "fof(test,axiom,(~a&b))."
t_negate =  parse "fof(test,axiom,a)."
t_negate2 = parse "fof(test,axiom,~a)."
t_eq = parse "fof(test,axiom,a<=>b)."
t_quant = parse "fof(test,axiom,? [A,Y] :fix(A))."
t_pred = parse "fof(test,axiom,fix(A,B))."
t_doublenegation = parse "fof(test,axiom,~(~(a)))."
t_scf1 = parse "fof(test,axiom,a&(b|c)&c)."
t_scf2 = parse "fof(test,axiom,a~&b)."
t_scf3 = parse "fof(test,axiom,~(a&b))."
t_scf4 = parse "fof(test,axiom,(a&~(x&y))=>d)."

--Listof AFOrmula
get_list_element (x:xs)= x

--always used first
get_formula (AFormula a b c d) = c

enter_formula (F x) = x

enter_identity (Identity x) = x

enter_binop (BinOp a x b) =  a

step x = enter_binop(enter_identity(enter_formula(x)))

walk_t [] = []
walk_t ((T (Identity ( Var v))):[]) = ((T (Identity( Var v))):[])
walk_t ((T (Identity ( Var v))):xs) = ((T (Identity( Var v))):walk_t(xs))

walk_f (F (Identity (Quant All cont op1)))		= (F (Identity (Quant All cont (walk_f(op1)))))
walk_f (F (Identity (Quant Exists cont op1)))	= (F (Identity (Quant Exists cont (walk_f(op1)))))
walk_f (F (Identity (PredApp aw t)))			= (F (Identity (PredApp aw (walk_t(t)))))
walk_f (F (Identity ((:~:) op1)))				= (F (Identity ((:~:) (walk_f(op1)))))
walk_f (F (Identity (BinOp op1 (:<=>:) op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:<=>:) (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:<=:)  op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:<=:)  (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:=>:)  op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:=>:)  (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:<~>:) op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:<~>:) (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:~|:)  op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:~|:)  (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:~&:)  op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:~&:)  (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:&:)   op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:&:)   (walk_f(op2)))))
walk_f (F (Identity (BinOp op1 (:|:)   op2))) 	= (F (Identity (BinOp (walk_f(op1)) (:|:)   (walk_f(op2)))))



--main
scf x = scf_top(get_formula(get_list_element(x)))

--top level (conjunctions)
scf_top (F (Identity (BinOp op1 (:&:) op2)))= (F (Identity (BinOp (scf_top(op1)) (:&:) (scf_top(op2)))))
scf_top (F (Identity (PredApp aw t))) = (F (Identity (PredApp aw t)))
scf_top (F (Identity ((:~:) (F (Identity (PredApp aw t)))))) = (F (Identity ((:~:) (F (Identity (PredApp aw t))))))
scf_top (F (Identity( (:~:) (F (Identity( ((:~:) op1))))))) = scf_top(op1)
scf_top x = scf_wrap(scf_dis_b (x,[]))

--transformation level (disjunctions)

--anchor
scf_dis_b ((F (Identity (PredApp aw t))),path) 							= ((F (Identity (PredApp aw t))) 							,path)
scf_dis_b ((F (Identity ((:~:) (F (Identity (PredApp aw t)))))),path) 	= ((F (Identity ((:~:) (F (Identity (PredApp aw t)))))) 	,path)

--beta
scf_dis_b ((F (Identity (BinOp op1 (:|:) op2))) 						,path) = scf_merge(scf_dis_b(op1,path++["L"]),scf_dis_b(op2,path++["R"]),(F (Identity (BinOp op1 (:|:) op2))),path)
scf_dis_b ((F (Identity ((:~:) (F (Identity (BinOp op1 (:~|:) op2)))))) ,path) = scf_merge(scf_dis_b(op1,path++["L"]),scf_dis_b(op2,path++["R"]),(F (Identity (BinOp op1 (:|:) op2))),path)
scf_dis_b ((F (Identity( (:~:) (F (Identity( ((:~:) op1))))))) 			,path) = scf_dis_b (op1,path)
scf_dis_b ((F (Identity (BinOp op1 (:=>:) op2))) 						,path) = scf_dis_b ((F (Identity (BinOp (scf_negate(op1)) (:|:) op2))) 				,path)
scf_dis_b ((F (Identity (BinOp op1 (:<=:) op2))) 						,path) = scf_dis_b ((F (Identity (BinOp op1 			  (:|:) (scf_negate(op2))))),path)
scf_dis_b ((F (Identity (BinOp op1 (:~&:)  op2)))						,path) = scf_dis_b ((F (Identity (BinOp (scf_negate(op1)) (:|:) (scf_negate(op2))))),path)
scf_dis_b ((F (Identity ((:~:) (F (Identity (BinOp op1 (:&:) op2)))))) 	,path) = scf_dis_b ((F (Identity (BinOp (scf_negate(op1)) (:|:) (scf_negate(op2))))),path)

--alpha
scf_dis_b ((F (Identity (BinOp op1 (:&:) op2)))							,path) = ((F (Identity (BinOp op1 (:&:) op2)))							,path++["A"])
scf_dis_b ((F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2))))))	,path) = ((F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2)))))) 	,path++["A"])
scf_dis_b ((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:)  op2)))))),path) = ((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:)  op2)))))) ,path++["A"])
scf_dis_b ((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:)  op2)))))),path) = ((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:)  op2)))))) ,path++["A"])
scf_dis_b ((F (Identity (BinOp op1 (:~|:)  op2)))						,path) = ((F (Identity (BinOp op1 (:~|:)  op2)))						,path++["A"])


scf_dis_aX (f,path) = (F (Identity (BinOp (scf_dis_aL(f,path)) (:&:) (scf_dis_aR(f,path)))))

scf_dis_aL ((F (Identity (BinOp op1 (:&:) op2)))						 ,x:[]) = op1
scf_dis_aL ((F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2))))))	 ,x:[]) = scf_negate(op1)
scf_dis_aL ((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:)  op2)))))),x:[]) = op1
scf_dis_aL ((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:)  op2)))))),x:[]) = scf_negate(op1)
scf_dis_aL ((F (Identity (BinOp op1 (:~|:)  op2)))						 ,x:[]) = scf_negate(op1)
scf_dis_aL ((F (Identity (BinOp op1 op op2)))							 ,x:xs)
	|x=="L" = (F (Identity (BinOp (scf_dis_aL(op1,xs)) op op2)))
	|x=="R" = (F (Identity (BinOp op1 op (scf_dis_aL(op2,xs)))))

scf_dis_aR ((F (Identity (BinOp op1 (:&:) op2)))						 ,x:[]) = op2
scf_dis_aR ((F (Identity ((:~:) (F (Identity (BinOp op1 (:|:) op2))))))	 ,x:[]) = scf_negate(op2)
scf_dis_aR ((F (Identity ((:~:) (F (Identity (BinOp op1 (:=>:)  op2)))))),x:[]) = scf_negate(op2)
scf_dis_aR ((F (Identity ((:~:) (F (Identity (BinOp op1 (:<=:)  op2)))))),x:[]) = op2
scf_dis_aR ((F (Identity (BinOp op1 (:~|:)  op2)))						 ,x:[]) = scf_negate(op2)
scf_dis_aR ((F (Identity (BinOp op1 op op2)))							 ,x:xs)
	|x=="L" = (F (Identity (BinOp (scf_dis_aR(op1,xs)) op op2)))		
	|x=="R" = (F (Identity (BinOp op1 op (scf_dis_aR(op2,xs)))))

--utility
scf_wrap (f,path)
	|last path =="A" 	= scf_dis_aX(f,path)
	|otherwise 			= f

scf_merge ((f1,path1),(f2,path2),(F (Identity (BinOp op1 (:|:) op2))),path)
	|last path1 =="A"	= ((F (Identity (BinOp f1  (:|:) op2))),path1)
	|last path2 =="A"	= ((F (Identity (BinOp op1 (:|:) f2 ))),path2)
	|otherwise 			= ((F (Identity (BinOp op1 (:|:) op2))),path)

scf_negate x = (F (Identity ((:~:) x)))
