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

--Listof AFOrmula
t2 (x:xs)= x

t3 (AFormula a b c d) = c

t4 (F x) = x

t5 (Identity x) = x

t6 (BinOp a x b) = x

tt (AFormula a b (F (Identity(BinOp r x s))) d) = x

tb_negate_term x = x


tb_negate_binop (BinOp op1 (:&:) op2) = (BinOp (tb_negate_term(op1)) (:|:) (tb_negate_term(op2)))
tb_negate_binop (BinOp op1 (:|:) op2) = (BinOp (tb_negate_term(op1)) (:&:) (tb_negate_term(op2)))
