module Prover () where
import TPTP.Codec

t2 :: [TPTP_Input]->TPTP_Input
t2 (x:xs) = x

test:: [TPTP_Input]
test x = t2 (TPTP.Codec.parse x)