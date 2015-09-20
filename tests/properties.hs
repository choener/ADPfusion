
-- | Test all properties automatically. We keep the QC2 modules in the main
-- library for now, as this allows for more efficient repl tests.

module Main where

import Test.Framework.Providers.QuickCheck2
import Test.Framework.TH

import qualified ADP.Fusion.QuickCheck.Subword  as QSW
import qualified ADP.Fusion.QuickCheck.Set      as QS
import qualified ADP.Fusion.QuickCheck.Point    as QP
import ADP.Fusion.QuickCheck.Point


{-
grep -o -e "^prop_[[:alnum:]_]*" ADP/Fusion/QuickCheck/Subword.hs | awk '{print $1"QSW", "=", "QSW."$1 }' | uniq
grep -o -e "^prop_[[:alnum:]_]*" ADP/Fusion/QuickCheck/Set.hs | awk '{print $1"QS", "=", "QS."$1 }' | uniq
grep -o -e "^prop_[[:alnum:]_]*" ADP/Fusion/QuickCheck/Point.hs | awk '{print $1"QP", "=", "QP."$1 }' | uniq
-}

-- subwords

prop_sv_OIQSW = QSW.prop_sv_OI
prop_sv_IOQSW = QSW.prop_sv_IO
prop_sv_OIIQSW = QSW.prop_sv_OII
prop_sv_IOIQSW = QSW.prop_sv_IOI
prop_sv_IIOQSW = QSW.prop_sv_IIO
prop_cOcQSW = QSW.prop_cOc
prop_ccOccQSW = QSW.prop_ccOcc
prop_cOcccQSW = QSW.prop_cOccc
prop_cOcIcQSW = QSW.prop_cOcIc
prop_cIcOcQSW = QSW.prop_cIcOc
prop_EpsilonQSW = QSW.prop_Epsilon

-- sets

prop_b_iiQS = QS.prop_b_ii
prop_b_ii_nnQS = QS.prop_b_ii_nn
prop_b_iiiQS = QS.prop_b_iii
prop_b_iii_nnnQS = QS.prop_b_iii_nnn
prop_bii_iQS = QS.prop_bii_i
prop_bii_i_nQS = QS.prop_bii_i_n
prop_bii_eQS = QS.prop_bii_e
prop_bii_ieQS = QS.prop_bii_ie
prop_bii_ie_nQS = QS.prop_bii_ie_n
prop_bii_ieeQS = QS.prop_bii_iee
prop_bii_ieeeQS = QS.prop_bii_ieee
prop_bii_iee_nQS = QS.prop_bii_iee_n
prop_bii_ieee_nQS = QS.prop_bii_ieee_n

-- points

prop_EpsilonQP = QP.prop_Epsilon
prop_O_EpsilonQP = QP.prop_O_Epsilon
prop_ZEpsilonQP = QP.prop_ZEpsilon
--prop_O_ZEpsilonQP = QP.prop_O_ZEpsilon
--prop_O_ZEpsilonEpsilonQP = QP.prop_O_ZEpsilonEpsilon
--prop_O_ItNCQP = QP.prop_O_ItNC
--prop_O_ZItNCQP = QP.prop_O_ZItNC
--prop_O_2dimIt_NC_CNQP = QP.prop_O_2dimIt_NC_CN
prop_2dimIt_NC_CNQP = QP.prop_2dimIt_NC_CN
prop_TtQP = QP.prop_Tt
prop_CCQP = QP.prop_CC
prop_ItQP = QP.prop_It
--prop_O_ItQP = QP.prop_O_It
prop_ZItQP = QP.prop_ZIt
--prop_O_ZItQP = QP.prop_O_ZIt
prop_ItCQP = QP.prop_ItC
--prop_O_ItCQP = QP.prop_O_ItC
--prop_O_ItCCQP = QP.prop_O_ItCC
--prop_O_ZItCCQP = QP.prop_O_ZItCC
prop_2dimItCCQP = QP.prop_2dimItCC
--prop_O_2dimItCCQP = QP.prop_O_2dimItCC
prop_ManySQP = QP.prop_ManyS
prop_SomeSQP = QP.prop_SomeS
prop_2dim_ManyS_ManySQP = QP.prop_2dim_ManyS_ManyS
prop_2dim_SomeS_SomeSQP = QP.prop_2dim_SomeS_SomeS
prop_Itbl_ManySQP = QP.prop_Itbl_ManyS
prop_Itbl_SomeSQP = QP.prop_Itbl_SomeS
prop_1dim_Itbl_ManySQP = QP.prop_1dim_Itbl_ManyS
prop_1dim_Itbl_SomeSQP = QP.prop_1dim_Itbl_SomeS
prop_2dim_Itbl_ManyS_ManySQP = QP.prop_2dim_Itbl_ManyS_ManyS
prop_2dim_Itbl_SomeS_SomeSQP = QP.prop_2dim_Itbl_SomeS_SomeS



main :: IO ()
main = $(defaultMainGenerator)

