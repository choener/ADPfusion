
module ADP.Fusion.Table where



-- | Mutable tables for memoization.
--
-- TODO Switch to an encoding using fully adaptive arrays. Cf. Manuel
-- Chakravarty's work (implemented in dph).

data MTable c es = MTable !es
