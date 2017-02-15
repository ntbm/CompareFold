-- Reeder and Giegerich Pseudoknot Class
module BioInf.CompareFold.RandG where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.ST
import           Data.Char (toUpper,toLower)
import           Data.List
import           Data.Vector.Fusion.Util
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           Text.Printf

import           ADP.Fusion
import           Data.PrimitiveArray as PA hiding (map)

import           FormalLanguage

-- | Define signature and grammar

[formalLanguage|
Verbose

Grammar: RandG
N: S
N: <V,2>
N: <O,2>
T: c
S: S
S -> unp <<< c S
S -> nil <<< e
S -> jux <<< c S c S
S -> pse <<< O S V S O S V S
<O,O> -> pk1 <<< [c,-] <V,V> [-,c]
<V,V> -> pk2 <<< [c,-] <V,V> [-,c]
<V,V> -> pair1 <<< [c,c]
//
Emit: RandG
|]
makeAlgebraProduct ''SigRandG

bpmax :: Monad m => SigRandG m Int Int Char
bpmax = SigRandG
  { unp   = \ c x                   -> x
  , nil   = \ ()                    -> 0
  , jux   = \ c x d y               -> if c `pairs` d then x + y + 1 else -999999
  , pse   = \ () a () b o c v d     -> a + b + c + d + o + v
  , pk1 = \ (Z:.a:.()) y (Z:.():.b) -> if a `pairs` b then  y + 1 else -777777
  , pk2 = \ (Z:.a:.()) y (Z:.():.b) -> if a `pairs` b then  y + 1 else -777777
  , pair1 = \ (Z:.c:.d)             -> if c `pairs` d then 1 else -888888 -- \ (Z:.():.()) -> 0
  , h     = SM.foldl' max (-999999)
}
{-# INLINE bpmax #-}

pairs !c !d
  =  c=='A' && d=='U'
  || c=='C' && d=='G'
  || c=='G' && d=='C'
  || c=='G' && d=='U'
  || c=='U' && d=='A'
  || c=='U' && d=='G'
{-# INLINE pairs #-}

pretty :: Monad m => SigRandG m [String] [[String]] Char
pretty = SigRandG
  { unp   = \ c [x] -> [x ++ "."]
  , jux   = \ c [x] d  [y] -> ["(" ++ x ++ ")" ++ y]
  , pse   = \ () [s1] () [s2] [u1,u2] [s3] [v1,v2] [s4] -> [u1 ++ s1 ++ v1 ++ s2 ++ u2 ++ s3 ++ v2 ++ s4]
  , nil   = \ () -> [""]
  , h     = SM.toList
  , pk1 = \ (Z:.a:.()) [y1,y2] (Z:.():.b) -> ["[" ++ y1 , y2 ++ "]"]
  , pk2 = \ (Z:.a:.()) [y1,y2] (Z:.():.b) -> ["[" ++ y1 , y2 ++ "]"]
  , pair1 = \ (Z:.c1:.c2) -> ["[1"++"]1"] -- \ (Z:.():.()) -> ["",""]
}
{-# INLINE pretty #-}

randgPairMax :: Int -> String -> (Int, [[String]])
randgPairMax k inp =
  error "not implemented"
--   (d, take k bs) where
--    i = VU.fromList . Prelude.map toUpper $ inp
--    n = VU.length i
--    !(Z:.t:.u:.v:.w:.x) = runInsideForward i
--    d = unId $ axiom t
--    bs = runInsideBacktrack i (Z:.t:.u:.v)
-- {-# NOINLINE randgPairMax #-}


type X = ITbl Id Unboxed Subword Int
type T = ITbl Id Unboxed (Z:.Subword:.Subword) Int


runInsideForward :: VU.Vector Char -> Z:.X:.T:.T
runInsideForward i =
  error "not implemented"
  -- mutateTablesWithHints (Proxy :: Proxy MonotoneMCFG)
  --                  $ gRandG bpmax
  --                       (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-666999) []))
  --                       (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-777999) []))
  --                       (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-888999) []))
  --                       (chr i)
  -- where n = VU.length i
{-# NoInline runInsideForward #-}
runInsideBacktrack :: VU.Vector Char -> Z:.X:.T:.T -> [[String]]
runInsideBacktrack i (Z:.t:.u:.v) =
  error "Not Implemented"
  -- unId $ axiom b
--   where !(Z:.b:._:._) = gRandG (bpmax <|| pretty)
--                           (toBacktrack t (undefined :: Id a -> Id a))
--                           (toBacktrack u (undefined :: Id a -> Id a))
--                           (toBacktrack v (undefined :: Id a -> Id a))
--                           (chr i)
-- {-# NoInline runInsideBacktrack #-}
