-- Dirks and Pierce Pseudoknot Grammar Class
module BioInf.CompareFold.DandP where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.ST
import           Data.Char (toUpper,toLower)
import           Data.List
import           Data.Vector.Fusion.Util
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
--import qualified Data.Vector.Fusion.Stream as S
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           Text.Printf

import           ADP.Fusion.Subword
import           Data.PrimitiveArray as PA hiding (map)

import           FormalLanguage

-- | Define signature and grammar

[formalLanguage|
Verbose

Grammar: DandP
N: S
N: <T,2>
N: <U,2>
T: c
S: S
S -> unp <<< c S
S -> nil <<< e
S -> jux <<< c S c S
S -> pse <<< T U T U
<U,U> -> dum <<< <T,T>
<T,T> -> nest <<< [-,c] [-,S] <T,T> [c,-] [S,-]
<T,T> -> jux2 <<< [c,-] [S,-] [-,c] [-,S]

//
Emit: DandP
|]
makeAlgebraProduct ''SigDandP

bpmax :: Monad m => SigDandP m Int Int Char Char
bpmax = SigDandP
  { unp   = \ c x                   -> x
  , nil   = \ ()                    -> 0
  , jux   = \ c x d y               -> if c `pairs` d then x + y + 1 else -999999
  , pse   = \ () () t u     -> t + u
  , dum   = \ y -> y
  , nest  = \ (Z:.():.a) (Z:.():.s1) t (Z:.b:.()) (Z:.s2:.()) -> if a `pairs` b then s1 + s2 + t + 1 else -888888
  , jux2  = \ (Z:.a:.()) (Z:.s1:.())   (Z:.():.b) (Z:.():.s2) -> if a `pairs` b then s1 + s2 + 1 else -777777
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

pretty :: Monad m => SigDandP m [String] [[String]] Char Char
pretty = SigDandP
  { unp   = \ c [x] -> ["." ++ x]
  , jux   = \ c [x] d  [y] -> ["(" ++ x ++ ")" ++ y]
  , pse   = \ () () [t1,t2] [u1,u2] -> [t1 ++ u1 ++ t2 ++ u2]
  , nil   = \ () -> [""]
  , dum   = \ [t1,t2] -> [t1, t2]
  , nest  = \ (Z:.():.a) (Z:.():.[s1]) [t1,t2] (Z:.b:.()) (Z:.[s2]:.()) ->  [ t1 ++ "{" ++ s1, "}" ++ s2 ++ t2]
  , jux2  = \ (Z:.a:.()) (Z:.[s1]:.()) (Z:.():.b) (Z:.():.[s2]) -> [ "(" ++ s1 , ")" ++ s1]
  , h     = SM.toList
}
{-# INLINE pretty #-}

dandpPairMax :: Int -> String -> (Int, [[String]])
dandpPairMax k inp =
  (d, take k bs) where
   i = VU.fromList . Prelude.map toUpper $ inp
   n = VU.length i
   !(Z:.t:.u:.v) = runInsideForward i
   d = unId $ axiom t -- Start Symbol
   bs = runInsideBacktrack i (Z:.t:.u:.v)
{-# NOINLINE dandpPairMax #-}


type X = TwITbl Id Unboxed EmptyOk (Subword I) Int
type T = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int


runInsideForward :: VU.Vector Char -> Z:.X:.T:.T
runInsideForward i =
  mutateTablesWithHints (Proxy :: Proxy MonotoneMCFG)
                   $ gDandP bpmax
                        (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-666999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-777999) []))
                        (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-888999) []))
                        (chr i)
                        (chr i)
  where n = VU.length i
{-# NoInline runInsideForward #-}

type X' = TwITblBt Unboxed EmptyOk (Subword I) Int Id Id [String]
type T' = TwITblBt Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Subword I:.Subword I) Int Id Id [String]

runInsideBacktrack :: VU.Vector Char -> Z:.X:.T:.T -> [[String]]
runInsideBacktrack i (Z:.t:.u:.v) =
  -- error "Not Implemented"
  unId $ axiom b -- StartSymbol
  where !(Z:.b:._:._) = gDandP (bpmax <|| pretty)
                          (toBacktrack t (undefined :: Id a -> Id a))
                          (toBacktrack u (undefined :: Id a -> Id a))
                          (toBacktrack v (undefined :: Id a -> Id a))
                          (chr i)
                          (chr i)
                          :: Z:.X':.T':.T'
{-# NoInline runInsideBacktrack #-}
