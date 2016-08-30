-- Knot free Grammar algorithm
module BioInf.CompareFold.PKF where

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

Grammar: PKF
N: S
{-
 - <U,2> is a split non-terminal.
 -
 - We explicitly introduce <U> and <V> as we want to have @pk1@ and @pk2@
 - in place. In principle, we could make use of an intermediate recursive
 - syntactic variable to ease the memory load, but this is simpler.
 -}
T: c
S: S
S -> unp <<< S c
S -> nil <<< e
//
Emit: PKF
|]
makeAlgebraProduct ''SigPKF

bpmax :: Monad m => SigPKF m Int Int Char
bpmax = SigPKF
  { unp = \ x c     -> 0
  , nil = \ ()      -> 0
  , h   = SM.foldl' max (-999999)
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

-- -- |
-- --
-- -- TODO It could be beneficial to introduce
-- -- @type Splitted = Either String (String,String)@
-- -- or something isomorphic. While [String] works, it allows for too many
-- -- possibilities here! ([] ist lightweight, on the other hand ...)
--
pretty :: Monad m => SigPKF m [String] [[String]] Char
pretty = SigPKF
  { unp = \ [x] c     -> [x ++ "."]
  , nil = \ ()      -> [""]
  , h   = SM.toList
  }
{-# INLINE pretty #-}
--
-- -- |
-- --
-- -- @
-- -- [{]}(())
-- -- caguagcu
-- -- [ ]
-- --  { }
-- --     (())
-- -- @

pkfPairMax :: Int -> String -> (Int,[[String]])
pkfPairMax k inp = (d, take k bs) where
  i = VU.fromList . Prelude.map toUpper $ inp
  n = VU.length i
  !(Z:.t) = runInsideForward i -- :._:._
  d = unId $ axiom t
  bs = runInsideBacktrack i (Z:.t) -- :.u:.v
{-# NOINLINE pkfPairMax #-}

type X = ITbl Id Unboxed Subword Int
type T = ITbl Id Unboxed (Z:.Subword:.Subword) Int

runInsideForward :: VU.Vector Char -> Z:.X-- :.T:.T
runInsideForward i = mutateTablesDefault -- WithHints (Proxy :: Proxy MonotoneMCFG)
                   $ gPKF bpmax
                        (ITbl 0 0 EmptyOk (PA.fromAssocs (subword 0 0) (subword 0 n) (-666999) []))
                        -- (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-777999) []))
                        -- (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.subword 0 0:.subword 0 0) (Z:.subword 0 n:.subword 0 n) (-888999) []))
                        (chr i)
  where n = VU.length i
{-# NoInline runInsideForward #-}

runInsideBacktrack :: VU.Vector Char -> Z:.X -> [[String]]-- :.T:.T -> [[String]]
runInsideBacktrack i (Z:.t) = unId $ axiom b -- :.u:.v) = unId $ axiom b
  where !(Z:.b) = gPKF (bpmax <|| pretty)  -- :._:._
                          (toBacktrack t (undefined :: Id a -> Id a))
                          -- (toBacktrack u (undefined :: Id a -> Id a))
                          -- (toBacktrack v (undefined :: Id a -> Id a))
                          (chr i)
{-# NoInline runInsideBacktrack #-}
