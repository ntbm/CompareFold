
module Main where

import Control.Applicative ( (<$>) )
import Control.Monad (forM_)
import System.Console.CmdArgs
import Text.Printf

import BioInf.CompareFold



data Options
  = Nussinov
    { coopts :: Int
    }
  deriving (Show,Data,Typeable)

oNussinov = Nussinov
  { coopts = 1 &= help "number of co-optimal backtracking results"
  }

main :: IO ()
main = do
  o <- cmdArgs $ modes [oNussinov]
  case o of
    Nussinov{..} -> do
      ls <- lines <$> getContents
      forM_ ls $ \l -> do
        let (r,bs) = pkfPairMax coopts l
        printf "PKF\t \t %s   %d\n" l r
        forM_ bs $ \[b] -> printf "PKF\t \t %s   %d\n" b r
        let (r,bs) = randgPairMax coopts l
        printf "RandG\t \t %s   %d\n" l r
        forM_ bs $ \[b] -> printf "RandG\t \t %s   %d\n" b r
        let (r,bs) = landpPairMax coopts l
        printf "LandP\t \t %s   %d\n" l r
        forM_ bs $ \[b] -> printf "LandP\t \t %s   %d\n" b r 
        let (r,bs) = landPplusPairMax coopts l
        printf "LandPplus\t %s   %d\n" l r
        forM_ bs $ \[b] -> printf "LandPplus\t %s   %d\n" b r
        let (r,bs) = candCPairMax coopts l
        printf "CandC\t \t %s   %d\n" l r
        forM_ bs $ \[b] -> printf "CandC\t\t %s   %d\n" b r
        let (r,bs) = dandpPairMax coopts l
        printf "DandP\t \t %s   %d\n" l r
        forM_ bs $ \[b] -> printf "DandP\t \t %s   %d\n" b r
