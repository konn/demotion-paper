{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.List (sortOn)
import Data.List.Split (splitOn)
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.Directory
import System.Environment
import System.FilePath
import System.FilePath.Glob (compile, glob, globDir, globDir1, match)
import System.IO (IOMode (WriteMode), withFile)
import Text.LaTeX
import Text.LaTeX.Base.Class (comm1, comm3, liftL)
import Text.LaTeX.Base.Syntax

main :: IO ()
main = do
  [dir0] <- getArgs
  dir <- canonicalizePath dir0
  print dir
  matches <-
    sortOn (T.splitOn (T.singleton pathSeparator) . snd)
      . map (\t -> (t, fromMaybe (T.pack t) $ T.stripPrefix (T.pack dir <> "/") $ T.pack t))
      . concat
      <$> globDir ["**/*.hs", "**/*.cabal"] dir
  print matches
  lat <- execLaTeXT $ do
    preamble
    document $ do
      maketitle
      "Here, we give an anonymised, entire working implementation for the paper ``Functional Pearl: Constructive Arguments Must Be Guarded with Concrete Witness'', submitted to ICFP '21. The contents will be made available on GitHub after the review phase."

      mapM_ (uncurry colorFile) matches
  T.writeFile "supplement.tex" $ render lat

preamble :: Monad m => LaTeXT m ()
preamble = do
  documentclass [] "article"
  title "Suppelement: Working Codes"
  date ""
  usepackage [] "minted"
  usepackage ["gray"] "xcolor"
  usepackage [] "fontspec"
  textell $
    TeXComm
      "setmonofont"
      [OptArg "StylisticSet=3", FixArg "inconsolata"]
  usepackage ["libertine"] "newtxmath"
  usepackage ["tt=false"] "libertine"
  comm1 "setminted" "style=borland"
  textell $
    TeXComm
      "newminted"
      [ OptArg "code"
      , FixArg "haskell"
      , FixArg
          "mathescape,linenos,numbersep=5pt,\
          \frame=lines,framesep=2mm"
      ]

colorFile :: FilePath -> Text -> LaTeXT IO ()
colorFile fp name = do
  src <- liftIO $ T.readFile fp
  section $ texttt $ raw name
  raw "\n"
  let code = "code"
  liftL (TeXEnv code []) $ do
    raw "\n"
    raw src
    raw "\n"
  raw "\n"