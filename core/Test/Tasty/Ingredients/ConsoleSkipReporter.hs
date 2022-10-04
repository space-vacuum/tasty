{-# LANGUAGE RankNTypes, ImplicitParams, MultiParamTypeClasses, FlexibleContexts #-}
module Test.Tasty.Ingredients.ConsoleSkipReporter
  ( -- SimSpace specific test skipping code
    consoleTestSkipReporter
  ) where

import Control.Concurrent.STM
import Control.Exception
import Control.Monad.Reader hiding (fail, reader)
import Control.Monad.State hiding (fail)
import Prelude hiding (EQ, fail)
import Text.Printf ( printf )
import qualified Data.IntMap as IntMap

import Data.List (isInfixOf)
import Data.Monoid (Any(..))
import Data.Typeable
import System.Console.ANSI
import System.IO
import qualified Data.Semigroup as Sem
import Test.Tasty.Ingredients.ConsoleReporter

-- NOTE: Tasty exposed-modules.
import Test.Tasty
import Test.Tasty.Options
import Test.Tasty.Patterns.Printer ( printAwkExpr )
import Test.Tasty.Runners
import Test.Tasty.Patterns.Types
import Test.Tasty.Providers.ConsoleFormat

--------------------------------------------------
-- TestOutput base definitions
--------------------------------------------------
-- {{{

applyHook :: ([TestName] -> Result -> IO Result) -> TestOutput -> TestOutput
applyHook hook = go []
  where
    go path (PrintTest name printName printResult) =
      PrintTest name printName (printResult <=< hook (name : path))
    go path (PrintHeading name printName printBody) =
      PrintHeading name printName (go (name : path) printBody)
    go path (Seq a b) = Seq (go path a) (go path b)
    go _ Skip = mempty

-- }}}

--------------------------------------------------
-- TestOutput modes
--------------------------------------------------
-- {{{
consoleOutput :: (?colors :: Bool) => TestOutput -> StatusMap -> IO ()
consoleOutput toutput smap =
  getTraversal . fst $ foldTestOutput foldTest foldHeading toutput smap
  where
    foldTest _name printName getResult printResult =
      ( Traversal $ do
          printName :: IO ()
          r <- getResult
          printResult r
      , Any True)
    foldHeading _name printHeading (printBody, Any nonempty) =
      ( Traversal $
          when nonempty $ do printHeading :: IO (); getTraversal printBody
      , Any nonempty
      )

consoleOutputHidingSuccesses :: (?colors :: Bool) => TestOutput -> StatusMap -> IO ()
consoleOutputHidingSuccesses toutput smap =
  void . getApp $ foldTestOutput foldTest foldHeading toutput smap
  where
    foldTest _name printName getResult printResult =
      Ap $ do
          printName :: IO ()
          r <- getResult
          if resultSuccessful r
            then do clearThisLine; return $ Any False
            else do printResult r :: IO (); return $ Any True

    foldHeading _name printHeading printBody =
      Ap $ do
        printHeading :: IO ()
        Any failed <- getApp printBody
        unless failed clearAboveLine
        return $ Any failed

    clearAboveLine = do cursorUpLine 1; clearThisLine
    clearThisLine = do clearLine; setCursorColumn 0

streamOutputHidingSuccesses :: (?colors :: Bool) => TestOutput -> StatusMap -> IO ()
streamOutputHidingSuccesses toutput smap =
  void . flip evalStateT [] . getApp $
    foldTestOutput foldTest foldHeading toutput smap
  where
    foldTest _name printName getResult printResult =
      Ap $ do
          r <- liftIO getResult
          if resultSuccessful r
            then return $ Any False
            else do
              stack <- get
              put []

              liftIO $ do
                sequence_ $ reverse stack
                printName :: IO ()
                printResult r :: IO ()

              return $ Any True

    foldHeading _name printHeading printBody =
      Ap $ do
        modify (printHeading :)
        Any failed <- getApp printBody
        unless failed $
          modify $ \stack ->
            case stack of
              _:rest -> rest
              [] -> [] -- shouldn't happen anyway
        return $ Any failed

-- }}}

--------------------------------------------------
-- Statistics
--------------------------------------------------
-- {{{


-- | Wait until
--
-- * all tests have finished successfully, and return 'True', or
--
-- * at least one test has failed, and return 'False'
statusMapResult
  :: Int -- ^ lookahead
  -> StatusMap
  -> IO Bool
statusMapResult lookahead0 smap
  | IntMap.null smap = return True
  | otherwise =
      join . atomically $
        IntMap.foldrWithKey f finish smap mempty lookahead0
  where
    f :: Int
      -> TVar Status
      -> (IntMap.IntMap () -> Int -> STM (IO Bool))
      -> (IntMap.IntMap () -> Int -> STM (IO Bool))
    -- ok_tests is a set of tests that completed successfully
    -- lookahead is the number of unfinished tests that we are allowed to
    -- look at
    f key tvar k ok_tests lookahead
      | lookahead <= 0 =
          -- We looked at too many unfinished tests.
          next_iter ok_tests
      | otherwise = do
          this_status <- readTVar tvar
          case this_status of
            Done r ->
              if resultSuccessful r
                then k (IntMap.insert key () ok_tests) lookahead
                else return $ return False
            _ -> k ok_tests (lookahead-1)

    -- next_iter is called when we end the current iteration,
    -- either because we reached the end of the test tree
    -- or because we exhausted the lookahead
    next_iter :: IntMap.IntMap () -> STM (IO Bool)
    next_iter ok_tests =
      -- If we made no progress at all, wait until at least some tests
      -- complete.
      -- Otherwise, reduce the set of tests we are looking at.
      if IntMap.null ok_tests
        then retry
        else return $ statusMapResult lookahead0 (IntMap.difference smap ok_tests)

    finish :: IntMap.IntMap () -> Int -> STM (IO Bool)
    finish ok_tests _ = next_iter ok_tests

-- }}}

--------------------------------------------------
-- Console test reporter
--------------------------------------------------
-- {{{


-- | A generalization of `consoleTestReporter` that takes a custom
-- test reporter function
consoleTestReporter' :: ((?colors :: Bool) => StatusMap -> Time -> IO Bool) -> Ingredient
consoleTestReporter' reporter = TestReporter consoleTestReporterOptions $ \opts tree ->
  let
    TestPattern pattern = lookupOption opts
    tests = testsNames opts tree
    hook = (return .) . appendPatternIfTestFailed tests pattern
    TestReporter _ cb = consoleTestReporterWithHook' hook reporter
  in cb opts tree

appendPatternIfTestFailed
  :: [TestName] -- ^ list of (pre-intercalated) test names
  -> Maybe Expr -- ^ current pattern, if any
  -> [TestName] -- ^ name of current test, represented as a list of group names
  -> Result     -- ^ vanilla result
  -> Result
appendPatternIfTestFailed [_] _ _ res = res -- if there is only one test, nothing to refine
appendPatternIfTestFailed _ _ [] res  = res -- should be impossible
appendPatternIfTestFailed tests currentPattern (name : names) res = case resultOutcome res of
  Success -> res
  Failure{} -> res { resultDescription = resultDescription res ++ msg }
  where
    msg = "\nUse -p '" ++ escapeQuotes (printAwkExpr pattern) ++ "' to rerun this test only."

    escapeQuotes = concatMap $ \c -> if c == '\'' then "'\\''" else [c]

    findPattern [_] pat _ = ERE pat
    findPattern _  pat [] = EQ (Field (IntLit 0)) (StringLit pat)
    findPattern ts pat (n : ns) = let pat' = n ++ '.' : pat in
      findPattern (filter (pat' `isInfixOf`) ts) pat' ns

    individualPattern = findPattern (filter (name `isInfixOf`) tests) name names

    pattern = maybe id And currentPattern individualPattern

consoleTestReporterOptions :: [OptionDescription]
consoleTestReporterOptions =
  [ Option (Proxy :: Proxy Quiet)
  , Option (Proxy :: Proxy HideSuccesses)
  , Option (Proxy :: Proxy UseColor)
  , Option (Proxy :: Proxy AnsiTricks)
  ]

-- | A generalization of `consoleTestReporterWithHook` that takes a custom
-- test reporter function
consoleTestReporterWithHook' :: ([TestName] -> Result -> IO Result) -> ((?colors :: Bool) => StatusMap -> Time -> IO Bool) -> Ingredient
consoleTestReporterWithHook' hook reporter = TestReporter consoleTestReporterOptions $
  \opts tree -> Just $ \smap -> do

  let
    whenColor = lookupOption opts
    Quiet quiet = lookupOption opts
    HideSuccesses hideSuccesses = lookupOption opts
    NumThreads numThreads = lookupOption opts
    AnsiTricks ansiTricks = lookupOption opts

  if quiet
    then do
      b <- statusMapResult numThreads smap
      return $ \_time -> return b
    else

      do
      isTerm <- hSupportsANSI stdout
      isTermColor <- hSupportsANSIColor stdout

      (\k -> if isTerm
        then (do hideCursor; k) `finally` showCursor
        else k) $ do

          hSetBuffering stdout LineBuffering

          let
            ?colors = useColor whenColor isTermColor

          let
            toutput = applyHook hook $ buildTestOutput opts tree

          case () of { _
            | hideSuccesses && isTerm && ansiTricks ->
                consoleOutputHidingSuccesses toutput smap
            | hideSuccesses ->
                streamOutputHidingSuccesses toutput smap
            | otherwise -> consoleOutput toutput smap
          }

          return $ reporter smap


-- }}}

--------------------------------------------------
-- Various utilities
--------------------------------------------------
-- {{{
getResultFromTVar :: TVar Status -> IO Result
getResultFromTVar var =
  atomically $ do
    status <- readTVar var
    case status of
      Done r -> return r
      _ -> retry

-- }}}

--------------------------------------------------
-- Formatting
--------------------------------------------------
-- {{{

-- (Potentially) colorful output
ok, fail :: (?colors :: Bool) => String -> IO ()
fail     = output failFormat
ok       = output okFormat

output
  :: (?colors :: Bool)
  => ConsoleFormat
  -> String
  -> IO ()
output format = withConsoleFormat format . putStr

-- }}}

--------------------------------------------------
-- SimSpace skip reporting code
--------------------------------------------------
-- {{{

consoleTestSkipReporter :: Ingredient
consoleTestSkipReporter = consoleTestReporter' skipReporter

skipReporter :: (?colors :: Bool) => StatusMap -> Time -> IO Bool
skipReporter smap time = do
  stats <- computeSkipStatistics smap
  printSkipStatistics stats time
  return $ skipStatTotal stats - skipStatSuccess stats == 0

data SkipStatistics = SkipStatistics
  { skipStatTotal :: !Int -- ^ Number of active tests (e.g., that match the
                      -- pattern specified on the commandline), inactive tests
                      -- are not counted.
  , skipStatFailures :: !Int -- ^ Number of active tests that failed.
  , skipStatSuccess :: !Int -- ^ Number of active tests that succeeded
  }

instance Sem.Semigroup SkipStatistics where
  SkipStatistics t1 f1 s1 <> SkipStatistics t2 f2 s2 = SkipStatistics (t1 + t2) (f1 + f2) (s1 + s2)
instance Monoid SkipStatistics where
  mempty = SkipStatistics 0 0 0

computeSkipStatistics :: StatusMap -> IO SkipStatistics
computeSkipStatistics =
  getApp . foldMap (\var -> Ap $
    (\r -> SkipStatistics
             1
             (if not (resultSuccessful r) && resultShortDescription r /= "SKIP" then 1 else 0)
             (if resultSuccessful r then 1 else 0)
    )
      <$> getResultFromTVar var)

reportSkipStatistics :: (?colors :: Bool) => SkipStatistics -> IO ()
reportSkipStatistics st = case skipStatTotal st - skipStatSuccess st of
    0 -> ok $ printf "All %d tests passed" (skipStatTotal st)
    _ -> fail $ printf
                  "%d failed and %d skipped out of %d tests"
                  (skipStatFailures st)
                  (skipStatTotal st - skipStatFailures st - skipStatSuccess st)
                  (skipStatTotal st)

printSkipStatistics :: (?colors :: Bool) => SkipStatistics -> Time -> IO ()
printSkipStatistics st time = do
  printf "\n"
  reportSkipStatistics st
  case skipStatTotal st - skipStatSuccess st of
    0 -> ok $ printf " (%.2fs)\n" time
    _ -> fail $ printf " (%.2fs)\n" time

-- }}}