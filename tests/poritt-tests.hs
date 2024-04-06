module Main (main) where

import Control.Exception (handle)
import Control.Monad     (forM, void)
import Data.List         (sort)
import System.Directory  (doesDirectoryExist, doesFileExist, listDirectory, setCurrentDirectory)
import System.Exit       (ExitCode (..))
import System.FilePath   (dropExtension, takeExtension, takeFileName, (-<.>), (</>))
import System.IO         (Handle, IOMode (WriteMode), hPutStrLn, withFile)
import System.IO.Temp    (withSystemTempDirectory)
import Test.Tasty        (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden (goldenVsFileDiff)

import PoriTT.Distill (DistillOpts (..))
import PoriTT.Main    (batchFile, builtinEnvironment)
import PoriTT.Opts    (Opts (..), ThreeWay (..), defaultOpts)
import PoriTT.PP      (PPOpts' (..))

main :: IO ()
main = do
    cwd
    examples <- sort . filter (\fn -> takeExtension fn == ".ptt") <$> listFilesRecursively "examples"
    withSystemTempDirectory "poritt-tests" $ \tmpDir -> do
        defaultMain $ testGroup "poritt" $ regroup
            [   ( goldenVsFileDiff (dropExtension ex) diff out tmp $
                    withFile tmp WriteMode $ \hdl -> do
                        env <- builtinEnvironment hdl opts
                        handle (exitCode hdl) $ void $ batchFile inp env

                , goldenVsFileDiff (dropExtension ex) diff out tmp $
                    withFile tmp WriteMode $ \hdl -> do
                        env <- builtinEnvironment hdl opts { elaborate = True }
                        handle (exitCode hdl) $ void $ batchFile inp env
                )
            | ex <- examples
            , let tmp = tmpDir </> takeFileName ex -<.> "tmp"
            , let out = "examples" </> ex -<.> "stdout"
            , let inp = "examples" </> ex
            ]
  where
    opts = defaultOpts
        { elaborate   = False
        , echo        = False
        , prettyOpts  = PPOpts { unicode = Always, colour = Never }
        , distillOpts = DistillOpts True True True True True
        }

    diff ref new = ["diff", "-u", ref, new]

    regroup :: [(TestTree, TestTree)] -> [TestTree]
    regroup xs = case unzip xs of
        (ys, zs) ->
            [ testGroup "conv" ys
            , testGroup "elab" zs
            ]

    exitCode :: Handle -> ExitCode -> IO ()
    exitCode hdl (ExitFailure _) = hPutStrLn hdl "ExitFailure"
    exitCode _ _               = return ()

listFilesRecursively :: FilePath -> IO [FilePath]
listFilesRecursively = go "" where
    go :: FilePath -> FilePath -> IO [FilePath]
    go pfx dir = do
        xs <- listDirectory dir
        fmap concat $ forM xs $ \x -> do
            does <- doesDirectoryExist (dir </> x)
            if does
            then go (pfx </> x) (dir </> x)
            else return [pfx </> x]

cwd :: IO ()
cwd = do
    here <- doesFileExist "poritt.cabal"
    if here then return () else setCurrentDirectory "poritt"
