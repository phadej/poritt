module Main (main) where

import Control.Exception (handle)
import Control.Monad     (forM, void)
import Data.List         (sort)
import Data.Either (partitionEithers)
import System.Directory  (doesDirectoryExist, doesFileExist, listDirectory, setCurrentDirectory)
import System.Exit       (ExitCode (..))
import System.FilePath   (dropExtension, takeExtension, takeFileName, (-<.>), (</>))
import System.IO         (Handle, IOMode (WriteMode), hPutStrLn, withFile)
import System.IO.Temp    (withSystemTempDirectory)
import Test.Tasty        (TestTree, TestName, defaultMain, testGroup)
import Test.Tasty.Golden (goldenVsFileDiff)
import Data.Map (Map)

import qualified Data.Map as Map
import qualified Data.Aeson as A
import qualified Data.ByteString as BS

import PoriTT.Distill (DistillOpts (..))
import PoriTT.Main    (batchFile, builtinEnvironment)
import PoriTT.Opts    (Opts (..), ThreeWay (..), defaultOpts)
import PoriTT.PP      (PPOpts' (..))

main :: IO ()
main = do
    cwd
    tree' <- sort <$> fileTree "examples"
    tree <- readConfigs tree'
    withSystemTempDirectory "poritt-tests" $ \tmpDir -> do
        defaultMain $ testGroup "poritt"
            [ testGroup dir $ case Map.toList configs of
                [ ("", config) ] -> tests tmpDir dir config files
                configs' ->
                    [ testGroup name $ tests tmpDir dir config files
                    | (name, config) <- configs'
                    ]
            | (dir, configs, files) <- tree
            , not (null configs)
            ]
  where
    opts = defaultOpts
        { elaborate   = False
        , echo        = False
        , prettyOpts  = PPOpts { unicode = Always, colour = Never }
        , distillOpts = DistillOpts True True True True True
        }

    tests :: FilePath -> FilePath -> Config -> [FilePath] -> [TestTree]
    tests tmpDir dir config files =
        [ goldenVsFileDiff (dropExtension ex) diff out tmp $
            withFile tmp WriteMode $ \hdl -> do
                env <- builtinEnvironment hdl opts
                handle (exitCode config hdl) $ void $ batchFile inp env
        | ex <- files
        , let tmp = tmpDir </> takeFileName ex -<.> "tmp" -- TODO: variant
        , let out = dir </> ex -<.> "stdout"
        , let inp = dir </> ex                
        ]

diff :: FilePath -> FilePath -> [FilePath]
diff ref new = ["diff", "-u", ref, new]

exitCode :: Config -> Handle -> ExitCode -> IO ()
exitCode cfg hdl (ExitFailure _)
    | cfg.expectFailure = hPutStrLn hdl "ExitFailure"
    | otherwise         = fail "unexpected failure exit code"
exitCode cfg _   ExitSuccess  
    | cfg.expectFailure = fail "unexpected success exit code"
    | otherwise         = return ()

readConfigs :: [(FilePath, [FilePath])] -> IO [(FilePath, Map TestName Config, [FilePath])]
readConfigs = traverse $ \(dir, files) -> do
    let configFileName = "config.json"
    configs <-
        if configFileName `elem` files
        then do
            contents <- BS.readFile (dir </> configFileName)
            A.throwDecodeStrict contents 
        else return $ Map.singleton "" defaultConfig
    return (dir, configs, filter (\ex -> takeExtension ex == ".ptt") files)

fileTree :: FilePath -> IO [(FilePath, [FilePath])]
fileTree dir = do
    es <- listDirectory dir
    (recs, fs) <- fmap partitionEithers $ forM es $ \e -> do
        does <- doesDirectoryExist (dir </> e)
        if does
        then Left <$> fileTree (dir </> e)
        else return (Right e)

    return $ (dir, sort fs) : concat recs

-- | Change directory in multipackage projects
cwd :: IO ()
cwd = do
    here <- doesFileExist "poritt.cabal"
    if here then return () else setCurrentDirectory "poritt"

data Config = Config
    { expectFailure :: Bool
    }

defaultConfig :: Config
defaultConfig = Config
    { expectFailure = False
    }

instance A.FromJSON Config where
    parseJSON = A.withObject "Config" $ \obj -> pure Config
        <*> obj A..:? "expectFailure" A..!= False
 