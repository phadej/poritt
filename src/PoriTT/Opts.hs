module PoriTT.Opts (
    Opts (..),
    ThreeWay (..),
    DumpOpts (..),
    defaultOpts,
    parseOpts,
    parseOptsEndo,
) where

import Optics.Core (set, (%))

import qualified Options.Applicative as O

import PoriTT.Base
import PoriTT.Distill
import PoriTT.PP
import PoriTT.Simpl

-------------------------------------------------------------------------------
-- Options
-------------------------------------------------------------------------------

data ThreeWay = Always | Never | Auto deriving Show

data DumpOpts = DumpOpts
    { ps :: !Bool
    , rn :: !Bool
    , tc :: !Bool
    , st :: !Bool
    , si :: !Bool
    }
  deriving (Show, Generic)

data Opts = Opts
    { evalFull    :: !Bool  -- ^ Evaluate the terms fully
    , echo        :: !Bool  -- ^ Echo the poritt statements
    , dump        :: !DumpOpts
    , prettyOpts  :: !(PPOpts' ThreeWay)
    , elaborate   :: !Bool
    -- elaborateOpts ?
    , distill     :: !Bool
    , distillOpts :: !DistillOpts
    , simplify    :: !Bool
    , simplOpts   :: !SimplOpts
    }
  deriving (Show, Generic)

defaultOpts :: Opts
defaultOpts = Opts
    { evalFull = False
    , echo = False
    , dump = DumpOpts
        { ps = False
        , rn = False
        , tc = False
        , st = False
        , si = False
        }
    , prettyOpts = PPOpts
        { unicode = Auto
        , colour  = Auto
        }
    , elaborate = True
    -- , elaborateOpts = ...
    , distill = True
    , distillOpts = DistillOpts
        { listEnumFun  =  True
        , listPairUnit = True
        , conHeadEnum  = True
        , implicitApp  = False
        , implicitLam  = False
        }
    , simplify = True
    , simplOpts = SimplOpts
        { iters = 3
        }
    }

-------------------------------------------------------------------------------
-- Cli parsing
-------------------------------------------------------------------------------

setImplicit :: Bool -> Opts -> Opts
setImplicit b
    = set (#distillOpts % #implicitApp) b
    . set (#distillOpts % #implicitLam) b

optsP :: O.Parser [Opts -> Opts]
optsP = many $ asum
    [ O.flag' (set #evalFull True) $ O.long "eval-full" <> O.help "Normalise completely"
    , O.flag' (set #evalFull False) $ O.long "eval-part" <> O.help "Don't normalise spines (default)" <> O.hidden
    , O.flag' (set #echo True) $ O.long "echo" <> O.help "Echo commands"
    , O.flag' (set #echo False) $ O.long "no-echo" <> O.help "Don't echo commands" <> O.hidden

    -- pretty unicode and colour
    , fmap (set (#prettyOpts % #unicode)) $ O.option threeWayReader $ O.long "unicode" <> O.help "Use unicode syntax" <> O.metavar "always|never|auto"
    , fmap (set (#prettyOpts % #colour)) $ O.option threeWayReader $ O.long "colour" <> O.help "Use color output" <> O.metavar "always|never|auto"

    , O.flag' (set #elaborate True)  $ O.long "elaborate" <> O.help "Elaborate terms (default)" <> O.hidden
    , O.flag' (set #elaborate False) $ O.long "no-elaborate" <> O.help "Don't elaborate, only type-check terms"

    -- distillation options
    , O.flag' (set #distill True)  $ O.long "distill" <> O.help "Distill type-checked terms (default)" <> O.hidden
    , O.flag' (set #distill False) $ O.long "no-distill" <> O.help "Don't distill type-checked terms"

    , O.flag' (set (#distillOpts % #listEnumFun) False) $ O.long "no-distill-enumfun" <> O.help "Print functions from enum explicitly as switch"
    , O.flag' (set (#distillOpts % #listEnumFun) True)  $ O.long "distill-enumfun" <> O.help "Print functions from enum using list syntax" <> O.hidden
    , O.flag' (set (#distillOpts % #listPairUnit) False) $ O.long "no-distill-pairunit" <> O.help "Print nested pairs and unit explicitly"
    , O.flag' (set (#distillOpts % #listPairUnit) True)  $ O.long "distill-pairunit" <> O.help "Print nested pairs and unit using list syntax" <> O.hidden
    , O.flag' (set (#distillOpts % #conHeadEnum) False) $ O.long "no-distill-conlabel" <> O.help "Print con [:label args...] explicitly"
    , O.flag' (set (#distillOpts % #conHeadEnum) True)  $ O.long "distill-conlabel" <> O.help "Print con [:label args...] as :label args" <> O.hidden
    , O.flag' (setImplicit True)  $ O.long "print-implicit-args" <> O.help "Print implicit lambda abstractions and applications"
    , O.flag' (setImplicit False) $ O.long "no-print-implicit-args" <> O.help "Print implicit lambda abstractions and applications" <> O.hidden

    -- simplifier
    , O.flag' (set #simplify True)  $ O.long "simplify"    <> O.help "Simplify terms (default)"
    , O.flag' (set #simplify False) $ O.long "no-simplify" <> O.help "Don't simplify terms"

    -- dumping of (intermediate) stages
    , O.flag' (set (#dump % #ps) True) $ O.long "dump-ps" <> O.help "Dump parsed term"
    , O.flag' (set (#dump % #rn) True) $ O.long "dump-rn" <> O.help "Dump renamed term"
    , O.flag' (set (#dump % #tc) True) $ O.long "dump-tc" <> O.help "Dump type-checked (elaborated) term"
    , O.flag' (set (#dump % #st) True) $ O.long "dump-st" <> O.help "Dump staged term"
    , O.flag' (set (#dump % #si) True) $ O.long "dump-si" <> O.help "Dump simplifier iterations"

    , O.flag' (set (#dump % #ps) False) $ O.long "no-dump-ps" <> O.help "Don't dump parsed term" <> O.hidden
    , O.flag' (set (#dump % #rn) False) $ O.long "no-dump-rn" <> O.help "Don't dump renamed term" <> O.hidden
    , O.flag' (set (#dump % #tc) False) $ O.long "no-dump-tc" <> O.help "Don't dump type-checked (elaborated) term" <> O.hidden
    , O.flag' (set (#dump % #st) False) $ O.long "no-dump-st" <> O.help "Don't dump staged term" <> O.hidden
    , O.flag' (set (#dump % #si) False) $ O.long "no-dump-si" <> O.help "Don't dump simplifier iterations" <> O.hidden
    ]

threeWayReader :: O.ReadM ThreeWay
threeWayReader = O.maybeReader $ \s -> case s of
    "always" -> Just Always
    "auto"   -> Just Auto
    "never"  -> Just Never
    _        -> Nothing

argP :: O.Parser FilePath
argP = O.strArgument $ mconcat
    [ O.metavar "FILE"
    , O.help "input file"
    ]

optsEndoP :: O.Parser (Opts -> Opts)
optsEndoP = foldl' (\f g -> g . f) id <$> optsP

parseOpts :: IO (Opts, [FilePath])
parseOpts = do
    (endos, args) <- O.execParser opts
    return (foldl' (&) defaultOpts endos, args)
  where
    opts = O.info (liftA2 (,) optsP (many argP) <**> O.helper) $ mconcat
        [ O.fullDesc
        , O.header "poritt - a type system from up north"
        ]

parseOptsEndo :: [String] -> Either String (Opts -> Opts)
parseOptsEndo args = case O.execParserPure O.defaultPrefs (O.info optsEndoP mempty) args of
    O.Success f           -> Right f
    O.Failure e           -> Left (fst (O.renderFailure e "poritt"))
    O.CompletionInvoked _ -> Left "completion invoked"
