module PoriTT.PP (
    Doc,
    A (..),
    -- * Options
    PPOpts,
    PPOpts' (..),
    defaultPPOpts,
    -- * Combinators
    ppRender,
    ppAnnotate,
    ppTyArr,
    ppSyArr,
    ppSkp,
    ppBullet,
    ppAlign,
    ppParens,
    ppParensIf,
    ppQuote,
    ppBracesSemi,
    ppBraces,
    ppSep,
    ppHSep,
    ppVCat,
    ppText,
    ppStr,
    ppInt,
    ppHanging,
    ppSoftHanging,
    (<+>),
    ($$),
    (<//>),
    (</>),
    prettyFilePath,
) where

import Data.String  (IsString (..))
import Data.Text    (Text)
import GHC.Generics (Generic)

import qualified Data.Text           as T
import qualified Prettyprinter       as PP
import qualified System.Console.ANSI as ANSI

data PPOpts' a = PPOpts
    { unicode :: !a
    , colour  :: !a
    }
  deriving (Show, Generic)

type PPOpts = PPOpts' Bool

defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts
    { unicode = False
    , colour  = False
    }

-- | Annotations
data A
    = AKey
    | ATyp
    | ALbl
    | ACon
    | ASel
    | ACmd
    | AEch
    | AGbl
    | AErr
    | ASkp
  deriving (Eq, Ord, Show)

newtype Doc = D (PPOpts -> PP.Doc A)

instance IsString Doc where
    fromString s = D (\opts -> ann s $ fromString $ uni opts.unicode s)

ann :: String -> PP.Doc A -> PP.Doc A
ann "U"       = PP.annotate ATyp
ann "forall"  = PP.annotate ATyp
ann "exists"  = PP.annotate ATyp
ann "*"       = PP.annotate ATyp
ann "mu"      = PP.annotate ATyp
ann "Desc"    = PP.annotate ATyp
ann "Unit"    = PP.annotate ATyp

ann "\\"      = PP.annotate AKey
ann "switch"  = PP.annotate AKey
ann "ind"     = PP.annotate AKey
ann "indDesc" = PP.annotate AKey
ann "="       = PP.annotate AKey
ann ":"       = PP.annotate AKey
ann "{"       = PP.annotate AKey
ann ";"       = PP.annotate AKey
ann "}"       = PP.annotate AKey
ann "["       = PP.annotate AKey
ann "]"       = PP.annotate AKey
ann "[|"      = PP.annotate AKey
ann "|]"      = PP.annotate AKey
ann "$"       = PP.annotate AKey
ann "#"       = PP.annotate AKey

ann ","       = PP.annotate ACon
ann "con"     = PP.annotate ACon
ann "`1"      = PP.annotate ACon
ann "`S"      = PP.annotate ACon
ann "`X"      = PP.annotate ACon
ann "tt"      = PP.annotate ACon

ann _         = id

uni :: Bool -> String -> String
uni True "[|"     = "⟦"
uni True "|]"     = "⟧"
uni True "forall" = "∀"
uni True "exists" = "∃"
uni True "*"      = "×"
uni True "mu"     = "μ"
uni True "\\"     = "λ"
uni True "$"      = "∫"
uni _    s        = s

ppTyArr :: Doc
ppTyArr = D $ \opts -> PP.annotate ATyp (if opts.unicode then "→" else "->")

ppSyArr :: Doc
ppSyArr = D $ \opts -> PP.annotate AKey (if opts.unicode then "↦" else "->")

ppBullet :: Doc
ppBullet = D $ \opts -> if opts.unicode then "•" else "*"

instance Semigroup Doc where
    D x <> D y = D (x <> y)

instance Show Doc where
    show = ppRender defaultPPOpts

ppRender :: PPOpts -> Doc -> String
ppRender opts (D doc) = renderShowS opts.colour sds ""
  where
    sds = PP.layoutSmart ppOpts (doc opts)
    ppOpts = PP.defaultLayoutOptions

renderShowS :: Bool -> PP.SimpleDocStream A -> ShowS
renderShowS _      PP.SFail            = id
renderShowS _      PP.SEmpty           = id
renderShowS colour (PP.SChar c x)      = showChar c . renderShowS colour x
renderShowS colour (PP.SText _l t x)   = showString (T.unpack t) . renderShowS colour x
renderShowS colour (PP.SLine i x)      = showString ('\n' : replicate i ' ') . renderShowS colour x
renderShowS colour (PP.SAnnPush a x)   = renderAnnPush colour a . renderShowS colour x
renderShowS colour (PP.SAnnPop x)      = renderAnnPop colour . renderShowS colour x

renderAnnPush :: Bool -> A -> ShowS
renderAnnPush True  a = showString (ANSI.setSGRCode (sgrCode a))
renderAnnPush False _ = id

renderAnnPop :: Bool -> ShowS
renderAnnPop True  = showString (ANSI.setSGRCode [])
renderAnnPop False = id

ppAnnotate :: A -> Doc -> Doc
ppAnnotate a (D d) = D (PP.annotate a . d)

ppSkp :: Doc
ppSkp = D (\_ -> PP.annotate ASkp "_")

sgrCode :: A -> [ANSI.SGR]
sgrCode ATyp = sgrCode' ANSI.Green
sgrCode AKey = sgrCode' ANSI.Yellow
sgrCode ASel = sgrCode' ANSI.Magenta
sgrCode ALbl = sgrCode' ANSI.Cyan -- keywords are kind of constructors.
sgrCode AGbl = sgrCode' ANSI.Blue
sgrCode ACon = sgrCode' ANSI.Cyan
sgrCode AErr = ANSI.SetConsoleIntensity ANSI.BoldIntensity : sgrCode' ANSI.Red
sgrCode ACmd = [ANSI.SetConsoleIntensity ANSI.BoldIntensity, ANSI.SetColor ANSI.Foreground ANSI.Vivid ANSI.White]
sgrCode AEch = [ANSI.SetConsoleIntensity ANSI.BoldIntensity, ANSI.SetColor ANSI.Foreground ANSI.Dull ANSI.White]
sgrCode ASkp = ANSI.SetColor ANSI.Background ANSI.Vivid ANSI.Yellow : sgrCode' ANSI.Black

sgrCode' :: ANSI.Color -> [ANSI.SGR]
sgrCode' c = [ANSI.SetColor ANSI.Foreground ANSI.Vivid c]

ppParensIf :: Bool -> Doc -> Doc
ppParensIf True  = ppParens
ppParensIf False = id

ppQuote :: Doc -> Doc
ppQuote d = "[|" <+> d <+> "|]"

ppParens :: Doc -> Doc
ppParens d = "(" <> ppAlign d <> ")"

ppBracesSemi :: [Doc] -> Doc
ppBracesSemi ds = ppBraces $ D $ \opts -> PP.sep $ PP.punctuate ";" [ d opts | D d <- ds ]

ppBraces :: Doc -> Doc
ppBraces d = "{" <> ppAlign d <> "}"

ppAlign :: Doc -> Doc
ppAlign (D d) = D (PP.align . d)

ppStr :: String -> Doc
ppStr x = D $ \_ -> PP.pretty x

ppText :: Text -> Doc
ppText x = D $ \_ -> PP.pretty x

ppInt :: Int -> Doc
ppInt x = D $ \_ -> PP.pretty x

ppHang :: Int -> Doc -> Doc
ppHang i (D d) = D (\opts -> PP.nest i (d opts))

ppHanging :: Doc -> [Doc] -> Doc
ppHanging d ds = ppHang 2 (ppVCat (d : ds))

ppSoftHanging :: Doc -> [Doc] -> Doc
ppSoftHanging d ds = ppHang 2 (ppSep (d : ds))

ppSep :: [Doc] -> Doc
ppSep ds = D $ \opts -> PP.sep [ d opts | D d <- ds ]

ppHSep :: [Doc] -> Doc
ppHSep ds = D $ \opts -> PP.hsep [ d opts | D d <- ds ]

ppVCat :: [Doc] -> Doc
ppVCat ds = D $ \opts -> PP.vcat [ d opts | D d <- ds ]

infixr 6 <+>
infixr 5 $$, <//>, </>

(<+>), ($$), (<//>), (</>) :: Doc -> Doc -> Doc

D x <+> D y = D $ \opts -> x opts PP.<+> y opts
x $$ y = ppVCat [x, y]

x <//> y = ppSoftHanging x [y]

x </> y = ppSep [x, y]

prettyFilePath :: FilePath -> Doc
prettyFilePath fp = "\"" <> ppStr fp <> "\""
