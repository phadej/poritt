{-# LANGUAGE TemplateHaskell #-}
module PoriTT.Lexer (
    Token (..),
    showToken,
    LexerState (..),
    initLexerState,
    scan,
) where

import Data.Char (isDigit, isPrint)

import qualified Data.Text                as T
import qualified Data.Text.Encoding       as TE
import qualified Data.Text.Encoding.Error as TEE
import qualified Text.Parsec              as P

import PoriTT.Base
import PoriTT.Enum
import PoriTT.Loc
import PoriTT.Name

-------------------------------------------------------------------------------
-- Tokens
-------------------------------------------------------------------------------

-- | Tokens produced by lexer.
data Token
    = TkIdent Name        -- ^ identifiers: @foobar@
    | TkLabel Label       -- ^ labels: @:label@
    | TkEnumIdx EnumIdx   -- ^ enum index: @:7@
    | TkSelector Selector -- ^ selectors: @.fst@ or @.snd@
    | TkHole Name         -- ^ hole: @?name@ (Name includes question mark)
    | TkString Text       -- ^ string literal: @"literal"@
    | TkDefine            -- ^ keyword @define@
    | TkEval              -- ^ keyword @eval@
    | TkType              -- ^ keyword @type@
    | TkInfo              -- ^ keyword @info@
    | TkInline            -- ^ keyword @inline@
    | TkFail              -- ^ keyword @fail@
    | TkMacro             -- ^ keyword @macro@
    | TkInclude           -- ^ keyword @include@
    | TkSection           -- ^ keyword @section@
    | TkOptions           -- ^ keyword @options@
    | TkLet               -- ^ keyword @let@
    | TkIn                -- ^ keyword @in@
    | TkU                 -- ^ type former @U@
    | TkForall            -- ^ type former @forall@
    | TkExists            -- ^ type former @exists@
    | TkMu                -- ^ type former @mu@
    | TkDesc              -- ^ type former @Desc@
    | TkCode              -- ^ type former @Code@
    | TkUnit              -- ^ type former @Unit@
    | TkCon               -- ^ constructor @con@
    | TkDesc1             -- ^ constructor @`1@
    | TkDescS             -- ^ constructor @`S@
    | TkDescX             -- ^ constructor @`X@
    | TkTt                -- ^ constructor @tt@
    | TkSwitch            -- ^ eliminator @switch@
    | TkInd               -- ^ eliminator @ind@
    | TkDescInd           -- ^ eliminator @indDesc@
    | TkLParen            -- ^ left parenthesis: @(@
    | TkRParen            -- ^ right parenthesis: @)@
    | TkLBracket          -- ^ left parenthesis: @[@
    | TkRBracket          -- ^ right parenthesis: @]@
    | TkLBrace            -- ^ left parenthesis: @{@
    | TkRBrace            -- ^ right parenthesis: @}@
    | TkLQuote            -- ^ left quote: @[|@
    | TkRQuote            -- ^ right quote: @|]@
    | TkVBar              -- ^ vertical bar: @|@
    | TkArrow             -- ^ arrow: @->@
    | TkBackSlash         -- ^ backslash: @\\@
    | TkColon             -- ^ colon: @:@
    | TkSemi              -- ^ semi: @;@
    | TkComma             -- ^ comma: @,@
    | TkAst               -- ^ ast: @*@
    | TkEquals            -- ^ equals: @=@
    | TkAnon              -- ^ anon: @_@
    | TkDollar            -- ^ dollar: @$@
    | TkHash              -- ^ hash: @#@
    | TkEOF               -- ^ end-of-file token
    | TkVSemi             -- ^ virtual semiquote
    | TkError String
  deriving (Eq, Show)

showToken :: Token -> String
showToken (TkIdent n)    = "identifier " ++ show (prettyName n)
showToken (TkLabel l)    = "label " ++ show (prettyLabel l)
showToken (TkEnumIdx i)  = "enum index " ++ show (prettyEnumIdx i)
showToken (TkSelector s) = "selector " ++ show (prettySelector s)
showToken (TkHole n)     = "hole " ++ show (prettyName n)
showToken (TkString s)   = show s
showToken TkDefine       = "define"
showToken TkEval         = "eval"
showToken TkType         = "type"
showToken TkFail         = "fail"
showToken TkLet          = "let"
showToken TkIn           = "in"
showToken TkInfo         = "info"
showToken TkInline       = "inline"
showToken TkMacro        = "macro"
showToken TkInclude      = "include"
showToken TkSection      = "section"
showToken TkOptions      = "options"
showToken TkU            = "U"
showToken TkForall       = "forall"
showToken TkExists       = "exists"
showToken TkSwitch       = "switch"
showToken TkMu           = "mu"
showToken TkInd          = "ind"
showToken TkCon          = "con"
showToken TkDesc         = "Desc"
showToken TkCode         = "Code"
showToken TkUnit         = "Unit"
showToken TkTt           = "tt"
showToken TkDesc1        = "`1"
showToken TkDescS        = "`S"
showToken TkDescX        = "`X"
showToken TkDescInd      = "indDesc"
showToken TkLParen       = "("
showToken TkRParen       = ")"
showToken TkLBracket     = "["
showToken TkRBracket     = "]"
showToken TkLBrace       = "{"
showToken TkRBrace       = "}"
showToken TkLQuote       = "[|"
showToken TkRQuote       = "|]"
showToken TkVBar         = "|"
showToken TkDollar       = "$"
showToken TkHash         = "#"
showToken TkArrow        = "->"
showToken TkBackSlash    = "\\"
showToken TkColon        = ":"
showToken TkSemi         = ";"
showToken TkComma        = ","
showToken TkAst          = "*"
showToken TkEquals       = "="
showToken TkAnon         = "_"
showToken TkEOF          = "end-of-file"
showToken TkVSemi        = "virtual ;"
showToken (TkError _)    = "ERROR!"

-------------------------------------------------------------------------------
-- Lexer state
-------------------------------------------------------------------------------

data LexerState = LS
    { contents :: {-# UNPACK #-} !Text
    , location :: !Loc
    , pending  :: !(Maybe (Loc, Token))
    }
  deriving Show

instance Monad m => P.Stream LexerState m (Loc, Token) where
    uncons = return . unconsLexerState

unconsLexerState :: LexerState -> Maybe ((Loc, Token), LexerState)
unconsLexerState (skipSpace -> ls)
    | Just pending <- ls.pending
    = (Just (pending, ls { pending = Nothing }))

    | T.null ls.contents
    = Nothing

    | otherwise
    = case scan ls of
        (TkEOF, _) -> Nothing
        (tok, ls') -> Just (f ls.location tok ls')
        where
        f :: Loc -> Token -> LexerState -> ((Loc, Token), LexerState)
        f loc tok ls'
            | loc.locColumn <= 1 = ((loc, TkVSemi), ls' { pending = Just (loc, tok) })
            | otherwise          = ((loc, tok), ls')

initLexerState :: FilePath -> ByteString -> LexerState
initLexerState fn bs = LS
    { contents = decodeUtf8Lenient bs
    , location = startLoc fn
    , pending  = Nothing
    }

decodeUtf8Lenient :: ByteString -> Text
decodeUtf8Lenient = TE.decodeUtf8With TEE.lenientDecode

skipSpace :: LexerState -> LexerState
skipSpace (LS bs loc indent)
    | Just sfx' <- T.stripPrefix "--" sfx
    , (pfx'', sfx'') <- T.span (/= '\n') sfx'
    = skipSpace $ LS sfx'' (loc `advanceLoc` pfx `advanceLoc` "--" `advanceLoc` pfx'') indent

    | otherwise
    = LS sfx (loc `advanceLoc` pfx) indent
  where
    (pfx, sfx) = T.span isSpace bs

-------------------------------------------------------------------------------
-- Char predicates
-------------------------------------------------------------------------------

isSpace :: Char -> Bool
isSpace c = ' ' == c || '\t' == c || '\n' == c

isIdentChar :: Char -> Bool
isIdentChar c
    | isSpace c                 = False
    | elem c ('\\':"(){}[]|$;") = False
    | otherwise                 = isPrint c

-------------------------------------------------------------------------------
-- Scanning function
-------------------------------------------------------------------------------

scan :: LexerState -> (Token, LexerState)
scan ls@(LS contents loc indent) = case T.uncons contents of
    Nothing                -> (TkEOF,       ls)
    Just ('(' , contents') -> (TkLParen,    LS contents' (advanceLoc loc "(") indent)
    Just (')' , contents') -> (TkRParen,    LS contents' (advanceLoc loc ")") indent)
    Just ('[' , contents') -> case T.uncons contents' of
        Just ('|', contents'') -> (TkLQuote,    LS contents'' (advanceLoc loc "[|") indent)
        _                      -> (TkLBracket,  LS contents'  (advanceLoc loc "[") indent)
    Just ('|' , contents') -> case T.uncons contents' of
        Just (']', contents'') -> (TkRQuote,    LS contents'' (advanceLoc loc "|]") indent)
        _                      -> (TkVBar,      LS contents'  (advanceLoc loc "|") indent)
    Just (']' , contents') -> (TkRBracket,  LS contents' (advanceLoc loc "]") indent)
    Just ('{' , contents') -> (TkLBrace,    LS contents' (advanceLoc loc "{") indent)
    Just ('}' , contents') -> (TkRBrace,    LS contents' (advanceLoc loc "}") indent)
    Just ('$' , contents') -> (TkDollar,    LS contents' (advanceLoc loc "$") indent)
    Just ('#' , contents') -> (TkHash,      LS contents' (advanceLoc loc "#") indent)
    Just (';' , contents') -> (TkSemi,      LS contents' (advanceLoc loc ";")indent)
    Just ('\\', contents') -> (TkBackSlash, LS contents' (advanceLoc loc "\\") indent)
    Just ('"' , contents') -> case T.span (/= '"') contents' of
        (pfx, sfx) -> case T.uncons sfx of
            Nothing        -> (TkError "Unterminated string literal", ls)
            Just (_, sfx') -> (TkString pfx, LS sfx' (loc `advanceLoc` "\"" `advanceLoc` pfx `advanceLoc` "\"") indent)
    Just (c,    _        )
        | isIdentChar c -> case T.span isIdentChar contents of
            (pfx, sfx)     -> (classify pfx, LS sfx (advanceLoc loc pfx) indent)

        | otherwise        -> (TkError $ "Unknown character: " ++ show c, ls)

classify :: Text -> Token
classify "define"  = TkDefine
classify "type"    = TkType
classify "fail"    = TkFail
classify "eval"    = TkEval
classify "info"    = TkInfo
classify "inline"  = TkInline
classify "macro"   = TkMacro
classify "include" = TkInclude
classify "section" = TkSection
classify "options" = TkOptions
classify "let"     = TkLet
classify "in"      = TkIn
classify "U"       = TkU
classify "forall"  = TkForall
classify "exists"  = TkExists
classify "switch"  = TkSwitch
classify "Desc"    = TkDesc
classify "`1"      = TkDesc1
classify "`S"      = TkDescS
classify "`X"      = TkDescX
classify "indDesc" = TkDescInd
classify "mu"      = TkMu
classify "con"     = TkCon
classify "ind"     = TkInd
classify "Code"    = TkCode
classify "Unit"    = TkUnit
classify "tt"      = TkTt
classify "->"      = TkArrow
classify ":"       = TkColon
classify ","       = TkComma
classify "*"       = TkAst
classify "="       = TkEquals
classify "_"       = TkAnon
classify bs        = case T.uncons bs of
    Just ('.', bs')         -> TkSelector (mkSelector bs')
    Just ('?', _)           -> TkHole (mkName bs)
    Just (':', bs')
        | T.all isDigit bs' -> TkEnumIdx (EnumIdx (read (T.unpack bs')))
        | otherwise         -> TkLabel (mkLabel bs')
    _                       -> TkIdent (mkName bs)
