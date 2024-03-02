module PoriTT.Main (
    main,
    batchFile,
    Environment,
    builtinEnvironment,
) where

import Control.Monad.Trans.Class        (lift)
import Control.Monad.Trans.State.Strict (StateT (StateT), evalStateT, execStateT)
import System.Console.ANSI              (hSupportsANSIColor)
import System.Directory                 (canonicalizePath)
import System.Exit                      (exitFailure)
import System.FilePath                  (takeDirectory)
import System.IO                        (Handle, hGetEncoding, hPutStrLn, stdout)

import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import qualified System.FilePath as FP
import qualified Text.Parsec     as P

import PoriTT.Base
import PoriTT.Builtins
import PoriTT.Check
import PoriTT.Conv
import PoriTT.Distill
import PoriTT.Eval
import PoriTT.ExceptState
import PoriTT.Global
import PoriTT.Info
import PoriTT.Lexer
import PoriTT.Lint
import PoriTT.Macro
import PoriTT.Name
import PoriTT.Opts
import PoriTT.Rigid
import PoriTT.Parser
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Raw
import PoriTT.Rename
import PoriTT.Simpl
import PoriTT.Term
import PoriTT.Value
import PoriTT.Well

modifyM :: Monad m => (s -> m s) -> StateT s m ()
modifyM f = StateT $ \ s -> do
    s' <- f s
    return ((), s')

data Environment = Environment
    { handle   :: Handle
    , ppopts   :: PPOpts
    , globals  :: Map Name Global
    , macros   :: Map Name Macro
    , included :: Set FilePath
    , pending  :: Maybe (Name, VTerm NoMetas EmptyCtx)
    , opts     :: Opts
    }

type MainM = StateT Environment IO

builtinEnvironment :: Handle -> Opts -> IO Environment
builtinEnvironment hdl opts = do
    colour <- case opts.prettyOpts.colour of
        Auto   -> hSupportsANSIColor hdl
        Always -> return True
        Never  -> return False

    unicode <- case opts.prettyOpts.unicode of
        Auto   -> do
            menc <- hGetEncoding hdl
            return $ maybe False (\enc -> "UTF-8" == show enc) menc
        Always -> return True
        Never  -> return False

    return Environment
        { handle = hdl
        , opts   = opts
        , ppopts = PPOpts
            { colour = colour
            , unicode = unicode
            }
        , globals = Map.fromList $ map (\g -> (g.name, g))
            [ evalDescGlobal
            , allTypeGlobal
            , allTermGlobal
            ]
        , macros = Map.empty
        , included = Set.empty
        , pending = Nothing
        }

nameScopeFromEnv :: Environment -> NameScope
nameScopeFromEnv Environment {..} =
    nameScopeFromSet (Map.keysSet globals) <> nameScopeFromSet (Map.keysSet macros)

readStatements :: FilePath -> MainM [Stmt]
readStatements fn = do
    cfn <- lift (canonicalizePath fn)
    env <- get
    if Set.member cfn env.included
    then return [DoneStmt fn]
    else do
        -- mark as included
        put $ env { included = Set.insert cfn env.included }

        -- read file
        bs <- lift $ BS.readFile fn

        -- parse statements
        statements' <- either (printError . ppStr . show) return $
            P.parse (stmtsP <* eofP) fn (initLexerState fn bs)

        let statements = statements' ++ [DoneStmt fn]

        -- recurse on include stmts.
        fmap concat $ for statements $ \stmt -> case stmt of
            IncludeStmt fn' -> fmap (stmt :) $ readStatements (takeDirectory fn FP.</> fn')
            _               -> return [stmt]

echo :: Doc -> Doc -> [Doc] -> MainM ()
echo cmd args extras = do
    env <- get
    let opts  = env.opts
    when opts.echo $ printDoc $ ppSoftHanging (ppAnnotate AEch cmd <+> args) extras

checkNoPending :: MainM ()
checkNoPending = do
    env@Environment { opts = opts, pending = p } <- get
    let names = nameScopeFromEnv env
    case p of
        Nothing -> return ()
        Just (n, ty)  -> printError $ "Pending definition of " <+> prettyName n <+> ":" <+> prettyVTermZ opts UnfoldNone names ty VUni

batchFile
    :: FilePath                -- ^ input file
    -> Environment             -- ^ evaluation state
    -> IO (Environment)        -- ^ new evaluation state
batchFile fn = execStateT $ do
    statements <- readStatements fn

    for_ statements $ \s -> do
        stmt s
        case s of
            TypeDefineStmt {} -> return ()
            _                 -> printDoc ""
  where
    lint :: Doc -> Elim NoMetas EmptyCtx -> VTerm NoMetas EmptyCtx -> MainM ()
    lint pass e et = do
        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        et' <- either printError return $ lintElim (emptyLintCtx names) e
        case evalExceptState (convTerm (mkConvCtx SZ EmptyEnv EmptyEnv names) VUni et et') initialRigidState of
            Right _  -> pure ()
            Left msg -> printError $ ppVCat
                [ pass <+> "lint failed"
                , msg
                , ppBullet <+> prettyVTermZ opts UnfoldNone names et VUni
                , ppBullet <+> prettyVTermZ opts UnfoldNone names et' VUni
                ]

    -- TODO: use only lintT
    lintT :: Doc -> Term NoMetas EmptyCtx -> VTerm NoMetas EmptyCtx -> MainM ()
    lintT _pass t et = do
        env <- get
        let names = nameScopeFromEnv env

        either printError return $ lintTerm (emptyLintCtx names) t et

    pipelineElim :: Raw -> MainM (Elim NoMetas EmptyCtx, VTerm NoMetas EmptyCtx)
    pipelineElim e = do
        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        when opts.dump.ps $ printDoc $ ppSoftHanging (ppAnnotate ACmd "ps") [ prettyRaw 0 e ]

        -- resolve names: rename
        w <- either printErrors return $ resolve (emptyRenameCtx env.globals env.macros) e
        when opts.dump.rn $  printDoc $ ppSoftHanging (ppAnnotate ACmd "rn") [ prettyWell names EmptyEnv 0 w ]

        -- elaborate, i.e. type-check
        (e1, et) <- either printError return $ checkElim (emptyCheckCtx names) w
        when opts.dump.tc $ printDoc $ ppSoftHanging (ppAnnotate ACmd "tc") [ prettyElimZ opts names e1 ]
        lint "First" e1 et

        e2 <- either (printError . ppStr . show) return $ preElim SZ EmptyEnv e1
        when opts.dump.st $ printDoc $ ppSoftHanging (ppAnnotate ACmd "st") [ prettyElimZ opts names e2 ]
        lint "Staging" e2 et

        e' <- if opts.simplify
            then do
                let loop :: Int -> Elim NoMetas EmptyCtx -> MainM (Elim NoMetas EmptyCtx)
                    loop n e' | n > opts.simplOpts.iters = return e'
                    loop n e' = do
                        e'' <- simplLoop ("s" <> ppInt n) e' et
                        loop (n + 1) e''

                loop 1 e2

            else return e2

        return (e', et)

    pipelineTerm :: Raw -> VTerm NoMetas EmptyCtx -> MainM (Term NoMetas EmptyCtx)
    pipelineTerm t et = do
        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        when opts.dump.ps $ printDoc $ ppSoftHanging (ppAnnotate ACmd "ps") [ prettyRaw 0 t ]

        -- resolve names: rename
        w <- either printErrors return $ resolve (emptyRenameCtx env.globals env.macros) t
        when opts.dump.rn $  printDoc $ ppSoftHanging (ppAnnotate ACmd "rn") [ prettyWell names EmptyEnv 0 w ]

        -- elaborate, i.e. type-check
        t1 <- either printError return $ checkTerm (emptyCheckCtx names) w et
        when opts.dump.tc $ printDoc $ ppSoftHanging (ppAnnotate ACmd "tc") [ prettyTermZ opts names t1 et ]
        lintT "First" t1 et

        t2 <- either (printError . ppStr . show) return $ preTerm SZ EmptyEnv t1
        when opts.dump.st $ printDoc $ ppSoftHanging (ppAnnotate ACmd "st") [ prettyTermZ opts names t2 et ]
        lintT "Staging" t2 et

        t' <- if opts.simplify
            then do
                let loop :: Int -> Term NoMetas EmptyCtx -> MainM (Term NoMetas EmptyCtx)
                    loop n e' | n > opts.simplOpts.iters = return e'
                    loop n e' = do
                        e'' <- simplLoopT ("s" <> ppInt n) e' et
                        loop (n + 1) e''

                loop 1 t2

            else return t2

        return t'

    simplLoop :: Doc -> Elim NoMetas EmptyCtx -> VTerm NoMetas EmptyCtx -> MainM (Elim NoMetas EmptyCtx)
    simplLoop iter e et = do
        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        let e' = simplElim (emptySimplCtx opts.simplOpts) e

        -- check that we simplified correctly
        lint ("Simplify" <+> iter) e' et

        when opts.dump.si $ printDoc $ ppSoftHanging (ppAnnotate ACmd iter) [ prettyElimZ opts names e' ]

        return e'

    simplLoopT :: Doc -> Term NoMetas EmptyCtx -> VTerm NoMetas EmptyCtx -> MainM (Term NoMetas EmptyCtx)
    simplLoopT iter e et = do
        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        let e' = simplTerm (emptySimplCtx opts.simplOpts) e

        -- check that we simplified correctly
        lintT ("Simplify" <+> iter) e' et

        when opts.dump.si $ printDoc $ ppSoftHanging (ppAnnotate ACmd iter) [ prettyTermZ opts names e' et ]

        return e'

    stmt :: Stmt -> MainM ()
    stmt (TypeDefineStmt name ty) = do
        checkNoPending
        echo "declare" (prettyName name)
            [ ":" <+> prettyRaw 0 ty
            ]

        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        when (nameScopeMember name names) $
            printError $ prettyName name <+> "is already defined"

        t' <- pipelineTerm ty VUni

        let t'' = evalTerm SZ emptyEvalEnv t'

        let env' :: Environment
            env' = env { pending = Just (name, t'') }

        put env'

        printDoc $ ppSoftHanging
            (ppAnnotate ACmd $ prettyName name)
            [ ":" <+> prettyTermZ opts names t' VUni
            ]

    stmt (DefineStmt name xs e_) = do
        echo "define" (prettyName name)
            [ ppStr (show xs) <+> "=" <+> prettyRaw 0 e_
            ]

        let e = foldr (\(i, x) t -> RLam x i t) e_ xs

        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        when (nameScopeMember name names) $
            printError $ prettyName name <+> "is already defined"

        (e', et) <- case env.pending of
            Nothing          -> pipelineElim e
            Just (name', ty) -> do
                unless (name == name') $ printError $ "Pending definition of " <+> prettyName name' <+> ":" <+> prettyVTermZ opts UnfoldNone names ty VUni
                t <- pipelineTerm e ty

                case quoteTerm UnfoldNone SZ ty of
                    Left err -> printError $ ppStr $ show err
                    Right ty' -> return (Ann t ty', ty)

        let ev = evalElim SZ emptyEvalEnv e'
        let g :: Global
            g = Global
                { name   = name
                , term   = e'
                , typ    = et
                , val    = ev
                , inline = False
                }

        put $ env { globals = Map.insert name g env.globals, pending = Nothing }

        when (isNothing env.pending) $ printDoc $ ppSoftHanging
            (ppAnnotate ACmd $ prettyName name)
            [ ":" <+> prettyVTermZ opts UnfoldNone names et VUni
            ]

        printDoc $ ppSoftHanging
                (ppAnnotate ACmd $ prettyName name)
                [ "=" <+> case e' of
                    Ann t _ -> prettyTermZ opts names t et
                    _       -> prettyElimZ opts names e'
                ]

    stmt (DefineStmt' name ty t) = do
        echo "define" (prettyName name)
            [ ":" <+> prettyRaw 0 ty
            , "=" <+> prettyRaw 0 t
            ]

        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        when (nameScopeMember name names) $
            printError $ prettyName name <+> "is already defined"

        (e', et) <- pipelineElim (RAnn t ty)

        let ev = evalElim SZ emptyEvalEnv e'
        let g :: Global
            g = Global
                { name   = name
                , term   = e'
                , typ    = et
                , val    = ev
                , inline = False
                }

        put $ env { globals = Map.insert name g env.globals }

        printDoc $ ppSoftHanging
            (ppAnnotate ACmd "define" <+> prettyName name)
            [ ":" <+> prettyVTermZ opts UnfoldNone names et VUni
            , "=" <+> case e' of
                Ann t' _ -> prettyTermZ opts names t' et
                _        -> prettyElimZ opts names e'
            ]

    stmt (MacroStmt name xs0 t) = do
        echo "macro" (prettyName name)
            [ "=" <+> prettyRaw 0 t
            ]

        env <- get
        let names = nameScopeFromEnv env

        when (nameScopeMember name names) $
            printError $ prettyName name <+> "is already defined"

        let loop :: Env arity Name -> RenameCtx arity -> [Name] -> MainM Macro
            loop ns ctx [] = do
                w <- either printErrors return $ resolve ctx t
                return (Macro name ns w)
            loop ns ctx (x:xs) = loop (ns :> x) (bindRenameCtx ctx (Just x)) xs

        m <- loop EmptyEnv (emptyRenameCtx env.globals env.macros) xs0

        put $ env { macros = Map.insert name m env.macros }

        printDoc $ infoMacro m

    stmt (TypeStmt e) = do
        echo "type" (prettyRaw 0 e) []

        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        (_e', et) <- pipelineElim e

        printDoc $ ppSoftHanging (ppAnnotate ACmd "type" <+> prettyRaw 0 e)
            [ ":" <+> prettyVTermZ opts UnfoldNone names et VUni
            ]

    stmt (FailStmt e) = do
        echo "fail" (prettyRaw 0 e) []

        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        when opts.dump.ps $ printDoc $ ppSoftHanging (ppAnnotate ACmd "ps") [ prettyRaw 0 e ]

        -- resolve names: rename
        w <- either printErrors return $ resolve (emptyRenameCtx env.globals env.macros) e
        when opts.dump.rn $  printDoc $ ppSoftHanging (ppAnnotate ACmd "rn") [ prettyWell names EmptyEnv 0 w ]

        -- elaborate, i.e. type-check
        case checkElim (emptyCheckCtx names) w of
            Right (e', et) -> printError $ ppSoftHanging ("Unexpected type-check success")
                [ ":" <+> prettyVTermZ opts UnfoldNone names et VUni
                , "=" <+> case e' of
                    Ann t' _ -> prettyTermZ opts names t' et
                    _        -> prettyElimZ opts names e'
                ]
            Left err -> printDoc $ ppSoftHanging (ppAnnotate ACmd "fail" <+> prettyRaw 0 e)
                [ err ]

    stmt (EvalStmt e) = do
        echo "eval" (prettyRaw 0 e) []

        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        (e', et) <- pipelineElim e

        let u :: Unfold
            u = if opts.evalFull then UnfoldAll else UnfoldElim

        printDoc $ ppSoftHanging
            (ppAnnotate ACmd "eval" <+> prettyRaw 0 e)
            [ "=" <+> prettyVElimZ opts u names (evalElim SZ emptyEvalEnv e')
            , ":" <+> prettyVTermZ opts UnfoldNone names et VUni
            ]

    stmt (InfoStmt x) = do
        echo "info" (prettyName x) []

        env <- get

        if | Just g <- Map.lookup x env.globals -> printDoc $ infoGlobal g
           | Just m <- Map.lookup x env.macros  -> printDoc $ infoMacro m
           | otherwise -> printError $ prettyName x <+> "is unknown"

    stmt (InlineStmt x) = do
        env <- get
        let globals = env.globals

        printDoc $ ppAnnotate ACmd "inline" <+> prettyName x

        if | Map.member x globals -> put $ env { globals = Map.adjust (\g -> g { inline = True }) x globals }
           | otherwise -> printError $ prettyName x <+> "is unknown"

    stmt (SectionStmt title) = do
        printDoc $ ppAnnotate ACmd "section" <+> ppText title

    stmt (IncludeStmt fp) = do
        printDoc $ ppAnnotate ACmd "include" <+> prettyFilePath fp

    stmt (DoneStmt fp) = do
        printDoc $ ppAnnotate ACmd "end-of-file" <+> prettyFilePath fp

    stmt (OptionsStmt args) = do
        printDoc $ ppAnnotate ACmd "options" <+> ppSep (map ppStr args)

        case parseOptsEndo args of
            Left err   -> printError $ ppStr err
            Right endo -> do
                env <- get
                put $ env { opts = endo env.opts }

main :: IO ()
main = do
    (opts, args) <- parseOpts
    env <- builtinEnvironment stdout opts
    evalStateT (mapM_ (\arg -> modifyM (batchFile arg)) args) env

prettyTermZ :: Opts -> NameScope -> Term NoMetas EmptyCtx -> VTerm NoMetas EmptyCtx -> Doc
prettyTermZ opts names t a
    | opts.distill = prettierTerm opts.distillOpts names t a
    | otherwise    = prettyTerm names EmptyEnv 0 t

prettyElimZ :: Opts -> NameScope -> Elim NoMetas EmptyCtx -> Doc
prettyElimZ opts names e
    | opts.distill = prettierElim opts.distillOpts names e
    | otherwise    = prettyElim names EmptyEnv 0 e

prettyElimZ' :: Opts -> NameScope -> Elim NoMetas EmptyCtx -> Doc
prettyElimZ' opts names e
    | opts.distill = prettierElim' opts.distillOpts names e
    | otherwise    = prettyElim' names EmptyEnv 0 e

prettyVTermZ :: Opts -> Unfold -> NameScope -> VTerm NoMetas EmptyCtx -> VTerm NoMetas EmptyCtx -> Doc
prettyVTermZ opts unfold ns v a = case quoteTerm unfold SZ v of
    Left err -> ppStr (show err) -- This shouldn't happen if type-checker is correct.
    Right n  -> prettyTermZ opts ns n a

prettyVElimZ :: Opts -> Unfold -> NameScope -> VElim NoMetas EmptyCtx -> Doc
prettyVElimZ opts unfold ns (VAnn t a) = prettyVTermZ opts unfold ns t a
prettyVElimZ opts unfold ns e          = case quoteElim unfold SZ e of
    Left err -> ppStr (show err)           -- This shouldn't happen if type-checker is correct.
    Right e' -> prettyElimZ' opts ns e'

printDoc :: Doc -> MainM ()
printDoc d = do
    Environment { handle = hdl, ppopts = ppOpts, opts = _opts } <- get
    lift $ hPutStrLn hdl $ ppRender ppOpts d

printErrors :: Foldable f => f Doc -> MainM a
printErrors msgs = do
    for_ msgs $ \msg -> printDoc $ ppAnnotate AErr "Error:" <+> msg
    lift exitFailure

printError :: Doc -> MainM a
printError msg = do
    printDoc $ ppAnnotate AErr "Error:" <+> msg
    lift exitFailure
