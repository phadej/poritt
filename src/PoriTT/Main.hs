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

-- TODO
import Unsafe.Coerce (unsafeCoerce)

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
import PoriTT.Nice
import PoriTT.Opts
import PoriTT.Parser
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Raw
import PoriTT.Rename
import PoriTT.Rigid
import PoriTT.Simpl
import PoriTT.Term
import PoriTT.Value
import PoriTT.Well
import PoriTT.Zonk

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
    , includeS :: Natural
    , pending  :: Maybe (Name, Term NoMetas EmptyCtx, VTerm NoMetas EmptyCtx)
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
        , includeS = 0
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
    then return [IncludeStmt fn []]
    else do
        -- mark as included
        put $ env { included = Set.insert cfn env.included }

        -- read file
        bs <- lift $ BS.readFile fn

        -- parse statements
        statements' <- either (printError . ppStr . show) return $
            P.parse (stmtsP <* eofP) fn (initLexerState fn bs)

        let statements = statements'

        -- recurse on include stmts.
        fmap concat $ for statements $ \stmt -> case stmt of
            IncludeStmt fn' _ -> pure . IncludeStmt fn' <$> readStatements (takeDirectory fn FP.</> fn')
            _                 -> return [stmt]

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
        Just (n, ty, _ty)  -> printError $ "Pending definition of " <+> prettyName n <+> ":" <+> prettyTermZ opts names ty VUni

batchFile
    :: FilePath                -- ^ input file
    -> Environment             -- ^ evaluation state
    -> IO (Environment)        -- ^ new evaluation state
batchFile fn = execStateT $ do
    statements <- readStatements fn

    case statements of
        []   -> return ()
        s:ss -> do
            stmt s
            for_ ss stmtN
  where
    stmtN :: Stmt -> MainM ()
    stmtN s = do
        -- print newline only if we are not pending the def
        Environment { pending = p } <- get
        when (isNothing p) $ printDoc ""
        stmt s

    lintE :: Doc -> Elim pass EmptyCtx -> VTerm pass EmptyCtx -> MainM ()
    lintE pass e et = do
        env <- get
        let names = nameScopeFromEnv env

        et' <- either printError return $ evalExceptState (lintElim (emptyLintCtx names) e) initialRigidState
        case evalExceptState (convTerm (mkConvCtx SZ EmptyEnv EmptyEnv names emptyRigidMap) VUni et et') initialRigidState of
            Right _  -> pure ()
            Left msg -> printError $ ppVCat
                [ pass <+> "lint failed"
                , msg
                -- , ppBullet <+> prettyVTermZ opts UnfoldNone names et VUni
                -- , ppBullet <+> prettyVTermZ opts UnfoldNone names et' VUni
                ]

    lintT :: Doc -> Term pass EmptyCtx -> VTerm NoMetas EmptyCtx -> MainM ()
    lintT pass t et = do
        env <- get
        let names = nameScopeFromEnv env

        case evalExceptState (lintTerm (emptyLintCtx names) t (coeNoMetasVTerm et)) initialRigidState of
            Right _  -> pure ()
            Left msg -> printError $ ppVCat
                [ pass <+> "lint failed"
                , msg
                ]

    pipelineElim :: Raw -> MainM (Elim NoMetas EmptyCtx, VTerm NoMetas EmptyCtx)
    pipelineElim e = do
        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        -- resolve names: rename
        w <- pipelineBegin e

        -- elaborate, i.e. type-check
        (e0, et') <- either printError return $ evalExceptState (checkElim (emptyCheckCtx names) w) initialRigidState
        when opts.dump.tc $ printDoc $ ppSoftHanging (ppAnnotate ACmd "tc") [ prettyElim names EmptyEnv 0 e0 ]
        lintE "tc" e0 et'

        -- type pipeline
        ty' <- case quoteTerm UnfoldNone SZ et' of
            Left err -> printError $ ppStr $ show err
            Right ty -> pure ty

        ty <- fastPipelineEnd ty' VUni
        let et = evalTerm SZ emptyEvalEnv ty

        -- term pipeline
        t <- pipelineEnd (emb_ e0) et

        return (ann_ t ty, et)

    pipelineTerm :: Raw -> VTerm NoMetas EmptyCtx -> MainM (Term NoMetas EmptyCtx)
    pipelineTerm t et = do
        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        w <- pipelineBegin t

        -- elaborate, i.e. type-check
        t0 <- either printError return $ evalExceptState (checkTerm (emptyCheckCtx names) w (coeNoMetasVTerm et)) initialRigidState
        when opts.dump.tc $ printDoc $ ppSoftHanging (ppAnnotate ACmd "tc") [ prettyTerm names EmptyEnv 0 t0 ]
        lintT "tc" t0 et

        pipelineEnd t0 et

    -- pipeline beginning, before typechecking: name resolution
    pipelineBegin :: Raw -> MainM (Well pass EmptyCtx)
    pipelineBegin t = do
        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        -- parsing (already done)
        when opts.dump.ps $ printDoc $ ppSoftHanging (ppAnnotate ACmd "ps") [ prettyRaw 0 t ]

        -- resolve names: rename
        w <- either printErrors return $ resolve (emptyRenameCtx env.globals env.macros) t
        when opts.dump.rn $  printDoc $ ppSoftHanging (ppAnnotate ACmd "rn") [ prettyWell names EmptyEnv 0 w ]

        return w

    -- pipeline end, after typechecking: zonk, stage, simplify
    pipelineEnd :: Term HasMetas EmptyCtx -> VTerm NoMetas EmptyCtx -> MainM (Term NoMetas EmptyCtx)
    pipelineEnd t0 et = do
        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        -- zonk: substitute metavariable solutions
        t1 <- maybe (printError $ "zonk failed") return $ zonkTerm t0
        when opts.dump.zk $ printDoc $ ppSoftHanging (ppAnnotate ACmd "zk") [ prettyTermZ opts names t1 et ]
        lintT "zk" t1 et

        -- stage: normalise top-level splices
        t2 <- either (printError . ppStr . show) return $ preTerm SZ EmptyEnv t1
        when opts.dump.st $ printDoc $ ppSoftHanging (ppAnnotate ACmd "st") [ prettyTermZ opts names t2 et ]
        lintT "st" t2 et

        -- simplify
        t' <- if opts.simplify
            then do
                let loop :: Int -> Term NoMetas EmptyCtx -> MainM (Term NoMetas EmptyCtx)
                    loop n e' | n > opts.simplOpts.iters = return e'
                    loop n e' = do
                        e'' <- simplLoopT (ppInt n) e' et
                        loop (n + 1) e''

                loop 1 t2

            else return t2

        return t'

    -- fast pipeline for just quoted terms.
    fastPipelineEnd :: Term HasMetas EmptyCtx -> VTerm NoMetas EmptyCtx -> MainM (Term NoMetas EmptyCtx)
    fastPipelineEnd t0 et = do
        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        -- zonk: substitute metavariable solutions
        t1 <- maybe (printError $ "zonk failed") return $ zonkTerm t0
        when opts.dump.zk $ printDoc $ ppSoftHanging (ppAnnotate ACmd "zk") [ prettyTermZ opts names t1 et ]
        lintT "zk" t1 et

        return t1

    simplLoopT :: Doc -> Term NoMetas EmptyCtx -> VTerm NoMetas EmptyCtx -> MainM (Term NoMetas EmptyCtx)
    simplLoopT iter e et = do
        env <- get
        let opts  = env.opts
        let names = nameScopeFromEnv env

        let e' = simplTerm (emptySimplCtx opts.simplOpts) e

        -- check that we simplified correctly
        lintT ("si" <> iter) e' et

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
            env' = env { pending = Just (name, t', t'') }

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
            Just (name', ty', ty) -> do
                unless (name == name') $ printError $ "Pending definition of " <+> prettyName name' <+> ":" <+> prettyVTermZ opts UnfoldNone names ty VUni
                t <- pipelineTerm e ty
                return (Ann t ty', ty)

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
        case evalExceptState (checkElim (emptyCheckCtx names) w) initialRigidState of
            Right (unsafeCoerce -> e', unsafeCoerce -> et) -> printError $ ppSoftHanging ("Unexpected type-check success")
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

    stmt (IncludeStmt fp stmts) = do
        printDoc $ ppAnnotate ACmd "include" <+> prettyFilePath fp
        modify' $ \env -> env { includeS = NS env.includeS }
        for_ stmts stmtN
        checkNoPending
        modify' $ \env -> env { includeS = case env.includeS of { NZ -> NZ; NS l -> l } }
        printDoc ""
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

-- always prints
printDoc' :: Doc -> MainM ()
printDoc' d = do
    Environment { handle = hdl, ppopts = ppOpts, opts = _opts } <- get
    lift $ hPutStrLn hdl $ ppRender ppOpts d

-- prints only if not inside include (controlled by options)
printDoc :: Doc -> MainM ()
printDoc d = do
    Environment { handle = hdl, ppopts = ppOpts, opts = _opts, includeS = s } <- get
    when (s <= 0) $ lift $ hPutStrLn hdl $ ppRender ppOpts d

printErrors :: Foldable f => f Doc -> MainM a
printErrors msgs = do
    for_ msgs $ \msg -> printDoc' $ ppAnnotate AErr "Error:" <+> msg
    lift exitFailure

printError :: Doc -> MainM a
printError msg = do
    printDoc' $ ppAnnotate AErr "Error:" <+> msg
    lift exitFailure
