module Language.LSP.Hover


import Control.Monad.State
import Core.Core
import Core.Env
import Core.TT.Traversals
import Data.String
import Idris.Doc.String
import Idris.Pretty
import Idris.REPL.Opts
import Idris.Resugar
import Idris.Syntax
import Libraries.Data.ANameMap
import Libraries.Data.NameMap
import Libraries.Data.StringMap as S
import Libraries.Data.WithDefault
import TTImp.TTImp
import TTImp.TTImp.Functor

public export
data MarkdownAnn = MDHeader Nat | MDCode | MDRaw

prettyName : Name -> Doc IdrisDocAnn
prettyName n =
  case userNameRoot n of
    -- shouldn't happen: we only show UN anyways...
    Nothing => pretty0 (nameRoot n)
    Just un => if isOpUserName un then parens (pretty0 un) else pretty0 un

prettyKindedName : Maybe String -> Doc IdrisDocAnn -> Doc IdrisDocAnn
prettyKindedName Nothing   nm = nm
prettyKindedName (Just kw) nm
  = annotate (Syntax Keyword) (pretty0 kw) <++> nm

||| Look up implementations
getImplDocs : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              (keep : Term [] -> Core Bool) ->
              Core (List (Doc MarkdownAnn))
getImplDocs keep
    = do defs <- get Ctxt
         docss <- for (concat $ values $ typeHints defs) $ \ (impl, _) =>
           do Just def <- lookupCtxtExact impl (gamma defs)
                | _ => pure []
              -- Only keep things that look like implementations.
              -- i.e. get rid of data constructors
              let Just Func = defNameType (definition def)
                | _ => pure []
              -- Check that the type mentions the name of interest
              ty <- toFullNames !(normaliseHoles defs [] (type def))
              True <- keep ty
                | False => pure []
              ty <- resugar [] ty
              pure $ the (List (Doc MarkdownAnn)) [annotate MDCode $ unAnnotate $ prettyBy Idris.Doc.Annotations.Syntax ty]
         pure $ case concat docss of
           [] => []
           [doc] => [annotate (MDHeader 3) "Hint" <++> annotate MDCode doc]
           docs  => [vcat [annotate (MDHeader 3) "Hints"
                    , annotate MDCode $
                        vcat docs]]

getHintsForType : {auto c : Ref Ctxt Defs} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  Name -> Core (List (Doc MarkdownAnn))
getHintsForType nty
    = do Core.Context.Log.log "doc.data" 10 $ "Looking at \{show nty}"
         getImplDocs $ \ ty =>
           do let nms = allGlobals ty
              Core.Context.Log.log "doc.data" 10 $ unlines
                [ "Candidate: " ++ show ty
                , "Containing names: " ++ show nms
                ]
              pure $ isJust (lookup nty nms)


export
getMarkdownDocsForName : {auto o : Ref ROpts REPLOpts}
  -> {auto c : Ref Ctxt Defs}
  -> {auto s : Ref Syn SyntaxInfo}
  -> FC -> Name -> Config -> Core (Doc MarkdownAnn)
getMarkdownDocsForName fc n config = do
  syn <- get Syn
  defs <- get Ctxt
  let extra = case nameRoot n of
                "-" => [NS numNS (UN $ Basic "negate")]
                _ => []
  resolved <- lookupCtxtName n (gamma defs)
  let all@(_ :: _) = extra ++ map fst resolved
      | _ => undefinedName fc n
  let ns@(_ :: _) = concatMap (\n => lookupName n (defDocstrings syn)) all
      | [] => pure emptyDoc
  docs <- traverse (showDoc config) ns
  pure $ vcat docs
  where

    showDoc : Config -> (Name, String) -> Core (Doc MarkdownAnn)

    --reflowDoc : String -> List (Doc MarkdownAnn)
    --reflowDoc str = map (indent 2 . pretty0) (lines str)

    formatDocComment : String -> List (Doc MarkdownAnn)
    formatDocComment str = go (lines str)
      where
        go : List String -> List (Doc MarkdownAnn)
        go (x :: y :: xs) = pretty0 (if "@" `isPrefixOf` y then x ++ "  " else x) :: go (y :: xs)
        go [line] = [pretty0 line]
        go [] = []

    showTotal : Totality -> Maybe (Doc MarkdownAnn)
    showTotal tot
        = case isTerminating tot of
              Unchecked => Nothing
              _ => pure (pretty0 tot)

    showVisible : Visibility -> Doc MarkdownAnn
    showVisible vis = pretty0 vis

    getDConDoc : {default True showType : Bool} -> Name -> Core (Doc MarkdownAnn)
    getDConDoc con = do
      defs <- get Ctxt
      Just def <- lookupCtxtExact con (gamma defs)
            -- should never happen, since we know that the DCon exists:
            | Nothing => pure Empty
      syn <- get Syn
      ty <- prettyType Idris.Doc.Annotations.Syntax (type def)
      let ty = unAnnotate ty
      let conWithTypeDoc
            = annotate MDCode --(Decl con)
            $ unAnnotate
            $ ifThenElse showType
                (hsep [dCon con (prettyName con), colon, ty])
                (dCon con (prettyName con))
      case Libraries.Data.ANameMap.lookupName con (defDocstrings syn) of
        [(n, "")] => pure conWithTypeDoc
        [(n, str)] => pure $ vcat
              [ conWithTypeDoc
              , annotate MDRaw
              $ vcat $ formatDocComment str
              ]
        _ => pure conWithTypeDoc

    ||| The name corresponds to an implementation, typeset its type accordingly
    getImplDoc : Name -> Core (List (Doc MarkdownAnn))
    getImplDoc n = do
      defs <- get Ctxt
      Just def <- lookupCtxtExact n (gamma defs)
            | Nothing => pure []
      ty <- prettyType Idris.Doc.Annotations.Syntax (type def)
      let ty = unAnnotate ty
      pure [annotate MDCode ty]

    getMethDoc : Method -> Core (List (Doc MarkdownAnn))
    getMethDoc meth = do
      syn <- get Syn
      let [nstr] = lookupName meth.name (defDocstrings syn)
            | _ => pure []
      pure <$> showDoc methodsConfig nstr

    getInfixDoc : Name -> Core (List (Doc MarkdownAnn))
    getInfixDoc n = do
      --let Just (Basic n) = userNameRoot n
      --        | _ => pure []
      --let Just (_, fixity, assoc) = S.lookup n (infixes !(get Syn))
      let Just (_, fixity, assoc) = lookupExact n (infixes !(get Syn))
              | Nothing => pure []
      --pure $ pure $ hsep
      --      [ pretty0 (show fixity)
      --      , "operator,"
      --      , "level"
      --      , pretty0 (show assoc)
      --      ]
      pure $ pure $ hsep
            [ pretty0 (show fixity)
            , pretty0 (show assoc)
            , pretty0 n
            ]

    getPrefixDoc : Name -> Core (List (Doc MarkdownAnn))
    getPrefixDoc n = do
      --let Just (Basic n) = userNameRoot n
      --        | _ => pure []
      --let Just (_, assoc) = S.lookup n (prefixes !(get Syn))
      let Just (_, assoc) = lookupExact n (prefixes !(get Syn))
              | Nothing => pure []
      --pure $ ["prefix operator, level" <++> pretty0 (show assoc)]
      pure $ ["prefix" <++> pretty0 (show assoc) <++> pretty0 n]

    getFixityDoc : Name -> Core (List (Doc MarkdownAnn))
    getFixityDoc n =
      pure $ case toList !(getInfixDoc n) ++ toList !(getPrefixDoc n) of
        []  => []
        [f] => [annotate (MDHeader 3) "Fixity Declaration" <+> annotate MDCode f]
        fs  => [annotate (MDHeader 3) "Fixity Declarations" <+> annotate MDCode (vcat fs)]

    getIFaceDoc : (Name, IFaceInfo) -> Core (Doc MarkdownAnn)
    getIFaceDoc (n, iface) = do
      let params = case params iface of
              [] => []
              ps => [hsep (annotate (MDHeader 3) "Parameters" :: punctuate comma (map pretty0 ps))]
      let constraints = case !(traverse (pterm . map defaultKindedName) (parents iface)) of
              [] => []
              ps => [annotate (MDHeader 3) "Constraints" <+> vcat (map (annotate MDCode . unAnnotate . prettyBy Idris.Doc.Annotations.Syntax) ps)]
      icon <- do
        cName <- toFullNames (iconstructor iface)
        case dropNS cName of
          UN{} => do
            doc <- getDConDoc {showType = False} cName
            pure $ [annotate (MDHeader 3) "Constructor" <+> doc]
          _ => pure [] -- machine inserted
      mdocs <- traverse getMethDoc (methods iface)
      let meths = case concat mdocs of
                    [] => []
                    docs => [annotate (MDHeader 3) "Methods" <+> vcat docs]
      sd <- getSearchData fc False n
      idocs <- case hintGroups sd of
                    [] => pure (the (List (List (Doc MarkdownAnn))) [])
                    ((_, tophs) :: _) => traverse getImplDoc tophs
      let insts = case concat idocs of
                    [] => []
                    [doc] => [annotate (MDHeader 3) "Implementation" <+> doc]
                    docs => [annotate (MDHeader 3) "Implementations" <+> vcat docs]
      pure (vcat (params ++ constraints ++ icon ++ meths ++ insts))

    getFieldDoc : Name -> Core (Doc MarkdownAnn)
    getFieldDoc nm = do
      syn <- get Syn
      defs <- get Ctxt
      Just def <- lookupCtxtExact nm (gamma defs)
            -- should never happen, since we know that the DCon exists:
            | Nothing => pure Empty
      ty <- prettyType Syntax (type def)
      --let ty = unAnnotate ty
      let projDecl = annotate MDCode $
                        unAnnotate (prettyRig def.multiplicity)
                        <+> unAnnotate (hsep [ fun nm (prettyName nm), colon, ty ])
      case lookupName nm (defDocstrings syn) of
            [(_, "")] => pure projDecl
            [(_, str)] =>
              pure $ vcat [ projDecl
                          , annotate MDRaw
                          $ vcat $ formatDocComment str
                          ]
            _ => pure projDecl

    getFieldsDoc : Name -> Core (Maybe (Doc MarkdownAnn))
    getFieldsDoc recName = do
      let (Just ns, n) = displayName recName
          | _ => pure Nothing
      let recNS = ns <.> mkNamespace n
      defs <- get Ctxt
      let fields = getFieldNames (gamma defs) recNS
      case fields of
        [] => pure Nothing
        [proj] => pure $ Just $ annotate (MDHeader 3) "Projection" <+> !(getFieldDoc proj)
        projs => pure $ Just $ vcat
                      [ annotate (MDHeader 3) "Projections"
                      , vcat $
                          map (indent 2) $ !(traverse getFieldDoc projs)
                      ]

    --getExtra : Name -> GlobalDef -> Core (Maybe String, Maybe (Doc MarkdownAnn), List (Doc MarkdownAnn))
    --getExtra n d = do
    --  let tot = showVisible (visibility d) <++> maybe Empty id (showTotal (totality d))
    --  syn <- get Syn
    --  let [] = lookupName n (ifaces syn)
    --      | [ifacedata] => pure (Just "interface", Just tot, [!(getIFaceDoc ifacedata)])
    --      | _ => pure (Nothing, Nothing, []) -- shouldn't happen, we've resolved ambiguity by now
    --  case definition d of
    --    PMDef _ _ _ _ _ => pure (Nothing, Just tot, [])
    --    TCon _ _ _ _ _ _ cons _ => do
    --      cdocs <- traverse (getDConDoc <=< toFullNames) cons
    --      cdoc <- case cdocs of
    --        [] => pure (Just "data", the (List (Doc MarkdownAnn)) [])
    --        [doc] =>
    --          let cdoc = annotate (MDHeader 3) "Constructor" <++> doc in
    --          case !(getFieldsDoc n) of
    --            Nothing => pure (Just "data", the (List (Doc MarkdownAnn)) [cdoc])
    --            Just fs => pure (Just "record", the (List (Doc MarkdownAnn)) $ cdoc :: [fs])
    --        docs => pure (Just "data"
    --                    , the (List (Doc MarkdownAnn)) [vcat [annotate (MDHeader 3) "Constructors"
    --                            , vcat $ map (indent 2) docs]])
    --      idoc <- getHintsForType n
    --      --pure (map (\ cons => tot ++ cons ++ idoc) cdoc)
    --      --pure (fst cdoc, Just tot, snd cdoc ++ idoc)
    --      pure (fst cdoc, Just tot, snd cdoc ++ idoc)
    --    _ => pure (Nothing, Nothing, [])

    getExtra : Name -> GlobalDef -> Core (Maybe String, Maybe (Doc MarkdownAnn), List (Doc MarkdownAnn))
    getExtra n d = do
      do syn <- get Syn
         let [] = lookupName n (ifaces syn)
             | [ifacedata] => (Just "interface", Nothing,) . pure <$> getIFaceDoc ifacedata
             | _ => pure (Nothing, Nothing, []) -- shouldn't happen, we've resolved ambiguity by now
         case definition d of
           PMDef _ _ _ _ _ => pure ( Nothing, Nothing
                                   , catMaybes [ showTotal (totality d)
                                               , pure (showVisible (collapseDefault $ visibility d))])
           TCon _ _ _ _ _ _ cons _ =>
             do let tot = catMaybes [ showTotal (totality d)
                                    , pure (showVisible (collapseDefault $ visibility d))]
                cdocs <- traverse (getDConDoc <=< toFullNames) cons
                cdoc <- case cdocs of
                  [] => pure (Just "data", the (List (Doc MarkdownAnn)) [])
                  [doc] =>
                    let cdoc = annotate (MDHeader 3) "Constructor" <++> doc in
                    case !(getFieldsDoc n) of
                      Nothing => pure (Just "data", the (List (Doc MarkdownAnn)) [cdoc])
                      Just fs => pure (Just "record", the (List (Doc MarkdownAnn)) $ cdoc :: [fs])
                  docs => pure (Just "data"
                               , the (List (Doc MarkdownAnn)) [vcat [annotate (MDHeader 3) "Constructors"
                                       , vcat $ map (indent 2) docs]])
                idoc <- getHintsForType n
                --pure (map (\ cons => tot ++ cons ++ idoc) cdoc)
                pure (fst cdoc, Just (hsep tot), snd cdoc ++ idoc)
           _ => pure (Nothing, Nothing, [])

    showDoc (MkConfig {showType, longNames, dropFirst, getTotality}) (n, str) = do
      defs <- get Ctxt
      Just def <- lookupCtxtExact n (gamma defs)
            | Nothing => undefinedName fc n
      -- First get the extra stuff because this also tells us whether a
      -- definition is `data`, `record`, or `interface`.
      (typ, pre, extra) <- ifThenElse getTotality
                        (getExtra n def)
                        (pure (Nothing, Nothing, []))

      -- Then form the type declaration
      ty <- resugar [] =<< normaliseHoles defs [] (type def)
      -- when printing e.g. interface methods there is no point in
      -- repeating the interface's name
      let ty = ifThenElse (not dropFirst) ty $ case ty of
                  PPi _ _ AutoImplicit _ _ sc => sc
                  _ => ty
      nm <- aliasName n
      --let prig = reAnnotate Syntax $ prettyRig def.multiplicity
      let prig = unAnnotate $ prettyRig def.multiplicity
      let cat = showCategory Syntax def
      let nm = unAnnotate $ prettyKindedName typ $ cat
              $ ifThenElse longNames (pretty0 (show nm)) (prettyName nm)
      let deprecated = if Context.Deprecate `elem` def.flags
                          then annotate (MDHeader 4) "=DEPRECATED=" <+> line else emptyDoc
      --let docDecl = deprecated <+> annotate (Decl n) (hsep [prig <+> nm, colon, prettyBy Syntax ty])
      let docDecl = deprecated <+> annotate MDCode (maybe Empty (<+> hardline) pre <+> hsep [prig <+> nm, colon, unAnnotate $ prettyBy Idris.Doc.Annotations.Syntax ty])
      
      ---- Finally add the user-provided docstring
      let docText = let docs = formatDocComment str in
                    --annotate UserDocString (vcat docs)
                    annotate MDRaw (vcat docs)
                    <$ guard (not $ null docs)
      fixes <- getFixityDoc n
      let docBody =
            let docs = extra ++ fixes -- map (indent 2) extra--(extra ++ fixes)
            in --annotate DocStringBody
              (concatWith (\l, r => l <+> hardline <+> r) docs)
              <$ guard (not (null docs))
      --let maybeDocDecl = [docDecl | showType]
      --pure . vcat . catMaybes $ maybeDocDecl :: (map Just $ docBody)
      pure $ docDecl <+> maybe Empty (hardline <+>) docText <+> maybe Empty (hardline <+>) docBody

idrisAnnToMarkdownAnn : IdrisDocAnn -> MarkdownAnn
idrisAnnToMarkdownAnn Header = MDHeader 3
idrisAnnToMarkdownAnn Deprecation = MDRaw
idrisAnnToMarkdownAnn Declarations = MDRaw
idrisAnnToMarkdownAnn (Decl n) = MDCode
idrisAnnToMarkdownAnn DocStringBody = MDRaw
idrisAnnToMarkdownAnn UserDocString = MDRaw
idrisAnnToMarkdownAnn (Syntax x) = MDRaw

%deprecate
export
renderMDString : SimpleDocStream MarkdownAnn -> String
renderMDString = evalState [] . go
  where
    push' : MarkdownAnn -> Maybe MarkdownAnn -> String
    push' (MDHeader n) _ = replicate n '#' ++ " "
    push' MDCode (Just MDCode) = ""
    push' MDCode _ = "\n```idris\n"
    push' MDRaw (Just MDCode) = "\n```\n"
    push' MDRaw _ = ""

    pop' : MarkdownAnn -> Maybe MarkdownAnn -> String
    pop' (MDHeader _) _ = "\n"
    pop' MDCode (Just MDCode) = ""
    pop' MDCode _ = "\n```\n"
    pop' MDRaw (Just MDCode) = "\n```idris\n"
    pop' MDRaw _ = ""

    push : MarkdownAnn -> State (List MarkdownAnn) String
    push ann = do
      prev <- gets head'
      modify (ann ::)
      pure (push' ann prev)
    
    pop : State (List MarkdownAnn) String
    pop = case !get of
      ann :: prev :: stack => put (prev :: stack) >> pure (pop' ann (Just prev))
      [ann] => put [] >> pure (pop' ann Nothing)
      [] => pure ""

    go : SimpleDocStream MarkdownAnn -> State (List MarkdownAnn) String
    go SEmpty = pure ""
    go (SChar c rest) = pure $ strCons c !(go rest)
    go (SText _ t rest) = pure $ t ++ !(go rest)
    go (SLine l rest) = pure $ "\n" ++ textSpaces l ++ !(go rest)
    go (SAnnPush ann rest) = pure $ !(push ann) ++ !(go rest)
    go (SAnnPop rest) = pure $ !pop ++ !(go rest)

