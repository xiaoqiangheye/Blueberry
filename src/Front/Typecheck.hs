module Front.Typecheck where

import Data.Maybe
import Front.Ast
import Data.List
import qualified Data.Set as Set
import qualified Unbound.Generics.LocallyNameless as Unbound
import System.IO(withFile, IOMode(ReadMode), hGetContents, hPutStrLn, stderr)
import Data.Bool (Bool)




-- -- -- | Return the free variables in an expression
fv :: Term -> Set.Set String
fv (Var s) = Set.singleton s
fv (Lam s e) = Set.difference (fv e) (Set.singleton s)
fv (App e1 e2) = Set.union (fv e1) (fv e2)
fv (PI s t1 t2) = Set.difference (Set.union (fv t1) (fv t2)) (Set.singleton s)
fv (Ann x t) = fv x
fv TUnit = Set.empty
fv VUnit = Set.empty
fv TBool = Set.empty
fv (VBool _) = Set.empty
fv (If e1 e2 e3) = Set.union (Set.union (fv e1) (fv e2)) (fv e3)
fv (Pair e1 e2) = Set.union (fv e1) (fv e2)
fv (Sigma x e1 e2) = Set.difference (Set.union (fv e1) (fv e2)) (Set.singleton x)
fv (TyEq t1 t2) = Set.union (fv t1) (fv t2)
fv Refl = Set.empty
fv (Subst t1 t2) = Set.union (fv t1) (fv t2)
fv (Contra t) = fv t
fv (Let x a b) = Set.difference (Set.union (fv a) (fv b)) (Set.singleton x)


-- fv (Prod e1 e2) = Set.union (fv e1) (fv e2)


subst :: Term -> String -> Term -> Term
subst n x (Var y) | x == y = n
                  | otherwise = Var y
subst n x (App e1 e2) = App (subst n x e1) (subst n x e2)
subst n x (Lam s e) | s == x = Lam s e
                    | otherwise = if Set.notMember s (fv n)
                                  then Lam s (subst n x e)
                                  else Lam newvar (subst n x (subst (Var newvar) s e))
 where newvar = pickFresh (Set.union (fv n) (fv e)) s

subst n x (PI s t1 t2) | s == x = PI s t1 t2
                       | otherwise = if Set.notMember s (fv n)
                                     then PI s (subst n x t1) (subst n x t2)
                                     else PI newvar (subst n x t1) (subst n x (subst (Var newvar) s t2))
 where newvar = pickFresh (Set.union (fv n) (fv t2)) s

subst n x (Ann v t) = subst n x v
subst n x (If a b1 b2) = If (subst n x a) (subst n x b1) (subst n x b2)
subst n x (TyEq t1 t2) = TyEq (subst n x t1) (subst n x t2)
subst n x Refl = Refl
subst n x (Subst t1 t2) = Subst (subst n x t1) (subst n x t2)
subst n x (Contra t) = Contra (subst n x t)
subst n x (Let s a b) | x == s = Let s a b
                      | otherwise = if Set.notMember s (fv n)
                                    then Let s (subst n x a) (subst n x b)
                                    else Let newvar (subst n x a) (subst n x (subst (Var newvar) s b))
 where newvar = pickFresh (Set.union (fv n) (fv b)) s

subst n x e = e


pickFresh :: Set.Set String -> String -> String
pickFresh s = pickFresh'
  where pickFresh' n | n `Set.notMember` s = n
        pickFresh' n                       = pickFresh' $ n ++ "'"



type Ctx = [Decl]


extendCtx :: Ctx -> Decl -> Ctx
extendCtx ctx delc = delc : ctx

extendCtxs :: Ctx -> [Decl] -> Ctx
extendCtxs ctx decl = decl ++ ctx

checkIsType :: Type -> Type -> Ctx -> Either String Type
checkIsType t1 t2 ctx | equal t1 t2 ctx = Right t1
                      | otherwise = Left $ printTypeDoesNotMatch t1 t2


lookupTy :: Ctx -> String -> Either String Type
lookupTy [] x = Left ("failed to find variable " ++ x)
lookupTy ((TypeSig sig):ls) x | sigName sig == x = Right (sigType sig)
                              | otherwise = lookupTy ls x
lookupTy (d:ls) x = lookupTy ls x

lookupDef :: Ctx -> String -> Either String Term
lookupDef [] x = Left ("failed to find def " ++ x)
lookupDef ((Def x t):ls) y   | x == y = Right t
                             | otherwise = lookupTy ls y
lookupDef (d:ls) x = lookupDef ls x

infer :: Program -> Ctx -> IO ()
infer (Program p) = inferProgram $ reverse p


inferProgram :: [Decl] -> Ctx -> IO ()
inferProgram [] ctx = do putStrLn "Typechecking Success! Let's get some blueberry!"
inferProgram (def@(Def s t):ls) ctx =
    case lookupTy ctx s of
        Right tysig -> (do let t1 = checkType t ctx tysig
                           case t1 of
                            Right t2 -> inferProgram ls (extendCtx ctx def)
                            Left msg -> do  putStrLn ("Type check failed when infer def: " ++ show def ++ ", tysig: " ++ show tysig)
                                            putStrLn msg)
        Left msg -> do putStrLn msg

inferProgram (a@(TypeSig sig):ls) ctx = inferProgram ls (extendCtx ctx a)
inferProgram _ _ = return ()


printTypeSig :: Ctx -> IO ()
printTypeSig ((TypeSig sig): ls) = do
  print sig
  printTypeSig ls
printTypeSig _ = return ()

printTypeDoesNotMatch :: Type -> Type -> String
printTypeDoesNotMatch t1 t2 =
    "Type does not match: " ++ show t1 ++ "," ++ show t2

printVarDoesNotMatch x y =
     "Variable name does not match: " ++ x ++ "," ++ y



inferType :: Term -> Ctx -> Maybe Type -> Either String Type
inferType (Var x) ctx Nothing = lookupTy ctx x

inferType TUnit ctx Nothing = Right Type

inferType VUnit ctx Nothing = Right TUnit

inferType TBool ctx Nothing = Right Type

inferType (VBool _) ctx Nothing = Right TBool

inferType (If a b1 b2) ctx (Just t) = do
    checkType a ctx TBool
    case a of
      (Var x) -> do
        ttrue <- eval (subst (VBool True) x t) ctx
        tfalse <- eval (subst (VBool False) x t) ctx
        -- checkType b1 (extendCtx ctx (Def x (VBool True))) t
        -- checkType b2 (extendCtx ctx (Def x (VBool False))) t
        return t
      _ -> do t1 <- eval t ctx
              checkType b1 ctx t1
              checkType b2 ctx t1
              return t

inferType Type ctx Nothing  = Right Type

inferType (PI x tyA tyB) ctx Nothing = do
    type2 <- checkType tyA ctx Type
    t2 <- eval type2 ctx
    checkType tyB (extendCtx ctx (mkSig x t2)) Type


inferType (Ann x t) ctx Nothing = do
    type1 <- checkType t ctx Type
    t1 <- eval type1 ctx
    checkType x ctx t1

inferType (App e1 e2) ctx Nothing = do
    type1 <- inferType e1 ctx Nothing
    (x, tyA, tyB) <- ensurePi type1
    type2 <- checkType e2 ctx tyA
    eval (subst e2 x tyB) ctx


inferType (Sigma x tyA tyB) ctx Nothing = do
    t1 <- checkType tyA ctx Type
    type1 <- eval t1 ctx
    checkType tyB (extendCtx ctx (mkSig x type1)) Type
    return Type

inferType (Pair t1 t2) ctx (Just t@(Sigma x tyA tyB)) = do
    checkType t1 ctx tyA
    tyB' <- eval (subst t1 x tyB) ctx
    checkType t2 ctx tyB'
    return t

inferType (Lam x e1) ctx (Just (PI x1 tyA tyB)) = do
    (if x == x1 || x1 == "_"
    then do tyA' <- eval tyA ctx
            tyB' <- eval tyB ctx
            checkType e1 (extendCtx ctx (mkSig x tyA')) tyB'
    else Left (printVarDoesNotMatch x x1))


inferType (Let x a b) ctx (Just tB) = do
    tA <- inferType a ctx Nothing
    checkType b (extendCtx (extendCtx ctx (mkSig x tA)) (Def x a)) tB
    return tB

inferType (Let x a b) ctx Nothing = do
    tA <- inferType a ctx Nothing
    tB <- inferType b (extendCtx (extendCtx ctx (mkSig x tA)) (Def x a)) Nothing
    return (subst a x tB)



inferType (Lam x e1) ctx (Just t) = Left (printTypeDoesNotMatch (Lam x e1) t)


inferType Refl ctx (Just t@(TyEq a b)) =
    do a' <- eval a ctx
       b' <- eval b ctx
       checkIsType a' b' ctx
       return t


inferType (TyEq a b) ctx Nothing = do
    tA <- inferType a ctx Nothing
    tB <- inferType b ctx Nothing
    tA' <- eval tA ctx
    tB' <- eval tB ctx
    checkIsType tA' tB' ctx
    return Type


inferType (Subst a y) ctx (Just tA) =
    do tyB <- inferType y ctx Nothing
       tyB' <- eval tyB ctx
       (x,x1) <- ensureTyEQ tyB
       case (x,x1) of
           (Var x2, Var x3) -> (do let t = checkType a ctx (subst (Var x2) x3 tA)
                                   case t of
                                     Left _ -> checkType a ctx (subst (Var x3) x2 tA)
                                     _ -> return tA)
           (Var x2, a2) -> (do checkType a ctx (subst a2 x2 tA)
                               return tA)
           (a2, Var x2) -> (do checkType a ctx (subst a2 x2 tA)
                               return tA)
           (_,_) ->  Left "not able to subst"

inferType t@(Subst a y) ctx Nothing = Left $ "can't infer " ++ show t



inferType (Contra t) ctx (Just tB) =
    do tA <- inferType t ctx Nothing
       tA' <- eval tA ctx
       (a,b) <- ensureTyEQ tA'
       a' <- eval a ctx
       b' <- eval b ctx
       case (a',b') of
        (VBool True, VBool False) -> return tB
        (VBool False, VBool True) -> return tB
        _ -> Left ("can't use contra since neigher branch reduces to True = False or False = True, " ++ show a' ++ show b')



-- inferType (Contra a) ctx (Just B) = 
-- 	do inferType a ctx A = 


inferType e ctx (Just t) = do typ <- inferType e ctx Nothing
                              t1 <- eval t ctx
                              t2 <- eval typ ctx
                              checkIsType t1 t2 ctx


ensureTyEQ (TyEq a b) = do return (a,b)
ensureTyEQ _ = Left "Not match Equal Type"



ensurePi :: Type -> Either String (String, Type, Type)
ensurePi t@(PI s tyA tyB) = do return (s, tyA, tyB)
ensurePi t = Left "Not match PI"



-- whnf :: Term -> Ctx -> Either String Term
-- whnf (Lam x e) _ = Right (Lam x e)
-- whnf (Ann e t) _ = whnf e
-- whnf Type _ = Right Type
-- whnf (Var x) _ = Right (Var x)
-- whnf (PI s e1 e2) _ = Right (PI s e1 e2)
-- whnf (App e1 e2) _ = do e1' <- eval e1 ctx
--                         case e1' of
--                          Lam x e -> return $ subst e2 x e
--                          _ -> return $ App e1' e2
-- whnf (If t1 t2 t3) ctx = do
--     nf <- whnf t1
--     case nf of
--         (VBool bo) -> if bo then whnf t2 ctx else whnf t3 ctx
--         _ -> return (If nf t2 t3)
-- whnf (Subst tm pf) ctx = do
--     pf' <- whnf pf
--     case pf' of
--         Refl -> whnf tm
--         _ -> return (Subst rm pf')
-- whnf e _ = return e



eval :: Term -> Ctx -> Either String Term
eval (If t1 t2 t3) ctx = do
    nf <- eval t1 ctx
    case nf of
        (VBool bo) -> if bo then eval t2 ctx else eval t3 ctx
        _ -> return (If nf t2 t3)

-- eval TBool _ = Right TBool
-- eval (Sigma x t1 t2) ctx = do t1' <- eval t1 ctx
--                               t2' <- eval t2 ctx
--                               return $ Sigma x t1' t2'
eval (Ann e t) ctx = eval e ctx
eval (Var x) ctx = case lookupDef ctx x of
                        Right e -> Right e
                        Left _ -> return $ Var x
-- eval (PI x tyA tyB) ctx = do tyA' <- eval tyA ctx
--                              tyB' <- eval tyB ctx
--                              return $ PI x tyA' tyB'
-- eval (Lam x e) ctx = do u <- eval e ctx
--                         return $ Lam x u
eval (App e1 e2) ctx = do e1' <- eval e1 ctx
                          case e1' of
                            Lam x e -> return $ subst e2 x e
                            _ -> do e2' <- eval e2 ctx
                                    return $ App e1' e2'
eval (Subst tm pf) ctx = do
    pf' <- eval pf ctx
    case pf' of
        Refl -> eval tm ctx
        _ -> return (Subst tm pf')

eval e ctx = return e
-- eval (TyEq t1 t2) ctx = do t1' <- eval t1 ctx
--                            t2' <- eval t2 ctx
--                            return $ TyEq t1' t2'
-- eval (Contra t) ctx = do t' <- eval t ctx
--                          return $ Contra t'


equal :: Term -> Term -> Ctx -> Bool
equal e1 e2 ctx =
    let e1' = eval e1 ctx in
    let e2' = eval e2 ctx in
    case (e1',e2') of
        (Right e1'', Right e2'') -> equate e1'' e2''
        _ -> False
  where
    equate (Var x1) (Var x2) = x1 == x2
    equate (App e1 e2) (App e1' e2') = equal e1 e1' ctx && equal e2 e2' ctx
    equate (PI x e1 e2) (PI x' e1' e2') = 
        equal e1 e1' ctx && equal e2 (subst (Var x) x' e2') ctx
    equate (Lam x e) (Lam y e') = equal e (subst (Var x) y e') ctx
    equate (Ann x _) (Ann x1 _) = equal x x1 ctx
    equate (If a b1 b2) (If a' b1' b2') = equal a a' ctx && equal b1 b1' ctx && equal b2 b2' ctx
    equate (Sigma x t1 t2) (Sigma y t1' t2') = 
        equal t1 t1' ctx && equal t2 (subst (Var x) y t2') ctx
    equate (Let x t1 t2) (Let y t1' t2') = x == y && equal t1 t1' ctx && equal t2 t2' ctx
    equate (VBool x) (VBool y) = x == y
    equate (TyEq t1 t2) (TyEq t1' t2') = equal t1 t1' ctx && equal t2 t2' ctx
    equate (Contra t') (Contra t) = equal t t' ctx
    equate (Subst a y) (Subst a' y') = equal a a' ctx && equal y y' ctx
    equate Type Type = True
    equate TUnit TUnit = True
    equate VUnit VUnit = True
    equate TBool TBool = True
    equate Refl Refl = True
    equate (Pair x y) (Pair x' y') = equal x x' ctx && equal y y' ctx
    equate e1 e2 = False


-- equate :: Term -> Term -> Either String ()
-- equate t1 t2 = do
--     n1 <- whnf t1
--     n2 <- whnf t2
--     case (n1,n2) of
--         (Type,Type) -> return ()
--         (Var y, Var y) | x== y -> return ()

    
-- equate n x
-- equate Type Type = True
-- equate TUnit TUnit = True
-- equate VUnit VUnit = True
-- equate TBool TBool = True
-- equate (VBool x) (VBool y) = x == y
-- equate (Var x) (Var y) = x == y
-- equate (Lam x e) (Lam x1 e1) = equate e e1
-- equate (Ann x _) (Ann x1 _) = equate x x1
-- equate (PI x tyA tyB) (PI y tyA' tyB') = equate tyA tyA' && equate tyB tyB'
-- equate (If a b1 b2) (If a' b1' b2') = equate a a' && equate b1 b1' && equate b2 b2'
-- equate (App e1 e2) (App e1' e2') = equate e1 e1' && equate e2 e2'
-- equate (Sigma x t1 t2) (Sigma y t1' t2') = equate t1 t1' && equate t2 t2'
-- equate (Let x t1 t2) (Let y t1' t2') = x == y && equate t1 t1' && equate t2 t2'

checkType :: Term -> Ctx -> Type -> Either String Type
checkType e ctx t = inferType e ctx (Just t)