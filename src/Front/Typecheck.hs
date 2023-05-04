module Front.Typecheck where

import Data.Maybe
import Front.Ast
import Data.List
import qualified Data.Set as Set
import qualified Unbound.Generics.LocallyNameless as Unbound
import System.IO(withFile, IOMode(ReadMode), hGetContents, hPutStrLn, stderr)


-- type Ctx = [(String, Type)]

-- -- -- | Return the free variables in an expression
fv :: Term -> Set.Set String
fv (Var s) = Set.singleton s
fv (Lam s e) = Set.difference (fv e) (Set.singleton s)
fv (App e1 e2) = Set.union (fv e1) (fv e2)
fv (PI s t1 t2) = Set.difference (fv t2) (Set.singleton s)
fv (Ann x t) = fv x
-- fv (TrustMe) = Set.empty
-- fv (PrintMe) = Set.empty
-- fv (Let x e1 e2) = Set.difference (fv e2) (Set.singleton x)
-- fv (TUnit) = Set.empty
-- fv (VUnit) = Set.empty
-- fv (TBool) = Set.empty
-- fv (VBool) = Set.empty
-- fv (If e1 e2 e3) = Set.union (Set.union (fv e1) (fv e2)) (fv e3)
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
                                     then PI s t1 (subst n x t2)
                                     else PI newvar t1 (subst n x (subst (Var newvar) s t2))
 where newvar = pickFresh (Set.union (fv n) (fv t2)) s

subst n x (Ann v t) = subst n x v


pickFresh :: Set.Set String -> String -> String
pickFresh s = pickFresh'
  where pickFresh' n | n `Set.notMember` s = n
        pickFresh' n                       = pickFresh' $ n ++ "'"



type Ctx = [Decl]


extendCtx :: Ctx -> Decl -> Ctx
extendCtx ctx delc = delc : ctx


checkIsType :: Type -> Type -> Either String Type
checkIsType t1 t2 | equate t1 t2 = Right t1
                  | otherwise = Left $ printTypeDoesNotMatch t1 t2


lookupTy :: Ctx -> String -> Either String Type
lookupTy [] x = Left ("failed to find variable" ++ x)
lookupTy ((TypeSig sig):ls) x | sigName sig == x = Right (sigType sig)
                              | otherwise = lookupTy ls x
lookupTy (d:ls) x = lookupTy ls x


infer :: Program -> Ctx -> IO ()
infer (Program p) = inferProgram p


inferProgram :: [Decl] -> Ctx -> IO ()
inferProgram [] ctx = printTypeSig ctx
inferProgram (def@(Def s t):ls) ctx =
    case lookupTy ctx s of
        Right tysig -> (do let t1 = checkType t ctx tysig
                           case t1 of
                            Right t2 -> inferProgram ls (extendCtx ctx def)
                            Left msg -> do putStrLn msg)
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

inferType Type ctx Nothing  = Right Type

inferType (PI x tyA tyB) ctx Nothing = do
    type2 <- checkType tyA ctx Type
    checkType tyB (extendCtx ctx (mkSig x (eval type2))) Type


inferType (Ann x t) ctx Nothing = do
    type1 <- checkType t ctx Type
    checkType x ctx (eval type1)

inferType (App e1 e2) ctx Nothing = do
    type1 <- inferType e1 ctx Nothing
    (x, tyA, tyB) <- ensurePi type1
    type2 <- checkType e2 ctx tyA
    return $ eval (subst e2 x tyB)

inferType (Lam x e1) ctx (Just (PI x1 tyA tyB)) = do
    (if x == x1
    then checkType e1 (extendCtx ctx (mkSig x tyA)) tyB
    else Left (printVarDoesNotMatch x x1))


inferType Refl ctx (Just t@(TyEq a b)) = if equate a b then Right t else Left (printTypeDoesNotMatch Refl t)

inferType (TyEq a b) ctx _ = do
    tA <- inferType a ctx Nothing
    tB <- inferType b ctx Nothing
    checkIsType tA tB

inferType e ctx (Just t) = do typ <- inferType e ctx Nothing
                              checkIsType t typ


-- inferType (Subst a y) ctx (Just tA) =
--     do tyB <- inferType y ctx Nothing
--        (x,x1) <- ensureTyEQ tyB
--        case (x,x1) of
--            (Var x,_) ->
--                     case checkType a ctx (subst a2 x tA) of
--                        Nothing -> case checkType a ctx (subst x a2 tA) of
-- 									    Nothing -> Nothing
-- 										Just e -> Just tA
-- 					   Just e -> Just tA
-- 		   (_, Var x) -> case checkType a ctx (subst a2 x tA) of
--                        Nothing -> case checkType a ctx (subst x a2 tA) of
-- 									    Nothing -> Nothing
-- 										Just e -> Just tA
-- 					   Just e -> Just tA


-- inferType (Contra a) ctx (Just B) = 
-- 	do inferType a ctx A = 


ensureTyEQ (TyEq a b) = do return (a,b)
ensureTyEQ _ = Left "Not match Equal Type"



ensurePi :: Type -> Either String (String, Type, Type)
ensurePi t@(PI s tyA tyB) = do return (s, tyA, tyB)
ensurePi t = Left "Not match PI"


eval :: Term -> Term
eval (VBool True) = VBool True
eval (VBool False) = VBool False
eval (Ann e t) = eval e
eval Type = Type
eval (Var x) = Var x
eval (PI x tyA tyB) = PI x (eval tyA) (eval tyB)
eval (Lam x e) = Lam x (eval e)
eval (App e1 e2) = let e1' = eval e1 in
                   case e1' of
                    Lam x e -> subst e2 x e
                    _ -> App e1' (eval e2)


equate :: Term -> Term -> Bool
equate Type Type = True
equate (Var x) (Var y) = x == y
equate (Lam x e) (Lam x1 e1) = equate e e1
equate (Ann x _) (Ann x1 _) = equate x x1
equate (PI x tyA tyB) (PI y tyA' tyB') = equate tyA tyA' && equate tyB tyB'
equate e1 e2 = equate (eval e1) (eval e2)

checkType :: Term -> Ctx -> Type -> Either String Type
checkType e ctx t = inferType e ctx (Just t)