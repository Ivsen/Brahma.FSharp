// Copyright (c) 2013 Semyon Grigorev <rsdpisuy@gmail.com>
// All rights reserved.
// 
// The contents of this file are made available under the terms of the
// Eclipse Public License v1.0 (the "License") which accompanies this
// distribution, and is available at the following URL:
// http://www.opensource.org/licenses/eclipse-1.0.php
// 
// Software distributed under the License is distributed on an "AS IS" basis,
// WITHOUT WARRANTY OF ANY KIND, either expressed or implied. See the License for
// the specific language governing rights and limitations under the License.
// 
// By using this software in any fashion, you are agreeing to be bound by the
// terms of the License.

module Brahma.FSharp.OpenCL.Translator.QuotationsTransformer

open Microsoft.FSharp.Quotations
open Brahma.FSharp.OpenCL.Translator.Type

let apply (expr:Expr) =
    let rec go expr = 
        match expr with    
        | Patterns.Application (expr1,expr2) -> translateApplication expr
        | Patterns.Call (exprOpt,mInfo,args) -> 
            match exprOpt with
            | Some e -> Expr.Call(go e, mInfo, args |> List.map go)
            | None -> Expr.Call(mInfo, args |> List.map go)
        | Patterns.ForIntegerRangeLoop (i, from, _to, _do) ->
            Expr.ForIntegerRangeLoop(i, from, _to, go _do)            
        | Patterns.IfThenElse (cond, thenExpr, elseExpr) ->
            Expr.IfThenElse(go cond, go thenExpr, go elseExpr)        
        | Patterns.Let (var, expr, inExpr) ->
            Expr.Let(var, go expr, go inExpr)
        | Patterns.Sequential(expr1,expr2) -> 
            Expr.Sequential(go expr1, go expr2)        
        | Patterns.VarSet(var,expr) -> 
            Expr.VarSet(var, go expr)
        | Patterns.WhileLoop(condExpr,bodyExpr) -> 
            Expr.WhileLoop(go condExpr, go bodyExpr)
        | Patterns.Lambda(v,e) ->
            Expr.Lambda(v,go e)
        | other -> other

    and translateApplication expr =
        let rec _go expr =
            match expr with            
            | Patterns.Application (Patterns.Lambda (fv,e),v) ->
                e.Substitute(fun x -> if x = fv then Some v else None) |> _go
            | Patterns.Application (e,v) ->
                let fb = go e
                Expr.Application(fb,v) |> _go 
            | e -> e
        let body = _go expr
        body

    go expr

let inlineLamdas (expr:Expr) =
    let rec go expr = 
        match expr with
        | Patterns.Let(var, expr, inExpr) ->
            match expr with
            | Patterns.Lambda _ ->
                inExpr.Substitute(fun x -> if x = var then Some expr else None) |> go
            | Patterns.Application _ -> Expr.Let(var, go expr |> apply, inExpr) |> go
            | e -> Expr.Let(var, expr, go inExpr)
        | Patterns.Application (expr1,expr2) -> Expr.Application (go expr1 |> apply, go expr2)
        | Patterns.Call (exprOpt,mInfo,args) ->
            match exprOpt with
            | Some e -> Expr.Call(go e, mInfo, args |> List.map go)
            | None -> Expr.Call(mInfo, args |> List.map go)
        | Patterns.ForIntegerRangeLoop (i, from, _to, _do) ->
            Expr.ForIntegerRangeLoop(i, from, _to, go _do)            
        | Patterns.IfThenElse (cond, thenExpr, elseExpr) ->
            Expr.IfThenElse(go cond, go thenExpr, go elseExpr)        
        | Patterns.Sequential(expr1,expr2) -> 
            Expr.Sequential(go expr1, go expr2)        
        | Patterns.VarSet(var,expr) -> 
            Expr.VarSet(var, go expr)
        | Patterns.WhileLoop(condExpr,bodyExpr) -> 
            Expr.WhileLoop(go condExpr, go bodyExpr)            
        | other -> other
    go expr

 // Copyright (c) 2014 Klimov Ivan <ivan.klimov.92@gmail.com>
  // deploy let
let rec recLet expr = 
    match expr with
    | Patterns.Let(v, valExpr, inExpr1) ->
        match valExpr with
        | Patterns.Let (var, inExpr, afterExpr) -> 
            let newLet = recLet ( Expr.Let(v, afterExpr, inExpr1))
            recLet (Expr.Let(var, inExpr, recLet newLet))
        | ExprShape.ShapeLambda(lv, lb) ->
            let newLet = recLet valExpr
            match newLet with
            | Patterns.Let (var, inExpr, afterExpr) -> 
                let newLetIn = (Expr.Let(v, afterExpr , inExpr1))
                recLet (Expr.Let(var, inExpr, recLet newLetIn))
            | _ ->
                Expr.Let(v, newLet , inExpr1) 
        | _ -> 
            Expr.Let(v, recLet valExpr, inExpr1)
    | ExprShape.ShapeVar(var) ->
        expr           
    | ExprShape.ShapeLambda(lv, lb) ->
        match lb with
        | Patterns.Let (var, inExpr, afterExpr) -> 
            Expr.Let(var, inExpr, (Expr.Lambda(lv, afterExpr)))
        | _ -> 
            let newExpr = recLet (lb)
            match newExpr with
            | Patterns.Let (var, inExpr, afterExpr) -> 
                Expr.Let(var, inExpr, (Expr.Lambda(lv, afterExpr)))
            | _ ->
                Expr.Lambda(lv, newExpr)
    | ExprShape.ShapeCombination(o, args) ->
        ExprShape.RebuildShapeCombination(o, List.map (fun (e:Expr) -> recLet (e)) args)

let rec quontationTransformerRec expr = 
    match expr with
    | ExprShape.ShapeLambda(lv, lb) ->
        Expr.Lambda(lv, quontationTransformerRec lb)
    | _ ->
        recLet expr

let renameAllTree expr (letScope:LetScope) (renamer1:Renamer) = 
    let rec renameRec expr =
        match expr with
        | Patterns.Lambda(param, body) ->
            let newName = renamer1.addName (param.Name)
            let NewVar = new Var(newName, param.Type, param.IsMutable)

            letScope.AddVarInLastLet param.Name newName param.Type

            let newLambda = Expr.Lambda(NewVar, renameRec body)
            newLambda
        | Patterns.Let(var, expr1, expr2) ->
            let newName = renamer1.addName (var.Name)
            let NewVar = new Var(newName, var.Type, var.IsMutable)

            letScope.LetIn var.Name newName var

            let prevStateIsInLet = letScope.GetIsInLastLet
            letScope.SetIsInLastLet true
            let exprIn = renameRec expr1

            letScope.SetIsInLastLet false
            let exprAfter = renameRec expr2
            letScope.SetIsInLastLet prevStateIsInLet
            letScope.LetOut |> ignore
            let newLet = Expr.Let(NewVar, exprIn, exprAfter)
            newLet
        | Patterns.Application(expr1, expr2) ->
            Expr.Application(renameRec expr1, renameRec expr2)
        | Patterns.Call(exprOpt, methodInfo, exprList) ->
            let newExprList = [for expr in exprList -> renameRec expr]
            Expr.Call(methodInfo, newExprList)
        | Patterns.Var(var) ->
            let newName = (letScope.GetNameForVarInLet var.Name (not letScope.GetIsInLastLet)).GetNewName
            let newVar = new Var(newName, var.Type, var.IsMutable)
            Expr.Var(newVar)
        | ExprShape.ShapeCombination (o, exprs) -> ExprShape.RebuildShapeCombination (o,List.map renameRec exprs)
        | other -> "OTHER!!! :" + string other |> failwith

    let rec quontationRenamerLetRec expr =
        match expr with
        | ExprShape.ShapeLambda(lv, lb) ->
            Expr.Lambda(lv, quontationRenamerLetRec lb)
        | _ ->
            renameRec expr
    quontationRenamerLetRec expr

let addNeededLamAndAppicatins expr (letScope:LetScope) =
    let rec addNeededLam expr =
        match expr with
        | ExprShape.ShapeVar(var) ->
            if(letScope.ContainsInfo var.Name) then
                let listNeededVars = (letScope.GetLetInfo var.Name).GetNeedVars
                if(listNeededVars.Count > 0) then
                    let mutable readyLet = Expr.Var((letScope.GetLetInfo var.Name).GetOrgnVar)
                    for elem in listNeededVars do
                        readyLet <- Expr.Application(readyLet, Expr.Var(new Var(elem.GetNewName, elem.GetVarType)))
                    readyLet
                else
                    expr 
             else
                expr          
        | Patterns.Let(var, expr1, expr2) ->
            let listNeededVars = (letScope.GetLetInfo var.Name).GetNeedVars
            if(listNeededVars.Count > 0) then
                let mutable readyLet = addNeededLam expr1
                listNeededVars.Reverse()
                for elem in listNeededVars do
                    readyLet <- Expr.Lambda(new Var(elem.GetNewName, elem.GetVarType), readyLet)
                let newVar = new Var(var.Name, readyLet.Type)
                (letScope.GetLetInfo var.Name).ChangeOrgnVar newVar
                Expr.Let( newVar, readyLet, addNeededLam expr2)
            else
                let ex1 = addNeededLam expr1
                let ex2 = addNeededLam expr2
                let newLet = Expr.Let(var, ex1, ex2)
                newLet
        | Patterns.Application(expr1, expr2) ->
            let exp1 = addNeededLam expr1
            let exp2 = addNeededLam expr2

            let mutable readyApp = Expr.Application(exp1, exp2)
            readyApp

        | ExprShape.ShapeLambda(lv, lb) ->
            let newExpr = addNeededLam (lb)
            Expr.Lambda(lv, newExpr)
        | ExprShape.ShapeCombination(o, args) ->
            ExprShape.RebuildShapeCombination(o, List.map (fun (e:Expr) -> addNeededLam (e)) args)

    let rec run expr =
        match expr with
        | ExprShape.ShapeLambda(lv, lb) ->
            (Expr.Lambda(lv, run lb))
        | _ ->
            addNeededLam expr
    run expr

//get list expr for translation
let getListLet expr =
    let listExpr = new ResizeArray<_>()
    let rec addLetInList expr =
        match expr with
        | Patterns.Let(var, exprIn, exprAfter) ->
            //let v = Expr.Var(new Var("some", var.Type))
            let newLet = Expr.Let(var, exprIn, Expr.Value(0)) // in  body some value
            listExpr.Add(newLet)
            addLetInList exprAfter
        | _ ->
            expr
    let rec firstLams expr =
        match expr with
        | Patterns.Lambda(lv, lb) ->
            Expr.Lambda(lv, firstLams lb)
        | _ ->
            addLetInList expr
    
    match expr with
    | Patterns.Lambda(lv, lb) ->
        listExpr.Add(firstLams (Expr.Lambda(lv, lb)))
        listExpr
    | _ -> 
        listExpr

let quontationTransformer expr translatorOptions =
    

    let renamer = new Renamer()
    let letScope = LetScope()
    let renamedTree = renameAllTree expr letScope renamer
    let qTransd = quontationTransformerRec renamedTree
    let addedLam = addNeededLamAndAppicatins qTransd letScope
    let listExpr = getListLet addedLam
    listExpr