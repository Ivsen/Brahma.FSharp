// Copyright (c) 2012, 2013 Semyon Grigorev <rsdpisuy@gmail.com>
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

module Brahma.FSharp.OpenCL.Translator.Type

open Brahma.FSharp.OpenCL.AST
open System.Reflection

let Translate (_type:System.Type) isKernelArg (collectedTypes:System.Collections.Generic.Dictionary<_,_>) size (context:TargetContext<_,_>) : Type<Lang> =
    let rec go (str:string) =
        match str.ToLowerInvariant() with
        | "int"| "int32" -> PrimitiveType<Lang>(Int) :> Type<Lang>
        | "int16" -> PrimitiveType<Lang>(Short) :> Type<Lang>
        | "uint16" -> PrimitiveType<Lang>(UShort) :> Type<Lang>
        | "uint32" -> PrimitiveType<Lang>(UInt) :> Type<Lang>
        | "float"| "float32" | "single"-> PrimitiveType<Lang>(Float) :> Type<Lang>
        | "byte" -> PrimitiveType<Lang>(UChar) :> Type<Lang>
        | "int64" -> PrimitiveType<Lang>(Long) :> Type<Lang>
        | "uint64" -> PrimitiveType<Lang>(ULong) :> Type<Lang>
        | "boolean" -> PrimitiveType<Lang>(Int) :> Type<Lang>
        | "double" -> 
            context.Flags.enableFP64 <- true
            PrimitiveType<Lang>(Double) :> Type<Lang>        
        | t when t.EndsWith "[]" ->
            let baseT = t.Substring(0,t.Length-2)
            if isKernelArg 
            then RefType<_>(go baseT) :> Type<Lang>
            else ArrayType<_>(go baseT, size |> Option.get) :> Type<Lang>
        | s when s.StartsWith "fsharpref" ->
            go (_type.GetGenericArguments().[0].Name)
        | x when collectedTypes.ContainsKey x 
            -> StructType(collectedTypes.[x]) :> Type<Lang>
        | x -> "Unsuported kernel type: " + x |> failwith 
    _type.Name
    |> go


let TransleteStructDecl collectedTypes (t:System.Type) targetContext =
    let name = t.Name
    let fields = [ for f in t.GetProperties (BindingFlags.Public ||| BindingFlags.Instance) ->
                    new StructField<_> (f.Name, Translate f.PropertyType true collectedTypes None targetContext)]
    new Struct<_>(name, fields)

// Copyright (c) 2014 Klimov Ivan <ivan.klimov.92@gmail.com>
open System.Collections.Generic
open Microsoft.FSharp.Quotations

type Renamer() =
    let allNames = new Dictionary<_,Stack<_>>()
//    let setNames = Set.empty
    let mutable counter = 0

    let newName vName = 
//        setNames.Add(vName) |> ignore
        if allNames.ContainsKey vName
        then 
            let mutable name = vName + string counter
            counter <- counter + 1
//            while(setNames.Contains(name)) do
//                name <- vName + string counter
//                counter <- counter + 1
//            setNames.Add(name) |> ignore
            name
        else
            vName

    member this.addName name =
        if allNames.ContainsKey name
        then
            let nName = newName name
            let scope = allNames.[name]
            scope.Push(nName)
            nName
        else
            let scope = new Stack<_>(10)
            scope.Push(name)
            allNames.Add(name, scope)
            name

    member this.removeName name =
        let scope = allNames.[name]
        scope.Pop()

    member this.getName name =
        let scope = allNames.[name]
        scope.Peek()

[<AllowNullLiteral>]
type VarInfo(orName:string, nName:string, isVar, typeV:System.Type) =
    let mutable origName = orName
    let mutable newName = nName
    let mutable isV = isVar
    let mutable typeVar = typeV

    member this.GetOriginalName =
        origName
    member this.GetNewName =
        newName
    member this.IsVar =
        isV
    member this.GetVarType =
        typeVar

[<AllowNullLiteral>]
type InfoScope(orgnName, nName, originVar) =
    let listVars = new ResizeArray<VarInfo>() // var current scope
    let needVars = new ResizeArray<VarInfo>()
    let mutable after:InfoScope = null
    let mutable inLet:InfoScope = null
    let mutable originalName = orgnName
    let mutable newName = nName
    let mutable orgnVar = originVar

    let FindInVars (orName:string) =
        let mutable var = null
        for v in listVars do
            if(v.GetOriginalName = orName) then 
                if(var = null) then
                    var <- v
        var
    
    let FindInAfter orName =
        let mutable var = null
        let mutable curAfter = after
        let mutable needList = new ResizeArray<_>()
        while(curAfter <> null) do
            if(curAfter.GetOriginalName = orName) then
                var <- new VarInfo(curAfter.GetOriginalName, curAfter.GetNewName, false, System.Type.GetType("Var"))
                needList.AddRange(curAfter.GetNeedVars)
                curAfter <- null
            else
                curAfter <- curAfter.GetAfter
        var, needList

    let rec GetNameForCurVar orgnName isAfter :VarInfo=
        let nameFromMyVar =
            if(not isAfter) then
                FindInVars orgnName
            else
                null
        if(nameFromMyVar = null) then
            if(isAfter && originalName = orgnName) then
              let nameFromMe = new VarInfo(originalName, newName, false, System.Type.GetType("Var"))
              nameFromMe
            else
                let nameFromListAfter, listNeed = FindInAfter orgnName
                if(nameFromListAfter = null) then
                    let (nameFromInLet:VarInfo) = inLet.GetNameForVar orgnName false
                    if(nameFromInLet.IsVar && (not isAfter)) then
                        needVars.Add(nameFromInLet)
                    nameFromInLet
                else
                    if(not isAfter) then
                        needVars.AddRange(listNeed)
                    nameFromListAfter
        else
            nameFromMyVar

    member this.ChangeOrgnVar (newOrgnVar:Var) =
        orgnVar <- newOrgnVar
    member this.GetOrgnVar =
        orgnVar

    member this.AddVar oName nNane typeV =
        listVars.Add(new VarInfo(oName, nNane, true, typeV))
    member this.GetVars =
        listVars

    member this.AddNeedVar oName nNane typeV =
        needVars.Add(new VarInfo(oName, nNane, true, typeV))
    member this.GetNeedVars =
        needVars

    member this.AddAfter afterScope =
        after <- afterScope
    member this.GetAfter =
        after

    member this.AddInLet letInScope =
        inLet <- letInScope
    member this.GetInLet = 
        inLet

    member this.SetOriginalName orName = 
        originalName <- orName
    member this.GetOriginalName = 
        originalName

    member this.SetNewName nName =
        newName <- nName
    member this.GetNewName =
        newName

    member this.GetNameForVar orgnName isAfter=
        GetNameForCurVar orgnName isAfter
        

type LetScope() =
    let allLet = new Dictionary<_,_>()
    let lastInLet = new Stack<_>(10)
    let mutable isInLastLet = true

    member this.SetIsInLastLet isIn = 
        isInLastLet <- isIn
    member this.GetIsInLastLet = 
        isInLastLet

    member private this.AddLetInfo (infoScope:InfoScope) = 
        allLet.Add(infoScope.GetNewName, infoScope)
    member this.GetLetInfo name =
        allLet.[name]
    member this.ContainsInfo name =
        allLet.ContainsKey(name)

    member this.LetIn name newName originVar = 
        let newInfoLet = new InfoScope(name, newName, originVar)

        if(isInLastLet) then
            if(lastInLet.Count > 0) then
                newInfoLet.AddInLet (allLet.[lastInLet.Peek()])
        else 
            if(lastInLet.Count > 0) then // если мы зашли лет после 
                let after = (allLet.[lastInLet.Peek()])
                newInfoLet.AddAfter after
                newInfoLet.AddInLet after.GetInLet

        lastInLet.Push(newName)
        this.AddLetInfo newInfoLet

    member this.GetLastInLet =
        lastInLet.Peek()

    member this.LetOut =
        lastInLet.Pop()

    member this.GetNameForVarInLet name isAfter =
        let infoLet = allLet.[this.GetLastInLet]
        infoLet.GetNameForVar name isAfter

    member this.AddVarInLastLet orgnName nName varType =
        let last = allLet.[this.GetLastInLet]
        last.AddVar orgnName nName varType