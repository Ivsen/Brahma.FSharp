module Brahma.FSharp.OpenCL.QuotationsTransformerTests

open NUnit.Framework
open System.IO
open Brahma.Helpers
open OpenCL.Net
open Brahma.OpenCL
open Brahma.FSharp.OpenCL.Core
open System
open System.Reflection
open Microsoft.FSharp.Quotations

[<TestFixture>]
type QTransformer() =

    let basePath = "../../../../Tests/Brahma.FSharp.OpenCL/Translator/Expected/"

    let deviceType = DeviceType.Gpu
    let platformName = "*"

    let provider =
        try  ComputeProvider.Create(platformName, deviceType)
        with 
        | ex -> failwith ex.Message   

    let filesAreEqual file1 file2 =
        let all1 = File.ReadAllBytes file1
        let all2 = File.ReadAllBytes file2
        Assert.AreEqual (all1.Length, all2.Length)
        Assert.IsTrue(Array.forall2 (=) all1 all2)

    let checkCode command outFile expected =
        let code = ref ""
        let _ = provider.Compile(command,_outCode = code)
        printfn "%s" !code
        System.IO.File.WriteAllText(outFile,!code)
        filesAreEqual outFile (System.IO.Path.Combine(basePath,expected))

    let a = [|0..3|]

    [<Test>]
    member this.``Let renamed``() =
        let command = 
            <@ 
                fun (range:_1D) (buf:array<int*int>) ->                                        
                    let f x = 
                        let g = 1 + x
                        g
                    f 1
            @>

        checkCode command "Let renamed.gen" "Let renamed.cl"

    [<Test>]
    member this.``Let renamed 2``() =
        let command = 
            <@ 
                fun (range:_1D) (buf:array<int*int>) ->                                        
                    let f m k = 
                        let g q w = 1 + q + w
                        let t p = 7 - p
                        (g 1 2) - m * k / (t 53)
                    f 1 4
            @>

        checkCode command "Let renamed 2.gen" "Let renamed 2.cl"

    [<Test>]
    member this.``Renamer Test``() =
        let command = 
            <@ 
                fun (range:_1D) (buf:array<int*int>) ->                                        
                    let f x y = 
                        let y = y
                        let y = y
                        let g x m = m + x
                        g x y
                    f 1 7
            @>

        checkCode command "Renamer Test.gen" "Renamer Test.cl"

    [<Test>]
    member this.``Template Let Transformation Test 1``() =
        let command = 
            <@ 
                fun (range:_1D) (buf:array<int*int>) ->                                        
                    let f = 
                        let x = 3
                        x
                    f
            @>

        checkCode command "Template Test 1.gen" "Template Test 1.cl"
        
    [<Test>]
    member this.``Template Let Transformation Test 2``() =
        let command = 
            <@ 
                fun (range:_1D) (buf:array<int*int>) ->                                        
                    let f = 
                        let x = 
                            let y = 3
                            y
                        x
                    f
            @>

        checkCode command "Template Test 2.gen" "Template Test 2.cl"

    [<Test>]
    member this.``Template Let Transformation Test 3``() =
        let command = 
            <@ 
                fun (range:_1D) (buf:array<int*int>) ->                                        
                    let f = 
                        let f = 5
                        f
                    f
            @>

        checkCode command "Template Test 3.gen" "Template Test 3.cl"

    [<Test>]
    member this.``Template Let Transformation Test 4``() =
        let command = 
            <@ 
                fun (range:_1D) (buf:array<int*int>) ->                                        
                    let f = 
                        let f = 
                            let f = 5
                            f
                        f
                    f
            @>

        checkCode command "Template Test 4.gen" "Template Test 4.cl"
    [<Test>]
    member this.``Template Let Transformation Test 5``() =
        let command = 
            <@ 
                fun (range:_1D) (buf:array<int*int>) ->                                        
                    let f a b = 
                        let x y z = y + z
                        x a b
                    f
            @>

        checkCode command "Template Test 5.gen" "Template Test 5.cl"
    
    [<Test>]
    member this.``Template Let Transformation Test 6``() =
        let command = 
            <@ 
                fun (range:_1D) (buf:array<int*int>) ->                                        
                    let f x y = 
                        let x = x
                        x + y
                    f 7 8
            @>
        checkCode command "Template Test 6.gen" "Template Test 6.cl"

    [<Test>]
    member this.``Template Let Transformation Test 7``() =
        let command = 
            <@ 
                fun (range:_1D) (buf:array<int*int>) ->                                        
                    let f y = 
                        let x y = 6 - y
                        x y
                    f 7
            @>
        checkCode command "Template Test 7.gen" "Template Test 7.cl"
    
    [<Test>]
    member this.``Template Let Transformation Test 8``() =
        let command = 
            <@ 
            fun (range:_1D) (buf:array<int*int>) ->                                        
                let f y = 
                    let y = 1 - y
                    let x y = y + y
                    y
                f 7
            @>
        checkCode command "Template Test 8.gen" "Template Test 8.cl"