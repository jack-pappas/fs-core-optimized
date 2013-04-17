(*

Copyright 2013 Jack Pappas

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

namespace PerfComparison

/// The results of two (2) tests -- a baseline test and a comparison test.
type TestResult<'T when 'T : comparison> = {
    Baseline : 'T;
    Result : 'T;
}

/// The results of three (3) tests -- a baseline test, and two comparison tests.
type TestResult3<'T when 'T : comparison> = {
    Baseline : 'T;
    Result1 : 'T;
    Result2 : 'T;
}

/// Functions for creating arrays of random values.
module RandomArray =
    /// Creates a random array of 32-bit integers.
    let int32 count maxValue density : int[] =
        // Preconditions
        if count < 0 then
            invalidArg "count" "The count cannot be negative."
        elif maxValue < 0 then
            invalidArg "maxValue" "The maximum value cannot be negative."
        elif density < 0.0 then
            invalidArg "density" "The density value cannot be negative."
        elif density > 1.0 then
            invalidArg "density" "The density value cannot be greater than one (1)."

        let rand = System.Random ()
        let maxValue = int <| (float maxValue) * (1.0 - density)
        let arr = Array.zeroCreate count
        for i = 0 to count - 1 do
            arr.[i] <- rand.Next maxValue
        arr

    /// Creates a random array of 64-bit integers.
    let int64 count (maxValue : int64) density : int64[] =
        // Preconditions
        if count < 0 then
            invalidArg "count" "The count cannot be negative."
        elif maxValue < 0L then
            invalidArg "maxValue" "The maximum value cannot be negative."
        elif density < 0.0 then
            invalidArg "density" "The density value cannot be negative."
        elif density > 1.0 then
            invalidArg "density" "The density value cannot be greater than one (1)."

        let rand = System.Random ()
        let maxValue = int64 <| (float maxValue) * (1.0 - density)
        let arr = Array.zeroCreate count
        let bytes = Array.zeroCreate sizeof<int64>
        for i = 0 to count - 1 do
            arr.[i] <-
                rand.NextBytes bytes
                System.BitConverter.ToInt64 (bytes, 0) % maxValue
        arr


[<AutoOpen>]
module Helpers =
    open System

    /// Print timing results.
    let printTimings (result : TestResult<TimeSpan>) =
        printfn "Baseline: %4f (ms)" result.Baseline.TotalMilliseconds
        printfn "Result  : %4f (ms)" result.Result.TotalMilliseconds
        printfn ""

    /// Print timing results.
    let printTimings3 (result : TestResult3<TimeSpan>) =
        printfn "Baseline: %4f (ms)" result.Baseline.TotalMilliseconds
        printfn "Result 1: %4f (ms)" result.Result1.TotalMilliseconds
        printfn "Result 2: %4f (ms)" result.Result2.TotalMilliseconds
        printfn ""

