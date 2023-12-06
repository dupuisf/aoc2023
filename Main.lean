import Aoc2023.Day01
import Aoc2023.Day02
import Aoc2023.Day03
import Aoc2023.Day04
import Aoc2023.Day05
import Aoc2023.Day06

def main (args : List String) : IO Unit :=
  match args with
  | ["1"] => do
    IO.println "Day 1:"
    IO.println s!"Part 1: {← Day01.firstPart "input_01"}"
    IO.println s!"Part 2: {← Day01.secondPart "input_01"}"
    IO.println ""
  | ["2"] => do
    IO.println "Day 2:"
    IO.println s!"Part 1: {← Day02.firstPart "input_02"}"
    IO.println s!"Part 2: {← Day02.secondPart "input_02"}"
    IO.println ""
  | ["3"] => do
    IO.println "Day 3:"
    IO.println s!"Part 1: {← Day03.firstPart "input_03"}"
    IO.println s!"Part 2: {← Day03.secondPart "input_03"}"
    IO.println ""
  | ["4"] => do
    IO.println "Day 4:"
    IO.println s!"Part 1: {← Day04.firstPart "input_04"}"
    IO.println s!"Part 2: {← Day04.secondPart "input_04"}"
    IO.println ""
  | ["5"] => do
    IO.println "Day 5:"
    IO.println s!"Part 1: {← Day05.firstPart "input_05"}"
    IO.println s!"Part 2: {← Day05.secondPart "input_05"}"
    IO.println ""
  | ["6"] => do
    IO.println "Day 6:"
    IO.println s!"Part 1: {← Day06.firstPart "input_06"}"
    IO.println s!"Part 2: {← Day06.secondPart "input_06"}"
    IO.println ""
  | _ => do
    IO.println "Help, what should I do!?"
