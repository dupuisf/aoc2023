import Aoc2023.Day01
import Aoc2023.Day02
import Aoc2023.Day03
import Aoc2023.Day04
import Aoc2023.Day05
import Aoc2023.Day06
import Aoc2023.Day07
import Aoc2023.Day08
import Aoc2023.Day09
import Aoc2023.Day10
import Aoc2023.Day11
import Aoc2023.Day12
import Aoc2023.Day13
import Aoc2023.Day14
import Aoc2023.Day15
import Aoc2023.Day16
import Aoc2023.Day17
import Aoc2023.Day18
import Aoc2023.Day19
import Aoc2023.Day20
import Aoc2023.Day21
import Aoc2023.Day22
import Aoc2023.Day23
import Aoc2023.Day24
import Aoc2023.Day25

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
    IO.println s!"Part 1: {← Day06.firstPart Day06.realinput}"
    IO.println s!"Part 2: {← Day06.secondPart Day06.realinput₂}"
    IO.println ""
  | ["7"] => do
    IO.println "Day 7:"
    IO.println s!"Part 1: {← Day07.firstPart "input_07"}"
    IO.println s!"Part 2: {← Day07part2.secondPart "input_07"}"
    IO.println ""
  | ["8"] => do
    IO.println "Day 8:"
    IO.println s!"Part 1: {← Day08.firstPart "input_08"}"
    IO.println s!"Part 2: {← Day08.secondPart "input_08"}"
    IO.println ""
  | ["9"] => do
    IO.println "Day 9:"
    IO.println s!"Part 1: {← Day09.firstPart "input_09"}"
    IO.println s!"Part 2: {← Day09.secondPart "input_09"}"
    IO.println ""
  | ["10"] => do
    IO.println "Day 10:"
    IO.println s!"Part 1: {← Day10.firstPart "input_10"}"
    IO.println s!"Part 2: {← Day10.secondPart "input_10"}"
    IO.println ""
  | ["10", s] => do
    IO.println "Day 10:"
    IO.println s!"Part 1: {← Day10.firstPart s!"input_10_test{s}"}"
    IO.println s!"Part 2: {← Day10.secondPart s!"input_10_test{s}"}"
    IO.println ""
  | ["11"] => do
    IO.println "Day 11:"
    IO.println s!"Part 1: {← Day11.firstPart "input_11"}"
    IO.println s!"Part 2: {← Day11.secondPart "input_11"}"
    IO.println ""
  | ["11", s] => do
    IO.println "Day 11:"
    IO.println s!"Part 1: {← Day11.firstPart s!"input_11_test{s}"}"
    IO.println s!"Part 2: {← Day11.secondPart s!"input_11_test{s}"}"
    IO.println ""
  | ["12"] => do
    IO.println "Day 12:"
    IO.println s!"Part 1: {← Day12.firstPart "input_12"}"
    IO.println s!"Part 2: {← Day12.secondPart "input_12"}"
    IO.println ""
  | ["12", s] => do
    IO.println "Day 12:"
    IO.println s!"Part 1: {← Day12.firstPart s!"input_12_test{s}"}"
    IO.println s!"Part 2: {← Day12.secondPart s!"input_12_test{s}"}"
    IO.println ""
  | ["13"] => do
    IO.println "Day 13:"
    IO.println s!"Part 1: {← Day13.firstPart "input_13"}"
    IO.println s!"Part 2: {← Day13.secondPart "input_13"}"
    IO.println ""
  | ["13", s] => do
    IO.println "Day 13:"
    IO.println s!"Part 1: {← Day13.firstPart s!"input_13_test{s}"}"
    IO.println s!"Part 2: {← Day13.secondPart s!"input_13_test{s}"}"
    IO.println ""
  | ["14", s] => do
    IO.println "Day 14:"
    IO.println s!"Part 1: {← Day14.firstPart "input_14"}"
    IO.println s!"Part 2: {← Day14.secondPart "input_14" s}"
    IO.println ""
  | ["14t", s] => do
    IO.println "Day 14:"
    IO.println s!"Part 1: {← Day14.firstPart "input_14"}"
    IO.println s!"Part 2: {← Day14.secondPart "input_14_test1" s}"
    IO.println ""
  | ["15", s] => do
    IO.println "Day 15:"
    IO.println s!"Part 1: {← Day15.firstPart s!"input_15_test{s}"}"
    IO.println s!"Part 2: {← Day15.secondPart s!"input_15_test{s}"}"
    IO.println ""
  | ["16"] => do
    IO.println "Day 16:"
    IO.println s!"Part 1: {← Day16.firstPart s!"input_16"}"
    IO.println s!"Part 2: {← Day16.secondPart s!"input_16"}"
    IO.println ""
  | ["17"] => do
    IO.println "Day 17:"
    IO.println s!"Part 1: {← Day17.firstPart s!"input_17"}"
    IO.println s!"Part 2: {← Day17.secondPart s!"input_17"}"
    IO.println ""
  | ["18"] => do
    IO.println "Day 18:"
    IO.println s!"Part 1: {← Day18.firstPart s!"input_18"}"
    IO.println s!"Part 2: {← Day18.secondPart s!"input_18"}"
    IO.println ""
  | ["19"] => do
    IO.println "Day 19:"
    IO.println s!"Part 1: {← Day19.firstPart s!"input_19"}"
    IO.println s!"Part 2: {← Day19.secondPart s!"input_19"}"
    IO.println ""
  | ["20"] => do
    IO.println "Day 20:"
    IO.println s!"Part 1: {← Day20.firstPart s!"input_20"}"
    IO.println s!"Part 2: {← Day20.secondPart s!"input_20"}"
    IO.println ""
  | ["20t"] => do
    IO.println "Day 20:"
    IO.println s!"Part 1: {← Day20.firstPart "input_20_test1"}"
    IO.println s!"Part 2: {← Day20.secondPart "input_20_test1"}"
    IO.println ""
  | ["20t2"] => do
    IO.println "Day 20:"
    IO.println s!"Part 1: {← Day20.firstPart "input_20_test2"}"
    IO.println s!"Part 2: {← Day20.secondPart "input_20_test2"}"
    IO.println ""
  | ["21"] => do
    IO.println "Day 21:"
    IO.println s!"Part 1: {← Day21.firstPart s!"input_21"}"
    IO.println s!"Part 2: {← Day21.secondPart s!"input_21"}"
    IO.println ""
  | ["22"] => do
    IO.println "Day 22:"
    IO.println s!"Part 1: {← Day22.firstPart s!"input_22"}"
    IO.println s!"Part 2: {← Day22.secondPart s!"input_22"}"
    IO.println ""
  | ["23"] => do
    IO.println "Day 23:"
    IO.println s!"Part 1: {← Day23.firstPart s!"input_23"}"
    IO.println s!"Part 2: {← Day23.secondPart s!"input_23"}"
    IO.println ""
  | ["24"] => do
    IO.println "Day 24:"
    IO.println s!"Part 1: {← Day24.firstPart s!"input_24"}"
    IO.println s!"Part 2: {← Day24.secondPart s!"input_24"}"
    IO.println ""
  | ["25"] => do
    IO.println "Day 25:"
    IO.println s!"Part 1: {← Day25.firstPart s!"input_25"}"
    IO.println s!"Part 2: {← Day25.secondPart s!"input_25"}"
    IO.println ""
  | _ => do
    IO.println "Help, what should I do!?"
