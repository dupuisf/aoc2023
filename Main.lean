import Aoc2023

def main (args : List String) : IO Unit :=
  match args with
  | ["1"] => do
    IO.println "Day 1:"
    IO.println s!"Part 1: {← Day1.first_part}"
    IO.println s!"Part 2: {← Day1.second_part}"
    IO.println ""
  | _ => do
    IO.println "Help, what should I do!?"
