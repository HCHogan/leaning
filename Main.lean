import Leaning

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

partial def getLines : IO String := do
  IO.println "Enter your text:"
  let line ← (← IO.getStdin).getLine
  if line.trim.isEmpty then
    return line.trimRight
  else
    return line.trimRight ++ (← getLines)
