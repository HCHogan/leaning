import Leaning

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

partial def getLines : IO String := do
  IO.println "Enter your text:"
  let line ← (← IO.getStdin).getLine
  if line.trimAscii.isEmpty then
    return line.trimAsciiEnd.toString
  else
    return line.trimAsciiEnd.toString ++ (← getLines)
