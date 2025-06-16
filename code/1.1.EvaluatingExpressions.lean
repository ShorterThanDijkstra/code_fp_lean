-- https://lean-lang.org/functional_programming_in_lean//Getting-to-Know-Lean/Evaluating-Expressions/#evaluating
#eval 1 + 2
#eval 1 + 2 * 5
#eval String.append "Hello, " "Lean!"
#eval String.append "great " (String.append "oak " "tree")
String.append "it is " (if 1 > 2 then "yes" else "no")
String.append "it is " (if false then "yes" else "no")
String.append "it is " "no"
String.append "it is " (if 1 > 2 then "yes" else "no")
String.append "it is " (if false then "yes" else "no")
String.append "it is " "no"
"it is no"
#eval String.append "it is "